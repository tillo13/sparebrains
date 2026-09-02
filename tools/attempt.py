"""The loop. Ask the free pool for proofs, let the kernel grade them, keep every receipt.

    python3 tools/attempt.py --sample 5 --seed 1 --order asc --stop-on-accept --max-calls 300
    python3 tools/attempt.py --sample 30 --seed 2 --min-tier medium --skip-benched --jobs 2 --max-calls 1400

Lanes are walked by quality tier (tiny → frontier, or reversed with --order desc).
With --stop-on-accept a target stops at the first kernel-verified proof, so the
ledger records the cheapest brain that solved it. Without it every lane gets every
target (the per-lane yield measurement). Each attempt writes one compact line to the
git ledger and posts its full transcript to kumori's sparebrains_attempts table.
Accepted proofs are saved whole under verified/.
"""
import argparse, hashlib, json, os, random, re, sys, threading, time
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT), str(ROOT / "tools")]
from check import judge                                              # the judge, unchanged
from utilities.kumori_api_client import (init as kumori_init, llm_backends, llm_backoff_state, llm_chat,
                                         sparebrains_attempt)

TIER_RANK = {"tiny": 0, "low": 1, "medium": 2, "high": 3, "frontier": 4}
PROOF_SEP = re.compile(r":=\s*by\b")
RUNNER_PATH = re.compile(r"\S*/\.lake/attempts/\S+?\.lean:")     # keep "line:col: error: …", drop the path
SITE = "https://sparebrains.kumori.ai"
FENCE = re.compile(r"```(?:lean4?)?\s*\n(.*?)```", re.S)
SYSTEM = ("You are an expert in Lean 4 and Mathlib. You complete formal proofs. "
          "You answer with code only.")
ASK = ("Complete the proof in this Lean 4 file (Lean v4.33.1, mathlib v4.33.1, `import Mathlib` is "
       "already there). Replace only the `sorry` with a complete proof.\n"
       "Rules: keep the theorem statement byte-for-byte; no `sorry`, `admit`, or `native_decide`; "
       "no new axioms; Lean 4 syntax, not Lean 3.\n"
       "Answer with the ENTIRE file inside one ```lean fence and nothing else.\n\n")


def lanes(explicit, min_tier=None, skip_benched=False):
    """Live chat lanes, ordered by quality tier. Shape of a backend dict is logged once.
    min_tier drops everything below it (and every untiered lane); skip_benched drops lanes
    the router's circuit breaker currently refuses, instead of spending a call to learn it."""
    raw = llm_backends()
    if raw:
        print("backend[0] =", json.dumps(raw[0])[:400])
    out = []
    for b in raw:
        name = b.get("name") or b.get("backend")
        if not name or b.get("enabled") is False or b.get("modality") not in (None, "chat"):
            continue
        tier = (b.get("quality_tier") or "unknown").lower()
        out.append({"backend": name, "provider": b.get("provider") or b.get("route") or name.split("-")[0],
                    "model": b.get("model"), "tier": tier, "rank": TIER_RANK.get(tier, -1)})
    if explicit:
        want = [x.strip() for x in explicit.split(",") if x.strip()]
        known = {l["backend"]: l for l in out}
        out = [known.get(w, {"backend": w, "provider": None, "model": None, "tier": "unknown", "rank": -1})
               for w in want]
    if skip_benched:
        state = llm_backoff_state()
        benched = {n for n, d in state.items() if d.get("backed_off")}
        dropped = [l["backend"] for l in out if l["backend"] in benched]
        out = [l for l in out if l["backend"] not in benched]
        print(f"skipping {len(dropped)} benched lane(s): {', '.join(dropped) or 'none'}")
    if min_tier:
        floor = TIER_RANK[min_tier]
        out = [l for l in out if l["rank"] >= floor]
    known = sorted((l for l in out if l["rank"] >= 0), key=lambda l: (l["rank"], l["backend"]))
    unknown = sorted((l for l in out if l["rank"] < 0), key=lambda l: l["backend"])
    return known, unknown                                # untiered lanes always go last


def extract_proof(reply, name):
    blocks = FENCE.findall(reply)
    text = max(blocks, key=len) if blocks else reply
    i = text.find(f"theorem {name}")
    if i >= 0:
        sep = PROOF_SEP.search(text, i)
        if not sep:
            return None
        proof = text[sep.end():]
    elif not blocks or "theorem " in text or "import " in text:
        return None                                  # prose, a different theorem, or an echoed preamble
    else:
        proof = text                                 # a fenced bare tactic block
    lines = proof.strip("\n").splitlines()
    if not any(l.strip() for l in lines):
        return None
    indent = min(len(l) - len(l.lstrip()) for l in lines if l.strip())
    if indent == 0:
        lines = ["  " + l if l.strip() else l for l in lines]
    return "\n".join(lines).rstrip() + "\n"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--targets", default="targets/minif2f/test")
    ap.add_argument("--only", default="", help="comma-separated target names (overrides --sample)")
    ap.add_argument("--unattempted", action="store_true",
                    help="take the first --sample targets no sweep run has touched (alphabetical); exit 0 when none remain")
    ap.add_argument("--sample", type=int, default=5)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--lanes", default="", help="comma-separated backend names (default: every live lane)")
    ap.add_argument("--min-tier", choices=list(TIER_RANK), default=None, help="drop lanes below this tier")
    ap.add_argument("--skip-benched", action="store_true", help="drop lanes the router currently refuses")
    ap.add_argument("--jobs", type=int, default=1, help="parallel attempts in sweep mode (ladder is sequential)")
    ap.add_argument("--order", choices=["asc", "desc"], default="asc")
    ap.add_argument("--stop-on-accept", action="store_true")
    ap.add_argument("--attempts", type=int, default=1)
    ap.add_argument("--max-calls", type=int, default=300)
    ap.add_argument("--max-tokens", type=int, default=4000)
    ap.add_argument("--call-timeout", type=int, default=180)
    ap.add_argument("--lean-timeout", type=int, default=300)
    ap.add_argument("--pace", type=float, default=1.0)
    args = ap.parse_args()

    if not os.environ.get("KUMORI_API_KEY"):
        sys.exit("KUMORI_API_KEY is not set")
    kumori_init(min_inter_call_sec=args.pace)
    run_id = os.environ.get("GITHUB_RUN_ID") or datetime.now(timezone.utc).strftime("local-%Y%m%dT%H%M%S")
    tdir = ROOT / args.targets
    target_set = str(Path(args.targets).relative_to("targets"))
    names = sorted(p.stem for p in tdir.glob("*.lean"))
    if args.only:
        names = [n.strip() for n in args.only.split(",") if n.strip()]
    elif args.unattempted:
        swept = set()
        for f in (ROOT / "ledger" / target_set).glob("*.jsonl"):
            for line in f.read_text().splitlines():
                try:
                    r = json.loads(line)
                except ValueError:
                    continue
                if str(r.get("mode", "")).startswith("sweep"):
                    swept.add(r["target"])
        remaining = [n for n in names if n not in swept]
        print(f"unattempted: {len(remaining)} of {len(names)} targets not yet swept")
        if not remaining:
            print("all targets swept; nothing to do")
            return 0
        names = remaining[:args.sample]
    else:
        names = random.Random(args.seed).sample(names, min(args.sample, len(names)))
    known, unknown = lanes(args.lanes, args.min_tier, args.skip_benched)
    order = (known[::-1] if args.order == "desc" else known) + unknown
    mode = f"{'ladder' if args.stop_on_accept else 'sweep'}-{args.order}"
    print(f"run {run_id}: {len(names)} targets × {len(order)} lanes × {args.attempts} attempts, "
          f"mode {mode}, cap {args.max_calls} calls")
    for l in order:
        print(f"  lane {l['backend']:40s} tier={l['tier']:8s} model={l['model']}")

    ledger = ROOT / "ledger" / target_set / f"{run_id}.jsonl"
    ledger.parent.mkdir(parents=True, exist_ok=True)
    tmpdir = ROOT / ".lake" / "attempts"
    tmpdir.mkdir(parents=True, exist_ok=True)
    lock = threading.Lock()
    state = {"calls": 0, "accepts": 0, "errors": 0}
    solved = {}

    def run_one(name, lane, attempt_no):
        """One attempt: ask, splice, judge, record. Returns the verdict."""
        target_text = (tdir / f"{name}.lean").read_text()
        prefix = target_text[:PROOF_SEP.search(target_text).end()]
        statement_sha = hashlib.sha256(prefix.encode()).hexdigest()
        with lock:
            state["calls"] += 1
            n = state["calls"]
        prompt = ASK + target_text
        t0 = time.monotonic()
        try:
            reply, _ = llm_chat(lane["backend"], [{"role": "user", "content": prompt}],
                                max_tokens=args.max_tokens, temperature=0.2, system=SYSTEM,
                                app_name="eval:sparebrains", timeout=(10, args.call_timeout))
            err = None
        except Exception as e:
            reply, err = "", f"{type(e).__name__}: {str(e)[:200]}"
        call_s = time.monotonic() - t0
        proof = extract_proof(reply or "", name) if reply else None
        candidate = lean_out = None
        lean_s = 0.0
        if err:
            verdict, reason = "error", err
        elif not proof:
            verdict, reason = "reject", "no proof extracted from reply"
        else:
            candidate = prefix + "\n" + proof
            cpath = tmpdir / f"{name}.{lane['backend']}.{attempt_no}.lean"
            cpath.write_text(candidate)
            verdict, reason, lean_s, lean_out = judge(str(cpath), args.lean_timeout)
            reason = RUNNER_PATH.sub("", reason)
            if verdict == "wellformed":
                verdict, reason = "reject", "proof still contains sorry"
        row = {"ts": datetime.now(timezone.utc).isoformat(timespec="seconds"), "run_id": run_id,
               "target_set": target_set, "target": name, "statement_sha": statement_sha,
               "backend": lane["backend"], "provider": lane["provider"], "model": lane["model"],
               "quality_tier": lane["tier"], "tier_rank": lane["rank"], "attempt_no": attempt_no,
               "mode": mode, "verdict": verdict, "reason": reason[:300],
               "call_seconds": round(call_s, 1), "lean_seconds": round(lean_s, 1),
               "response_chars": len(reply or ""),
               "proof_sha": hashlib.sha256(proof.encode()).hexdigest() if proof else None}
        with lock:
            with ledger.open("a") as fh:
                fh.write(json.dumps(row) + "\n")
            if verdict == "accept":
                state["accepts"] += 1
                solved.setdefault(name, lane)
            elif verdict == "error":
                state["errors"] += 1
        saved = sparebrains_attempt({**row, "prompt": prompt, "response": reply, "proof": proof,
                                     "candidate": candidate, "lean_output": lean_out}) or {}
        link = f"  {SITE}/attempts/{saved['id']}" if saved.get("id") else ""
        print(f"[{n}/{args.max_calls}] {name} ← {lane['backend']} ({lane['tier']}) → {verdict}  "
              f"call {call_s:.0f}s lean {lean_s:.1f}s  {reason[:110]}{link}", flush=True)
        if n % 25 == 0:
            with lock:
                print(f"[tally] {n} attempts · {state['accepts']} verified · {state['errors']} lane errors · "
                      f"{len(solved)}/{len(names)} targets solved so far", flush=True)
        if verdict == "accept":
            vpath = ROOT / "verified" / target_set / name / f"{lane['backend']}.lean"
            vpath.parent.mkdir(parents=True, exist_ok=True)
            vpath.write_text(candidate)
        return verdict

    if args.stop_on_accept:                              # ladder: order matters, so sequential
        for name in names:
            for lane in order:
                if state["calls"] >= args.max_calls or name in solved:
                    break
                for attempt_no in range(1, args.attempts + 1):
                    if state["calls"] >= args.max_calls:
                        break
                    if run_one(name, lane, attempt_no) == "accept":
                        break
            if state["calls"] >= args.max_calls:
                print(f"cap reached: {args.max_calls} calls")
                break
    else:                                                # sweep: every pair, independent, parallel
        work = [(n, l, a) for n in names for l in order for a in range(1, args.attempts + 1)]
        if len(work) > args.max_calls:
            print(f"cap: {len(work)} planned attempts trimmed to {args.max_calls}")
            work = work[:args.max_calls]
        with ThreadPoolExecutor(max_workers=max(1, args.jobs)) as pool:
            list(pool.map(lambda w: run_one(*w), work))

    calls, accepts = state["calls"], state["accepts"]
    print(f"done: {calls} calls, {accepts} accepts, {len(solved)}/{len(names)} targets solved")
    for n in names:
        l = solved.get(n)
        print(f"  {n:45s} {'solved by ' + l['backend'] + ' (' + l['tier'] + ')' if l else 'unsolved'}")
    out = os.environ.get("GITHUB_OUTPUT")
    if out:
        with open(out, "a") as fh:
            fh.write(f"calls={calls}\naccepts={accepts}\nlanes={len(order)}\ntargets={len(names)}\nmode={mode}\n")
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        with open(summary, "a") as fh:
            fh.write(f"### attempt run `{run_id}` — {mode}: {calls} calls, {accepts} accepts, "
                     f"{len(solved)}/{len(names)} targets solved, $0\n\n| target | solved by | tier |\n|---|---|---|\n")
            for n in names:
                l = solved.get(n)
                fh.write(f"| `{n}` | {l['backend'] if l else '—'} | {l['tier'] if l else '—'} |\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
