"""The loop. Ask the free pool for proofs, let the kernel grade them, keep every receipt.

    python3 tools/attempt.py --sample 5 --seed 1 --order asc --stop-on-accept --max-calls 300

Lanes are walked by quality tier (tiny → frontier, or reversed with --order desc).
With --stop-on-accept a target stops at the first kernel-verified proof, so the
ledger records the cheapest brain that solved it. Without it every lane gets every
target (the per-lane yield measurement). Each attempt writes one compact line to the
git ledger and posts its full transcript to kumori's sparebrains_attempts table.
Accepted proofs are saved whole under verified/.
"""
import argparse, hashlib, json, os, random, re, sys, time
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT), str(ROOT / "tools")]
from check import judge                                              # the judge, unchanged
from utilities.kumori_api_client import init as kumori_init, llm_backends, llm_chat, sparebrains_attempt

TIER_RANK = {"tiny": 0, "low": 1, "medium": 2, "high": 3, "frontier": 4}
PROOF_SEP = re.compile(r":=\s*by\b")
FENCE = re.compile(r"```(?:lean4?)?\s*\n(.*?)```", re.S)
SYSTEM = ("You are an expert in Lean 4 and Mathlib. You complete formal proofs. "
          "You answer with code only.")
ASK = ("Complete the proof in this Lean 4 file (Lean v4.33.1, mathlib v4.33.1, `import Mathlib` is "
       "already there). Replace only the `sorry` with a complete proof.\n"
       "Rules: keep the theorem statement byte-for-byte; no `sorry`, `admit`, or `native_decide`; "
       "no new axioms; Lean 4 syntax, not Lean 3.\n"
       "Answer with the ENTIRE file inside one ```lean fence and nothing else.\n\n")


def lanes(explicit):
    """Live chat lanes, ordered by quality tier. Shape of a backend dict is logged once."""
    raw = llm_backends()
    if raw:
        print("backend[0] =", json.dumps(raw[0])[:400])
    out = []
    for b in raw:
        name = b.get("name") or b.get("backend")
        if not name or b.get("enabled") is False or b.get("modality") not in (None, "chat"):
            continue
        tier = (b.get("quality_tier") or "unknown").lower()
        out.append({"backend": name, "provider": b.get("provider") or b.get("route"),
                    "model": b.get("model"), "tier": tier, "rank": TIER_RANK.get(tier, -1)})
    if explicit:
        want = [x.strip() for x in explicit.split(",") if x.strip()]
        known = {l["backend"]: l for l in out}
        out = [known.get(w, {"backend": w, "provider": None, "model": None, "tier": "unknown", "rank": -1})
               for w in want]
    return sorted(out, key=lambda l: (l["rank"], l["backend"]))


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
    ap.add_argument("--sample", type=int, default=5)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--lanes", default="", help="comma-separated backend names (default: every live lane)")
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
    else:
        names = random.Random(args.seed).sample(names, min(args.sample, len(names)))
    order = lanes(args.lanes)
    if args.order == "desc":
        order.reverse()
    mode = f"{'ladder' if args.stop_on_accept else 'sweep'}-{args.order}"
    print(f"run {run_id}: {len(names)} targets × {len(order)} lanes × {args.attempts} attempts, "
          f"mode {mode}, cap {args.max_calls} calls")
    for l in order:
        print(f"  lane {l['backend']:40s} tier={l['tier']:8s} model={l['model']}")

    ledger = ROOT / "ledger" / target_set / f"{run_id}.jsonl"
    ledger.parent.mkdir(parents=True, exist_ok=True)
    calls, accepts, solved = 0, 0, {}
    tmpdir = ROOT / ".lake" / "attempts"
    tmpdir.mkdir(parents=True, exist_ok=True)

    for name in names:
        target_text = (tdir / f"{name}.lean").read_text()
        sep = PROOF_SEP.search(target_text)
        prefix = target_text[:sep.end()]
        statement_sha = hashlib.sha256(prefix.encode()).hexdigest()
        for lane in order:
            if calls >= args.max_calls:
                break
            for attempt_no in range(1, args.attempts + 1):
                if calls >= args.max_calls:
                    break
                calls += 1
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
                with ledger.open("a") as fh:
                    fh.write(json.dumps(row) + "\n")
                sparebrains_attempt({**row, "prompt": prompt, "response": reply, "proof": proof,
                                     "candidate": candidate, "lean_output": lean_out})
                print(f"[{calls}/{args.max_calls}] {name} ← {lane['backend']} ({lane['tier']}) → {verdict}  "
                      f"call {call_s:.0f}s lean {lean_s:.1f}s  {reason[:90]}", flush=True)
                if verdict == "accept":
                    accepts += 1
                    solved.setdefault(name, lane)
                    vpath = ROOT / "verified" / target_set / name / f"{lane['backend']}.lean"
                    vpath.parent.mkdir(parents=True, exist_ok=True)
                    vpath.write_text(candidate)
                    break
            if args.stop_on_accept and name in solved:
                break
        if calls >= args.max_calls:
            print(f"cap reached: {args.max_calls} calls")
            break

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
