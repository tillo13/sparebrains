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
from collections import defaultdict, deque
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT), str(ROOT / "tools")]
from check import judge                                              # the judge, unchanged
from utilities.kumori_api_client import (KumoriAPIError, init as kumori_init, llm_backends, llm_backoff_state,
                                         llm_chat, sparebrains_attempt)

TIER_RANK = {"tiny": 0, "low": 1, "medium": 2, "high": 3, "frontier": 4}
PROOF_SEP = re.compile(r":=\s*by\b")
RUNNER_PATH = re.compile(r"\S*/\.lake/attempts/\S+?\.lean:")     # keep "line:col: error: …", drop the path
MIN_ANSWERED_TO_COUNT_SWEPT = 8   # a target is "swept" only once this many lanes actually answered it
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


def interleave_by_provider(lanes_in_order):
    """Round-robin across providers so consecutive calls never hammer one account.
    Twenty-eight Mistral lanes share one free-tier rate limit; walking them back to back is
    what benched half of sweep 1. Tier order is kept within each provider's queue."""
    queues = defaultdict(deque)
    for l in lanes_in_order:
        queues[l["provider"]].append(l)
    out = []
    while queues:
        for prov in list(queues):
            out.append(queues[prov].popleft())
            if not queues[prov]:
                del queues[prov]
    return out


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
    ap.add_argument("--max-per-provider", type=int, default=0,
                    help="keep at most N lanes per provider, highest tier first (0 = all); the Mistral list is 28 aliases of a few models")
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
        answered = defaultdict(int)          # target → lanes that actually answered in sweep runs
        for f in (ROOT / "ledger" / target_set).glob("*.jsonl"):
            for line in f.read_text().splitlines():
                try:
                    r = json.loads(line)
                except ValueError:
                    continue
                if str(r.get("mode", "")).startswith("sweep") and r.get("verdict") in ("accept", "reject"):
                    answered[r["target"]] += 1
        swept = {t for t, k in answered.items() if k >= MIN_ANSWERED_TO_COUNT_SWEPT}
        remaining = [n for n in names if n not in swept]
        print(f"unattempted: {len(remaining)} of {len(names)} targets not yet swept")
        if not remaining:
            print("all targets swept; nothing to do")
            return 0
        names = remaining[:args.sample]
    else:
        names = random.Random(args.seed).sample(names, min(args.sample, len(names)))
    known, unknown = lanes(args.lanes, args.min_tier, args.skip_benched)
    if args.max_per_provider:
        kept, seen = [], defaultdict(int)
        for l in sorted(known, key=lambda l: (-l["rank"], l["backend"])):   # strongest first within a provider
            if seen[l["provider"]] < args.max_per_provider:
                kept.append(l)
                seen[l["provider"]] += 1
        dropped = len(known) - len(kept)
        known = sorted(kept, key=lambda l: (l["rank"], l["backend"]))
        print(f"max {args.max_per_provider} lanes per provider: kept {len(known)}, dropped {dropped}")
    order = (known[::-1] if args.order == "desc" else known) + unknown
    mode = f"{'ladder' if args.stop_on_accept else 'sweep'}-{args.order}"
    t_start = time.time()
    print(f"run {run_id}: {len(names)} targets × {len(order)} lanes × {args.attempts} attempts, "
          f"mode {mode}, cap {args.max_calls} calls")
    for l in order:
        print(f"  lane {l['backend']:40s} tier={l['tier']:8s} model={l['model']}")

    ledger = ROOT / "ledger" / target_set / f"{run_id}.jsonl"
    ledger.parent.mkdir(parents=True, exist_ok=True)
    tmpdir = ROOT / ".lake" / "attempts"
    tmpdir.mkdir(parents=True, exist_ok=True)
    lock = threading.Lock()
    state = {"calls": 0, "accepts": 0, "errors": 0, "skipped": 0, "waits": 0}
    solved = {}
    per_target = {n: {"done": 0, "accepts": 0, "errors": 0, "lanes": []} for n in names}
    per_lane = {l["backend"]: {"tier": l["tier"], "attempts": 0, "accepts": 0, "errors": 0} for l in order}
    planned_per_target = len(order) * args.attempts
    provider_lock = defaultdict(threading.Lock)          # never two workers on one provider at once
    bench = {"t": 0.0, "state": {}}
    exhausted = {}                                       # provider → why it is parked for the rest of the run

    def benched(backend):
        """Router bench state, refreshed at most every 30 s. True = the router would 503 this lane now."""
        now = time.monotonic()
        with lock:
            if now - bench["t"] > 30:
                try:
                    bench["state"] = llm_backoff_state() or {}
                except Exception as e:
                    print(f"bench state unavailable ({e}); assuming nothing is benched", flush=True)
                bench["t"] = now
            d = bench["state"].get(backend, {})
        return bool(d.get("backed_off")) and (d.get("remaining_sec") or 0) > 0

    def record(row, prompt=None, reply=None, proof=None, candidate=None, lean_out=None):
        with lock:
            with ledger.open("a") as fh:
                fh.write(json.dumps(row) + "\n")
        saved = sparebrains_attempt({**row, "prompt": prompt, "response": reply, "proof": proof,
                                     "candidate": candidate, "lean_output": lean_out}) or {}
        return f"  {SITE}/attempts/{saved['id']}" if saved.get("id") else ""

    def base_row(name, lane, attempt_no, statement_sha):
        return {"ts": datetime.now(timezone.utc).isoformat(timespec="seconds"), "run_id": run_id,
                "target_set": target_set, "target": name, "statement_sha": statement_sha,
                "backend": lane["backend"], "provider": lane["provider"], "model": lane["model"],
                "quality_tier": lane["tier"], "tier_rank": lane["rank"], "attempt_no": attempt_no, "mode": mode}

    def skip(name, lane, attempt_no, why):
        """A pair the router would refuse: recorded honestly, no model call, no Lean."""
        target_text = (tdir / f"{name}.lean").read_text()
        prefix = target_text[:PROOF_SEP.search(target_text).end()]
        row = {**base_row(name, lane, attempt_no, hashlib.sha256(prefix.encode()).hexdigest()),
               "verdict": "skipped", "reason": why, "call_seconds": 0.0, "lean_seconds": 0.0,
               "response_chars": 0, "proof_sha": None}
        with lock:
            state["skipped"] += 1
            t = per_target[name]
            t["done"] += 1
            target_done = (not args.stop_on_accept) and t["done"] >= planned_per_target
        record(row)
        print(f"[skip] {name} ← {lane['backend']} ({lane['tier']}): {why}", flush=True)
        if target_done:
            who = ", ".join(t["lanes"]) if t["lanes"] else "nobody"
            print(f"[target done] {name}: {t['accepts']}/{t['done']} lanes proved it ({t['errors']} lane errors) — {who}",
                  flush=True)

    def run_one(name, lane, attempt_no):
        """One attempt: ask (honoring retry-after once), splice, judge, record. Returns the verdict,
        or 'defer' when the router benched the lane between the pre-check and the call."""
        target_text = (tdir / f"{name}.lean").read_text()
        prefix = target_text[:PROOF_SEP.search(target_text).end()]
        statement_sha = hashlib.sha256(prefix.encode()).hexdigest()
        prompt = ASK + target_text
        t0 = time.monotonic()
        reply, err = "", None
        with provider_lock[lane["provider"]]:
            for tries in (1, 2):
                try:
                    reply, _ = llm_chat(lane["backend"], [{"role": "user", "content": prompt}],
                                        max_tokens=args.max_tokens, temperature=0.2, system=SYSTEM,
                                        app_name="sparebrains", timeout=(10, args.call_timeout),
                                        timeout_s=60)                   # router's per-attempt ceiling; 30 s default cuts slow proofs
                    err = None
                    break
                except KumoriAPIError as e:
                    msg = str(e)
                    if "spent its share" in msg or "is gated" in msg:
                        with lock:                        # the router's fair-share or pool gate: done for today
                            exhausted[lane["provider"]] = msg.split(" : ", 1)[-1][:120]
                        return "exhausted"
                    if "is benched" in msg:
                        return "defer"                   # the router's breaker tripped since the pre-check
                    limited = e.status_code == 429 or "rate limit" in msg.lower() or "RPM spacing" in msg
                    if tries == 1 and limited and e.retry_after and e.retry_after <= 90:
                        with lock:
                            state["waits"] += 1
                        time.sleep(e.retry_after + 0.5)   # the router said when; wait and ask once more
                        continue
                    err = f"KumoriAPIError: {msg[:200]}"
                    break
                except Exception as e:
                    err = f"{type(e).__name__}: {str(e)[:200]}"
                    break
        with lock:
            state["calls"] += 1
            n = state["calls"]
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
        row = {**base_row(name, lane, attempt_no, statement_sha), "verdict": verdict, "reason": reason[:300],
               "call_seconds": round(call_s, 1), "lean_seconds": round(lean_s, 1),
               "response_chars": len(reply or ""),
               "proof_sha": hashlib.sha256(proof.encode()).hexdigest() if proof else None}
        with lock:
            t, pl = per_target[name], per_lane[lane["backend"]]
            t["done"] += 1
            pl["attempts"] += 1
            if verdict == "accept":
                state["accepts"] += 1
                solved.setdefault(name, lane)
                t["accepts"] += 1
                pl["accepts"] += 1
                t["lanes"].append(lane["backend"])
            elif verdict == "error":
                state["errors"] += 1
                t["errors"] += 1
                pl["errors"] += 1
            target_done = (not args.stop_on_accept) and t["done"] >= planned_per_target
        link = record(row, prompt, reply, proof, candidate, lean_out)
        print(f"[{n}/{args.max_calls}] {name} ← {lane['backend']} ({lane['tier']}) → {verdict}  "
              f"call {call_s:.0f}s lean {lean_s:.1f}s  {reason[:110]}{link}", flush=True)
        if verdict == "accept":
            vpath = ROOT / "verified" / target_set / name / f"{lane['backend']}.lean"
            vpath.parent.mkdir(parents=True, exist_ok=True)
            vpath.write_text(candidate)
            print("    ┌ kernel-accepted proof, verbatim:\n" +
                  "\n".join("    │ " + l for l in proof.rstrip("\n").splitlines()) + "\n    └", flush=True)
        if target_done:
            t = per_target[name]
            who = ", ".join(t["lanes"]) if t["lanes"] else "nobody"
            print(f"[target done] {name}: {t['accepts']}/{t['done']} lanes proved it ({t['errors']} lane errors) — {who}",
                  flush=True)
        if n % 25 == 0:
            with lock:
                print(f"[tally] {n} calls · {state['accepts']} verified · {state['errors']} lane errors · "
                      f"{state['skipped']} skipped (benched) · {state['waits']} rate-limit waits · "
                      f"{len(solved)}/{len(names)} targets solved so far", flush=True)
        return verdict

    if args.stop_on_accept:                              # ladder: order matters, so sequential
        for name in names:
            for lane in order:
                if state["calls"] >= args.max_calls or name in solved:
                    break
                if lane["provider"] in exhausted:
                    skip(name, lane, 1, f"provider parked for the run: {exhausted[lane['provider']]}")
                    continue
                if benched(lane["backend"]):
                    skip(name, lane, 1, "lane benched by the router at the time of the ask")
                    continue
                for attempt_no in range(1, args.attempts + 1):
                    if state["calls"] >= args.max_calls:
                        break
                    v = run_one(name, lane, attempt_no)
                    if v == "defer":
                        skip(name, lane, attempt_no, "router benched the lane mid-ask")
                        break
                    if v == "exhausted":
                        skip(name, lane, attempt_no, f"provider parked for the run: {exhausted[lane['provider']]}")
                        break
                    if v == "accept":
                        break
            if state["calls"] >= args.max_calls:
                print(f"cap reached: {args.max_calls} calls")
                break
    else:                                                # sweep: a queue of pairs, providers interleaved
        lanes_rr = interleave_by_provider(order)
        work = deque((n, l, a) for n in names for l in lanes_rr for a in range(1, args.attempts + 1))
        if len(work) > args.max_calls:
            print(f"cap: {len(work)} planned attempts trimmed to {args.max_calls}")
            work = deque(list(work)[:args.max_calls])
        deferrals = defaultdict(int)

        def worker():
            while True:
                with lock:
                    if not work or state["calls"] >= args.max_calls:
                        return
                    item = work.popleft()
                    remaining = len(work)
                name, lane, a = item
                key = (name, lane["backend"], a)
                if lane["provider"] in exhausted:
                    skip(name, lane, a, f"provider parked for the run: {exhausted[lane['provider']]}")
                    continue
                if benched(lane["backend"]):
                    if deferrals[key] < 3 and remaining > 0:
                        deferrals[key] += 1               # try again after the rest of the queue
                        with lock:
                            work.append(item)
                        continue
                    skip(name, lane, a, "lane benched by the router for the whole run")
                    continue
                v = run_one(name, lane, a)
                if v == "exhausted":
                    skip(name, lane, a, f"provider parked for the run: {exhausted[lane['provider']]}")
                    continue
                if v == "defer":
                    if deferrals[key] < 3:
                        deferrals[key] += 1
                        with lock:
                            work.append(item)
                    else:
                        skip(name, lane, a, "router benched the lane mid-ask, three times")

        threads = [threading.Thread(target=worker, daemon=True) for _ in range(max(1, args.jobs))]
        for th in threads:
            th.start()
        for th in threads:
            th.join()
        if state["calls"] >= args.max_calls and work:
            print(f"cap reached: {args.max_calls} calls, {len(work)} pairs not attempted")

    calls, accepts = state["calls"], state["accepts"]
    print(f"done: {calls} calls, {accepts} accepts, {state['errors']} lane errors, {state['skipped']} skipped "
          f"(benched), {state['waits']} rate-limit waits honored, {len(solved)}/{len(names)} targets solved, "
          f"mode {mode}, run {run_id}")
    print("\nper target:")
    for n in names:
        t = per_target[n]
        first = solved.get(n)
        print(f"  {n:45s} {t['accepts']:3d}/{t['done']:3d} lanes  "
              f"{'first: ' + first['backend'] + ' (' + first['tier'] + ')' if first else 'unsolved so far'}")
    ranked = sorted(per_lane.items(), key=lambda kv: (-kv[1]["accepts"], -kv[1]["attempts"]))
    print("\nper lane:")
    for b, pl in ranked:
        if pl["attempts"]:
            answered = pl["attempts"] - pl["errors"]
            per_k = round(1000 * pl["accepts"] / answered) if answered else 0
            print(f"  {b:40s} {pl['tier']:9s} {pl['accepts']:3d}/{answered:3d} answered  "
                  f"({per_k} per 1,000, {pl['errors']} errors)")
    if exhausted:
        print("\nproviders parked during this run (fair-share or pool gate, resets at UTC midnight):")
        for prov, why in exhausted.items():
            print(f"  {prov}: {why}")
    print(f"\nsite: {SITE}/runs/{run_id}")
    out = os.environ.get("GITHUB_OUTPUT")
    if out:
        with open(out, "a") as fh:
            fh.write(f"calls={calls}\naccepts={accepts}\nlanes={len(order)}\ntargets={len(names)}\nmode={mode}\n")
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        with open(summary, "a") as fh:
            fh.write(f"### attempt run `{run_id}` — {mode}: {calls} calls, {accepts} verified, "
                     f"{state['errors']} lane errors, {state['skipped']} skipped as benched, "
                     f"{state['waits']} rate-limit waits, {len(solved)}/{len(names)} targets solved, $0 · "
                     f"[every transcript]({SITE}/runs/{run_id})\n\n")
            fh.write("| target | proved by (lanes) | of | first solver | tier |\n|---|---|---|---|---|\n")
            for n in names:
                t, l = per_target[n], solved.get(n)
                fh.write(f"| `{n}` | {t['accepts']} | {t['done']} | {l['backend'] if l else '—'} | {l['tier'] if l else '—'} |\n")
            fh.write("\n| lane | tier | verified | answered | per 1,000 | errors |\n|---|---|---|---|---|---|\n")
            for b, pl in ranked:
                if pl["attempts"]:
                    answered = pl["attempts"] - pl["errors"]
                    fh.write(f"| `{b}` | {pl['tier']} | {pl['accepts']} | {answered} | "
                             f"{round(1000 * pl['accepts'] / answered) if answered else 0} | {pl['errors']} |\n")
            if solved:
                fh.write("\n<details><summary>every kernel-accepted proof in this run</summary>\n\n")
                for vf in sorted((ROOT / "verified" / target_set).glob("*/*.lean")):
                    if vf.stat().st_mtime >= t_start:
                        fh.write(f"**{vf.parent.name} ← {vf.stem}**\n\n```lean\n{vf.read_text()}```\n\n")
                fh.write("</details>\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
