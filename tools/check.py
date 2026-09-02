"""The judge. A .lean file is VERIFIED only if the kernel accepts it, no `sorry`
survives, and every theorem in it depends on nothing outside the axiom allowlist.

    python3 tools/check.py --expect accept checks/accept/*.lean
    python3 tools/check.py --expect reject checks/reject/*.lean

Exit 0 iff every file's verdict matches --expect. Runs `lake env lean` per file
(needs the lake workspace built and the mathlib cache present).
"""
import argparse, json, os, re, resource, subprocess, sys, tempfile, time
from pathlib import Path

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
DECL_RE = re.compile(r"^\s*(?:theorem|lemma)\s+([^\s:({\[]+)", re.M)
AXIOMS_RE = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]")
NO_AXIOMS_RE = re.compile(r"'([^']+)' does not depend on any axioms")


def judge(path, timeout):
    src = Path(path).read_text()
    names = DECL_RE.findall(src)
    if not names:
        return "reject", "no theorem or lemma declared", 0.0, ""
    probe = src.rstrip("\n") + "\n\n" + "\n".join(f"#print axioms {n}" for n in names) + "\n"
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as tmp:
        tmp.write(probe)
    t0 = time.monotonic()
    try:
        run = subprocess.run(["lake", "env", "lean", tmp.name], capture_output=True,
                             text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        os.unlink(tmp.name)
        return "reject", f"timeout after {timeout}s", time.monotonic() - t0, ""
    os.unlink(tmp.name)
    secs = time.monotonic() - t0
    out = (run.stdout + run.stderr).replace(tmp.name, path)
    if run.returncode != 0:
        first_error = next((l for l in out.splitlines() if "error" in l), out[:200])
        return "reject", f"lean exit {run.returncode}: {first_error.strip()}", secs, out
    if "declaration uses 'sorry'" in out:
        return "reject", "declaration uses sorry", secs, out
    audited = {n for n, _ in AXIOMS_RE.findall(out)} | set(NO_AXIOMS_RE.findall(out))
    missing = set(names) - audited
    if missing:
        return "reject", f"no axiom report for {sorted(missing)}", secs, out
    for name, axioms in AXIOMS_RE.findall(out):
        used = {a.strip() for a in axioms.split(",") if a.strip()}
        bad = used - ALLOWED_AXIOMS
        if bad:
            return "reject", f"{name} depends on disallowed axioms {sorted(bad)}", secs, out
    return "accept", f"kernel accepted {names}", secs, out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("files", nargs="+")
    ap.add_argument("--expect", choices=["accept", "reject"], required=True)
    ap.add_argument("--timeout", type=int, default=600)
    ap.add_argument("--verbose", action="store_true")
    args = ap.parse_args()

    rows, ok = [], True
    for f in args.files:
        verdict, reason, secs, out = judge(f, args.timeout)
        matched = verdict == args.expect
        ok &= matched
        rows.append((f, verdict, matched, secs, reason))
        print(json.dumps({"file": f, "verdict": verdict, "expected": args.expect,
                          "ok": matched, "seconds": round(secs, 1), "reason": reason}))
        if args.verbose or not matched:
            print(out, file=sys.stderr)

    peak_mb = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss // 1024
    print(f"peak child RSS {peak_mb} MB")
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        with open(summary, "a") as fh:
            fh.write(f"### expect `{args.expect}`  (peak child RSS {peak_mb} MB)\n\n")
            fh.write("| file | verdict | ok | s | reason |\n|---|---|---|---|---|\n")
            for f, v, m, s, r in rows:
                fh.write(f"| `{f}` | {v} | {'✅' if m else '❌'} | {s:.1f} | {r} |\n")
            fh.write("\n")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
