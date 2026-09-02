"""Materialize miniF2F statements as one .lean target per theorem.

Source: google-deepmind/miniF2F (Apache-2.0), the Lean 4 fork with misformalizations
removed; the version AlphaProof is evaluated on. Pinned to one commit so the target
set is reproducible. Only the Test split: Valid wraps 204 statements in the
`answer(...)` marker from google-deepmind/formal-conjectures, which this repo does
not depend on.

    python3 tools/import_minif2f.py        # rewrites targets/minif2f/test/*.lean
"""
import re, sys, urllib.request
from pathlib import Path

REPO = "google-deepmind/miniF2F"
SHA = "f0a20e14c1eeccd859d51bb4c2b3ee487889c303"   # main @ 2026-04-23
SPLITS = {"test": "MiniF2F/Test.lean"}
PREAMBLE = "import Mathlib\n\nopen scoped Nat\nopen scoped Real\n\n"
OUT = Path(__file__).resolve().parent.parent / "targets" / "minif2f"

NAME_RE = re.compile(r"^theorem\s+([A-Za-z0-9_']+)")
PROOF_SEP = re.compile(r":=\s*(?:by)?\s*\n")   # first `:=` at a line end = proof starts


def fetch(path):
    url = f"https://raw.githubusercontent.com/{REPO}/{SHA}/{path}"
    with urllib.request.urlopen(url, timeout=60) as r:
        return r.read().decode()


def blocks(src):
    """Yield (docstring, theorem_text) for every top-level theorem."""
    starts = [m.start() for m in re.finditer(r"^theorem ", src, re.M)]
    for i, s in enumerate(starts):
        e = starts[i + 1] if i + 1 < len(starts) else len(src)
        chunk = src[s:e]
        # the next theorem's docstring (if any) sits at the tail of this chunk
        parts = re.split(r"\n(?=/--)", chunk, maxsplit=1)
        thm = parts[0].rstrip()
        # this theorem's docstring is the tail of the previous chunk
        prev = src[starts[i - 1] if i else 0:s]
        m = re.search(r"(/--.*?-/)\s*$", prev, re.S)
        yield (m.group(1) if m else ""), thm


def main():
    total = 0
    for split, path in SPLITS.items():
        src = fetch(path)
        outdir = OUT / split
        outdir.mkdir(parents=True, exist_ok=True)
        for old in outdir.glob("*.lean"):
            old.unlink()
        names = set()
        for doc, thm in blocks(src):
            name = NAME_RE.match(thm).group(1)
            assert name not in names, f"duplicate {name}"
            names.add(name)
            sep = PROOF_SEP.search(thm)
            assert sep, f"no proof separator in {name}"
            statement = thm[:sep.start()].rstrip()
            body = (doc + "\n" if doc else "") + statement + " := by\n  sorry\n"
            (outdir / f"{name}.lean").write_text(PREAMBLE + body)
        print(f"{split}: {len(names)} targets from {REPO}@{SHA[:7]}:{path}")
        total += len(names)
    return total


if __name__ == "__main__":
    sys.exit(0 if main() else 1)
