"""Label every `mathd_*` miniF2F target with its MATH difficulty level.

miniF2F's `mathd_*` problems were drawn from MATH (Hendrycks et al., NeurIPS 2021,
MIT license; 12,500 problems, each tagged `Level 1`..`Level 5` and a subject). Each
target file carries the informal statement as its docstring; this matches the
docstring to a MATH problem by text similarity and records the level.

    python3 tools/map_math_levels.py        # rewrites targets/minif2f/levels.json

Source: the Hugging Face datasets-server rows API for `EleutherAI/hendrycks_math`
(7 subject configs x train/test, 100 rows per page), cached page by page under
`_oneoff/math_dataset/` so a re-run is offline. Deterministic: a docstring's score
against every one of the 12,500 problems is difflib's SequenceMatcher ratio on
normalized text (LaTeX delimiters, `\\left`/`\\right`, spacing macros and whitespace
removed, lowercased). Only matches at or above THRESHOLD are labeled; the rest are
listed under "unmatched" with their best candidate for a human to decide.
"""
import difflib, json, re, sys, time, urllib.error, urllib.request
from pathlib import Path

DATASET = "EleutherAI/hendrycks_math"
CONFIGS = ["algebra", "counting_and_probability", "geometry", "intermediate_algebra",
           "number_theory", "prealgebra", "precalculus"]
SPLITS = ["train", "test"]
PAGE = 100                                    # the API's maximum page length
ROWS = ("https://datasets-server.huggingface.co/rows?dataset={ds}&config={cfg}"
        "&split={split}&offset={off}&length={n}")
THRESHOLD = 0.85
ROOT = Path(__file__).resolve().parent.parent
CACHE = ROOT / "_oneoff" / "math_dataset"
TARGETS = ROOT / "targets" / "minif2f" / "test"
OUT = ROOT / "targets" / "minif2f" / "levels.json"

DOC_RE = re.compile(r"/--(.*?)-/", re.S)
LEVEL_RE = re.compile(r"Level (\d)")


def get_json(url, tries=6):
    for i in range(tries):
        try:
            with urllib.request.urlopen(url, timeout=60) as r:
                return json.load(r)
        except urllib.error.HTTPError as e:
            if i == tries - 1:
                raise
            # the API allows roughly 100 requests per few minutes; a 429 clears in about a minute
            time.sleep(60 if e.code == 429 else 5 * 2 ** i)
        except OSError:                       # transport error: retry quickly
            if i == tries - 1:
                raise
            time.sleep(5 * 2 ** i)


def load_split(cfg, split):
    """All rows of one (config, split), from cache or the rows API."""
    path = CACHE / f"{cfg}_{split}.json"
    if path.exists():
        return json.loads(path.read_text())
    rows, off, total = [], 0, None
    while total is None or off < total:
        page = get_json(ROWS.format(ds=DATASET, cfg=cfg, split=split, off=off, n=PAGE))
        total = page["num_rows_total"]
        rows += [r["row"] for r in page["rows"]]
        off += PAGE
        print(f"  {cfg}/{split}: {len(rows)}/{total}", file=sys.stderr)
        time.sleep(2)                         # 125 pages for the whole set; be gentle with the quota
    assert len(rows) == total, (cfg, split, len(rows), total)
    CACHE.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(rows, ensure_ascii=False))
    return rows


def norm(s):
    s = s.replace("\\dfrac", "\\frac").replace("\\tfrac", "\\frac")
    s = re.sub(r"\\(left|right)\b", "", s)
    s = re.sub(r"\\[,;:! ]|\\q?quad\b|~", " ", s)     # LaTeX spacing
    s = re.sub(r"\\[\[\]()]|\$", "", s)                 # \[ \] \( \) $
    return re.sub(r"\s+", " ", s).strip().lower()


def top2(query, corpus):
    """Exact best two (ratio, index) over corpus. quick_ratio bounds ratio from above,
    so walking candidates in quick_ratio order and stopping once the bound drops below
    the current runner-up is exact, and avoids ~12k full alignments per target."""
    sm = difflib.SequenceMatcher(None, autojunk=False)
    sm.set_seq2(query)
    bounds = []
    for i, cand in enumerate(corpus):
        sm.set_seq1(cand)
        bounds.append((sm.quick_ratio(), i))
    bounds.sort(reverse=True)
    best = []
    for ub, i in bounds:
        if len(best) == 2 and ub < best[1][0]:
            break
        sm.set_seq1(corpus[i])
        best = sorted(best + [(sm.ratio(), i)], reverse=True)[:2]
    return best


def main():
    print(f"MATH from {DATASET} (cache {CACHE.relative_to(ROOT)}/)", file=sys.stderr)
    rows, where = [], []
    for cfg in CONFIGS:
        for split in SPLITS:
            for i, r in enumerate(load_split(cfg, split)):
                rows.append(r)
                where.append(f"MATH {cfg}/{split} #{i}")
    corpus = [norm(r["problem"]) for r in rows]
    print(f"{len(rows)} MATH problems", file=sys.stderr)

    matched, unmatched, ties, per_level = {}, {}, [], {}
    for path in sorted(TARGETS.glob("mathd_*.lean")):
        name = path.stem
        doc = DOC_RE.search(path.read_text())
        assert doc, f"{name}: no docstring"
        (r1, i1), (r2, i2) = top2(norm(doc.group(1)), corpus)
        row, r1, r2 = rows[i1], round(r1, 3), round(r2, 3)
        snippet = re.sub(r"\s+", " ", row["problem"])[:80]
        if r1 >= THRESHOLD:
            m = LEVEL_RE.fullmatch(row["level"])
            level = int(m.group(1)) if m else None      # MATH has a few "Level ?"
            matched[name] = {"level": level, "type": row["type"], "match": r1,
                             "source": where[i1], "problem": snippet}
            per_level[level] = per_level.get(level, 0) + 1
        else:
            unmatched[name] = {"best": r1, "source": where[i1], "candidate": snippet}
        if r2 >= r1 - 0.02:
            ties.append((name, r1, where[i1], r2, where[i2]))
        print(f"{name:28s} {r1:.3f} {where[i1]:36s} {row['level']:8s} {row['type']}",
              file=sys.stderr)

    out = dict(sorted(matched.items()))
    out["unmatched"] = dict(sorted(unmatched.items()))
    OUT.write_text(json.dumps(out, indent=1, ensure_ascii=False) + "\n")
    print(f"\n{len(matched)} matched at >= {THRESHOLD}, {len(unmatched)} unmatched -> "
          f"{OUT.relative_to(ROOT)}", file=sys.stderr)
    print("per level: " + ", ".join(f"L{k}={v}" for k, v in sorted(per_level.items(),
          key=lambda kv: (kv[0] is None, kv[0]))), file=sys.stderr)
    for name, r1, w1, r2, w2 in ties:
        print(f"near-tie: {name} {r1:.3f} {w1} vs {r2:.3f} {w2}", file=sys.stderr)
    return len(matched)


if __name__ == "__main__":
    sys.exit(0 if main() else 1)
