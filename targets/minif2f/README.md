# miniF2F targets

One `.lean` file per theorem, statement only, proof replaced by `sorry`. A target exists
here only if `.github/workflows/targets.yml` confirms it type-checks under this repo's pin
(Lean `v4.33.1`, mathlib `v4.33.1`) with `sorryAx` as its sole hole.

| | |
|---|---|
| Source | [google-deepmind/miniF2F](https://github.com/google-deepmind/miniF2F), commit `f0a20e14c1eeccd859d51bb4c2b3ee487889c303` (main, 2026-04-23) |
| Upstream of that | [openai/miniF2F](https://github.com/openai/miniF2F) (Lean 3), ported with mathport, misformalizations removed, docstrings added. The version AlphaProof is evaluated on. |
| License | Apache-2.0, see `LICENSE` in this directory. Copyright (c) 2021 OpenAI; changes by Google DeepMind and by this repo. |
| Splits | `test/` (244). `valid/` is not imported: 204 of its statements use the `answer(...)` marker from google-deepmind/formal-conjectures, a package this repo does not depend on. |
| Regenerate | `python3 tools/import_minif2f.py` (deterministic; pinned commit). |

## Changes from the source (Apache-2.0 §4b)
- `MiniF2F/Test.lean` split into one file per theorem, named after the theorem.
- `import MiniF2F.ProblemImports` replaced by `import Mathlib`; `open scoped Nat` and
  `open scoped Real` carried over from the source preamble.
- Every proof replaced by `sorry`, including the two the source proves
  (`mathd_numbertheory_66`, `mathd_algebra_302`).
- The source pins mathlib `v4.27.0`; these files are checked against `v4.33.1`.

## Baselines, for context only
Published pass rates are on the original statements (openai / yangky11 port), not this
corrected set, and use whole-proof provers with large sample budgets. From the
miniF2F-v2 paper's table (arXiv 2511.03108, Nov 2025), on the original `test` split:
DeepSeek-Prover-V2-7B 73.4%, Goedel-Prover-V2 82.0%, Kimina-Prover-Distill-7B 65.2%.
The free pool here is general chat models at a few attempts per statement; expect far less.

## MATH difficulty levels (`levels.json`)
The 130 `mathd_*` statements are problems from the MATH dataset (Hendrycks et al., NeurIPS
2021), which carries a published difficulty label per problem, `Level 1` (easiest) to
`Level 5`, plus a subject. `levels.json` records that label for each `mathd_*` target, keyed by
theorem name: `{"level": 3, "type": "Algebra", "match": 1.0, "source": "MATH algebra/test #31",
"problem": "<first 80 chars of the matched problem>"}`. Targets whose best match falls under
the threshold go under a top-level `"unmatched"` key with the best candidate, for a human to
decide. The number in a theorem name is not a MATH row index.

| | |
|---|---|
| Dataset | [`EleutherAI/hendrycks_math`](https://huggingface.co/datasets/EleutherAI/hendrycks_math) on Hugging Face: the MATH dataset, 12,500 problems, 7 subject configs × train/test, read through the datasets-server rows API and cached under `_oneoff/math_dataset/` (gitignored) |
| License | MIT (the dataset card; `LICENSE` in [hendrycks/math](https://github.com/hendrycks/math), copyright 2021 Dan Hendrycks) |
| Method | `python3 tools/map_math_levels.py`. Each target's docstring is scored against all 12,500 problems with difflib `SequenceMatcher.ratio()` on normalized text (`$`, `\(`, `\[`, `\left`/`\right`, LaTeX spacing macros and whitespace stripped, `\dfrac`→`\frac`, lowercased). Best match wins at ratio ≥ 0.85. Deterministic; a re-run is offline once the cache exists. |
| Result (2026-09-02) | 130 of 130 matched, 0 unmatched. 129 at ratio 1.000; `mathd_numbertheory_321` at 0.996 (one space). Every match is in MATH's **test** split: Algebra 70, Number Theory 60. |
| Per level | Level 1: 25 · Level 2: 25 · Level 3: 25 · Level 4: 25 · Level 5: 30 |
| Near-ties | Three, each a MATH pair that shares a template and differs by a number, at the same level: `mathd_algebra_156` (algebra/test #263 at 1.000 vs #976 at 0.981), `mathd_numbertheory_277` (number_theory/test #210 vs #415) and `mathd_numbertheory_711` (#415 vs #210), both 1.000 vs 0.986. The label is unaffected. |

Citation, as given on the dataset card and in the paper's repository:
```bibtex
@article{hendrycksmath2021,
  title={Measuring Mathematical Problem Solving With the MATH Dataset},
  author={Dan Hendrycks and Collin Burns and Saurav Kadavath and Akul Arora and Steven Basart and Eric Tang and Dawn Song and Jacob Steinhardt},
  journal={NeurIPS},
  year={2021}
}
```
