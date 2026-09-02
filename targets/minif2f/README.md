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
