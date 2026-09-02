# sparebrAIns

**Idle free-tier compute → machine-verified public artifacts.**

The kumori free-LLM pool (60+ free-tier models behind one router) sits idle most of the day.
sparebrAIns points that spare capacity at competition mathematics written in Lean 4 and lets
the Lean proof kernel, not a person and not another model, decide what counts. Every call
either produces a kernel-verified proof or is honestly recorded as a miss, in full, for the
next attempt to build on. Nothing false survives; nothing learned is thrown away. Cost: $0.

| | |
|---|---|
| Live scoreboard, every run, every transcript | **https://sparebrains.kumori.ai** |
| How it works, in full | https://sparebrains.kumori.ai/how |
| Why, where the problems come from, the plan, how to check every claim | https://sparebrains.kumori.ai/about |
| Code, targets, ledger, verified proofs | this repository |

## What is happening right now
- **The exam paper.** `targets/minif2f/test/`: 244 competition problems (AMC, AIME, IMO,
  textbook algebra and number theory) in Lean 4, from DeepMind's corrected miniF2F fork, one
  file per theorem with `sorry` as the only hole. All 244 type-check under this repo's pin.
- **The judge.** `tools/check.py` compiles a file with Lean and audits its axioms. Accepted
  means: compiles, statement untouched, only the three standard axioms. `checks/` must pass
  and be refused, respectively, on every push (`.github/workflows/check.yml`).
- **The loop.** `tools/attempt.py`, run by `.github/workflows/attempt.yml` on GitHub's free
  runners: ask each model lane for a proof, splice it under the original statement, hand it to
  the judge, record everything. Ladder mode asks the cheapest lanes first; sweep mode asks
  every lane so each gets a real score.
- **The schedule.** Two sweep chunks a night (22:00 and 03:00 Pacific) over whatever targets
  no sweep has touched yet, until all 244 are covered. Then the same loop points at open
  problems (`PLAN.md` §7).
- **The record.** Every attempt's full transcript goes to a Postgres table behind kumori's
  API (the site renders it). This repo keeps the compact ledger (`ledger/`) and every
  accepted proof whole (`verified/`), committed by the workflow with a `Generated-by:` trailer.
- **The digest.** One email a day: first-time solves, last night's runs, the lane scoreboard.

## Verified means
A `.lean` file counts only if all three hold, checked by `tools/check.py` on a GitHub-hosted
runner with Lean `v4.33.1` and mathlib `v4.33.1`:
1. `lake env lean` exits 0 (the kernel accepted it);
2. its only hole marker, `sorryAx`, is absent from the axiom audit;
3. `#print axioms` for every theorem is within `propext`, `Classical.choice`, `Quot.sound`.

No proof is graded by eye, and no model grades another model. Unsolved means not yet.

## Check the work
- A run: its line-per-attempt file under `ledger/`, its commit on the commits page (author
  `sparebrains-bot`), its job log under Actions (kept 90 days), its page on the site.
- A proof: the file under `verified/<set>/<target>/<lane>.lean`. Re-check it yourself:
  ```
  git clone https://github.com/tillo13/sparebrains && cd sparebrains
  curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
  lake exe cache get && lake build
  python3 tools/check.py --expect accept verified/minif2f/test/amc12_2000_p12/mistral-devstral.lean
  ```
- A decision: `DECISIONS.md`, dated, with receipts. Open items: `PLAN.md` §6. The plan: §7.
- Secrets: none in this repository or its history. The router key lives in a GitHub Actions
  secret and reaches the loop only as an environment variable.

## Read next
1. `DECISIONS.md`: what's settled, dated, with receipts. Don't re-litigate.
2. `PLAN.md`: the yield gate, the measured numbers, what's not in v1, what's open, the plan.
3. `TARGETS.md`: where machine-checkable problems live (math, forecasting, code, science).
4. `BRAINSTORMS.md`: the original three-session braindump, verbatim, for provenance.

## The name
`sparebrains` in every machine identifier (folder, repo, package, service, caller tag).
`sparebrAIns` wherever a human reads it. Spare AI brains, put to work. The pun is also the
honest part: free-tier models are spare parts, and the verifier is what makes that fine.

## Money
No money flows through this project. Prizes won by contributors are theirs; anything paid to
the org's own accounts is donated to a named recipient and logged here. The org never funds
prizes itself. Every run costs $0 and says so in its commit.

## Provenance
Built on the kumori free-LLM substrate (`kumori/shared/kumori_free_llm`) that also runs
pilgrims_world and kindness_social. Those apps are how the substrate got built; this is what
its spare capacity does now. Targets: google-deepmind/miniF2F, Apache-2.0
(`targets/minif2f/README.md`). Verifier: Lean 4 + mathlib via leanprover/lean-action.
