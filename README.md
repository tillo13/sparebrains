# sparebrAIns

**Idle free-tier compute → machine-verified public artifacts.**

The kumori free-LLM pool (60+ free-tier backends behind one router) spends most of its
~2,300 calls/day on bots grading bots. sparebrAIns points that spare capacity at work whose
output a machine can check (a proof kernel, a test suite, a scoring function), so every call
either produces something verified or is honestly recorded as a miss, in full, for the next
attempt to build on. Nothing false survives; nothing learned is thrown away.

| | |
|---|---|
| Story, scoreboard, every transcript | sparebrains.kumori.ai (read-only pages on the kumori app) |
| Code, queue, ledger | github.com/tillo13/sparebrains (public; moves to the kumori-ai org after the first verified artifact) |
| Status 2026-09-02 | **first kernel-verified proof landed** (`amc12_2000_p12`, run 33582595117). Steps 1–3 of milestone 1 built; the loop is running. Earlier: the verifier runs in GitHub Actions and 244 miniF2F targets type-check under it. No model has been asked anything yet. Milestone 1 is a measurement, not an engine (`PLAN.md` §2). |

## Read in this order
1. `DECISIONS.md`: what's settled, dated, with receipts. Don't re-litigate.
2. `PLAN.md`: the yield gate, lanes, verifier, what's not in v1, what's still open.
3. `TARGETS.md`: where machine-checkable problems live (math, forecasting, code, science).
4. `BRAINSTORMS.md`: the original three-session braindump, verbatim, for provenance.

## Verified means
A `.lean` file counts only if all three hold, checked by `tools/check.py` on a GitHub-hosted
runner with Lean `v4.33.1` and mathlib `v4.33.1`:
1. `lake env lean` exits 0 (the kernel accepted it);
2. no `declaration uses 'sorry'`;
3. `#print axioms` for every theorem is within `propext`, `Classical.choice`, `Quot.sound`.

`checks/accept/` must pass and `checks/reject/` (a `sorry`, a smuggled `axiom`, a false
statement) must be refused on every run of `.github/workflows/check.yml`. No proof is graded by
eye, and no model grades another model.

## The name
`sparebrains` in every machine identifier (folder, repo, package, service, caller tag).
`sparebrAIns` wherever a human reads it. Spare AI brains, put to work. The pun is also the
honest part: free-tier models are spare parts, and the verifier is what makes that fine.

## Money
No money flows through this project. Prizes won by contributors are theirs; anything paid to
the org's own accounts is donated to a named recipient and logged here. The org never funds
bounties itself.

## Provenance
Built on the kumori free-LLM substrate (`kumori/shared/kumori_free_llm`) that also runs
pilgrims_world and kindness_social. Those apps are how the substrate got built; this is what
its spare capacity does now.
