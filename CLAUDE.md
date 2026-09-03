# sparebrains (`sparebrAIns`) — project rules

Idle free-tier compute → machine-verified public artifacts. Read `DECISIONS.md`, then
`PLAN.md`, before doing anything. `BRAINSTORMS.md` is provenance, not instructions.

## Rules specific to this project
- **Each step of `PLAN.md` §2 (the yield gate) needs its own green light from Andy.** Step 1,
  the verifier in GitHub Actions, was green-lit and built 2026-09-01. The first deliverable is
  a measurement, not an engine.
- **Free-lane only.** Paid Claude "Reserve" is off limits here without explicit written
  permission each time (the kumori `CLAUDE.md` invariant). Every run's commit names the pool and the verifier versions.
- **The kernel is the judge.** A result exists only if the verifier accepted it. No
  LLM-judged "verified". No proofs graded by eye.
- **Attribution inversion (scoped exception to the global no-AI-attribution rule).** Engine
  results and attempts committed to THIS repo must disclose model / lane / method / cost via
  the ASF `Generated-by:` commit trailer. Everything else, including planning and doc commits,
  follows the global rule (no AI trailer). Product repos elsewhere are unchanged.
  Receipt: `BRAINSTORMS.md` §16 item 5 and §17; `DECISIONS.md` 2026-08-31.
- **Vocabulary in anything public:** open problems, targets, scoreboard. Never "bounty"
  unless money is attached.
- **Show the work, verbosely, always (Andy, 2026-09-02).** Every computed number on the site or in
  the docs carries its equation with the live inputs substituted (the ETA, the pace, per 1,000,
  "clears a rung", the leaderboard order). Nothing computed appears bare. Charts derive from
  `sparebrains_attempts` / `sparebrains_jobs` in Postgres, never from a hand-made number.
- **Machine identifiers are `sparebrains`, lowercase, everywhere.** `sparebrAIns` only where
  a human reads it.
- **Nothing runs locally or on the ROG** (`DECISIONS.md` 2026-09-01 evening). Verification is
  GitHub Actions; generation is the kumori router over HTTPS.
- **Docs move, never copy.** The ROG folder `Q:\studio_dev\20260831_ai_for_good_free_lane\`
  is a pointer stub only. ROG-side work for this project lands in a dated `Q:\studio_dev\`
  dir when green-lit, under the studio's ROG rules (visible window, telemetry, no timeouts).
- Scratch → `_oneoff/`. Ship via `deploy --git-only "msg"`, never raw git.

## Substrate
`kumori/shared/kumori_free_llm` (router; `docs/LIFECYCLE.md`, `docs/CAPACITY.md`) and a synced
`kumori_api_client`, as in pilgrims_world and kindness_social. Caller tag for this project:
`sparebrains` for every real run (35% fair share of each provider pool); `eval:sparebrains`
only for throwaway checks (the router treats `eval:` as test traffic, 15% share).
