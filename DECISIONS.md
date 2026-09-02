# DECISIONS — the settled ledger

Dated, with receipts. Re-open one only with new evidence; otherwise it stands.
Everything NOT here is open and lives in `PLAN.md` §6.

## 2026-09-01 (evening)

- **Nothing runs locally. All cloud.** Arm B (a prover model on the ROG GPU) is dropped and the
  ROG leaves this project entirely. Andy: "I don't want anything to run locally." The local
  prover stays a question for `kumori/code/PLAN_local_llm_lane.md`, not here.
- **The verifier is GitHub Actions on the public repo.** Standard runner for public repos:
  4 vCPU, 16 GB RAM, 14 GB SSD, free minutes with no cap, 20 concurrent jobs, 6 h per job,
  10 GB Actions cache per repo. Private repos on the Free plan get 2 vCPU, 8 GB and 2,000
  min/month. Receipts: docs.github.com runner specs + Actions limits pages, 2026-09-01.
  `leanprover/lean-action` v1.6.0 installs elan and pulls the mathlib olean cache, which comes
  from mathlib's own server, not the Actions cache. Built: `.github/workflows/check.yml`.
- **Attempts are ledger commits, not PRs; the ledger lives in git.** PRs opened by
  `github-actions[bot]` run no workflows until a human approves (changelog 2026-06-11), so a
  bot-opened attempt PR never self-verifies. From 2026-10-01 workflow runs, checks and statuses
  expire on the 90-day retention default (changelog 2026-08-27), so run history is not a ledger.
  Verification happens inside the job; the result is committed. This is
  `tillo13/mr_beast_puzzle_private`'s `daily_sources.yml` shape, which already existed.
- **Public under `tillo13/sparebrains` from day one.** Supersedes "private until the first
  artifact" above. Reason: the runner and minutes table. The transfer to kumori-ai after the
  first verified artifact is unchanged; an org holding one CI hello-world is the storefront trap.
- **"Verified" means, mechanically:** `lake env lean` exits 0, no `declaration uses 'sorry'`,
  and `#print axioms` for every theorem in the file is a subset of
  `{propext, Classical.choice, Quot.sound}` (this catches `sorryAx` and smuggled `axiom`s).
  Implemented in `tools/check.py`; exercised by `checks/accept/*` (must pass) and
  `checks/reject/*` (sorry, a smuggled axiom, a false statement; all must be refused).
  Statement byte-identity to the target is added when targets exist (step 2).
- **Lane one is math: Lean-checked proofs, miniF2F as the calibration floor.** Science and
  space fail `TARGETS.md`'s fit filter (methods you build, not LLM calls); code bounties need
  a human gate; forecasting is verified by reality weeks later and was already out of v1.
  Lean over the counterexample hunt because the artifact is unimpeachable, a target list and
  published baselines exist, and the Actions+mathlib setup is reused by every later math lane.
- **Pins: Lean `v4.33.1`, mathlib `v4.33.1`** (commit `0df444a3`), the same pin
  `google-deepmind/formal-conjectures` carries on 2026-09-01, so its statements load without a
  toolchain bump. `lake-manifest.json` was derived from mathlib's own manifest at that tag.
- **GitHub Models is retired (2026-07-30).** No free LLM exists inside GitHub; the kumori router
  is the only propose side. Three sources: changelog 2026-07-01 and 2026-07-30, docs landing
  page. Four router lanes still point at it (kumori cleanup, logged in `PLAN.md` §6).
- **GitHub Agentic Workflows is an intake tool, not the engine.** Public preview 2026-06-11,
  `github/gh-aw` v0.87.10. Every engine accepts a custom base URL (`ANTHROPIC_BASE_URL` /
  `OPENAI_BASE_URL`), so it can run against code.kumori.ai at $0. Deferred until strangers file
  targets. The propose→check loop is plain Python.
- **Two live kumori API keys were scrubbed from `PLAN.md` §1** before the repo went public.
  They had been pasted as caller labels; `kumori_free_llms.py:235` shows they are keys.
- **Step 1 is green.** `tillo13/sparebrains` run 33577335558: 2 min 47 s end to end, 4.6–7.1 s
  per check with `import Mathlib`, 6.6 GB peak RSS, 6.5 GB mathlib cache, $0. Two accepts
  accepted; a `sorry`, a smuggled `axiom`, and a false statement all refused for the stated
  reasons. Numbers in `PLAN.md` §2. Steps 2–4 remain gated.
- **Step 2 is green: the target set is google-deepmind/miniF2F, Test split, 244 statements.**
  Chosen over yangky11/miniF2F-lean4 (unmaintained, original misformalizations) and
  miniF2F-v2 (jsonl only, no Lean project). All 244 type-check under mathlib v4.33.1 with
  `sorryAx` as the sole hole; zero edits needed. One file per theorem in
  `targets/minif2f/test/`, Apache-2.0 with license and change list in `targets/minif2f/README.md`.
  Valid split excluded: 204 of its statements use `answer(...)` from formal-conjectures.
  `tools/check.py --expect wellformed` is the gate; run 33578810121.
- **The judge reads `sorryAx` from the kernel's axiom audit, never the warning text.** Lean
  v4.33 prints "declaration uses `sorry`" with backticks; a text match on the old quoting let a
  `sorry` proof through on run 33578565414. The reject suite caught it. Now the only sorry
  signal is `#print axioms`.

## 2026-09-01

- **Name: `sparebrains` / `sparebrAIns`.** Machine identifiers lowercase: App Engine and Cloud
  Run require it, PEP 8 expects it, the fleet has zero capitalized project folders, and GitHub
  resolves repo URLs case-insensitively (verified: `TILLO13/KUMORI` → `tillo13/kumori`), so a
  mixed-case repo name would be a permanent paper cut on a case-insensitive APFS volume.
  Stylized form wherever a human reads it. Rejected: sieve, nightshift, idlehands, sparecycles,
  proofhound, crucible, lemming, spareai.
- **Name clearance (deep-search, 2026-09-01).** One US mark ever existed: SPAREBRAINS, serial
  75945170 / reg. 2423507, SLSoftware and Consulting Services LLC, class 9 "information
  management software for computers", registered 2001-01-23, **cancelled 2007-10-27 under
  Section 8** (two sources: Justia, Bizapedia). Exact-string search of Justia's USPTO index
  returns that one record only. Not checked: EUIPO/WIPO, state marks, USPTO directly (its API
  needs a key; its search is JS-only). Common-law users, none in software or AI: Spare Brains
  Games (board-game publisher, BGG 5644), a WordPress placeholder, gaming/art handles, a 2012
  album. Domains: `.com` registered 2023-05, parked for sale (Afternic); `.org` registered
  2023-07, serves nothing; **`.ai` and `.io` unregistered**; `.dev` unknown. GitHub: user
  `sparebrains` and org `Sparebrainss` both created 2017-10, zero repos, dormant; no repo by the
  name anywhere. npm and PyPI names free. Reddit: zero on-topic threads across three harvests.
- **Home = `~/Desktop/code/sparebrains/` on the Mac; its own top-level project.** kumori is the
  private infra hub (`tillo13/kumori`, isPrivate=true); a public repo cannot be a folder inside
  it. pilgrims_world and kindness_social are the pattern: apps on the substrate, each its own
  repo with `cron.yaml` + `deploy.json`, consuming a synced `kumori_api_client`. The ROG holds a
  pointer stub only (`Q:\studio_dev\20260831_ai_for_good_free_lane\PLAN.md`), the same pattern
  as the local-LLM lane. The one piece that belongs INSIDE kumori: the live lane-health
  dashboard route, because only kumori sees pool health.
- **Repo posture: private under tillo13 until the first verified artifact exists, then a
  GitHub transfer to kumori-ai** (transfer keeps history). Git via `deploy --git-only`, never
  raw git. Why: an empty plan-only repo on the public org is the storefront-before-product trap.
- **Milestone 1 is a yield measurement, not the engine.** `PLAN.md` §2. Every downstream
  choice (substrate, turn-down, lane order, org shape) depends on verified-per-1,000-calls,
  which nobody has measured.
- **kindness_social and pilgrims_world stay as they are.** Live 7-day numbers (`PLAN.md` §1):
  pool ≈2,300/day, not 5,400; self-play ≈1,500/day, not 3,600; OpenRouter ≈570 of its 1,000.
  The provider-exhaustion case for a turn-down was built on a pool that no longer exists, and
  the bots are currently the only steady canary traffic. Revisit after the yield gate.
- **quality_judge pre-check: answered.** Router tier ordering reads only
  `judge_kind='heuristic_v1'` canary rows
  (`kumori/shared/kumori_free_llm/kumori_free_llms.py:1618`). kindness (`kindness_live_v1`,
  `kindness_rerank_v1`, `kindness_imgembed_v1`) and pilgrims write into the same
  `kumori_llm_quality_samples` table under their own judge kinds, which the router ignores.
  A turn-down cannot blind routing. (BRAINSTORMS.md §3 assumed kindness never wrote to the
  catalog; wrong in detail, right in conclusion.)
- **Docs moved, not copied.** `plan.md` → `BRAINSTORMS.md` (verbatim), `bounties.md` →
  `TARGETS.md` (verbatim, renamed to the public vocabulary). Byte-exact on arrival
  (34,213 / 12,541), then a provenance header added to each.

## 2026-08-31 (carried from `BRAINSTORMS.md` §16–17)

- **github.com/kumori-ai org exists.** Created 21:54, org id 323345833, free plan, `tillo13`
  admin, 0 repos. The only real-world artifact so far.
  **⚠ Pending Andy click: set the org's Copilot per-user budget to $0** so the free org has
  zero billable surface.
- **GitHub is the product; kumori.ai is the narrative.** Issues = target queue (Issue Forms),
  PRs = attempts, Actions CI = the oracle at PR granularity, README scoreboard regenerated
  nightly, Discussions = the forum, Projects board = state. Landing = org profile README or
  GitHub Pages with `good.kumori.ai` CNAMEd to it. No separate website.
- **Money posture (README sentence, never revisited):** no money flows through the project;
  contributors keep their prizes; anything paid to the org's own accounts is donated to a
  named recipient and logged; the org never funds bounties itself. Recipient: OPEN.
- **Attribution inversion (scoped exception).** The global no-AI-attribution rule stays intact
  for product repos. In THIS repo every engine result or attempt must disclose model / lane /
  method / cost via the ASF `Generated-by:` commit trailer, not `Co-Authored-By`. Written into
  `CLAUDE.md`.
- **Vocabulary:** never "bounty" in public unless money is attached. "Open problems",
  "targets", "scoreboard".
- **Contribution policy:** issues-only for strangers first; PRs later, CI-gated;
  `CONTRIBUTING.md` modeled on the allowed + disclosure-required + human-in-loop cluster
  (Airflow, Arrow, Django, cilium DCO). Lines to steal: curl's "worth more than the review
  time"; Ghostty's "not anti-AI, anti-unqualified".
- **Ordering on the org page:** the engine leads; pilgrims / kindness / kumori.ai appear below
  as provenance, never as the lead.
