# DECISIONS — the settled ledger

Dated, with receipts. Re-open one only with new evidence; otherwise it stands.
Everything NOT here is open and lives in `PLAN.md` §6.

## 2026-09-02

- **Loop, second version (before the first scheduled run).** Andy: "I want it to work super
  well." Four changes, all in `tools/attempt.py`: bench state re-checked before every attempt
  (cached 30 s) and benched pairs deferred to the back of the queue up to three times, then
  recorded as `skipped` with no call made; consecutive calls interleaved across providers so 28
  Mistral lanes are never walked back to back; a per-provider lock so two workers never hit one
  provider at once; the router's retry-after honored once on a rate limit instead of counting a
  dead attempt. Sweep mode is now a work queue with daemon workers rather than a fixed map.
  Proven on a stubbed harness (benched, mid-run bench, rate limit, prose reply, accept path)
  before shipping; the real proof is the 22:00 run's error count against sweep 1's 479.
- **Sweep 1 closed: 241 verified proofs on 17 of 30 targets, 1,050 attempts, $0.** The
  per-lane number exists now: the best free lanes return about one accepted proof per two
  answered asks on this exam paper (`PLAN.md` §2). Nearly half of attempts were lost to
  lanes benched mid-run; re-checking bench state per attempt moves up to the next loop change.
  The 13 unsolved are the IMO items, late AMC/AIME problems, and a few algebra identities:
  the "not yet" list. Ledger commit `ce7df0e`. 20 of 244 targets verified across all runs.
- **Unsolved means not yet, never never.** Andy: "the ones that'll never be solved — that's
  exactly my challenge and hope here, that we WILL solve them at some point … saving
  thoughts/theories/equations that are close or help others learn from them or iterate on
  them. That's EXACTLY my hope, not a 'never' thing." The planning docs said "honestly
  discarded" (README, TARGETS.md §Tier-1 mechanics, BRAINSTORMS.md §6); that phrase is now
  "honestly recorded as a miss, in full." Mechanically nothing changes: every attempt was
  already kept whole in `sparebrains_attempts`. What changes is the framing on the site and
  in the digest, and the priority of Phase B (Lean's error fed back, more tries, a closeness
  signal so the nearest misses surface first).
- **Runs on the roadmap need no per-run go.** Andy: "why would you need a go from me? of
  course go, that's the whole point." Deploys and outward changes still get the disclosure
  line first.
- **Do them all: the nightly schedule.** Andy: "do them all to see if we can solve all them,
  it's free, and no reason not to." The one constraint is the shared pool's per-provider daily
  caps that pilgrims and kindness lean on by day, so the full pass runs at night: the attempt
  workflow fires at 22:00 and 03:00 Pacific (Actions' timezone cron), each firing a sweep of
  the next 30 targets no sweep has touched (`--unattempted`, alphabetical), lanes from medium
  up, benched lanes skipped, two attempts in flight, cap 1,400 calls. About four nights for
  244. Sweep mode runs (target, lane) pairs in parallel; ladder mode stays sequential because
  its early stop depends on order. First chunk launched by hand: run 33586743955 (30 targets,
  seed 2).
- **Run 3 closed: 4 kernel-verified proofs on 5 sampled targets, 137 attempts, $0.** Three by
  `mistral-devstral` (medium), one by `openrouter-openrouter-free` (low, on its 14th lane).
  Tiny and low tiers: 1 accept in 70 attempts. High and frontier: 0 in 35, but 21 of those 35
  were benched-lane errors on the one unsolved target, so their yield is unmeasured, not zero.
  Numbers and the ledger commit (`045c9b2`, sparebrains-bot, `Generated-by:` trailer) in
  `PLAN.md` §2. Next per §7: the sweep run.
- **The first verified artifact exists.** Run 33582595117, target `amc12_2000_p12` (AMC 12,
  2000, #12), accepted by the kernel from lane `mistral-devstral` (medium tier) after eighteen
  tiny/low lanes failed it. 3.1 s model reply, 6.3 s Lean check, $0. This opens the storefront
  gate in `PLAN.md` §7: the site and the org transfer are no longer blocked.
- **The public site is sparebrains.kumori.ai, served by the kumori app, read-only.** Andy:
  "all this documentation on how it works and what to click must be written on
  sparebrains.kumori.ai so everyone knows everything about it." Pages: overview (totals,
  latest verified proofs, runs), how it works (the full explainer), lanes (verified per 1,000
  calls), targets (cheapest tier that solved each), a page per run, a page per attempt with the
  full transcript. Rendered from `sparebrains_attempts`; aggregates cached 60 s. Extends
  kumori's own `base.html` (nav, theme toggle, fonts, main.css) per Andy: "keep the style css js
  like the current kumori.ai page." Code: `kumori/blueprints/sparebrains_site_bp.py`,
  `kumori/templates/sparebrains/`, `kumori/static/css/sparebrains.css`.
- **Subdomain plumbing.** DNS: CNAME `sparebrains` → `ghs.googlehosted.com` (TTL 600) on
  kumori.ai's GoDaddy zone, written by the new `kumori/utilities/godaddy_utils.py` (creds
  `GODADDY_API_KEY`/`GODADDY_API_SECRET` in kumori-404602 Secret Manager; the API answered 200
  for this account). App Engine domain mapping created, managed certificate pending on DNS.
  A WSGI middleware in kumori `main.py` maps the subdomain onto the blueprint's `/sparebrains`
  prefix so URLs stay clean; the same pages also answer at kumori.ai/sparebrains/.
- **Git keeps the verifiable half, Postgres keeps the whole story.** Failed attempts' transcripts
  live only in the table by design (size); the site is the only place a human reads them.
  Publishing raw model outputs is a provider output-use question; math with no PII is the easy
  case, flagged, not yet read clause by clause.
- **Step 3 shape: the loop is a GitHub job that is one more caller on the kumori router.**
  Shared client vendored via deploy.json `shared_files` like pilgrims; key in the repo secret
  `KUMORI_API_KEY`, which the client reads first. Caller attribution `app_name=eval:sparebrains`.
- **Router key minted for `sparebrains`:** `kumori_api_keys` id 62,
  scopes `llm.chat, llm.read, catalog.read, sparebrains.write`, owner key, tier experiment,
  cap 2000 (telemetry only for owner keys). Plaintext lives only in kumori-404602 Secret Manager
  as `SPAREBRAINS_KUMORI_API_KEY` (same naming as PILGRIMS_/KINDNESS_) and in the repo secret.
- **Lanes are walked by quality tier, Andy's ladder.** The router labels every lane
  tiny/low/medium/high/frontier. `--order asc --stop-on-accept` asks the cheapest brains first
  and stops a target at its first kernel-verified proof, so the ledger records the lowest tier
  that solved it. `--order desc` reverses; without `--stop-on-accept` every lane gets every
  target (the per-lane yield measurement). Both are the same script.
- **Show your work: every attempt's full transcript goes to Postgres.** Table
  `sparebrains_attempts` on the shared instance, owned by `kumori/blueprints/sparebrains_bp.py`,
  written through `POST /api/v1/sparebrains/attempt` (scope `sparebrains.write`), because the
  runner must never reach Cloud SQL directly. Columns include prompt, response, extracted proof,
  the exact file handed to Lean, and Lean's output. Git keeps the compact ledger
  (`ledger/<set>/<run_id>.jsonl`) and every accepted proof whole (`verified/<set>/<target>/<lane>.lean`).
  The DB post is fire-and-forget so a telemetry outage never stops a run.
- **Ledger commits carry the `Generated-by:` trailer** (lanes, verifier, cost $0) per the
  attribution-inversion rule; the workflow commits as `sparebrains-bot`.
- **Hard guards on the loop:** `--max-calls` stop, one progress line per call in the job log,
  1 s pacing between router calls, 180 s per call, 300 s per Lean check, first run watched.

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
