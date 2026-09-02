> **Moved 2026-09-01** from `Q:\studio_dev\20260831_ai_for_good_free_lane\bounties.md` (ROG) to
> `~/Desktop/code/sparebrains/TARGETS.md` (Mac, the canon). Renamed to the public vocabulary
> (DECISIONS.md: never "bounty" unless money is attached); content verbatim. `plan.md` referenced
> below is now `BRAINSTORMS.md`. Point-in-time 2026-08-31: re-verify any entry the week you act on it.

# bounties.md — where free LLM compute could actually help (math · science · space)

**Written:** 2026-08-31, from a live deep-search session (web fan-out + Reddit scrapes).
**Companion to:** `plan.md` in this folder (the thinking doc; §11–15 = same session).
**Point-in-time warning:** prize amounts, deadlines and "live" statuses below are 2026-08
snapshots. Re-verify any entry the week you act on it.

## THE FIT FILTER (apply before adding anything to this list)

The kumori free pool's shape: thousands of weak-model calls/day, bursty, async-tolerant,
near-zero marginal cost, already wired for web+PDF+image. It can NOT out-think frontier
models. Its only edge is **massive cheap parallel generation** — which is worth something
ONLY where a **mechanical verifier** separates right from plausible-wrong:

> A target belongs on this list iff: (1) output is machine-checkable (proof kernel, test
> suite, scoring function, resolved reality), (2) work is async/daily-grindable, (3) entry
> is free and permitted for automated systems, (4) no PII.

Anything failing the filter is listed under NOT-FITS so we stop re-discovering it.

---

## TIER 1 — MATH (perfect verifiers; the pool's true home)

### erdosproblems.com — the registry
- **What:** 1,217 Erdős problems, 570 solved (47%), forum, prizes page. Very alive: a wave
  of 2026 status flips; blog literally has "Problem 728 and the use of AI on Erdős problems"
  (Jan 2026) and "Erdős, aliens, and evil spirits" (Jun 2026).
- **Why us:** the target queue for proof-search. AI is already scoring here: problem 90
  solved by an OpenAI internal model (May 2026); Astra closed 183/146/180 with Lean 4
  certificates (Aug 2026, github.com/openai/ten-proofs).
- **Bounty?** The literal Erdős cash tradition ($100–$3,000+/problem; Ron Graham
  administered, presumably Fan Chung continues — Quanta "Cash for Math," r/math mn7bfq).
  Symbolic money; real payoff is the status flip with your name on it.
- **How we'd help:** nightly cron feeds open problems (weighted toward combinatorics /
  graph-theory, where finite counterexamples live) into generate→verify. See Tier-1
  mechanics below.

### vibemathed.com — the scoreboard ⭐ (best find of the session)
- **What:** community-curated record of math problems **first solved with AI in the loop**.
  643 tracked · 453 fully resolved · 8,916 combined years-open closed · **136 Lean-verified**.
  Per-entry verification ladder (site-confirmed → expert-verified), AI-discovered tags,
  significance scores, votes, **disclosed-cost field**, CC-BY dataset, GitHub, Discord, RSS.
- **Why us:** this is the exact arena. Entries like "Dean's conjecture for k=5" (last open
  case, under review this week) show the cadence: small named problems falling weekly.
  A free-pool result has a place to be SUBMITTED, reviewed, and counted — the public,
  durable-artifact property the whole ai_for_good thesis wants. The disclosed-cost field is
  tailor-made for our punchline: "solved on $0 of free-tier compute."
- **How we'd help:** (a) mine its open/under-review entries + RSS as a live target feed;
  (b) submit anything our loop verifies; (c) their CC-BY dataset = calibration for what
  AI-solvable looks like.

### The existence proof — amateurs on subscriptions are already scoring (added same day)
- **Liam Price, 23, no advanced math training, cracked a 60-year-old Erdős conjecture**
  (the primitive-sets sum limit — Lichtman and others got stuck on it) **with a single
  prompt to GPT-5.4 Pro on a ChatGPT Pro subscription**, posted to erdosproblems.com.
  Terence Tao on it: humans "collectively made a slight wrong turn at move one"; experts
  say the method looks genuinely NEW, possibly reusable — the rarest kind of AI-math result.
  (Scientific American, 2026-04-24, Joseph Howlett.)
- So the 2026 Erdős wave is substantially hobbyists + subscriptions, not just labs —
  vibemathed's disclosed-cost field exists to track exactly this.
- **Economics, stated honestly (so nobody chases the wrong thing):** the prize money does
  NOT pay for subscriptions. Math bounties are symbolic and rarely claimed; Metaculus pools
  split among funded bot-makers; OSS bounties are a race. What the community means by "pays
  for itself" is the **sub-vs-API arbitrage** (r/ClaudeAI 1pi2zct: $950/week API before Max;
  ~$6,500 would-be API in 2-3 months on a $200 sub). Also note: providers are fencing the
  grind-your-flat-sub pattern (reported June 2026: Anthropic split programmatic/Agent-SDK
  usage into its own credit pool — single blog source, verify before relying on it).
- **Why this matters for US:** our version needs no arbitrage — free lanes at $0 + a local
  rung with no meter and no ToS dependency. Price is the proof the upside is real; the
  engine just industrializes the aiming. The payoff currency is the scoreboard, not cash —
  which is the point (the goal here is humanity-good, not income).

### github.com/google-deepmind/formal-conjectures — the pre-formalized target queue
- **What:** open conjectures already STATED in Lean 4 (statements, not proofs) — Millennium
  problems through Erdős items.
- **Why us:** kills the hardest part of autoformalization for the famous targets — the
  statement already exists; the pool only has to hunt proofs/counterexamples against a
  fixed formal goal. Plus **mathlib's** backlog of known-but-unformalized math = the volume
  lane (plan.md §5's honest niche; PRs to mathlib are the deliverable).

### The computer-search counterexample lane (no registry — a *style* of target)
- **What:** conjectures whose refutation is ONE finite checkable object. Precedents:
  Hedetniemi's conjecture (2019, small graph, Quanta), Hadwiger–Nelson chromatic-number-5
  (Aubrey de Grey, 2018 — an *amateur* + computer search), the July 2026 Jacobian-conjecture
  counterexample (Alpöge + Claude, a 216-char polynomial — verified community-wide in a day),
  vibemathed's Albertson–Berman entry ("the refutation is a single finite object").
  Maps of the territory: MathOverflow "eventual counterexamples" (mo/15444), r/math qy4bwo,
  math.SE 514, OEIS.
- **Why us:** counterexample hunting is embarrassingly parallel and self-verifying — the
  checker is a few lines of code, no Lean required. Cheapest possible entry into Tier 1.
- **How we'd help:** pool proposes candidate objects/constructions; a local checker (SAT/SMT
  or plain Python) verifies; only survivors surface. FunSearch pattern (which produced
  genuinely new cap-set results) is the prior art.

### Big-ticket math prizes (context, not targets)
- Clay **Millennium Prize Problems** — $1M each (claymath.org). **Beal Conjecture — $1M**
  (AMS-held). Reality per plan.md §6: not our weight class; listed so nobody re-asks.

**Tier-1 mechanics (shared):** target feed (erdosproblems + vibemathed RSS + formal-conjectures)
→ nightly propose cron on free lanes → verifier (Lean sandbox for proofs; plain checkers for
counterexamples) → ledger of attempts → human review → submit (vibemathed / mathlib PR /
erdosproblems forum). Every call ends as verified-true or honestly-discarded. This doubles as
canary traffic (plan.md §11).

---

## TIER 2 — FORECASTING (real prize money, bot-native, live now)

### Metaculus AI Forecasting Benchmark / FutureEval bot tournaments
- **What:** bot-ONLY tournaments, explicitly no-human-in-the-loop, **$50,000 per season**,
  bi-weekly rounds + MiniBench. Spring 2026 ran; Summer 2026 live (metaculus.com/aib/2026/spring ·
  /tournament/spring-aib-2026 · EA Forum announcement Dec 2025).
- **Why us:** the single closest thing to "free lanes plug away daily for money." Questions
  open/close on an external schedule → natural canary cadence. And the method that works —
  multi-model ensemble, disagreement-as-signal, calibration — IS plan.md §6's tertiary build.
  The router is already a forecasting-bot substrate.
- **How we'd help (honest version):** better public forecasts are a mild public good; the
  real returns are (a) dependable canary traffic, (b) a scored external benchmark of the
  pool's collective judgment, (c) lottery-ticket prize share vs well-funded bot-makers.
- **Caveats:** verifier = reality (weeks feedback); check each season's model/API rules.

---

## TIER 3 — CODE / OSS (real money, test-suite verifiers, HUMAN GATE MANDATORY)

### Algora.io + curated paid-issue lists
- **What:** OSS bounty board (/bounty $X comments on GitHub issues); curated
  GITHUB_PAID_ISSUES lists (upd. 2026-03); "win bounties in 2026" guides on dev.to.
- **Why us:** test suites = decent oracle; overnight lanes can draft candidate patches.
- **HARD CAVEATS:** first-mergeable-PR race; maintainers openly hostile to AI-slop
  submissions (curl's ban on AI-generated reports is the emblem). **Only viable as:
  lanes draft → Andy reviews → Andy submits.** Never autonomous — an unreviewed PR
  firehose is the OPPOSITE of helping. Volume must stay tiny and quality-gated.

---

## TIER 4 — BIOMED / SCIENCE BENCHMARKS (leaderboards, not grind-lanes)

### openproblems.bio — Open Problems in Single-Cell Analysis
- **What:** 13 formalized benchmarks (batch integration, perturbation prediction, label
  projection…), each with gold-standard datasets, metrics, continuously updated leaderboard.
- **Fit:** verifier exists (metrics), but entries are *methods you build*, not LLM calls —
  this is Andy-the-engineer work, not pool-grinding. Park unless a benchmark task turns
  out to be promptable.

### DREAM Challenges (Sage Bionetworks)
- **What:** 30,000-solver community benchmarking biomedical predictive models; decades of
  challenges. Notable 2026 twist: a Feb 2026 paper benchmarks *LLMs writing the analysis
  code* for DREAM tasks — the LLM-shaped door is opening.
- **Fit:** same as above — competitions for model-builders; watch for LLM-native editions.

### NIH / NCATS challenge programs + NCI citizen-science portal
- **What:** government prize competitions (nih.gov/challenges), health/cancer adjacent.
- **Fit:** episodic, human-team shaped. Watch list, not a lane.

---

## TIER 5 — SPACE (inspiration-grade; almost none of it is LLM-shaped)

- **NASA Tournament Lab / HeroX** — real crowdsourced prizes (Venus rover clock, Watts on
  the Moon, 2022 Mars life-evidence data challenge). Episodic engineering/design comps;
  HeroX live list is JS-walled — check herox.com directly when curious.
- **NASA Space Apps Challenge** — annual global hackathon (spaceappschallenge.org). Fun,
  human-shaped, weekend-scale — actually plausible as an Andy+tools outing.
- **SETI reality check** (the "finding aliens screensaver" = **SETI@home**, 1999–2020, now
  hibernating): modern SETI is ML over Breakthrough Listen archives; the volunteer lane is
  GPU/CPU donation, not LLM calls. Zooniverse (1B classifications, Aug 2026) wants human
  judgment — using AI there violates the spirit/rules.

---

## APPENDIX — THE OTHER LEVER (not the LLM pool): GPU-cycle donation

Separate resource, same "idle capacity → good" instinct: **Folding@home**, **BOINC**
(Einstein@home — has found real pulsars; Rosetta@home), **World Community Grid** (cancer
projects, e.g. Mapping Cancer Markers — r/bioinformatics gzncy5). The 5060 Ti's idle cycles
could run these tonight with zero build — BUT it contends with renders (VRAM/GPU-exclusive
box) and with any local-LLM-lane plans. A decision for the local-lane project, not this one.

## NOT-FITS (so we stop re-litigating)
- Vesuvius Challenge ($1.84M awarded; $1M grand + $2M bounties live) · ARC Prize 2026 ($2M)
  · DrivenData ($5M+ lifetime) · AIMO Progress Prize 3 ($2M+, Kaggle) — all "Andy competes
  with skills/hardware" engineering competitions, not pool-grinding. AIMO is the closest to
  tempting; it's offline Kaggle submission, so the pool can't play.
- Security bug bounties — authorization + slop; hard no.
- Zooniverse & citizen-science classification — human-judgment by design.

## FIRST MOVES (when this gets picked up — matches plan.md §13)
1. Metaculus Summer/Fall FutureEval bot — cheapest live wedge, prize attached, §6-tertiary
   ensemble design already on paper.
2. Counterexample-hunt loop on erdosproblems/vibemathed targets — cheapest Tier-1 entry
   (plain checkers, no Lean sandbox yet).
3. Lean sandbox → autoformalization volume lane — the deep build.
4. Before any of it: the quality_judge check + kindness/pilgrims turn-down (plan.md §3).
