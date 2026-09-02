# PLAN — sparebrAIns

**Status 2026-09-02: §2 steps 1–3 are built (verifier, targets, loop). First loop run in
flight; first verified proof landed (`DECISIONS.md` 2026-09-02). §7 storefront gate is open. Earlier: §2 step 1 is built. The verifier runs in GitHub Actions
(`.github/workflows/check.yml`, `tools/check.py`). Steps 2–4 of §2 each need their own
green light. Decisions taken today: `DECISIONS.md` 2026-09-01 (evening).**
Point-in-time: every number here was measured on the day stated; re-derive before acting.

## 0. Root

Idle free-tier compute → machine-verified public artifacts. The free pool cannot out-think
frontier models; its only edge is massive cheap parallel generation, which is worth something
ONLY where a mechanical verifier separates right from plausible-wrong. Pool proposes, oracle
disposes, only truth survives. Machinery already owned: the kumori router (multi-model
fan-out), crons + workers (the kindness / pilgrims pattern), web/PDF/image input, GitHub as
the interface.

Two invariants. **Free-lane only:** paid Claude "Reserve" is off limits without explicit
written permission each time (kumori `CLAUDE.md`). **No PII:** the math and fact lanes carry
none; that is part of why they were chosen.

## 1. Live capacity (measured 2026-09-01 from `kumori_llm_daily_caps`, 08-26 → 08-31)

| caller | calls/day |
|---|---|
| pilgrims_world tick engine (its own router key) | 850–1,000 |
| kindness_social direct + eval (its own router key) | 440–680 |
| pool self-checks: llm_canary, quality_judge, admin_health, health_probe | ≈600 |
| galactica | ≈98 |
| **total** | **2,200–2,400** |
| OpenRouter pool, of its 1,000/day cap | ≈570 |

Read: reclaimable self-play ≈1,500/day, not the 3,600 in `BRAINSTORMS.md`. A quarter of the
pool is the pool checking itself. Nothing is saturating. 09-01 itself ran hot (3,944 by
mid-afternoon; mistral 1,723 against a 52/day norm all week; the code cites the 07-12 mistral
org death as why monthly token caps exist). Cause unknown, flagged, not chased.

Consequence: this is a hobby-scale engine. Expectations are set against ~1,500 calls/day of
weak models. That is why the yield gate exists.

## 2. MILESTONE 1 — the yield gate (the only thing that gets built first)

**Question:** verified proofs per 1,000 calls, on the target class we would actually run.
Nobody has this number. Every other decision in this file depends on it. `BRAINSTORMS.md` §6
says the checker makes model weakness free; it makes weakness *safe* (nothing false survives),
not free (a near-zero hit rate spends the whole quota on nothing).

**Shape: a measurement, not the engine.**
- **Targets:** the same 20–50 for both arms. Candidate sources: textbook lemmas absent from
  mathlib; `google-deepmind/formal-conjectures` statements (already in Lean 4); miniF2F-style
  items as a calibration floor. Final list: OPEN (§6).
- **Arm A, free pool:** the kumori router as-is, N attempts per target with Lean error
  feedback between attempts. Caller tagged `eval:sparebrains` so it lands in the existing
  caller-share and quality accounting.
- **Arm B — DROPPED 2026-09-01 (evening), `DECISIONS.md`: nothing runs locally.** Kept for
  the record: local specialized prover on the ROG: a 7–8B Lean-trained prover on the 5060 Ti.
  Candidates from recollection, verify current releases and benchmarks before picking:
  DeepSeek-Prover-V2 7B, Goedel-Prover-V2 8B, Kimina-Prover 8B. Same targets, same attempt
  budget. Runs under the studio's ROG rules: visible window, telemetry sidecar, no timeouts.
- **Verifier:** Lean 4 + mathlib, resident checker (§4). A proof counts only if the kernel
  accepts it with no `sorry` and the statement is byte-identical to the target.
- **Metric:** verified per 1,000 calls per arm; wall time per verified proof; the $0 receipt
  (no paid lane touched). The kernel is the judge; nobody grades proofs by eye.

**Decision table (the outcome gets written into `DECISIONS.md`):**

| outcome | what it decides |
|---|---|
| A clearly > 0 | the free-pool Lean lane is real; build the generate-verify cron on the router |
| A ≈ 0, B > 0 | proof search is a ROG GPU job; the free pool does statements / ensemble / forecast; the local-prover lane merges here (§6) |
| both ≈ 0 on known lemmas | Lean is not lane one; the counterexample hunt with plain checkers (`TARGETS.md` Tier 1) is the next thing to measure |

With Arm B dropped only rows 1 and 3 remain. Step order (2026-09-01 evening): (1) prove the
checker in Actions, (2) the miniF2F Lean 4 target set, pinned to the same mathlib, (3) the
propose→check→ledger loop in the same job, (4) nightly schedule for a week.

**Step 1 measured (run 33577335558, 2026-09-02 00:56 UTC, public-repo `ubuntu-latest`):**

| item | measured |
|---|---|
| whole job | 2 min 47 s |
| elan + mathlib cache (8,690 files, 6.5 GB) + `lake build` | 2 min 17 s |
| one check (`lake env lean` incl. `import Mathlib`) | 4.6–7.1 s |
| peak RSS of one check | 6.6 GB |
| runner | 4 vCPU, 15 GiB RAM, 145 GB disk (75 GB free after mathlib) |
| verdicts | 2 accept, 3 reject, all as expected; `sorryAx` and a smuggled `axiom` both caught |
| cost | $0 |

Read: ~5 s per check means a few hundred attempts per job without a resident Lean server.
The 6.6 GB peak rules out the private-repo 8 GB runner; public was the right call.

**Step 2 measured (run 33578810121, 2026-09-02 01:17 UTC):** `targets/minif2f/test/`, 244
statements from google-deepmind/miniF2F `f0a20e1` (their pin mathlib v4.27.0), all 244
well-formed under mathlib v4.33.1 with `sorryAx` as the only hole. 3.4–3.8 s per statement,
two in parallel, 9 min for the split, 6.6 GB peak. Zero statements needed editing. Valid split
not imported (204 statements use formal-conjectures' `answer(...)`). Also found on the way: the
judge's first version keyed on Lean's `sorry` warning text, which v4.33 quotes differently; it
now reads `sorryAx` from `#print axioms`, and the reject suite is what caught it.

## 3. Lanes, and the substrate each one fits

| lane | verifier | substrate | status |
|---|---|---|---|
| Lean proof search on known-but-unformalized results | Lean kernel (perfect) | gated by §2; likely the ROG prover | measure first |
| Autoformalization of *statements* (NL → Lean statement) | type-check + expert review | free pool (a language task; diversity helps) | after §2 |
| Counterexample hunt (one finite object refutes a conjecture) | plain checker / SAT-SMT | free pool or ROG | cheapest Tier-1 entry; second thing to measure |
| Ensemble consensus, disagreement as signal | cross-model + sources (weak) | free pool (its natural shape) | v2 |
| Metaculus FutureEval bot | reality, weeks later | free pool | not v1 (§5) |
| OSS bounties | test suites | free pool drafts → Andy reviews | not v1 (§5) |

The free pool's edge (diversity, breadth, web) fits the language-shaped rows. The proof-search
inner loop is a specialist's job. Twenty weak models agreeing is shared bias, not truth, so
there is no row where the pool is its own judge.

## 4. The verifier at two granularities

- **Resolved 2026-09-01 (evening):** GitHub Actions on the public repo is the checker at both
  granularities until the loop outgrows it. Attempts are ledger commits, not PRs (bot-opened
  PRs get no CI without human approval since 2026-06-11). Original text kept below.
- **Inner loop (thousands per day):** a resident Lean server (REPL or Pantograph-style) with
  mathlib loaded once, on the ROG or a worker. Never one `lake build` per attempt, never one
  Actions job per attempt. Where it lives: OPEN (§6). Lean + mathlib is heavy on RAM and the
  olean cache; the ROG has the RAM, but the GPU is exclusive with renders. A CPU-only Lean
  checker coexists with a render; a prover model does not.
- **Outer gate (per PR):** GitHub Actions on the public repo. Standard-runner minutes are free
  for public repos, and `lake exe cache get` makes a check minutes rather than hours. Green
  check = verified; stranger slop fails without human time. This is what `BRAINSTORMS.md` §16
  meant by "CI is the oracle": correct at PR granularity, wrong for the inner loop.

## 5. Not in v1 (decided, so nobody re-discovers them)

- **Metaculus bot.** Contradicts the root: reality-verified, mild public good, lottery ticket.
  Fine as a later daytime-canary lane. Season rules and whether new bots are still accepted
  for Summer/Fall 2026: unverified.
- **OSS bounties.** Human-gate overhead, first-mergeable-PR race, maintainer hostility.
- **mathlib PRs as the deliverable.** Puts us on the wrong side of our own anti-slop policy;
  mathlib's bottleneck is review, naming and placement, not proof existence. The deliverable
  is the public ledger of kernel-checked proofs plus vibemathed entries; a mathlib PR only
  for the rare one a human judged worth a maintainer's hour. mathlib's AI-contribution
  policy: check before any PR.
- **Turning kindness / pilgrims down.** §1 numbers. Revisit after §2.
- **Dashboards, org README, CONTRIBUTING, issue forms, the Pages site.** Storefront. After
  the first verified artifact.
- **Any web code.** GitHub's native features plus one read-only route in kumori cover every
  interaction.

## 6. Open (survives this rewrite)

- [x] ~~The 20–50 targets for §2~~ `targets/minif2f/test/` (244, all well-formed). The loop
      picks a fixed sample; "already in mathlib" does not apply to competition statements.
- [x] ~~Where the resident Lean checker runs~~ GitHub Actions (`DECISIONS.md` 2026-09-01 evening). Was: ROG (CPU-only, coexists with renders) or a Cloud
      Run worker (the pilgrims burn/ward pattern). Needs a real RAM and olean-cache answer.
- [x] ~~Prover model for Arm B~~ moot, Arm B dropped. Was: verify current releases and benchmarks; VRAM fit on 16 GB.
- [x] ~~Local-prover lane merge~~ stays in the local-LLM lane; nothing local here. Was: does it merge into sparebrains or stay in the local-LLM lane
      (`kumori/code/PLAN_local_llm_lane.md`)? Decided by §2's outcome.
- [ ] Donation recipient for the money-posture sentence (Lean FRO / mathlib, Folding@home,
      Internet Archive; Andy picks).
- [ ] Success metric v2: verified count, upstreamed count, scoreboard entries.
- [ ] mathlib AI-contribution policy; Metaculus season rules. Both unverified.
- [ ] Copilot budget → $0 on the org (Andy click).
- [ ] The 09-01 mistral spike (§1): what drove 1,723 calls against a 52/day norm.
- [ ] kumori cleanup, not this repo: GitHub Models retired 2026-07-30; four router lanes still
      point at it (`kumori_free_llm/config.yaml` 247–262). §1 pool numbers exclude them already.
- [x] ~~Which Lean 4 port of miniF2F~~ google-deepmind/miniF2F (Apache-2.0, corrected, the
      AlphaProof eval set); yangky11's port is unmaintained and carries the original errors.
- [ ] Subdomain: `sparebrains.` vs `spare.` vs `good.kumori.ai`. Storefront item, after the gate.

## 7. After the gate (outline only; each step is its own green light)

1. Write §2's outcome into `DECISIONS.md`.
2. The generate-verify loop as a cron on whichever substrate won: caller-tagged, telemetry
   on, every attempt ledgered as verified / rejected / error. The ledger IS the product.
3. First verified artifact → repo transfers to kumori-ai, README scoreboard goes up, and only
   then the storefront items in §5.
