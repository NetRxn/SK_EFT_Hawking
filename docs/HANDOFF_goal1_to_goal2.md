# Handoff — goal 1 → goal 2

**Branch:** `infra/adr-009-validation-modularization`, committed, clean tree, **NOT merged**.
**Written:** 2026-08-09, at the close of goal 1.

Goal 1 was: close the 30 enumerated `ARCHITECTURE_TODOs` items, get three bundle gates
green, pass the full pr-review-toolkit suite, leave the branch green and unmerged. Goal 2
owns the wave-pipeline reviewer stages, the merge, and the manuscript programme.

---

## 1. What goal 1 closed

**All 38 D-items in `docs/architecture/.working-docs/ARCHITECTURE_TODOs.MD` are closed as
findings — with one OPEN remainder, stated here because a heading-scanner would miss it:**

> **D4 carries an OPEN remainder.** Ledger coverage is 361/361, but its *perishability
> queue* is not executed and carries into goal 2. The D4 heading says so explicitly
> (`✅ 100% (361/361) COVERED; ⚠️ the perishability queue is OPEN`) — a phrasing the closure
> reviewer chose precisely so a scanner would not read D4 as wholly closed. This document
> was that scanner, and claimed "None is left OPEN" one commit after the heading was written.

Sixteen of the 38 were wrong about their own scope, premise or remedy, and **five** named a
hazard or blocker that did not exist: D1 (WITHDRAWN), D17, D36, D37 (CLOSED-NOT-A-DEFECT), and
**D28 — whose heading reads `✅ DONE` while its body records "THIS ENTRY'S LOAD-BEARING HAZARD
DOES NOT EXIST"**. Each is recorded in the entry with the measurement that refuted it, not
silently dropped.

⚠️ This count was wrong twice — three, then four — and both times for the same reason: it was
taken by scanning DISPOSITION LABELS rather than the claims. D28's label says DONE. That is the
instrument failure this handoff and `ARCHITECTURE_TODOs` both diagnose elsewhere, committed
here in the sentence that reports the diagnosis.

Load-bearing outcomes goal 2 should know about:

| | |
|---|---|
| **D26 / F-02** | A source registration no longer creates a `\section`. `bundle_append.py` takes `--target-section`; `--new-section` needs a written rationale. The section plan is read off the draft, so there is **no `CHARTER.md` to author** — that dependency is retired. |
| **D27 / F-07** | The Lean freshness trigger is live for all 21 bundles. It keys on **last commit time**, not mtime — the audit's mtime proposal is rejected on evidence and ADR-010 §Open item 4 is resolved. |
| **D35** | The AGP recursion is derived, not defined. `steane_concatenated_failure_below_threshold` reaches both the measure-theoretic and real-valued halves in one closure. |
| **D21** | `D9 ∩ I3` = **11** (was 0). D9's consumption claim is true in the substrate; D9 and I3 drafts both say so. |
| **F-03** | 40 figure deferrals declared across 11 bundles — the first use of the mechanism the pipeline law has mandated all along. |

---

## 2. Per-bundle Stage 9 / 10 / 13 / §7.5 status — **all pending**

**No bundle has a green reviewer stage, and that is by design.** Goal 1's out-of-scope
clause deferred Stages 9, 10, 13 and §7.5 to goal 2 because the installed `skeft-qa`
plugin is stale. Nothing in goal 1 advanced a reviewer stage; several bundles were
*flagged for re-review* because their content changed.

| Bundle | Tier | s9 | s10 | s13 | redo required | readiness | pp |
|---|---:|---|---|---|---|---|---:|
| F | 0 | pending | pending | pending | **yes** | RED | 24 |
| D1 | 1 | pending | pending | pending | **yes** | RED | 11 |
| D2 | 1 | pending | pending | pending | **yes** | RED | 11 |
| D3 | 1 | pending | pending | pending | **yes** | RED | 58 |
| D4 | 1 | pending | pending | pending | **yes** | RED | 32 |
| D5 | 1 | pending | pending | pending | no | RED | 14 |
| D6 | 1 | **not_started** | **skeleton** | pending | **yes** | YELLOW | 8 |
| D7 | 1 | **not_started** | pending | pending | **yes** | RED | 4 |
| D8 | 1 | pending | pending | pending | **yes** | YELLOW | 9 |
| D9 | 1 | pending | pending | pending | **yes** | **UNMEASURED** | 12 |
| D10 | 1 | pending | pending | pending | **yes** | YELLOW | 5 |
| D11 | 1 | pending | pending | pending | **yes** | RED | 9 |
| D12 | 1 | pending-redo | pending-redo | pending-redo | **yes** | RED | 11 |
| L1 | 2 | pending | pending | pending | **yes** | RED | 4 |
| L2 | 2 | pending | pending | pending | no | RED | 4 |
| L3 | 2 | pending | pending | pending | no | RED | 4 |
| I1 | 3 | pending | pending | pending | no | RED | 23 |
| I2 | 3 | pending | pending | pending | no | RED | 15 |
| I3 | 3 | pending | pending | pending | **yes** | RED | 19 |
| E1 | 4 | pending | pending | pending | no | RED | 5 |
| E2 | 4 | pending | pending | pending | **yes** | YELLOW | 5 |

**§7.5 (prose read-through):** never run for any bundle. The `prose-reviewer` agent exists
in the repo but **not in the installed plugin** — see §4.

⚠️ **D9's readiness is `UNMEASURED`, not YELLOW or GREEN.** It was the portfolio's only
GREEN before goal 1, reached with its Stage 10 never run. The distinction is now
representable and D9 sits in it. Do not read `UNMEASURED` as a mild YELLOW.

---

## 3. What goal 2 must run

1. **Refresh or work around the plugin** (§4), then run Stages 9 → 10 → 13 in that order.
   The Stage-9-and-10-before-13 hard gate is enforced by `bundle_reviewer_stage_ordering`;
   a Stage-13 verdict recorded ahead of them fails the check.
2. **Clear the 15 `stage13_redo_required` flags** by re-review, not by editing the field.
   (This note said 14 until the closure reviewer counted 15 — its own §2 table listed 15
   all along, so the prose contradicted the table beside it.)
3. **The manuscript programme.** `bundle_manuscript_length` reports **11 bundles under
   floor** — F needs 80pp and has 24; D7 needs 24 and has 4. The gate PASSES on that
   (under-floor is advisory by operator decision — see §5); the 11 gaps are the work.
   ⚠️ **That count requires a fresh compile.** Run
   `uv run python scripts/compile_bundle_pdf.py --all --force` first: the check reports
   `UNMEASURED` for any bundle whose PDF predates its `\input` closure, and adding a
   shared input already in the closure staleness-invalidates every bundle that carries it
   at once — `docs/counts.tex` reaches 16 of the 21, and goal 1's own
   `docs/figuredeferred.tex` reaches 11, not all 21. Measured stale, the same check reported 3 under floor and 16 UNMEASURED —
   the closure reviewer saw exactly that and was right to flag the discrepancy.
   ⚠️ **A stale tree now FAILS `--ci` rather than passing quietly**: the unmeasured
   population folds into the check's `measured`, so staleness reads as `74 MEASURED,
   floor 75` instead of a green tick over part of the corpus. That is deliberate — the
   gate could otherwise degrade from 11 reported gaps to 1 and stay green. The
   per-bundle `pp` column in §2 is likewise only meaningful on a freshly compiled tree. This is goal 2's headline
   deliverable and is roughly 150 pages of new physics manuscript plus the figures behind
   the 40 deferrals. **No floor was lowered and no `length_target` was nulled** — see §5.
4. **Merge to main** once the above is green, with the full suite and a clean
   `rm -rf .lake/build && lake build SKEFTHawking.ExtractDeps`.

---

## 4. The plugin decision goal 2 faces

The installed `skeft-qa` plugin is **stale against the repo**: 8 agents installed vs the
repo's 9, `prose-reviewer` absent entirely, and `figure-reviewer` / `claims-reviewer` /
`adversarial-reviewer` differing by 14 / 26 / 17 lines. Running Stage 9, 10 or 13 through
the installed copy runs a **stale contract**, which is why goal 1 deferred them rather
than running them against the wrong brief.

Two routes, and goal 2 must pick one **explicitly**:

* **Refresh the plugin cache** so the installed agents match the repo, then dispatch
  normally. Procedure: `docs/dev-loops/HARNESS_GUIDE.md`, the cache-refresh section.
* **Fall back to `general-purpose` agents carrying the repo's agent briefs**, reading each
  `.claude/plugins/skeft-qa/agents/*.md` from disk as the operating prompt. This is what
  goal 1 did for five of the six pr-review-toolkit agents (only `code-simplifier` was
  registered as a subagent type), and it worked — the agents found real defects including
  a security control failing open. It is the lower-risk route if the cache refresh is
  awkward, and it does **not** require the plugin to be correct.

Whichever is chosen, record it. A reviewer stage run against a stale brief and a reviewer
stage not run are different states, and only one of them is recoverable by re-running.

---

## 5. Gate state at handoff — and the one that stays red on purpose

`validate.py`: **77 of 79 pass.** The two that do not:

> ⚠️ Verified by running the suite, not asserted. A first draft of this note said
> 77/79 before the run and the run said 76 — E2's trim had added a companion
> self-citation with no `CITATION_REGISTRY` entry, and the inventory needed a
> resync. Both are fixed; the number below is the measured one.

* **`readiness_submission_gate` — RED BY DESIGN.** It is downstream of Stages 9/10/13.
  It cannot go green until goal 2 runs them. **Do not "fix" it.**
* **`bundle_manuscript_length` — now GREEN, by OPERATOR DECISION, with 11 bundles still under
  their floors.** The operator ruled on 2026-08-09: *"if length of paper is not sufficient,
  it's ok to skip. I don't think it's realistic to write that length in many areas."*
  Under-floor is ADVISORY — every gap is still reported with its magnitude as a warning;
  over-ceiling still fails, because a venue rejects an over-length manuscript outright.

  ⚠️ **Goal 2 must not read this green as "the manuscripts are the right length".** No floor
  was lowered and no `length_target` was re-set; the charters still say what the venues want
  and the drafts are still short of them. What changed is that the gate stopped blocking.
  **The open question goal 2 inherits is per-bundle: for each of the 11, does the CHARTER move
  or does the DRAFT?** That is an editorial call to make with the operator, one bundle at a
  time, with the reason recorded — not a sweep. See `ACCURACY_LEDGER` V75 (the conflict) and
  V77 (the decision and what it did not authorise).

⚠️ **`bundle_figure_adequacy` is green with EIGHT bundles carrying zero drawn figures.** That is
legitimate — the pipeline law mandates `\figuredeferred{id}{reason}` as the deferral form and the
gate counts it toward the tier floor — but a reader should not have to derive it from the
summary. Goal 2 owns turning 40 declared deferrals into drawn figures; the green means "every
deferral is declared with a reason", not "every bundle has its figures".

Green and worth not regressing: `bundle_figure_adequacy` (green **by declared deferral** —
its summary reads `42 drawn, 40 declared-deferred, 8 bundle(s) with zero drawn figures`,
so the magnitude cannot hide behind the green), `bundle_structural_coherence`,
`bundle_source_freshness`, `lean_zero_sorry`, `graph_integrity`,
`axiom_closure_allowlist`, `formula_grounding`.

**E2 is under its PRL ceiling by trimming, not re-chartering:** 4751 → 3738 word-equivalents
against 3750. Everything removed landed in D1, its declared deep companion.

---

## 6. Substrate state

* `rm -rf .lake/build && lake build SKEFTHawking.ExtractDeps` — **clean, 10,827 jobs**.
* Zero `sorry`. Axioms exactly `{propext, Classical.choice, Quot.sound}` on every new
  declaration. No new project-local axiom was introduced.
* Three new Lean modules: `FaultTolerance/MalignantUnionBound.lean`,
  `FaultTolerance/ConcatenatedComposition.lean`, `QuantumNetwork/FDTLDPBridge.lean`, plus
  a rewritten `SakharovGenerationBridge.lean`.
* All 21 publication bundles compile with zero undefined references.

---

## 7. Two things goal 2 should not have to rediscover

**The `\figuredeferred` mechanism was mandated by the pipeline law and had zero uses.**
It counts toward `bundle_figure_adequacy`'s floor (`if n_fig + n_def < floor`). Reading
only the check's docstring and its failure messages — as goal 1 initially did — yields the
false conclusion that the gate needs ~40 drawn figures or a lowered floor. **A check's
contract is its code.**

**The nine sourceless bundles can now signal Stage A.** `freshness_stale` is `true` for
D6/D7/D9/I3 and the rest of the nine, written by the Lean trigger. Before goal 1 the
trigger could not signal at all, so an absorption pass keying on that field saw nothing.
