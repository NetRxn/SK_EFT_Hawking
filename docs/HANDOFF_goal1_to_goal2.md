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

---

## 8. The six-agent pr-review-toolkit round (2026-08-10) — what it found and what changed

The full six-agent suite ran over the **branch diff vs `main`** (`c2b597e1..336ebcc7`,
448 files): code-reviewer, comment-analyzer, silent-failure-hunter, pr-test-analyzer,
type-design-analyzer, code-simplifier. Every finding acted on below was **reproduced
before it was fixed** — including the ones the agents attributed to me — and every
replacement test was **mutation-proven** by re-seeding the defect.

### The one physics defect

`formulas.adw_effective_potential` guarded on `C < 1e-15` instead of `abs(C)`, so the
entire negative branch of a **double well** returned `0.0`. Every term is even in `C`
(`C²`, `C⁴`, and `C²` inside the log), so `V(-0.5)` must equal `V(+0.5)`; measured
`-0.4987…` vs `0.0`.

**It never reached a figure or a solver result.** Every caller samples `C ≥ 0` —
`gap_equation.py:334` `linspace(0, Lambda)`, the minimizer's `bounds=(1e-6·Λ, C_max)`,
`ginzburg_landau.py:683` `linspace(0.5, 5.0)`. Latent, not observed. The pre-existing
equivalence test sampled only `C ∈ {0.01, 0.1, 0.5}`, which is exactly why it survived;
`test_effective_potential_even_in_C` now covers both signs.

### Four gates that could not fire

| Gate | Why it was inert | Now |
|---|---|---|
| `validate.py --check` | single-value arg — repeating it kept only the LAST name and printed "1/1 passed". The Aristotle gauntlet lost its `axiom_closure_allowlist` leg (the Invariant #15 backstop); two frozen procedures silently skipped checks | `action="append"`; unknown-name guard covers every name; single `--check` byte-identical |
| `aristotle_submit` sorry guard | matched `"declaration uses 'sorry'"`; Lean v4.32 emits **backticks**, so `sorry_warns` was always `[]` and `zero_sorry == build_ok` | quote-agnostic regex, matching its already-repaired sibling in `pre-commit-sync.sh` |
| `record_review.py` | `--doc` optional ⇒ a Stage-13 **GREEN with no evidence document**, and the previous doc path left in place while `review_kind` flipped | `--doc` required for stage 13; path always overwritten |
| `convert_inprep_citations` | split on `"%"`, truncating at an escaped `\%` | canonical `\%`-aware stripper (one owner) |

### Three gates that reported what they had not measured

- **`update_counts.py`** — `except Exception: _n_debt = 0` around the tracked-vacuity
  split. Because `theorems_kernel_substantive = _substantive - _n_debt`, a swallowed
  failure **inflated the published kernel count by the whole debt (69)** and asserted
  `tracked_vacuity_debt: 0`. These render into `docs/counts.tex`, which drafts
  `\input` — the lie reached the papers. Now raises.
- **`_eval_computation_correctness`** — formulas absent from the graph were
  `continue`d, then `len(formula_ids)` was reported as the number examined. The four
  buckets now partition the population exactly (asserted) and the unexamined ones are
  named.
- **`ensure_lean_deps_fresh`** — returned `True` unconditionally after calling
  `_run_extraction()`, and the resulting stale pass is memoized under the **new** source
  key, so it replays. Now re-asks the hash guard.

### `_eval_assumption_disclosure` is vacuous for the whole corpus — measured, not fixed

The 4-hop walk (`CLAIMS → GROUNDED_IN → VERIFIED_BY → ASSUMES`) **runs** and lands
empty for **all 64 papers**. Measured cause: the walk reaches **122** theorem nodes,
**66** lean nodes carry an `ASSUMES` edge, and the two sets are **disjoint**
(intersection 0). The hypothesis-bearing theorems are simply not cited by any paper's
claim chain.

It is kept as a pass — an empty population *reached* is not a population *unreachable* —
but the pass now says so instead of reading as verified disclosure. **Goal 2 decision:**
if a wave cites one of those 66, the gate starts working; if none ever does, retire it
rather than leave it as decorative green.

### The `measured` axis — a self-contradiction of goal 1's own making

`bundle_manuscript_length` returned `measured=False` whenever **any** bundle was
unsizable. THE ONE POLICY is that `measured=False` means the population was
**UNREACHABLE**, not that coverage of it was **INCOMPLETE** — sizing 20 of 21 is the
latter. One stale PDF took the whole `--ci` coverage floor down. Worse, the policy note
in `_registry.py` named this very check as a legitimate `measured=False` while its own
preceding sentence said the opposite, and the implementation followed the wrong half.

Now `measured = sized > 0`, with each skipped bundle carrying `measured=False` on its
**own Detail** — the granular signal survives, so check-level `measured=True` is honest
rather than a loss. What the bad fold was reaching for is real and is **not** solved by
that line: a bundle that goes UNMEASURED escapes the over-ceiling leg, the only one that
still gates. That is contained by keeping it loud (the summary always prints the
UNMEASURED count and names every skipped bundle), not by lying about `measured`.

### Perishability, exercised rather than described

Regenerating `counts.tex` staled every bundle PDF; `bundle_manuscript_length` correctly
went 21-UNMEASURED and **FAILED** (nothing sizable ⇒ UNVERIFIED, not passing); the
documented remedy `compile_bundle_pdf.py --all --force` restored 21/21 sized, 0
unmeasured. **The §5.1 regeneration ORDER is real — follow it.** The 17 compile failures
are legacy per-paper drafts (`paperNN_*`, `note_*`), **none of the 21 bundles**.

### Five tests that could not fail

Three had **self-referential expectations** — a test whose expectation is read from the
code under test asserts only that the code equals itself:

- `_spot_names()` AST-lifted `spot_checks` out of `check_lean_source`; replacing a
  production name with a fiction left it green. Now a pinned literal **plus a drift
  detector** that forces a deliberate update.
- `test_lean_root_defaults_under_the_project_anchor` asserted the production expression
  verbatim; rewriting the resolver as a `Path(__file__)` parent-walk — the exact ADR-009
  H1 violation its own module header pins — left it green.
- `test_d5_physics._patch` lifts the `expected` table from the check, so `rel_err ≡ 0`
  by construction. The lift stays (it keeps the seeded-drift tests honest); the **shape**
  is pinned separately, because `assert r.details` passed on a single detail.

Two **matched nothing**: `msg.startswith("fresh:")` against a production string that
begins `source-fresh:`, and `"0 unresolved" in message` — a substring of
`"10 unresolved"`, so the zero-headroom ratchet passed for any count ending in 0.

### Refutable numbers corrected

- **`5.2×` → `2.58×`.** `(v_F/c_s)²` with the `/2` dropped; `ν = 2·(η/sT)·c_s²` in the
  `c_s` form but `(η/sT)·v_F²` in the `v_F` form, so the ratio carries a factor ½.
  `provenance.py:852` already stated the correct value. Fixed in
  `hawking_predictions.py` and `DiracFluidSK.lean`.
- **`papers/F:514` said "four bundles … (D6, D9)"** — reader-visible, rendered in an
  `\fbox` in the compiled PDF. Measured against the pre-08-08 baseline: exactly **two**
  changed (D6 11→23, D9 25→27), the two it already named.
- **"`docs/counts.tex` sits in EVERY bundle's `\input` closure"** is false for 5 of 21,
  and it was the stated premise of the perishability workflow. ⚠️ My first correction
  transcribed the member list and was **caught by `architecture_inventory_fresh`** — the
  no-census-in-narrative rule is machine-enforced. Restated as a **mechanism**
  (`draft_input_closure` is the authority), which is the form that rule wants.
- `figuredeferred.tex` claimed 21 consumers; measured **11**.
- The registry's own "derive it" grep used ERE negative lookahead and **exited 2**
  instead of answering; the replacement runs and excludes itself from its own count.
- A comment claimed the under-floor population "shrank 11 → 10 → 1"; the third
  degradation is recorded nowhere. Corrected to the two measured facts (11→3 stale tree,
  11→10 test-seeded).
- ADR-011's status block said `bundle_manuscript_length` is RED; the operator amendment
  **156 lines below in the same document** made under-floor advisory, and it passes.

### Canonical-home bypass

`transonic_background` open-coded `Γ_H` while `formulas.py` declared itself the canonical
home and said callers must not. Three defects in three lines: the graphene path was
routed and the BEC path — the one the docstring *names* — was not; it kept the
`if cs > 0 else 0.0` silent sentinel, which reports a **dissipationless horizon**; and it
cited a Lean theorem (`SecondOrderSK.gamma_H_from_transport`) that **does not exist** in
`lean_deps.json`. `lean_docstring_refs_resolve` scans Lean docstrings, not Python
comments, so nothing caught the dangling reference. Now routed through
`horizon_damping_rate`, which raises instead.

### Still open for goal 2 (from these reports, not fixed here)

1. **`gate_precheck s9` cannot fail for 11 of the 13 bundles that carry figures** —
   `check_viz_consistency` has one unconditional `passed=True` return, and
   `bundle_figure_integrity`'s SPECS cover only D11 and D12.
2. **The `submission` gate (`"__strict__"`) cannot pass on any tree** — it keys on mtime,
   which `git checkout`/merge restamps. Needs a product decision, not a code fix.
3. **`BundleClosure.measurable` never checks that any apex *resolved*** → an
   all-unresolvable apex list emits `\bundleTheorems{0}` into D1, D5, E1, E2, F.
4. **30 graph nodes point at files that don't exist** — the `rglob` widening was not
   swept into path/key construction (`tests/e2e/*`); stem collision is latent today.
5. **`render_bundle_counts.py --check` is blind to an orphaned `bundle_counts.tex`.**
6. The comment-analyzer's remaining doc corrections: stale line cross-references in
   `END_TO_END_MAP.md`, the `ADR-010 §Open item 4` mis-citation at three sites (the
   mtime decision lives in **§D6**), "fifteen live sites" superseded by a sixteenth, and
   D36's at-HEAD figures that were stale one commit after they were written.
