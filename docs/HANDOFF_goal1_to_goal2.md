# Handoff — goal 1 → goal 2

**Branch:** `infra/adr-009-validation-modularization`, committed, clean tree, **NOT merged**.
**Written:** 2026-08-09, at the close of goal 1.

Goal 1 was: close the 30 enumerated `ARCHITECTURE_TODOs` items, get three bundle gates
green, pass the full pr-review-toolkit suite, leave the branch green and unmerged. Goal 2
owns the wave-pipeline reviewer stages, the merge, and the manuscript programme.

---

## 1. What goal 1 closed

**All D-items in `docs/architecture/.working-docs/ARCHITECTURE_TODOs.MD` are closed as
findings. None is left OPEN** — verified 2026-08-10 by scanning every `###` D-item heading
for an OPEN/⚠️ marker, not by trusting this sentence.

> **The D4 "perishability queue", resolved 2026-08-10.** This paragraph used to record it as
> the one OPEN remainder. It is closed, and the term is retired rather than carried forward.
> V9–V18 executed the work: all six prose documents read 100% in the ledger's §Final state
> table (`CHECK_AUTHORING_GUIDE.md` 54/54 and `END_TO_END_MAP.md` 80/80 last), and D4's body
> has said "The queue is CLOSED" since — while its heading still asserted OPEN twelve lines
> above. Both now agree.
>
> ⚠️ Worth keeping as a lesson rather than a status: "perishability queue" occurred in exactly
> two places repo-wide — that heading and this paragraph — and named **no concrete artifact**.
> An item that cannot be pointed at can be neither executed nor verified closed, which is why
> it survived three separate reviews. What is real is the ledger's P/D perishability
> *convention* for individual atoms; there was never a queue derived from it.

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

⚠️ **Do not run this as one goal.** Goal 1 absorbed five rounds of scope growth, and every
defect its closure reviews found entered during one of them. The work below is sequenced so
each item closes and is reviewed before the next opens.

### The execution order is not the gate-recording order

Recording is Stage 9 → 10 → 13 (`bundle_reviewer_stage_ordering` enforces it). **Execution is
not.** `BUNDLE_LIFT_PROCEDURE.md` §7.5 puts the whole-document read-through before the claims
review and before Stage 9, so per bundle the real sequence is:

> draft → `skeft-qa:prose-reviewer` read-through → `skeft-qa:claims-reviewer` → Stage 9 figures
> → Stage 13 adversarial

Stage 10 is not a step between two reviews; it is the drafting stage and it *contains* the
first two sub-gates. Most of goal 2's labour lives there.

### What the agents do and do not do

The four reviewers are **findings-only by design** — Stage 13 says so explicitly. No agent
writes physics. `skeft-qa:paper-authoring` is a *skill*: drafting guidance for the lead, not an
autonomous drafter. Plan the manuscript work as lead labour reviewed by agents, not as agent
output.

### Sequence

**Item 0 — ExtractDeps declaration classification** (own branch, own review; see §12).
Do this first: it removes a whole defect class rather than guarding it, and every later item
reads the artifact it fixes.

**Item 1 — the three infrastructure bundles, I1 → I2 → I3.** Smallest floors (15 / 9 / 9 pp)
and the most mechanical content, so they exercise the full Stage-10 machinery on low-stakes
material. This is the decision point: if the I-bundles come out weak, the problem is the
pipeline, and it cost ~33 pages to learn rather than 150.

**Item 2 — the deep papers**, one bundle per wave, ordered by substrate readiness. Split the
roster explicitly into *needs new physics* and *needs only drafting* before starting; they are
different kinds of work and should not share a wave.

**Item 3 — F, last.** `PAPER_STRATEGY.md` §33: the flagship "ships *last*, after the Tier 1
papers are out, so it can cite them and serve as the stable reference rather than a snapshot."
F's floor is 80 pp against 24 today, but that gap is **blocked by design**, not outstanding
work. Do not schedule it against the Tier-1 bundles.

### Standing requirements for every bundle wave

1. **Refresh or work around the plugin** (§4) before the first wave.
2. **Clear the 15 `stage13_redo_required` flags** by re-review, never by editing the field.
3. **Compile before measuring.** Run `compile_bundle_pdf.py --all --force` first:
   `bundle_manuscript_length` reports `UNMEASURED` for any bundle whose PDF predates its
   `\input` closure, and a shared input invalidates every bundle carrying it at once
   (`docs/counts.tex` reaches 16 of 21). Measured stale, the same check reported 3 under floor
   and 16 UNMEASURED against 11 under floor on a fresh tree. A stale tree now FAILS `--ci`
   rather than passing quietly, which is deliberate.
4. **Merge to main** per item, with the full suite and a clean
   `rm -rf .lake/build && lake build SKEFTHawking.ExtractDeps`.

**Current state:** all 21 bundles are `pending` on Stage 9, 10 and 13. Nothing is green.

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
* Zero `sorry`. No new project-local axiom was introduced.
* **Axioms: exactly `{propext, Classical.choice, Quot.sound}` on every declaration this
  branch ADDED — but NOT across the whole apex set.** Measured 2026-08-10 with
  `lake env lean` + `#print axioms` over all 578 declared bundle apexes (not
  `lean_verify`, which has produced a false `sorryAx` here):

  ```
  555 of 578 kernel-pure
   23 carry a `…_native.native_decide.ax_*` compiler-trust axiom
  owning bundles: D4 18 · D2 3 · F 3 · I2 1 · L2 1
  ```

  Those 23 include headline theorems (`e8_det_one`, `FibonacciMTC.fib_pentagon`,
  the `IsingBraiding` family). The owning-bundle histogram matches
  `NATIVE_DECIDE_BUNDLE_DEBT = {D4:19, L2:6, F:3, D2:3, I2:1}` exactly, so this is
  **disclosed and ratcheted, not a regression** — but the unqualified sentence that
  used to sit here was false, and a reader entitled to take "kernel-pure" literally
  would have been misled.

  ### ⏭️ CIRCLE BACK: re-state this once the `native_decide` elimination lands

  This wording is **provisional by design**. The decl-closure ceiling has come down
  `852 → 587 → 546` (`NATIVE_DECIDE_DECL_CLOSURE_CEILING`, `constants.py:2516`), so
  elimination is an active trajectory, not a permanent posture — the project's stance
  is that `native_decide` is compiler trust to be discharged, the same posture it
  holds toward axioms.

  **When that ceiling reaches 0**, come back here and to `TODO-D39` and collapse this
  whole caveat to the one-line claim it replaced. Until then, do NOT restore the
  unqualified sentence, and do NOT quote "kernel-pure" of the apex set without the
  23. The check to re-run is:

  ```bash
  uv run python scripts/validate.py --check native_decide_regression   # ceiling → 0?
  ```
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
unmeasured. **The §5.1 regeneration ORDER is real — follow it**, and note it is *counts
first, compile second*: regenerating `counts.tex` after compiling re-stales 16 of the 21 at
once, which is what happened here.

Compile failures are **14** legacy per-paper drafts, **none of the 21 bundles** —
`paper_latex_compiles` reports `50/64 drafts clean (21/21 bundles, 29/43 legacy) … 14 legacy
(ratcheted)` at its frozen ceiling of 14. ⚠️ An earlier draft of this section said "17",
counted off raw `compile_bundle_pdf.py --all --force` FAIL lines rather than off the ratcheted
check. The check is the authoritative instrument; the raw script's failure set is wider.

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

---

## 9. Closure review (2026-08-10) — what it overturned, and three things it is right about

A fresh-context reviewer audited the branch under a rule barring it from accepting this
loop's commit messages, ledger, handoff, or code comments as evidence. Only commands it
ran itself counted. It verified ten of the eleven specific claims put to it — including
the `adw_effective_potential` symmetry fix, the `--check` repeat semantics, the sorry-guard
regex against real Lean output, the `record_review` refusal (with all 21 metadata files
byte-identical before/after), the `update_counts` refusal, the `2.58×` ratio, the 16-of-21
`counts.tex` closure, and the "two bundles" correction in F.

**It overturned one, and the one it overturned was a claim about my own work.** See §8's
`test_lean_root_defaults_under_the_project_anchor`: I asserted it was mutation-proven
against an ADR-009 H1 parent-walk. It was not. `validate_helpers.py:73` sets
`PROJECT_ROOT = SCRIPT_DIR.parent`, so a *faithful* walk from `scripts/validation/checks/`
returns the byte-identical path and satisfies every assertion about the result. My mutation
walked the wrong number of levels — a typo, not the violation — so it proved nothing. The
property is about **derivation, not value**, and is only visible in the source; there is
now a test that reads the parsed function body, and it is proven against the reviewer's own
seed. **The lesson generalises: a mutation only proves a test when the mutation is the
defect the test claims to catch, not merely something nearby.**

### Three findings that are real and are NOT closed

1. **Goal condition 5, read literally, is not met — by inheritance.** 22 `set_option
   maxHeartbeats` sites sit in proof bodies (Pipeline Invariant #10 forbids them), and 26
   of 631 apex theorems carry `native_decide` axioms in their closure, so "axiom closure is
   exactly `{propext, Classical.choice, Quot.sound}`" holds only if compiler-trust axioms
   are excluded. Both are **identical on `main`**, ratcheted at zero headroom
   (`MAXHEARTBEATS_PROOF_BODY_CEILING`, ADR-002 / `bundle_native_decide_debt`), and
   untouched by this branch. They are disclosed debt, not regressions.

   ⚠️ **This paragraph previously said "nothing gates on Invariant #10". That is FALSE.**
   `check_elaboration_knob_watchlist` returns `passed=not over` against
   `MAXHEARTBEATS_PROOF_BODY_CEILING = 22` at zero headroom, so a 23rd proof-body
   heartbeat site FAILS the check. The *name* is advisory; the `invariant_10` leg is
   not. `AI-DEFECT-DEFENSE-LAYER.md:54` had it right ("enforced … zero-headroom
   ratchet") and this file contradicted it. The 22 existing sites are frozen debt that
   cannot grow — which is the enforcement, not the absence of it.
   **Whether `native_decide` should count toward the headline-axiom claim is an operator
   call, not one this loop should make silently.**

2. **`--ci` green is not reproducible from a bare checkout.** `papers/**/*.pdf` is
   gitignored (3 of 21 bundle PDFs are tracked), and `bundle_manuscript_length` refuses to
   size a PDF that is absent or older than its draft's `\input` closure. In a fresh
   `git worktree` of HEAD it returns `passed=False, measured=False` with all 21 unmeasured —
   which also drops the run below `CI_MIN_CHECKS_RUN = 75`, since that floor counts
   *measured* checks at zero headroom. **A clone must run `compile_bundle_pdf.py --all`
   before `--ci` means anything.** This is a build-artifact dependency rather than a defect,
   but it is undocumented anywhere the reader would look, and it makes the gate's green
   depend on local state.

3. **~~`bundle_manuscript_length` coverage~~ — DESCOPED BY THE OPERATOR (2026-08-10).**
   Manuscript length is out of the goal entirely: writing to the declared floors is not
   realistic across this many bundles, so under-length is accepted and the gate's partial
   coverage is no longer a blocker. The mechanism is kept below because it is a *real and
   still-live* defect in the freshness machinery that will bite any FUTURE gate keyed the
   same way — it is simply no longer this goal's problem.

   **The suite stales its own input.** Measured 2026-08-10, sharpening the reviewer's Finding 7 with a
   mechanism. The cycle:

   * `docs/counts.tex` carries `\totaltests`, so **adding a test changes it** (6153 → 6156
     this session — a real content change, not a stamp-only rewrite).
   * `counts.tex` is in 16 of the 21 bundles' `\input` closures.
   * `counts_fresh` runs inside `validate.py` and advances `counts.tex`'s mtime — observed
     04:16:08 → 04:29:02 across a single `--check counts_fresh` invocation.
   * `bundle_manuscript_length` refuses to size any PDF older than its draft's closure.

   So compiling all 21, then running the suite, leaves **5 sized and 16 UNMEASURED** — which
   is the state at this HEAD. The gate still PASSES (it gates only on over-ceiling, and the 5
   it sized are within target), but it is green over 24% of its population, and no ordering of
   the documented §5.1 workflow fixes it: the step that checks freshness is downstream of the
   step that destroys it.

   **This is a design defect, not a stale artifact, and it is NOT closed.** The plausible
   repairs — exclude `counts.tex` from the length-freshness closure (it cannot change a page
   count by more than a digit), or key freshness on content hash rather than mtime, or have
   `counts_fresh` leave mtime alone when the content is unchanged — are each a real decision
   with blast radius beyond this branch, so none was taken unilaterally at the close of a
   loop. Goal 2 should pick one before treating this gate's green as meaningful.

4. **The branch was a moving target during review.** The loop committed twice while the
   reviewer measured, resolving two findings mid-audit. Any closure verdict on this branch
   must name a SHA — the reviewer's is `f8f2fa52`, and §8's fixes land after it. **Freeze
   the tree before dispatching the next one.**

---

# 10. GOAL-2 HANDOFF — measured state, what to run, and the one decision waiting

Everything in this section was measured on 2026-08-10 at branch HEAD, not carried
forward from an earlier note. Re-derive anything you intend to act on: the commands are
given so you can.

## 10.1 Every bundle's reviewer-stage status

Source: `papers/<CODE>/bundle_metadata.json`. Re-derive with the loop in §10.5.

| | Stage 9 | Stage 10 | Stage 13 | §7.5 prose | readiness | s13 redo |
|---|---|---|---|---|---|---|
| D1  | pending | pending | pending | not run | RED | ✔ |
| D2  | pending | pending | pending | not run | RED | ✔ |
| D3  | pending | pending | pending | not run | RED | ✔ |
| D4  | pending | pending | pending | not run | RED | ✔ |
| D5  | pending | pending | pending | not run | RED | — |
| D6  | **not_started** | **skeleton** | pending | not run | YELLOW | ✔ |
| D7  | **not_started** | pending | pending | not run | RED | ✔ |
| D8  | pending | pending | pending | not run | YELLOW | ✔ |
| D9  | pending | pending | pending | not run | **UNMEASURED** | ✔ |
| D10 | pending | pending | pending | not run | YELLOW | ✔ |
| D11 | pending | pending | pending | not run | RED | ✔ |
| D12 | **pending-redo** | **pending-redo** | **pending-redo** | not run | RED | ✔ |
| E1  | pending | pending | pending | not run | RED | — |
| E2  | pending | pending | pending | not run | YELLOW | ✔ |
| F   | pending | pending | pending | not run | RED | ✔ |
| I1  | pending | pending | pending | not run | RED | — |
| I2  | pending | pending | pending | not run | RED | — |
| I3  | pending | pending | pending | not run | RED | ✔ |
| L1  | pending | pending | pending | not run | RED | ✔ |
| L2  | pending | pending | pending | not run | RED | — |
| L3  | pending | pending | pending | not run | RED | — |

Three facts a reader should not have to infer:

- **No bundle is `green` at any reviewer stage.** Commit `14ba438c` (2026-08-07,
  branch-only) demoted every reviewer-stage green to `pending` by operator decision. The
  live value set is exactly `{pending, pending-redo, skeleton, not_started}` — `green`
  does not occur. Any tool or doc branching on a live `green` is reading a state no
  bundle is in.
- **§7.5 prose review has never run for any bundle** — the agent that would run it
  (`prose-reviewer`) is not installed. See §10.3.
- **D9's readiness is `UNMEASURED`, not RED or GREEN.** It is the portfolio's only
  former GREEN and the one bundle whose P1 gates could not be computed. Do not read it
  as either colour.

**15 of 21 carry `stage13_redo_required`.** That flag — not `freshness_stale` — is the
lift exit gate (`BUNDLE_LIFT_PROCEDURE.md:395`).

## 10.2 What goal 2 must run

In order. Each is blocked on the one above it.

1. **Resolve the plugin decision (§10.3).** Everything else in Stage 9/10/13/§7.5 runs a
   stale contract until this is settled.
2. **Stage 9 (figure) and Stage 10 (claims)** per bundle. ⚠️ `gate_precheck.py s9` is a
   weak gate: `check_viz_consistency` has exactly one unconditional `passed=True` return,
   and `bundle_figure_integrity`'s SPECS cover **D11 and D12 only**, so an s9 precheck on
   any of the other 19 bundles passes having examined zero of that bundle's figures.
   Treat a green s9 as "not blocked", never as "figures verified".
3. **Stage 13 (adversarial)** per bundle. `record_review.py` now REQUIRES `--doc` for
   stage 13 and overwrites `stage13_review_doc` on every write, so a green cannot be
   recorded without a citable artifact.
4. **§7.5 prose** — only after `prose-reviewer` is installed.
5. **Then, and only then, `readiness_submission_gate`.** It is downstream of all four and
   is expected to stay red until they land. It is not a defect and must not be "fixed".
6. **The merge to main.** Deliberately not done in goal 1.

## 10.3 The plugin decision goal 2 faces

Measured against the newest cache revision (`skeft-local/skeft-qa/57c1067d9d23`):

| | installed | in repo |
|---|---:|---:|
| agents | **8** | **9** |

`prose-reviewer.md` is **absent from the installed plugin**. The three reviewer agents
that *are* installed have drifted from the repo copies:

| agent | differing lines |
|---|---:|
| `figure-reviewer` | 14 |
| `claims-reviewer` | 26 |
| `adversarial-reviewer` | 17 |

**The decision: refresh, or fall back.**

- **Refresh** (recommended) — reinstall the plugin from the in-repo
  `.claude/plugins/skeft-qa/` so all 9 agents are present and the three reviewers match
  their repo contracts. Then Stages 9/10/13/§7.5 run the contract this branch actually
  wrote. Cost: one plugin refresh, then re-verify the count is 9 and the three diffs are 0.
- **Fall back** — run Stages 9/10/13 against the stale installed agents and skip §7.5
  entirely. **Not recommended**: the 26-line drift in `claims-reviewer` is the largest,
  and that agent is the one whose output feeds the chain-of-backing records. A review run
  against a stale contract produces findings keyed to a schema the repo no longer uses.

Whichever is chosen, **record it** — a Stage-13 green produced under the fallback means
something materially weaker than one produced after a refresh, and nothing in the
metadata distinguishes them.

## 10.4 What goal 1 leaves behind, stated as risk

- **`--ci` green is not reproducible from a bare checkout.** `papers/**/*.pdf` is
  gitignored (3 of 21 bundle PDFs are tracked) and `bundle_manuscript_length` refuses to
  size an absent PDF, so a fresh clone drops below `CI_MIN_CHECKS_RUN`. Run
  `compile_bundle_pdf.py --all` first.
- **`counts.tex` perishability is self-inflicting.** It carries `\totaltests`, so adding
  a test changes it; it sits in 16 of 21 `\input` closures; and `counts_fresh` advances
  its mtime from inside `validate.py`. Regenerate in the order
  `pytest → update_counts → compile_bundle_pdf --all --force → validate --ci`.
- **`readiness_submission_gate` stays red by design** until §10.2 steps 2–4 land.
- Open items with measurements, not guesses, are in `ACCURACY_LEDGER.md` V81–V82 and the
  residue list in §8.

## 10.5 Re-derive the table above

```bash
uv run python -c "
import sys,json,os;sys.path.insert(0,'scripts')
from bundle_registry import BUNDLE_CODES
for c in sorted(BUNDLE_CODES):
    d=json.load(open(f'papers/{c}/bundle_metadata.json'))
    print(c, d.get('stage9_status'), d.get('stage10_status'),
          d.get('stage13_status'), d.get('readiness'),
          d.get('stage13_redo_required'))"
```

## 11. Second closure review (2026-08-10, at `2f920e46`) — six findings, all fixed

The first closure review's fixes were themselves reviewed by a second fresh-context
reviewer, which **reopened condition 3**. Its verdict is worth quoting for goal 2,
because it names the branch's recurring shape rather than six unrelated bugs:

> the counts fix is materially incomplete in three independent ways — the published
> theorem figure is still not author-written-only, one published macro family still has
> no autogen filter at all, and the staleness mechanism still misses the fourth tree it
> publishes. […] F4 is the branch's recurring "fix breaks a neighbour" shape recurring
> twice more, unnoticed.

All six landed in `78ded271`. What generalises:

- **F1 — one predicate, three re-derivations.** Three generators each answered "is this
  declaration compiler-generated?" from a different source. The fix is a single shared
  accessor, not three corrected copies. **Rule for goal 2:** when a fix touches a
  predicate, grep for every site that answers the same question before declaring it
  fixed; a corrected duplicate is a defect that has not been found yet.
- **F2 — a guard in the wrong branch never matches.** `eq_def` sat in the suffix set
  whose branch requires an inductive/structure parent; all 20 live instances are
  parentless, so it filtered nothing while appearing to. **Rule:** a guard's membership
  list and its branch condition are two facts; verifying the list is not verifying the
  guard. Assert the count moves.
- **F3 — a published figure with no staleness input.** `counts.json` publishes a figure
  derived from `src/`, but `src/` was not an input to `_counts_is_stale`. The
  parametrized test now proves one leg per published tree, and is mutation-verified
  against all four. The other three legs had **no positive test at all** before this.
  **Rule:** for each figure a generator publishes, there must be a test that the tree it
  derives from can make it stale.
- **F4 — the H1 hazard, twice, introduced while fixing something else.** Two checks
  reached the corpus by re-deriving from `_H.PROJECT_ROOT` instead of using
  `_H.PAPERS_DIR` / `_H.LEAN_DIR`. Ten tests then failed — and the reason is the
  instructive part: **they had been passing *because* the code re-derived from
  `PROJECT_ROOT`, which is exactly what their fixtures patched.** The isolation was a
  no-op against the anchor the check actually read; retargeting `PAPERS_DIR` at a tmp
  tree had been reporting 631 declared apexes read from production. Fixtures now patch
  the anchor under test and carry a comment saying what breaks if it is dropped.
  **Rule:** a fixture that patches a path the check does not read is not isolation —
  prove it by retargeting and confirming the check goes `measured=False`.
- **F5 — two populations, one number.** TODO-D39 cited the apex histogram
  (`D4 18 · L2 1`) as evidence about `NATIVE_DECIDE_BUNDLE_DEBT` (`D4 19 · L2 6`). The
  debt figure is closure-scoped; the histogram is not. **Rule:** before a count supports
  a claim, state the predicate that scopes it.
- **F6 — a doc asserting a check cannot fail** on a condition it can.

**Status of the ten conditions is therefore condition 3 = re-verification pending**: the
fixes are committed and the fast suite is green (6,098 passed, 6 skipped), and the
third fresh-context closure review is the gate that decides whether it closes. Goal 2
should treat a *clean* third review as the merge signal, not this note — this note is
prose, and prose is not evidence for itself.

## 12. Item 0 — classify compiler-generated declarations at the producer

**The problem this removes.** `kind == "theorem"` in `lean_deps.json` includes Lean's own
products (`.eq_1`, `.sizeOf_spec`, `.inj`, `.congr_simp`, `.eq_def`). Six consumers wrote the
naive filter and were each wrong; the worst published **26,398 "theorem nodes"** in
`docs/ATLAS_HEATMAP.md` against `counts.tex`'s **22,669** — the same corpus, differing by
exactly the 3,729 generated declarations. Goal 1 routed all six through
`validate_helpers.autogen_index` and added `theorem_census_agrees` to catch a seventh. That
guard **detects**; it does not **prevent**.

**The fix, and its real cost.** `kind` is emitted at one line —
`lean/SKEFTHawking/ExtractDeps.lean:252`. Emitting `"theorem_autogen"` there makes the naive
`kind == "theorem"` every consumer already writes *correct*. But that emit is the LAST step,
not the work.

⚠️ **Lean's current detection is incomplete, measured against the live artifact:**

| | |
|---|---|
| declarations | 40,726 (all carry an `autogen` field) |
| Lean-side `autogen = True` | 5,878 |
| Python `autogen_index` | 8,283 |
| **gap Lean would miss** | **2,405** |
| Lean-marks-but-Python-doesn't | 0 (Lean is sound; Python is a strict superset) |

The gap is whole families, not stragglers: `.sizeOf_spec` (790), `.ctorIdx` (498), `.inj`
(420), `.congr_simp` (184), `.ctorElimType` (88), `.toCtorIdx` (81), `.repr` (76), `.ofNat`
(71), `.decEq` (34), `.eq_def` (20). Emitting the new `kind` from today's Lean detection would
publish 2,405 generated declarations as authored — re-opening the exact defect this removes.

**So Item 0 is: extend ExtractDeps' autogen detection to cover those 2,405, THEN change the
emit.** These come from inductive elaboration and `deriving`, which Lean tracks structurally,
so name-independent detection is very likely available — but that is **unverified**, and it is
the real risk in this item. Verify it in Lean before committing to the approach; if structural
detection cannot reach the whole set, the item does not deliver what it promises and the
`theorem_census_agrees` guard stays as the mechanism.

**Why the producer and not the loader.** Inverting `load_lean_deps()`'s default was considered
and rejected on measurement: 76 call sites across 18 script files, but **14 files bypass the
loader entirely** and `json.load` the artifact directly — including `build_graph`, `atlas_view`,
`paper_tables/sources` and `render_bundle_counts`, i.e. the sites that actually shipped wrong
numbers. The loader inversion covers less ground than the check already does.

**What it deletes on success:** `autogen_index`'s three hand-maintained suffix sets, the
ownership leg of `theorem_census_agrees`, `THEOREM_FILTER_SITES_FLOOR`, and
`THEOREM_FILTER_ALLOWLIST`. Classification moves from Python suffix-matching to Lean's own
environment, which knows what it generated rather than inferring it from names.

**Blast radius (measured where stated, estimated where said).**

| | |
|---|---|
| producer change | one line at `ExtractDeps.lean:252` |
| rebuild | full `rm -rf .lake/build && lake build SKEFTHawking.ExtractDeps`; invalidates every memo fingerprint |
| consumers needing opt-in | **zero — enumerated, not estimated.** No "must see everything" consumer selects on `kind`: `build_graph.py` has 0 kind-filter sites and already drops generated declarations by name (`build_graph.py:605`), and `axiom_closure_allowlist` runs the `AxiomAudit` Lean executable over all `SKEFTHawking.*` declarations without reading `kind` at all (`lean_zero_sorry` is subsumed by it — a `sorry` elaborates to `sorryAx` in the transitive closure). The rename is invisible to them |
| sites that simplify automatically | 7 of the 9 executable `kind == "theorem"` sites drop their autogen guard and become correct as written |
| the one site needing a decision | `provenance_dashboard.py:2700` dispatches a node-ID prefix on `kind`; decide whether generated declarations should get `LeanTheorem` ids (today they do) |
| schema surface | `lean_deps.json` is tracked; `KNOWLEDGE_GRAPH.md` describes it |
| test surface | 8 test files reference the loader; any fixture hardcoding `kind: "theorem"` for a generated declaration changes meaning **silently** — the "fix breaks a neighbour" shape |

**Do it on its own branch with its own closure review.** It is a schema change to a tracked
artifact behind a Lean rebuild, and it touches the trusted baseline.
