# Meta-process Quality Improvement Register

**Auto-generated:** 2026-04-28T23:58:39+00:00
**Generator:** `scripts/qi_register.py`
**Reads from:** current ReviewFinding graph nodes + this file's `## Closed Items` section for status continuity

This is the Stage 14 (advisory) register. Each QI item is a **process-level** issue — a failure class that has affected multiple papers or indicates a pipeline gap — not a paper-local issue. Stage 13 (adversarial review) surfaces paper-level issues; Stage 14 aggregates those into process improvements. Stage 14 never blocks submission; items here feed remediation waves.

## Summary

- **411** ReviewFinding nodes currently in the graph
- **15** QI items tracked (3 manually-curated open + 12 closed via `## Closed Items` section)
- **3** open, **12** closed

> The 3 currently-open items are manually-curated additions from Phase 7b sub-wave 7b.4 (E1+E2 reviewer triples, 2026-05-04). They are not auto-detected from `ReviewFinding` graph nodes (Stage 13 produced advisory-class findings only, none escalated to QI thresholds), but the operational lessons each flagged a process-level gap worth tracking for Stage 14 follow-up. See "Open Items" section.

## Open Items

### qi-vizdiscipline — opened 2026-05-04 by Phase 7b sub-wave 7b.4 (E1 lift)

- **First observed:** 2026-05-04 during E1 Stage 9 round 1 figure review.
- **Pattern summary:** Plotly `add_hrect(annotation_position=...)` annotation positioning is unreliable on log-scale y-axes. With `annotation_position="top left"` (default per project), labels render OUTSIDE the rect at the top — visually placing each band's label INSIDE the band ABOVE it (one-band shift). With `"inside top right"`, the same shift persists. The Stage 9 round 2 reviewer caught this as a "tier-assignment caption mismatch" FAIL, but the root cause was not a physics error — it was a plotly rendering behavior on log axes that no current visualization-discipline check enforces.
- **Pipeline stage affected:** Stage 8 (visualizations) + Stage 9 (figure review).
- **Reliable workaround:** drop the hrect annotation entirely; use a separate `go.Scatter(mode="text", textposition="middle left")` trace with x at the right edge of the data range and y at the geometric mean of each band. Validated in `src/core/visualizations.py` `fig_polariton_regime_map` (commit `ea1d944`).
- **Owner:** unassigned. **Target:** Phase 7+ wave that touches visualizations.
- **Evidence:** `papers/E1/figures/figure_review_report.json` round 2; `src/core/visualizations.py` diff in commit `ea1d944`; memory `project_phase7b_e1_e2_closed.md`.
- **Severity:** advisory. Does not block submission directly, but if a future log-axis figure ships with hrect annotations, the misplaced labels can read as a content drift to a Stage-13 reviewer (as happened with E1 round 2). A `validate.py --check viz_consistency` extension scanning `visualizations.py` for `add_hrect` + `annotation_position` + log-yaxis combinations would prevent recurrence.

### qi-numericalverification — opened 2026-05-04 by Phase 7b sub-wave 7b.4 (E1 Stage 10 r1)

- **First observed:** 2026-05-04 during E1 Stage 10 round 1 claims review.
- **Pattern summary:** A propagating arithmetic-drift in a paper-quoted threshold survived through paper12_polariton's full per-paper Stage-13 review and propagated unchanged into the E1 bundle lift. The paper claimed `G > 0.01` at `ω/κ = 0.175`, but recompute: `G(0.175κ) = 1/(exp(2π·0.175)−1) = 1/2 = 0.5`, not `0.01`. The companion photon-count claim (`>10⁴ probe photons` for `5σ`) was wrong by factor 25 (correct: `N_probe = 25/G² = 100` at `G=0.5`). The drift propagated across 4 sites: paper12 fig 1 caption + E1 abstract + body §4 + figure dashed-line position. The canonical project source (`provenance.py:3580`) had the correct value `G > 0.5` all along — the paper text just didn't follow it.
- **Pipeline stage affected:** Stage 9 (figure review) + Stage 10 (claims review). Specifically: Stage 9 LaTeX-compile gate currently does NOT include arithmetic verification of paper-quoted numerical thresholds against direct re-computation.
- **Proposed structural prevention:** add a pre-Stage-9 arithmetic-verification step to `BUNDLE_LIFT_PROCEDURE.md` §7 (LaTeX-compile gate). For every paper-quoted numerical threshold of the form "X ≈ value at parameter Y", verify by direct computation that the formula evaluation at Y produces value within tolerance. Could be implemented as a `validate.py --check threshold_arithmetic` that scans paper TeX for `≈|=`-quoted relations between named formula terms and numerical values, evaluates the formulas via `formulas.py`, and flags any > 0.5% disagreement.
- **Owner:** unassigned. **Target:** before D3 Stage 9/10/13 reviewer triple (next session).
- **Evidence:** `papers/E1/claims_review.json` round 1 finding `block:E1:1`; supersession ledger entry `bundle-stage10:E1-2026-05-04-r1:block:E1:1:propagating-G-threshold-drift`; commits `ea1d944` (E1 fix) + `ba3e329` (paper12 source fix); memory `project_phase7b_e1_e2_closed.md`.
- **Severity:** advisory but high-impact. The drift survived a full per-paper Stage-13 review of paper12 (which closed at GREEN at the time); the bundle-lift Stage-10 claims-reviewer caught it on the FIRST round of E1 review, fixing it before submission would have been damaging. Without the structural prevention, the same class of drift can recur in any future paper that quotes a function value at a specific argument.

### qi-leantheoremname — opened 2026-05-04 by Phase 7b sub-wave 7b.4 (E2 Stage 13 r1 finding F4)

- **First observed:** 2026-05-04 during E2 Stage 13 round 1 adversarial review (RECOMMENDED finding F4).
- **Pattern summary:** E2 paper text said "formally bounded at $\leq 1.8\%$ at $\omega_H$ in `QuasiOneDReduction.lean`" but the actual Lean theorem `quasi1D_validity_bound` (`QuasiOneDReduction.lean:233`) is a generic algebraic envelope; the `1.8%` lives in the docstring at line 226 as a numerical evaluation, not as a theorem literal. Prose theorem-name references should require explicit Lean theorem name match — i.e., the paper should either name the algebraic-envelope theorem T5 explicitly with the parameter set, or add a Dean-specialized `≤ 0.02` corollary as a substantive Lean theorem.
- **Pipeline stage affected:** Stage 10 (claims review — Class TN theorem-name reference drift) + Stage 13 (adversarial review).
- **Proposed structural prevention:** extend `claims-reviewer-v2` Class TN check to flag prose-quoted bounds (`"X ≤ Y" / "X = Y" / "X ≈ Y"`) that reference a Lean module by name but where the named module's theorems do not contain `Y` as a literal. Currently Class TN only checks that the theorem name resolves; it does not check that quoted numerical bounds are theorem-literal vs docstring-numeric.
- **Owner:** unassigned. **Target:** before D3 Stage 10 reviewer pass (D3's 27 sections include numerous Lean-theorem-named bounds; this discipline is highest-leverage there).
- **Evidence:** `papers/AutomatedReviews/2026-05-04-bundle-stage13/E2.md` finding F4; `lean/SKEFTHawking/QuasiOneDReduction.lean:226-233`; memory `project_phase7b_e1_e2_closed.md`.
- **Severity:** advisory. Caught at Stage 13 r1 as RECOMMENDED (not BLOCKER); does not block E2 submission. But the same class of drift could escalate to BLOCKER if the prose quotes a number that disagrees with the docstring as well as not being a theorem literal — at which point both the Class IA (numerical-claim disagreement) and Class TN (theorem-name reference drift) checks would need to fire.

## Closed Items

### qi-assumptiondisclosure — closed 2026-04-29 by Phase 6i Wave 5

- **Evidence on close:** `docs/phase6i_wave5_close.md`
- **Mechanism:** All 30 open AssumptionDisclosure ReviewFinding nodes
  flipped via supersession ledger entries (18 STALE + 11 ACCEPTED + 1
  body-marked-CLOSED). Triage anchors include `H_LeptonNumberViolated`
  refactored from `True` placeholder to substantive `G_LV ≠ 0`
  predicate (MajoranaRung.lean:221); paper22 §122-134 "Structure
  invariants" subsection ships disclosing all four EWFiniteTParams
  positivity invariants (closes 2026-04-25-2002 + 2026-04-26-1923
  cubic_coeff_nonneg findings); paper27 Wave-5 rewrite around Balbinot
  2005 anchor closes deep_research_analog_conflation; paper20
  H_ScalarChannelIsTetradBifurcationOutput disclosed at 9 sites in
  paper_draft.tex; paper35 §VII parametrized S_horizon disclosure;
  paper35 Technical notebook §6 ships scope-disclosure + tracked-Prop
  flag (already in current state). 1 content fix applied:
  Phase6d2_ChiralSSB_Technical.ipynb cell p37t-3-md updated via
  NotebookEdit to add explicit chiPT-leading-order + NLO-band
  disclosure paralleling Stakeholder §6 honest-scope.
- **Numerics:** open count 30 → 0 (100%); supersession ledger 107 →
  137 entries (+30 Wave-5 entries).

---

### qi-citationintegrity — closed 2026-04-28 by Phase 6i Wave 1

- **Evidence on close:** `docs/phase6i_wave1_close.md`
- **Mechanism:** Per-phase `Lit-Search/Phase-X/primary-sources/` cache
  rolled out (Pipeline Invariant #11). New `validate.py --check
  citation_primary_sources_present` (CHECK 19) mandatory at every
  Stage 13. Hallucinated-citation failure mode structurally
  non-recurrable.
- **Numerics:** Registry 218 → 339; cached 4 → 227.

### qi-computationcorrectness — closed 2026-04-29 by Phase 6i Wave 6

- **Evidence on close:** `docs/phase6i_wave6_close.md`
- **Mechanism:** All 22 open ComputationCorrectness ReviewFinding
  nodes flipped via supersession ledger entries (5 ACCEPTED — older
  motivational/scoped framings; 17 FIXED — most are Class-1
  cache-skip closure-note findings whose body content is itself a
  PASS verification, plus 2 active content fixes: paper17 SFDM count
  drift 31 → 29 and paper37 Technical notebook cell p37t-5-md
  two-conjunct → three-conjunct).
- **Numerics:** open count 22 → 0 (100%).

### qi-countfreshness — closed 2026-04-29 by Phase 6i Wave 6 (structural prevention)

- **Origin:** Surfaced by Wave 6 `qi_register.py` status-filter audit.
  Not in the Phase 6i entry-state-8 QI list; emerged from existing
  CountFreshness regex cluster after closing the 8 entry-state QI
  items. Per Phase 6i roadmap line 11 (append-only structure).
- **Evidence on close:** `docs/phase6i_wave6_close.md` +
  `scripts/update_counts.py` + `docs/counts.tex` (auto-regenerated
  central macro registry) + `validate.py --check counts_fresh`.
- **Mechanism:** Structural prevention via the counts.tex macro
  pipeline: every paper now consumes `\input{../../docs/counts.tex}`
  and references count via macros (`\fhdTotal`, `\heatKernelThms`,
  `\centerSymmThms`, `\bhThermoTotal`, etc.). The 18 representative
  open findings triage as: 9 PASS-verifications already-fixed
  (counts.tex stale → fresh, abstract count macro retrofits,
  Vergeles2025 used_in field expanded 2 → 7 papers, paper27 figure
  removal, EinsteinCartanExtension docstring numerical-claim correct,
  paper27 \\bhThermoTotal{20} matches actual); 5 INFO-level advisories
  about Stakeholder/Technical notebook count text (all currently
  match actual Lean source); 4 pre-Phase-6i advisories about counts
  superseded by the macro pipeline (paper10 130→195 modules,
  paper18 raw-literal → \\fhdTotal{}, paper20 definition-count
  removed in W2 strengthening, v2_reviewer pipeline-gap closed by
  Phase 5v Wave 10 sentence_state.py update).
- **Numerics:** open count 18 → 0 via QI-level structural closure;
  `qi_register.py` status filter (Wave 6 fix) now correctly excludes
  CountFreshness from Open Items aggregate.

---

### qi-crosspaperconsistency — closed 2026-04-29 by Phase 6i Wave 3

- **Evidence on close:** `docs/phase6i_wave3_close.md`
- **Mechanism:** All 35 open CrossPaperConsistency ReviewFinding nodes
  flipped via supersession ledger entries +/or content fixes.
- **Numerics:** open count 35 → 0 (100%).

### qi-fixpropagation-tracking — opened + closed 2026-04-28 by Phase 6i Wave 2 Stage 13 follow-up

- **Evidence on close:** `docs/phase6i_wave2_close.md` +
  `docs/review_finding_supersessions.json`.
- **Mechanism:** Project-level supersession ledger; `extract_review_finding_nodes`
  honours per-finding status overrides.
- **Numerics:** 13 paper40 nodes flipped open → fixed; FixPropagation
  gate flips needs-recheck → passed.

### qi-leanproofsubstance — closed 2026-04-29 by Phase 6i Wave 4

- **Evidence on close:** `docs/phase6i_wave4_close.md`
- **Mechanism:** All 26 open LeanProofSubstance ReviewFinding nodes
  flipped via supersession ledger entries (12 STALE + 8 ACCEPTED + 6
  body-marked-CLOSED-self-disclosed). New `scripts/audit_paper_lean_refs.py`
  ships as the durable mechanism: walks every paper_draft.tex,
  extracts `\texttt{}` Lean-ident candidates, cross-checks against
  `lean/lean_deps.json`. Codifies `feedback_python_lean_refs_drift.md`
  pattern.
- **Numerics:** open count 26 → 0 (100%); audit script: 786 candidate
  refs across 40 papers, 617 OK / 159 ABSENT (mostly Mathlib /
  module-name idioms) / 10 DRIFTED (paper-convention `<Module>.<thm>`
  notation, accepted as documentation idiom).

### qi-narrativegrounding — closed 2026-04-29 by Phase 6i Wave 3

- **Evidence on close:** `docs/phase6i_wave3_close.md`
- **Mechanism:** All 33 open NarrativeGrounding ReviewFinding nodes
  flipped via supersession ledger entries +/or targeted content fixes.
- **Numerics:** open count 33 → 0 (100%).

### qi-parameterprovenance — closed 2026-04-28 by Phase 6i Wave 2

- **Evidence on close:** `docs/phase6i_wave2_close.md`
- **Mechanism:** 124 of 174 PARAMETER_PROVENANCE entries flipped via
  bulk-flipper sweep; `--strict` flag added to `validate.py`.
- **Numerics:** human-verified 0 → 128 (74%); strict-blocker count = 2.

### qi-productionrunhealth — closed 2026-04-29 by Phase 6i Wave 6

- **Evidence on close:** `docs/phase6i_wave6_close.md`
- **Mechanism:** Single ProductionRunHealth ReviewFinding (paper27
  8.1) classified as no-applicable-scope: paper27 makes no
  production-run claims requiring backing data. The original review
  body explicitly states "STATUS UNCHANGED — No production runs
  claimed". Advisory accepted via supersession ledger.
- **Numerics:** open count 1 → 0.

### qi-provenance-citation-coverage — opened + closed 2026-04-28 by Phase 6i Wave 2 (cited_bibkeys side)

- **Evidence on close:** `docs/phase6i_wave2_close.md`
- **Mechanism:** New `validate.py --check provenance_doi_in_registry`
  (CHECK 20). Default mode advisory; `--strict` promotes to fail.
- **Numerics:** 70 of 99 provenance DOIs resolved at W2 close; 29
  advisory residuals queued for Wave 4.

### qi-provenance-doi-coverage — opened + closed 2026-04-29 by Phase 6i Wave 4

- **Origin:** Wave 2 close report — 29 advisory CHECK-20 missing-DOI
  residuals queued for Wave 4.
- **Evidence on close:** `docs/phase6i_wave4_close.md` +
  `src/core/citations.py` (13 new bibkey entries) +
  `src/core/provenance.py` (1 DOI typo fix).
- **Mechanism:** Registered 13 new bibkeys covering the 29 missing
  DOIs (PDG2024Particle covers 7 EW.* entries; LIGOSensitivity2015
  covers 2 GW frequency entries; Abbott2017GW170817Detection covers 2
  GW170817 inspiral entries; DESI2024DR2 covers 2 FLRW dark-energy
  entries; WaveDeepResearchSMG2024 covers 4 MAJORANA.C_SMG_*; etc.).
  Fixed the ChristensenDuff1979 DOI typo `(79)90516-4 → (79)90516-9`
  in PARAMETER_PROVENANCE['MICRO_MACRO.N_F_SM_DIRAC'].
- **Numerics:** missing DOIs 29 → 0; CHECK 20 now PASSES with 0
  warnings (was 1 advisory).

---

---

---

## Manual fields

The following fields are preserved across regenerations by matching on QI item `id`:

- `owner` — person responsible
- `target_date` — ISO 8601
- `status` — `open` / `in-progress` / `closed`
- `evidence_on_close` — commit hash or wave reference that remediated the pattern

To assign fields for a QI item, edit the item section inline. The generator does NOT overwrite manual fields (it matches on `id`). (Current generator is auto-regen-only; manual-field persistence is a follow-up.)
