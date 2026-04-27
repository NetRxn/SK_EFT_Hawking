---
paper: paper34_equivalence_principle
reviewer: adversarial-reviewer
model: claude-opus-4-7-1m
review_date: 2026-04-28T22:00:00Z
readiness_gates_version: 1
---

# Adversarial Review — paper34_equivalence_principle

## Summary

Cost-bounded review (Classes 1, 3, 4, 5, 6 only). The Lean module
`EquivalencePrinciple.lean` ships 26 substantive theorems plus a
`module_summary_marker : True := trivial` (excluded from substance
count). The bulk of the formalization is sound, but two Lean theorems
are P5 / within-own-tolerance tautologies that the paper cites as
"quantitative anchors" — they cannot fail and so do not constrain the
classification: `step_target_can_test_vestigial_relics : 1.0e-18 ≤ 1.0e-18 := le_refl _`
(literally `x ≤ x`, the project's audit memory flags this exact
pattern as P5) and `module_summary_marker : True := trivial`. One
narrative overclaim: the abstract says vestigial relics are
"sub-MICROSCOPE but within reach of next-generation satellite EP
tests," but the formalization never establishes the *reach* claim
beyond `1e-18 ≤ 1e-18`, which is just self-equality, not a bound on
detectability. Class 1 cache-skip on all four cited bibitems.

## Findings

### 3.1 — 🟡 REQUIRED — `step_target_can_test_vestigial_relics` is a self-equality tautology cited as a "quantitative anchor"

- **Gate:** LeanProofSubstance (Gate 5)
- **Location:** `paper34_equivalence_principle/paper_draft.tex:181-182`; `lean/SKEFTHawking/EquivalencePrinciple.lean:502-503`
- **Observed:** Lean theorem body: `theorem step_target_can_test_vestigial_relics : (1.0e-18 : ℝ) ≤ (1.0e-18 : ℝ) := le_refl _`. The statement is `x ≤ x`, which is true for any positive `x`; the theorem encodes no relationship between `STEP_TARGET` and `VESTIGIAL_RELICS_ETA` beyond what is already definitionally true (both numeric Python constants happen to be `1e-18`). The project's own audit memory (`feedback_post_wave_strengthening_audit.md`, summarized in `CLAUDE.md` lines 200-220) flags exactly this anti-pattern: "within-own-±2σ-band tautologies: `central - 2σ ≤ central ≤ central + 2σ` is vacuously true for any positive σ."
- **Evidence:** `EquivalencePrinciple.lean:502-503`. Paper cites this at line 181-182 ("\texttt{step\_target\_can\_test\_vestigial\_relics}") as one of the "quantitative anchors tying the classification to the published η-bound constants."
- **Expected:** A theorem with substantive content along the lines of `STEP_TARGET ≤ VESTIGIAL_RELICS_ETA ∧ VESTIGIAL_RELICS_ETA < MICROSCOPE_BOUND` — using *named distinct constants*, not two literal `1e-18` values, so a future redefinition of either constant would force the comparison to be re-validated. Or: replace with a falsifiable detection-margin statement like `VESTIGIAL_RELICS_ETA ≤ STEP_TARGET ⇒ detectable`.
- **Fix:** Replace the body with `STEP_TARGET ≤ VESTIGIAL_RELICS_ETA` (where these are *separately defined* constants, not both `1.0e-18` literals). If the constants are equal, prove via `rfl` *but* lift them to named definitions so the theorem statement reads `STEP_TARGET ≤ VESTIGIAL_RELICS_ETA`, exposing the structural relationship. Or remove this theorem and consolidate the η-anchor content into `vestigial_relics_below_microscope_bound` (which is genuinely substantive).

### 3.2 — 🔵 RECOMMENDED — `module_summary_marker : True := trivial` is decorative

- **Gate:** LeanProofSubstance (Gate 5)
- **Location:** `lean/SKEFTHawking/EquivalencePrinciple.lean:565`
- **Observed:** `theorem module_summary_marker : True := trivial`. The module's docstring already serves as a summary; this theorem adds no formal content.
- **Evidence:** Paper does not cite this theorem in prose; the abstract claim "26 substantive theorems" appears to exclude it (which is correct).
- **Expected:** Remove the marker theorem — it is purely decorative. Marker theorems fall under the project's audit memory anti-pattern catalog.
- **Fix:** Delete the declaration at lines 564-565 of `EquivalencePrinciple.lean`. Module docstring already documents the §6/§7 structure.

### 5.1 — 🔵 RECOMMENDED — abstract "within reach of next-generation satellite EP tests" is unsupported by the formalization

- **Gate:** NarrativeGrounding (Gate 7)
- **Location:** `paper34_equivalence_principle/paper_draft.tex:42-43`
- **Observed:** Abstract: "vestigial relics, which predict a residual η ∼ 10⁻¹⁸ from defect remnants in a full-tetrad phase, sub-MICROSCOPE but within reach of next-generation satellite EP tests." The "within reach" feasibility claim is not backed by any formal artifact: the Lean theorem `step_target_can_test_vestigial_relics` is a self-equality (Finding 3.1), and there is no `STEP-class` figure-of-merit, mission-specific reach computation, or ProductionRun backing the feasibility claim. The phrase "within reach" is exactly the kind of soft prose that Gate 7's `feasibility-claim` heuristic targets.
- **Evidence:** Searching `lean/SKEFTHawking/EquivalencePrinciple.lean` for "STEP", "next-generation", "sensitivity", "reach": only the within-own-tolerance theorem at line 502 surfaces.
- **Expected:** Either (a) tag this claim as interpretive/prospective with explicit "projected sensitivity" language, or (b) cite a primary-source reference for the STEP-class η ≤ 10⁻¹⁸ design sensitivity (e.g., Mester et al. 2001 Class. Quantum Grav. 18, 2475 or Overduin et al. 2012 Class. Quantum Grav. 29, 184012) and make it a registry-tracked citation.
- **Fix:** Add a citation to the STEP mission design paper at line 42-43; or change "within reach" → "at the η ∼ 10⁻¹⁸ design sensitivity discussed by next-generation EP missions [cite]."

### 6.1 — 🔵 RECOMMENDED — `vestigial_microscope_violation_consistent` first conjunct is a `rfl`

- **Gate:** LeanProofSubstance (Gate 5)
- **Location:** `lean/SKEFTHawking/EquivalencePrinciple.lean:378-385`
- **Observed:** The first conjunct, `(ClassificationTableDark.classification ClassificationTableDark.DarkMechanism.vestigialGravity).microscope = ClassificationTableDark.MicroscopeStatus.violated`, is closed by `rfl`. This means it is true by definitional unfolding alone — not a substantive structural fact. The second conjunct (`violatesAt vestigialDifferentialCoupling WEP = true`) is more substantive (`decide`-based). The combined theorem reads as a "bridge" but only one half is non-trivial.
- **Evidence:** `EquivalencePrinciple.lean:383`: `refine ⟨rfl, ?_⟩` closes the first conjunct.
- **Expected:** Either (a) consolidate to a single-conjunct theorem documenting only the substantive content `violatesAt vestigialDifferentialCoupling WEP = true ∧ classification.microscope = violated` is OK if the docstring acknowledges that the first half is `rfl`-closable and merely a sanity check, or (b) replace with a stronger biconditional, e.g. "`vestigialGravity.microscope = violated ↔ violatesAt vestigialDifferentialCoupling WEP = true`" — that would force the EP and Phase-5y bookkeeping to track each other under future renames.
- **Fix:** Add a docstring sentence noting "the first conjunct is `rfl` (a bookkeeping consistency check); the substantive structural content lives in the second conjunct via `decide`." Or upgrade to a biconditional bridge.

## Class 1 cache-skip summary

Bibitems inspected by author/title/venue plausibility:
- `Will2018` — *Theory and Experiment in Gravitational Physics* 2nd ed., CUP 2018 — `cache-skip` (well-known textbook).
- `Touboul2017` — arXiv:1712.01176, PRL 119, 231101 (2017), MICROSCOPE first results — `cache-skip`.
- `Pretko2017` — arXiv:1604.05329, PRB 95, 115139 (2017) — `cache-skip`.
- `Berezhiani2015` — arXiv:1507.01019, PRD 92, 103510 (2015) — `cache-skip`.

## Class 4 cross-paper consistency

`Touboul2017` is also cited in companion paper text in the broader project (the ClassificationTableDark module references MICROSCOPE elsewhere). Not a contradiction. No shared bibkeys with the other six papers in this batch.

## Class 6 assumption disclosure

`fangGu_failure_mode_is_kinematic_not_ep` consumes `fg_cdm_obstruction` from `FangGuTorsionDM`, which assumes `0 < s.rho` and `mink_trace s = 0`. Paper §3 last bullet describes this cross-bridge as "imports the Einstein-Cartan torsion module and invokes the torsion-trace obstruction theorem." Sufficient at the prose level; the specific structure-field assumptions (perfect-fluid traceless stress-energy) are not disclosed but are downstream of an already-established Phase 5x result. Marginal; not a finding.
