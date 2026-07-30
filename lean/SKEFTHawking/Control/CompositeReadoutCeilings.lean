/-
Phase 6EE Wave 3: end-to-end assignment-fidelity ceilings.

The capstone of the `6E*` series. Every mechanism floor in the series lower-bounds the SAME
quantity, `avgAssignmentError e₀ e₁ = (e₀+e₁)/2`:

  relaxation      `avgAssignmentError_rational_floor`   (QuantumNetwork.ReadoutRelaxationBound)
  thermal         `avgAssignmentError_thermal_floor`    (QuantumNetwork.ThermalAssignmentFloor)
  photon budget   `Detection.poisson_avgError_floor`    (6EA)
  filtered readout `Detection.error_floor_from_budget`  (6EB)
  detector chain  `Electrothermal.ETFModel.bolometer_error_floor` (6EC)

so they compose. This module turns each floor into a consumer-facing FIDELITY CEILING and states
how several of them combine.

⚠️ THE DEFECT CLASS THIS MODULE IS GATED ON. A composite that silently *under*-counts is fail-open
and is the worst defect available here. Two disciplines follow, and both are enforced structurally
rather than by comment:

  1. **Attribution is a hypothesis, never an assumption.** Every composition binds the mechanism
     floors as explicit hypotheses about the SAME `(e₀, e₁)` pair. Nothing is combined across
     readouts by fiat.
  2. **The sharper form is only available under a stated hypothesis.** The worst-mechanism (`max`)
     form is unconditionally sound and needs nothing. The additive form is strictly sharper but
     requires disjointness of the mechanisms' error events, supplied as a binder. The gap between
     the two is itself proved (`combined_floor_add_strictly_sharper`), so the sharpening is
     demonstrated rather than claimed.
-/

import Mathlib
import SKEFTHawking.QuantumNetwork.ReadoutRelaxationBound
import SKEFTHawking.QuantumNetwork.ThermalAssignmentFloor
import SKEFTHawking.Detection.PoissonDiscrimination
import SKEFTHawking.Detection.MatchedFilter
import SKEFTHawking.Electrothermal.BolometricFloors

set_option autoImplicit false

namespace SKEFTHawking.Control

open SKEFTHawking.QuantumNetwork

noncomputable section

/-! ## 1. Fidelity, and the floor → ceiling conversion -/

/-- Assignment **fidelity** of a binary readout: the complement of the averaged assignment error. -/
def assignmentFidelity (e0 e1 : ℝ) : ℝ := 1 - avgAssignmentError e0 e1

/-- **Floor → ceiling.** Any lower bound on the averaged assignment error is an upper bound on the
assignment fidelity. This is the uniform format every mechanism ceiling below is stated in. -/
theorem assignmentFidelity_le_of_floor {F e0 e1 : ℝ} (hfloor : F ≤ avgAssignmentError e0 e1) :
    assignmentFidelity e0 e1 ≤ 1 - F := by
  unfold assignmentFidelity
  linarith

/-! ## 2. Composing mechanisms -/

/-- **Worst-mechanism combined floor.** Unconditionally sound: no independence, no attribution
model, nothing beyond the two floors applying to the same readout. This is the form to reach for
when the mechanisms' error events might overlap. -/
theorem combined_floor_max {F₁ F₂ e0 e1 : ℝ}
    (h₁ : F₁ ≤ avgAssignmentError e0 e1) (h₂ : F₂ ≤ avgAssignmentError e0 e1) :
    max F₁ F₂ ≤ avgAssignmentError e0 e1 :=
  max_le h₁ h₂

/-- **Worst-mechanism ceiling** — the same statement in fidelity form. -/
theorem combined_ceiling_max {F₁ F₂ e0 e1 : ℝ}
    (h₁ : F₁ ≤ avgAssignmentError e0 e1) (h₂ : F₂ ≤ avgAssignmentError e0 e1) :
    assignmentFidelity e0 e1 ≤ 1 - max F₁ F₂ :=
  assignmentFidelity_le_of_floor (combined_floor_max h₁ h₂)

/-! ### 2.1 Disjointness, as actual measure theory

The additive form is only sound when the mechanisms' error events genuinely do not overlap. That
must be *derived* from disjoint events, not asserted: a hypothesis of the shape `ε₁ + ε₂ ≤ e₁` IS
the additive composition restated, so taking it as a binder would assume the very thing the
composite claims to establish — and would let a consumer obtain a sharper ceiling than their
budget licenses, which is the fail-open defect this module is gated on. -/

open MeasureTheory in
/-- **Disjoint error events add.** If mechanism 1's error event `A` and mechanism 2's error event
`B` are disjoint and both lie inside the branch-1 misassignment event `E`, then their individual
probabilities sum to at most the branch error. This is the theorem that earns the word
"disjointness"; everything additive downstream goes through it. -/
theorem add_le_branch_error_of_disjoint {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {A B E : Set Ω} (hB : MeasurableSet B)
    (hdisj : Disjoint A B) (hAE : A ⊆ E) (hBE : B ⊆ E)
    {ε₁ ε₂ e1 : ℝ} (h₁ : ε₁ ≤ (μ A).toReal) (h₂ : ε₂ ≤ (μ B).toReal)
    (he1 : (μ E).toReal ≤ e1) :
    ε₁ + ε₂ ≤ e1 := by
  have hunion : (μ (A ∪ B)).toReal = (μ A).toReal + (μ B).toReal := by
    rw [measure_union hdisj hB]
    exact ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)
  have hsub : (μ (A ∪ B)).toReal ≤ (μ E).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.union_subset hAE hBE))
  linarith

open MeasureTheory in
/-- **Additive combined floor, from genuinely disjoint error events.**

The disjointness is now measure-theoretic input (`Disjoint A B`, both inside the branch-1 error
event), and the additive bound is derived from it via `add_le_branch_error_of_disjoint` rather than
assumed. -/
theorem combined_floor_add {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {A B E : Set Ω} (hB : MeasurableSet B) (hdisj : Disjoint A B) (hAE : A ⊆ E) (hBE : B ⊆ E)
    {ε₁ ε₂ e0 e1 : ℝ} (he0 : 0 ≤ e0)
    (h₁ : ε₁ ≤ (μ A).toReal) (h₂ : ε₂ ≤ (μ B).toReal) (he1 : (μ E).toReal ≤ e1) :
    (ε₁ + ε₂) / 2 ≤ avgAssignmentError e0 e1 := by
  have hadd := add_le_branch_error_of_disjoint μ hB hdisj hAE hBE h₁ h₂ he1
  unfold avgAssignmentError
  linarith

open MeasureTheory in
/-- **Additive ceiling** — fidelity form, on the same measure-theoretic input. -/
theorem combined_ceiling_add {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {A B E : Set Ω} (hB : MeasurableSet B) (hdisj : Disjoint A B) (hAE : A ⊆ E) (hBE : B ⊆ E)
    {ε₁ ε₂ e0 e1 : ℝ} (he0 : 0 ≤ e0)
    (h₁ : ε₁ ≤ (μ A).toReal) (h₂ : ε₂ ≤ (μ B).toReal) (he1 : (μ E).toReal ≤ e1) :
    assignmentFidelity e0 e1 ≤ 1 - (ε₁ + ε₂) / 2 :=
  assignmentFidelity_le_of_floor (combined_floor_add μ hB hdisj hAE hBE he0 h₁ h₂ he1)

/-- Arithmetic core of the sharpening (`max(a,b) < a+b` for positive `a, b`). Stated separately so
that the ceiling-level comparison below is visibly a statement about the two CEILINGS and not about
bare reals. -/
private theorem max_half_lt_half_add {ε₁ ε₂ : ℝ} (h₁ : 0 < ε₁) (h₂ : 0 < ε₂) :
    max (ε₁ / 2) (ε₂ / 2) < (ε₁ + ε₂) / 2 := by
  rcases max_cases (ε₁ / 2) (ε₂ / 2) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> linarith

open MeasureTheory in
/-- **The additive ceiling is STRICTLY tighter than the worst-mechanism ceiling on the SAME
readout.** Both bounds are derived here from one shared hypothesis set — the measure-theoretic
disjointness input plus each mechanism's own floor — so this is a comparison of the two composite
theorems' conclusions, not an inequality between unrelated reals.

This is what makes carrying the disjointness input worthwhile: without a strict gap the additive
form would be the max form with extra hypotheses. -/
theorem combined_ceiling_add_lt_max {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {A B E : Set Ω} (hB : MeasurableSet B) (hdisj : Disjoint A B)
    (hAE : A ⊆ E) (hBE : B ⊆ E) {ε₁ ε₂ e0 e1 : ℝ} (he0 : 0 ≤ e0)
    (h₁ : ε₁ ≤ (μ A).toReal) (h₂ : ε₂ ≤ (μ B).toReal) (he1 : (μ E).toReal ≤ e1)
    (hp₁ : 0 < ε₁) (hp₂ : 0 < ε₂)
    (hf₁ : ε₁ / 2 ≤ avgAssignmentError e0 e1) (hf₂ : ε₂ / 2 ≤ avgAssignmentError e0 e1) :
    (1 - (ε₁ + ε₂) / 2 : ℝ) < 1 - max (ε₁ / 2) (ε₂ / 2)
      ∧ assignmentFidelity e0 e1 ≤ 1 - (ε₁ + ε₂) / 2
      ∧ assignmentFidelity e0 e1 ≤ 1 - max (ε₁ / 2) (ε₂ / 2) := by
  refine ⟨by linarith [max_half_lt_half_add hp₁ hp₂], ?_, ?_⟩
  · exact combined_ceiling_add μ hB hdisj hAE hBE he0 h₁ h₂ he1
  · exact combined_ceiling_max hf₁ hf₂

/-- **Numeric witness of the sharpening.** At mechanism floors `ε₁ = 1/100`, `ε₂ = 1/50` the
worst-mechanism ceiling is `1 - 1/100` while the additive ceiling is `1 - 3/200`: a gap of exactly
`1/200`. The AC asks for the difference to be *witnessed*, and a witness is a number. -/
theorem combined_ceiling_gap_witness :
    (1 : ℝ) - ((1 / 100 : ℝ) + 1 / 50) / 2 < 1 - max ((1 / 100 : ℝ) / 2) ((1 / 50 : ℝ) / 2)
      ∧ (1 - max ((1 / 100 : ℝ) / 2) ((1 / 50 : ℝ) / 2))
          - (1 - ((1 / 100 : ℝ) + 1 / 50) / 2) = 1 / 200 := by
  norm_num

/-! ## 3. Per-mechanism ceilings

Each takes its mechanism's floor as an explicit hypothesis about this readout's `(e₀, e₁)`, so the
attribution is visible in the type rather than assumed in prose. -/

/-- **Relaxation ceiling** (format anchor; cites `avgAssignmentError_rational_floor`, no re-proof). -/
theorem relaxation_ceiling {t T1 e0 e1 : ℝ} (ht : 0 ≤ t) (hT1 : 0 < T1)
    (he0 : 0 ≤ e0) (he1 : readoutDecayProb t T1 ≤ e1) :
    assignmentFidelity e0 e1 ≤ 1 - t / T1 / (2 * (1 + t / T1)) :=
  assignmentFidelity_le_of_floor (avgAssignmentError_rational_floor ht hT1 he0 he1)

/-- **Relaxation ⊕ thermal ceiling** — the existing two-mechanism worst-case composition, restated
in the uniform ceiling format. -/
theorem relaxation_thermal_ceiling {t T1 x e0 e1 : ℝ} (he0 : 0 ≤ e0)
    (hd : readoutDecayProb t T1 ≤ e1) (hth : thermalExcitedPop x ≤ e1) :
    assignmentFidelity e0 e1 ≤ 1 - max (readoutDecayProb t T1) (thermalExcitedPop x) / 2 :=
  assignmentFidelity_le_of_floor (avgAssignmentError_combined_floor he0 hd hth)

/-- **Photon-budget ceiling (6EA).** Specialised to the 6EA Poisson objects: the error pair is the
count rule's own `(falseAlarm, missProb)`, and the floor is the Bhattacharyya-affinity form. -/
theorem photon_budget_ceiling {Nb Na : NNReal} {δ : ℕ → ℝ} (hδ : Detection.IsCountRule δ) :
    assignmentFidelity (Detection.falseAlarm Nb δ) (Detection.missProb Na δ)
      ≤ 1 - (1 / 4) * Real.exp (-(Real.sqrt (Na : ℝ) - Real.sqrt (Nb : ℝ)) ^ 2) :=
  assignmentFidelity_le_of_floor (Detection.poisson_avgError_floor hδ)

open MeasureTheory in
/-- **Filtered-readout ceiling (6EB).** DERIVED, not assumed: the floor is discharged by calling
`Detection.error_floor_from_budget`, so this carries that theorem's own physical binder list
(whiteness of the filtered variance, filter admissibility, the mean-separation identity, `σ` from
the filtered variance) rather than its conclusion. -/
theorem filtered_readout_ceiling {V : (ℝ → ℝ) → ℝ} {S₀ T : ℝ}
    (hwhite : Detection.IsWhiteFilteredVariance V S₀ T) (hS : 0 < S₀) (hT : 0 ≤ T)
    {s h : ℝ → ℝ} (hadm : Detection.IsAdmissibleFilter T s h)
    (hs : IntervalIntegrable (fun x => s x ^ 2) volume 0 T)
    {μ₀ μ₁ σ t : ℝ} (hσ : 0 < σ) (hμle : μ₀ ≤ μ₁)
    (hμ : μ₁ - μ₀ = ∫ x in (0:ℝ)..T, h x * s x) (hσV : σ = Real.sqrt (V h)) :
    assignmentFidelity (Detection.thrErr0 μ₀ σ t) (Detection.thrErr1 μ₁ σ t)
      ≤ 1 - Detection.gaussianQ (Detection.matchedBudget S₀ T s / 2) :=
  assignmentFidelity_le_of_floor
    (Detection.error_floor_from_budget hwhite hS hT hadm hs hσ hμle hμ hσV)

open MeasureTheory in
/-- **Detector-chain ceiling (6EC).** DERIVED by calling `Electrothermal.ETFModel.bolometer_error_floor`,
so every link of the chain — detector NEP → filter → Gaussian error → fidelity — is actually
traversed. What distinguishes it from the 6EB ceiling is that the noise budget is the bolometer's
own phonon ⊕ Johnson quadrature sum rather than a free parameter, and `m` is genuinely load-bearing
(it supplies `G`, `phononNEP`, `johnsonNEP`). -/
theorem detector_chain_ceiling (m : Electrothermal.ETFModel) {kB T Tw : ℝ}
    {Vtot : (ℝ → ℝ) → ℝ} {V : Fin 2 → (ℝ → ℝ) → ℝ} {s hf : ℝ → ℝ} {μ₀ μ₁ σ t : ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hG : 0 < m.G)
    (hindep : Detection.IsUncorrelatedAt Finset.univ Vtot V)
    (hphonon : Electrothermal.ETFModel.IsThermalFluctuationLimited (V 0) m kB T Tw)
    (hjohnson : Detection.IsWhiteFilteredVariance (V 1) (m.johnsonNEP kB T ^ 2) Tw)
    (hTw : 0 ≤ Tw) (hadm : Detection.IsAdmissibleFilter Tw s hf)
    (hs : IntervalIntegrable (fun x => s x ^ 2) volume 0 Tw)
    (hσ : 0 < σ) (hμle : μ₀ ≤ μ₁)
    (hμ : μ₁ - μ₀ = ∫ x in (0:ℝ)..Tw, hf x * s x) (hσV : σ = Real.sqrt (Vtot hf)) :
    assignmentFidelity (Detection.thrErr0 μ₀ σ t) (Detection.thrErr1 μ₁ σ t)
      ≤ 1 - Detection.gaussianQ
        (Detection.matchedBudget (m.phononNEP kB T ^ 2 + m.johnsonNEP kB T ^ 2) Tw s / 2) :=
  assignmentFidelity_le_of_floor
    (m.bolometer_error_floor hkB hT hG hindep hphonon hjohnson hTw hadm hs hσ hμle hμ hσV)

/-! ## 4. Witness pairs

Both witnesses use the RELAXATION floor, which is rational in `t/T₁` and therefore settles under
`norm_num` without any transcendental bound. (The Poisson floor's available lower enclosure
`1 - r ≤ exp(-r)` is vacuous for `r ≥ 1`, so it cannot witness a bite at a realistic operating
point; using it here would have produced a witness that looks quantitative but proves nothing.) -/

/-- **The ceiling BITES.** At `t = T₁` the relaxation floor is `1/4`, so no readout of this
duration can exceed fidelity `3/4` — a claimed `0.99` is refuted outright. -/
theorem relaxation_ceiling_bites {e0 e1 : ℝ} (he0 : 0 ≤ e0)
    (he1 : readoutDecayProb 1 1 ≤ e1) :
    assignmentFidelity e0 e1 ≤ 3 / 4 := by
  have h := relaxation_ceiling (t := 1) (T1 := 1) (by norm_num) (by norm_num) he0 he1
  norm_num at h
  linarith

/-- **The ceiling does NOT bite.** At `t = T₁/1000` the same ceiling is `1 - 1/2002`, which permits
a `0.999` readout. The pair together shows the ceiling is informative in one regime and
non-binding in the other — i.e. it tracks the budget rather than being vacuous or always-fatal. -/
theorem relaxation_ceiling_does_not_bite :
    (1 : ℝ) - (1 / 1000) / 1 / (2 * (1 + (1 / 1000) / 1)) > 999 / 1000 := by
  norm_num

end

end SKEFTHawking.Control
