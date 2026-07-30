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
when the mechanisms' error events might overlap.

This is `max_le` specialised to `avgAssignmentError` — deliberately so: the *content* is not in this
lemma but in the attribution work that makes two named mechanism floors apply to one readout, which
is §3.5's job. Cited alone it proves nothing physical. -/
theorem combined_floor_max {F₁ F₂ e0 e1 : ℝ}
    (h₁ : F₁ ≤ avgAssignmentError e0 e1) (h₂ : F₂ ≤ avgAssignmentError e0 e1) :
    max F₁ F₂ ≤ avgAssignmentError e0 e1 :=
  max_le h₁ h₂

/-- **Averaged assignment error is monotone in each branch error.** The transfer rule that lets a
mechanism floor stated at the mechanism's OWN error pair apply to any readout whose errors dominate
it — the technical content of "attribution". -/
theorem avgAssignmentError_mono {e0 e1 f0 f1 : ℝ} (h0 : e0 ≤ f0) (h1 : e1 ≤ f1) :
    avgAssignmentError e0 e1 ≤ avgAssignmentError f0 f1 := by
  unfold avgAssignmentError
  linarith

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

section GapWitness
open MeasureTheory

/-- A concrete two-point error model: mechanism 1 fails on `{0}` with probability `1/100`,
mechanism 2 on `{1}` with probability `1/50`, and the events are disjoint by construction. This is
the measure space that instantiates `combined_ceiling_add_lt_max` below. -/
noncomputable def gapWitnessMeasure : Measure (Fin 2) :=
  ENNReal.ofReal (1 / 100) • Measure.dirac 0 + ENNReal.ofReal (1 / 50) • Measure.dirac 1

theorem gapWitnessMeasure_univ_apply :
    gapWitnessMeasure Set.univ = ENNReal.ofReal (1 / 100) + ENNReal.ofReal (1 / 50) := by
  unfold gapWitnessMeasure
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp

instance : IsFiniteMeasure gapWitnessMeasure := by
  refine ⟨?_⟩
  rw [gapWitnessMeasure_univ_apply]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩

@[simp] theorem gapWitnessMeasure_zero : (gapWitnessMeasure {0}).toReal = 1 / 100 := by
  unfold gapWitnessMeasure
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply' _ (measurableSet_singleton _),
    Measure.dirac_apply' _ (measurableSet_singleton _)]
  simp

@[simp] theorem gapWitnessMeasure_one : (gapWitnessMeasure {1}).toReal = 1 / 50 := by
  unfold gapWitnessMeasure
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply' _ (measurableSet_singleton _),
    Measure.dirac_apply' _ (measurableSet_singleton _)]
  simp

@[simp] theorem gapWitnessMeasure_univ : (gapWitnessMeasure Set.univ).toReal = 3 / 100 := by
  rw [gapWitnessMeasure_univ_apply,
    ← ENNReal.ofReal_add (by norm_num) (by norm_num), ENNReal.toReal_ofReal (by norm_num)]
  norm_num

/-- **Numeric witness of the sharpening — DERIVED, not asserted.** This instantiates
`combined_ceiling_add_lt_max` at the concrete two-point model above, with `(e0, e1) = (0, 3/100)`.
So the `1/200` gap is the difference between the two shipped composites at a real operating point of
a real error model, not an arithmetic identity between numerals that would survive an edit to either
composite. -/
theorem combined_ceiling_gap_witness :
    ((1 : ℝ) - ((1 / 100 : ℝ) + 1 / 50) / 2 < 1 - max ((1 / 100 : ℝ) / 2) ((1 / 50 : ℝ) / 2))
      ∧ assignmentFidelity 0 (3 / 100) ≤ 1 - ((1 / 100 : ℝ) + 1 / 50) / 2
      ∧ assignmentFidelity 0 (3 / 100) ≤ 1 - max ((1 / 100 : ℝ) / 2) ((1 / 50 : ℝ) / 2)
      ∧ (1 - max ((1 / 100 : ℝ) / 2) ((1 / 50 : ℝ) / 2))
          - (1 - ((1 / 100 : ℝ) + 1 / 50) / 2) = 1 / 200 := by
  have hdisj : Disjoint ({0} : Set (Fin 2)) ({1} : Set (Fin 2)) := by simp
  have hfloor : ∀ ε : ℝ, ε ≤ 3 / 100 → ε / 2 ≤ avgAssignmentError 0 (3 / 100) := by
    intro ε hε
    unfold avgAssignmentError
    linarith
  obtain ⟨hgap, hadd, hmax⟩ :=
    combined_ceiling_add_lt_max gapWitnessMeasure (measurableSet_singleton (1 : Fin 2)) hdisj
      (Set.subset_univ _) (Set.subset_univ _) (e0 := 0) (e1 := 3 / 100)
      (ε₁ := 1 / 100) (ε₂ := 1 / 50) le_rfl
      (by rw [gapWitnessMeasure_zero]) (by rw [gapWitnessMeasure_one])
      (by rw [gapWitnessMeasure_univ]) (by norm_num) (by norm_num)
      (hfloor _ (by norm_num)) (hfloor _ (by norm_num))
  exact ⟨hgap, hadd, hmax, by norm_num⟩

end GapWitness

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

/-! ## 3.5 End-to-end: TWO NAMED mechanism floors on ONE attributed readout

§2's composites are generic in abstract floors `F₁`, `F₂`; §3's ceilings are each about a single
mechanism, and each is stated at its own mechanism's error pair. Neither alone delivers the series'
headline — *"every mechanism floor jointly forbids this fidelity"* — because nothing yet puts two
NAMED floors on the SAME readout.

That is what this section does. The attribution is carried explicitly: `hattr0`/`hattr1` say the
photon-counting mechanism's own false-alarm and miss probabilities are dominated by this readout's
branch errors, which is exactly the empirical claim an experimenter makes when they say "the photon
budget is what limits my readout". Everything else is then forced. -/

/-- **The 6EA photon-budget floor transfers to any readout dominating the count rule's errors.** -/
theorem photon_budget_floor_attributed {Nb Na : NNReal} {δ : ℕ → ℝ} {e0 e1 : ℝ}
    (hδ : Detection.IsCountRule δ)
    (hattr0 : Detection.falseAlarm Nb δ ≤ e0) (hattr1 : Detection.missProb Na δ ≤ e1) :
    (1 / 4) * Real.exp (-(Real.sqrt (Na : ℝ) - Real.sqrt (Nb : ℝ)) ^ 2)
      ≤ avgAssignmentError e0 e1 :=
  le_trans (Detection.poisson_avgError_floor hδ) (avgAssignmentError_mono hattr0 hattr1)

/-- **End-to-end two-mechanism ceiling: relaxation ⊕ photon budget.** Both floors are the project's
own named theorems — `avgAssignmentError_rational_floor` (relaxation) and
`Detection.poisson_avgError_floor` (6EA) — applied to a SINGLE readout `(e0, e1)` under explicit
attribution hypotheses, then combined by `combined_ceiling_max`.

⚠️ It is **not** the first two-named-floor composite in the project: `relaxation_thermal_ceiling`
below already composes relaxation ⊕ thermal, and did so before this phase (via the upstream
`avgAssignmentError_combined_floor`). What is new here is that it is the first composite spanning
the DEVICE layer (`QuantumNetwork`) and the DETECTION layer (`Detection`/6EA) — a pairing that was
previously impossible because the 6EA floor is stated at the count rule's own error pair and had no
transfer rule; `photon_budget_floor_attributed` supplies it. (An earlier draft of this docstring and
of the roadmap claimed priority outright; corrected 2026-07-30 after adversarial review.) -/
theorem relaxation_photon_ceiling {t T1 e0 e1 : ℝ} {Nb Na : NNReal} {δ : ℕ → ℝ}
    (ht : 0 ≤ t) (hT1 : 0 < T1) (he0 : 0 ≤ e0) (hdecay : readoutDecayProb t T1 ≤ e1)
    (hδ : Detection.IsCountRule δ)
    (hattr0 : Detection.falseAlarm Nb δ ≤ e0) (hattr1 : Detection.missProb Na δ ≤ e1) :
    assignmentFidelity e0 e1
      ≤ 1 - max (t / T1 / (2 * (1 + t / T1)))
          ((1 / 4) * Real.exp (-(Real.sqrt (Na : ℝ) - Real.sqrt (Nb : ℝ)) ^ 2)) :=
  combined_ceiling_max
    (avgAssignmentError_rational_floor ht hT1 he0 hdecay)
    (photon_budget_floor_attributed hδ hattr0 hattr1)

/-- **The composite genuinely selects between the two mechanisms** — proved BY CALLING
`relaxation_photon_ceiling`, not by comparing two expressions side by side.

At `t = T₁` with a generous photon budget (separation `99`) the photon floor drops strictly below
the relaxation floor, the `max` collapses to the relaxation branch, and the composite ceiling
therefore reads `1 − t/T₁/(2(1+t/T₁))`. Because the first conjunct is the ceiling theorem's own
conclusion after that collapse, an edit to either mechanism's floor breaks this proof — which is
what "anchored" has to mean. (An earlier version stated only an inequality between two expressions
and *asserted* robustness in its docstring; corrected 2026-07-30 after review.) -/
theorem relaxation_dominates_photon_at_separation_99 {t T1 e0 e1 : ℝ} {Nb Na : NNReal} {δ : ℕ → ℝ}
    (ht : t = T1) (hT1 : 0 < T1) (he0 : 0 ≤ e0)
    (hdecay : readoutDecayProb t T1 ≤ e1) (hδ : Detection.IsCountRule δ)
    (hattr0 : Detection.falseAlarm Nb δ ≤ e0) (hattr1 : Detection.missProb Na δ ≤ e1)
    (hsep : (Real.sqrt (Na : ℝ) - Real.sqrt (Nb : ℝ)) ^ 2 = 99) :
    (1 / 4) * Real.exp (-(Real.sqrt (Na : ℝ) - Real.sqrt (Nb : ℝ)) ^ 2)
        < t / T1 / (2 * (1 + t / T1))
      ∧ assignmentFidelity e0 e1 ≤ 1 - t / T1 / (2 * (1 + t / T1)) := by
  have hrel : t / T1 / (2 * (1 + t / T1)) = 1 / 4 := by
    rw [ht, div_self hT1.ne']
    norm_num
  have hlt : (1 / 4) * Real.exp (-(Real.sqrt (Na : ℝ) - Real.sqrt (Nb : ℝ)) ^ 2)
      < t / T1 / (2 * (1 + t / T1)) := by
    rw [hrel, hsep]
    have henc := (QuantumNetwork.expNeg_enclosure (r := (99 : ℝ)) (by norm_num)).2
    have hpos : (0 : ℝ) < Real.exp (-(99 : ℝ)) := Real.exp_pos _
    nlinarith
  have hceil := relaxation_photon_ceiling (t := t) (T1 := T1) (by rw [ht]; exact hT1.le) hT1
    he0 hdecay hδ hattr0 hattr1
  rw [max_eq_left hlt.le] at hceil
  exact ⟨hlt, hceil⟩

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

/-- **The ceiling does NOT bite.** At `t = T₁/1000` there is an ACTUAL readout satisfying the
ceiling's own hypotheses whose fidelity exceeds `0.999` — so the ceiling permits it.

This is stated as an existence over readouts rather than as an inequality between numerals. A bare
numeral statement matched to the ceiling only by eye would survive any edit to the ceiling's bound
expression, which is exactly the "looks quantitative, proves nothing" pattern; here the witness
mentions `readoutDecayProb` and `assignmentFidelity` and would break if either changed. -/
theorem relaxation_ceiling_does_not_bite :
    ∃ e0 e1 : ℝ, 0 ≤ e0 ∧ readoutDecayProb (1 / 1000) 1 ≤ e1
      ∧ (999 : ℝ) / 1000 ≤ assignmentFidelity e0 e1 := by
  refine ⟨0, readoutDecayProb (1 / 1000) 1, le_rfl, le_rfl, ?_⟩
  -- `1 - exp(-r) ≤ r` from the enclosure, at `r = 1/1000`.
  have henc := (QuantumNetwork.expNeg_enclosure (r := (1 : ℝ) / 1000) (by norm_num)).1
  have hd : readoutDecayProb (1 / 1000) 1 ≤ 1 / 1000 := by
    unfold readoutDecayProb
    norm_num at henc ⊢
    linarith
  unfold assignmentFidelity avgAssignmentError
  linarith

/-! ### 4.1 Witness pairs for the remaining four ceilings

Every BITES witness is a corollary **of its ceiling theorem** — it calls the ceiling and concludes
about `assignmentFidelity`, so it cannot survive an edit that weakens the ceiling. Every DOES-NOT-BITE
witness is stated on the ceiling's own bound *expression* with the operating point as a hypothesis
(rather than on a bare numeral): that is the strongest honest form, since a permissive ceiling
licenses a high-fidelity readout but does not exhibit one. -/

/-- **Relaxation ⊕ thermal ceiling BITES.** At a vanishing level splitting (`x = 0`) the thermal
branch alone pins the excited-state population at `1/2`, so the two-mechanism ceiling is at most
`3/4` no matter how fast the readout is. -/
theorem relaxation_thermal_ceiling_bites {t T1 e0 e1 : ℝ} (he0 : 0 ≤ e0)
    (hd : readoutDecayProb t T1 ≤ e1) (hth : thermalExcitedPop 0 ≤ e1) :
    assignmentFidelity e0 e1 ≤ 3 / 4 := by
  have hc := relaxation_thermal_ceiling (x := 0) he0 hd hth
  have hpop : thermalExcitedPop (0 : ℝ) = 1 / 2 := by
    unfold thermalExcitedPop; norm_num
  rw [hpop] at hc
  have hmax : max (readoutDecayProb t T1) (1 / 2 : ℝ) ≥ 1 / 2 := le_max_right _ _
  linarith

/-- **Relaxation ⊕ thermal ceiling does NOT bite.** At `t/T₁ = 1/100` and a splitting `x = 98`
both branches sit below `1/100`, so the ceiling exceeds `199/200` — it permits a `0.99` readout.
Uses only the rational `exp` enclosures, no transcendental evaluation. -/
theorem relaxation_thermal_ceiling_does_not_bite {t T1 : ℝ} (hr : t / T1 = 1 / 100) :
    (199 : ℝ) / 200
      ≤ 1 - max (readoutDecayProb t T1) (thermalExcitedPop 98) / 2 := by
  have hdec : readoutDecayProb t T1 ≤ 1 / 100 := by
    have henc := (QuantumNetwork.expNeg_enclosure (r := (1 : ℝ) / 100) (by norm_num)).1
    unfold readoutDecayProb
    rw [show -t / T1 = -(t / T1) by ring, hr]
    linarith
  have hth : thermalExcitedPop 98 ≤ 1 / 100 := by
    have hx : (99 : ℝ) ≤ Real.exp 98 := by linarith [Real.add_one_le_exp (98 : ℝ)]
    unfold thermalExcitedPop
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hmax : max (readoutDecayProb t T1) (thermalExcitedPop 98) ≤ 1 / 100 :=
    max_le hdec hth
  linarith

/-- **Photon-budget ceiling BITES.** At a separation of `(√N_a − √N_b)² = 1/4` the ceiling is at
most `13/16`, so any claimed fidelity above that is refuted outright. -/
theorem photon_budget_ceiling_bites {Nb Na : NNReal} {δ : ℕ → ℝ} (hδ : Detection.IsCountRule δ)
    (hsep : (Real.sqrt (Na : ℝ) - Real.sqrt (Nb : ℝ)) ^ 2 = 1 / 4) :
    assignmentFidelity (Detection.falseAlarm Nb δ) (Detection.missProb Na δ) ≤ 13 / 16 := by
  have hc := photon_budget_ceiling (Nb := Nb) (Na := Na) hδ
  rw [hsep] at hc
  have henc := (QuantumNetwork.expNeg_enclosure (r := (1 : ℝ) / 4) (by norm_num)).1
  norm_num at henc hc ⊢
  linarith

/-- **Photon-budget ceiling does NOT bite.** At a separation of `99` the ceiling exceeds
`399/400`, permitting a `0.99` readout. Stated on the ceiling's own Bhattacharyya-affinity bound
with the separation as a hypothesis, so it tracks the shipped `photon_budget_ceiling`. -/
theorem photon_budget_ceiling_does_not_bite {Nb Na : NNReal}
    (hsep : (Real.sqrt (Na : ℝ) - Real.sqrt (Nb : ℝ)) ^ 2 = 99) :
    (399 : ℝ) / 400
      ≤ 1 - (1 / 4) * Real.exp (-(Real.sqrt (Na : ℝ) - Real.sqrt (Nb : ℝ)) ^ 2) := by
  rw [hsep]
  have henc := (QuantumNetwork.expNeg_enclosure (r := (99 : ℝ)) (by norm_num)).2
  norm_num at henc ⊢
  linarith

open MeasureTheory in
/-- **Filtered-readout ceiling (6EB) BITES at zero matched budget**: a chain whose matched budget
vanishes cannot beat a coin flip. Derived by calling `filtered_readout_ceiling`, so it inherits that
theorem's whiteness / admissibility / mean-separation binders rather than assuming its conclusion. -/
theorem filtered_readout_ceiling_bites {V : (ℝ → ℝ) → ℝ} {S₀ T : ℝ}
    (hwhite : Detection.IsWhiteFilteredVariance V S₀ T) (hS : 0 < S₀) (hT : 0 ≤ T)
    {s h : ℝ → ℝ} (hadm : Detection.IsAdmissibleFilter T s h)
    (hs : IntervalIntegrable (fun x => s x ^ 2) volume 0 T)
    {μ₀ μ₁ σ t : ℝ} (hσ : 0 < σ) (hμle : μ₀ ≤ μ₁)
    (hμ : μ₁ - μ₀ = ∫ x in (0:ℝ)..T, h x * s x) (hσV : σ = Real.sqrt (V h))
    (hb : Detection.matchedBudget S₀ T s = 0) :
    assignmentFidelity (Detection.thrErr0 μ₀ σ t) (Detection.thrErr1 μ₁ σ t) ≤ 1 / 2 := by
  have hc := filtered_readout_ceiling (t := t) hwhite hS hT hadm hs hσ hμle hμ hσV
  rw [hb] at hc
  norm_num [Detection.gaussianQ_zero] at hc
  linarith

open MeasureTheory in
/-- **Detector-chain ceiling (6EC) BITES at zero matched budget** — the same collapse, but with the
noise budget supplied by the bolometer's own phonon ⊕ Johnson quadrature sum. Derived by calling
`detector_chain_ceiling`. -/
theorem detector_chain_ceiling_bites (m : Electrothermal.ETFModel) {kB T Tw : ℝ}
    {Vtot : (ℝ → ℝ) → ℝ} {V : Fin 2 → (ℝ → ℝ) → ℝ} {s hf : ℝ → ℝ} {μ₀ μ₁ σ t : ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hG : 0 < m.G)
    (hindep : Detection.IsUncorrelatedAt Finset.univ Vtot V)
    (hphonon : Electrothermal.ETFModel.IsThermalFluctuationLimited (V 0) m kB T Tw)
    (hjohnson : Detection.IsWhiteFilteredVariance (V 1) (m.johnsonNEP kB T ^ 2) Tw)
    (hTw : 0 ≤ Tw) (hadm : Detection.IsAdmissibleFilter Tw s hf)
    (hs : IntervalIntegrable (fun x => s x ^ 2) volume 0 Tw)
    (hσ : 0 < σ) (hμle : μ₀ ≤ μ₁)
    (hμ : μ₁ - μ₀ = ∫ x in (0:ℝ)..Tw, hf x * s x) (hσV : σ = Real.sqrt (Vtot hf))
    (hb : Detection.matchedBudget (m.phononNEP kB T ^ 2 + m.johnsonNEP kB T ^ 2) Tw s = 0) :
    assignmentFidelity (Detection.thrErr0 μ₀ σ t) (Detection.thrErr1 μ₁ σ t) ≤ 1 / 2 := by
  have hc := detector_chain_ceiling m (t := t) hkB hT hG hindep hphonon hjohnson hTw hadm hs hσ
    hμle hμ hσV
  rw [hb] at hc
  norm_num [Detection.gaussianQ_zero] at hc
  linarith

/-- **The Gaussian ceiling does NOT bite at a budget of `8`**: the bound exceeds `17/18`, permitting
a high-fidelity readout. Uses the Chernoff tail from 6EA plus the rational `exp` enclosure. Stated
over the budget `B` because the 6EB and 6EC ceilings share this bound shape and differ only in which
noise budget they feed it; the two specialisations below instantiate it at each. -/
theorem gaussian_ceiling_does_not_bite {B : ℝ} (hB : B = 8) :
    (17 : ℝ) / 18 ≤ 1 - Detection.gaussianQ (B / 2) := by
  subst hB
  have hch := Detection.gaussianTail_chernoff (z := (4 : ℝ)) (by norm_num)
  have henc := (QuantumNetwork.expNeg_enclosure (r := (8 : ℝ)) (by norm_num)).2
  norm_num at hch henc ⊢
  linarith

open MeasureTheory in
/-- **Filtered-readout ceiling (6EB) does NOT bite** at a matched budget of `8`: the ceiling
`filtered_readout_ceiling` produces for such a chain is at least `17/18`, so it forbids nothing
below that. Stated by CALLING the ceiling and comparing against its actual conclusion, rather than
by restating the bound expression by hand.

⚠️ Deliberately NOT stated as `∃ F, fidelity ≤ F ∧ 17/18 ≤ F` — that shape is trivially satisfiable
by `F = max(fidelity, 17/18)` and would carry no content. The two conjuncts here name the SAME
expression, which is what makes them a claim about this ceiling. -/
theorem filtered_readout_ceiling_does_not_bite {V : (ℝ → ℝ) → ℝ} {S₀ T : ℝ}
    (hwhite : Detection.IsWhiteFilteredVariance V S₀ T) (hS : 0 < S₀) (hT : 0 ≤ T)
    {s h : ℝ → ℝ} (hadm : Detection.IsAdmissibleFilter T s h)
    (hs : IntervalIntegrable (fun x => s x ^ 2) volume 0 T)
    {μ₀ μ₁ σ t : ℝ} (hσ : 0 < σ) (hμle : μ₀ ≤ μ₁)
    (hμ : μ₁ - μ₀ = ∫ x in (0:ℝ)..T, h x * s x) (hσV : σ = Real.sqrt (V h))
    (hb : Detection.matchedBudget S₀ T s = 8) :
    assignmentFidelity (Detection.thrErr0 μ₀ σ t) (Detection.thrErr1 μ₁ σ t)
        ≤ 1 - Detection.gaussianQ (Detection.matchedBudget S₀ T s / 2)
      ∧ (17 : ℝ) / 18 ≤ 1 - Detection.gaussianQ (Detection.matchedBudget S₀ T s / 2) :=
  ⟨filtered_readout_ceiling hwhite hS hT hadm hs hσ hμle hμ hσV,
    gaussian_ceiling_does_not_bite hb⟩

open MeasureTheory in
/-- **Detector-chain ceiling (6EC) does NOT bite** at a bolometer noise budget yielding matched
budget `8` — the same permissive point, reached through the phonon ⊕ Johnson sum, and likewise
stated by calling `detector_chain_ceiling` rather than by mirroring its bound. -/
theorem detector_chain_ceiling_does_not_bite (m : Electrothermal.ETFModel) {kB T Tw : ℝ}
    {Vtot : (ℝ → ℝ) → ℝ} {V : Fin 2 → (ℝ → ℝ) → ℝ} {s hf : ℝ → ℝ} {μ₀ μ₁ σ t : ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hG : 0 < m.G)
    (hindep : Detection.IsUncorrelatedAt Finset.univ Vtot V)
    (hphonon : Electrothermal.ETFModel.IsThermalFluctuationLimited (V 0) m kB T Tw)
    (hjohnson : Detection.IsWhiteFilteredVariance (V 1) (m.johnsonNEP kB T ^ 2) Tw)
    (hTw : 0 ≤ Tw) (hadm : Detection.IsAdmissibleFilter Tw s hf)
    (hs : IntervalIntegrable (fun x => s x ^ 2) volume 0 Tw)
    (hσ : 0 < σ) (hμle : μ₀ ≤ μ₁)
    (hμ : μ₁ - μ₀ = ∫ x in (0:ℝ)..Tw, hf x * s x) (hσV : σ = Real.sqrt (Vtot hf))
    (hb : Detection.matchedBudget (m.phononNEP kB T ^ 2 + m.johnsonNEP kB T ^ 2) Tw s = 8) :
    assignmentFidelity (Detection.thrErr0 μ₀ σ t) (Detection.thrErr1 μ₁ σ t)
        ≤ 1 - Detection.gaussianQ
            (Detection.matchedBudget (m.phononNEP kB T ^ 2 + m.johnsonNEP kB T ^ 2) Tw s / 2)
      ∧ (17 : ℝ) / 18 ≤ 1 - Detection.gaussianQ
            (Detection.matchedBudget (m.phononNEP kB T ^ 2 + m.johnsonNEP kB T ^ 2) Tw s / 2) :=
  ⟨detector_chain_ceiling m hkB hT hG hindep hphonon hjohnson hTw hadm hs hσ hμle hμ hσV,
    gaussian_ceiling_does_not_bite hb⟩

end

end SKEFTHawking.Control
