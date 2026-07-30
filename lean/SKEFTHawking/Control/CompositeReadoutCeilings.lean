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

/-- **Additive combined floor, under an explicit disjointness hypothesis.**

`hdisj` says the two mechanisms contribute *separately* to the excited-branch misassignment — their
error events do not overlap, so the contributions add rather than merely each being present. That
hypothesis is exactly what a fail-open composite would omit, so it is a binder here. -/
theorem combined_floor_add {ε₁ ε₂ e0 e1 : ℝ} (he0 : 0 ≤ e0) (hdisj : ε₁ + ε₂ ≤ e1) :
    (ε₁ + ε₂) / 2 ≤ avgAssignmentError e0 e1 := by
  unfold avgAssignmentError
  linarith

/-- **Additive ceiling** — fidelity form. -/
theorem combined_ceiling_add {ε₁ ε₂ e0 e1 : ℝ} (he0 : 0 ≤ e0) (hdisj : ε₁ + ε₂ ≤ e1) :
    assignmentFidelity e0 e1 ≤ 1 - (ε₁ + ε₂) / 2 :=
  assignmentFidelity_le_of_floor (combined_floor_add he0 hdisj)

/-- **The additive form is STRICTLY sharper — the difference is proved, not asserted.**

Whenever both mechanisms genuinely contribute, the additive floor exceeds the worst-mechanism
floor. This is what makes the independence hypothesis worth carrying: without a strict gap the
sharper form would be a restated hypothesis rather than a stronger theorem. -/
theorem combined_floor_add_strictly_sharper {ε₁ ε₂ : ℝ} (h₁ : 0 < ε₁) (h₂ : 0 < ε₂) :
    max (ε₁ / 2) (ε₂ / 2) < (ε₁ + ε₂) / 2 := by
  rcases max_cases (ε₁ / 2) (ε₂ / 2) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> linarith

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

/-- **Filtered-readout ceiling (6EB).** Specialised to the 6EB threshold objects: the error pair is
`(thrErr0, thrErr1)` and the floor is `gaussianQ` at half the matched-filter budget. -/
theorem filtered_readout_ceiling {S₀ T : ℝ} {s : ℝ → ℝ} {μ₀ μ₁ σ t : ℝ}
    (hfloor : Detection.gaussianQ (Detection.matchedBudget S₀ T s / 2)
      ≤ avgAssignmentError (Detection.thrErr0 μ₀ σ t) (Detection.thrErr1 μ₁ σ t)) :
    assignmentFidelity (Detection.thrErr0 μ₀ σ t) (Detection.thrErr1 μ₁ σ t)
      ≤ 1 - Detection.gaussianQ (Detection.matchedBudget S₀ T s / 2) :=
  assignmentFidelity_le_of_floor hfloor

/-- **Detector-chain ceiling (6EC).** The deepest chain: detector NEP → filter → Gaussian error →
fidelity. What distinguishes it from the 6EB ceiling is the noise budget — here the PSD is the
bolometer's own phonon ⊕ Johnson quadrature sum, not a free parameter. -/
theorem detector_chain_ceiling (m : Electrothermal.ETFModel) {kB T Tw : ℝ} {s : ℝ → ℝ}
    {μ₀ μ₁ σ t : ℝ}
    (hfloor : Detection.gaussianQ
        (Detection.matchedBudget (m.phononNEP kB T ^ 2 + m.johnsonNEP kB T ^ 2) Tw s / 2)
      ≤ avgAssignmentError (Detection.thrErr0 μ₀ σ t) (Detection.thrErr1 μ₁ σ t)) :
    assignmentFidelity (Detection.thrErr0 μ₀ σ t) (Detection.thrErr1 μ₁ σ t)
      ≤ 1 - Detection.gaussianQ
        (Detection.matchedBudget (m.phononNEP kB T ^ 2 + m.johnsonNEP kB T ^ 2) Tw s / 2) :=
  assignmentFidelity_le_of_floor hfloor

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
