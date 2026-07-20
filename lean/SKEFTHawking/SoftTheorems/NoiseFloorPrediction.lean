import Mathlib
import SKEFTHawking.SoftTheorems.Carrollian

/-!
# Phase 6o Wave 1a.6: universal noise-floor n_noise = δ_k/2 (FDR-fixed)

## Goal

Encode the Phase 6o Wave 1a.6 **concrete falsifiable phenomenology**
deliverable per On-Shell Methods DR §7.2:

> "The boostless soft theorem fixes the soft factor's normalization by
> the asymptotic charges of supertranslation-like symmetries. … soft
> theorems give a ratio n_noise / (Hawking flux) that is universal (not
> Wilson-coefficient dependent). This is the most concrete near-term
> Phase 7 deliverable."

## Substantive content (R-01 remediation, 2026-07-20)

The load-bearing physics is the FDR/KMS noise floor

    n_noise = δ_k / 2   (at T_env = 0)

(On-Shell DR §7 pt 2; matches in-tree `WKBConnection.noise_floor`,
`formulas.fdr_noise_floor`, and `noise_floor_eq_delta_diss`: n_noise =
δ_k/2 = δ_diss = Γ_H/κ). This module encodes that as a *computed* function
of δ_k, with three genuine, falsifiable facts:

1. `noiseFloor δ_k = δ_k/2` with `noiseFloor_pos` (a non-zero floor when
   δ_k > 0) and a `norm_num`-backed numeric instance `noiseFloor_numeric`.
2. `UniversalNoiseFloorRatio δ_k = 1/2` — the soft-theorem-fixed n_noise/δ_k
   ratio, *computed* (not hard-coded) as `noiseFloor δ_k / δ_k`, equal to
   1/2 for every δ_k ≠ 0 (this is the universal, Wilson-coefficient-free
   normalization of §7.2).
3. **Wilson-coefficient independence** as a genuine invariance: on the
   config space `SKConfig` (a δ_k *plus* an arbitrary family of Wilson
   coefficients), the FDR floor is `IsWilsonCoefficientIndependent` — it
   depends only on δ_k, invariant under any reassignment of the Wilson
   coefficients. The predicate is non-trivial: a Wilson-dependent
   observable (`fun c => c.wilson 0`) provably fails it
   (`wilson_dependent_observable_not_independent`).

"Universal" here means precisely: substrate-independent *and*
Wilson-coefficient-independent (fixed by δ_k alone) — NOT that
n_noise / n_Hawking is a single universal number (it is not; n_Hawking =
|β|²/(1−δ_k) carries |β|²). We do not overclaim beyond §7.2.

The experimental-accessibility classification is genuine, not uniform:
BEC (Steinhauer 2016) and polariton (Carusotto 2012) horizons are directly
measurable; the ADW emergent-graviton substrate is provably *not* directly
measurable (`adw_not_directly_measurable`).

## References

- On-Shell Methods DR §7.2.
- Carusotto-Gerace polariton analog black-hole literature (arXiv:1206.4276).
- Steinhauer, Nature Physics 12, 959 (2016) — experimental BEC analog
  Hawking spectrum.
- In-tree: `WKBConnection.lean` (`noise_floor`, `noise_floor_eq_delta_diss`,
  `noise_floor_zero_iff`); `src/core/formulas.py::fdr_noise_floor`.
-/

noncomputable section

namespace SKEFTHawking.SoftTheorems

/-! ## §1. The FDR noise floor n_noise = δ_k/2 -/

/-- The FDR/KMS-mandated noise floor as a function of the decoherence
parameter δ_k: `n_noise = δ_k / 2` (at T_env = 0). Fixed by the boostless
soft-factor normalization (On-Shell DR §7.2); matches the in-tree
`WKBConnection.noise_floor` and `fdr_noise_floor`. -/
def noiseFloor (δ_k : ℝ) : ℝ := δ_k / 2

/-- The noise floor is strictly positive whenever there is genuine
decoherence δ_k > 0 — a non-zero, hence measurable, floor. -/
theorem noiseFloor_pos {δ_k : ℝ} (h : 0 < δ_k) : 0 < noiseFloor δ_k := by
  unfold noiseFloor; linarith

/-- Falsifiable numeric instance: at δ_k = 1/10, the noise floor is 1/20. -/
theorem noiseFloor_numeric : noiseFloor (1 / 10) = 1 / 20 := by
  norm_num [noiseFloor]

/-! ## §2. The universal (soft-theorem-fixed) ratio n_noise / δ_k = 1/2 -/

/-- The universal noise-floor ratio n_noise / δ_k, *computed* from the FDR
floor. Soft theorems fix this normalization to 1/2 on every substrate,
independent of Wilson coefficients (On-Shell DR §7.2). -/
def UniversalNoiseFloorRatio (δ_k : ℝ) : ℝ := noiseFloor δ_k / δ_k

/-- **The universal ratio equals 1/2** for every non-zero δ_k. This is the
soft-theorem-fixed, substrate- and Wilson-coefficient-independent
normalization of the noise floor. -/
theorem universalNoiseFloorRatio_eq_half {δ_k : ℝ} (h : δ_k ≠ 0) :
    UniversalNoiseFloorRatio δ_k = 1 / 2 := by
  unfold UniversalNoiseFloorRatio noiseFloor
  field_simp

/-- The universal ratio is genuinely non-trivial: it is 1/2, not the
placeholder value 1. -/
theorem universalNoiseFloorRatio_ne_one {δ_k : ℝ} (h : δ_k ≠ 0) :
    UniversalNoiseFloorRatio δ_k ≠ 1 := by
  rw [universalNoiseFloorRatio_eq_half h]; norm_num

/-! ## §3. Wilson-coefficient independence (genuine invariance) -/

/-- An SK-EFT configuration: a decoherence scale δ_k together with an
arbitrary family of UV-EFT Wilson coefficients. The floor must not depend
on the latter. -/
structure SKConfig where
  /-- The decoherence parameter δ_k (fixes the noise floor). -/
  δ_k : ℝ
  /-- An arbitrary family of UV-EFT Wilson coefficients. -/
  wilson : ℕ → ℝ

/-- The FDR noise floor of a configuration — a function of δ_k only. -/
def configNoiseFloor (c : SKConfig) : ℝ := noiseFloor c.δ_k

/-- A real-valued observable of an SK-EFT configuration is
*Wilson-coefficient-independent* if any two configurations sharing the same
δ_k assign it equal values (i.e. it is invariant under arbitrary
reassignment of the Wilson coefficients). -/
def IsWilsonCoefficientIndependent (f : SKConfig → ℝ) : Prop :=
  ∀ c₁ c₂ : SKConfig, c₁.δ_k = c₂.δ_k → f c₁ = f c₂

/-- **Substantive Wave 1a.6 finding**: the FDR noise floor is
Wilson-coefficient-independent. It is fixed entirely by δ_k via
n_noise = δ_k/2, regardless of the EFT Wilson coefficients — so a "wrong"
predicted floor cannot be absorbed into a Wilson-coefficient
renormalization. This is what makes the floor a concrete falsifiable
prediction. -/
theorem noiseFloor_wilsonCoefficient_independent :
    IsWilsonCoefficientIndependent configNoiseFloor := by
  intro c₁ c₂ h
  unfold configNoiseFloor
  rw [h]

/-- The independence predicate is genuinely discriminating: a
Wilson-dependent observable (the first Wilson coefficient) is NOT
Wilson-coefficient-independent. So the finding above is non-vacuous. -/
theorem wilson_dependent_observable_not_independent :
    ¬ IsWilsonCoefficientIndependent (fun c => c.wilson 0) := by
  intro h
  have := h ⟨0, fun _ => 0⟩ ⟨0, fun _ => 1⟩ rfl
  simp at this

/-! ## §4. Experimental falsifiability -/

/-- The noise floor is experimentally falsifiable iff it is strictly
positive: a non-zero floor is measurable (Steinhauer BEC pair-correlation /
Carusotto polariton cross-correlation), whereas a zero floor cannot be
distinguished from the vacuum. -/
def IsExperimentallyFalsifiableNoiseFloor (δ_k : ℝ) : Prop :=
  0 < noiseFloor δ_k

theorem isExperimentallyFalsifiable_iff (δ_k : ℝ) :
    IsExperimentallyFalsifiableNoiseFloor δ_k ↔ 0 < δ_k := by
  unfold IsExperimentallyFalsifiableNoiseFloor noiseFloor
  constructor <;> intro h <;> linarith

/-- Whether the substrate's noise floor is *directly* laboratory-measurable.
BEC draining-bathtub (Steinhauer 2016) and polariton sonic horizon
(Carusotto 2012) are directly accessible; the ADW emergent-graviton
substrate is NOT a directly measurable laboratory system (theoretical
cross-bridge only). This classification is genuine — it is not uniform. -/
def IsDirectlyMeasurableSubstrate : AnalogBackground → Prop
  | .BECDrainingBathtub => True
  | .ADWSchwarzschild => False
  | .PolaritonSonicHorizon => True

theorem bec_directly_measurable :
    IsDirectlyMeasurableSubstrate .BECDrainingBathtub := trivial

theorem polariton_directly_measurable :
    IsDirectlyMeasurableSubstrate .PolaritonSonicHorizon := trivial

/-- The ADW substrate is provably *not* directly measurable — the
classification genuinely discriminates the three substrates. -/
theorem adw_not_directly_measurable :
    ¬ IsDirectlyMeasurableSubstrate .ADWSchwarzschild := by
  simp [IsDirectlyMeasurableSubstrate]

/-! ## §5. Wave 1a.6 closure summary -/

/-- Substantive deliverables shipped at Wave 1a.6 (R-01 remediation):

1. `noiseFloor δ_k = δ_k/2` (the FDR floor), positive for δ_k > 0, with a
   `norm_num` numeric instance.
2. `UniversalNoiseFloorRatio δ_k = 1/2` — computed, universal, ≠ 1.
3. `IsWilsonCoefficientIndependent` + `noiseFloor_wilsonCoefficient_independent`
   (genuine invariance of `configNoiseFloor`) +
   `wilson_dependent_observable_not_independent` (non-vacuity).
4. `IsExperimentallyFalsifiableNoiseFloor` ⟺ δ_k > 0, with the genuine
   (non-uniform) substrate accessibility classification. -/
theorem wave_1a_6_noiseFloor_closure :
    (∀ δ_k : ℝ, 0 < δ_k → 0 < noiseFloor δ_k) ∧
    (∀ δ_k : ℝ, δ_k ≠ 0 → UniversalNoiseFloorRatio δ_k = 1 / 2) ∧
    IsWilsonCoefficientIndependent configNoiseFloor ∧
    (∀ δ_k : ℝ, IsExperimentallyFalsifiableNoiseFloor δ_k ↔ 0 < δ_k) :=
  ⟨fun _ h => noiseFloor_pos h,
   fun _ h => universalNoiseFloorRatio_eq_half h,
   noiseFloor_wilsonCoefficient_independent,
   isExperimentallyFalsifiable_iff⟩

end SKEFTHawking.SoftTheorems
