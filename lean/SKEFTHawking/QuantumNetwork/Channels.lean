import Mathlib.Analysis.SpecialFunctions.Pow.Real
import SKEFTHawking.QuantumNetwork.Basic

/-!
# Quantum-Network channel models (Phase 6AA, Wave 1 / 1′)

Fiber-loss attenuation in the **dB-primitive / Np-derived** convention (DR-SIM):
the attenuation coefficient is specified in dB/km (the engineering standard,
matching QuISP / SeQUeNCe / NetSquid and ITU-T G.652 at 0.2 dB/km), and the
neper form is a *derived* quantity. The load-bearing Tier-1 anchor is the
**dB↔Np consistency identity** relating the base-10 engineering transmission
`10^(−α_dB·L/10)` to the natural-exponential form `exp(−α_Np·L)`.

This resolves the literature "0.046" ambiguity: `0.046` is Np/km (= `0.2` dB/km),
NOT `0.046` dB/km (which would be wrong by a factor of `ln 10 / 1 ≈ 4.343`).

Invariants (Phase 6AA): kernel-pure, zero sorry, no project-local axioms,
no `maxHeartbeats` in proof bodies.
-/

namespace SKEFTHawking.QuantumNetwork

open Real

/-- Derived neper-per-km attenuation from the dB/km primitive: `α_Np = α_dB · ln 10 / 10`. -/
noncomputable def attenuationNp (αdB : ℝ) : ℝ := αdB * Real.log 10 / 10

/-- Fiber transmission probability over length `L` (km) at attenuation `αdB` (dB/km),
in the engineering base-10 convention `η = 10^(−α_dB·L/10)`. -/
noncomputable def fiberTransmission (αdB L : ℝ) : ℝ := (10 : ℝ) ^ (-αdB * L / 10)

/-- **Tier-1 anchor — dB↔Np consistency.** The base-10 engineering transmission
`10^(−α_dB·L/10)` equals the natural-exponential form `exp(−α_Np·L)` with the
derived neper coefficient `α_Np = α_dB · ln 10 / 10`. All three reference
simulators (QuISP/SeQUeNCe/NetSquid) use the dB convention; this identity is the
bridge to the `Real.exp`-based bounds of Wave 2. -/
theorem fiberTransmission_eq_exp_neg_attenuationNp (αdB L : ℝ) :
    fiberTransmission αdB L = Real.exp (-(attenuationNp αdB) * L) := by
  unfold fiberTransmission attenuationNp
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 10)]
  congr 1
  ring

/-- Fiber transmission is strictly positive (a probability lower bound the
envelope can rely on unconditionally). -/
theorem fiberTransmission_pos (αdB L : ℝ) : 0 < fiberTransmission αdB L :=
  Real.rpow_pos_of_pos (by norm_num) _

/-- Over physical parameters (`αdB, L ≥ 0`) transmission is at most 1. -/
theorem fiberTransmission_le_one (αdB L : ℝ) (hα : 0 ≤ αdB) (hL : 0 ≤ L) :
    fiberTransmission αdB L ≤ 1 := by
  unfold fiberTransmission
  apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
  nlinarith [mul_nonneg hα hL]

/-- **Monotone loss:** longer fiber transmits no more. Antitone in length for
`αdB ≥ 0` — the load-bearing fact for propagating an end-to-end fidelity-decay
bound through a link. -/
theorem fiberTransmission_antitone_length (αdB : ℝ) (hα : 0 ≤ αdB) {L₁ L₂ : ℝ}
    (h : L₁ ≤ L₂) : fiberTransmission αdB L₂ ≤ fiberTransmission αdB L₁ := by
  unfold fiberTransmission
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  nlinarith [mul_nonneg hα (sub_nonneg.mpr h)]

end SKEFTHawking.QuantumNetwork
