import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import SKEFTHawking.QuantumNetwork.Teleportation

/-!
# The Haar–Pauli quadratic integral, discharged (Phase 6AD / Bucket 3.1)

This module proves the analytic value that Phase 6AC `Teleportation.lean` carried as
the tracked hypothesis `HaarPauliConstant`:

`∫_{S²} (⟨ψ|σ_k|ψ⟩)² dμ = 1/3`,

the single real-analysis step of the Horodecki teleportation-fidelity proof
(PRA 60, 1888 (1999) §III, step 4; exact-formulas DR §4b). With it the Horodecki
theorems become **unconditional** (no hypothesis, no axiom).

We work in the Bloch picture (consistent with the substrate's real-parameter
discipline — no density matrices). For the Bloch-parameterized pure qubit
`|ψ(θ,φ)⟩ = (cos(θ/2), e^{iφ} sin(θ/2))`, the Pauli-`z` expectation is the Bloch
`z`-coordinate `⟨ψ|σ_z|ψ⟩ = cos θ` (`pauliExpZ_blochKet`), so the Haar (uniform
solid-angle) average of its square is the normalized spherical integral
`(1/4π)∫₀^{2π}∫₀^π cos²θ · sin θ \,dθ\,dφ = 1/3` (`haarPauliBlochAverage_eq`).
By the isotropy of the sphere the same value holds for `k = x, y`.

Invariants: kernel-pure, zero sorry, zero project-local axioms, no `maxHeartbeats`.
-/

namespace SKEFTHawking.QuantumNetwork

open Real intervalIntegral

/-- `∫₀^π cos²θ · sin θ dθ = 2/3` (antiderivative `−cos³θ/3`, FTC). -/
theorem cosSq_mul_sin_integral :
    ∫ θ in (0:ℝ)..π, (Real.cos θ) ^ 2 * Real.sin θ = 2 / 3 := by
  have hderiv : ∀ θ ∈ Set.uIcc (0:ℝ) π,
      HasDerivAt (fun θ => -(Real.cos θ ^ 3) / 3) ((Real.cos θ) ^ 2 * Real.sin θ) θ := by
    intro θ _
    have h1 : HasDerivAt (fun θ => Real.cos θ ^ 3)
        (3 * Real.cos θ ^ 2 * (-Real.sin θ)) θ := by
      simpa using (Real.hasDerivAt_cos θ).pow 3
    have h2 := (h1.neg).div_const 3
    convert h2 using 1
    ring
  have hint : IntervalIntegrable (fun θ => (Real.cos θ) ^ 2 * Real.sin θ)
      MeasureTheory.volume 0 π :=
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  norm_num [Real.cos_pi, Real.cos_zero]

/-- Bloch-parameterized pure qubit `|ψ(θ,φ)⟩ = (cos(θ/2), e^{iφ} sin(θ/2))`. -/
noncomputable def blochKet (θ φ : ℝ) : Fin 2 → ℂ :=
  ![(Real.cos (θ / 2) : ℂ), Complex.exp (φ * Complex.I) * (Real.sin (θ / 2) : ℂ)]

/-- The Pauli-`z` matrix `diag(1, -1)`. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- Pauli-`z` expectation value `⟨ψ|σ_z|ψ⟩`. -/
noncomputable def pauliExpZ (ψ : Fin 2 → ℂ) : ℂ :=
  ∑ i, ∑ j, (starRingEnd ℂ) (ψ i) * pauliZ i j * ψ j

/-- **`⟨ψ|σ_z|ψ⟩ = cos θ`** for the Bloch-parameterized pure qubit: the Pauli-`z`
expectation is exactly the Bloch `z`-coordinate. (Steps 1–3/5 of the Horodecki proof —
the elementary, non-analytic part.) -/
theorem pauliExpZ_blochKet (θ φ : ℝ) : pauliExpZ (blochKet θ φ) = (Real.cos θ : ℂ) := by
  have hexp : (starRingEnd ℂ) (Complex.exp (φ * Complex.I)) * Complex.exp (φ * Complex.I) = 1 := by
    rw [← Complex.exp_conj, ← Complex.exp_add,
      show (starRingEnd ℂ) (↑φ * Complex.I) + ↑φ * Complex.I = 0 by
        simp [map_mul, Complex.conj_ofReal, Complex.conj_I]]
    exact Complex.exp_zero
  simp only [pauliExpZ, blochKet, pauliZ, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val', Matrix.cons_val_fin_one,
    Matrix.of_apply, Matrix.empty_val', Complex.conj_ofReal]
  ring_nf
  rw [map_mul, Complex.conj_ofReal,
    show Complex.exp (↑φ * Complex.I) * ↑(Real.sin (θ * (1 / 2))) *
        ((starRingEnd ℂ) (Complex.exp (↑φ * Complex.I)) * ↑(Real.sin (θ * (1 / 2))))
      = ((starRingEnd ℂ) (Complex.exp (↑φ * Complex.I)) * Complex.exp (↑φ * Complex.I))
        * (↑(Real.sin (θ * (1 / 2))) ^ 2) by ring,
    hexp, one_mul]
  norm_cast
  rw [← Real.cos_two_mul']
  congr 1
  ring

/-- The Haar (uniform solid-angle) average over the Bloch sphere of the squared
Pauli-`z` expectation: `(1/4π)∫₀^{2π}∫₀^π cos²θ · sin θ dθ dφ`. -/
noncomputable def haarPauliBlochAverage : ℝ :=
  (1 / (4 * Real.pi)) * ∫ _φ in (0:ℝ)..(2 * Real.pi),
    ∫ θ in (0:ℝ)..π, (Real.cos θ) ^ 2 * Real.sin θ

/-- **The Haar–Pauli quadratic integral equals `1/3`.** Discharges the Phase-6AC
tracked hypothesis: the `1/3` in Horodecki's `(2F+1)/3` is now a proven value. -/
theorem haarPauliBlochAverage_eq : haarPauliBlochAverage = 1 / 3 := by
  unfold haarPauliBlochAverage
  rw [cosSq_mul_sin_integral, intervalIntegral.integral_const, smul_eq_mul]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- The genuine Haar–Pauli quadratic integral `∫_{S²}(⟨ψ|σ_z|ψ⟩)² dμ`, with
`⟨ψ|σ_z|ψ⟩` the spinor expectation, in Bloch `(θ,φ)` coordinates with solid-angle
weight `sin θ`. -/
noncomputable def haarPauliZSqAverage : ℝ :=
  (1 / (4 * Real.pi)) * ∫ φ in (0:ℝ)..(2 * Real.pi),
    ∫ θ in (0:ℝ)..π, ((pauliExpZ (blochKet θ φ)).re) ^ 2 * Real.sin θ

/-- **The Haar–Pauli quadratic integral `∫_{S²}(⟨ψ|σ_z|ψ⟩)² dμ = 1/3`** — fully
discharged: the spinor expectation reduces to the Bloch `z`-coordinate
(`pauliExpZ_blochKet`) and the resulting spherical integral is `1/3`
(`haarPauliBlochAverage_eq`). This is the analytic step the Phase-6AC teleportation
module carried as the tracked hypothesis `HaarPauliConstant`. -/
theorem haarPauliZSqAverage_eq : haarPauliZSqAverage = 1 / 3 := by
  have h : haarPauliZSqAverage = haarPauliBlochAverage := by
    unfold haarPauliZSqAverage haarPauliBlochAverage
    simp_rw [pauliExpZ_blochKet, Complex.ofReal_re]
  rw [h, haarPauliBlochAverage_eq]

/-- **The Phase-6AC Haar tracked hypothesis, discharged:** the constant equals the
proven Haar–Pauli integral value. -/
theorem haarPauliConstant_haarPauliZSqAverage : HaarPauliConstant haarPauliZSqAverage :=
  haarPauliZSqAverage_eq

/-- **Unconditional Horodecki teleportation fidelity** `f_avg = (2F+1)/3` — the Haar
value is now a proven theorem, not a hypothesis and not an axiom. -/
theorem teleportAvgFidelity_horodecki_unconditional (F : ℝ) :
    teleportAvgFidelity F haarPauliZSqAverage = (2 * F + 1) / 3 :=
  teleportAvgFidelity_horodecki F haarPauliConstant_haarPauliZSqAverage

/-- **Unconditional entanglement-utility threshold** `f_avg > 2/3 ↔ F > 1/2`
(Horodecki / Massar–Popescu). -/
theorem teleport_beats_classical_iff_unconditional (F : ℝ) :
    2 / 3 < teleportAvgFidelity F haarPauliZSqAverage ↔ 1 / 2 < F :=
  teleport_beats_classical_iff F haarPauliConstant_haarPauliZSqAverage

/-- **Unconditional chain teleportation usefulness:** the `k`-swap Werner end-to-end
state teleports above the classical bound iff the `k`-fold Werner parameter exceeds `1/3`. -/
theorem teleport_useful_over_chain_unconditional (F : ℝ) (k : ℕ) :
    2 / 3 < teleportAvgFidelity (endToEndFidelity F k) haarPauliZSqAverage
      ↔ 1 / 3 < (wernerParam F) ^ k :=
  teleport_useful_over_chain F k haarPauliConstant_haarPauliZSqAverage

end SKEFTHawking.QuantumNetwork
