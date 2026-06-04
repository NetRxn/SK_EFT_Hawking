/-
Phase 5q.B: the definite-case input [Θ] — a positive-definite even unimodular form has `8 ∣ rank` (= σ).

This is one of the two remaining classical inputs to van der Blij (`VanDerBlijReduction.eight_dvd_latticeSig
_of_HM_of_Theta`). Contrary to the earlier "no Mathlib substrate / multi-year" framing, the analytic route
is REACHABLE — the substrate exists — and is decomposed here into a concrete lemma-by-lemma plan.

DE-RISKED PATH (theta-modularity), with the exact Mathlib toeholds (verified 2026-06-04):
  [Θ1]  *n-dimensional Poisson summation* for Schwartz `f : (Fin n → ℝ) → ℂ`:
        `∑_{v∈ℤⁿ} f v = ∑_{w∈ℤⁿ} 𝓕 f w`.  Mirror Mathlib's 1-D proof `Real.tsum_eq_tsum_fourier`
        (`Mathlib/Analysis/Fourier/PoissonSummation.lean`) in `n` dimensions, using the multivariate torus
        Fourier series engine `UnitAddTorus.hasSum_mFourier_series_apply_of_summable` + `mFourierCoeff` +
        `measurePreserving_equivPiIoc`/`integral_preimage` (file `Mathlib/Analysis/Fourier/AddCircleMulti.lean`,
        namespace `UnitAddTorus`). The crux lemma is the n-dim analog of `Real.fourierCoeff_tsum_comp_add`: the
        multivariate Fourier coefficient of the periodisation equals `𝓕 f` at the lattice point. The
        origin-collapse step `∑ₙ mFourierCoeff f n = f 0` is already shipped (`MultivarPoisson.lean`).
  [Θ2]  *anisotropic multivariate Gaussian Fourier transform*: `𝓕 (fun v ↦ cexp(-π vᵀ A v)) w =
        (det A)^{-1/2} cexp(-π wᵀ A⁻¹ w)` for `A` real posdef. Build from the isotropic
        `fourier_gaussian_innerProductSpace` (`Mathlib/Analysis/SpecialFunctions/Gaussian/FourierTransform`)
        via the linear change of variables `x ↦ A^{1/2} x` (spectral square root + Jacobian `det A^{1/2}`).
  [Θ3]  the *S-transform* `Θ_A(-1/τ) = (det A)^{-1/2} (τ/i)^{n/2} Θ_{A⁻¹}(τ)` from [Θ1]+[Θ2]; then for even
        unimodular `A`: `det A = 1` (`posDef_unimodular_det_one`) and `A⁻¹ ≅ A` (congruence by the unimodular
        `A⁻¹`), so `Θ_{A⁻¹} = Θ_A` (`LatticeTheta.latticeTheta_congr`), giving `Θ_A(-1/τ) = (τ/i)^{n/2}Θ_A(τ)`.
  [Θ4]  with `Θ_A(τ+1) = Θ_A(τ)` (even; `LatticeTheta.latticeTheta_T_int`) and `Θ_A ≠ 0` (cusp constant `1`;
        `LatticeTheta.latticeTheta_eq_one_add`), `Θ_A` is a nonzero level-1 modular form of weight `n/2`;
        the multiplier/weight constraint (`Mathlib/.../ModularForms/LevelOne.lean`) forces `8 ∣ n`.

`LatticeTheta.lean` already supplies convergence (`summable_gram_gaussian`), `T`-invariance, `T²`-invariance,
congruence-invariance, cusp normalisation, and the diagonal S-transform. This module collects the reachable
algebraic bricks and the plan; [Θ1]/[Θ2] are the substantial analytic builds remaining.

All proofs are kernel-pure (`propext`/`Classical.choice`/`Quot.sound` only); no `native_decide`, no
`maxHeartbeats`, no axiom.
-/

import Mathlib
import SKEFTHawking.AlgebraicRokhlin
import SKEFTHawking.LatticeSignature

namespace SKEFTHawking

open Matrix

/-- A positive-definite even unimodular form has determinant exactly `1` (posdef ⟹ `det > 0`, unimodular ⟹
`det = ±1`). -/
theorem posDef_unimodular_det_one {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hunim : IsUnimodular A)
    (hpd : (A.map (Int.cast : ℤ → ℝ)).PosDef) : A.det = 1 := by
  have hpos : 0 < (A.map (Int.cast : ℤ → ℝ)).det := hpd.det_pos
  rw [← Int.cast_det] at hpos
  rcases hunim with h | h
  · exact h
  · rw [h] at hpos; norm_num at hpos

/-- For a positive-definite even unimodular form, `latticeSig = rank = n` — so the theta-modularity
conclusion `8 ∣ n` is exactly `8 ∣ latticeSig`, the [Θ] input demanded by `eight_dvd_latticeSig_of_HM_of_Theta`
in the definite (`sigNeg = 0`) branch. -/
theorem latticeSig_posDef_eq_rank {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hpd : (A.map (Int.cast : ℤ → ℝ)).PosDef) : latticeSig A = (n : ℤ) :=
  latticeSig_of_posDef A hpd

end SKEFTHawking
