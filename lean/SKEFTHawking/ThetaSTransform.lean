/-
Phase 5q.B, [Θ3]: the theta S-transformation `Θ_G(-1/τ) = (det G)^{-1/2}(τ/i)^{d/2} Θ_{G⁻¹}(τ)`.

Assembled from multivariate Poisson summation (`MultivarPoissonDescent.multivar_poisson`) applied to the
Gaussian `F(x) = exp(iπσ·xᵀGx)` (σ = -1/τ), the anisotropic Gaussian integral
(`AnisotropicGaussianFT.integral_cexp_neg_quadratic_form` + `sum_sq_vecMul_sqrtInv_eq`), and the lattice theta
`LatticeTheta.latticeTheta`. The derivation's exact constants: with `b = -iπσ = iπ/τ` (so `b.re = π·Im σ > 0`
and `π/b = τ/i`) and character coefficient `cᵢ = -2πI·nᵢ`, the Gaussian-integral exponent
`(cᵀG⁻¹c)/(4b) = iπτ·nᵀG⁻¹n`, so `∑ₙ latFourier = (det G)^{-1/2}(τ/i)^{d/2} Θ_{G⁻¹}(τ)`.

This module's first brick is the reindexing `∑'_{γ∈Λ} F(↑γ) = Θ_G(σ)` connecting the submodule-indexed Poisson
sum to the `ℤᵈ`-indexed `latticeTheta`, via the ℤ-basis `(Pi.basisFun ℝ (Fin d)).restrictScalars ℤ` of the
standard lattice.

All proofs are kernel-pure (`propext`/`Classical.choice`/`Quot.sound` only); no `native_decide`, no
`maxHeartbeats`, no axiom.
-/

import Mathlib
import SKEFTHawking.LatticeTheta
import SKEFTHawking.AnisotropicGaussianFT
import SKEFTHawking.MultivarPoissonDescent

namespace SKEFTHawking

open Matrix Complex
open scoped Real

/-- Coordinates of the standard integer lattice: the underlying vector of `(basisFun.restrictScalars ℤ).equivFun.symm v`
is `fun i => (v i : ℝ)`. (Each `v ↦ ∑ᵢ vᵢ • basisFun i = fun j => (v j : ℝ)`.) -/
theorem coe_zlatticeBasis_equivFun_symm {d : ℕ} (v : Fin d → ℤ) :
    (((Pi.basisFun ℝ (Fin d)).restrictScalars ℤ).equivFun.symm v : Fin d → ℝ)
      = fun i => (v i : ℝ) := by
  rw [Module.Basis.equivFun_symm_apply]
  funext j
  rw [Submodule.coe_sum]
  simp [Module.Basis.restrictScalars_apply, Pi.basisFun_apply, Pi.single_apply, zsmul_eq_mul,
    Finset.sum_ite_eq]

/-- **Reindexing the Poisson lattice sum as the lattice theta.** The sum over the standard integer lattice
`Λ = span ℤ (range basisFun)` of the Gaussian `exp(iπσ·xᵀGx)` equals `Θ_G(σ)`. (Reindex `Λ ≃ ℤᵈ` by the
ℤ-basis `basisFun.restrictScalars ℤ`; each lattice point `↑γ` is the integer vector of its coordinates.) -/
theorem latticeTheta_eq_lattice_sum {d : ℕ} (G : Matrix (Fin d) (Fin d) ℝ) (σ : ℂ) :
    ∑' γ : ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin d)))),
        Complex.exp (π * I * σ * (((γ : Fin d → ℝ) ⬝ᵥ G *ᵥ (γ : Fin d → ℝ) : ℝ) : ℂ))
      = latticeTheta G σ := by
  rw [latticeTheta, ← Equiv.tsum_eq
    ((Pi.basisFun ℝ (Fin d)).restrictScalars ℤ).equivFun.symm.toEquiv]
  refine tsum_congr fun v => ?_
  rw [LinearEquiv.coe_toEquiv, coe_zlatticeBasis_equivFun_symm]

end SKEFTHawking
