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

open Matrix Complex MeasureTheory
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

/-- **Integrability of the character × Gaussian** (the `hFint` hypothesis of `multivar_poisson` for the
Gaussian `F(x) = exp(iπσ·xᵀGx)`). For positive-definite `G` and `Im σ > 0`, `x ↦ exp(2πi·∑cᵢxᵢ)·exp(iπσ·xᵀGx)`
is integrable: its norm is `exp(-π·Im σ·xᵀGx) ≤ exp(-π·Im σ·λ·∑xᵢ²)` by coercivity (`posDef_coercive`), and the
diagonal Gaussian dominator is integrable (`GaussianFourier.integrable_cexp_neg_mul_sum_add`). -/
theorem integrable_gaussianChar {d : ℕ} {G : Matrix (Fin d) (Fin d) ℝ} (hG : G.PosDef) {σ : ℂ}
    (hσ : 0 < σ.im) (c : Fin d → ℝ) :
    Integrable (fun x : Fin d → ℝ =>
      Complex.exp (2 * (π : ℂ) * I * ((∑ i, c i * x i : ℝ) : ℂ)) *
        Complex.exp ((π : ℂ) * I * σ * ((x ⬝ᵥ G *ᵥ x : ℝ) : ℂ))) := by
  obtain ⟨lam, hlam, hcoe⟩ := posDef_coercive G hG
  have hb : (0 : ℝ) < π * σ.im * lam := by positivity
  have hdom : Integrable (fun x : Fin d → ℝ =>
      Complex.exp (-((π * σ.im * lam : ℝ) : ℂ) * ∑ i, ((x i : ℂ)) ^ 2)) := by
    have h := GaussianFourier.integrable_cexp_neg_mul_sum_add (b := ((π * σ.im * lam : ℝ) : ℂ))
      (by simpa using hb) (fun _ : Fin d => (0 : ℂ))
    simpa using h
  refine Integrable.mono' hdom.norm (by fun_prop) ?_
  filter_upwards with x
  rw [norm_mul, Complex.norm_exp, Complex.norm_exp, Complex.norm_exp]
  have him : (2 * (π : ℂ) * I * ((∑ i, c i * x i : ℝ) : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  have hre : ((π : ℂ) * I * σ * ((x ⬝ᵥ G *ᵥ x : ℝ) : ℂ)).re = -(π * σ.im * (x ⬝ᵥ G *ᵥ x)) := by
    simp [Complex.mul_re, Complex.mul_im]
  have hScast : ∑ i, ((x i : ℂ)) ^ 2 = ((∑ i, (x i) ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have hdomre : (-((π * σ.im * lam : ℝ) : ℂ) * ∑ i, ((x i : ℂ)) ^ 2).re
      = -(π * σ.im * lam * ∑ i, (x i) ^ 2) := by
    rw [hScast, ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_re]; ring
  rw [him, hre, hdomre, Real.exp_zero, one_mul]
  apply Real.exp_le_exp.mpr
  nlinarith [Real.pi_pos, hσ, hlam, hcoe x]

/-- The **Gaussian** `x ↦ exp(iπσ·xᵀGx)` bundled as a `ContinuousMap` — the `F : C(Fin d → ℝ, ℂ)` that
`multivar_poisson` is applied to in the theta S-transformation. -/
noncomputable def gaussianCM {d : ℕ} (σ : ℂ) (G : Matrix (Fin d) (Fin d) ℝ) : C(Fin d → ℝ, ℂ) :=
  ⟨fun x => Complex.exp ((π : ℂ) * I * σ * ((x ⬝ᵥ G *ᵥ x : ℝ) : ℂ)), by fun_prop⟩

@[simp] theorem gaussianCM_apply {d : ℕ} (σ : ℂ) (G : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    gaussianCM σ G x = Complex.exp ((π : ℂ) * I * σ * ((x ⬝ᵥ G *ᵥ x : ℝ) : ℂ)) := rfl

/-- Measurability of the character × translated Gaussian (the `hmeas` hypothesis of `multivar_poisson` for
`F = gaussianCM σ G`): the integrand is continuous in `x`, hence a.e.-strongly-measurable on the fundamental
domain. -/
theorem gaussian_translate_aesm {d : ℕ} (σ : ℂ) (G : Matrix (Fin d) (Fin d) ℝ) (n : Fin d → ℤ)
    (γ : ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin d))))) :
    AEStronglyMeasurable
      (fun x => Complex.exp (2 * (π : ℂ) * I * ((∑ i, (-(n i) : ℝ) * x i : ℝ) : ℂ))
        * gaussianCM σ G (x + (γ : Fin d → ℝ)))
      (volume.restrict (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin d)))) := by
  apply Continuous.aestronglyMeasurable
  simp only [gaussianCM, ContinuousMap.coe_mk]
  fun_prop

/-- **Norm of the Gaussian**: `‖exp(iπσ·yᵀGy)‖ = exp(-π·Im σ·yᵀGy)`. The decay rate underpinning the
summability of the Gaussian's lattice translates (hF/hsum). -/
theorem norm_gaussianCM {d : ℕ} (σ : ℂ) (G : Matrix (Fin d) (Fin d) ℝ) (y : Fin d → ℝ) :
    ‖gaussianCM σ G y‖ = Real.exp (-(π * σ.im * (y ⬝ᵥ G *ᵥ y))) := by
  rw [gaussianCM_apply, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-- **Real multivariate Gaussian summability over `ℤᵈ`**: `∑_{v∈ℤᵈ} exp(-c·∑ᵢvᵢ²)` is summable for `c > 0`.
(Take `τ = (c/π)·I`: each `‖exp(iπτ·n²)‖ = exp(-c·n²)`, and `summable_normprod_pi` lifts the 1-D Jacobi-theta
summability `summable_gaussian_coord` to the `d`-fold product.) The dominating series for the lattice-translate
summability hF. -/
theorem summable_real_diagonal_gaussian {d : ℕ} {c : ℝ} (hc : 0 < c) :
    Summable (fun v : Fin d → ℤ => Real.exp (-(c * ∑ i, (v i : ℝ) ^ 2))) := by
  have hτ : 0 < (((c / π : ℝ) : ℂ) * I).im := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
      Complex.I_re, mul_zero, add_zero]
    positivity
  have hsum := summable_normprod_pi
    (fun _ : Fin d => fun n : ℤ => Complex.exp (π * I * (n : ℂ) ^ 2 * (((c / π : ℝ) : ℂ) * I)))
    (fun _ => summable_gaussian_coord (((c / π : ℝ) : ℂ) * I) hτ)
  refine hsum.congr (fun v => ?_)
  simp only [Complex.norm_exp]
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hre : ((v i : ℂ) ^ 2).re = (v i : ℝ) ^ 2 := by
    rw [← Complex.ofReal_intCast, ← Complex.ofReal_pow, Complex.ofReal_re]
  have him : ((v i : ℂ) ^ 2).im = 0 := by
    rw [← Complex.ofReal_intCast, ← Complex.ofReal_pow, Complex.ofReal_im]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, hre, him]
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- The real Gaussian summability transported to the **standard integer lattice** (submodule-indexed):
`∑_{γ∈Λ} exp(-c·∑ᵢ(↑γ)ᵢ²)` is summable for `c > 0`. Reindex `Λ ≃ ℤᵈ` (`coe_zlatticeBasis_equivFun_symm`)
and apply `summable_real_diagonal_gaussian`. This is the dominating series for hF. -/
theorem summable_lattice_gaussian {d : ℕ} {c : ℝ} (hc : 0 < c) :
    Summable (fun γ : ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin d)))) =>
      Real.exp (-(c * ∑ i, ((γ : Fin d → ℝ) i) ^ 2))) := by
  apply (Equiv.summable_iff
    ((Pi.basisFun ℝ (Fin d)).restrictScalars ℤ).equivFun.symm.toEquiv).mp
  refine (summable_real_diagonal_gaussian hc).congr (fun v => ?_)
  simp only [Function.comp_apply, LinearEquiv.coe_toEquiv, coe_zlatticeBasis_equivFun_symm]

/-- **Quadratic-form lower bound for a translate**: for `x` in a ball `∑xᵢ² ≤ R²` and any lattice
vector `γ`, `(x+γ)ᵀG(x+γ) ≥ (λ/2)·∑γᵢ² − 2λR²` (`λ` from coercivity). Via coercivity, Cauchy–Schwarz
`(∑xᵢγᵢ)² ≤ (∑xᵢ²)(∑γᵢ²)`, and `(√Sγ − 2R)² ≥ 0`. The uniform-in-`x` Gaussian decay that makes the
lattice translates summable (hF). -/
theorem quadform_translate_lower {d : ℕ} {G : Matrix (Fin d) (Fin d) ℝ} {lam R : ℝ} (hlam : 0 ≤ lam)
    (hR : 0 ≤ R) (hcoe : ∀ y : Fin d → ℝ, lam * ∑ i, (y i) ^ 2 ≤ y ⬝ᵥ G *ᵥ y)
    {x : Fin d → ℝ} (hx : ∑ i, (x i) ^ 2 ≤ R ^ 2) (γ : Fin d → ℝ) :
    lam / 2 * (∑ i, (γ i) ^ 2) - 2 * lam * R ^ 2 ≤ (x + γ) ⬝ᵥ G *ᵥ (x + γ) := by
  have hexp : ∑ i, (x + γ) i ^ 2
      = (∑ i, (x i) ^ 2) + 2 * (∑ i, x i * γ i) + ∑ i, (γ i) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply]; ring
  have hSxnn : 0 ≤ ∑ i, (x i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hSγnn : 0 ≤ ∑ i, (γ i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  set s := Real.sqrt (∑ i, (γ i) ^ 2) with hs
  have hs2 : s ^ 2 = ∑ i, (γ i) ^ 2 := Real.sq_sqrt hSγnn
  have hsnn : 0 ≤ s := Real.sqrt_nonneg _
  have hsqrtSx : Real.sqrt (∑ i, (x i) ^ 2) ≤ R := by
    rw [← Real.sqrt_sq hR]; exact Real.sqrt_le_sqrt hx
  -- `∑ xᵢγᵢ ≥ -R·√Sγ` (Cauchy–Schwarz applied to `-x`)
  have hPge : -(R * s) ≤ ∑ i, x i * γ i := by
    have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => -(x i)) γ
    simp only [neg_mul, neg_sq, Finset.sum_neg_distrib] at h
    have h2 : Real.sqrt (∑ i, (x i) ^ 2) * s ≤ R * s :=
      mul_le_mul_of_nonneg_right hsqrtSx hsnn
    rw [hs]; linarith
  have hPRs : 0 ≤ (∑ i, x i * γ i) + R * s := by linarith
  have hcoeγ := hcoe (x + γ)
  have hlow : lam / 2 * (∑ i, (γ i) ^ 2) - 2 * lam * R ^ 2 ≤ lam * (∑ i, (x + γ) i ^ 2) := by
    rw [hexp, ← hs2]
    nlinarith [mul_nonneg hlam hSxnn, mul_nonneg hlam hPRs,
      mul_nonneg hlam (sq_nonneg (s - 2 * R)), hlam]
  exact hlow.trans hcoeγ

/-- **hF: locally-uniform summability of the Gaussian's lattice translates.** For each compact `K`, the
sup-norms `‖(gaussianCM σ G)(·+↑γ)|_K‖` are summable over the lattice `Λ`. On `K` (bounded, `∑xᵢ²≤R²`) the
translate decays as `exp(-π Im σ·(x+↑γ)ᵀG(x+↑γ)) ≤ C·exp(-c·∑(↑γ)ᵢ²)` (quadform_translate_lower + norm_gaussianCM),
dominated by `summable_lattice_gaussian`. This is the `hF` hypothesis of `multivar_poisson` for the Gaussian. -/
theorem gaussian_hF {d : ℕ} {σ : ℂ} {G : Matrix (Fin d) (Fin d) ℝ} (hG : G.PosDef) (hσ : 0 < σ.im) :
    ∀ K : TopologicalSpace.Compacts (Fin d → ℝ),
      Summable (fun γ : ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin d)))) =>
        ‖((gaussianCM σ G).comp (ContinuousMap.addRight (γ : Fin d → ℝ))).restrict K‖) := by
  intro K
  obtain ⟨lam, hlam, hcoe⟩ := posDef_coercive G hG
  obtain ⟨M, hM⟩ : ∃ M, ∀ x ∈ K, ∑ i, (x i) ^ 2 ≤ M := by
    obtain ⟨M, hMub⟩ := K.isCompact.bddAbove_image
      (f := fun x : Fin d → ℝ => ∑ i, (x i) ^ 2) (by fun_prop)
    exact ⟨M, fun x hx => hMub (Set.mem_image_of_mem _ hx)⟩
  have hR : (0 : ℝ) ≤ Real.sqrt (max M 0) := Real.sqrt_nonneg _
  have hR2 : ∀ x ∈ K, ∑ i, (x i) ^ 2 ≤ (Real.sqrt (max M 0)) ^ 2 := by
    intro x hx
    rw [Real.sq_sqrt (le_max_right M 0)]
    exact (hM x hx).trans (le_max_left M 0)
  have hcpos : 0 < π * σ.im * lam / 2 := by positivity
  refine Summable.of_nonneg_of_le (fun γ => norm_nonneg _) (fun γ => ?_)
    ((summable_lattice_gaussian hcpos).mul_left (Real.exp (2 * π * σ.im * lam * (Real.sqrt (max M 0)) ^ 2)))
  refine (ContinuousMap.norm_le _ (by positivity)).mpr (fun p => ?_)
  rw [ContinuousMap.restrict_apply, ContinuousMap.comp_apply]
  show ‖gaussianCM σ G ((p : Fin d → ℝ) + (γ : Fin d → ℝ))‖ ≤ _
  rw [norm_gaussianCM, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hq := quadform_translate_lower hlam.le hR hcoe (hR2 (p : Fin d → ℝ) p.2) (γ : Fin d → ℝ)
  have hscale := mul_le_mul_of_nonneg_left hq (by positivity : (0 : ℝ) ≤ π * σ.im)
  nlinarith [hscale]

/-- **hLsum: `L¹`-summability over the lattice of the fundamental-domain integrals** (the `hLsum` hypothesis
of `multivar_poisson` for the Gaussian). On `[0,1)ᵈ` (`∑xᵢ²≤d`, volume 1) the integrand is bounded by
`C·exp(-c·∑(↑γ)ᵢ²)`, so each `∫⁻ ≤ ofReal(C·exp(-c·∑(↑γ)ᵢ²))`, and the lattice sum is `ofReal` of a
convergent series (`summable_lattice_gaussian`), hence `≠ ⊤`. -/
theorem gaussian_hLsum {d : ℕ} {σ : ℂ} {G : Matrix (Fin d) (Fin d) ℝ} (hG : G.PosDef) (hσ : 0 < σ.im)
    (n : Fin d → ℤ) :
    ∑' γ : ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin d)))),
      ∫⁻ x in ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin d)),
        ‖Complex.exp (2 * (π : ℂ) * I * ((∑ i, (-(n i) : ℝ) * x i : ℝ) : ℂ))
          * gaussianCM σ G (x + (γ : Fin d → ℝ))‖ₑ ≠ ⊤ := by
  obtain ⟨lam, hlam, hcoe⟩ := posDef_coercive G hG
  have hcpos : 0 < π * σ.im * lam / 2 := by positivity
  have hRdnn : (0 : ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hvol : volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin d))) = 1 := by
    rw [ZSpan.volume_fundamentalDomain]
    have hid : (Matrix.of ⇑(Pi.basisFun ℝ (Fin d))) = (1 : Matrix (Fin d) (Fin d) ℝ) := by
      ext i j
      simp [Matrix.one_apply, Pi.basisFun_apply, Pi.single_apply, eq_comm]
    rw [hid, Matrix.det_one, abs_one, ENNReal.ofReal_one]
  have hRd : ∀ x ∈ ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin d)),
      ∑ i, (x i) ^ 2 ≤ (Real.sqrt d) ^ 2 := by
    intro x hx
    rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (d : ℝ))]
    rw [ZSpan.fundamentalDomain_pi_basisFun, Set.mem_pi] at hx
    calc ∑ i, (x i) ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := hx i (Set.mem_univ i)
          rw [Set.mem_Ico] at this
          nlinarith [this.1, this.2]
      _ = (d : ℝ) := by simp
  have hbound : ∀ γ : ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin d)))),
      (∫⁻ x in ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin d)),
        ‖Complex.exp (2 * (π : ℂ) * I * ((∑ i, (-(n i) : ℝ) * x i : ℝ) : ℂ))
          * gaussianCM σ G (x + (γ : Fin d → ℝ))‖ₑ)
      ≤ ENNReal.ofReal (Real.exp (2 * π * σ.im * lam * (Real.sqrt d) ^ 2)
          * Real.exp (-(π * σ.im * lam / 2 * ∑ i, ((γ : Fin d → ℝ) i) ^ 2))) := by
    intro γ
    calc (∫⁻ x in ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin d)),
            ‖Complex.exp (2 * (π : ℂ) * I * ((∑ i, (-(n i) : ℝ) * x i : ℝ) : ℂ))
              * gaussianCM σ G (x + (γ : Fin d → ℝ))‖ₑ)
        ≤ ∫⁻ _ in ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin d)),
            ENNReal.ofReal (Real.exp (2 * π * σ.im * lam * (Real.sqrt d) ^ 2)
              * Real.exp (-(π * σ.im * lam / 2 * ∑ i, ((γ : Fin d → ℝ) i) ^ 2))) := by
          refine lintegral_mono_ae ?_
          refine (ae_restrict_iff' (ZSpan.fundamentalDomain_measurableSet _)).mpr ?_
          filter_upwards with x hx
          rw [← ofReal_norm_eq_enorm]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [norm_mul]
          have hchar : ‖Complex.exp (2 * (π : ℂ) * I * ((∑ i, (-(n i) : ℝ) * x i : ℝ) : ℂ))‖ = 1 := by
            rw [Complex.norm_exp]; simp [Complex.mul_re, Complex.mul_im]
          rw [hchar, one_mul]
          show ‖gaussianCM σ G (x + (γ : Fin d → ℝ))‖ ≤ _
          rw [norm_gaussianCM, ← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have hq := quadform_translate_lower hlam.le hRdnn hcoe (hRd x hx) (γ : Fin d → ℝ)
          have hscale := mul_le_mul_of_nonneg_left hq (by positivity : (0 : ℝ) ≤ π * σ.im)
          nlinarith [hscale]
      _ = ENNReal.ofReal _ * volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin d))) :=
          setLIntegral_const _ _
      _ = ENNReal.ofReal _ := by rw [hvol, mul_one]
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun γ => by positivity)
    ((summable_lattice_gaussian hcpos).mul_left _)]
  exact ENNReal.ofReal_ne_top

end SKEFTHawking
