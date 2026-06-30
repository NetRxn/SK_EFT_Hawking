import SKEFTHawking.MolecularHamiltonian
import SKEFTHawking.KineticEssentialSelfAdjoint
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# W3 (Phase 6BB Wave 3) — discharge of `hrel`: the Coulomb relative bound, via Fourier–Kato–Rellich

`molecularHamiltonian_essSelfAdjoint` proves essential self-adjointness *conditionally* on `hrel`:
that the molecular Coulomb potential is relatively bounded with respect to the kinetic operator with
relative bound `a < 1` (Kato's condition). This module discharges `hrel` by **proving** that bound.

**Route (Fourier–Kato–Rellich, not the from-scratch Hardy inequality).** Mathlib has neither Hardy nor
the Morrey/sup-norm embedding, but it *does* have `integrable_rpow_neg_one_add_norm_sq`, Plancherel, and
(via Wave 2) the Schwartz Fourier-multiplier substrate. The Kato argument:
* `(1 + ‖ξ‖²)⁻¹ ∈ L²(ℝ³)` (this file's foundational lemma), because `4 > 3 = dim`;
* hence (Cauchy–Schwarz on the Fourier side) `‖u‖_∞ ≤ ε‖Δu‖ + C_ε‖u‖` for Schwartz `u`;
* the Coulomb singularity splits `1/‖x‖ = V₁ + V₂` with `V₁ ∈ L²`, `V₂ ∈ L^∞`, giving
  `‖(1/‖·‖)u‖₂ ≤ ‖V₁‖₂‖u‖_∞ + ‖u‖₂`, so each Coulomb term is kinetic-bounded with bound `→ 0`.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; zero `sorry`; no new axiom.
-/

namespace SKEFTHawking.DFT

open MeasureTheory
open scoped FourierTransform SchwartzMap

/-- **The L² integrability crux of the Fourier sup-norm bound:** `(1 + ‖ξ‖²)⁻¹ ∈ L²(ℝ³)`, equivalently
`(1 + ‖ξ‖²)⁻² ∈ L¹(ℝ³)`. Holds because the exponent `4` exceeds the dimension `3`
(`integrable_rpow_neg_one_add_norm_sq`). This is the integrability that bounds `‖û‖₁` by `‖(1−Δ)u‖₂`. -/
lemma integrable_oneAddNormSq_rpow_neg_two :
    Integrable (fun ξ : Space 3 => (1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ)) volume := by
  have h3 : Module.finrank ℝ (Space 3) = 3 := by simp
  have hdim : (Module.finrank ℝ (Space 3) : ℝ) < 4 := by rw [h3]; norm_num
  have h := integrable_rpow_neg_one_add_norm_sq (E := Space 3) (μ := volume) (r := 4) hdim
  have he : (fun ξ : Space 3 => (1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ))
      = fun x : Space 3 => (1 + ‖x‖ ^ 2) ^ (-4 / 2 : ℝ) := by funext x; norm_num
  rw [he]; exact h

/-- **The Fourier weight `(1 + ‖ξ‖²)⁻¹ ∈ L²(ℝ³)`** — finite `L²` norm, the factor that Cauchy–Schwarz
pairs against `(1+‖ξ‖²)·û` to bound `‖û‖_{L¹}` by `‖(1−Δ)u‖_{L²}`. -/
lemma memLp_two_oneAddNormSq_inv :
    MemLp (fun ξ : Space 3 => ((1 + ‖ξ‖ ^ 2)⁻¹ : ℝ)) 2 volume := by
  have hcont : Continuous (fun ξ : Space 3 => ((1 + ‖ξ‖ ^ 2)⁻¹ : ℝ)) :=
    Continuous.inv₀ (by fun_prop) (fun ξ => (by positivity : (0:ℝ) < 1 + ‖ξ‖ ^ 2).ne')
  rw [memLp_two_iff_integrable_sq hcont.aestronglyMeasurable]
  refine integrable_oneAddNormSq_rpow_neg_two.congr ?_
  filter_upwards with ξ
  rw [Real.rpow_neg (by positivity), Real.rpow_two, ← inv_pow]

/-- **Young's inequality, the relative-bound ε-step:** `2·√(A·B) ≤ ε·A + ε⁻¹·B` for `A, B ≥ 0`,
`ε > 0`. This converts the Hardy/interpolation estimate `‖Vu‖ ≤ 2·(‖Δu‖·‖u‖)^{1/2}` into the Kato
relative-bound form `a‖Δu‖ + b‖u‖` with `a = ε` arbitrarily small (so `a < 1`). -/
lemma two_sqrt_mul_le_smul_add {A B ε : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hε : 0 < ε) :
    2 * Real.sqrt (A * B) ≤ ε * A + ε⁻¹ * B := by
  have h1 : A * B = (ε * A) * (ε⁻¹ * B) := by field_simp
  have hkey := two_mul_le_add_sq (Real.sqrt (ε * A)) (Real.sqrt (ε⁻¹ * B))
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at hkey
  rw [h1, Real.sqrt_mul (by positivity)]
  nlinarith [hkey]

/-- **The interpolation `‖∇u‖² ≤ ‖Δu‖·‖u‖` on the Fourier side:** `∫ ‖ξ‖²‖f‖² ≤ √(∫‖ξ‖⁴‖f‖²)·√(∫‖f‖²)`.
Cauchy–Schwarz pairing the weight `‖ξ‖²` as `‖ξ‖²·1`. Instantiated at `f = û` (Plancherel), this is the
gradient–Laplacian interpolation feeding the Young step. -/
lemma integral_normSq_weight_le (f : Space 3 → ℂ)
    (hf : MemLp f 2 volume) (hwf : MemLp (fun ξ => (‖ξ‖ ^ 2 : ℝ) • f ξ) 2 volume) :
    ∫ ξ, ‖ξ‖ ^ 2 * ‖f ξ‖ ^ 2 ≤
      Real.sqrt (∫ ξ, ‖ξ‖ ^ 4 * ‖f ξ‖ ^ 2) * Real.sqrt (∫ ξ, ‖f ξ‖ ^ 2) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]; norm_num
  have hf' : MemLp f (ENNReal.ofReal 2) volume := by rw [ENNReal.ofReal_ofNat]; exact hf
  have hwf' : MemLp (fun ξ => (‖ξ‖ ^ 2 : ℝ) • f ξ) (ENNReal.ofReal 2) volume := by
    rw [ENNReal.ofReal_ofNat]; exact hwf
  have hcs := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq hpq hwf' hf'
  have hns : ∀ ξ : Space 3, ‖(‖ξ‖ ^ 2 : ℝ) • f ξ‖ = ‖ξ‖ ^ 2 * ‖f ξ‖ := fun ξ => by
    rw [Complex.real_smul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖ξ‖ ^ 2)]
  have hnat : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  have e1 : ∀ ξ : Space 3, ‖(‖ξ‖ ^ 2 : ℝ) • f ξ‖ * ‖f ξ‖ = ‖ξ‖ ^ 2 * ‖f ξ‖ ^ 2 := fun ξ => by
    rw [hns]; ring
  have e2 : ∀ ξ : Space 3, ‖(‖ξ‖ ^ 2 : ℝ) • f ξ‖ ^ (2 : ℝ) = ‖ξ‖ ^ 4 * ‖f ξ‖ ^ 2 := fun ξ => by
    rw [hns, hnat, Real.rpow_natCast]; ring
  have e3 : ∀ ξ : Space 3, ‖f ξ‖ ^ (2 : ℝ) = ‖f ξ‖ ^ 2 := fun ξ => by
    rw [hnat, Real.rpow_natCast]
  have i1 : ∫ ξ : Space 3, ‖ξ‖ ^ 2 * ‖f ξ‖ ^ 2 = ∫ ξ, ‖(‖ξ‖ ^ 2 : ℝ) • f ξ‖ * ‖f ξ‖ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ξ => (e1 ξ).symm)
  have i2 : ∫ ξ : Space 3, ‖ξ‖ ^ 4 * ‖f ξ‖ ^ 2 = ∫ ξ, ‖(‖ξ‖ ^ 2 : ℝ) • f ξ‖ ^ (2 : ℝ) :=
    integral_congr_ae (Filter.Eventually.of_forall fun ξ => (e2 ξ).symm)
  have i3 : ∫ ξ : Space 3, ‖f ξ‖ ^ 2 = ∫ ξ, ‖f ξ‖ ^ (2 : ℝ) :=
    integral_congr_ae (Filter.Eventually.of_forall fun ξ => (e3 ξ).symm)
  rw [i1, i2, i3, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact hcs

/-- **The far part of the Coulomb singularity is in `L^∞`:** `(1/‖x‖)·1_{‖x‖>1} ≤ 1`. Together with
the (forthcoming) near part `(1/‖x‖)·1_{‖x‖≤1} ∈ L²`, this is the `L² + L^∞` decomposition of the
Coulomb potential `1/‖x‖` that the Kato–Rellich bound consumes. -/
lemma coulomb_far_le_one (x : Space 3) :
    Set.indicator {y : Space 3 | 1 < ‖y‖} (fun y => 1 / ‖y‖) x ≤ 1 := by
  rw [Set.indicator_apply]
  split_ifs with hx
  · exact (div_le_one (by exact lt_trans one_pos hx)).mpr (le_of_lt hx)
  · norm_num

/-- **The L²·L^∞ Hölder step:** `∫ (V·u)² ≤ ‖u‖_∞² · ∫ V²`. With `V = V₁` (the Coulomb near part, in L²)
and `‖u‖_∞` controlled by the Fourier sup-norm bound, this is `‖V₁ u‖₂ ≤ ‖V₁‖₂·‖u‖_∞` — the bound on
the singular part of the Coulomb potential applied to `u`. -/
lemma integral_mul_sq_le_sup_sq_mul {V u : Space 3 → ℝ} {M : ℝ}
    (hM : ∀ x, |u x| ≤ M) (hV : Integrable (fun x => V x ^ 2)) :
    ∫ x, (V x * u x) ^ 2 ≤ M ^ 2 * ∫ x, V x ^ 2 := by
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
    (hV.const_mul _) (Filter.Eventually.of_forall fun x => ?_)
  have hux : u x ^ 2 ≤ M ^ 2 := sq_le_sq' (abs_le.mp (hM x)).1 (abs_le.mp (hM x)).2
  calc (V x * u x) ^ 2 = V x ^ 2 * u x ^ 2 := by ring
    _ ≤ V x ^ 2 * M ^ 2 := mul_le_mul_of_nonneg_left hux (sq_nonneg (V x))
    _ = M ^ 2 * V x ^ 2 := by ring

/-- **The L^∞·L² step (far Coulomb part):** `∫ (V·u)² ≤ ∫ u²` for `0 ≤ V ≤ 1`. With `V = V₂` (the bounded
far part, `V₂ ≤ 1` by `coulomb_far_le_one`), this is `‖V₂ u‖₂ ≤ ‖u‖₂` — the bound on the bounded part of
the Coulomb potential, the companion of `integral_mul_sq_le_sup_sq_mul` (the singular part). -/
lemma integral_bdd_mul_sq_le {V u : Space 3 → ℝ} (hV0 : ∀ x, 0 ≤ V x) (hV1 : ∀ x, V x ≤ 1)
    (hu : Integrable (fun x => u x ^ 2)) :
    ∫ x, (V x * u x) ^ 2 ≤ ∫ x, u x ^ 2 := by
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity) hu
    (Filter.Eventually.of_forall fun x => ?_)
  have hV2 : V x ^ 2 ≤ 1 := by nlinarith [hV0 x, hV1 x]
  calc (V x * u x) ^ 2 = V x ^ 2 * u x ^ 2 := by ring
    _ ≤ 1 * u x ^ 2 := mul_le_mul_of_nonneg_right hV2 (sq_nonneg _)
    _ = u x ^ 2 := one_mul _

/-- **L¹–weighted-L² Hölder (the heart of the sup-norm bound):** `∫ ‖g‖ ≤ ‖(1+‖ξ‖²)⁻¹‖₂ · ‖(1+‖ξ‖²)·g‖₂`.
With `g = û`: the LHS `‖û‖_{L¹}` bounds `‖u‖_∞` (Fourier inversion + `norm_fourierIntegral_le_integral_norm`),
and the second factor is `‖(1−Δ)u‖₂` (Plancherel). The weight `(1+‖ξ‖²)⁻¹ ∈ L²(ℝ³)` is
`memLp_two_oneAddNormSq_inv` — this is exactly where the `dim 3 < 4` integrability is consumed. -/
lemma integral_norm_le_weighted_L2 {g : Space 3 → ℂ}
    (hb : MemLp (fun ξ : Space 3 => ((1 + ‖ξ‖ ^ 2) * ‖g ξ‖ : ℝ)) 2 volume) :
    ∫ ξ : Space 3, ‖g ξ‖
      ≤ Real.sqrt (∫ ξ : Space 3, (((1 + ‖ξ‖ ^ 2)⁻¹ : ℝ)) ^ 2) *
          Real.sqrt (∫ ξ : Space 3, ((1 + ‖ξ‖ ^ 2) * ‖g ξ‖) ^ 2) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by rw [Real.holderConjugate_iff]; norm_num
  have ha' : MemLp (fun ξ : Space 3 => ((1 + ‖ξ‖ ^ 2)⁻¹ : ℝ)) (ENNReal.ofReal 2) volume := by
    rw [ENNReal.ofReal_ofNat]; exact memLp_two_oneAddNormSq_inv
  have hb' : MemLp (fun ξ : Space 3 => ((1 + ‖ξ‖ ^ 2) * ‖g ξ‖ : ℝ)) (ENNReal.ofReal 2) volume := by
    rw [ENNReal.ofReal_ofNat]; exact hb
  have hcs := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq hpq ha' hb'
  have hnat : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  have hna : ∀ ξ : Space 3, ‖((1 + ‖ξ‖ ^ 2)⁻¹ : ℝ)‖ = (1 + ‖ξ‖ ^ 2)⁻¹ := fun ξ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hnb : ∀ ξ : Space 3, ‖((1 + ‖ξ‖ ^ 2) * ‖g ξ‖ : ℝ)‖ = (1 + ‖ξ‖ ^ 2) * ‖g ξ‖ := fun ξ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have e0 : ∀ ξ : Space 3,
      ‖((1 + ‖ξ‖ ^ 2)⁻¹ : ℝ)‖ * ‖((1 + ‖ξ‖ ^ 2) * ‖g ξ‖ : ℝ)‖ = ‖g ξ‖ := fun ξ => by
    rw [hna, hnb, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  have ea : ∀ ξ : Space 3, ‖((1 + ‖ξ‖ ^ 2)⁻¹ : ℝ)‖ ^ (2 : ℝ) = ((1 + ‖ξ‖ ^ 2)⁻¹) ^ 2 := fun ξ => by
    rw [hna, hnat, Real.rpow_natCast]
  have eb : ∀ ξ : Space 3,
      ‖((1 + ‖ξ‖ ^ 2) * ‖g ξ‖ : ℝ)‖ ^ (2 : ℝ) = ((1 + ‖ξ‖ ^ 2) * ‖g ξ‖) ^ 2 := fun ξ => by
    rw [hnb, hnat, Real.rpow_natCast]
  have i0 : ∫ ξ : Space 3, ‖g ξ‖
      = ∫ ξ, ‖((1 + ‖ξ‖ ^ 2)⁻¹ : ℝ)‖ * ‖((1 + ‖ξ‖ ^ 2) * ‖g ξ‖ : ℝ)‖ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ξ => (e0 ξ).symm)
  have ia : ∫ ξ : Space 3, (((1 + ‖ξ‖ ^ 2)⁻¹ : ℝ)) ^ 2 = ∫ ξ, ‖((1 + ‖ξ‖ ^ 2)⁻¹ : ℝ)‖ ^ (2 : ℝ) :=
    integral_congr_ae (Filter.Eventually.of_forall fun ξ => (ea ξ).symm)
  have ib : ∫ ξ : Space 3, ((1 + ‖ξ‖ ^ 2) * ‖g ξ‖) ^ 2
      = ∫ ξ, ‖((1 + ‖ξ‖ ^ 2) * ‖g ξ‖ : ℝ)‖ ^ (2 : ℝ) :=
    integral_congr_ae (Filter.Eventually.of_forall fun ξ => (eb ξ).symm)
  rw [i0, ia, ib, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact hcs

/-- **The Coulomb near part is in `L²`:** `(1/‖x‖)·1_{‖x‖≤1} ∈ L²(ℝ³)`, equivalently
`‖x‖⁻² ·1_{‖x‖≤1} ∈ L¹`. Via the polar-coordinate reduction (`integrable_fun_norm_addHaar`): the radial
integrand `y^(3-1)·(y⁻² 1_{y≤1}) = 1_{0<y≤1}` is integrable. This is `V₁ ∈ L²`, the singular part of the
`L²+L^∞` Coulomb split (the bounded part `V₂` is `coulomb_far_le_one`), feeding `integral_mul_sq_le_sup_sq_mul`. -/
lemma integrable_coulombNear_sq :
    Integrable (fun x : Space 3 => if ‖x‖ ≤ 1 then ‖x‖ ^ (-2 : ℝ) else 0) volume := by
  have hdim : Module.finrank ℝ (Space 3) = 3 := by simp
  rw [integrable_fun_norm_addHaar (μ := volume) (f := fun r : ℝ => if r ≤ 1 then r ^ (-2 : ℝ) else 0),
    hdim]
  have h2 : (3 : ℕ) - 1 = 2 := rfl
  rw [h2, ← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one), integrableOn_union]
  refine ⟨?_, ?_⟩
  · -- on Ioc 0 1 the radial integrand `y² · y⁻²` equals the constant 1
    have hμs : volume (Set.Ioc (0 : ℝ) 1) ≠ ⊤ := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
    have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc 0 1) volume :=
      integrableOn_const hμs (by simp)
    refine hconst.congr_fun ?_ measurableSet_Ioc
    rintro y ⟨hy0, hy1⟩
    simp only [if_pos hy1, smul_eq_mul]
    rw [← Real.rpow_natCast y 2, ← Real.rpow_add hy0]
    norm_num
  · -- on Ioi 1 the radial integrand vanishes (the indicator is off)
    refine integrableOn_zero.congr_fun ?_ measurableSet_Ioi
    intro y hy
    simp only [Set.mem_Ioi] at hy
    simp only [if_neg (by linarith : ¬ y ≤ 1), smul_zero]

/-- **Fourier inversion ⟹ the L^∞≤L¹ sup-bound:** `‖u x‖ ≤ ∫ ‖𝓕 u‖` for Schwartz `u`. Since
`u = 𝓕⁻(𝓕 u)` (`SchwartzMap.fourier_inversion`) and the inverse transform unfolds to a
`VectorFourier.fourierIntegral`, the L^∞≤L¹ bound `norm_fourierIntegral_le_integral_norm` applies. This is
the first step of the Fourier sup-norm bound: `‖u‖_∞ ≤ ‖û‖_{L¹}`, to be chained with
`integral_norm_le_weighted_L2` (Hölder) and Plancherel. -/
lemma norm_le_integral_norm_fourier (u : 𝓢(Space 3, ℂ)) (x : Space 3) :
    ‖u x‖ ≤ ∫ ξ : Space 3, ‖(𝓕 u) ξ‖ := by
  have h1 : (u : Space 3 → ℂ) = 𝓕⁻ ((𝓕 u : 𝓢(Space 3, ℂ)) : Space 3 → ℂ) := by
    rw [← SchwartzMap.fourierInv_coe]
    exact congrArg DFunLike.coe (FourierPair.fourierInv_fourier_eq u).symm
  rw [show ‖u x‖ = ‖𝓕⁻ ((𝓕 u : 𝓢(Space 3, ℂ)) : Space 3 → ℂ) x‖ from by rw [h1],
    Real.fourierInv_eq]
  have heq : ∫ v : Space 3, ‖𝐞 (inner ℝ v x) • (𝓕 u) v‖ = ∫ ξ : Space 3, ‖(𝓕 u) ξ‖ :=
    integral_congr_ae (Filter.Eventually.of_forall fun v => by simp)
  rw [← heq]
  exact norm_integral_le_integral_norm _

/-- **The Fourier sup-norm bound (assembled):** `‖u x‖ ≤ ‖(1+‖ξ‖²)⁻¹‖₂ · ‖(1+‖ξ‖²)·û‖₂` for Schwartz `u`.
Chains the L^∞≤L¹ inversion step (`norm_le_integral_norm_fourier`) with the weighted-L² Hölder
(`integral_norm_le_weighted_L2`). The first factor `‖(1+‖ξ‖²)⁻¹‖₂` is a finite constant (`dim 3 < 4`,
`memLp_two_oneAddNormSq_inv`); the second is `‖(1−Δ)u‖₂` by Plancherel + the W2 multiplier. The hypothesis
`hb` (the weighted transform is in L²) holds because `(1+‖ξ‖²)·û` is Schwartz. -/
lemma norm_le_weighted_L2_sup (u : 𝓢(Space 3, ℂ))
    (hb : MemLp (fun ξ : Space 3 => ((1 + ‖ξ‖ ^ 2) * ‖(𝓕 u) ξ‖ : ℝ)) 2 volume) (x : Space 3) :
    ‖u x‖ ≤ Real.sqrt (∫ ξ : Space 3, (((1 + ‖ξ‖ ^ 2)⁻¹ : ℝ)) ^ 2) *
              Real.sqrt (∫ ξ : Space 3, ((1 + ‖ξ‖ ^ 2) * ‖(𝓕 u) ξ‖) ^ 2) :=
  (norm_le_integral_norm_fourier u x).trans (integral_norm_le_weighted_L2 hb)

/-- **Discharge of the sup-norm hypothesis `hb`:** the weighted Fourier transform `(1+‖ξ‖²)·‖û‖` is in
`L²(ℝ³)`, because `(1+‖ξ‖²)·û` is a Schwartz function (`smulLeftCLM` by the temperate-growth weight
`1+‖ξ‖²`) and every Schwartz function is in `L²` (`SchwartzMap.memLp`). This makes `norm_le_weighted_L2_sup`
unconditional for any Schwartz `u`. -/
lemma memLp_weighted_fourier (u : 𝓢(Space 3, ℂ)) :
    MemLp (fun ξ : Space 3 => ((1 + ‖ξ‖ ^ 2) * ‖(𝓕 u) ξ‖ : ℝ)) 2 volume := by
  have hgr : Function.HasTemperateGrowth (fun ξ : Space 3 => (1 + ‖ξ‖ ^ 2 : ℝ)) :=
    (Function.HasTemperateGrowth.const (1 : ℝ)).add (Function.hasTemperateGrowth_norm_sq (H := Space 3))
  have hg : Function.HasTemperateGrowth (fun ξ : Space 3 => ((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.hasTemperateGrowth.comp hgr
  have hmem : MemLp (fun ξ : Space 3 =>
      ‖(SchwartzMap.smulLeftCLM ℂ (fun ξ : Space 3 => ((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ)) (𝓕 u)) ξ‖) 2 volume :=
    (SchwartzMap.memLp _ 2 volume).norm
  refine hmem.ae_eq (Filter.Eventually.of_forall fun ξ => ?_)
  rw [SchwartzMap.smulLeftCLM_apply_apply hg, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖ξ‖ ^ 2)]

/-- **Operator-bridge split:** `‖(1+‖ξ‖²)g‖₂ ≤ √2·‖g‖₂ + √2·‖‖ξ‖²g‖₂` (in `√(∫‖·‖²)` form). Uses the
pointwise quadratic bound `(1+‖ξ‖²)² ≤ 2 + 2‖ξ‖⁴` (i.e. `(1−‖ξ‖²)² ≥ 0`) + sqrt subadditivity — avoiding
full L² Minkowski. At `g = û`: `√(∫‖g‖²) = ‖u‖₂` (Plancherel) and `√(∫‖ξ‖⁴‖g‖²) = ‖‖ξ‖²û‖₂` connects to
`‖momentumSq u‖₂` via the W2 multiplier, turning the sup-norm bound into a kinetic-operator bound. -/
lemma sqrt_weighted_le {g : Space 3 → ℂ}
    (h0 : Integrable (fun ξ : Space 3 => ‖g ξ‖ ^ 2))
    (h4 : Integrable (fun ξ : Space 3 => ‖ξ‖ ^ 4 * ‖g ξ‖ ^ 2)) :
    Real.sqrt (∫ ξ : Space 3, ((1 + ‖ξ‖ ^ 2) * ‖g ξ‖) ^ 2)
      ≤ Real.sqrt 2 * Real.sqrt (∫ ξ : Space 3, ‖g ξ‖ ^ 2)
        + Real.sqrt 2 * Real.sqrt (∫ ξ : Space 3, ‖ξ‖ ^ 4 * ‖g ξ‖ ^ 2) := by
  have hsub : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
    intro a b ha hb
    have h := Real.sqrt_le_sqrt (show a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 by
      nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb,
        mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)])
    rwa [Real.sqrt_sq (by positivity)] at h
  have hstep : ∫ ξ : Space 3, ((1 + ‖ξ‖ ^ 2) * ‖g ξ‖) ^ 2
      ≤ ∫ ξ : Space 3, (2 * ‖g ξ‖ ^ 2 + 2 * (‖ξ‖ ^ 4 * ‖g ξ‖ ^ 2)) :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun ξ => by positivity)
      ((h0.const_mul 2).add (h4.const_mul 2))
      (Filter.Eventually.of_forall fun ξ => by
        nlinarith [mul_nonneg (sq_nonneg (1 - ‖ξ‖ ^ 2)) (sq_nonneg ‖g ξ‖), sq_nonneg ‖g ξ‖])
  rw [integral_add (h0.const_mul 2) (h4.const_mul 2), integral_const_mul, integral_const_mul] at hstep
  have hA : (0 : ℝ) ≤ 2 * ∫ ξ : Space 3, ‖g ξ‖ ^ 2 := by
    have : (0 : ℝ) ≤ ∫ ξ : Space 3, ‖g ξ‖ ^ 2 := integral_nonneg fun ξ => by positivity
    linarith
  have hB : (0 : ℝ) ≤ 2 * ∫ ξ : Space 3, ‖ξ‖ ^ 4 * ‖g ξ‖ ^ 2 := by
    have : (0 : ℝ) ≤ ∫ ξ : Space 3, ‖ξ‖ ^ 4 * ‖g ξ‖ ^ 2 := integral_nonneg fun ξ => by positivity
    linarith
  calc Real.sqrt (∫ ξ : Space 3, ((1 + ‖ξ‖ ^ 2) * ‖g ξ‖) ^ 2)
      ≤ Real.sqrt (2 * (∫ ξ : Space 3, ‖g ξ‖ ^ 2) + 2 * ∫ ξ : Space 3, ‖ξ‖ ^ 4 * ‖g ξ‖ ^ 2) :=
        Real.sqrt_le_sqrt hstep
    _ ≤ Real.sqrt (2 * ∫ ξ : Space 3, ‖g ξ‖ ^ 2)
          + Real.sqrt (2 * ∫ ξ : Space 3, ‖ξ‖ ^ 4 * ‖g ξ‖ ^ 2) := hsub _ _ hA hB
    _ = Real.sqrt 2 * Real.sqrt (∫ ξ : Space 3, ‖g ξ‖ ^ 2)
          + Real.sqrt 2 * Real.sqrt (∫ ξ : Space 3, ‖ξ‖ ^ 4 * ‖g ξ‖ ^ 2) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]

/-- **The Fourier multiplier acts as pointwise multiplication on the transform:**
`𝓕(fourierMultiplierCLM g f) = g · 𝓕f`. Immediate from the definition
`fourierMultiplierCLM g f = 𝓕⁻(g · 𝓕f)` (`fourierMultiplierCLM_apply`) and `𝓕 ∘ 𝓕⁻ = id`
(`fourier_inversion_inv`). Applied to W2's `momentumSq_schwartz_eq_fourierMultiplier` this turns
`∑ pᵢ²u` into `(2πℏ)²·‖ξ‖²·û` on the Fourier side — the bridge from the momentum operator to the
`‖ξ‖²û` weight in the sup-norm bound. -/
lemma fourier_fourierMultiplierCLM (g : Space 3 → ℂ) (f : 𝓢(Space 3, ℂ)) :
    𝓕 (SchwartzMap.fourierMultiplierCLM ℂ g f) = SchwartzMap.smulLeftCLM ℂ g (𝓕 f) := by
  rw [SchwartzMap.fourierMultiplierCLM_apply, FourierInvPair.fourier_fourierInv_eq]

open QuantumMechanics in
/-- **Fourier-side form of the momentum-square operator:** `𝓕(∑ pᵢ²f) = (2πℏ)²·(‖ξ‖²·û)`. Apply `𝓕` to
W2's `momentumSq_schwartz_eq_fourierMultiplier` (`∑pᵢ²f = (2πℏ)²·M[‖ξ‖²]f`) using `𝓕`-linearity and the
multiplier-Fourier identity `fourier_fourierMultiplierCLM`. This is the operator→Fourier bridge feeding
the momentum-norm identity (Plancherel then connects `∫‖ξ‖⁴‖û‖²` to `‖∑pᵢ²f‖₂`). -/
lemma fourier_momentumSq (f : 𝓢(Space 3, ℂ)) :
    𝓕 (∑ i, momentumCLM i (momentumCLM i f))
      = ((2 * Real.pi * Constants.ℏ) ^ 2 : ℂ) •
        SchwartzMap.smulLeftCLM ℂ (fun ξ : Space 3 => ((‖ξ‖ ^ 2 : ℝ) : ℂ)) (𝓕 f) := by
  rw [momentumSq_schwartz_eq_fourierMultiplier, FourierTransform.fourier_smul,
    fourier_fourierMultiplierCLM]

open QuantumMechanics in
/-- **The momentum-norm identity:** `(2πℏ)⁴·∫ ‖ξ‖⁴‖û‖² = ∫ ‖∑ pᵢ²f‖²`. Take the pointwise norm of
`fourier_momentumSq` (`𝓕(∑pᵢ²f) ξ = (2πℏ)²‖ξ‖²·û ξ`) and integrate, then apply the free Plancherel
isometry `SchwartzMap.integral_norm_sq_fourier`. This closes the operator bridge: the `‖‖ξ‖²û‖₂` term of
the sup-norm bound (W3-13) equals `(2πℏ)⁻²·‖∑pᵢ²f‖₂`, i.e. a constant times the kinetic-operator L² norm. -/
lemma integral_normSq_weight_eq_momentumSq (f : 𝓢(Space 3, ℂ)) :
    ((2 * Real.pi * Constants.ℏ) ^ 2) ^ 2 * ∫ ξ : Space 3, ‖ξ‖ ^ 4 * ‖(𝓕 f) ξ‖ ^ 2
      = ∫ x : Space 3, ‖(∑ i, momentumCLM i (momentumCLM i f)) x‖ ^ 2 := by
  have hg2 : Function.HasTemperateGrowth (fun ξ : Space 3 => ((‖ξ‖ ^ 2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.hasTemperateGrowth.comp (Function.hasTemperateGrowth_norm_sq (H := Space 3))
  have hpt : ∀ ξ : Space 3, ‖(𝓕 (∑ i, momentumCLM i (momentumCLM i f))) ξ‖ ^ 2
      = ((2 * Real.pi * Constants.ℏ) ^ 2) ^ 2 * (‖ξ‖ ^ 4 * ‖(𝓕 f) ξ‖ ^ 2) := by
    intro ξ
    rw [fourier_momentumSq, SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hg2, smul_smul,
      show ((2 * Real.pi * Constants.ℏ) ^ 2 : ℂ) * ((‖ξ‖ ^ 2 : ℝ) : ℂ)
        = (((2 * Real.pi * Constants.ℏ) ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) by push_cast; ring,
      norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 * Real.pi * Constants.ℏ) ^ 2 * ‖ξ‖ ^ 2), mul_pow]
    ring
  rw [← SchwartzMap.integral_norm_sq_fourier (∑ i, momentumCLM i (momentumCLM i f)),
    integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul]

/-- `‖û‖² ∈ L¹` — the `h0` integrability `sqrt_weighted_le` (W3-13) consumes (`û` Schwartz ⟹ `MemLp 2`). -/
lemma integrable_normSq_fourier (f : 𝓢(Space 3, ℂ)) :
    Integrable (fun ξ : Space 3 => ‖(𝓕 f) ξ‖ ^ 2) := by
  have h := (SchwartzMap.memLp (𝓕 f) 2 volume).norm
  rw [memLp_two_iff_integrable_sq (𝓕 f).continuous.norm.aestronglyMeasurable] at h
  simpa only [norm_norm] using h

/-- `‖ξ‖⁴‖û‖² ∈ L¹` — the `h4` integrability `sqrt_weighted_le` (W3-13) consumes. Equals `‖(‖ξ‖²·û)‖²`,
integrable because `‖ξ‖²·û` is Schwartz (`smulLeftCLM`). -/
lemma integrable_weight4_normSq_fourier (f : 𝓢(Space 3, ℂ)) :
    Integrable (fun ξ : Space 3 => ‖ξ‖ ^ 4 * ‖(𝓕 f) ξ‖ ^ 2) := by
  have hg2 : Function.HasTemperateGrowth (fun ξ : Space 3 => ((‖ξ‖ ^ 2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.hasTemperateGrowth.comp (Function.hasTemperateGrowth_norm_sq (H := Space 3))
  have hwint := (SchwartzMap.memLp
    (SchwartzMap.smulLeftCLM ℂ (fun ξ : Space 3 => ((‖ξ‖ ^ 2 : ℝ) : ℂ)) (𝓕 f)) 2 volume).norm
  rw [memLp_two_iff_integrable_sq (SchwartzMap.smulLeftCLM ℂ (fun ξ : Space 3 => ((‖ξ‖ ^ 2 : ℝ) : ℂ))
    (𝓕 f)).continuous.norm.aestronglyMeasurable] at hwint
  refine hwint.congr (Filter.Eventually.of_forall fun ξ => ?_)
  dsimp only
  rw [SchwartzMap.smulLeftCLM_apply_apply hg2, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖ξ‖ ^ 2), mul_pow]
  ring

open QuantumMechanics in
/-- **The operator-form Fourier sup-norm bound (single-particle Kato sup-estimate):**
`‖f x‖ ≤ C₀√2·‖f‖₂ + (C₀√2/(2πℏ)²)·‖∑ pᵢ²f‖₂` for Schwartz `f`, where `C₀ = ‖(1+‖ξ‖²)⁻¹‖₂` is a finite
constant (`dim 3 < 4`). Composes the unconditional sup-norm bound (W3-11/12), the operator-bridge split
(W3-13 with integrability W3-17/18), the free Plancherel isometry, and the momentum-norm identity (W3-16).
This is the heart of the Kato relative bound: `‖u‖_∞` controlled by the L² and kinetic-operator norms. The
scaling `u→u(λ·)` (next) turns the kinetic coefficient into an arbitrarily small `ε`. -/
lemma norm_sup_le_kinetic (f : 𝓢(Space 3, ℂ)) (x : Space 3) :
    ‖f x‖ ≤ Real.sqrt (∫ ξ : Space 3, (((1 + ‖ξ‖ ^ 2)⁻¹ : ℝ)) ^ 2) * Real.sqrt 2
              * Real.sqrt (∫ y : Space 3, ‖f y‖ ^ 2)
          + Real.sqrt (∫ ξ : Space 3, (((1 + ‖ξ‖ ^ 2)⁻¹ : ℝ)) ^ 2) * Real.sqrt 2
              / (2 * Real.pi * Constants.ℏ) ^ 2
              * Real.sqrt (∫ y : Space 3, ‖(∑ i, momentumCLM i (momentumCLM i f)) y‖ ^ 2) := by
  have h11 := norm_le_weighted_L2_sup f (memLp_weighted_fourier f) x
  have h13 := sqrt_weighted_le (integrable_normSq_fourier f) (integrable_weight4_normSq_fourier f)
  have hpl : Real.sqrt (∫ ξ : Space 3, ‖(𝓕 f) ξ‖ ^ 2) = Real.sqrt (∫ y : Space 3, ‖f y‖ ^ 2) := by
    rw [SchwartzMap.integral_norm_sq_fourier]
  have hmom : Real.sqrt (∫ ξ : Space 3, ‖ξ‖ ^ 4 * ‖(𝓕 f) ξ‖ ^ 2)
      = Real.sqrt (∫ y : Space 3, ‖(∑ i, momentumCLM i (momentumCLM i f)) y‖ ^ 2)
        / (2 * Real.pi * Constants.ℏ) ^ 2 := by
    have hℏ := Constants.ℏ_pos
    rw [eq_div_iff (by positivity : (2 * Real.pi * Constants.ℏ) ^ 2 ≠ 0),
      ← integral_normSq_weight_eq_momentumSq f, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by positivity)]
    ring
  calc ‖f x‖
      ≤ Real.sqrt (∫ ξ : Space 3, (((1 + ‖ξ‖ ^ 2)⁻¹ : ℝ)) ^ 2)
          * Real.sqrt (∫ ξ : Space 3, ((1 + ‖ξ‖ ^ 2) * ‖(𝓕 f) ξ‖) ^ 2) := h11
    _ ≤ Real.sqrt (∫ ξ : Space 3, (((1 + ‖ξ‖ ^ 2)⁻¹ : ℝ)) ^ 2)
          * (Real.sqrt 2 * Real.sqrt (∫ ξ : Space 3, ‖(𝓕 f) ξ‖ ^ 2)
            + Real.sqrt 2 * Real.sqrt (∫ ξ : Space 3, ‖ξ‖ ^ 4 * ‖(𝓕 f) ξ‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left h13 (Real.sqrt_nonneg _)
    _ = _ := by rw [hpl, hmom]; ring

/-- **Dilation L²-scaling:** `∫ ‖u(R·x)‖² = R⁻³·∫ ‖u‖²` for `R > 0` on `ℝ³`. The change-of-variables
`x ↦ R·x` with Jacobian `R⁻³` (`Measure.integral_comp_smul`, `dim 3`). Foundation of the Kato scaling
argument: applied to `u` and to `∑pᵢ²u`, it gives `‖u_R‖₂ = R^{-3/2}‖u‖₂` etc., shrinking the kinetic
coefficient of the sup-estimate to an arbitrary `ε`. -/
lemma integral_normSq_comp_smul (u : Space 3 → ℂ) {R : ℝ} (hR : 0 < R) :
    ∫ x : Space 3, ‖u (R • x)‖ ^ 2 = (R ^ 3)⁻¹ * ∫ x : Space 3, ‖u x‖ ^ 2 := by
  have h3 : Module.finrank ℝ (Space 3) = 3 := by simp
  rw [MeasureTheory.Measure.integral_comp_smul volume (fun x => ‖u x‖ ^ 2) R, h3, smul_eq_mul,
    abs_of_pos (by positivity)]

/-- **Weight-constant scaling:** `∫ ((1+t‖ξ‖²)⁻¹)² = (√t)⁻³ · ∫ ((1+‖ξ‖²)⁻¹)²` for `t > 0`. The
substitution `ξ = (1/√t)·η` collapses `1+t‖ξ‖² = 1+‖√t·ξ‖²` to the unit weight (`integral_comp_smul`,
`dim 3`). This is the `t`-dependence of the sup-norm constant `C₀(t) = (√t)^{-3/2}C₀`, whose `t^{-3/4}`
growth trades against the `t^{1/4}` shrink of the kinetic coefficient — the engine of the Kato ε-trick. -/
lemma integral_weightInv_sq_smul {t : ℝ} (ht : 0 < t) :
    ∫ ξ : Space 3, (((1 + t * ‖ξ‖ ^ 2)⁻¹ : ℝ)) ^ 2
      = ((Real.sqrt t) ^ 3)⁻¹ * ∫ ξ : Space 3, (((1 + ‖ξ‖ ^ 2)⁻¹ : ℝ)) ^ 2 := by
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have h3 : Module.finrank ℝ (Space 3) = 3 := by simp
  have hrw : ∀ ξ : Space 3, (((1 + t * ‖ξ‖ ^ 2)⁻¹ : ℝ)) ^ 2
      = (fun η : Space 3 => (((1 + ‖η‖ ^ 2)⁻¹ : ℝ)) ^ 2) (Real.sqrt t • ξ) := by
    intro ξ
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hst, mul_pow, Real.sq_sqrt ht.le]
  rw [integral_congr_ae (Filter.Eventually.of_forall hrw),
    MeasureTheory.Measure.integral_comp_smul volume
      (fun η : Space 3 => (((1 + ‖η‖ ^ 2)⁻¹ : ℝ)) ^ 2) (Real.sqrt t),
    h3, smul_eq_mul, abs_of_pos (by positivity)]

/-- **t-parameterized operator-bridge split:** `‖(1+t‖ξ‖²)g‖₂ ≤ √2·‖g‖₂ + √2·t·‖‖ξ‖²g‖₂`. The t-version
of `sqrt_weighted_le` via `(1+t‖ξ‖²)² ≤ 2 + 2t²‖ξ‖⁴` (= `(1−t‖ξ‖²)² ≥ 0`). The factor `t` on the second
term is the kinetic shrink of the Kato ε-trick: paired with the `t^{-3/4}` constant growth (W3-21), the
kinetic coefficient `∝ t^{1/4} → 0`. -/
lemma sqrt_weighted_le_t {g : Space 3 → ℂ} {t : ℝ} (ht : 0 < t)
    (h0 : Integrable (fun ξ : Space 3 => ‖g ξ‖ ^ 2))
    (h4 : Integrable (fun ξ : Space 3 => ‖ξ‖ ^ 4 * ‖g ξ‖ ^ 2)) :
    Real.sqrt (∫ ξ : Space 3, ((1 + t * ‖ξ‖ ^ 2) * ‖g ξ‖) ^ 2)
      ≤ Real.sqrt 2 * Real.sqrt (∫ ξ : Space 3, ‖g ξ‖ ^ 2)
        + Real.sqrt 2 * t * Real.sqrt (∫ ξ : Space 3, ‖ξ‖ ^ 4 * ‖g ξ‖ ^ 2) := by
  have hsub : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
    intro a b ha hb
    have h := Real.sqrt_le_sqrt (show a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 by
      nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb,
        mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)])
    rwa [Real.sqrt_sq (by positivity)] at h
  have hstep : ∫ ξ : Space 3, ((1 + t * ‖ξ‖ ^ 2) * ‖g ξ‖) ^ 2
      ≤ ∫ ξ : Space 3, (2 * ‖g ξ‖ ^ 2 + 2 * t ^ 2 * (‖ξ‖ ^ 4 * ‖g ξ‖ ^ 2)) :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun ξ => by positivity)
      ((h0.const_mul 2).add (h4.const_mul (2 * t ^ 2)))
      (Filter.Eventually.of_forall fun ξ => by
        nlinarith [mul_nonneg (sq_nonneg (1 - t * ‖ξ‖ ^ 2)) (sq_nonneg ‖g ξ‖), sq_nonneg ‖g ξ‖,
          mul_nonneg (sq_nonneg t) (sq_nonneg ‖g ξ‖)])
  rw [integral_add (h0.const_mul 2) (h4.const_mul (2 * t ^ 2))] at hstep
  simp only [integral_const_mul] at hstep
  have hA : (0 : ℝ) ≤ 2 * ∫ ξ : Space 3, ‖g ξ‖ ^ 2 := by
    have : (0 : ℝ) ≤ ∫ ξ : Space 3, ‖g ξ‖ ^ 2 := integral_nonneg fun ξ => by positivity
    linarith
  have hB : (0 : ℝ) ≤ 2 * t ^ 2 * ∫ ξ : Space 3, ‖ξ‖ ^ 4 * ‖g ξ‖ ^ 2 := by
    have : (0 : ℝ) ≤ ∫ ξ : Space 3, ‖ξ‖ ^ 4 * ‖g ξ‖ ^ 2 := integral_nonneg fun ξ => by positivity
    positivity
  have e2 : Real.sqrt (2 * t ^ 2 * ∫ ξ : Space 3, ‖ξ‖ ^ 4 * ‖g ξ‖ ^ 2)
      = Real.sqrt 2 * t * Real.sqrt (∫ ξ : Space 3, ‖ξ‖ ^ 4 * ‖g ξ‖ ^ 2) := by
    rw [show (2 : ℝ) * t ^ 2 * (∫ ξ : Space 3, ‖ξ‖ ^ 4 * ‖g ξ‖ ^ 2)
        = 2 * (t ^ 2 * (∫ ξ : Space 3, ‖ξ‖ ^ 4 * ‖g ξ‖ ^ 2)) from by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le,
      mul_assoc]
  calc Real.sqrt (∫ ξ : Space 3, ((1 + t * ‖ξ‖ ^ 2) * ‖g ξ‖) ^ 2)
      ≤ Real.sqrt (2 * (∫ ξ : Space 3, ‖g ξ‖ ^ 2)
          + 2 * t ^ 2 * ∫ ξ : Space 3, ‖ξ‖ ^ 4 * ‖g ξ‖ ^ 2) := Real.sqrt_le_sqrt hstep
    _ ≤ Real.sqrt (2 * ∫ ξ : Space 3, ‖g ξ‖ ^ 2)
          + Real.sqrt (2 * t ^ 2 * ∫ ξ : Space 3, ‖ξ‖ ^ 4 * ‖g ξ‖ ^ 2) := hsub _ _ hA hB
    _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), e2]

/-- **The t-weight `(1+t‖ξ‖²)⁻¹ ∈ L²(ℝ³)`** for any `t > 0`. Since `(1+t‖ξ‖²)⁻¹ = (1+‖√t·ξ‖²)⁻¹` is a
dilation of the unit weight (`memLp_two_oneAddNormSq_inv`, W3-2a) and dilation preserves integrability
(`integrable_comp_smul_iff`). The L² weight that the t-Hölder pairs against `(1+t‖ξ‖²)·û`. -/
lemma memLp_two_oneAddTNormSq_inv {t : ℝ} (ht : 0 < t) :
    MemLp (fun ξ : Space 3 => ((1 + t * ‖ξ‖ ^ 2)⁻¹ : ℝ)) 2 volume := by
  have hst : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have hcont : Continuous (fun ξ : Space 3 => ((1 + t * ‖ξ‖ ^ 2)⁻¹ : ℝ)) :=
    Continuous.inv₀ (by fun_prop) (fun ξ => (by positivity : (0 : ℝ) < 1 + t * ‖ξ‖ ^ 2).ne')
  have hcont0 : Continuous (fun ξ : Space 3 => ((1 + ‖ξ‖ ^ 2)⁻¹ : ℝ)) :=
    Continuous.inv₀ (by fun_prop) (fun ξ => (by positivity : (0 : ℝ) < 1 + ‖ξ‖ ^ 2).ne')
  have hg2 : Integrable (fun η : Space 3 => (((1 + ‖η‖ ^ 2)⁻¹ : ℝ)) ^ 2) := by
    have h := memLp_two_oneAddNormSq_inv
    rwa [memLp_two_iff_integrable_sq hcont0.aestronglyMeasurable] at h
  rw [memLp_two_iff_integrable_sq hcont.aestronglyMeasurable]
  refine ((integrable_comp_smul_iff volume
    (fun η : Space 3 => (((1 + ‖η‖ ^ 2)⁻¹ : ℝ)) ^ 2) hst).mpr hg2).congr ?_
  filter_upwards with ξ
  have hsm : ‖(Real.sqrt t • ξ : Space 3)‖ ^ 2 = t * ‖ξ‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr ht), mul_pow, Real.sq_sqrt ht.le]
  simp only [hsm]

/-- **t-parameterized L¹–weighted-L² Hölder:** `∫ ‖g‖ ≤ ‖(1+t‖ξ‖²)⁻¹‖₂ · ‖(1+t‖ξ‖²)·g‖₂`. The t-version
of `integral_norm_le_weighted_L2` (W3-8), now with the t-weight L² factor `memLp_two_oneAddTNormSq_inv`
(W3-23). Pairs the `(√t)^{-3/2}` constant (W3-21) against `(1+t‖ξ‖²)·g` (split by W3-22) — the t-Hölder
of the Kato ε-trick. -/
lemma integral_norm_le_weighted_L2_t {g : Space 3 → ℂ} {t : ℝ} (ht : 0 < t)
    (hb : MemLp (fun ξ : Space 3 => ((1 + t * ‖ξ‖ ^ 2) * ‖g ξ‖ : ℝ)) 2 volume) :
    ∫ ξ : Space 3, ‖g ξ‖
      ≤ Real.sqrt (∫ ξ : Space 3, (((1 + t * ‖ξ‖ ^ 2)⁻¹ : ℝ)) ^ 2) *
          Real.sqrt (∫ ξ : Space 3, ((1 + t * ‖ξ‖ ^ 2) * ‖g ξ‖) ^ 2) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by rw [Real.holderConjugate_iff]; norm_num
  have ha' : MemLp (fun ξ : Space 3 => ((1 + t * ‖ξ‖ ^ 2)⁻¹ : ℝ)) (ENNReal.ofReal 2) volume := by
    rw [ENNReal.ofReal_ofNat]; exact memLp_two_oneAddTNormSq_inv ht
  have hb' : MemLp (fun ξ : Space 3 => ((1 + t * ‖ξ‖ ^ 2) * ‖g ξ‖ : ℝ)) (ENNReal.ofReal 2) volume := by
    rw [ENNReal.ofReal_ofNat]; exact hb
  have hcs := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq hpq ha' hb'
  have hnat : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  have hna : ∀ ξ : Space 3, ‖((1 + t * ‖ξ‖ ^ 2)⁻¹ : ℝ)‖ = (1 + t * ‖ξ‖ ^ 2)⁻¹ := fun ξ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hnb : ∀ ξ : Space 3, ‖((1 + t * ‖ξ‖ ^ 2) * ‖g ξ‖ : ℝ)‖ = (1 + t * ‖ξ‖ ^ 2) * ‖g ξ‖ := fun ξ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have e0 : ∀ ξ : Space 3,
      ‖((1 + t * ‖ξ‖ ^ 2)⁻¹ : ℝ)‖ * ‖((1 + t * ‖ξ‖ ^ 2) * ‖g ξ‖ : ℝ)‖ = ‖g ξ‖ := fun ξ => by
    rw [hna, hnb, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  have ea : ∀ ξ : Space 3, ‖((1 + t * ‖ξ‖ ^ 2)⁻¹ : ℝ)‖ ^ (2 : ℝ) = ((1 + t * ‖ξ‖ ^ 2)⁻¹) ^ 2 :=
    fun ξ => by rw [hna, hnat, Real.rpow_natCast]
  have eb : ∀ ξ : Space 3,
      ‖((1 + t * ‖ξ‖ ^ 2) * ‖g ξ‖ : ℝ)‖ ^ (2 : ℝ) = ((1 + t * ‖ξ‖ ^ 2) * ‖g ξ‖) ^ 2 :=
    fun ξ => by rw [hnb, hnat, Real.rpow_natCast]
  have i0 : ∫ ξ : Space 3, ‖g ξ‖
      = ∫ ξ, ‖((1 + t * ‖ξ‖ ^ 2)⁻¹ : ℝ)‖ * ‖((1 + t * ‖ξ‖ ^ 2) * ‖g ξ‖ : ℝ)‖ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ξ => (e0 ξ).symm)
  have ia : ∫ ξ : Space 3, (((1 + t * ‖ξ‖ ^ 2)⁻¹ : ℝ)) ^ 2
      = ∫ ξ, ‖((1 + t * ‖ξ‖ ^ 2)⁻¹ : ℝ)‖ ^ (2 : ℝ) :=
    integral_congr_ae (Filter.Eventually.of_forall fun ξ => (ea ξ).symm)
  have ib : ∫ ξ : Space 3, ((1 + t * ‖ξ‖ ^ 2) * ‖g ξ‖) ^ 2
      = ∫ ξ, ‖((1 + t * ‖ξ‖ ^ 2) * ‖g ξ‖ : ℝ)‖ ^ (2 : ℝ) :=
    integral_congr_ae (Filter.Eventually.of_forall fun ξ => (eb ξ).symm)
  rw [i0, ia, ib, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact hcs

/-- **t-version of the sup-norm hypothesis `hb`:** `(1+t‖ξ‖²)·‖û‖ ∈ L²` for `t ≥ 0`, because
`(1+t‖ξ‖²)·û` is Schwartz (`smulLeftCLM` by the temperate-growth weight `1+t‖ξ‖²`). Mirrors W3-12;
discharges the hypothesis of `integral_norm_le_weighted_L2_t` (W3-24) for any Schwartz `u`. -/
lemma memLp_weighted_fourier_t (u : 𝓢(Space 3, ℂ)) {t : ℝ} (ht : 0 ≤ t) :
    MemLp (fun ξ : Space 3 => ((1 + t * ‖ξ‖ ^ 2) * ‖(𝓕 u) ξ‖ : ℝ)) 2 volume := by
  have hgr : Function.HasTemperateGrowth (fun ξ : Space 3 => (1 + t * ‖ξ‖ ^ 2 : ℝ)) :=
    (Function.HasTemperateGrowth.const (1 : ℝ)).add
      ((Function.HasTemperateGrowth.const t).mul (Function.hasTemperateGrowth_norm_sq (H := Space 3)))
  have hg : Function.HasTemperateGrowth (fun ξ : Space 3 => ((1 + t * ‖ξ‖ ^ 2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.hasTemperateGrowth.comp hgr
  have hmem : MemLp (fun ξ : Space 3 =>
      ‖(SchwartzMap.smulLeftCLM ℂ (fun ξ : Space 3 => ((1 + t * ‖ξ‖ ^ 2 : ℝ) : ℂ)) (𝓕 u)) ξ‖) 2 volume :=
    (SchwartzMap.memLp _ 2 volume).norm
  refine hmem.ae_eq (Filter.Eventually.of_forall fun ξ => ?_)
  rw [SchwartzMap.smulLeftCLM_apply_apply hg, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + t * ‖ξ‖ ^ 2)]

open QuantumMechanics in
/-- **The t-parameterized operator-form sup-norm bound:**
`‖f x‖ ≤ C₀(t)√2·‖f‖₂ + (C₀(t)√2·t/(2πℏ)²)·‖∑pᵢ²f‖₂`, where `C₀(t) = ‖(1+t‖ξ‖²)⁻¹‖₂`. The t-version of
`norm_sup_le_kinetic` (W3-19), composing the t-Hölder (W3-24, hb=W3-25), the t-split (W3-22, h0/h4=W3-17/18),
the free Plancherel, and the momentum-norm identity (W3-16). The kinetic coefficient carries the explicit
factor `t` — combined with `C₀(t)=(√t)^{-3/2}C₀` (W3-21) it is `∝ t^{1/4}`, shrinkable to any `ε` (next). -/
lemma norm_sup_le_kinetic_t (f : 𝓢(Space 3, ℂ)) {t : ℝ} (ht : 0 < t) (x : Space 3) :
    ‖f x‖ ≤ Real.sqrt (∫ ξ : Space 3, (((1 + t * ‖ξ‖ ^ 2)⁻¹ : ℝ)) ^ 2) * Real.sqrt 2
              * Real.sqrt (∫ y : Space 3, ‖f y‖ ^ 2)
          + Real.sqrt (∫ ξ : Space 3, (((1 + t * ‖ξ‖ ^ 2)⁻¹ : ℝ)) ^ 2) * Real.sqrt 2 * t
              / (2 * Real.pi * Constants.ℏ) ^ 2
              * Real.sqrt (∫ y : Space 3, ‖(∑ i, momentumCLM i (momentumCLM i f)) y‖ ^ 2) := by
  have h11 := (norm_le_integral_norm_fourier f x).trans
    (integral_norm_le_weighted_L2_t ht (memLp_weighted_fourier_t f ht.le))
  have h13 := sqrt_weighted_le_t ht (integrable_normSq_fourier f) (integrable_weight4_normSq_fourier f)
  have hpl : Real.sqrt (∫ ξ : Space 3, ‖(𝓕 f) ξ‖ ^ 2) = Real.sqrt (∫ y : Space 3, ‖f y‖ ^ 2) := by
    rw [SchwartzMap.integral_norm_sq_fourier]
  have hmom : Real.sqrt (∫ ξ : Space 3, ‖ξ‖ ^ 4 * ‖(𝓕 f) ξ‖ ^ 2)
      = Real.sqrt (∫ y : Space 3, ‖(∑ i, momentumCLM i (momentumCLM i f)) y‖ ^ 2)
        / (2 * Real.pi * Constants.ℏ) ^ 2 := by
    have hℏ := Constants.ℏ_pos
    rw [eq_div_iff (by positivity : (2 * Real.pi * Constants.ℏ) ^ 2 ≠ 0),
      ← integral_normSq_weight_eq_momentumSq f, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by positivity)]
    ring
  calc ‖f x‖
      ≤ Real.sqrt (∫ ξ : Space 3, (((1 + t * ‖ξ‖ ^ 2)⁻¹ : ℝ)) ^ 2)
          * Real.sqrt (∫ ξ : Space 3, ((1 + t * ‖ξ‖ ^ 2) * ‖(𝓕 f) ξ‖) ^ 2) := h11
    _ ≤ Real.sqrt (∫ ξ : Space 3, (((1 + t * ‖ξ‖ ^ 2)⁻¹ : ℝ)) ^ 2)
          * (Real.sqrt 2 * Real.sqrt (∫ ξ : Space 3, ‖(𝓕 f) ξ‖ ^ 2)
            + Real.sqrt 2 * t * Real.sqrt (∫ ξ : Space 3, ‖ξ‖ ^ 4 * ‖(𝓕 f) ξ‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left h13 (Real.sqrt_nonneg _)
    _ = _ := by rw [hpl, hmom]; ring

/-- **The sup-norm constant `C₀² = ∫((1+‖ξ‖²)⁻¹)²` is strictly positive** — the integrand is everywhere
positive and integrable (W3-2a), and `volume (ℝ³) ≠ 0`. Needed so the ε-trick can divide by `C₀`. -/
lemma integral_weightInv_sq_pos : 0 < ∫ ξ : Space 3, (((1 + ‖ξ‖ ^ 2)⁻¹ : ℝ)) ^ 2 := by
  have hint : Integrable (fun ξ : Space 3 => (((1 + ‖ξ‖ ^ 2)⁻¹ : ℝ)) ^ 2) := by
    have h := memLp_two_oneAddNormSq_inv
    rwa [memLp_two_iff_integrable_sq (Continuous.inv₀ (by fun_prop)
      (fun ξ => (by positivity : (0 : ℝ) < 1 + ‖ξ‖ ^ 2).ne')).aestronglyMeasurable] at h
  rw [integral_pos_iff_support_of_nonneg (fun ξ => by positivity) hint]
  have hsupp : Function.support (fun ξ : Space 3 => (((1 + ‖ξ‖ ^ 2)⁻¹ : ℝ)) ^ 2) = Set.univ :=
    Set.eq_univ_of_forall fun ξ =>
      Function.mem_support.mpr (by positivity : (0 : ℝ) < (((1 + ‖ξ‖ ^ 2)⁻¹ : ℝ)) ^ 2).ne'
  rw [hsupp]
  simp

/-- `‖g‖² ∈ L¹` for any Schwartz `g` (Schwartz ⟹ `MemLp 2`). The L²-integrability of `u` itself that the
Coulomb `L^∞·L²` step (W3-7) consumes. -/
lemma integrable_normSq_schwartz (g : 𝓢(Space 3, ℂ)) :
    Integrable (fun x : Space 3 => ‖g x‖ ^ 2) := by
  have h := (SchwartzMap.memLp g 2 volume).norm
  rw [memLp_two_iff_integrable_sq g.continuous.norm.aestronglyMeasurable] at h
  simpa only [norm_norm] using h

/-- `((1/‖x‖)·1_{‖x‖>1}·‖u‖)² ∈ L¹` — the far-Coulomb·u part, dominated by `‖u‖²` (since `V₂ ≤ 1`,
W3-30). One of the two integrability inputs of the single-electron Coulomb relative bound. -/
lemma integrable_coulombFar_mul_sq (u : 𝓢(Space 3, ℂ)) :
    Integrable (fun x : Space 3 => ((if 1 < ‖x‖ then ‖x‖⁻¹ else 0) * ‖u x‖) ^ 2) := by
  refine (integrable_normSq_schwartz u).mono'
    (Measurable.aestronglyMeasurable (by
      apply Measurable.pow_const
      exact (Measurable.ite (measurableSet_lt measurable_const measurable_norm)
        measurable_norm.inv measurable_const).mul u.continuous.norm.measurable))
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hV2le : (if 1 < ‖x‖ then ‖x‖⁻¹ else 0) ≤ 1 := by
    split_ifs with h
    · exact inv_le_one_of_one_le₀ (le_of_lt h)
    · norm_num
  have hV2nn : 0 ≤ (if 1 < ‖x‖ then ‖x‖⁻¹ else 0) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hV2le (norm_nonneg (u x)),
    mul_nonneg hV2nn (norm_nonneg (u x)), norm_nonneg (u x)]

/-- `((1/‖x‖)·1_{‖x‖≤1}·‖u‖)² ∈ L¹` — the near-Coulomb·u part, dominated by `(seminorm₀₀ u)²·‖x‖⁻²·1_{‖x‖≤1}`
(`SchwartzMap.norm_le_seminorm` + W3-9). The second integrability input of the single-electron Coulomb bound. -/
lemma integrable_coulombNear_mul_sq (u : 𝓢(Space 3, ℂ)) :
    Integrable (fun x : Space 3 => ((if ‖x‖ ≤ 1 then ‖x‖⁻¹ else 0) * ‖u x‖) ^ 2) := by
  have hrec : ∀ x : Space 3, (if ‖x‖ ≤ 1 then ‖x‖⁻¹ else 0) ^ 2
      = if ‖x‖ ≤ 1 then ‖x‖ ^ (-2 : ℝ) else 0 := by
    intro x
    split_ifs with h
    · rcases eq_or_lt_of_le (norm_nonneg x) with hx0 | hx0
      · rw [← hx0]; simp [Real.zero_rpow (show (-2 : ℝ) ≠ 0 by norm_num)]
      · rw [Real.rpow_neg hx0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
          ← inv_pow]
    · ring
  refine (integrable_coulombNear_sq.const_mul (((SchwartzMap.seminorm ℂ 0 0) u) ^ 2)).mono'
    (Measurable.aestronglyMeasurable (by
      apply Measurable.pow_const
      exact (Measurable.ite (measurableSet_le measurable_norm measurable_const)
        measurable_norm.inv measurable_const).mul u.continuous.norm.measurable))
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow, hrec,
    mul_comm (((SchwartzMap.seminorm ℂ 0 0) u) ^ 2) _]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  nlinarith [SchwartzMap.norm_le_seminorm ℂ u x, norm_nonneg (u x), apply_nonneg (SchwartzMap.seminorm ℂ 0 0) u]

/-- **Disjoint-support Coulomb split (L² level):** `∫(‖x‖⁻¹‖u‖)² = ∫(V₁‖u‖)² + ∫(V₂‖u‖)²`, where
`V₁ = ‖x‖⁻¹·1_{‖x‖≤1}`, `V₂ = ‖x‖⁻¹·1_{‖x‖>1}`. The supports `{‖x‖≤1}` and `{‖x‖>1}` are disjoint, so the
cross term vanishes and the additivity is exact (no factor of 2). Integrabilities from W3-31/32. -/
lemma coulomb_integral_split (u : 𝓢(Space 3, ℂ)) :
    ∫ x : Space 3, (‖x‖⁻¹ * ‖u x‖) ^ 2
      = (∫ x : Space 3, ((if ‖x‖ ≤ 1 then ‖x‖⁻¹ else 0) * ‖u x‖) ^ 2)
        + ∫ x : Space 3, ((if 1 < ‖x‖ then ‖x‖⁻¹ else 0) * ‖u x‖) ^ 2 := by
  rw [← integral_add (integrable_coulombNear_mul_sq u) (integrable_coulombFar_mul_sq u)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  by_cases h : ‖x‖ ≤ 1
  · rw [if_pos h, if_neg (not_lt.mpr h)]; ring
  · rw [if_neg h, if_pos (not_le.mp h)]; ring

/-- **The near-Coulomb L² norm is strictly positive:** `0 < ∫ ‖x‖⁻²·1_{‖x‖≤1}` (= `‖V₁‖₂²`). The integrand
is positive on the punctured unit ball (positive volume) and integrable (W3-9). Lets the single-electron
Coulomb relative bound divide by `‖V₁‖₂` when calibrating the ε-trick. -/
lemma integral_coulombNear_sq_pos :
    0 < ∫ x : Space 3, if ‖x‖ ≤ 1 then ‖x‖ ^ (-2 : ℝ) else 0 := by
  rw [integral_pos_iff_support_of_nonneg (fun x => by positivity) integrable_coulombNear_sq]
  refine lt_of_lt_of_le ?_
    (measure_mono (show Metric.ball (0 : Space 3) 1 \ {0} ⊆ _ from ?_))
  · rw [measure_diff_null (measure_singleton 0)]
    exact Metric.measure_ball_pos volume 0 one_pos
  · intro x hx
    rw [Set.mem_diff, Metric.mem_ball, dist_zero_right, Set.mem_singleton_iff] at hx
    rw [Function.mem_support, if_pos (le_of_lt hx.1)]
    exact (Real.rpow_pos_of_pos (norm_pos_iff.mpr hx.2) (-2)).ne'

open QuantumMechanics in
/-- **The ε-form single-particle Kato sup-estimate** (culmination of the ε-trick): for every `ε > 0`,
`‖f x‖ ≤ ε·‖∑pᵢ²f‖₂ + C_ε·‖f‖₂` for some `C_ε ≥ 0` and all `x`. Pick `t = δ⁴`, `δ = ε(2πℏ)²/(C₀√2)`;
then `C₀(δ⁴) = δ⁻³C₀` (W3-21 + `Real.sqrt_sq`) collapses the kinetic coefficient of `norm_sup_le_kinetic_t`
to exactly `ε`. This is the form Kato–Rellich consumes — the kinetic relative bound is arbitrarily small. -/
lemma exists_sup_relbound (f : 𝓢(Space 3, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Space 3,
      ‖f x‖ ≤ ε * Real.sqrt (∫ y : Space 3, ‖(∑ i, momentumCLM i (momentumCLM i f)) y‖ ^ 2)
            + C * Real.sqrt (∫ y : Space 3, ‖f y‖ ^ 2) := by
  have hℏ := Constants.ℏ_pos
  have hC0 : 0 < Real.sqrt (∫ ξ : Space 3, (((1 + ‖ξ‖ ^ 2)⁻¹ : ℝ)) ^ 2) :=
    Real.sqrt_pos.mpr integral_weightInv_sq_pos
  set C₀ := Real.sqrt (∫ ξ : Space 3, (((1 + ‖ξ‖ ^ 2)⁻¹ : ℝ)) ^ 2) with hC0def
  set δ := ε * (2 * Real.pi * Constants.ℏ) ^ 2 / (C₀ * Real.sqrt 2) with hδdef
  have hδ : 0 < δ := by rw [hδdef]; positivity
  refine ⟨(δ ^ 3)⁻¹ * C₀ * Real.sqrt 2, by positivity, fun x => ?_⟩
  have hC0t : Real.sqrt (∫ ξ : Space 3, (((1 + δ ^ 4 * ‖ξ‖ ^ 2)⁻¹ : ℝ)) ^ 2) = (δ ^ 3)⁻¹ * C₀ := by
    rw [integral_weightInv_sq_smul (by positivity : (0 : ℝ) < δ ^ 4),
      show Real.sqrt (δ ^ 4) = δ ^ 2 from by
        rw [show (δ : ℝ) ^ 4 = (δ ^ 2) ^ 2 from by ring, Real.sqrt_sq (by positivity)],
      Real.sqrt_mul (by positivity), ← hC0def, Real.sqrt_inv,
      show ((δ ^ 2) ^ 3 : ℝ) = (δ ^ 3) ^ 2 from by ring, Real.sqrt_sq (by positivity)]
  have h26 := norm_sup_le_kinetic_t f (by positivity : (0 : ℝ) < δ ^ 4) x
  rw [hC0t] at h26
  refine h26.trans (le_of_eq ?_)
  have hkin : (δ ^ 3)⁻¹ * C₀ * Real.sqrt 2 * δ ^ 4 / (2 * Real.pi * Constants.ℏ) ^ 2 = ε := by
    rw [show (δ ^ 3)⁻¹ * C₀ * Real.sqrt 2 * δ ^ 4
          = (δ ^ 3)⁻¹ * δ ^ 4 * (C₀ * Real.sqrt 2) from by ring,
      show (δ ^ 3)⁻¹ * δ ^ 4 = δ from by field_simp, hδdef]
    field_simp
  rw [hkin]; ring

open QuantumMechanics in
/-- **Uniform-`C` sup-estimate.** The same ε-Kato sup bound as `exists_sup_relbound`, but with the constant
`C` chosen *before* (hence independent of) the Schwartz function `f` — `C = (δ³)⁻¹C₀√2` depends only on `ε`
and the fixed constants `C₀`, `ℏ`. This uniformity is essential for the molecular lift's params-integration:
the fiberwise bound's constant must not vary with the fiber. -/
lemma exists_sup_relbound_uniform {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : 𝓢(Space 3, ℂ)) (x : Space 3),
      ‖f x‖ ≤ ε * Real.sqrt (∫ y : Space 3, ‖(∑ i, momentumCLM i (momentumCLM i f)) y‖ ^ 2)
            + C * Real.sqrt (∫ y : Space 3, ‖f y‖ ^ 2) := by
  have hℏ := Constants.ℏ_pos
  have hC0 : 0 < Real.sqrt (∫ ξ : Space 3, (((1 + ‖ξ‖ ^ 2)⁻¹ : ℝ)) ^ 2) :=
    Real.sqrt_pos.mpr integral_weightInv_sq_pos
  set C₀ := Real.sqrt (∫ ξ : Space 3, (((1 + ‖ξ‖ ^ 2)⁻¹ : ℝ)) ^ 2) with hC0def
  set δ := ε * (2 * Real.pi * Constants.ℏ) ^ 2 / (C₀ * Real.sqrt 2) with hδdef
  have hδ : 0 < δ := by rw [hδdef]; positivity
  refine ⟨(δ ^ 3)⁻¹ * C₀ * Real.sqrt 2, by positivity, fun f x => ?_⟩
  have hC0t : Real.sqrt (∫ ξ : Space 3, (((1 + δ ^ 4 * ‖ξ‖ ^ 2)⁻¹ : ℝ)) ^ 2) = (δ ^ 3)⁻¹ * C₀ := by
    rw [integral_weightInv_sq_smul (by positivity : (0 : ℝ) < δ ^ 4),
      show Real.sqrt (δ ^ 4) = δ ^ 2 from by
        rw [show (δ : ℝ) ^ 4 = (δ ^ 2) ^ 2 from by ring, Real.sqrt_sq (by positivity)],
      Real.sqrt_mul (by positivity), ← hC0def, Real.sqrt_inv,
      show ((δ ^ 2) ^ 3 : ℝ) = (δ ^ 3) ^ 2 from by ring, Real.sqrt_sq (by positivity)]
  have h26 := norm_sup_le_kinetic_t f (by positivity : (0 : ℝ) < δ ^ 4) x
  rw [hC0t] at h26
  refine h26.trans (le_of_eq ?_)
  have hkin : (δ ^ 3)⁻¹ * C₀ * Real.sqrt 2 * δ ^ 4 / (2 * Real.pi * Constants.ℏ) ^ 2 = ε := by
    rw [show (δ ^ 3)⁻¹ * C₀ * Real.sqrt 2 * δ ^ 4
          = (δ ^ 3)⁻¹ * δ ^ 4 * (C₀ * Real.sqrt 2) from by ring,
      show (δ ^ 3)⁻¹ * δ ^ 4 = δ from by field_simp, hδdef]
    field_simp
  rw [hkin]; ring

open QuantumMechanics in
/-- **The single-electron Coulomb relative bound** (3D model of each molecular Coulomb term): for every
`ε > 0`, `‖(1/‖x‖)·u‖₂ ≤ ε·‖∑pᵢ²u‖₂ + C·‖u‖₂`. Split `1/‖x‖ = V₁+V₂` (disjoint, W3-33), bound the near part
`‖V₁u‖₂ ≤ ‖V₁‖₂·‖u‖_∞` (W3-6) with `‖u‖_∞ ≤ ε'·K + C'·L` from the ε-sup-estimate (W3-28), the far part
`‖V₂u‖₂ ≤ ‖u‖₂` (W3-7, `V₂≤1`); calibrate `ε' = ε/‖V₁‖₂` (W3-29). -/
lemma exists_coulomb_relbound (u : 𝓢(Space 3, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      Real.sqrt (∫ x : Space 3, (‖x‖⁻¹ * ‖u x‖) ^ 2)
        ≤ ε * Real.sqrt (∫ y : Space 3, ‖(∑ i, momentumCLM i (momentumCLM i u)) y‖ ^ 2)
          + C * Real.sqrt (∫ y : Space 3, ‖u y‖ ^ 2) := by
  have hsub : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
    intro a b ha hb
    have h := Real.sqrt_le_sqrt (show a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 by
      nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb,
        mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)])
    rwa [Real.sqrt_sq (by positivity)] at h
  have hrec : ∀ x : Space 3, (if ‖x‖ ≤ 1 then ‖x‖⁻¹ else 0) ^ 2
      = if ‖x‖ ≤ 1 then ‖x‖ ^ (-2 : ℝ) else 0 := by
    intro x
    split_ifs with h
    · rcases eq_or_lt_of_le (norm_nonneg x) with hx0 | hx0
      · rw [← hx0]; simp [Real.zero_rpow (show (-2 : ℝ) ≠ 0 by norm_num)]
      · rw [Real.rpow_neg hx0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
          ← inv_pow]
    · ring
  set nV1 := Real.sqrt (∫ x : Space 3, if ‖x‖ ≤ 1 then ‖x‖ ^ (-2 : ℝ) else 0) with hnV1def
  have hnV1 : 0 < nV1 := Real.sqrt_pos.mpr integral_coulombNear_sq_pos
  set K := Real.sqrt (∫ y : Space 3, ‖(∑ i, momentumCLM i (momentumCLM i u)) y‖ ^ 2)
  set L := Real.sqrt (∫ y : Space 3, ‖u y‖ ^ 2)
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  have hL0 : 0 ≤ L := Real.sqrt_nonneg _
  obtain ⟨C', hC'0, hsup⟩ := exists_sup_relbound u (show (0 : ℝ) < ε / nV1 by positivity)
  refine ⟨C' * nV1 + 1, by positivity, ?_⟩
  set M := ε / nV1 * K + C' * L with hMdef
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  have hV1 : ∫ x : Space 3, ((if ‖x‖ ≤ 1 then ‖x‖⁻¹ else 0) * ‖u x‖) ^ 2 ≤ M ^ 2 * nV1 ^ 2 := by
    have h6 := integral_mul_sq_le_sup_sq_mul (M := M)
      (V := fun x => if ‖x‖ ≤ 1 then ‖x‖⁻¹ else 0) (u := fun x => ‖u x‖)
      (fun x => by rw [abs_of_nonneg (norm_nonneg _)]; exact hsup x)
      (integrable_coulombNear_sq.congr (Filter.Eventually.of_forall fun x => (hrec x).symm))
    have hint : ∫ x : Space 3, (if ‖x‖ ≤ 1 then ‖x‖⁻¹ else 0) ^ 2 = nV1 ^ 2 := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hrec), hnV1def,
        Real.sq_sqrt (le_of_lt integral_coulombNear_sq_pos)]
    rwa [hint] at h6
  have hV2 : ∫ x : Space 3, ((if 1 < ‖x‖ then ‖x‖⁻¹ else 0) * ‖u x‖) ^ 2
      ≤ ∫ y : Space 3, ‖u y‖ ^ 2 := by
    refine integral_bdd_mul_sq_le (fun x => by positivity) (fun x => ?_) (integrable_normSq_schwartz u)
    split_ifs with h
    · exact inv_le_one_of_one_le₀ (le_of_lt h)
    · norm_num
  rw [coulomb_integral_split u]
  refine (hsub _ _ (integral_nonneg fun x => sq_nonneg _)
    (integral_nonneg fun x => sq_nonneg _)).trans ?_
  have hb1 : Real.sqrt (∫ x : Space 3, ((if ‖x‖ ≤ 1 then ‖x‖⁻¹ else 0) * ‖u x‖) ^ 2) ≤ M * nV1 :=
    (Real.sqrt_le_sqrt hV1).trans_eq (by
      rw [show M ^ 2 * nV1 ^ 2 = (M * nV1) ^ 2 from by ring, Real.sqrt_sq (by positivity)])
  have hb2 : Real.sqrt (∫ x : Space 3, ((if 1 < ‖x‖ then ‖x‖⁻¹ else 0) * ‖u x‖) ^ 2) ≤ L :=
    Real.sqrt_le_sqrt hV2
  refine (add_le_add hb1 hb2).trans_eq ?_
  rw [hMdef]; field_simp; ring

open QuantumMechanics in
/-- **Uniform-`C` single-electron Coulomb relative bound.** As `exists_coulomb_relbound`, but `C` is chosen
*before* the Schwartz function `u` — `C = C'·nV1 + 1` with `nV1` the Coulomb near-part L² norm and `C'` the
uniform sup-estimate constant, both `u`-independent. This is the form the molecular lift consumes: the
fiberwise bound must hold with one `C` across all fibers `ũ_z` so the params-integration (Minkowski over `z`)
goes through. -/
lemma exists_coulomb_relbound_uniform {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : 𝓢(Space 3, ℂ),
      Real.sqrt (∫ x : Space 3, (‖x‖⁻¹ * ‖u x‖) ^ 2)
        ≤ ε * Real.sqrt (∫ y : Space 3, ‖(∑ i, momentumCLM i (momentumCLM i u)) y‖ ^ 2)
          + C * Real.sqrt (∫ y : Space 3, ‖u y‖ ^ 2) := by
  have hsub : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
    intro a b ha hb
    have h := Real.sqrt_le_sqrt (show a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 by
      nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb,
        mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)])
    rwa [Real.sqrt_sq (by positivity)] at h
  have hrec : ∀ x : Space 3, (if ‖x‖ ≤ 1 then ‖x‖⁻¹ else 0) ^ 2
      = if ‖x‖ ≤ 1 then ‖x‖ ^ (-2 : ℝ) else 0 := by
    intro x
    split_ifs with h
    · rcases eq_or_lt_of_le (norm_nonneg x) with hx0 | hx0
      · rw [← hx0]; simp [Real.zero_rpow (show (-2 : ℝ) ≠ 0 by norm_num)]
      · rw [Real.rpow_neg hx0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
          ← inv_pow]
    · ring
  set nV1 := Real.sqrt (∫ x : Space 3, if ‖x‖ ≤ 1 then ‖x‖ ^ (-2 : ℝ) else 0) with hnV1def
  have hnV1 : 0 < nV1 := Real.sqrt_pos.mpr integral_coulombNear_sq_pos
  obtain ⟨C', hC'0, hsupU⟩ := exists_sup_relbound_uniform (show (0 : ℝ) < ε / nV1 by positivity)
  refine ⟨C' * nV1 + 1, by positivity, fun u => ?_⟩
  set K := Real.sqrt (∫ y : Space 3, ‖(∑ i, momentumCLM i (momentumCLM i u)) y‖ ^ 2)
  set L := Real.sqrt (∫ y : Space 3, ‖u y‖ ^ 2)
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  have hL0 : 0 ≤ L := Real.sqrt_nonneg _
  have hsup := hsupU u
  set M := ε / nV1 * K + C' * L with hMdef
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  have hV1 : ∫ x : Space 3, ((if ‖x‖ ≤ 1 then ‖x‖⁻¹ else 0) * ‖u x‖) ^ 2 ≤ M ^ 2 * nV1 ^ 2 := by
    have h6 := integral_mul_sq_le_sup_sq_mul (M := M)
      (V := fun x => if ‖x‖ ≤ 1 then ‖x‖⁻¹ else 0) (u := fun x => ‖u x‖)
      (fun x => by rw [abs_of_nonneg (norm_nonneg _)]; exact hsup x)
      (integrable_coulombNear_sq.congr (Filter.Eventually.of_forall fun x => (hrec x).symm))
    have hint : ∫ x : Space 3, (if ‖x‖ ≤ 1 then ‖x‖⁻¹ else 0) ^ 2 = nV1 ^ 2 := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hrec), hnV1def,
        Real.sq_sqrt (le_of_lt integral_coulombNear_sq_pos)]
    rwa [hint] at h6
  have hV2 : ∫ x : Space 3, ((if 1 < ‖x‖ then ‖x‖⁻¹ else 0) * ‖u x‖) ^ 2
      ≤ ∫ y : Space 3, ‖u y‖ ^ 2 := by
    refine integral_bdd_mul_sq_le (fun x => by positivity) (fun x => ?_) (integrable_normSq_schwartz u)
    split_ifs with h
    · exact inv_le_one_of_one_le₀ (le_of_lt h)
    · norm_num
  rw [coulomb_integral_split u]
  refine (hsub _ _ (integral_nonneg fun x => sq_nonneg _)
    (integral_nonneg fun x => sq_nonneg _)).trans ?_
  have hb1 : Real.sqrt (∫ x : Space 3, ((if ‖x‖ ≤ 1 then ‖x‖⁻¹ else 0) * ‖u x‖) ^ 2) ≤ M * nV1 :=
    (Real.sqrt_le_sqrt hV1).trans_eq (by
      rw [show M ^ 2 * nV1 ^ 2 = (M * nV1) ^ 2 from by ring, Real.sqrt_sq (by positivity)])
  have hb2 : Real.sqrt (∫ x : Space 3, ((if 1 < ‖x‖ then ‖x‖⁻¹ else 0) * ‖u x‖) ^ 2) ≤ L :=
    Real.sqrt_le_sqrt hV2
  refine (add_le_add hb1 hb2).trans_eq ?_
  rw [hMdef]; field_simp; ring

/-- **`electronPos` is additive** — the projection onto electron `i`'s 3 coordinates is linear. Foundational
for the coordinate-split machinery of the molecular lift (`Space(3N) ≃ Space 3 × Space(3(N-1))`). -/
lemma electronPos_add {N : ℕ} (x y : Space (3 * N)) (i : Fin N) :
    electronPos (x + y) i = electronPos x i + electronPos y i := by
  ext j
  simp [electronPos]

/-- **`electronPos` is homogeneous** — companion of `electronPos_add`. -/
lemma electronPos_smul {N : ℕ} (c : ℝ) (x : Space (3 * N)) (i : Fin N) :
    electronPos (c • x) i = c • electronPos x i := by
  ext j
  simp [electronPos]

/-- **`electronPos` as a continuous linear map** `Space(3N) →L[ℝ] Space 3` — bundling the linearity
(`electronPos_add`/`electronPos_smul`) with the continuity (`electronPos_continuous`). The projection onto
electron `i`'s coordinates; the coordinate-split equiv of the molecular lift is built from it. -/
noncomputable def electronPosCLM {N : ℕ} (i : Fin N) : Space (3 * N) →L[ℝ] Space 3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => electronPos x i
      map_add' := fun x y => electronPos_add x y i
      map_smul' := fun c x => electronPos_smul c x i }

@[simp] lemma electronPosCLM_apply {N : ℕ} (i : Fin N) (x : Space (3 * N)) :
    electronPosCLM i x = electronPos x i := rfl

/-- The **relative position** `electronPos x i - electronPos x j` as a continuous linear map — the singular
coordinate of the electron–electron repulsion term `1/‖eᵢ - eⱼ‖`. Difference of the two projection CLMs. -/
noncomputable def electronRelCLM {N : ℕ} (i j : Fin N) : Space (3 * N) →L[ℝ] Space 3 :=
  electronPosCLM i - electronPosCLM j

@[simp] lemma electronRelCLM_apply {N : ℕ} (i j : Fin N) (x : Space (3 * N)) :
    electronRelCLM i j x = electronPos x i - electronPos x j := by
  simp [electronRelCLM]

open QuantumMechanics in
/-- **Pointwise triangle bound for the molecular Coulomb potential:** `|V_mol(x)|` is bounded by the sum of
the absolute values of all nuclear-attraction and electron-repulsion terms. Reduces the molecular relative
bound to the per-term single-electron Coulomb bound (W3-34, lifted to 3N by the slice-Fubini). -/
lemma molecularCoulombPotential_abs_le {N : ℕ} (nuclei : Finset (Space 3 × ℝ)) (x : Space (3 * N)) :
    |molecularCoulombPotential nuclei x|
      ≤ (∑ i : Fin N, ∑ p ∈ nuclei, |p.2| / ‖electronPos x i - p.1‖)
        + ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (i < ·), 1 / ‖electronPos x i - electronPos x j‖ := by
  unfold molecularCoulombPotential
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_neg]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    rw [abs_div, abs_of_nonneg (norm_nonneg _)]
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_of_nonneg (by positivity)]

/-- A single electron-nucleus Coulomb term `x ↦ ‖electronPos x i - R‖⁻¹` is measurable (continuous away
from the singularity; `electronPos_continuous` + `norm` + measurable `inv`). Foundational for the per-term
`L²` integral in the molecular lift. -/
lemma coulombTerm_measurable {N : ℕ} (i : Fin N) (R : Space 3) :
    Measurable (fun x : Space (3 * N) => ‖electronPos x i - R‖⁻¹) :=
  (((electronPos_continuous i).sub continuous_const).norm).measurable.inv

/-- A single electron-electron Coulomb term `x ↦ ‖electronPos x i - electronPos x j‖⁻¹` is measurable. -/
lemma coulombTermRel_measurable {N : ℕ} (i j : Fin N) :
    Measurable (fun x : Space (3 * N) => ‖electronPos x i - electronPos x j‖⁻¹) :=
  (((electronPos_continuous i).sub (electronPos_continuous j)).norm).measurable.inv

/-- The squared electron-nucleus Coulomb-term·`u` integrand `(‖eᵢ-R‖⁻¹·‖u‖)²` is measurable — the per-term
`L²` integrand of the molecular lift. -/
lemma coulombTerm_mul_sq_measurable {N : ℕ} (i : Fin N) (R : Space 3) {u : Space (3 * N) → ℂ}
    (hu : Continuous u) :
    Measurable (fun x : Space (3 * N) => (‖electronPos x i - R‖⁻¹ * ‖u x‖) ^ 2) :=
  ((coulombTerm_measurable i R).mul hu.norm.measurable).pow_const 2

/-- **`Space d ↔ EuclideanSpace ℝ (Fin d)` is measure-preserving** via the orthonormal-basis isometry
`Space.basis.repr` (a `LinearIsometryEquiv`, hence volume-preserving). This is the bridge that lets the
molecular lift reuse Mathlib's full `EuclideanSpace` coordinate-split + Fubini machinery
(`volume_preserving_piEquivPiSubtypeProd`) on `Space (3N)`. -/
lemma basis_repr_measurePreserving {d : ℕ} :
    MeasureTheory.MeasurePreserving (Space.basis (d := d)).repr
      (volume : MeasureTheory.Measure (Space d))
      (volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) :=
  (Space.basis (d := d)).repr.measurePreserving

/-- **`Space d ↔ (Fin d → ℝ)` is measure-preserving** — composing the `Space ↔ EuclideanSpace` bridge
(`basis_repr_measurePreserving`) with Mathlib's `EuclideanSpace ↔ Pi` (`volume_preserving_measurableEquiv`).
Puts `Space (3N)` at the `Pi` level where `volume_preserving_piEquivPiSubtypeProd` isolates electron `i`'s
coordinate block — the start of the L²-Fubini for the molecular lift. -/
lemma space_pi_measurePreserving {d : ℕ} :
    MeasureTheory.MeasurePreserving
      (fun x : Space d => (EuclideanSpace.measurableEquiv (Fin d)) ((Space.basis (d := d)).repr x))
      (volume : MeasureTheory.Measure (Space d)) (volume : MeasureTheory.Measure (Fin d → ℝ)) :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).comp basis_repr_measurePreserving

/-- **Electron `i` owns coordinate `k`** iff `k.val / 3 = i.val` — i.e. `k ∈ {3i, 3i+1, 3i+2}`, exactly the
three coordinates `electronPos x i` reads (`x.val ⟨3*i+j, _⟩`, `j : Fin 3`). The decidable predicate that
drives the measure-preserving coordinate split for the molecular L²-Fubini. -/
def electronCoord {N : ℕ} (i : Fin N) (k : Fin (3 * N)) : Prop := k.val / 3 = i.val

instance {N : ℕ} (i : Fin N) : DecidablePred (electronCoord i) := fun k => by
  unfold electronCoord; infer_instance

/-- **Measure-preserving split of `Space (3N)` isolating electron `i`'s coordinate block.** Composes the
`Space (3N) ↔ (Fin (3N) → ℝ)` bridge (`space_pi_measurePreserving`) with Mathlib's
`volume_preserving_piEquivPiSubtypeProd` over the predicate `electronCoord i`, landing in
`(electron-i's 3 coords → ℝ) × (the other 3N−3 coords → ℝ)` — both with their own volume. This is the
measure-theoretic foundation of the L²-Fubini that lifts the single-electron bound (`exists_coulomb_relbound`)
to each molecular Coulomb term: integrate the spectator coordinates out, apply the 3D bound on electron `i`'s
fiber. -/
lemma electron_split_measurePreserving {N : ℕ} (i : Fin N) :
    MeasureTheory.MeasurePreserving
      (fun x : Space (3 * N) =>
        (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin (3 * N) => ℝ) (electronCoord i))
          ((EuclideanSpace.measurableEquiv (Fin (3 * N))) ((Space.basis (d := 3 * N)).repr x)))
      (volume : MeasureTheory.Measure (Space (3 * N)))
      (volume : MeasureTheory.Measure
        ((∀ _ : {k // electronCoord i k}, ℝ) × (∀ _ : {k // ¬ electronCoord i k}, ℝ))) :=
  (volume_preserving_piEquivPiSubtypeProd (fun _ : Fin (3 * N) => ℝ) (electronCoord i)).comp
    space_pi_measurePreserving

/-- **Electron `i`'s 3-coordinate block is canonically `Fin 3`.** The bijection `j ↦ 3i+j` (inverse
`k ↦ k % 3`) identifies `{k : Fin (3N) // k/3 = i}` with `Fin 3` — the reassembly that makes the fiber
`Space 3`-shaped, so the single-electron Coulomb bound (`exists_coulomb_relbound`) applies to electron `i`'s
coordinates inside the molecular L²-Fubini. -/
def electronCoordEquiv {N : ℕ} (i : Fin N) : {k : Fin (3 * N) // electronCoord i k} ≃ Fin 3 where
  toFun k := ⟨k.1.val % 3, Nat.mod_lt _ (by norm_num)⟩
  invFun j := ⟨⟨3 * i.val + j.val, by have hj := j.isLt; have hi := i.isLt; omega⟩, by
    have hj := j.isLt; show (3 * i.val + j.val) / 3 = i.val; omega⟩
  left_inv := by
    rintro ⟨⟨k, hk⟩, hik⟩
    simp only [electronCoord] at hik
    apply Subtype.ext; apply Fin.ext
    show 3 * i.val + k % 3 = k
    omega
  right_inv := by
    intro j
    apply Fin.ext
    have hj := j.isLt
    show (3 * i.val + j.val) % 3 = j.val
    omega

/-- **The block-coordinate function space is measure-preservingly `Fin 3 → ℝ`.** Lifts `electronCoordEquiv`
through `volume_measurePreserving_piCongrLeft`: `(Fin 3 → ℝ) ≃ᵐ ({k // electronCoord i k} → ℝ)`, volume to
volume. Composed with `space_pi_measurePreserving` (at `d = 3`) this gives electron `i`'s fiber as a
`Space 3`, the home of `exists_coulomb_relbound`. -/
lemma electronBlock_piCongr_measurePreserving {N : ℕ} (i : Fin N) :
    MeasureTheory.MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : {k // electronCoord i k} => ℝ) (electronCoordEquiv i).symm)
      (volume : MeasureTheory.Measure (Fin 3 → ℝ))
      (volume : MeasureTheory.Measure ({k // electronCoord i k} → ℝ)) :=
  volume_measurePreserving_piCongrLeft (fun _ : {k // electronCoord i k} => ℝ) (electronCoordEquiv i).symm

/-- **Electron `i`'s block function-space is measure-preservingly `Space 3`.** Chains the reversed pi-congr
(`electronBlock_piCongr_measurePreserving`, `BlockPi → Fin 3 → ℝ`), the reversed Euclidean↔Pi
(`EuclideanSpace.measurableEquiv (Fin 3)`), and the reversed orthonormal-basis isometry
(`Space.basis.repr.symm`) into one measure-preserving map `({k // electronCoord i k} → ℝ) → Space 3`. This
is what transports the inner (block) Fubini integral onto `Space 3`, the domain of the single-electron
Coulomb bound `exists_coulomb_relbound`. -/
lemma block_pi_measurePreserving_space3 {N : ℕ} (i : Fin N) :
    MeasureTheory.MeasurePreserving
      (fun b : {k // electronCoord i k} → ℝ =>
        (Space.basis (d := 3)).repr.symm
          ((EuclideanSpace.measurableEquiv (Fin 3)).symm
            ((MeasurableEquiv.piCongrLeft (fun _ : {k // electronCoord i k} => ℝ)
                (electronCoordEquiv i).symm).symm b)))
      (volume : MeasureTheory.Measure ({k // electronCoord i k} → ℝ))
      (volume : MeasureTheory.Measure (Space 3)) :=
  (((Space.basis (d := 3)).repr.symm.measurePreserving).comp
      (MeasureTheory.MeasurePreserving.symm (EuclideanSpace.measurableEquiv (Fin 3))
        (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)))).comp
    (MeasureTheory.MeasurePreserving.symm
      (MeasurableEquiv.piCongrLeft (fun _ : {k // electronCoord i k} => ℝ) (electronCoordEquiv i).symm)
      (electronBlock_piCongr_measurePreserving i))

/-- **The molecular coordinate-split map** `Space (3N) → Space 3 × (spectator coords)`: first split off
electron `i`'s block (`electron_split_measurePreserving`), then identify the block with `Space 3`
(`block_pi_measurePreserving_space3`), leaving the other `3N−3` coordinates as the spectator factor. -/
noncomputable def molecularSplitMap {N : ℕ} (i : Fin N) :
    Space (3 * N) → Space 3 × ({k // ¬ electronCoord i k} → ℝ) :=
  Prod.map
    (fun b : {k // electronCoord i k} → ℝ =>
      (Space.basis (d := 3)).repr.symm
        ((EuclideanSpace.measurableEquiv (Fin 3)).symm
          ((MeasurableEquiv.piCongrLeft (fun _ : {k // electronCoord i k} => ℝ)
              (electronCoordEquiv i).symm).symm b)))
    id
  ∘ (fun x : Space (3 * N) =>
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin (3 * N) => ℝ) (electronCoord i))
        ((EuclideanSpace.measurableEquiv (Fin (3 * N))) ((Space.basis (d := 3 * N)).repr x)))

/-- **`molecularSplitMap` is measure-preserving** onto the product `volume (Space 3) ⊗ volume (spectator)`.
Composes the electron-`i` split (W3-45) with the block↔`Space 3` transport (W3-48) on the first factor and
the identity on the spectator factor (`MeasurePreserving.prod`), after rewriting the split's codomain
`volume (BlockPi × SpecPi)` as the product measure (`volume_eq_prod`). This is the change-of-variables that
turns the molecular L² integral of a Coulomb term into a `Space 3 × spectator` product integral, ready for
Fubini (`integral_prod`) + the fiberwise single-electron bound `exists_coulomb_relbound`. -/
lemma molecularSplit_measurePreserving {N : ℕ} (i : Fin N) :
    MeasureTheory.MeasurePreserving (molecularSplitMap i)
      (volume : MeasureTheory.Measure (Space (3 * N)))
      ((volume : MeasureTheory.Measure (Space 3)).prod
        (volume : MeasureTheory.Measure ({k // ¬ electronCoord i k} → ℝ))) := by
  have hsplit := electron_split_measurePreserving i
  rw [Measure.volume_eq_prod] at hsplit
  exact ((block_pi_measurePreserving_space3 i).prod (MeasureTheory.MeasurePreserving.id _)).comp hsplit

/-- **Fubini through the molecular split.** For any measurable `G : Space 3 × (spectator) → ℝ≥0∞`, the
molecular `Space (3N)` lower integral of `G ∘ molecularSplitMap` is the iterated integral with electron
`i`'s block (`Space 3`) on the inside and the spectator coordinates on the outside. Composes the
measure-preserving change of variables (`molecularSplit_measurePreserving`, `lintegral_comp`) with Tonelli
(`lintegral_prod_symm`). This is the reusable identity that reduces a molecular Coulomb-term `L²` integral
to `∫_spectator (∫_{Space 3} …)`, where the inner integral is exactly the single-electron bound's left side. -/
lemma molecularSplit_lintegral {N : ℕ} (i : Fin N)
    (G : Space 3 × ({k // ¬ electronCoord i k} → ℝ) → ENNReal) (hG : Measurable G) :
    ∫⁻ x, G (molecularSplitMap i x) ∂(volume : MeasureTheory.Measure (Space (3 * N)))
      = ∫⁻ z, ∫⁻ y, G (y, z) ∂(volume : MeasureTheory.Measure (Space 3))
          ∂(volume : MeasureTheory.Measure ({k // ¬ electronCoord i k} → ℝ)) := by
  rw [(molecularSplit_measurePreserving i).lintegral_comp hG]
  exact lintegral_prod_symm G hG.aemeasurable

/-- **The molecular coordinate split as a measurable equivalence** `Space (3N) ≃ᵐ Space 3 × (spectator)`.
The same composition as `molecularSplitMap` packaged as a `MeasurableEquiv`, so it carries `.symm`
(needed to express `u x` as a function of the split image in the integrand factorization) and the round-trip
identities. -/
noncomputable def molecularSplitEquiv {N : ℕ} (i : Fin N) :
    Space (3 * N) ≃ᵐ Space 3 × ({k // ¬ electronCoord i k} → ℝ) :=
  (((Space.basis (d := 3 * N)).repr.toHomeomorph.toMeasurableEquiv.trans
      (EuclideanSpace.measurableEquiv (Fin (3 * N)))).trans
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin (3 * N) => ℝ) (electronCoord i))).trans
    (MeasurableEquiv.prodCongr
      (((MeasurableEquiv.piCongrLeft (fun _ : {k // electronCoord i k} => ℝ)
            (electronCoordEquiv i).symm).symm.trans
          (EuclideanSpace.measurableEquiv (Fin 3)).symm).trans
        (Space.basis (d := 3)).repr.toHomeomorph.toMeasurableEquiv.symm)
      (MeasurableEquiv.refl ({k // ¬ electronCoord i k} → ℝ)))

/-- `molecularSplitEquiv` and `molecularSplitMap` are the same map. -/
lemma coe_molecularSplitEquiv {N : ℕ} (i : Fin N) :
    ⇑(molecularSplitEquiv i) = molecularSplitMap i := rfl

/-- **The split's `Space 3` factor IS electron `i`'s position.** The first component of the molecular split
reads exactly electron `i`'s three coordinates — so a Coulomb term `‖electronPos x i − R‖⁻¹` depends only on
the block factor, and the inner `∫⁻_{Space 3}` of `molecularSplit_lintegral` is a genuine single-electron
integral. -/
lemma molecularSplitMap_fst {N : ℕ} (i : Fin N) (x : Space (3 * N)) :
    (molecularSplitMap i x).1 = electronPos x i := by
  ext j
  rfl

/-- **Per-term molecular Coulomb L² identity (Tonelli form).** The molecular `L²` lower integral of a single
nuclear Coulomb term `‖electronPos x i − R‖⁻¹ · ‖u x‖` equals the iterated integral whose inner `Space 3`
integral is a genuine single-electron Coulomb integral `‖y − R‖⁻¹ · ‖ũ_z(y)‖` over the fiber
`ũ_z(y) = u ((molecularSplitEquiv i).symm (y, z))`. Combines the Fubini-through-the-split
(`molecularSplit_lintegral`), the block-factor identity (`molecularSplitMap_fst`), and the equiv round-trip. -/
lemma molecular_coulombTerm_lintegral {N : ℕ} (i : Fin N) (R : Space 3)
    {u : Space (3 * N) → ℂ} (hu : Measurable u) :
    ∫⁻ x, (ENNReal.ofReal (‖electronPos x i - R‖⁻¹ * ‖u x‖)) ^ 2
        ∂(volume : MeasureTheory.Measure (Space (3 * N)))
      = ∫⁻ z, ∫⁻ y, (ENNReal.ofReal (‖y - R‖⁻¹ * ‖u ((molecularSplitEquiv i).symm (y, z))‖)) ^ 2
          ∂(volume : MeasureTheory.Measure (Space 3))
          ∂(volume : MeasureTheory.Measure ({k // ¬ electronCoord i k} → ℝ)) := by
  have hG : Measurable (fun p : Space 3 × ({k // ¬ electronCoord i k} → ℝ) =>
      (ENNReal.ofReal (‖p.1 - R‖⁻¹ * ‖u ((molecularSplitEquiv i).symm p)‖)) ^ 2) := by
    refine (ENNReal.measurable_ofReal.comp (Measurable.mul ?_ ?_)).pow_const 2
    · exact (measurable_fst.sub measurable_const).norm.inv
    · exact (hu.comp (molecularSplitEquiv i).symm.measurable).norm
  have hpt : (fun x => (ENNReal.ofReal (‖electronPos x i - R‖⁻¹ * ‖u x‖)) ^ 2)
      = (fun x => (ENNReal.ofReal (‖(molecularSplitMap i x).1 - R‖⁻¹
          * ‖u ((molecularSplitEquiv i).symm (molecularSplitMap i x))‖)) ^ 2) := by
    funext x
    rw [molecularSplitMap_fst, ← coe_molecularSplitEquiv, MeasurableEquiv.symm_apply_apply]
  rw [hpt]
  exact molecularSplit_lintegral i _ hG

end SKEFTHawking.DFT
