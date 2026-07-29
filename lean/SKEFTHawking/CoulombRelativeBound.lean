import SKEFTHawking.MolecularHamiltonian
import SKEFTHawking.KineticEssentialSelfAdjoint
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Physlib.QuantumMechanics.Operators.Commutation

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
    rw [fourier_momentumSq, smul_apply, SchwartzMap.smulLeftCLM_apply_apply hg2, smul_smul,
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
    have hcont : Continuous (fun ξ : Space 3 => ((1 + ‖ξ‖ ^ 2)⁻¹ : ℝ)) :=
      Continuous.inv₀ (by fun_prop) (fun ξ => (by positivity : (0 : ℝ) < 1 + ‖ξ‖ ^ 2).ne')
    have h := memLp_two_oneAddNormSq_inv
    rwa [memLp_two_iff_integrable_sq hcont.aestronglyMeasurable] at h
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
  · rw [measure_sdiff_null (measure_singleton 0)]
    exact Metric.measure_ball_pos volume 0 one_pos
  · intro x hx
    rw [Set.mem_sdiff, Metric.mem_ball, dist_zero_right, Set.mem_singleton_iff] at hx
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
(`basis_repr_measurePreserving`) with Mathlib's `EuclideanSpace ↔ Pi`
(`EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp`).
Puts `Space (3N)` at the `Pi` level where `volume_preserving_piEquivPiSubtypeProd` isolates electron `i`'s
coordinate block — the start of the L²-Fubini for the molecular lift. -/
lemma space_pi_measurePreserving {d : ℕ} :
    MeasureTheory.MeasurePreserving
      (fun x : Space d =>
        (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm ((Space.basis (d := d)).repr x))
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
          (((MeasurableEquiv.toLp 2 (Fin (3 * N) → ℝ)).symm) ((Space.basis (d := 3 * N)).repr x)))
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
(`MeasurableEquiv.toLp 2 (Fin 3 → ℝ)`), and the reversed orthonormal-basis isometry
(`Space.basis.repr.symm`) into one measure-preserving map `({k // electronCoord i k} → ℝ) → Space 3`. This
is what transports the inner (block) Fubini integral onto `Space 3`, the domain of the single-electron
Coulomb bound `exists_coulomb_relbound`. -/
lemma block_pi_measurePreserving_space3 {N : ℕ} (i : Fin N) :
    MeasureTheory.MeasurePreserving
      (fun b : {k // electronCoord i k} → ℝ =>
        (Space.basis (d := 3)).repr.symm
          ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
            ((MeasurableEquiv.piCongrLeft (fun _ : {k // electronCoord i k} => ℝ)
                (electronCoordEquiv i).symm).symm b)))
      (volume : MeasureTheory.Measure ({k // electronCoord i k} → ℝ))
      (volume : MeasureTheory.Measure (Space 3)) :=
  (((Space.basis (d := 3)).repr.symm.measurePreserving).comp
      (MeasureTheory.MeasurePreserving.symm ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm)
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
        ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
          ((MeasurableEquiv.piCongrLeft (fun _ : {k // electronCoord i k} => ℝ)
              (electronCoordEquiv i).symm).symm b)))
    id
  ∘ (fun x : Space (3 * N) =>
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin (3 * N) => ℝ) (electronCoord i))
        (((MeasurableEquiv.toLp 2 (Fin (3 * N) → ℝ)).symm) ((Space.basis (d := 3 * N)).repr x)))

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
      ((MeasurableEquiv.toLp 2 (Fin (3 * N) → ℝ)).symm)).trans
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin (3 * N) => ℝ) (electronCoord i))).trans
    (MeasurableEquiv.prodCongr
      (((MeasurableEquiv.piCongrLeft (fun _ : {k // electronCoord i k} => ℝ)
            (electronCoordEquiv i).symm).symm.trans
          (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))).trans
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

/-- **Per-term molecular Coulomb L² identity with a spectator-dependent center** (generalizes
`molecular_coulombTerm_lintegral` from a fixed `R : Space 3` to a center `Rf` that is a measurable
function of the spectator coordinates). Needed for the electron–electron term `‖eᵢ − eⱼ‖⁻¹`, whose
center `eⱼ` is fixed *within* electron-`i`'s fiber (it is part of the spectator `z`), unlike the nuclear
term's constant center. The nuclear term is the special case `Rf = fun _ => R`. -/
lemma molecular_coulombTerm_lintegral_var {N : ℕ} (i : Fin N)
    (Rf : ({k // ¬ electronCoord i k} → ℝ) → Space 3) (hRf : Measurable Rf)
    {u : Space (3 * N) → ℂ} (hu : Measurable u) :
    ∫⁻ x, (ENNReal.ofReal (‖electronPos x i - Rf (molecularSplitMap i x).2‖⁻¹ * ‖u x‖)) ^ 2
        ∂(volume : MeasureTheory.Measure (Space (3 * N)))
      = ∫⁻ z, ∫⁻ y, (ENNReal.ofReal (‖y - Rf z‖⁻¹ * ‖u ((molecularSplitEquiv i).symm (y, z))‖)) ^ 2
          ∂(volume : MeasureTheory.Measure (Space 3))
          ∂(volume : MeasureTheory.Measure ({k // ¬ electronCoord i k} → ℝ)) := by
  have hG : Measurable (fun p : Space 3 × ({k // ¬ electronCoord i k} → ℝ) =>
      (ENNReal.ofReal (‖p.1 - Rf p.2‖⁻¹ * ‖u ((molecularSplitEquiv i).symm p)‖)) ^ 2) := by
    refine (ENNReal.measurable_ofReal.comp (Measurable.mul ?_ ?_)).pow_const 2
    · exact (measurable_fst.sub (hRf.comp measurable_snd)).norm.inv
    · exact (hu.comp (molecularSplitEquiv i).symm.measurable).norm
  have hpt : (fun x => (ENNReal.ofReal
        (‖electronPos x i - Rf (molecularSplitMap i x).2‖⁻¹ * ‖u x‖)) ^ 2)
      = (fun x => (ENNReal.ofReal (‖(molecularSplitMap i x).1 - Rf (molecularSplitMap i x).2‖⁻¹
          * ‖u ((molecularSplitEquiv i).symm (molecularSplitMap i x))‖)) ^ 2) := by
    funext x
    rw [molecularSplitMap_fst, ← coe_molecularSplitEquiv, MeasurableEquiv.symm_apply_apply]
  rw [hpt]
  exact molecularSplit_lintegral i _ hG

/-- **L² integral triangle inequality (params-Minkowski).** For nonnegative `F, G ∈ L²(μ)`,
`√(∫(F+G)²) ≤ √(∫F²) + √(∫G²)`. Proven via the algebraic expansion plus the integral Cauchy–Schwarz
(`integral_mul_le_Lp_mul_Lq_of_nonneg`, `p = q = 2`). This is the reassembly step of the molecular lift: the
fiberwise single-electron bound `√(inner z) ≤ ε√(K z) + C√(M z)` is integrated over the spectator parameter
`z` and recombined into the molecular `‖V u‖₂ ≤ ε‖T u‖₂ + C‖u‖₂` via this inequality (with `F = ε√K`,
`G = C√M`). -/
lemma sqrt_integral_add_sq_le {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {F G : α → ℝ} (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) :
    Real.sqrt (∫ a, (F a + G a) ^ 2 ∂μ)
      ≤ Real.sqrt (∫ a, F a ^ 2 ∂μ) + Real.sqrt (∫ a, G a ^ 2 ∂μ) := by
  have hF2 : Integrable (fun a => F a ^ 2) μ := hF.integrable_sq
  have hG2 : Integrable (fun a => G a ^ 2) μ := hG.integrable_sq
  have hFG : Integrable (fun a => F a * G a) μ := hF.integrable_mul hG
  have hIF : 0 ≤ ∫ a, F a ^ 2 ∂μ := integral_nonneg fun a => sq_nonneg _
  have hIG : 0 ≤ ∫ a, G a ^ 2 ∂μ := integral_nonneg fun a => sq_nonneg _
  -- Cauchy–Schwarz via the discriminant of `0 ≤ ∫ (F - t G)²`.
  have hquad : ∀ t : ℝ,
      0 ≤ (∫ a, G a ^ 2 ∂μ) * (t * t) + -(2 * ∫ a, F a * G a ∂μ) * t + ∫ a, F a ^ 2 ∂μ := by
    intro t
    have hcongr : ∫ a, (F a - t * G a) ^ 2 ∂μ
        = (∫ a, G a ^ 2 ∂μ) * (t * t) + -(2 * ∫ a, F a * G a ∂μ) * t + ∫ a, F a ^ 2 ∂μ := by
      have h1 : Integrable (fun a => (t * t) * G a ^ 2) μ := hG2.const_mul (t * t)
      have h2 : Integrable (fun a => (-(2 * t)) * (F a * G a)) μ := hFG.const_mul (-(2 * t))
      have key : ∀ a, (F a - t * G a) ^ 2
          = (t * t) * G a ^ 2 + ((-(2 * t)) * (F a * G a) + F a ^ 2) := fun a => by ring
      simp_rw [key]
      rw [integral_add h1 (show Integrable (fun a => (-(2 * t)) * (F a * G a) + F a ^ 2) μ from
            h2.add hF2),
        integral_add h2 hF2, integral_const_mul, integral_const_mul]
      ring
    rw [← hcongr]; exact integral_nonneg fun a => sq_nonneg _
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  have hcs2 : (∫ a, F a * G a ∂μ) ^ 2 ≤ (∫ a, F a ^ 2 ∂μ) * (∫ a, G a ^ 2 ∂μ) := by nlinarith [hdisc]
  have hcs : ∫ a, F a * G a ∂μ ≤ Real.sqrt (∫ a, F a ^ 2 ∂μ) * Real.sqrt (∫ a, G a ^ 2 ∂μ) := by
    rw [← Real.sqrt_mul hIF]
    calc ∫ a, F a * G a ∂μ ≤ |∫ a, F a * G a ∂μ| := le_abs_self _
      _ = Real.sqrt ((∫ a, F a * G a ∂μ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((∫ a, F a ^ 2 ∂μ) * (∫ a, G a ^ 2 ∂μ)) := Real.sqrt_le_sqrt hcs2
  have hint : ∫ a, (F a + G a) ^ 2 ∂μ
      = ∫ a, F a ^ 2 ∂μ + 2 * (∫ a, F a * G a ∂μ) + ∫ a, G a ^ 2 ∂μ := by
    have h1 : Integrable (fun a => 2 * (F a * G a)) μ := hFG.const_mul 2
    have key : ∀ a, (F a + G a) ^ 2 = F a ^ 2 + (2 * (F a * G a) + G a ^ 2) := fun a => by ring
    simp_rw [key]
    rw [integral_add hF2 (show Integrable (fun a => 2 * (F a * G a) + G a ^ 2) μ from h1.add hG2),
      integral_add h1 hG2, integral_const_mul]
    ring
  rw [hint]
  have hsq : ∫ a, F a ^ 2 ∂μ + 2 * (∫ a, F a * G a ∂μ) + ∫ a, G a ^ 2 ∂μ
      ≤ (Real.sqrt (∫ a, F a ^ 2 ∂μ) + Real.sqrt (∫ a, G a ^ 2 ∂μ)) ^ 2 := by
    nlinarith [hcs, Real.sq_sqrt hIF, Real.sq_sqrt hIG]
  calc Real.sqrt (∫ a, F a ^ 2 ∂μ + 2 * (∫ a, F a * G a ∂μ) + ∫ a, G a ^ 2 ∂μ)
      ≤ Real.sqrt ((Real.sqrt (∫ a, F a ^ 2 ∂μ) + Real.sqrt (∫ a, G a ^ 2 ∂μ)) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (∫ a, F a ^ 2 ∂μ) + Real.sqrt (∫ a, G a ^ 2 ∂μ) :=
        Real.sqrt_sq (by positivity)

/-- **The coordinate-scatter linear map** placing `y : Space 3` into electron `i`'s three coordinates of
`Space (3N)` (zero elsewhere). This is the linear part of the fiber injection
`(molecularSplitEquiv i).symm (·, z) = gatherLM i · + (spectator scatter of z)`; the fiber
`ũ_z = u ∘ (that affine map)` is then Schwartz by `SchwartzMap.compCLMOfAntilipschitz`. -/
def gatherLM {N : ℕ} (i : Fin N) : Space 3 →ₗ[ℝ] Space (3 * N) where
  toFun y := ⟨fun k => if k.val / 3 = i.val then y.val ⟨k.val % 3, Nat.mod_lt _ (by norm_num)⟩ else 0⟩
  map_add' y₁ y₂ := by
    ext k
    simp only [Space.add_val, Pi.add_apply]
    split_ifs with h
    · rfl
    · rw [add_zero]
  map_smul' c y := by
    ext k
    simp only [Space.smul_val, RingHom.id_apply]
    split_ifs with h
    · rfl
    · simp

@[simp] lemma gatherLM_apply {N : ℕ} (i : Fin N) (y : Space 3) (k : Fin (3 * N)) :
    (gatherLM i y) k
      = if k.val / 3 = i.val then y.val ⟨k.val % 3, Nat.mod_lt _ (by norm_num)⟩ else 0 := rfl

/-- **`gatherLM` is norm-preserving** (an isometry onto electron `i`'s coordinate block): each of `y`'s
three coordinates lands in exactly one slot of `Space (3N)` and the rest are zero, so
`‖gatherLM i y‖ = ‖y‖`. The sum reindexes via `electronCoordEquiv`. This gives `AntilipschitzWith 1` for the
fiber injection — the hypothesis `SchwartzMap.compCLMOfAntilipschitz` needs. -/
lemma norm_gatherLM {N : ℕ} (i : Fin N) (y : Space 3) : ‖gatherLM i y‖ = ‖y‖ := by
  rw [Space.norm_eq, Space.norm_eq]
  congr 1
  rw [← Fintype.sum_subtype_add_sum_subtype (fun k => electronCoord i k)
    (fun k => ((gatherLM i y) k) ^ 2)]
  have hblock : ∑ k : {k // electronCoord i k}, ((gatherLM i y) k.1) ^ 2 = ∑ j : Fin 3, (y j) ^ 2 := by
    rw [← Fintype.sum_equiv (electronCoordEquiv i)
      (fun k : {k // electronCoord i k} => ((gatherLM i y) k.1) ^ 2) (fun j => (y j) ^ 2)]
    intro k
    have hk : k.1.val / 3 = i.val := k.2
    simp only [gatherLM_apply, hk, if_true]
    rfl
  have hrest : ∑ k : {k // ¬ electronCoord i k}, ((gatherLM i y) k.1) ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    have hk : ¬ k.1.val / 3 = i.val := k.2
    simp only [gatherLM_apply, hk, if_false]
    ring
  rw [hblock, hrest, add_zero]

/-- `gatherLM` as a continuous linear map (`Space 3` is finite-dimensional). -/
noncomputable def gatherCLM {N : ℕ} (i : Fin N) : Space 3 →L[ℝ] Space (3 * N) :=
  (gatherLM i).toContinuousLinearMap

@[simp] lemma gatherCLM_apply {N : ℕ} (i : Fin N) (y : Space 3) :
    gatherCLM i y = gatherLM i y := rfl

/-- The coordinate scatter is an **isometry** (`norm_gatherLM`). -/
lemma isometry_gatherLM {N : ℕ} (i : Fin N) : Isometry (gatherLM i) :=
  AddMonoidHomClass.isometry_of_norm (gatherLM i) (norm_gatherLM i)

/-- The coordinate scatter is `AntilipschitzWith 1` — the hypothesis `compCLMOfAntilipschitz` consumes. -/
lemma antilipschitz_gatherLM {N : ℕ} (i : Fin N) : AntilipschitzWith 1 (gatherLM i) :=
  (isometry_gatherLM i).antilipschitz

/-- The **spectator factor** of the molecular split reads the non-`i` coordinates: `(molecularSplitMap i x).2`
is `fun k => x.val k.1`. (Definitional, like `molecularSplitMap_fst`.) -/
lemma molecularSplitMap_snd {N : ℕ} (i : Fin N) (x : Space (3 * N)) :
    (molecularSplitMap i x).2 = fun k : {k // ¬ electronCoord i k} => x.val k.1 := rfl

/-- **`electronPos ∘ gatherLM = id`** — scattering `y` into electron `i`'s coordinates and reading them back
returns `y`. (`gatherLM` is a right inverse of the `electronPos` projection.) -/
lemma electronPos_gatherLM {N : ℕ} (i : Fin N) (y : Space 3) :
    electronPos (gatherLM i y) i = y := by
  ext j
  simp only [electronPos, gatherLM_apply]
  rw [if_pos (by omega : (3 * i.val + j.val) / 3 = i.val)]
  congr 1
  apply Fin.ext
  simp

/-- **The fiber injection is affine:** `(molecularSplitEquiv i).symm (y, z) = gatherLM i y + c_z`, where
`c_z := (molecularSplitEquiv i).symm (0, z)` (constant in `y`). Proven by injectivity of the split equiv +
the round-trip helpers (`molecularSplitMap_fst`/`_snd`, `electronPos_add`, `electronPos_gatherLM`): applying
`molecularSplitEquiv i` to `gatherLM i y + c_z` recovers `(y, z)`. This translation structure carries
`gatherLM`'s isometry / temperate growth to the full fiber map. -/
lemma molecularSplit_symm_eq {N : ℕ} (i : Fin N) (y : Space 3)
    (z : {k // ¬ electronCoord i k} → ℝ) :
    (molecularSplitEquiv i).symm (y, z)
      = gatherLM i y + (molecularSplitEquiv i).symm (0, z) := by
  have h0 : molecularSplitMap i ((molecularSplitEquiv i).symm (0, z)) = (0, z) := by
    rw [← coe_molecularSplitEquiv, MeasurableEquiv.apply_symm_apply]
  have hz1 : electronPos ((molecularSplitEquiv i).symm (0, z)) i = 0 := by
    rw [← molecularSplitMap_fst, h0]
  have hz2 : ∀ k : {k // ¬ electronCoord i k}, ((molecularSplitEquiv i).symm (0, z)).val k.1 = z k := by
    intro k
    have h := congrArg Prod.snd h0
    rw [molecularSplitMap_snd] at h
    exact congrFun h k
  apply (molecularSplitEquiv i).injective
  rw [MeasurableEquiv.apply_symm_apply, coe_molecularSplitEquiv]
  refine Prod.ext ?_ ?_
  · show y = (molecularSplitMap i (gatherLM i y + (molecularSplitEquiv i).symm (0, z))).1
    rw [molecularSplitMap_fst, electronPos_add, electronPos_gatherLM, hz1, add_zero]
  · show z = (molecularSplitMap i (gatherLM i y + (molecularSplitEquiv i).symm (0, z))).2
    rw [molecularSplitMap_snd]
    funext k
    rw [Space.add_val]
    simp only [Pi.add_apply, gatherLM_apply]
    split_ifs with h
    · exact absurd h k.2
    · rw [hz2 k, zero_add]

/-- The fiber injection `y ↦ (molecularSplitEquiv i).symm (y, z)` has **temperate growth** — it is affine
(`molecularSplit_symm_eq`): a continuous linear map (`gatherCLM`, temperate growth) plus a constant. -/
lemma hasTemperateGrowth_fiber {N : ℕ} (i : Fin N) (z : {k // ¬ electronCoord i k} → ℝ) :
    Function.HasTemperateGrowth (fun y : Space 3 => (molecularSplitEquiv i).symm (y, z)) := by
  have he : (fun y : Space 3 => (molecularSplitEquiv i).symm (y, z))
      = (fun y => gatherCLM i y) + (fun _ => (molecularSplitEquiv i).symm (0, z)) := by
    funext y
    simp only [Pi.add_apply, gatherCLM_apply]
    exact molecularSplit_symm_eq i y z
  rw [he]
  exact (gatherCLM i).hasTemperateGrowth.add (Function.HasTemperateGrowth.const _)

/-- The fiber injection is an **isometry** — `gatherLM`'s isometry (`norm_gatherLM`) plus a translation. -/
lemma isometry_fiber {N : ℕ} (i : Fin N) (z : {k // ¬ electronCoord i k} → ℝ) :
    Isometry (fun y : Space 3 => (molecularSplitEquiv i).symm (y, z)) := by
  refine Isometry.of_dist_eq fun y₁ y₂ => ?_
  rw [molecularSplit_symm_eq i y₁ z, molecularSplit_symm_eq i y₂ z, dist_add_right]
  exact (isometry_gatherLM i).dist_eq y₁ y₂

/-- The fiber injection is **`AntilipschitzWith 1`** (from `isometry_fiber`) — the last hypothesis
`compCLMOfAntilipschitz` needs. -/
lemma antilipschitz_fiber {N : ℕ} (i : Fin N) (z : {k // ¬ electronCoord i k} → ℝ) :
    AntilipschitzWith 1 (fun y : Space 3 => (molecularSplitEquiv i).symm (y, z)) :=
  (isometry_fiber i z).antilipschitz

/-- **The fiber as a genuine Schwartz map.** For a molecular Schwartz function `u : 𝓢(Space (3N), ℂ)` and a
fixed spectator `z`, the restriction `y ↦ u ((molecularSplitEquiv i).symm (y, z))` is `𝓢(Space 3, ℂ)` — by
`SchwartzMap.compCLMOfAntilipschitz` (temperate growth + antilipschitz of the affine fiber injection). This is
the object the fiberwise single-electron bound (`exists_coulomb_relbound_uniform`) applies to. -/
noncomputable def fiberSchwartz {N : ℕ} (i : Fin N) (z : {k // ¬ electronCoord i k} → ℝ)
    (u : 𝓢(Space (3 * N), ℂ)) : 𝓢(Space 3, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℝ (hasTemperateGrowth_fiber i z) (antilipschitz_fiber i z) u

@[simp] lemma fiberSchwartz_apply {N : ℕ} (i : Fin N) (z : {k // ¬ electronCoord i k} → ℝ)
    (u : 𝓢(Space (3 * N), ℂ)) (y : Space 3) :
    fiberSchwartz i z u y = u ((molecularSplitEquiv i).symm (y, z)) := rfl

/-- The translation `y ↦ y + R` has **temperate growth** (affine: `id + const`). -/
lemma hasTemperateGrowth_translate {d : ℕ} (R : Space d) :
    Function.HasTemperateGrowth (fun y : Space d => y + R) := by
  have he : (fun y : Space d => y + R)
      = (fun y => ContinuousLinearMap.id ℝ (Space d) y) + (fun _ => R) := by funext y; simp
  rw [he]
  exact (ContinuousLinearMap.id ℝ (Space d)).hasTemperateGrowth.add
    (Function.HasTemperateGrowth.const _)

/-- The translation `y ↦ y + R` is **`AntilipschitzWith 1`** (it is an isometry). -/
lemma antilipschitz_translate {d : ℕ} (R : Space d) :
    AntilipschitzWith 1 (fun y : Space d => y + R) :=
  (Isometry.of_dist_eq fun a b => dist_add_right a b R).antilipschitz

/-- **Translation of a Schwartz map** `v ↦ v(· + R)` is again Schwartz (translation is an affine isometry).
This recenters a Coulomb singularity `‖y − R‖⁻¹` to the origin so the uniform single-electron bound
`exists_coulomb_relbound_uniform` (stated at the origin) applies to a `R`-centered term. -/
noncomputable def translateSchwartz {d : ℕ} (R : Space d) (v : 𝓢(Space d, ℂ)) : 𝓢(Space d, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℝ (hasTemperateGrowth_translate R) (antilipschitz_translate R) v

@[simp] lemma translateSchwartz_apply {d : ℕ} (R : Space d) (v : 𝓢(Space d, ℂ)) (y : Space d) :
    translateSchwartz R v y = v (y + R) := rfl

/-- **Translation is measure-preserving on `Space d`** — its volume is add-right-invariant (Haar). This is
the change of variables `∫ f(y) dy = ∫ f(y' + R) dy'` underpinning the recentering of a Coulomb term. -/
lemma measurePreserving_translate {d : ℕ} (R : Space d) :
    MeasureTheory.MeasurePreserving (fun y : Space d => y + R)
      (volume : MeasureTheory.Measure (Space d)) (volume : MeasureTheory.Measure (Space d)) :=
  measurePreserving_add_right volume R

/-- **L² norm is translation-invariant:** `∫ ‖translateSchwartz R v‖² = ∫ ‖v‖²`. -/
lemma integral_normSq_translateSchwartz {d : ℕ} (R : Space d) (v : 𝓢(Space d, ℂ)) :
    ∫ y : Space d, ‖translateSchwartz R v y‖ ^ 2 = ∫ y : Space d, ‖v y‖ ^ 2 := by
  simp only [translateSchwartz_apply]
  exact (measurePreserving_translate R).integral_comp (measurableEmbedding_addRight R)
    (fun y => ‖v y‖ ^ 2)

/-- **Recentering identity:** the origin-Coulomb integral of the translated `translateSchwartz R v` equals the
`R`-centered Coulomb integral of `v`. (Change of variables `y' = y − R`.) -/
lemma integral_coulombSq_translate {d : ℕ} (R : Space d) (v : 𝓢(Space d, ℂ)) :
    ∫ y : Space d, (‖y‖⁻¹ * ‖translateSchwartz R v y‖) ^ 2
      = ∫ y : Space d, (‖y - R‖⁻¹ * ‖v y‖) ^ 2 := by
  rw [← (measurePreserving_translate R).integral_comp (measurableEmbedding_addRight R)
    (fun y => (‖y - R‖⁻¹ * ‖v y‖) ^ 2)]
  simp only [translateSchwartz_apply, add_sub_cancel_right]

open QuantumMechanics in
/-- **Momentum commutes with translation:** `𝐩ᵢ (translateSchwartz R v) = translateSchwartz R (𝐩ᵢ v)`.
The momentum operator is `-iℏ ∂ᵢ`, and `∂ᵢ(v(·+R)) = (∂ᵢv)(·+R)` (chain rule, translation has identity
derivative). Consequence: the kinetic L² norm is translation-invariant. -/
lemma momentumCLM_translateSchwartz {d : ℕ} (i : Fin d) (R : Space d) (v : 𝓢(Space d, ℂ)) :
    momentumCLM i (translateSchwartz R v) = translateSchwartz R (momentumCLM i v) := by
  have hfd : ∀ x : Space d,
      fderiv ℝ (⇑(translateSchwartz R v)) x = fderiv ℝ (⇑v) (x + R) := by
    intro x
    have hc : ⇑(translateSchwartz R v) = fun x => (⇑v) (x + R) := by
      funext y; exact translateSchwartz_apply R v y
    rw [hc]
    have h1 : HasFDerivAt (fun x : Space d => x + R) (ContinuousLinearMap.id ℝ (Space d)) x :=
      (hasFDerivAt_id x).add_const R
    have h2 : HasFDerivAt (⇑v) (fderiv ℝ (⇑v) (x + R)) (x + R) :=
      v.differentiableAt.hasFDerivAt
    have h3 := h2.comp x h1
    rw [ContinuousLinearMap.comp_id] at h3
    exact h3.fderiv
  ext x
  rw [momentumCLM_apply, translateSchwartz_apply, momentumCLM_apply]
  congr 1
  show (fderiv ℝ (⇑(translateSchwartz R v)) x) (Space.basis i) = (fderiv ℝ (⇑v) (x + R)) (Space.basis i)
  rw [hfd]

open QuantumMechanics in
/-- **The kinetic operator `∑ᵢ pᵢ²` commutes with translation** (W3-79 applied twice per component, then
`translateSchwartz`'s linearity `map_sum`). -/
lemma kineticSq_translateSchwartz {d : ℕ} (R : Space d) (v : 𝓢(Space d, ℂ)) :
    (∑ i, momentumCLM i (momentumCLM i (translateSchwartz R v)))
      = translateSchwartz R (∑ i, momentumCLM i (momentumCLM i v)) := by
  have hsum : translateSchwartz R (∑ i, momentumCLM i (momentumCLM i v))
      = ∑ i, translateSchwartz R (momentumCLM i (momentumCLM i v)) :=
    map_sum (SchwartzMap.compCLMOfAntilipschitz ℝ (hasTemperateGrowth_translate R)
      (antilipschitz_translate R)) _ _
  rw [hsum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [momentumCLM_translateSchwartz, momentumCLM_translateSchwartz]

open QuantumMechanics in
/-- **The kinetic L² norm is translation-invariant:** `∫ ‖∑pᵢ²(translateSchwartz R v)‖² = ∫ ‖∑pᵢ²v‖²`. -/
lemma integral_kineticSq_translateSchwartz {d : ℕ} (R : Space d) (v : 𝓢(Space d, ℂ)) :
    ∫ y : Space d, ‖(∑ i, momentumCLM i (momentumCLM i (translateSchwartz R v))) y‖ ^ 2
      = ∫ y : Space d, ‖(∑ i, momentumCLM i (momentumCLM i v)) y‖ ^ 2 := by
  rw [kineticSq_translateSchwartz]
  exact integral_normSq_translateSchwartz R (∑ i, momentumCLM i (momentumCLM i v))

open QuantumMechanics in
/-- **Center-`R` uniform Coulomb relative bound** — the single-electron bound for a Coulomb singularity
centered at an arbitrary `R : Space 3` (not just the origin). For every `ε > 0` there is a uniform
`C` such that `√(∫(‖y−R‖⁻¹‖v y‖)²) ≤ ε√(∫‖∑pᵢ²v‖²) + C√(∫‖v‖²)` for all `v` and `R`. Derived from the
origin bound (`exists_coulomb_relbound_uniform`) applied to `translateSchwartz R v`, then the three
translation identities (Coulomb W3-78, kinetic W3-81, L² W3-77) recenter it. This is the fiberwise tool
the molecular lift applies to each nuclear term (`R` = nucleus) and each e-e term (`R` = electron `j`'s
position, fixed by the spectator coordinates). -/
lemma exists_coulomb_relbound_center {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : 𝓢(Space 3, ℂ)) (R : Space 3),
      Real.sqrt (∫ y : Space 3, (‖y - R‖⁻¹ * ‖v y‖) ^ 2)
        ≤ ε * Real.sqrt (∫ y : Space 3, ‖(∑ i, momentumCLM i (momentumCLM i v)) y‖ ^ 2)
          + C * Real.sqrt (∫ y : Space 3, ‖v y‖ ^ 2) := by
  obtain ⟨C, hC0, hbound⟩ := exists_coulomb_relbound_uniform hε
  refine ⟨C, hC0, fun v R => ?_⟩
  have h := hbound (translateSchwartz R v)
  rw [integral_coulombSq_translate, integral_kineticSq_translateSchwartz,
    integral_normSq_translateSchwartz] at h
  exact h

/-- **The squared Coulomb·Schwartz integrand `(‖y‖⁻¹‖u y‖)²` is integrable** (origin). The disjoint-support
split `‖y‖⁻¹ = V₁ + V₂` makes it the sum of the near part (W3-32, dominated by `‖y‖⁻²·1_{≤1}`) and the far
part (W3-31, bounded). Needed to convert the fiber's `lintegral` to a Bochner integral so the
single-electron bound applies. -/
lemma integrable_coulombSq (u : 𝓢(Space 3, ℂ)) :
    Integrable (fun y : Space 3 => (‖y‖⁻¹ * ‖u y‖) ^ 2) := by
  refine ((integrable_coulombNear_mul_sq u).add (integrable_coulombFar_mul_sq u)).congr
    (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.add_apply]
  by_cases h : ‖x‖ ≤ 1
  · rw [if_pos h, if_neg (not_lt.mpr h)]; ring
  · rw [if_neg h, if_pos (not_le.mp h)]; ring

/-- **Center-`R` Coulomb-squared integrability** `Integrable (fun y => (‖y − R‖⁻¹‖v y‖)²)` — by translating
the origin version (`integrable_coulombSq` on `translateSchwartz R v`) through the measure-preserving
`(· − R)`. -/
lemma integrable_coulombSq_center (R : Space 3) (v : 𝓢(Space 3, ℂ)) :
    Integrable (fun y : Space 3 => (‖y - R‖⁻¹ * ‖v y‖) ^ 2) := by
  have h := ((measurePreserving_translate (-R)).integrable_comp_emb
    (measurableEmbedding_addRight (-R))).mpr (integrable_coulombSq (translateSchwartz R v))
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [Function.comp_apply, translateSchwartz_apply, ← sub_eq_add_neg, sub_add_cancel]

/-- **lintegral↔Bochner bridge for the center-`R` Coulomb integrand:**
`∫⁻ (ofReal (‖y − R‖⁻¹‖v y‖))² = ENNReal.ofReal (∫ (‖y − R‖⁻¹‖v y‖)²)`. Turns the inner `Space 3` lower
integral of the molecular Fubini (W3-53) into a Bochner integral, so the Bochner-form center-`R` bound
(`exists_coulomb_relbound_center`) applies. -/
lemma lintegral_coulombSq_center_eq (R : Space 3) (v : 𝓢(Space 3, ℂ)) :
    ∫⁻ y : Space 3, (ENNReal.ofReal (‖y - R‖⁻¹ * ‖v y‖)) ^ 2
      = ENNReal.ofReal (∫ y : Space 3, (‖y - R‖⁻¹ * ‖v y‖) ^ 2) := by
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_coulombSq_center R v)
    (Filter.Eventually.of_forall fun y => by positivity)]
  refine lintegral_congr fun y => ?_
  rw [ENNReal.ofReal_pow (by positivity)]

/-- **Per-fiber squared Coulomb bound (lintegral form).** Given the center-`R` relative bound
`√(∫(‖y−R‖⁻¹‖v y‖)²) ≤ A + B` (with `A, B ≥ 0` the kinetic and L² contributions), the inner `Space 3` lower
integral is bounded: `∫⁻(ofReal(‖y−R‖⁻¹‖v y‖))² ≤ ENNReal.ofReal ((A + B)²)`. (Square the bound through the
lintegral↔Bochner bridge.) The per-spectator input to the params-Minkowski reassembly. -/
lemma lintegral_coulombSq_center_le {R : Space 3} {v : 𝓢(Space 3, ℂ)} {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hb : Real.sqrt (∫ y : Space 3, (‖y - R‖⁻¹ * ‖v y‖) ^ 2) ≤ A + B) :
    ∫⁻ y : Space 3, (ENNReal.ofReal (‖y - R‖⁻¹ * ‖v y‖)) ^ 2 ≤ ENNReal.ofReal ((A + B) ^ 2) := by
  rw [lintegral_coulombSq_center_eq]
  apply ENNReal.ofReal_le_ofReal
  have hI : 0 ≤ ∫ y : Space 3, (‖y - R‖⁻¹ * ‖v y‖) ^ 2 := integral_nonneg fun y => sq_nonneg _
  nlinarith [Real.sq_sqrt hI, Real.sqrt_nonneg (∫ y : Space 3, (‖y - R‖⁻¹ * ‖v y‖) ^ 2), hb, hA, hB]

/-- **Molecular L²-Fubini for `‖u‖²`** (the spectator analog of W3-53, no Coulomb factor): the molecular
`L²` lower integral of `u` equals the iterated integral of the fibers' `L²` densities. (Round-trip through
the split equiv via `molecularSplit_lintegral`.) Used to relate the spectator-integrated fiber `L²`/kinetic
norms back to the molecular ones. -/
lemma molecular_normSq_lintegral {N : ℕ} (i : Fin N) {u : Space (3 * N) → ℂ} (hu : Measurable u) :
    ∫⁻ x, (ENNReal.ofReal (‖u x‖)) ^ 2 ∂(volume : MeasureTheory.Measure (Space (3 * N)))
      = ∫⁻ z, ∫⁻ y, (ENNReal.ofReal (‖u ((molecularSplitEquiv i).symm (y, z))‖)) ^ 2
          ∂(volume : MeasureTheory.Measure (Space 3))
          ∂(volume : MeasureTheory.Measure ({k // ¬ electronCoord i k} → ℝ)) := by
  have hG : Measurable (fun p : Space 3 × ({k // ¬ electronCoord i k} → ℝ) =>
      (ENNReal.ofReal (‖u ((molecularSplitEquiv i).symm p)‖)) ^ 2) :=
    (ENNReal.measurable_ofReal.comp
      (hu.comp (molecularSplitEquiv i).symm.measurable).norm).pow_const 2
  have hpt : (fun x => (ENNReal.ofReal (‖u x‖)) ^ 2)
      = (fun x => (ENNReal.ofReal (‖u ((molecularSplitEquiv i).symm (molecularSplitMap i x))‖)) ^ 2) := by
    funext x
    rw [← coe_molecularSplitEquiv, MeasurableEquiv.symm_apply_apply]
  rw [hpt]
  exact molecularSplit_lintegral i _ hG

/-- **`gatherLM` sends the block basis vector to the molecular basis vector** `gatherLM iₑ (eⱼ) = e_{3iₑ+j}`:
the scatter places electron `iₑ`'s `j`-th coordinate direction at slot `3iₑ+j`. This identifies the fiber's
block momentum direction with electron `iₑ`'s coordinate momentum in the full system. -/
lemma gatherLM_basis {N : ℕ} (iₑ : Fin N) (j : Fin 3) :
    gatherLM iₑ (Space.basis j)
      = Space.basis ⟨3 * iₑ.val + j.val, by have := iₑ.isLt; have := j.isLt; omega⟩ := by
  ext k
  simp only [gatherLM_apply, Space.basis_apply, Fin.ext_iff]
  split_ifs with h1 h2 h3 h3 <;> first | rfl | (exfalso; omega)

open QuantumMechanics in
/-- **Momentum commutes with the fiber restriction:** the fiber's `j`-th block momentum equals the fiber of
`u`'s momentum in electron `iₑ`'s `j`-th coordinate, `𝐩ⱼ (fiberSchwartz iₑ z u) = fiberSchwartz iₑ z (𝐩_{3iₑ+j} u)`.
Chain rule through the affine fiber injection (linear part `gatherCLM iₑ`, `molecularSplit_symm_eq`) + the
basis identification `gatherLM_basis`. Mirrors `momentumCLM_translateSchwartz` (W3-79). -/
lemma momentumCLM_fiberSchwartz {N : ℕ} (iₑ : Fin N) (j : Fin 3)
    (z : {k // ¬ electronCoord iₑ k} → ℝ) (u : 𝓢(Space (3 * N), ℂ)) :
    momentumCLM j (fiberSchwartz iₑ z u)
      = fiberSchwartz iₑ z (momentumCLM ⟨3 * iₑ.val + j.val, by
          have := iₑ.isLt; have := j.isLt; omega⟩ u) := by
  have hfd : fderiv ℝ (⇑(fiberSchwartz iₑ z u))
      = fun y => (fderiv ℝ (⇑u) ((molecularSplitEquiv iₑ).symm (y, z))).comp (gatherCLM iₑ) := by
    funext y
    have hc : ⇑(fiberSchwartz iₑ z u) = fun y => (⇑u) ((molecularSplitEquiv iₑ).symm (y, z)) := by
      funext y'; exact fiberSchwartz_apply iₑ z u y'
    rw [hc]
    have hgeq : (fun y : Space 3 => (molecularSplitEquiv iₑ).symm (y, z))
        = fun y => gatherCLM iₑ y + (molecularSplitEquiv iₑ).symm (0, z) := by
      funext y; rw [gatherCLM_apply]; exact molecularSplit_symm_eq iₑ y z
    have hg : HasFDerivAt (fun y : Space 3 => (molecularSplitEquiv iₑ).symm (y, z)) (gatherCLM iₑ) y := by
      rw [hgeq]; exact ((gatherCLM iₑ).hasFDerivAt).add_const _
    have hu : HasFDerivAt (⇑u) (fderiv ℝ (⇑u) ((molecularSplitEquiv iₑ).symm (y, z)))
        ((molecularSplitEquiv iₑ).symm (y, z)) := u.differentiableAt.hasFDerivAt
    exact (hu.comp y hg).fderiv
  ext y
  rw [momentumCLM_apply, fiberSchwartz_apply, momentumCLM_apply]
  congr 1
  show (fderiv ℝ (⇑(fiberSchwartz iₑ z u)) y) (Space.basis j)
      = (fderiv ℝ (⇑u) ((molecularSplitEquiv iₑ).symm (y, z)))
          (Space.basis ⟨3 * iₑ.val + j.val, by have := iₑ.isLt; have := j.isLt; omega⟩)
  rw [hfd, ContinuousLinearMap.comp_apply, gatherCLM_apply, gatherLM_basis]

open QuantumMechanics in
/-- **The fiber's block kinetic operator `∑ⱼ 𝐩ⱼ²` is the fiber of `u`'s electron-`iₑ` block kinetic**:
`∑_{j:Fin 3} 𝐩ⱼ² (fiberSchwartz iₑ z u) = fiberSchwartz iₑ z (∑_{j:Fin 3} 𝐩_{3iₑ+j}² u)` (W3-89 twice per
component + `fiberSchwartz`'s linearity `map_sum`). -/
lemma kineticSq_fiberSchwartz {N : ℕ} (iₑ : Fin N) (z : {k // ¬ electronCoord iₑ k} → ℝ)
    (u : 𝓢(Space (3 * N), ℂ)) :
    (∑ j, momentumCLM j (momentumCLM j (fiberSchwartz iₑ z u)))
      = fiberSchwartz iₑ z (∑ j : Fin 3, momentumCLM ⟨3 * iₑ.val + j.val, by
            have := iₑ.isLt; have := j.isLt; omega⟩
          (momentumCLM ⟨3 * iₑ.val + j.val, by have := iₑ.isLt; have := j.isLt; omega⟩ u)) := by
  have hsum : fiberSchwartz iₑ z (∑ j : Fin 3, momentumCLM ⟨3 * iₑ.val + j.val, by
        have := iₑ.isLt; have := j.isLt; omega⟩
      (momentumCLM ⟨3 * iₑ.val + j.val, by have := iₑ.isLt; have := j.isLt; omega⟩ u))
      = ∑ j : Fin 3, fiberSchwartz iₑ z (momentumCLM ⟨3 * iₑ.val + j.val, by
            have := iₑ.isLt; have := j.isLt; omega⟩
          (momentumCLM ⟨3 * iₑ.val + j.val, by have := iₑ.isLt; have := j.isLt; omega⟩ u)) :=
    map_sum (SchwartzMap.compCLMOfAntilipschitz ℝ (hasTemperateGrowth_fiber iₑ z)
      (antilipschitz_fiber iₑ z)) _ _
  rw [hsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [momentumCLM_fiberSchwartz, momentumCLM_fiberSchwartz]

open QuantumMechanics in
/-- **Molecular kinetic L²-Fubini (Kᶠ Fubini-reverse):** the spectator-iterated lower integral of the fiber's
block-kinetic density equals the molecular lower integral of the electron-`iₑ` block kinetic of `u`. Combines
the fiber kinetic commutation (W3-90) with the L²-Fubini (W3-87, applied to `∑ⱼ𝐩_{3iₑ+j}² u`). -/
lemma molecular_kineticSq_lintegral {N : ℕ} (iₑ : Fin N) (u : 𝓢(Space (3 * N), ℂ)) :
    ∫⁻ z, ∫⁻ y, (ENNReal.ofReal ‖(∑ j, momentumCLM j (momentumCLM j (fiberSchwartz iₑ z u))) y‖) ^ 2
        ∂(volume : MeasureTheory.Measure (Space 3))
        ∂(volume : MeasureTheory.Measure ({k // ¬ electronCoord iₑ k} → ℝ))
      = ∫⁻ x, (ENNReal.ofReal ‖(∑ j : Fin 3, momentumCLM ⟨3 * iₑ.val + j.val, by
            have := iₑ.isLt; have := j.isLt; omega⟩
          (momentumCLM ⟨3 * iₑ.val + j.val, by have := iₑ.isLt; have := j.isLt; omega⟩ u)) x‖) ^ 2
          ∂(volume : MeasureTheory.Measure (Space (3 * N))) := by
  have hw : Measurable (⇑(∑ j : Fin 3, momentumCLM ⟨3 * iₑ.val + j.val, by
      have := iₑ.isLt; have := j.isLt; omega⟩
    (momentumCLM ⟨3 * iₑ.val + j.val, by have := iₑ.isLt; have := j.isLt; omega⟩ u))) :=
    (SchwartzMap.continuous _).measurable
  rw [molecular_normSq_lintegral iₑ hw]
  refine lintegral_congr fun z => lintegral_congr fun y => ?_
  rw [kineticSq_fiberSchwartz, fiberSchwartz_apply]

open QuantumMechanics in
/-- **Momentum operators commute** (Schwartz level): `𝐩ᵢ (𝐩ⱼ f) = 𝐩ⱼ (𝐩ᵢ f)` — from PhysLib's
`momentum_comp_commute`. Building block for the kinetic-partial≤full cross-term. -/
lemma momentumCLM_comm {d : ℕ} (i j : Fin d) (f : 𝓢(Space d, ℂ)) :
    momentumCLM i (momentumCLM j f) = momentumCLM j (momentumCLM i f) := by
  rw [← ContinuousLinearMap.comp_apply, momentum_comp_commute, ContinuousLinearMap.comp_apply]

open QuantumMechanics SpaceDHilbertSpace SchwartzSubmodule in
/-- **Momentum is self-adjoint at the Schwartz/L² level:** `∫ conj(𝐩ᵢf)·g = ∫ conj(f)·𝐩ᵢg`. Extracted from
PhysLib's `momentumOperator_isSymmetric` (the Hilbert-space symmetry) via `schwartzEquiv_inner`
(`⟪Sf,Sg⟫ = ∫ conj(f)·g`). The integration-by-parts fact at the heart of the kinetic-positivity cross-term. -/
lemma momentumCLM_self_adjoint {d : ℕ} (i : Fin d) (f g : 𝓢(Space d, ℂ)) :
    ∫ x : Space d, starRingEnd ℂ (momentumCLM i f x) * g x
      = ∫ x : Space d, starRingEnd ℂ (f x) * momentumCLM i g x := by
  rw [← schwartzEquiv_inner (momentumCLM i f) g, ← schwartzEquiv_inner f (momentumCLM i g)]
  have key := momentumOperator_isSymmetric i (schwartzEquiv MeasureTheory.volume f)
    (schwartzEquiv MeasureTheory.volume g)
  simpa only [momentumOperator_apply, (schwartzEquiv MeasureTheory.volume).symm_apply_apply,
    Submodule.coe_inner] using key

open QuantumMechanics in
/-- **Kinetic cross-term is a nonnegative real:** `∫ conj(𝐩ⱼ²u)·𝐩ₘ²u = ↑(∫ ‖𝐩ₘ𝐩ⱼu‖²)`. Via momentum
self-adjointness (W3-93, twice) + commutation (W3-92): move both momenta onto `u`. This makes the
off-diagonal `⟨block-kinetic u, rest-kinetic u⟩` terms `≥ 0`, which is what forces
`‖block-kinetic u‖₂ ≤ ‖full-kinetic u‖₂`. -/
lemma momentum_cross_term_eq {d : ℕ} (j m : Fin d) (u : 𝓢(Space d, ℂ)) :
    ∫ x : Space d, starRingEnd ℂ (momentumCLM j (momentumCLM j u) x)
        * momentumCLM m (momentumCLM m u) x
      = ((∫ x : Space d, ‖momentumCLM m (momentumCLM j u) x‖ ^ 2 : ℝ) : ℂ) := by
  rw [momentumCLM_self_adjoint j (momentumCLM j u) (momentumCLM m (momentumCLM m u))]
  have hc : momentumCLM j (momentumCLM m (momentumCLM m u))
      = momentumCLM m (momentumCLM m (momentumCLM j u)) := by
    rw [momentumCLM_comm j m (momentumCLM m u), momentumCLM_comm j m u]
  simp_rw [fun x => congrFun (congrArg DFunLike.coe hc) x]
  rw [← momentumCLM_self_adjoint m (momentumCLM j u) (momentumCLM m (momentumCLM j u)),
    ← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [mul_comm ((starRingEnd ℂ) _), Complex.mul_conj]
  norm_cast
  exact Complex.normSq_eq_norm_sq _

/-- `‖g‖² ∈ L¹` for any Schwartz `g` on `Space d` (general-dimension version of `integrable_normSq_schwartz`). -/
lemma integrable_normSq_schwartz_gen {d : ℕ} (g : 𝓢(Space d, ℂ)) :
    Integrable (fun x : Space d => ‖g x‖ ^ 2) := by
  have h := (SchwartzMap.memLp g 2 volume).norm
  rw [memLp_two_iff_integrable_sq g.continuous.norm.aestronglyMeasurable] at h
  simpa only [norm_norm] using h

/-- **Positivity expansion:** if the cross term `∫ conj(a)·b` is a nonnegative real, then
`∫ ‖a‖² ≤ ∫ ‖a + b‖²`. (`‖a+b‖² = ‖a‖² + 2Re(conj a·b) + ‖b‖²`; integrate, the middle `= 2r ≥ 0`, the last
`≥ 0`.) This is what turns the kinetic cross-term nonnegativity into `‖block-kinetic u‖₂ ≤ ‖full-kinetic u‖₂`. -/
lemma integral_normSq_le_add {d : ℕ} (a b : 𝓢(Space d, ℂ)) {r : ℝ} (hr : 0 ≤ r)
    (hcross : ∫ x : Space d, starRingEnd ℂ (a x) * b x = (r : ℂ)) :
    ∫ x : Space d, ‖a x‖ ^ 2 ≤ ∫ x : Space d, ‖(a + b) x‖ ^ 2 := by
  have hint_cross : Integrable (fun x : Space d => starRingEnd ℂ (a x) * b x) := by
    exact (SchwartzMap.memLp a 2 volume).star.integrable_mul (SchwartzMap.memLp b 2 volume)
  have hIa := integrable_normSq_schwartz_gen a
  have hIb := integrable_normSq_schwartz_gen b
  have hmid : Integrable (fun x : Space d => 2 * RCLike.re (starRingEnd ℂ (a x) * b x)) :=
    hint_cross.re.const_mul 2
  have hexp : (fun x : Space d => ‖(a + b) x‖ ^ 2)
      = fun x => ‖a x‖ ^ 2 + 2 * RCLike.re (starRingEnd ℂ (a x) * b x) + ‖b x‖ ^ 2 := by
    funext x
    rw [add_apply, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_add]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, RCLike.re_to_complex,
      Complex.mul_re]
    ring
  rw [hexp, integral_add (show Integrable
      (fun x : Space d => ‖a x‖ ^ 2 + 2 * RCLike.re (starRingEnd ℂ (a x) * b x)) volume
      from hIa.add hmid) hIb,
    integral_add hIa hmid, integral_const_mul, integral_re hint_cross]
  erw [hcross]
  rw [show RCLike.re ((r : ℂ)) = r from Complex.ofReal_re r]
  have hIb0 : 0 ≤ ∫ x : Space d, ‖b x‖ ^ 2 := integral_nonneg fun x => sq_nonneg _
  nlinarith [hIb0, hr]

open QuantumMechanics in
/-- **Full molecular kinetic = electron-`iₑ` block + the rest.** `∑_{m:Fin 3N} 𝐩ₘ²u = (∑_{j:Fin 3}
𝐩_{3iₑ+j}²u) + (∑_{m∉block} 𝐩ₘ²u)`, splitting the full index set into electron `iₑ`'s three coordinates
(reindexed to `Fin 3` via `electronCoordEquiv`) and the complement. -/
lemma fullKinetic_eq_block_add_rest {N : ℕ} (iₑ : Fin N) (u : 𝓢(Space (3 * N), ℂ)) :
    (∑ m : Fin (3 * N), momentumCLM m (momentumCLM m u))
      = (∑ j : Fin 3, momentumCLM ⟨3 * iₑ.val + j.val, by
            have := iₑ.isLt; have := j.isLt; omega⟩
          (momentumCLM ⟨3 * iₑ.val + j.val, by have := iₑ.isLt; have := j.isLt; omega⟩ u))
        + ∑ m : {m : Fin (3 * N) // ¬ electronCoord iₑ m},
            momentumCLM m.1 (momentumCLM m.1 u) := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun m => electronCoord iₑ m)
    (fun m => momentumCLM m (momentumCLM m u))]
  congr 1
  refine Fintype.sum_equiv (electronCoordEquiv iₑ)
    (fun m : {m // electronCoord iₑ m} => momentumCLM m.1 (momentumCLM m.1 u)) _ (fun m => ?_)
  have hm : m.1 = (⟨3 * iₑ.val + (electronCoordEquiv iₑ m).val, by
      have := iₑ.isLt; have := (electronCoordEquiv iₑ m).isLt; omega⟩ : Fin (3 * N)) := by
    have h1 : m.1.val / 3 = iₑ.val := m.2
    apply Fin.ext
    show m.1.val = 3 * iₑ.val + (electronCoordEquiv iₑ m).val
    have h2 : (electronCoordEquiv iₑ m).val = m.1.val % 3 := rfl
    omega
  simp only [hm]

open QuantumMechanics in
/-- **Bilinear cross-term expansion for two families of iterated momenta.** For any two finite families
of directions `p : ι → Fin d`, `q : κ → Fin d`, the L² cross term of the two block kinetics
`(∑ᵢ 𝐩_{pi}²u)` and `(∑ₖ 𝐩_{qk}²u)` equals the double sum of per-pair `∫‖𝐩_{qk}𝐩_{pi}u‖²` — a sum of
**nonnegative reals**. Combines `sum_apply`, `map_sum` (conj), `Finset.sum_mul_sum`,
`integral_finsetSum`, and the per-pair identity (W3-94). This makes the off-diagonal
`⟪block-kinetic u, rest-kinetic u⟫` term `≥ 0`, forcing `‖block-kinetic u‖₂ ≤ ‖full-kinetic u‖₂`. -/
lemma integral_cross_kinetic_eq {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → Fin d) (q : κ → Fin d) (u : 𝓢(Space d, ℂ)) :
    ∫ x : Space d, starRingEnd ℂ ((∑ i, momentumCLM (p i) (momentumCLM (p i) u)) x)
        * ((∑ k, momentumCLM (q k) (momentumCLM (q k) u)) x)
      = ((∑ i, ∑ k, ∫ x : Space d,
          ‖momentumCLM (q k) (momentumCLM (p i) u) x‖ ^ 2 : ℝ) : ℂ) := by
  have hint : ∀ (i : ι) (k : κ), Integrable (fun x : Space d =>
      starRingEnd ℂ (momentumCLM (p i) (momentumCLM (p i) u) x)
        * momentumCLM (q k) (momentumCLM (q k) u) x) := by
    intro i k
    exact (SchwartzMap.memLp (momentumCLM (p i) (momentumCLM (p i) u)) 2 volume).star.integrable_mul
      (SchwartzMap.memLp (momentumCLM (q k) (momentumCLM (q k) u)) 2 volume)
  have hpt : (fun x : Space d =>
        starRingEnd ℂ ((∑ i, momentumCLM (p i) (momentumCLM (p i) u)) x)
          * ((∑ k, momentumCLM (q k) (momentumCLM (q k) u)) x))
      = fun x => ∑ i, ∑ k, starRingEnd ℂ (momentumCLM (p i) (momentumCLM (p i) u) x)
          * momentumCLM (q k) (momentumCLM (q k) u) x := by
    funext x
    rw [sum_apply, sum_apply, map_sum, Finset.sum_mul_sum]
  rw [hpt, integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun k _ => hint i k)]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun k _ => hint i k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact momentum_cross_term_eq (p i) (q k) u

open QuantumMechanics in
/-- **Kinetic partial ≤ full (Bochner L² form).** For electron `iₑ`, the L² norm of the block kinetic
`∑ⱼ 𝐩_{3iₑ+j}²u` is bounded by that of the full molecular kinetic `∑ₘ 𝐩ₘ²u`. The off-diagonal cross
term `⟪block u, rest u⟫` is a nonnegative real (`integral_cross_kinetic_eq`), so
`‖block u‖₂² ≤ ‖block u + rest u‖₂² = ‖full u‖₂²` (`integral_normSq_le_add` + W3-97). -/
lemma integral_block_kineticSq_le {N : ℕ} (iₑ : Fin N) (u : 𝓢(Space (3 * N), ℂ)) :
    ∫ x : Space (3 * N), ‖(∑ j : Fin 3, momentumCLM ⟨3 * iₑ.val + j.val, by
          have := iₑ.isLt; have := j.isLt; omega⟩
        (momentumCLM ⟨3 * iₑ.val + j.val, by have := iₑ.isLt; have := j.isLt; omega⟩ u)) x‖ ^ 2
      ≤ ∫ x : Space (3 * N), ‖(∑ m : Fin (3 * N), momentumCLM m (momentumCLM m u)) x‖ ^ 2 := by
  have hcross := integral_cross_kinetic_eq
    (fun j : Fin 3 => (⟨3 * iₑ.val + j.val, by have := iₑ.isLt; have := j.isLt; omega⟩ : Fin (3 * N)))
    (fun m : {m : Fin (3 * N) // ¬ electronCoord iₑ m} => m.1) u
  have hr : (0 : ℝ) ≤ ∑ j : Fin 3, ∑ m : {m : Fin (3 * N) // ¬ electronCoord iₑ m},
      ∫ x : Space (3 * N), ‖momentumCLM m.1 (momentumCLM (⟨3 * iₑ.val + j.val, by
          have := iₑ.isLt; have := j.isLt; omega⟩ : Fin (3 * N)) u) x‖ ^ 2 :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun m _ => integral_nonneg fun x => sq_nonneg _
  have hle := integral_normSq_le_add _ _ hr hcross
  rwa [← fullKinetic_eq_block_add_rest iₑ u] at hle

/-- **lintegral↔Bochner bridge for `‖g‖²`** (general Schwartz version of `lintegral_coulombSq_center_eq`):
`∫⁻ (ofReal ‖g x‖)² = ENNReal.ofReal (∫ ‖g x‖²)`. Lets the Bochner-form kinetic partial≤full
(`integral_block_kineticSq_le`) transfer into the lower-integral world where the params-Minkowski
reassembly lives. -/
lemma lintegral_ofReal_normSq_eq {d : ℕ} (g : 𝓢(Space d, ℂ)) :
    ∫⁻ x : Space d, (ENNReal.ofReal ‖g x‖) ^ 2
      = ENNReal.ofReal (∫ x : Space d, ‖g x‖ ^ 2) := by
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_normSq_schwartz_gen g)
    (Filter.Eventually.of_forall fun x => by positivity)]
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_pow (by positivity)]

open QuantumMechanics in
/-- **Kinetic partial ≤ full (lintegral form).** The lower-integral version of `integral_block_kineticSq_le`,
obtained by transferring the Bochner bound through the `‖g‖²` lintegral↔Bochner bridge
(`lintegral_ofReal_normSq_eq`) and `ENNReal.ofReal_le_ofReal`. This is the form consumed by the
params-Minkowski reassembly (route B): it bounds `∫⁻_z Kᶠ⁻` (W3-91) by `∫⁻` of the full molecular kinetic. -/
lemma lintegral_block_kineticSq_le {N : ℕ} (iₑ : Fin N) (u : 𝓢(Space (3 * N), ℂ)) :
    ∫⁻ x : Space (3 * N), (ENNReal.ofReal ‖(∑ j : Fin 3, momentumCLM ⟨3 * iₑ.val + j.val, by
          have := iₑ.isLt; have := j.isLt; omega⟩
        (momentumCLM ⟨3 * iₑ.val + j.val, by have := iₑ.isLt; have := j.isLt; omega⟩ u)) x‖) ^ 2
      ≤ ∫⁻ x : Space (3 * N), (ENNReal.ofReal ‖(∑ m : Fin (3 * N),
          momentumCLM m (momentumCLM m u)) x‖) ^ 2 := by
  rw [lintegral_ofReal_normSq_eq, lintegral_ofReal_normSq_eq]
  exact ENNReal.ofReal_le_ofReal (integral_block_kineticSq_le iₑ u)

/-- **√↔`(∫⁻)^½` glue for Schwartz L²:** `ofReal(√(∫‖g‖²)) = (∫⁻(ofReal‖g‖)²)^(1/2)`. Bridges the
Bochner-side square-root norms produced by `exists_coulomb_relbound_center` with the lower-integral
`(1/2)`-powers the lintegral-Minkowski reassembly (`ENNReal.lintegral_Lp_add_le`) works in. -/
lemma sqrt_integral_normSq_eq_rpow {d : ℕ} (g : 𝓢(Space d, ℂ)) :
    ENNReal.ofReal (Real.sqrt (∫ y : Space d, ‖g y‖ ^ 2))
      = (∫⁻ y : Space d, (ENNReal.ofReal ‖g y‖) ^ 2) ^ (1 / 2 : ℝ) := by
  rw [lintegral_ofReal_normSq_eq, Real.sqrt_eq_rpow,
    ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun y => sq_nonneg _) (by norm_num)]

open QuantumMechanics in
/-- **Fiberwise Coulomb bound in the `(A⁻+B⁻)²` shape** the `z`-Minkowski consumes. For a fiber
`v = fiberSchwartz iₑ z u`, the inner `Space 3` lower integral of the center-`R` Coulomb density is
bounded by `(ofReal ε · (∫⁻‖kin v‖²)^½ + ofReal C · (∫⁻‖v‖²)^½)²`. Combines the per-fiber squared bound
(`lintegral_coulombSq_center_le`, W3-86) applied to the Bochner center-`R` bound (`hbound`, from
`exists_coulomb_relbound_center`) with the √↔`(∫⁻)^½` glue (W3-102). -/
lemma coulombSq_fiber_le {N : ℕ} (iₑ : Fin N) (R : Space 3) {ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hbound : ∀ (v : 𝓢(Space 3, ℂ)) (R : Space 3),
      Real.sqrt (∫ y : Space 3, (‖y - R‖⁻¹ * ‖v y‖) ^ 2)
        ≤ ε * Real.sqrt (∫ y : Space 3, ‖(∑ i, momentumCLM i (momentumCLM i v)) y‖ ^ 2)
          + C * Real.sqrt (∫ y : Space 3, ‖v y‖ ^ 2))
    (z : {k // ¬ electronCoord iₑ k} → ℝ) (u : 𝓢(Space (3 * N), ℂ)) :
    ∫⁻ y : Space 3, (ENNReal.ofReal (‖y - R‖⁻¹ * ‖fiberSchwartz iₑ z u y‖)) ^ 2
      ≤ (ENNReal.ofReal ε * (∫⁻ y : Space 3, (ENNReal.ofReal
            ‖(∑ i, momentumCLM i (momentumCLM i (fiberSchwartz iₑ z u))) y‖) ^ 2) ^ (1 / 2 : ℝ)
          + ENNReal.ofReal C * (∫⁻ y : Space 3, (ENNReal.ofReal
            ‖fiberSchwartz iₑ z u y‖) ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := by
  refine le_trans (lintegral_coulombSq_center_le (mul_nonneg hε (Real.sqrt_nonneg _))
    (mul_nonneg hC (Real.sqrt_nonneg _)) (hbound (fiberSchwartz iₑ z u) R)) (le_of_eq ?_)
  rw [ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul hε, ENNReal.ofReal_mul hC,
    sqrt_integral_normSq_eq_rpow, sqrt_integral_normSq_eq_rpow]

/-- **Constant-pull through the `(1/2)`-power lower integral:** `(∫⁻ (c·f^½)²)^½ = c·(∫⁻ f)^½` for a
finite constant `c`. The reassembly step that turns each Minkowski summand `(∫⁻_z (A⁻ z)²)^½` (with
`A⁻ z = ofReal ε · Kᶠ(z)^½`) into `ofReal ε · (∫⁻_z Kᶠ)^½`. Applied twice (ε·kinetic, C·L²). -/
lemma rpow_half_lintegral_const_mul {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {c : ENNReal} (hc : c ≠ ⊤) (f : α → ENNReal) :
    (∫⁻ z, (c * (f z) ^ (1 / 2 : ℝ)) ^ 2 ∂μ) ^ (1 / 2 : ℝ)
      = c * (∫⁻ z, f z ∂μ) ^ (1 / 2 : ℝ) := by
  have hpt : ∀ z, (c * (f z) ^ (1 / 2 : ℝ)) ^ 2 = c ^ 2 * f z := by
    intro z
    rw [mul_pow, ← ENNReal.rpow_natCast ((f z) ^ (1 / 2 : ℝ)) 2, ← ENNReal.rpow_mul]
    norm_num
  simp_rw [hpt]
  rw [MeasureTheory.lintegral_const_mul' _ _ (ENNReal.pow_ne_top hc),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ENNReal.rpow_natCast c 2, ← ENNReal.rpow_mul]
  norm_num

/-- **The fiber `L²`-density lower integral is measurable in the spectator `z`.** `z ↦ ∫⁻_y (ofReal‖fiber
w y‖)²` is measurable — the joint measurability of `(z, y) ↦ w ((molecularSplitEquiv iₑ).symm (y, z))`
(Schwartz `w` continuous, split-equiv measurable) integrated out via `Measurable.lintegral_prod_right'`.
Supplies the `AEMeasurable` hypotheses for the `z`-Minkowski step (used for both `Mᶠ`, `w = u`, and `Kᶠ`,
`w = ∑𝐩²u` via W3-90). -/
lemma measurable_fiber_lintegral {N : ℕ} (iₑ : Fin N) (w : 𝓢(Space (3 * N), ℂ)) :
    Measurable (fun z : {k // ¬ electronCoord iₑ k} → ℝ =>
      ∫⁻ y : Space 3, (ENNReal.ofReal ‖fiberSchwartz iₑ z w y‖) ^ 2) := by
  apply Measurable.lintegral_prod_right'
    (f := fun p : ({k // ¬ electronCoord iₑ k} → ℝ) × Space 3 =>
      (ENNReal.ofReal ‖fiberSchwartz iₑ p.1 w p.2‖) ^ 2)
  refine (ENNReal.measurable_ofReal.comp (Measurable.norm ?_)).pow_const 2
  have hpt : (fun p : ({k // ¬ electronCoord iₑ k} → ℝ) × Space 3 => fiberSchwartz iₑ p.1 w p.2)
      = fun p => w ((molecularSplitEquiv iₑ).symm (p.2, p.1)) := by
    funext p; exact fiberSchwartz_apply iₑ p.1 w p.2
  rw [hpt]
  exact (SchwartzMap.continuous w).measurable.comp
    ((molecularSplitEquiv iₑ).symm.measurable.comp measurable_swap)

open QuantumMechanics in
/-- **Spectator-integrated fiber kinetic ≤ full molecular kinetic (`∫⁻` form).** `∫⁻_z Kᶠ(z) ≤
∫⁻_{3N}(ofReal‖∑ₘ𝐩ₘ²u‖)²`: the `Kᶠ` Fubini-reverse (`molecular_kineticSq_lintegral`, W3-91) collapses
the spectator integral to the molecular block-kinetic `∫⁻`, then the kinetic partial≤full
(`lintegral_block_kineticSq_le`, W3-101) bounds it by the full kinetic. -/
lemma lintegral_z_fiberKineticSq_le {N : ℕ} (iₑ : Fin N) (u : 𝓢(Space (3 * N), ℂ)) :
    ∫⁻ z : {k // ¬ electronCoord iₑ k} → ℝ, (∫⁻ y : Space 3, (ENNReal.ofReal
        ‖(∑ j, momentumCLM j (momentumCLM j (fiberSchwartz iₑ z u))) y‖) ^ 2)
      ≤ ∫⁻ x : Space (3 * N), (ENNReal.ofReal
        ‖(∑ m : Fin (3 * N), momentumCLM m (momentumCLM m u)) x‖) ^ 2 := by
  rw [molecular_kineticSq_lintegral iₑ u]
  exact lintegral_block_kineticSq_le iₑ u

open QuantumMechanics in
/-- **Per-term molecular Coulomb relative bound (ENNReal `(1/2)`-power form).** For every `ε > 0`'s
uniform fiber constant `C` (via `hbound = exists_coulomb_relbound_center`), a single molecular Coulomb
term whose center `Rf` is a measurable function of the spectator coordinates (nuclear: `Rf = const`
nucleus; e-e: `Rf` = electron-`j` position, fixed within electron-`iₑ`'s fiber) satisfies
`‖V·u‖₂ ≤ ε‖∑ₘ𝐩ₘ²u‖₂ + C‖u‖₂` in the lower-integral `(1/2)`-power form. Assembles the fiber Fubini
(W3-108), the fiberwise `(A+B)²` bound (W3-103, at fixed center `Rf z`), lintegral Minkowski
(`ENNReal.lintegral_Lp_add_le`), the constant-pull (W3-104), the kinetic partial≤full collapse (W3-106),
and the `L²` Fubini (W3-87). -/
lemma coulombTerm_relbound_enn {N : ℕ} (iₑ : Fin N)
    (Rf : ({k // ¬ electronCoord iₑ k} → ℝ) → Space 3) (hRf : Measurable Rf)
    {ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hbound : ∀ (v : 𝓢(Space 3, ℂ)) (R : Space 3),
      Real.sqrt (∫ y : Space 3, (‖y - R‖⁻¹ * ‖v y‖) ^ 2)
        ≤ ε * Real.sqrt (∫ y : Space 3, ‖(∑ i, momentumCLM i (momentumCLM i v)) y‖ ^ 2)
          + C * Real.sqrt (∫ y : Space 3, ‖v y‖ ^ 2))
    (u : 𝓢(Space (3 * N), ℂ)) :
    (∫⁻ x : Space (3 * N),
        (ENNReal.ofReal (‖electronPos x iₑ - Rf (molecularSplitMap iₑ x).2‖⁻¹ * ‖u x‖)) ^ 2) ^ (1 / 2 : ℝ)
      ≤ ENNReal.ofReal ε * (∫⁻ x : Space (3 * N),
            (ENNReal.ofReal ‖(∑ m, momentumCLM m (momentumCLM m u)) x‖) ^ 2) ^ (1 / 2 : ℝ)
        + ENNReal.ofReal C * (∫⁻ x : Space (3 * N), (ENNReal.ofReal ‖u x‖) ^ 2) ^ (1 / 2 : ℝ) := by
  set K : ({k // ¬ electronCoord iₑ k} → ℝ) → ENNReal := fun z =>
    ∫⁻ y : Space 3, (ENNReal.ofReal
      ‖(∑ i, momentumCLM i (momentumCLM i (fiberSchwartz iₑ z u))) y‖) ^ 2 with hK
  set M : ({k // ¬ electronCoord iₑ k} → ℝ) → ENNReal := fun z =>
    ∫⁻ y : Space 3, (ENNReal.ofReal ‖fiberSchwartz iₑ z u y‖) ^ 2 with hM
  have hpow : ∀ x : ENNReal, x ^ (2 : ℝ) = x ^ 2 := fun x => by
    rw [← ENNReal.rpow_natCast x 2]; norm_num
  have hKm : Measurable K := by
    rw [hK]; simp_rw [kineticSq_fiberSchwartz]; exact measurable_fiber_lintegral iₑ _
  have hMm : Measurable M := measurable_fiber_lintegral iₑ u
  have hAm : AEMeasurable (fun z => ENNReal.ofReal ε * (K z) ^ (1 / 2 : ℝ)) := by fun_prop
  have hBm : AEMeasurable (fun z => ENNReal.ofReal C * (M z) ^ (1 / 2 : ℝ)) := by fun_prop
  calc (∫⁻ x : Space (3 * N),
          (ENNReal.ofReal (‖electronPos x iₑ - Rf (molecularSplitMap iₑ x).2‖⁻¹ * ‖u x‖)) ^ 2) ^ (1 / 2 : ℝ)
      = (∫⁻ z, ∫⁻ y : Space 3,
          (ENNReal.ofReal (‖y - Rf z‖⁻¹ * ‖fiberSchwartz iₑ z u y‖)) ^ 2) ^ (1 / 2 : ℝ) := by
        rw [molecular_coulombTerm_lintegral_var iₑ Rf hRf (SchwartzMap.continuous u).measurable]
        simp_rw [← fiberSchwartz_apply]
    _ ≤ (∫⁻ z, (ENNReal.ofReal ε * (K z) ^ (1 / 2 : ℝ)
          + ENNReal.ofReal C * (M z) ^ (1 / 2 : ℝ)) ^ 2) ^ (1 / 2 : ℝ) := by
        refine ENNReal.rpow_le_rpow (lintegral_mono fun z => ?_) (by norm_num)
        rw [hK, hM]; exact coulombSq_fiber_le iₑ (Rf z) hε hC hbound z u
    _ ≤ (∫⁻ z, (ENNReal.ofReal ε * (K z) ^ (1 / 2 : ℝ)) ^ 2) ^ (1 / 2 : ℝ)
          + (∫⁻ z, (ENNReal.ofReal C * (M z) ^ (1 / 2 : ℝ)) ^ 2) ^ (1 / 2 : ℝ) := by
        have h := ENNReal.lintegral_Lp_add_le (μ := volume)
          (f := fun z => ENNReal.ofReal ε * (K z) ^ (1 / 2 : ℝ))
          (g := fun z => ENNReal.ofReal C * (M z) ^ (1 / 2 : ℝ)) hAm hBm one_le_two
        simpa only [Pi.add_apply, hpow] using h
    _ = ENNReal.ofReal ε * (∫⁻ z, K z) ^ (1 / 2 : ℝ)
          + ENNReal.ofReal C * (∫⁻ z, M z) ^ (1 / 2 : ℝ) := by
        rw [rpow_half_lintegral_const_mul ENNReal.ofReal_ne_top K,
          rpow_half_lintegral_const_mul ENNReal.ofReal_ne_top M]
    _ ≤ ENNReal.ofReal ε * (∫⁻ x : Space (3 * N),
            (ENNReal.ofReal ‖(∑ m, momentumCLM m (momentumCLM m u)) x‖) ^ 2) ^ (1 / 2 : ℝ)
          + ENNReal.ofReal C * (∫⁻ x : Space (3 * N), (ENNReal.ofReal ‖u x‖) ^ 2) ^ (1 / 2 : ℝ) := by
        refine add_le_add ?_ (le_of_eq ?_)
        · gcongr
          simp only [hK]
          exact lintegral_z_fiberKineticSq_le iₑ u
        · simp only [hM]
          simp_rw [fiberSchwartz_apply]
          rw [← molecular_normSq_lintegral iₑ (SchwartzMap.continuous u).measurable]

/-- The **other electron's position as a spectator-coordinate function.** For `j ≠ i`, electron `j`'s
three coordinates all lie outside electron `i`'s block, so `electronPos x j` depends only on the
spectator part `(molecularSplitMap i x).2`. This packages that dependence (`otherElectronPos_eq`), so the
electron–electron Coulomb term `‖eᵢ − eⱼ‖⁻¹` fits the spectator-dependent-center form of
`coulombTerm_relbound_enn` (its center is fixed *within* electron `i`'s fiber). -/
def otherElectronPos {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    ({k // ¬ electronCoord i k} → ℝ) → Space 3 :=
  fun spec => ⟨fun a : Fin 3 => spec ⟨⟨3 * j.val + a.val, by have := j.isLt; have := a.isLt; omega⟩, by
    show ¬ (3 * j.val + a.val) / 3 = i.val
    have hji : (3 * j.val + a.val) / 3 = j.val := by have := a.isLt; omega
    rw [hji]; exact fun h => hij (Fin.ext h.symm)⟩⟩

/-- **`otherElectronPos` recovers electron `j`'s position:** `otherElectronPos i j hij (spectator of x) =
electronPos x j` (for `j ≠ i`). The e-e term `‖electronPos x i − electronPos x j‖⁻¹` is therefore exactly
`‖electronPos x i − Rf ((molecularSplitMap i x).2)‖⁻¹` with `Rf = otherElectronPos i j hij`. -/
lemma otherElectronPos_eq {N : ℕ} (i j : Fin N) (hij : i ≠ j) (x : Space (3 * N)) :
    otherElectronPos i j hij (molecularSplitMap i x).2 = electronPos x j := by
  rw [molecularSplitMap_snd]; rfl

/-- **`otherElectronPos` is measurable** (each output coordinate is a coordinate projection of the
spectator input). Supplies the `hRf` hypothesis for the e-e instance of `coulombTerm_relbound_enn`. -/
lemma measurable_otherElectronPos {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    Measurable (otherElectronPos i j hij) :=
  Space.mk_continuous.measurable.comp
    (measurable_pi_lambda _ (fun _ => measurable_pi_apply _))

/-- **The `(1/2)`-power lower integral is exactly the `L²` seminorm `eLpNorm · 2`.** Bridges the raw
`(∫⁻(ofReal‖g‖)²)^½` form of the per-term Coulomb bounds (`coulombTerm_relbound_enn`) into `eLpNorm`, where
Mathlib's finite-sum Minkowski (`eLpNorm_sum_le`) and the `L²` Hilbert-norm identity live — the entry point
for the finite-sum-over-terms and the operator-level relative bound. -/
lemma lintegral_ofReal_normSq_rpow_eq_eLpNorm {d : ℕ} (g : Space d → ℂ) :
    (∫⁻ x : Space d, (ENNReal.ofReal ‖g x‖) ^ 2) ^ (1 / 2 : ℝ) = eLpNorm g 2 volume := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [ofReal_norm, ← ENNReal.rpow_natCast (‖g x‖ₑ) 2]
  norm_num

open QuantumMechanics in
/-- **Per-term molecular Coulomb relative bound, `eLpNorm` form.** The `eLpNorm` (L² seminorm)
version of `coulombTerm_relbound_enn`: multiplication by a single Coulomb factor
`x ↦ ‖eᵢ − Rf(spectator)‖⁻¹` is `(ε, C)`-relatively bounded with respect to the full kinetic operator,
`‖Vₜ·u‖₂ ≤ ε‖∑ₘ𝐩ₘ²u‖₂ + C‖u‖₂`. Obtained by rewriting all three `eLpNorm`s to `(1/2)`-power lower
integrals (`lintegral_ofReal_normSq_rpow_eq_eLpNorm`), reducing the multiplied factor's norm
`‖(r:ℝ)•u x‖ = r‖u x‖` (`norm_smul`, `r ≥ 0`), and applying `coulombTerm_relbound_enn`. This is the
per-term summand of the finite-sum molecular potential bound. -/
lemma coulombTerm_relbound_eLpNorm {N : ℕ} (iₑ : Fin N)
    (Rf : ({k // ¬ electronCoord iₑ k} → ℝ) → Space 3) (hRf : Measurable Rf)
    {ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hbound : ∀ (v : 𝓢(Space 3, ℂ)) (R : Space 3),
      Real.sqrt (∫ y : Space 3, (‖y - R‖⁻¹ * ‖v y‖) ^ 2)
        ≤ ε * Real.sqrt (∫ y : Space 3, ‖(∑ i, momentumCLM i (momentumCLM i v)) y‖ ^ 2)
          + C * Real.sqrt (∫ y : Space 3, ‖v y‖ ^ 2))
    (u : 𝓢(Space (3 * N), ℂ)) :
    eLpNorm (fun x => (‖electronPos x iₑ - Rf (molecularSplitMap iₑ x).2‖⁻¹ : ℝ) • u x) 2 volume
      ≤ ENNReal.ofReal ε * eLpNorm (fun x => (∑ m, momentumCLM m (momentumCLM m u)) x) 2 volume
        + ENNReal.ofReal C * eLpNorm (fun x => u x) 2 volume := by
  rw [← lintegral_ofReal_normSq_rpow_eq_eLpNorm
        (fun x => (‖electronPos x iₑ - Rf (molecularSplitMap iₑ x).2‖⁻¹ : ℝ) • u x),
      ← lintegral_ofReal_normSq_rpow_eq_eLpNorm (fun x => (∑ m, momentumCLM m (momentumCLM m u)) x),
      ← lintegral_ofReal_normSq_rpow_eq_eLpNorm (fun x => u x)]
  have hL : (fun x : Space (3 * N) => (ENNReal.ofReal
        ‖(‖electronPos x iₑ - Rf (molecularSplitMap iₑ x).2‖⁻¹ : ℝ) • u x‖) ^ 2)
      = fun x => (ENNReal.ofReal
        (‖electronPos x iₑ - Rf (molecularSplitMap iₑ x).2‖⁻¹ * ‖u x‖)) ^ 2 := by
    funext x
    rw [Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hL]
  exact coulombTerm_relbound_enn iₑ Rf hRf hε hC hbound u

open QuantumMechanics in
/-- **Scaled per-term Coulomb relative bound (`eLpNorm`, complex-scalar form).** A coefficient-`c`
multiple of a single Coulomb term satisfies `‖c·Vₜ·u‖₂ ≤ |c|·(ε‖∑ₘ𝐩ₘ²u‖₂ + C‖u‖₂)`. The complex-scalar
`(c:ℂ) • (Vₜ·u)` form (rather than `(cVₜ:ℝ) • u`) matches `potentialOperator = 𝓜(ofReal∘potential)` and
sidesteps the missing `NormSMulClass ℝ ℂ` instance; `eLpNorm_const_smul` (𝕜 = ℂ) pulls the scalar out.
This is the finite-sum summand: each nuclear term has `c = ±Zₖ`, each e-e term `c = ±1`. -/
lemma coulombTerm_relbound_eLpNorm_smul {N : ℕ} (iₑ : Fin N)
    (Rf : ({k // ¬ electronCoord iₑ k} → ℝ) → Space 3) (hRf : Measurable Rf) (c : ℝ)
    {ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hbound : ∀ (v : 𝓢(Space 3, ℂ)) (R : Space 3),
      Real.sqrt (∫ y : Space 3, (‖y - R‖⁻¹ * ‖v y‖) ^ 2)
        ≤ ε * Real.sqrt (∫ y : Space 3, ‖(∑ i, momentumCLM i (momentumCLM i v)) y‖ ^ 2)
          + C * Real.sqrt (∫ y : Space 3, ‖v y‖ ^ 2))
    (u : 𝓢(Space (3 * N), ℂ)) :
    eLpNorm (fun x => (c : ℂ) •
        ((‖electronPos x iₑ - Rf (molecularSplitMap iₑ x).2‖⁻¹ : ℝ) • u x)) 2 volume
      ≤ ENNReal.ofReal |c| * (ENNReal.ofReal ε *
            eLpNorm (fun x => (∑ m, momentumCLM m (momentumCLM m u)) x) 2 volume
          + ENNReal.ofReal C * eLpNorm (fun x => u x) 2 volume) := by
  rw [show (fun x => (c : ℂ) •
        ((‖electronPos x iₑ - Rf (molecularSplitMap iₑ x).2‖⁻¹ : ℝ) • u x))
      = (c : ℂ) • fun x => (‖electronPos x iₑ - Rf (molecularSplitMap iₑ x).2‖⁻¹ : ℝ) • u x from rfl,
    eLpNorm_const_smul, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
  gcongr
  exact coulombTerm_relbound_eLpNorm iₑ Rf hRf hε hC hbound u

open QuantumMechanics in
/-- **Nuclear-attraction part of the molecular Coulomb relative bound (`eLpNorm`).** The sum of all
electron–nucleus terms `∑ᵢₖ (−Zₖ)·‖eᵢ−Rₖ‖⁻¹·u` is `(∑ᵢₖ|Zₖ|)`-times-`(ε,C)` relatively bounded. Nested
`eLpNorm_sum_le` over electrons `i` and nuclei `p`, each term bounded by the scaled per-term bound
(`coulombTerm_relbound_eLpNorm_smul` with `Rf = const p.1`, `c = −p.2`), then the coefficient sum factors. -/
lemma coulomb_relbound_nuclear {N : ℕ} (nuclei : Finset (Space 3 × ℝ)) {ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hbound : ∀ (v : 𝓢(Space 3, ℂ)) (R : Space 3),
      Real.sqrt (∫ y : Space 3, (‖y - R‖⁻¹ * ‖v y‖) ^ 2)
        ≤ ε * Real.sqrt (∫ y : Space 3, ‖(∑ i, momentumCLM i (momentumCLM i v)) y‖ ^ 2)
          + C * Real.sqrt (∫ y : Space 3, ‖v y‖ ^ 2))
    (u : 𝓢(Space (3 * N), ℂ)) :
    eLpNorm (fun x => ∑ i : Fin N, ∑ p ∈ nuclei,
        (-(p.2 : ℂ)) • ((‖electronPos x i - p.1‖⁻¹ : ℝ) • u x)) 2 volume
      ≤ (∑ _i : Fin N, ∑ p ∈ nuclei, ENNReal.ofReal |p.2|)
        * (ENNReal.ofReal ε * eLpNorm (fun x => (∑ m, momentumCLM m (momentumCLM m u)) x) 2 volume
          + ENNReal.ofReal C * eLpNorm (fun x => u x) 2 volume) := by
  have hmeas : ∀ (i : Fin N) (p : Space 3 × ℝ), AEStronglyMeasurable
      (fun x : Space (3 * N) => (-(p.2 : ℂ)) • ((‖electronPos x i - p.1‖⁻¹ : ℝ) • u x)) volume := by
    intro i p
    have heq : (fun x : Space (3 * N) => (-(p.2 : ℂ)) • ((‖electronPos x i - p.1‖⁻¹ : ℝ) • u x))
        = fun x => (-(p.2 : ℂ)) * ((↑(‖electronPos x i - p.1‖⁻¹) : ℂ) * u x) := by
      funext x; rw [smul_eq_mul, Complex.real_smul]
    rw [heq]
    exact (((Complex.measurable_ofReal.comp (coulombTerm_measurable i p.1)).mul
      (SchwartzMap.continuous u).measurable).const_mul _).aestronglyMeasurable
  have key : (fun x : Space (3 * N) => ∑ i : Fin N, ∑ p ∈ nuclei,
        (-(p.2 : ℂ)) • ((‖electronPos x i - p.1‖⁻¹ : ℝ) • u x))
      = ∑ i : Fin N, ∑ p ∈ nuclei,
        (fun x : Space (3 * N) => (-(p.2 : ℂ)) • ((‖electronPos x i - p.1‖⁻¹ : ℝ) • u x)) := by
    funext x; simp only [Finset.sum_apply]
  rw [key, Finset.sum_mul]
  refine le_trans (eLpNorm_sum_le (fun i _ => Finset.aestronglyMeasurable_sum _
    (fun p _ => hmeas i p)) one_le_two) (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine le_trans (eLpNorm_sum_le (fun p _ => hmeas i p) one_le_two) (Finset.sum_le_sum fun p _ => ?_)
  have h := coulombTerm_relbound_eLpNorm_smul i (fun _ => p.1) measurable_const (-p.2) hε hC hbound u
  rwa [abs_neg, Complex.ofReal_neg] at h

open QuantumMechanics in
/-- **Electron–repulsion part of the molecular Coulomb relative bound (`eLpNorm`).** The sum of all
electron–electron terms `∑_{i<j} ‖eᵢ−eⱼ‖⁻¹·u` is `(#pairs)`-times-`(ε,C)` relatively bounded. Same nested
`eLpNorm_sum_le` structure as the nuclear part, but each term uses the spectator center
`Rf = otherElectronPos i j` (electron `j`'s position, fixed within electron `i`'s fiber), rewritten to the
literal `‖eᵢ−eⱼ‖⁻¹` via `otherElectronPos_eq`; the coefficient is `1`. -/
lemma coulomb_relbound_ee {N : ℕ} {ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hbound : ∀ (v : 𝓢(Space 3, ℂ)) (R : Space 3),
      Real.sqrt (∫ y : Space 3, (‖y - R‖⁻¹ * ‖v y‖) ^ 2)
        ≤ ε * Real.sqrt (∫ y : Space 3, ‖(∑ i, momentumCLM i (momentumCLM i v)) y‖ ^ 2)
          + C * Real.sqrt (∫ y : Space 3, ‖v y‖ ^ 2))
    (u : 𝓢(Space (3 * N), ℂ)) :
    eLpNorm (fun x => ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (i < ·),
        (1 : ℂ) • ((‖electronPos x i - electronPos x j‖⁻¹ : ℝ) • u x)) 2 volume
      ≤ (∑ i : Fin N, ∑ _j ∈ Finset.univ.filter (i < ·), (1 : ENNReal))
        * (ENNReal.ofReal ε * eLpNorm (fun x => (∑ m, momentumCLM m (momentumCLM m u)) x) 2 volume
          + ENNReal.ofReal C * eLpNorm (fun x => u x) 2 volume) := by
  have hmeas : ∀ (i j : Fin N), AEStronglyMeasurable
      (fun x : Space (3 * N) => (1 : ℂ) • ((‖electronPos x i - electronPos x j‖⁻¹ : ℝ) • u x)) volume := by
    intro i j
    have heq : (fun x : Space (3 * N) => (1 : ℂ) • ((‖electronPos x i - electronPos x j‖⁻¹ : ℝ) • u x))
        = fun x => (1 : ℂ) * ((↑(‖electronPos x i - electronPos x j‖⁻¹) : ℂ) * u x) := by
      funext x; rw [smul_eq_mul, Complex.real_smul]
    rw [heq]
    exact (((Complex.measurable_ofReal.comp (coulombTermRel_measurable i j)).mul
      (SchwartzMap.continuous u).measurable).const_mul _).aestronglyMeasurable
  have key : (fun x : Space (3 * N) => ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (i < ·),
        (1 : ℂ) • ((‖electronPos x i - electronPos x j‖⁻¹ : ℝ) • u x))
      = ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (i < ·),
        (fun x : Space (3 * N) => (1 : ℂ) • ((‖electronPos x i - electronPos x j‖⁻¹ : ℝ) • u x)) := by
    funext x; simp only [Finset.sum_apply]
  rw [key, Finset.sum_mul]
  refine le_trans (eLpNorm_sum_le (fun i _ => Finset.aestronglyMeasurable_sum _
    (fun j _ => hmeas i j)) one_le_two) (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine le_trans (eLpNorm_sum_le (fun j _ => hmeas i j) one_le_two) (Finset.sum_le_sum fun j hj => ?_)
  have hij : i ≠ j := ne_of_lt (Finset.mem_filter.mp hj).2
  have h := coulombTerm_relbound_eLpNorm_smul i (otherElectronPos i j hij)
    (measurable_otherElectronPos i j hij) 1 hε hC hbound u
  simp_rw [otherElectronPos_eq i j hij] at h
  simpa only [Complex.ofReal_one, abs_one, ENNReal.ofReal_one] using h

open QuantumMechanics in
/-- **Full molecular Coulomb potential relative bound (`eLpNorm`, Schwartz level).** Multiplication by the
whole molecular Coulomb potential `V = −∑ᵢₖ Zₖ/‖eᵢ−Rₖ‖ + ∑_{i<j} 1/‖eᵢ−eⱼ‖` is `Ctot`-times-`(ε,C)`
relatively bounded with respect to `∑ₘ𝐩ₘ²`, where `Ctot = ∑ᵢₖ|Zₖ| + #pairs`. Decomposes `(↑V)·u` into the
nuclear and electron–repulsion function sums, splits via `eLpNorm_add_le`, and applies
`coulomb_relbound_nuclear` + `coulomb_relbound_ee`. **This is the finite-sum molecular bound — choosing `ε`
small enough that `Ctot·ε·(2m) < 1` will give the Kato `a < 1` at the operator level.** -/
lemma coulomb_relbound_schwartz {N : ℕ} (nuclei : Finset (Space 3 × ℝ)) {ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hbound : ∀ (v : 𝓢(Space 3, ℂ)) (R : Space 3),
      Real.sqrt (∫ y : Space 3, (‖y - R‖⁻¹ * ‖v y‖) ^ 2)
        ≤ ε * Real.sqrt (∫ y : Space 3, ‖(∑ i, momentumCLM i (momentumCLM i v)) y‖ ^ 2)
          + C * Real.sqrt (∫ y : Space 3, ‖v y‖ ^ 2))
    (u : 𝓢(Space (3 * N), ℂ)) :
    eLpNorm (fun x => (↑(molecularCoulombPotential nuclei x) : ℂ) * u x) 2 volume
      ≤ ((∑ _i : Fin N, ∑ p ∈ nuclei, ENNReal.ofReal |p.2|)
          + ∑ i : Fin N, ∑ _j ∈ Finset.univ.filter (i < ·), (1 : ENNReal))
        * (ENNReal.ofReal ε * eLpNorm (fun x => (∑ m, momentumCLM m (momentumCLM m u)) x) 2 volume
          + ENNReal.ofReal C * eLpNorm (fun x => u x) 2 volume) := by
  have hNmeas : AEStronglyMeasurable (fun x : Space (3 * N) => ∑ i : Fin N, ∑ p ∈ nuclei,
      (-(p.2 : ℂ)) • ((‖electronPos x i - p.1‖⁻¹ : ℝ) • u x)) volume := by
    rw [show (fun x : Space (3 * N) => ∑ i : Fin N, ∑ p ∈ nuclei,
          (-(p.2 : ℂ)) • ((‖electronPos x i - p.1‖⁻¹ : ℝ) • u x))
        = ∑ i : Fin N, ∑ p ∈ nuclei,
          fun x : Space (3 * N) => (-(p.2 : ℂ)) • ((‖electronPos x i - p.1‖⁻¹ : ℝ) • u x)
        from by funext x; simp only [Finset.sum_apply]]
    refine Finset.aestronglyMeasurable_sum _ fun i _ => Finset.aestronglyMeasurable_sum _ fun p _ => ?_
    have heq : (fun x : Space (3 * N) => (-(p.2 : ℂ)) • ((‖electronPos x i - p.1‖⁻¹ : ℝ) • u x))
        = fun x => (-(p.2 : ℂ)) * ((↑(‖electronPos x i - p.1‖⁻¹) : ℂ) * u x) := by
      funext x; rw [smul_eq_mul, Complex.real_smul]
    rw [heq]
    exact (((Complex.measurable_ofReal.comp (coulombTerm_measurable i p.1)).mul
      (SchwartzMap.continuous u).measurable).const_mul _).aestronglyMeasurable
  have hEmeas : AEStronglyMeasurable (fun x : Space (3 * N) => ∑ i : Fin N,
      ∑ j ∈ Finset.univ.filter (i < ·),
      (1 : ℂ) • ((‖electronPos x i - electronPos x j‖⁻¹ : ℝ) • u x)) volume := by
    rw [show (fun x : Space (3 * N) => ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (i < ·),
          (1 : ℂ) • ((‖electronPos x i - electronPos x j‖⁻¹ : ℝ) • u x))
        = ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (i < ·),
          fun x : Space (3 * N) => (1 : ℂ) • ((‖electronPos x i - electronPos x j‖⁻¹ : ℝ) • u x)
        from by funext x; simp only [Finset.sum_apply]]
    refine Finset.aestronglyMeasurable_sum _ fun i _ => Finset.aestronglyMeasurable_sum _ fun j _ => ?_
    have heq : (fun x : Space (3 * N) => (1 : ℂ) • ((‖electronPos x i - electronPos x j‖⁻¹ : ℝ) • u x))
        = fun x => (1 : ℂ) * ((↑(‖electronPos x i - electronPos x j‖⁻¹) : ℂ) * u x) := by
      funext x; rw [smul_eq_mul, Complex.real_smul]
    rw [heq]
    exact (((Complex.measurable_ofReal.comp (coulombTermRel_measurable i j)).mul
      (SchwartzMap.continuous u).measurable).const_mul _).aestronglyMeasurable
  have hdecomp : (fun x : Space (3 * N) => (↑(molecularCoulombPotential nuclei x) : ℂ) * u x)
      = (fun x => ∑ i : Fin N, ∑ p ∈ nuclei, (-(p.2 : ℂ)) • ((‖electronPos x i - p.1‖⁻¹ : ℝ) • u x))
        + fun x => ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (i < ·),
            (1 : ℂ) • ((‖electronPos x i - electronPos x j‖⁻¹ : ℝ) • u x) := by
    funext x
    simp only [molecularCoulombPotential, Pi.add_apply, smul_eq_mul, Complex.real_smul,
      Complex.ofReal_add, Complex.ofReal_neg, Complex.ofReal_sum, div_eq_mul_inv,
      Complex.ofReal_mul, Complex.ofReal_inv, one_mul, neg_mul, add_mul,
      Finset.sum_mul, Finset.sum_neg_distrib, mul_assoc]
  rw [hdecomp, add_mul]
  exact le_trans (eLpNorm_add_le hNmeas hEmeas one_le_two)
    (add_le_add (coulomb_relbound_nuclear nuclei hε hC hbound u)
      (coulomb_relbound_ee hε hC hbound u))

open QuantumMechanics SpaceDHilbertSpace in
/-- **L² norm of a Schwartz inclusion = its `eLpNorm`.** For `G : 𝓢`,
`‖schwartzIncl volume G‖ =
(eLpNorm ⇑G 2 volume).toReal`. The bridge from the analysis-side `eLpNorm` bounds
(`coulomb_relbound_schwartz`) to the operator-side Hilbert norms `‖potentialOperator ψ‖`,
`‖kineticOperator ψ‖`, `‖ψ‖` on `SpaceDHilbertSpace = L²`. -/
lemma norm_schwartzIncl_eq {d : ℕ} (G : 𝓢(Space d, ℂ)) :
    ‖schwartzIncl MeasureTheory.volume G‖ = (eLpNorm (⇑G) 2 volume).toReal := by
  rw [Lp.norm_def]
  congr 1
  refine eLpNorm_congr_ae ?_
  rw [← SchwartzSubmodule.schwartzEquiv_apply_coe]
  exact SchwartzSubmodule.schwartzEquiv_coe_ae G

open QuantumMechanics SpaceDHilbertSpace in
/-- **L² norm of a Schwartz vector = its `eLpNorm`.** `‖(schwartzEquiv u : L²)‖ = (eLpNorm ⇑u 2).toReal`
— the `‖x‖` factor of the Kato bound at the Schwartz core, via `norm_schwartzIncl_eq`. -/
lemma norm_schwartzEquiv_eq {d : ℕ} (u : 𝓢(Space d, ℂ)) :
    ‖(schwartzEquiv MeasureTheory.volume u : SpaceDHilbertSpace d)‖
      = (eLpNorm (⇑u) 2 volume).toReal := by
  rw [SchwartzSubmodule.schwartzEquiv_apply_coe, norm_schwartzIncl_eq]

open QuantumMechanics in
/-- **The molecular Coulomb potential times a Schwartz function is L².** `(↑V)·u ∈ L²` — the finiteness
that puts `schwartzEquiv u` in `potentialOperator.domain` (`potentialOperator = 𝓜(ofReal∘V)`, whose domain
is `{ψ | V•ψ ∈ L²}`). Crucially this uses the finite-sum relative bound (`coulomb_relbound_schwartz` at
`ε = 1`), NOT temperate growth — the Coulomb potential has `1/r` singularities and is not of temperate
growth, so the generic `mulOperator_domain_ge_of_hasTemperateGrowth` does not apply. -/
lemma memLp_molecular_coulomb {N : ℕ} (nuclei : Finset (Space 3 × ℝ)) (u : 𝓢(Space (3 * N), ℂ)) :
    MemLp (fun x => (↑(molecularCoulombPotential nuclei x) : ℂ) * u x) 2 volume := by
  refine ⟨((Complex.measurable_ofReal.comp (molecularCoulombPotential_measurable nuclei)).mul
    (SchwartzMap.continuous u).measurable).aestronglyMeasurable, ?_⟩
  obtain ⟨C, hC0, hbound⟩ := exists_coulomb_relbound_center (by norm_num : (0 : ℝ) < 1)
  refine lt_of_le_of_lt (coulomb_relbound_schwartz nuclei (by norm_num) hC0 hbound u) ?_
  refine ENNReal.mul_lt_top ?_ ?_
  · refine ENNReal.add_lt_top.mpr ⟨ENNReal.sum_lt_top.mpr fun i _ => ENNReal.sum_lt_top.mpr
      fun p _ => ENNReal.ofReal_lt_top, ENNReal.sum_lt_top.mpr fun i _ => ENNReal.sum_lt_top.mpr
      fun j _ => ENNReal.one_lt_top⟩
  · exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (SchwartzMap.memLp _ 2 volume).2, ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (SchwartzMap.memLp u 2 volume).2⟩

open QuantumMechanics SpaceDHilbertSpace in
/-- **Kinetic operator norm on a Schwartz vector.** `‖kineticOperator (schwartzEquiv u)‖ =
(2m)⁻¹·(eLpNorm (∑ᵢ𝐩ᵢ²u) 2).toReal`, since `kineticOperator = ofReal(2m)⁻¹ • momentumSqOperator`
(`smul_apply`), `momentumSqOperator (schwartzEquiv u) = schwartzIncl (∑ᵢ𝐩ᵢ²u)` (KESA
`momentumSqOperator_apply_eq`), and `norm_schwartzIncl_eq`. The `‖A x‖` side of the Kato bound at the
Schwartz core. -/
lemma norm_kineticOperator_schwartz {N : ℕ} (m : ℝ) (hm : 0 < m) (nuclei : Finset (Space 3 × ℝ))
    (u : 𝓢(Space (3 * N), ℂ))
    (hmem : (schwartzEquiv MeasureTheory.volume u : SpaceDHilbertSpace (3 * N)) ∈
      (molecularSystem N m hm nuclei).kineticOperator.domain) :
    ‖((molecularSystem N m hm nuclei).kineticOperator ⟨_, hmem⟩ : SpaceDHilbertSpace (3 * N))‖
      = (2 * m)⁻¹ * (eLpNorm (fun x => (∑ i, momentumCLM i (momentumCLM i u)) x) 2 volume).toReal := by
  show ‖(Complex.ofReal (2 * m)⁻¹ • momentumSqOperator) ⟨_, hmem⟩‖ = _
  rw [LinearPMap.smul_apply, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  congr 1
  exact (congrArg norm (momentumSqOperator_apply_eq u hmem)).trans (norm_schwartzIncl_eq _)

open QuantumMechanics SpaceDHilbertSpace in
/-- **Potential operator norm on a Schwartz vector.** `‖potentialOperator (schwartzEquiv u)‖ =
(eLpNorm ((↑V)·u) 2).toReal`, since `potentialOperator = 𝓜(ofReal∘V)` acts a.e. as multiplication
(`mulOperator_apply_ae`) and `schwartzEquiv u =ᵐ u`; then `Lp.norm_def` + `eLpNorm_congr_ae`. The `‖B x‖`
side of the Kato bound at the Schwartz core. -/
lemma norm_potentialOperator_schwartz {N : ℕ} (m : ℝ) (hm : 0 < m) (nuclei : Finset (Space 3 × ℝ))
    (u : 𝓢(Space (3 * N), ℂ))
    (hmem : (schwartzEquiv MeasureTheory.volume u : SpaceDHilbertSpace (3 * N)) ∈
      (molecularSystem N m hm nuclei).potentialOperator.domain) :
    ‖((molecularSystem N m hm nuclei).potentialOperator ⟨_, hmem⟩ : SpaceDHilbertSpace (3 * N))‖
      = (eLpNorm (fun x => (↑(molecularCoulombPotential nuclei x) : ℂ) * u x) 2 volume).toReal := by
  rw [Lp.norm_def]
  congr 1
  refine eLpNorm_congr_ae ?_
  filter_upwards [mulOperator_apply_ae (f := Complex.ofReal ∘ molecularCoulombPotential nuclei) ⟨_, hmem⟩,
    SchwartzSubmodule.schwartzEquiv_coe_ae (μ := MeasureTheory.volume) u] with x h₁ h₂
  erw [h₁]
  rw [Pi.smul_apply', smul_eq_mul, Function.comp_apply]
  -- v4.32: `erw` above leaves the goal well-typed only at default transparency
  -- (`(molecularSystem …).d` vs `3 * N`), so `rw [h₂]` cannot see the pattern; close in term mode.
  exact congrArg (fun c => (↑(molecularCoulombPotential nuclei x) : ℂ) * c) h₂

open QuantumMechanics SpaceDHilbertSpace in
/-- **The Schwartz core lies in the potential operator's domain.** `schwartzSubmodule ≤
potentialOperator.domain` — for `ψ = schwartzIncl u`, `V•ψ =ᵐ (↑V)·u ∈ L²` (`memLp_molecular_coulomb`,
transported along `schwartzEquiv_coe_ae` via `memHS_of_ae`). This is the `domain_le` field of the
Schwartz-core `IsRelBounded` (and, since `kineticOperator.domain = schwartzSubmodule`, exactly
`kineticOperator.domain ≤ potentialOperator.domain`). -/
lemma schwartz_le_potOp_domain {N : ℕ} (m : ℝ) (hm : 0 < m) (nuclei : Finset (Space 3 × ℝ)) :
    SchwartzSubmodule (3 * N) ≤ (molecularSystem N m hm nuclei).potentialOperator.domain := by
  intro ψ hψ
  obtain ⟨u, rfl⟩ := hψ
  rw [SpaceDQuantumSystem.potentialOperator_eq]
  refine mem_mulOperator_domain_iff.mpr (MemHS.ae_eq (f :=
    fun x => (↑(molecularCoulombPotential nuclei x) : ℂ) * u x) ?_
    (memLp_molecular_coulomb nuclei u))
  filter_upwards [SchwartzSubmodule.schwartzEquiv_coe_ae (μ := MeasureTheory.volume) u] with x hx
  simp only [SchwartzSubmodule.schwartzEquiv_apply_coe] at hx
  show (↑(molecularCoulombPotential nuclei x) : ℂ) * u x
      = (↑(molecularCoulombPotential nuclei x) : ℂ)
        * ((schwartzIncl MeasureTheory.volume u : SpaceDHilbertSpace (3 * N)) : Space (3 * N) → ℂ) x
  rw [hx]

open QuantumMechanics in
/-- **Real-valued (`.toReal`) molecular Coulomb relative bound.** The `ENNReal → ℝ` cast of
`coulomb_relbound_schwartz`: `‖(↑V)·u‖₂ ≤ Ctot·(ε‖∑𝐩²u‖₂ + C‖u‖₂)` with all norms as `eLpNorm·.toReal`
(the real L² norms). `Ctot` is the (finite) real coefficient sum `(∑ᵢₖ|Zₖ|) + #pairs`. This is the
mathematical content of the Kato bound at the Schwartz core, ready for the operator-norm bridges. -/
lemma coulomb_relbound_schwartz_real {N : ℕ} (nuclei : Finset (Space 3 × ℝ)) {ε C : ℝ}
    (hε0 : 0 ≤ ε) (hC0 : 0 ≤ C)
    (hbound : ∀ (v : 𝓢(Space 3, ℂ)) (R : Space 3),
      Real.sqrt (∫ y : Space 3, (‖y - R‖⁻¹ * ‖v y‖) ^ 2)
        ≤ ε * Real.sqrt (∫ y : Space 3, ‖(∑ i, momentumCLM i (momentumCLM i v)) y‖ ^ 2)
          + C * Real.sqrt (∫ y : Space 3, ‖v y‖ ^ 2))
    (u : 𝓢(Space (3 * N), ℂ)) :
    (eLpNorm (fun x => (↑(molecularCoulombPotential nuclei x) : ℂ) * u x) 2 volume).toReal
      ≤ ((∑ _i : Fin N, ∑ p ∈ nuclei, ENNReal.ofReal |p.2|)
            + ∑ i : Fin N, ∑ _j ∈ Finset.univ.filter (i < ·), (1 : ENNReal)).toReal
        * (ε * (eLpNorm (fun x => (∑ i, momentumCLM i (momentumCLM i u)) x) 2 volume).toReal
          + C * (eLpNorm (fun x => u x) 2 volume).toReal) := by
  have hKfin : eLpNorm (fun x => (∑ i, momentumCLM i (momentumCLM i u)) x) 2 volume ≠ ⊤ :=
    (SchwartzMap.memLp _ 2 volume).2.ne
  have hMfin : eLpNorm (fun x => u x) 2 volume ≠ ⊤ := (SchwartzMap.memLp u 2 volume).2.ne
  have hCtotfin : ((∑ _i : Fin N, ∑ p ∈ nuclei, ENNReal.ofReal |p.2|)
      + ∑ i : Fin N, ∑ _j ∈ Finset.univ.filter (i < ·), (1 : ENNReal)) ≠ ⊤ :=
    (ENNReal.add_lt_top.mpr ⟨ENNReal.sum_lt_top.mpr fun i _ => ENNReal.sum_lt_top.mpr
      fun p _ => ENNReal.ofReal_lt_top, ENNReal.sum_lt_top.mpr fun i _ => ENNReal.sum_lt_top.mpr
      fun j _ => ENNReal.one_lt_top⟩).ne
  have hAfin : ENNReal.ofReal ε * eLpNorm (fun x => (∑ i, momentumCLM i (momentumCLM i u)) x) 2 volume
      ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKfin
  have hBfin : ENNReal.ofReal C * eLpNorm (fun x => u x) 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hMfin
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top hCtotfin (ENNReal.add_ne_top.mpr ⟨hAfin, hBfin⟩))
    (coulomb_relbound_schwartz nuclei hε0 hC0 hbound u)).trans_eq ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_add hAfin hBfin, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hε0, ENNReal.toReal_ofReal hC0]

open QuantumMechanics SpaceDHilbertSpace in
/-- **Coulomb relative bound on the Schwartz core (`IsRelBounded`, `a < 1`).** The molecular potential is
relatively bounded w.r.t. the (un-closed) molecular kinetic operator with relative bound `a < 1`. Choosing
`ε = 1/(4m(Ctot+1))` in `exists_coulomb_relbound_center` gives `a = 2m·Ctot·ε = Ctot/(2(Ctot+1)) < ½`.
Assembles `domain_le` (`schwartz_le_potOp_domain`) with the per-vector bound: the norm bridges
(`norm_kineticOperator_schwartz`, `norm_potentialOperator_schwartz`, `norm_schwartzEquiv_eq`) reduce it to
`coulomb_relbound_schwartz_real`, with `2m·(2m)⁻¹ = 1` closing the arithmetic. -/
lemma coulomb_isRelBounded_core {N : ℕ} (m : ℝ) (hm : 0 < m) (nuclei : Finset (Space 3 × ℝ)) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < 1 ∧ 0 ≤ b ∧
      IsRelBounded (molecularSystem N m hm nuclei).kineticOperator
        (molecularSystem N m hm nuclei).potentialOperator a b := by
  have hkindom :
      (molecularSystem N m hm nuclei).kineticOperator.domain = SchwartzSubmodule (3 * N) := by
    rw [SpaceDQuantumSystem.kineticOperator_eq, LinearPMap.smul_domain]
    exact momentumSqOperator_domain_eq
  set Ctr : ℝ := ((∑ _i : Fin N, ∑ p ∈ nuclei, ENNReal.ofReal |p.2|)
      + ∑ i : Fin N, ∑ _j ∈ Finset.univ.filter (i < ·), (1 : ENNReal)).toReal with hCtr
  have hCtr0 : 0 ≤ Ctr := ENNReal.toReal_nonneg
  have hεpos : 0 < 1 / (4 * m * (Ctr + 1)) := by positivity
  obtain ⟨C, hC0, hbound⟩ := exists_coulomb_relbound_center hεpos
  refine ⟨2 * m * Ctr * (1 / (4 * m * (Ctr + 1))), Ctr * C, by positivity, ?_, by positivity,
    hkindom ▸ schwartz_le_potOp_domain m hm nuclei, ?_⟩
  · rw [mul_one_div, div_lt_one (by positivity)]
    nlinarith [hm, hCtr0]
  · intro x
    obtain ⟨u, hu⟩ : ∃ u : 𝓢(Space (3 * N), ℂ),
        (schwartzEquiv MeasureTheory.volume u : SpaceDHilbertSpace (3 * N)) = x.1 :=
      ⟨(schwartzEquiv MeasureTheory.volume).symm ⟨x.1, by rw [← hkindom]; exact x.2⟩, by
        rw [(schwartzEquiv MeasureTheory.volume).apply_symm_apply]⟩
    have hmemK : (schwartzEquiv MeasureTheory.volume u : SpaceDHilbertSpace (3 * N)) ∈
        (molecularSystem N m hm nuclei).kineticOperator.domain := by rw [hu]; exact x.2
    have hAx : ‖(molecularSystem N m hm nuclei).kineticOperator x‖
        = (2 * m)⁻¹ * (eLpNorm (fun y => (∑ i, momentumCLM i (momentumCLM i u)) y) 2 volume).toReal := by
      rw [show x = ⟨(schwartzEquiv MeasureTheory.volume u : SpaceDHilbertSpace (3 * N)), hmemK⟩
        from Subtype.ext hu.symm]
      exact norm_kineticOperator_schwartz m hm nuclei u hmemK
    have hxn : ‖(x : (molecularSystem N m hm nuclei).HS)‖ = (eLpNorm (fun y => u y) 2 volume).toReal := by
      rw [← hu]; exact norm_schwartzEquiv_eq u
    have hBx : ∀ h, ‖(molecularSystem N m hm nuclei).potentialOperator ⟨↑x, h⟩‖
        = (eLpNorm (fun y => (↑(molecularCoulombPotential nuclei y) : ℂ) * u y) 2 volume).toReal := by
      intro h
      rw [show (⟨↑x, h⟩ : (molecularSystem N m hm nuclei).potentialOperator.domain)
          = ⟨(schwartzEquiv MeasureTheory.volume u : SpaceDHilbertSpace (3 * N)),
            by rw [hu]; exact h⟩ from Subtype.ext hu.symm]
      exact norm_potentialOperator_schwartz m hm nuclei u _
    rw [hAx, hxn, hBx]
    refine (coulomb_relbound_schwartz_real nuclei hεpos.le hC0 hbound u).trans (le_of_eq ?_)
    have h2m : (2 * m) ≠ 0 := by positivity
    field_simp
    ring

open LinearPMap Filter Topology in
/-- **Relative bound extends from a core to the closure.** If `A` is closable, `B` is closed, and `B`
is `(a, b)`-relatively bounded w.r.t. `A` on `A.domain` (a core of `A.closure`), then `B` is
`(a, b)`-relatively bounded w.r.t. `A.closure`. Graph-limit argument: for `x ∈ A.closure.domain` pick
`φₙ ∈ A.domain` with `(φₙ, Aφₙ) → (x, A.closure x)`; the core bound makes `Bφₙ` Cauchy, so `Bφₙ → z`,
and since `B` is closed `(x, z) ∈ B.graph`, giving `x ∈ B.domain`, `B x = z`, and
`‖B x‖ = lim‖Bφₙ‖ ≤ lim(a‖Aφₙ‖ + b‖φₙ‖) = a‖A.closure x‖ + b‖x‖`. Mathlib lacks this lemma; in-tree
closure-extension keystone for the Kato–Rellich `hrel` discharge. -/
lemma IsRelBounded.extend_to_closure {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {A B : H →ₗ.[ℂ] H} (hAcl : A.IsClosable) (hBcl : B.IsClosed)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hrel : IsRelBounded A B a b) :
    IsRelBounded A.closure B a b := by
  have key : ∀ x : A.closure.domain, ∃ hxB : (↑x : H) ∈ B.domain,
      ‖B ⟨↑x, hxB⟩‖ ≤ a * ‖A.closure x‖ + b * ‖(↑x : H)‖ := by
    intro x
    have hmem : ((↑x : H), (A.closure x : H)) ∈ closure (↑A.graph : Set (H × H)) := by
      have hg := A.closure.mem_graph x
      rw [← hAcl.graph_closure_eq_closure_graph, ← SetLike.mem_coe,
        Submodule.topologicalClosure_coe] at hg
      exact hg
    obtain ⟨p, hp_mem, hp_tend⟩ := mem_closure_iff_seq_limit.mp hmem
    choose φ hφ1 hφ2 using fun n => (mem_graph_iff A).mp (hp_mem n)
    have htend1 : Tendsto (fun n => (↑(φ n) : H)) atTop (𝓝 (↑x : H)) := by
      simp_rw [hφ1]; exact (continuous_fst.tendsto _).comp hp_tend
    have htend2 : Tendsto (fun n => (A (φ n) : H)) atTop (𝓝 (A.closure x : H)) := by
      simp_rw [hφ2]; exact (continuous_snd.tendsto _).comp hp_tend
    set Bφ : ℕ → H := fun n => B ⟨↑(φ n), hrel.domain_le (φ n).2⟩ with hBφdef
    have hbnd : ∀ n m, ‖Bφ n - Bφ m‖ ≤ a * ‖(A (φ n) : H) - A (φ m)‖ + b * ‖(↑(φ n) : H) - ↑(φ m)‖ := by
      intro n m
      have hb2 := hrel.bound (φ n - φ m)
      have heq : (B ⟨(↑(φ n - φ m) : H), hrel.domain_le (φ n - φ m).2⟩ : H) = Bφ n - Bφ m := by
        rw [hBφdef, ← LinearPMap.map_sub]; congr 1
      rw [heq, LinearPMap.map_sub, Submodule.coe_sub] at hb2
      exact hb2
    have hBφ_cauchy : CauchySeq Bφ := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N1, hN1⟩ := Metric.cauchySeq_iff.mp htend2.cauchySeq (ε / 2 / (a + 1)) (by positivity)
      obtain ⟨N2, hN2⟩ := Metric.cauchySeq_iff.mp htend1.cauchySeq (ε / 2 / (b + 1)) (by positivity)
      refine ⟨max N1 N2, fun n hn m hm => ?_⟩
      rw [dist_eq_norm]
      have h1 := hN1 n (le_trans (le_max_left _ _) hn) m (le_trans (le_max_left _ _) hm)
      have h2 := hN2 n (le_trans (le_max_right _ _) hn) m (le_trans (le_max_right _ _) hm)
      rw [dist_eq_norm] at h1 h2
      have hab := hbnd n m
      have hae : a * ‖(A (φ n) : H) - A (φ m)‖ < ε / 2 := by
        have hlt : a / (a + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
        calc a * ‖(A (φ n) : H) - A (φ m)‖ ≤ a * (ε / 2 / (a + 1)) :=
              mul_le_mul_of_nonneg_left h1.le ha
          _ = (a / (a + 1)) * (ε / 2) := by ring
          _ < 1 * (ε / 2) := mul_lt_mul_of_pos_right hlt (by positivity)
          _ = ε / 2 := one_mul _
      have hbe : b * ‖(↑(φ n) : H) - ↑(φ m)‖ < ε / 2 := by
        have hlt : b / (b + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
        calc b * ‖(↑(φ n) : H) - ↑(φ m)‖ ≤ b * (ε / 2 / (b + 1)) :=
              mul_le_mul_of_nonneg_left h2.le hb
          _ = (b / (b + 1)) * (ε / 2) := by ring
          _ < 1 * (ε / 2) := mul_lt_mul_of_pos_right hlt (by positivity)
          _ = ε / 2 := one_mul _
      linarith
    obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hBφ_cauchy
    have hxz : ((↑x : H), z) ∈ B.graph := by
      -- v4.32: `hBcl.closure_eq` now resolves to `LinearPMap.IsClosed.closure_eq`
      -- (`B.closure = B`); pin the *topological* `IsClosed.closure_eq` by ascribing the type.
      have hBset : _root_.IsClosed (↑B.graph : Set (H × H)) := hBcl
      rw [← SetLike.mem_coe, ← hBset.closure_eq]
      refine mem_closure_iff_seq_limit.mpr ⟨fun n => (↑(φ n), Bφ n), fun n => ?_, ?_⟩
      · rw [SetLike.mem_coe, mem_graph_iff]
        exact ⟨⟨↑(φ n), hrel.domain_le (φ n).2⟩, rfl, rfl⟩
      · exact htend1.prodMk_nhds hz
    rw [mem_graph_iff] at hxz
    obtain ⟨ψ, hψ1, hψ2⟩ := hxz
    have hψ1' : (↑ψ : H) = ↑x := hψ1
    have hψ2' : (B ψ : H) = z := hψ2
    refine ⟨hψ1' ▸ ψ.2, ?_⟩
    have hBz : ‖B ⟨↑x, hψ1' ▸ ψ.2⟩‖ = ‖z‖ := by
      rw [show (⟨↑x, hψ1' ▸ ψ.2⟩ : B.domain) = ψ from Subtype.ext hψ1'.symm, hψ2']
    rw [hBz]
    have hR_tend : Tendsto (fun n => a * ‖(A (φ n) : H)‖ + b * ‖(↑(φ n) : H)‖) atTop
        (𝓝 (a * ‖(A.closure x : H)‖ + b * ‖(↑x : H)‖)) :=
      (htend2.norm.const_mul a).add (htend1.norm.const_mul b)
    exact le_of_tendsto_of_tendsto' hz.norm hR_tend (fun n => hrel.bound (φ n))
  exact ⟨fun y hy => (key ⟨y, hy⟩).choose, fun x => (key x).choose_spec⟩

open QuantumMechanics SpaceDHilbertSpace MeasureTheory in
/-- **The molecular Coulomb potential is relatively bounded w.r.t. the CLOSED molecular kinetic
operator, with `a < 1` (the `hrel` discharge).** Combines the Schwartz-core relative bound
(`coulomb_isRelBounded_core`) with the closure-extension keystone (`IsRelBounded.extend_to_closure`):
`kineticOperator` is closable (symmetric + dense-domain `momentumSqOperator`, scaled), and
`potentialOperator = 𝓜(ofReal∘V)` is closed (self-adjoint, since `V` is real). This is exactly the
`hrel` hypothesis of `molecularHamiltonian_essSelfAdjoint`, now a **proven theorem**. -/
lemma coulomb_isRelBounded {N : ℕ} (m : ℝ) (hm : 0 < m) (nuclei : Finset (Space 3 × ℝ)) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < 1 ∧ 0 ≤ b ∧
      IsRelBounded (molecularSystem N m hm nuclei).kineticOperator.closure
        (molecularSystem N m hm nuclei).potentialOperator a b := by
  obtain ⟨a, b, ha0, ha1, hb0, hcore⟩ := coulomb_isRelBounded_core m hm nuclei
  have hAcl : (molecularSystem N m hm nuclei).kineticOperator.IsClosable :=
    (momentumSqOperator_isSymmetric.isClosable momentumSqOperator_hasDenseDomain).smul
      (Complex.ofReal (2 * m)⁻¹)
  have hBcl : (molecularSystem N m hm nuclei).potentialOperator.IsClosed := by
    refine (mulOperator_isSelfAdjoint_ofReal (μ := MeasureTheory.volume)
      ((Complex.measurable_ofReal.comp
        (molecularCoulombPotential_measurable nuclei)).aestronglyMeasurable)
      ?_).isClosed
    funext x
    exact Complex.conj_ofReal _
  exact ⟨a, b, ha0, ha1, hb0, hcore.extend_to_closure hAcl hBcl ha0 hb0⟩

open QuantumMechanics in
/-- **The N-electron molecular Coulomb Hamiltonian is essentially self-adjoint — FULLY
UNCONDITIONAL.** All three analytic hypotheses are now discharged as proven theorems: `hkin`
(`kineticOperator_isSelfAdjoint_closure`), `hpot` (`molecularPotentialOperator_isSymmetric`), and
`hrel` (`coulomb_isRelBounded`, the Coulomb relative bound `a < 1` w.r.t. the closed kinetic operator).
This theorem takes **no disclosed-hypothesis argument** — molecular-Hamiltonian essential
self-adjointness holds outright. (Supersedes the `hrel`-disclosing
`molecularHamiltonian_essSelfAdjoint_of_hpot_hrel` / `_of_kinetic` in `KineticEssentialSelfAdjoint.lean`.) -/
theorem molecularHamiltonian_essSelfAdjoint (N : ℕ) (m : ℝ) (hm : 0 < m)
    (nuclei : Finset (Space 3 × ℝ)) :
    IsSelfAdjoint ((molecularSystem N m hm nuclei).kineticOperator.closure
      + (molecularSystem N m hm nuclei).potentialOperator) := by
  obtain ⟨a, b, ha0, ha, hb, hrel⟩ := coulomb_isRelBounded m hm nuclei
  exact molecularHamiltonian_essSelfAdjoint_of_kinetic N m hm nuclei ha0 ha hb hrel
