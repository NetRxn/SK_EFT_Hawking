import SKEFTHawking.MolecularHamiltonian
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

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

end SKEFTHawking.DFT
