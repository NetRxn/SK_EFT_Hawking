import SKEFTHawking.QuantumNetwork.GaussianMoments
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Multivariate Gaussian moment product (Phase 6AG, Ask 4 — brick 2)

The coordinate-factorisation step of the Gaussian→sphere route. For the unnormalised Gaussian
weight `exp(-‖x‖²/2)` on `EuclideanSpace ℝ (Fin N)`, the integral of a coordinate monomial
`∏ᵢ xᵢ^{mᵢ}` factorises into a product of the 1-D moments `Jₘ = ∫ t^m·exp(-t²/2)` (built in
`GaussianMoments`). This is the multivariate Wick/Isserlis tensor at the integral level; the
per-pattern evaluation (delta-contractions) is assembled downstream.

The factorisation transports `volume` on `EuclideanSpace ℝ (Fin N)` to `Measure.pi (fun _ ↦ volume)`
on `Fin N → ℝ` via `PiLp.volume_preserving_toLp`, after which the integrand
`∏ᵢ (xᵢ^{mᵢ}·exp(-xᵢ²/2))` is a coordinate product and `integral_fintype_prod_volume_eq_prod`
applies. The Gaussian weight splits as a coordinate product because the ℓ²-norm satisfies
`‖x‖² = ∑ᵢ xᵢ²`.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open MeasureTheory ProbabilityTheory Real Set Finset

/-- **Gaussian monomial-moment factorisation.** The unnormalised Gaussian integral of a coordinate
monomial over `EuclideanSpace ℝ (Fin N)` factorises into the product of the 1-D moments
`Jₘᵢ = ∫ t^{mᵢ}·exp(-t²/2)`:
`∫ (∏ᵢ xᵢ^{mᵢ})·exp(-‖x‖²/2) = ∏ᵢ ∫ t^{mᵢ}·exp(-t²/2)`. -/
theorem gaussInt_monomial {ι : Type*} [Fintype ι] (m : ι → ℕ) :
    ∫ x : EuclideanSpace ℝ ι, (∏ i, (x i) ^ (m i)) * Real.exp (-‖x‖ ^ 2 / 2)
      = ∏ i, ∫ t : ℝ, t ^ (m i) * Real.exp (-t ^ 2 / 2) := by
  have hw : ∀ x : EuclideanSpace ℝ ι,
      (∏ i, (x i) ^ (m i)) * Real.exp (-‖x‖ ^ 2 / 2)
        = ∏ i, ((x i) ^ (m i) * Real.exp (-(x i) ^ 2 / 2)) := by
    intro x
    rw [show Real.exp (-‖x‖ ^ 2 / 2) = ∏ i, Real.exp (-(x i) ^ 2 / 2) from by
          rw [← Real.exp_sum]; congr 1
          rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), ← Finset.sum_div,
              ← Finset.sum_neg_distrib]
          congr 1; apply Finset.sum_congr rfl; intro i _; rw [Real.norm_eq_abs, sq_abs],
        ← Finset.prod_mul_distrib]
  simp_rw [hw]
  rw [← (PiLp.volume_preserving_toLp (ι := ι)).integral_comp
        (MeasurableEquiv.toLp 2 (ι → ℝ)).measurableEmbedding]
  rw [integral_fintype_prod_volume_eq_prod (fun i t => t ^ (m i) * Real.exp (-t ^ 2 / 2))]

/-! ### Per-coordinate 1-D moment values

The factors `Jₘ = ∫ t^m·exp(-t²/2)` for the degrees that appear in a degree-4 monomial
(`m ∈ {0,1,2,3,4}`), specialising the `GaussianMoments` results. `J₀ = J₂ = √(2π)`, `J₄ = 3√(2π)`,
and the odd moments `J₁ = J₃ = 0`. -/

/-- `J₀ = ∫ t⁰·exp(-t²/2) = √(2π)`. -/
theorem moment_zero : ∫ t : ℝ, t ^ 0 * Real.exp (-t ^ 2 / 2) = Real.sqrt (2 * π) := by
  simp only [pow_zero, one_mul]; exact integral_gaussian_weight

/-- `J₁ = ∫ t¹·exp(-t²/2) = 0`. -/
theorem moment_one : ∫ t : ℝ, t ^ 1 * Real.exp (-t ^ 2 / 2) = 0 := by
  have h := integral_odd_mul_gaussian 0
  simpa using h

/-- `J₂ = ∫ t²·exp(-t²/2) = √(2π)`. -/
theorem moment_two : ∫ t : ℝ, t ^ 2 * Real.exp (-t ^ 2 / 2) = Real.sqrt (2 * π) :=
  integral_pow_two_mul_gaussian

/-- `J₃ = ∫ t³·exp(-t²/2) = 0`. -/
theorem moment_three : ∫ t : ℝ, t ^ 3 * Real.exp (-t ^ 2 / 2) = 0 := by
  have h := integral_odd_mul_gaussian 1
  simpa using h

/-- `J₄ = ∫ t⁴·exp(-t²/2) = 3·√(2π)`. -/
theorem moment_four : ∫ t : ℝ, t ^ 4 * Real.exp (-t ^ 2 / 2) = 3 * Real.sqrt (2 * π) :=
  integral_pow_four_mul_gaussian

/-! ### Wick-weight factorisation -/

/-- The Wick weight `w(m) = Jₘ / √(2π)`: `w(0) = w(2) = 1`, `w(1) = w(3) = 0`, `w(4) = 3`. Only
the values `m ≤ 4` occur in a degree-4 monomial. -/
def wval : ℕ → ℝ
  | 0 => 1 | 1 => 0 | 2 => 1 | 3 => 0 | 4 => 3 | _ => 0

/-- Each 1-D moment factors as `Jₘ = √(2π)·w(m)` for `m ≤ 4`. -/
theorem moment_eq_wval (m : ℕ) (hm : m ≤ 4) :
    (∫ t : ℝ, t ^ m * Real.exp (-t ^ 2 / 2)) = Real.sqrt (2 * π) * wval m := by
  interval_cases m
  · rw [moment_zero, wval]; ring
  · rw [moment_one, wval]; ring
  · rw [moment_two, wval]; ring
  · rw [moment_three, wval]; ring
  · rw [moment_four, wval]; ring

/-! ### Coordinate multiplicity of a degree-4 monomial -/

/-- The multiplicity of coordinate `e` in the monomial `x_a x_b x_c x_d`. -/
def coordMult {ι : Type*} [DecidableEq ι] (a b c d e : ι) : ℕ :=
  (if e = a then 1 else 0) + (if e = b then 1 else 0)
    + (if e = c then 1 else 0) + (if e = d then 1 else 0)

/-- Coordinate multiplicity in a degree-4 monomial never exceeds `4`. -/
theorem coordMult_le_four {ι : Type*} [DecidableEq ι] (a b c d e : ι) :
    coordMult a b c d e ≤ 4 := by
  unfold coordMult
  split_ifs <;> omega

/-- **Degree-4 coordinate monomial as a power product.** `x_a x_b x_c x_d = ∏_e (x e)^{mult e}`,
the algebraic input to the `gaussInt_monomial` factorisation. -/
theorem monomial_coord_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : EuclideanSpace ℝ ι) (a b c d : ι) :
    x a * x b * x c * x d = ∏ e, (x e) ^ (coordMult a b c d e) := by
  unfold coordMult
  simp_rw [pow_add, Finset.prod_mul_distrib, pow_ite, pow_one, pow_zero,
           Finset.prod_ite_eq' Finset.univ _ (fun e => x e)]
  simp

/-! ### The Wick (Isserlis) coefficient and the degree-4 real moment tensor -/

/-- The degree-4 Wick/Isserlis coefficient: the sum over the three perfect matchings of `{a,b,c,d}`,
`δ_ab δ_cd + δ_ac δ_bd + δ_ad δ_bc`. Equal to `3` when all four indices coincide, `1` for a genuine
two-pair pattern, and `0` otherwise. -/
def realWick {ι : Type*} [DecidableEq ι] (a b c d : ι) : ℝ :=
  (if a = b then 1 else 0) * (if c = d then 1 else 0)
    + (if a = c then 1 else 0) * (if b = d then 1 else 0)
    + (if a = d then 1 else 0) * (if b = c then 1 else 0)

/-- If every coordinate multiplicity is even (`0` or `2`), the Wick-weight product is `1`. -/
theorem prod_wval_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι] (a b c d : ι)
    (h : ∀ e, coordMult a b c d e = 0 ∨ coordMult a b c d e = 2) :
    ∏ e, wval (coordMult a b c d e) = 1 := by
  apply Finset.prod_eq_one; intro e _; rcases h e with h | h <;> rw [h] <;> rfl

/-- When all four indices coincide, the Wick-weight product is `3` (`w(4) = 3`, rest `w(0) = 1`). -/
theorem prod_wval_allEqual {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) :
    ∏ e, wval (coordMult a a a a e) = 3 := by
  rw [Finset.prod_eq_single a]
  · simp [coordMult, wval]
  · intro e _ hne; simp [coordMult, hne, wval]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- **The Wick-weight product equals the Isserlis coefficient:** `∏_e w(mult e) = δδ + δδ + δδ`.
The full case analysis on the equality pattern of `(a,b,c,d)`: an odd multiplicity forces a
vanishing factor (`prod_eq_zero`), a two-pair pattern gives all-even multiplicities (`prod_eq_one`),
and a total coincidence gives the single `w(4) = 3` factor (`prod_eq_single`). -/
theorem prod_wval_coordMult {ι : Type*} [Fintype ι] [DecidableEq ι] (a b c d : ι) :
    ∏ e, wval (coordMult a b c d e) = realWick a b c d := by
  by_cases hab : a = b
  · subst hab
    by_cases hcd : c = d
    · subst hcd
      by_cases hac : a = c
      · subst hac; rw [prod_wval_allEqual]; norm_num [realWick]
      · rw [prod_wval_eq_one a a c c (by
          intro e; unfold coordMult
          by_cases hea : e = a <;> by_cases hec : e = c <;> simp_all)]
        simp [realWick, hac]
    · rw [Finset.prod_eq_zero (Finset.mem_univ c)
          (by by_cases hca : c = a <;> simp_all [coordMult, wval])]
      simp only [realWick, if_neg hcd]
      by_cases hac : a = c <;> by_cases had : a = d <;> simp_all
  · by_cases hac : a = c
    · subst hac
      by_cases hbd : b = d
      · subst hbd
        rw [prod_wval_eq_one a b a b (by
          intro e; unfold coordMult
          by_cases hea : e = a <;> by_cases heb : e = b <;> simp_all)]
        simp [realWick, hab]
      · have hdb : ¬ d = b := fun h => hbd h.symm
        have hba : ¬ b = a := fun h => hab h.symm
        rw [Finset.prod_eq_zero (Finset.mem_univ d)
            (by by_cases hda : d = a <;> simp [coordMult, hda, hdb, hab, wval])]
        simp [realWick, hab, hbd, hba]
    · by_cases had : a = d
      · subst had
        by_cases hbc : b = c
        · subst hbc
          rw [prod_wval_eq_one a b b a (by
            intro e; unfold coordMult
            by_cases hea : e = a <;> by_cases heb : e = b <;> simp_all)]
          simp [realWick, hab]
        · have hba : ¬ b = a := fun h => hab h.symm
          rw [Finset.prod_eq_zero (Finset.mem_univ b)
              (by simp [coordMult, hba, hbc, wval])]
          simp [realWick, hab, hac, hbc]
      · rw [Finset.prod_eq_zero (Finset.mem_univ a)
            (by simp [coordMult, hab, hac, had, wval])]
        simp [realWick, hab, hac, had]

/-- **Degree-4 real Gaussian moment tensor (Wick/Isserlis).** For the standard Gaussian weight on
`EuclideanSpace ℝ ι`,
`∫ (x_a x_b x_c x_d)·exp(-‖x‖²/2) = (δ_ab δ_cd + δ_ac δ_bd + δ_ad δ_bc)·(√(2π))^{card ι}`.
The unnormalised fourth-moment tensor; dividing by the normalisation `(√(2π))^{card ι}` gives the
familiar dimensionless Isserlis numbers `{0, 1, 3}`. -/
theorem gaussRealFourTensor {ι : Type*} [Fintype ι] [DecidableEq ι] (a b c d : ι) :
    ∫ x : EuclideanSpace ℝ ι, (x a * x b * x c * x d) * Real.exp (-‖x‖ ^ 2 / 2)
      = realWick a b c d * Real.sqrt (2 * π) ^ Fintype.card ι := by
  simp_rw [monomial_coord_pow]
  rw [gaussInt_monomial (coordMult a b c d),
      Finset.prod_congr rfl (fun i _ =>
        moment_eq_wval (coordMult a b c d i) (coordMult_le_four a b c d i)),
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      prod_wval_coordMult]
  ring

end SKEFTHawking.QuantumNetwork
