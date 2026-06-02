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
theorem gaussInt_monomial (N : ℕ) (m : Fin N → ℕ) :
    ∫ x : EuclideanSpace ℝ (Fin N), (∏ i, (x i) ^ (m i)) * Real.exp (-‖x‖ ^ 2 / 2)
      = ∏ i, ∫ t : ℝ, t ^ (m i) * Real.exp (-t ^ 2 / 2) := by
  have hw : ∀ x : EuclideanSpace ℝ (Fin N),
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
  rw [← (PiLp.volume_preserving_toLp (ι := Fin N)).integral_comp
        (MeasurableEquiv.toLp 2 (Fin N → ℝ)).measurableEmbedding]
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
def coordMult {N : ℕ} (a b c d e : Fin N) : ℕ :=
  (if e = a then 1 else 0) + (if e = b then 1 else 0)
    + (if e = c then 1 else 0) + (if e = d then 1 else 0)

/-- Coordinate multiplicity in a degree-4 monomial never exceeds `4`. -/
theorem coordMult_le_four {N : ℕ} (a b c d e : Fin N) : coordMult a b c d e ≤ 4 := by
  unfold coordMult
  split_ifs <;> omega

/-- **Degree-4 coordinate monomial as a power product.** `x_a x_b x_c x_d = ∏_e (x e)^{mult e}`,
the algebraic input to the `gaussInt_monomial` factorisation. -/
theorem monomial_coord_pow {N : ℕ} (x : EuclideanSpace ℝ (Fin N)) (a b c d : Fin N) :
    x a * x b * x c * x d = ∏ e, (x e) ^ (coordMult a b c d e) := by
  unfold coordMult
  simp_rw [pow_add, Finset.prod_mul_distrib, pow_ite, pow_one, pow_zero,
           Finset.prod_ite_eq' Finset.univ _ (fun e => x e)]
  simp

end SKEFTHawking.QuantumNetwork
