import Mathlib
import SKEFTHawking.SingularHomotopyInvariance
import SKEFTHawking.SingularPuncturedRetract

/-!
# Phase 5q.F (w₂-foundation, brick 6e) — the convex-complement radial retract

For `A ⊆ ℝⁿ` compact convex with `0 ∈ interior A`, the complement `ℝⁿ ∖ A` deformation-retracts to
`ℝⁿ ∖ 0`: the inclusion `f : ℝⁿ∖A ↪ ℝⁿ∖0` is a homotopy equivalence, with inverse
`g(x) = (1 + 1/gauge A x) • x` (pushing each point radially out past `∂A`). This mirrors
`SingularPuncturedRetract` (the `ℝⁿ∖0 ≃ Sⁿ⁻¹` normalize-retract) but for the convex complement, using
Mathlib's `gauge`. It gives `Hₖ(ℝⁿ∖A) ≅ Hₖ(ℝⁿ∖0)`, the homotopy input to the convex base case of the
Hatcher 3.27 fundamental-class induction. Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularHomotopyInvariance
open SKEFTHawking.SingularPuncturedRetract

namespace SKEFTHawking.SingularConvexComplementRetract

variable {n : ℕ} {A : Set (EuclideanSpace ℝ (Fin n))}

/-- `x ∉ A ↔ gauge A x > 1` (for `A` closed convex with `0 ∈ interior`). -/
theorem not_mem_iff_one_lt_gauge (hAc : Convex ℝ A) (hAcomp : IsCompact A)
    (hA0 : A ∈ nhds (0 : EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) :
    x ∉ A ↔ 1 < gauge A x := by
  rw [← not_le, gauge_le_one_iff_mem_closure hAc hA0, hAcomp.isClosed.closure_eq]

/-- `gauge A x > 0` for `x ≠ 0`. -/
theorem gauge_pos_of (hAcomp : IsCompact A)
    (hA0 : A ∈ nhds (0 : EuclideanSpace ℝ (Fin n))) {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    0 < gauge A x :=
  (gauge_pos (absorbent_nhds_zero hA0) (hAcomp.totallyBounded.isVonNBounded ℝ)).2 hx

/-- The radial push-out scalar `1 + s/gauge A x` is `≥ 1 > 0`. -/
theorem one_le_radial (hAcomp : IsCompact A) (hA0 : A ∈ nhds (0 : EuclideanSpace ℝ (Fin n)))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    1 ≤ 1 + s * (gauge A x)⁻¹ := by
  have := gauge_pos_of hAcomp hA0 hx
  nlinarith [mul_nonneg hs (inv_nonneg.2 this.le)]

/-- **The radial push-out** `(x, s) ↦ (1 + s/gauge A x) • x` has `gauge` value `gauge A x + s`
(`gauge` is positively homogeneous). For `x ∉ A` (`gauge x > 1`) and `s ≥ 0` it stays out of `A`;
for `x ≠ 0` and the scalar `> 0` it stays nonzero. -/
theorem gauge_radial (hAcomp : IsCompact A) (hA0 : A ∈ nhds (0 : EuclideanSpace ℝ (Fin n)))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    gauge A ((1 + s * (gauge A x)⁻¹) • x) = gauge A x + s := by
  have hp := gauge_pos_of hAcomp hA0 hx
  rw [gauge_smul_of_nonneg (zero_le_one.trans (one_le_radial hAcomp hA0 hx hs)), smul_eq_mul,
    add_mul, one_mul, mul_assoc, inv_mul_cancel₀ hp.ne', mul_one]

end SKEFTHawking.SingularConvexComplementRetract
