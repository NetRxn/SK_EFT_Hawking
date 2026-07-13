import Mathlib
import SKEFTHawking.RP2PointSet

/-!
# Phase 5q.G (B-arc, M2-a) — `S² → ℝP²` is a covering map

The antipodal action is **free** (`IsCancelSMul` — a scalar `±1` fixing a sphere point would
force `x = -x`, impossible off `0`), so Mathlib's properly-discontinuous quotient machinery
(`isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul`) makes the orbit map a genuine
covering map — the input to the simplex-lifting transfer of the Smith sequence (M2-b).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open Metric
open SKEFTHawking.RP2PointSet

namespace SKEFTHawking.RP2Covering

/-- **The antipodal action is cancellative/free**: distinct units move every point differently
(`x ≠ 0` on the sphere), and each unit acts injectively. -/
instance : IsCancelSMul ℤˣ S2 where
  left_cancel' u x y h := by
    have hcoe := congrArg Subtype.val h
    simp only [smul_coe] at hcoe
    have hu : (((u : ℤ) : ℝ)) ≠ 0 := by
      rcases Int.units_eq_one_or u with h1 | h1 <;> rw [h1] <;> norm_num
    exact Subtype.ext (smul_right_injective _ hu hcoe)
  right_cancel' u v x h := by
    have hcoe := congrArg Subtype.val h
    simp only [smul_coe] at hcoe
    have hx : (x : EuclideanSpace ℝ (Fin (2 + 1))) ≠ 0 := by
      intro h0
      have := mem_sphere_zero_iff_norm.mp x.2
      rw [h0, norm_zero] at this
      exact one_ne_zero this.symm
    have hscal : (((u : ℤ) : ℝ)) = (((v : ℤ) : ℝ)) := smul_left_injective ℝ hx hcoe
    have : (u : ℤ) = (v : ℤ) := by exact_mod_cast hscal
    exact Units.ext this

/-- **The orbit map `S² → ℝP²` is a covering map** — free + properly discontinuous. -/
theorem rp2_isCoveringMap :
    IsCoveringMap (Quotient.mk (MulAction.orbitRel ℤˣ S2)) :=
  (isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul (G := ℤˣ)
    (E := S2)).isCoveringMap

end SKEFTHawking.RP2Covering
