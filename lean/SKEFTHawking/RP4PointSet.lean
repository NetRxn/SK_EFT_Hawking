import Mathlib

/-!
# Phase 5q.G (B-arc, B4a) — `ℝP⁴` as `S⁴/±`: the point-set layer

The carrier for the tied datum's odd witness (`w₁⁴[ℝP⁴] = 1`): real projective 4-space as the
orbit space of the antipodal `ℤˣ`-action on the unit 4-sphere. This brick supplies the
point-set layer — the action, its continuity and proper discontinuity, and the quotient's
`TopologicalSpace`/`T2Space`/`CompactSpace`/`Nonempty` instances — all from Mathlib's stock
machinery (`t2Space_of_properlyDiscontinuousSMul_of_t2Space`, `Quotient.compactSpace`).
The charted structure (descending the sphere's stereographic charts on hemispheres where the
quotient map is injective) is B4b.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open Metric

namespace SKEFTHawking.RP4PointSet

/-- The unit 4-sphere in `ℝ⁵`. -/
abbrev S4 : Type := sphere (0 : EuclideanSpace ℝ (Fin (4 + 1))) 1

/-- The antipodal `ℤˣ`-action on the sphere: `u • x = (±1) • x`. -/
instance : SMul ℤˣ S4 where
  smul u x := ⟨((u : ℤ) : ℝ) • x.1, by
    rw [mem_sphere_zero_iff_norm, norm_smul, mem_sphere_zero_iff_norm.mp x.2, mul_one]
    rcases Int.units_eq_one_or u with h | h <;> rw [h] <;> norm_num⟩

@[simp] theorem smul_coe (u : ℤˣ) (x : S4) :
    ((u • x : S4) : EuclideanSpace ℝ (Fin (4 + 1))) = ((u : ℤ) : ℝ) • x.1 := rfl

instance : MulAction ℤˣ S4 where
  one_smul x := Subtype.ext (by simp)
  mul_smul u v x := Subtype.ext (by
    simp only [smul_coe]
    rw [Units.val_mul, Int.cast_mul, mul_smul])

instance : ContinuousConstSMul ℤˣ S4 :=
  ⟨fun _u => Continuous.subtype_mk (continuous_const.smul continuous_subtype_val) _⟩

/-- The antipodal action is properly discontinuous (`ℤˣ` is finite). -/
instance : ProperlyDiscontinuousSMul ℤˣ S4 :=
  ⟨fun _ _ => Set.toFinite _⟩

/-- **`ℝP⁴` as the antipodal orbit space `S⁴/±`.** -/
def RP4 : Type := Quotient (MulAction.orbitRel ℤˣ S4)

instance : TopologicalSpace RP4 :=
  inferInstanceAs (TopologicalSpace (Quotient (MulAction.orbitRel ℤˣ S4)))

instance : CompactSpace RP4 :=
  inferInstanceAs (CompactSpace (Quotient (MulAction.orbitRel ℤˣ S4)))

/-- `ℝP⁴` is Hausdorff — the properly-discontinuous quotient theorem. -/
instance : T2Space RP4 :=
  inferInstanceAs (T2Space (Quotient (MulAction.orbitRel ℤˣ S4)))

/-- A basepoint: the class of the first coordinate vector. -/
noncomputable instance : Nonempty RP4 :=
  ⟨Quotient.mk _ ⟨EuclideanSpace.single (0 : Fin 5) (1 : ℝ), by
    rw [mem_sphere_zero_iff_norm]
    simp⟩⟩

end SKEFTHawking.RP4PointSet
