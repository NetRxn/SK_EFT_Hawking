import Mathlib
import SKEFTHawking.SingularLineMinusPoint
import SKEFTHawking.SingularRelativeFunctoriality

/-!
# Translation-invariance of the local model: `Hₙ(ℝⁿ, ℝⁿ ∖ p) ≅ ℤ/2`

The local homology of `ℝⁿ` at an *arbitrary* point `p` is `ℤ/2`, by translating `p` to the origin
(`y ↦ y - p` is a homeomorphism of pairs `(ℝⁿ, ℝⁿ∖p) → (ℝⁿ, ℝⁿ∖0)`, `RelativeHomology.map_bijective_of_comp_id`)
and applying `localHomologyIso`. This is the form the chart↔excision bridge needs, since a chart sends
the chosen point `x ∈ M` to some `φ(x) ∈ ℝⁿ`, not necessarily `0`.
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularEuclideanAcyclic SKEFTHawking.SingularRelativeFunctoriality
open SKEFTHawking.SingularLineMinusPoint

namespace SKEFTHawking.SingularLocalModelChart

variable {n : ℕ} (p : EuclideanSpace ℝ (Fin n))

/-- Translation `y ↦ y - p` as a self-map of `ℝⁿ`. -/
noncomputable def transl : C(↑(Eucl n), ↑(Eucl n)) := ⟨fun y => y - p, by fun_prop⟩

theorem transl_comp_transl_neg : (transl p).comp (transl (-p)) = ContinuousMap.id ↑(Eucl n) :=
  ContinuousMap.ext fun y => by simp [transl]

theorem transl_neg_comp_transl : (transl (-p)).comp (transl p) = ContinuousMap.id ↑(Eucl n) :=
  ContinuousMap.ext fun y => by simp [transl]

/-- `y ↦ y - p` maps `ℝⁿ ∖ {p}` into `ℝⁿ ∖ {0}`. -/
theorem mapsTo_transl : Set.MapsTo (transl p) {y | y ≠ p} {y | y ≠ (0 : EuclideanSpace ℝ (Fin n))} :=
  fun y hy => by simp only [Set.mem_setOf_eq, transl, ContinuousMap.coe_mk, sub_ne_zero]; exact hy

theorem mapsTo_transl_neg :
    Set.MapsTo (transl (-p)) {y | y ≠ (0 : EuclideanSpace ℝ (Fin n))} {y | y ≠ p} :=
  fun y hy => by
    simp only [Set.mem_setOf_eq, transl, ContinuousMap.coe_mk, sub_neg_eq_add]
    intro h; exact hy (by simpa using h)

/-- **`Hₙ(ℝⁿ, ℝⁿ ∖ p) ≅ ℤ/2`** for `n = m + 2` and any point `p` — the translated local model. -/
noncomputable def localHomologyAtPointIso (m : ℕ) (p : EuclideanSpace ℝ (Fin (m + 2))) :
    RelativeHomology (X := Eucl (m + 2)) {y | y ≠ p} (m + 2) ≃ₗ[ZMod 2] ZMod 2 :=
  (LinearEquiv.ofBijective (RelativeHomology.map (transl p) (mapsTo_transl p) (m + 2))
      (RelativeHomology.map_bijective_of_comp_id (transl p) (transl (-p)) (mapsTo_transl p)
        (mapsTo_transl_neg p) (transl_neg_comp_transl p) (transl_comp_transl_neg p) (m + 2))).trans
    (localHomologyIso m)

end SKEFTHawking.SingularLocalModelChart
