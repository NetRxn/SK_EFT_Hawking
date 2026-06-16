import Mathlib
import SKEFTHawking.SingularDisjointUnion
import SKEFTHawking.SingularSphereBottom

/-!
# `H̃₀(ℝ¹ ∖ 0) ≅ ℤ/2` and the circle `H₁(S¹) ≅ ℤ/2`

The concrete base value of the sphere/local-homology induction. `ℝ¹ ∖ 0 = Punc 1` is the clopen union
of two open half-lines `{x₀ > 0}` and `{x₀ < 0}`, each convex (hence reduced-acyclic with nonzero
`H₀`, `convex_augH_bijective` after transport to the single-subtype half-line). So
`H̃₀(ℝ¹∖0) ≅ ℤ/2` (`augH_ker_iso_zmod2`); transporting across `equatorHomeo` and composing with
`bottomSuspEquiv` gives `H₁(S¹) ≅ ℤ/2`, and `topSphereReduce` lifts it to `Hₙ(Sⁿ) ≅ ℤ/2`.
-/

open CategoryTheory Opposite Metric
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularH0
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularHomotopyInvariance
open SKEFTHawking.SingularPuncturedRetract SKEFTHawking.SingularDisjointUnion

namespace SKEFTHawking.SingularLineMinusPoint

/-- In `ℝ¹ = EuclideanSpace ℝ (Fin 1)`, a vector is nonzero iff its single coordinate is. -/
theorem ne_zero_iff_coord (x : EuclideanSpace ℝ (Fin 1)) : x ≠ 0 ↔ x 0 ≠ 0 := by
  rw [not_iff_not]; constructor
  · intro h; rw [h]; rfl
  · intro h; ext i; fin_cases i; exact h

/-- The coordinate functional `x ↦ x 0` is continuous on `ℝ¹`. -/
theorem continuous_coord : Continuous (fun x : EuclideanSpace ℝ (Fin 1) => x 0) := by fun_prop

/-- The **positive arc** of `ℝ¹ ∖ 0`: the points with positive coordinate. -/
def posSet : Set ↑(Punc 1) := {y | 0 < (y : EuclideanSpace ℝ (Fin 1)) 0}

/-- The open positive half-line in `ℝ¹` (a single-subtype convex set). -/
def posRay : Set (EuclideanSpace ℝ (Fin 1)) := {x | 0 < x 0}

theorem convex_posRay : Convex ℝ posRay :=
  convex_halfSpace_gt (IsLinearMap.mk (fun _ _ => rfl) (fun _ _ => rfl)) 0

/-- Forward homeo map `↥posSet → ↥posRay` (forget the redundant `≠ 0`). -/
noncomputable def posFwd : C(↑(sub posSet), ↑(sub (X := TopCat.of (EuclideanSpace ℝ (Fin 1))) posRay)) :=
  ⟨fun y => ⟨(y : ↑(Punc 1)), y.2⟩, by
    apply Continuous.subtype_mk; exact continuous_subtype_val.comp continuous_subtype_val⟩

/-- Backward homeo map `↥posRay → ↥posSet` (recover `≠ 0` from `0 < x₀`). -/
noncomputable def posBwd : C(↑(sub (X := TopCat.of (EuclideanSpace ℝ (Fin 1))) posRay), ↑(sub posSet)) :=
  ⟨fun x => ⟨⟨(x : EuclideanSpace ℝ (Fin 1)), (ne_zero_iff_coord _).mpr (ne_of_gt x.2)⟩, x.2⟩, by
    apply Continuous.subtype_mk; apply Continuous.subtype_mk; exact continuous_subtype_val⟩

theorem posBwd_comp_posFwd : posBwd.comp posFwd = ContinuousMap.id _ :=
  ContinuousMap.ext fun y => Subtype.ext (Subtype.ext rfl)

theorem posFwd_comp_posBwd : posFwd.comp posBwd = ContinuousMap.id _ :=
  ContinuousMap.ext fun x => Subtype.ext rfl

/-- **The positive arc of `ℝ¹∖0` is reduced-acyclic with nonzero `H₀`** (`ε̄` bijective): it is
homeomorphic to the convex half-line `posRay`. -/
theorem augH_posSet_bijective : Function.Bijective (augH (sub posSet)) :=
  augH_bijective_of_homeo posFwd posBwd posBwd_comp_posFwd posFwd_comp_posBwd
    (convex_augH_bijective convex_posRay (p := EuclideanSpace.single 0 1)
      (by show (0:ℝ) < EuclideanSpace.single 0 (1:ℝ) 0; simp))

/-- For a point of `ℝ¹∖0` in the complement of the positive arc, the coordinate is `< 0`. -/
theorem coord_neg_of_mem_compl (y : ↑(Punc 1)) (hy : y ∈ posSetᶜ) :
    (y : EuclideanSpace ℝ (Fin 1)) 0 < 0 :=
  lt_of_le_of_ne (not_lt.mp hy) ((ne_zero_iff_coord _).mp y.2)

/-- Antipodal map `↥posSetᶜ → ↥posSet` (`x ↦ -x` swaps the two arcs). -/
noncomputable def negFwd : C(↑(sub posSetᶜ), ↑(sub posSet)) :=
  ⟨fun y => ⟨⟨-(y.1.1 : EuclideanSpace ℝ (Fin 1)), neg_ne_zero.mpr y.1.2⟩, by
    show 0 < (-(y.1.1 : EuclideanSpace ℝ (Fin 1))) 0
    rw [PiLp.neg_apply, neg_pos]; exact coord_neg_of_mem_compl y.1 y.2⟩, by
    apply Continuous.subtype_mk; apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_subtype_val).neg⟩

/-- Antipodal map `↥posSet → ↥posSetᶜ`. -/
noncomputable def negBwd : C(↑(sub posSet), ↑(sub posSetᶜ)) :=
  ⟨fun x => ⟨⟨-(x.1.1 : EuclideanSpace ℝ (Fin 1)), neg_ne_zero.mpr x.1.2⟩, by
    show ¬ (0 < (-(x.1.1 : EuclideanSpace ℝ (Fin 1))) 0)
    rw [PiLp.neg_apply, neg_pos, not_lt]; exact le_of_lt x.2⟩, by
    apply Continuous.subtype_mk; apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_subtype_val).neg⟩

theorem negBwd_comp_negFwd : negBwd.comp negFwd = ContinuousMap.id _ :=
  ContinuousMap.ext fun y => Subtype.ext (Subtype.ext (neg_neg _))

theorem negFwd_comp_negBwd : negFwd.comp negBwd = ContinuousMap.id _ :=
  ContinuousMap.ext fun x => Subtype.ext (Subtype.ext (neg_neg _))

/-- **The negative arc is reduced-acyclic with nonzero `H₀`** (antipodal to the positive arc). -/
theorem augH_posSetCompl_bijective : Function.Bijective (augH (sub posSetᶜ)) :=
  augH_bijective_of_homeo negFwd negBwd negBwd_comp_negFwd negFwd_comp_negBwd augH_posSet_bijective

/-- **The positive arc is clopen** in `ℝ¹∖0`: open as `{y₀ > 0}`, closed since its complement is
`{y₀ < 0}` (in `ℝ¹∖0` the coordinate is never `0`). -/
theorem isClopen_posSet : IsClopen posSet := by
  have hco : Continuous (fun y : ↑(Punc 1) => (y : EuclideanSpace ℝ (Fin 1)) 0) :=
    continuous_coord.comp continuous_subtype_val
  have hopen : IsOpen posSet := hco.isOpen_preimage _ isOpen_Ioi
  refine ⟨?_, hopen⟩
  rw [← isOpen_compl_iff]
  have heq : posSetᶜ = (fun y : ↑(Punc 1) => (y : EuclideanSpace ℝ (Fin 1)) 0) ⁻¹' Set.Iio 0 := by
    ext y
    simp only [posSet, Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iio, not_lt]
    exact ⟨fun h => lt_of_le_of_ne h ((ne_zero_iff_coord _).mp y.2), le_of_lt⟩
  rw [heq]
  exact hco.isOpen_preimage _ isOpen_Iio

/-- **`H̃₀(ℝ¹ ∖ 0) ≅ ℤ/2`** — the concrete base value of the sphere/local-homology induction. -/
theorem augH_ker_punc1_iso_zmod2 :
    Nonempty (↥(LinearMap.ker (augH (Punc 1))) ≃ₗ[ZMod 2] ZMod 2) :=
  augH_ker_iso_zmod2 isClopen_posSet augH_posSet_bijective augH_posSetCompl_bijective

end SKEFTHawking.SingularLineMinusPoint
