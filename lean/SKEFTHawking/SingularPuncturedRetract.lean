import Mathlib
import SKEFTHawking.SingularHomotopyInvariance

/-!
# `ℝⁿ ∖ 0` deformation retracts onto `Sⁿ⁻¹`

The punctured Euclidean space `ℝⁿ ∖ 0` retracts onto the unit sphere via `x ↦ x / ‖x‖`, with the
straight-line homotopy `H(x, t) = t • x + (1 - t) • (x / ‖x‖)` (which stays off the origin because
the scalar `t + (1 - t)/‖x‖` is strictly positive). Hence the inclusion `Sⁿ⁻¹ ↪ ℝⁿ ∖ 0` induces an
isomorphism on `Hₖ(·; ℤ/2)` — reducing the homology of the punctured space (and so the local
homology `Hₖ(ℝⁿ, ℝⁿ ∖ 0)`) to that of the sphere.
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularHomotopyInvariance
open SKEFTHawking.SingularFunctoriality

namespace SKEFTHawking.SingularPuncturedRetract

variable (n : ℕ)

/-- The unit sphere `Sⁿ⁻¹ ⊆ ℝⁿ` as a topological space object. -/
abbrev Sph : TopCat := TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)

/-- The punctured space `ℝⁿ ∖ 0` as a topological space object. -/
abbrev Punc : TopCat := TopCat.of {x : EuclideanSpace ℝ (Fin n) // x ≠ 0}

variable {n}

theorem norm_ne_zero_of_punc (x : {x : EuclideanSpace ℝ (Fin n) // x ≠ 0}) : ‖(x : EuclideanSpace ℝ (Fin n))‖ ≠ 0 :=
  norm_ne_zero_iff.mpr x.2

/-- `x / ‖x‖` lies on the unit sphere. -/
theorem normalize_mem_sphere (x : {x : EuclideanSpace ℝ (Fin n) // x ≠ 0}) :
    ‖(x : EuclideanSpace ℝ (Fin n))‖⁻¹ • (x : EuclideanSpace ℝ (Fin n)) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_of_punc x)]

/-- The **retraction** `ℝⁿ ∖ 0 → Sⁿ⁻¹`, `x ↦ x / ‖x‖`. -/
noncomputable def normalize : C(↑(Punc n), ↑(Sph n)) where
  toFun x := ⟨‖(x : EuclideanSpace ℝ (Fin n))‖⁻¹ • (x : EuclideanSpace ℝ (Fin n)),
    normalize_mem_sphere x⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.smul ?_ continuous_subtype_val) _
    exact (continuous_norm.comp continuous_subtype_val).inv₀ (fun x => norm_ne_zero_of_punc x)

/-- Sphere points are nonzero. -/
theorem sphere_ne_zero (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    (x : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
  rw [← norm_ne_zero_iff, mem_sphere_zero_iff_norm.mp x.2]; norm_num

/-- The **inclusion** `Sⁿ⁻¹ ↪ ℝⁿ ∖ 0` (sphere points are nonzero). -/
noncomputable def incl : C(↑(Sph n), ↑(Punc n)) where
  toFun x := ⟨(x : EuclideanSpace ℝ (Fin n)), sphere_ne_zero x⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _

/-- The retraction splits the inclusion: `normalize ∘ incl = id` on the sphere (norm-1 points are
fixed). -/
theorem normalize_comp_incl : (normalize (n := n)).comp incl = ContinuousMap.id _ := by
  refine ContinuousMap.ext fun x => ?_
  refine Subtype.ext ?_
  show ‖(x : EuclideanSpace ℝ (Fin n))‖⁻¹ • (x : EuclideanSpace ℝ (Fin n)) = (x : _)
  rw [mem_sphere_zero_iff_norm.mp x.2, inv_one, one_smul]

/-- The straight-line retract homotopy stays off the origin: `t • x + (1 - t) • (x / ‖x‖)` is a
strictly-positive scalar multiple of `x ≠ 0`. -/
theorem puncHomotopy_ne_zero (x : {x : EuclideanSpace ℝ (Fin n) // x ≠ 0}) (t : unitInterval) :
    (t : ℝ) • (x : EuclideanSpace ℝ (Fin n))
        + (1 - (t : ℝ)) • (‖(x : EuclideanSpace ℝ (Fin n))‖⁻¹ • (x : EuclideanSpace ℝ (Fin n)))
      ≠ 0 := by
  have hnorm : (0 : ℝ) < ‖(x : EuclideanSpace ℝ (Fin n))‖ := norm_pos_iff.mpr x.2
  have hinv : (0 : ℝ) < ‖(x : EuclideanSpace ℝ (Fin n))‖⁻¹ := inv_pos.mpr hnorm
  rw [smul_smul, ← add_smul]
  refine smul_ne_zero (ne_of_gt ?_) x.2
  rcases eq_or_lt_of_le t.2.1 with h | h
  · rw [← h]; simp only [sub_zero, one_mul, zero_add]; exact hinv
  · have : (0 : ℝ) ≤ (1 - (t : ℝ)) * ‖(x : EuclideanSpace ℝ (Fin n))‖⁻¹ :=
      mul_nonneg (by linarith [t.2.2]) hinv.le
    linarith

/-- The **deformation-retract homotopy** `H(x, t) = t • x + (1 - t) • (x / ‖x‖)` on `ℝⁿ ∖ 0`:
`H(·, 0) = incl ∘ normalize` and `H(·, 1) = id`. -/
noncomputable def puncHomotopy : C(↑(Punc n) × unitInterval, ↑(Punc n)) where
  toFun p := ⟨(p.2 : ℝ) • (p.1 : EuclideanSpace ℝ (Fin n))
      + (1 - (p.2 : ℝ)) • (‖(p.1 : EuclideanSpace ℝ (Fin n))‖⁻¹ • (p.1 : EuclideanSpace ℝ (Fin n))),
    puncHomotopy_ne_zero p.1 p.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.add (Continuous.smul ?_ ?_) (Continuous.smul ?_ ?_)) _
    · exact continuous_subtype_val.comp continuous_snd
    · exact continuous_subtype_val.comp continuous_fst
    · exact (continuous_const.sub (continuous_subtype_val.comp continuous_snd))
    · exact ((continuous_norm.comp (continuous_subtype_val.comp continuous_fst)).inv₀
        (by intro p; exact norm_ne_zero_of_punc p.1)).smul
          (continuous_subtype_val.comp continuous_fst)

/-- `H(·, 0) = incl ∘ normalize` (the retraction `x ↦ x / ‖x‖`). -/
theorem slice_puncHomotopy_zero : slice (puncHomotopy (n := n)) 0 = incl.comp normalize := by
  refine ContinuousMap.ext fun x => Subtype.ext ?_
  show ((0 : unitInterval) : ℝ) • (x : EuclideanSpace ℝ (Fin n))
      + (1 - ((0 : unitInterval) : ℝ)) • (‖(x : EuclideanSpace ℝ (Fin n))‖⁻¹ • (x : _))
    = ‖(x : EuclideanSpace ℝ (Fin n))‖⁻¹ • (x : EuclideanSpace ℝ (Fin n))
  simp

/-- `H(·, 1) = id`. -/
theorem slice_puncHomotopy_one : slice (puncHomotopy (n := n)) 1 = ContinuousMap.id _ := by
  refine ContinuousMap.ext fun x => Subtype.ext ?_
  show ((1 : unitInterval) : ℝ) • (x : EuclideanSpace ℝ (Fin n))
      + (1 - ((1 : unitInterval) : ℝ)) • (‖(x : EuclideanSpace ℝ (Fin n))‖⁻¹ • (x : _))
    = (x : EuclideanSpace ℝ (Fin n))
  simp

/-- The constant homotopy on the sphere (projection to the point coordinate). -/
noncomputable def constHomotopy : C(↑(Sph n) × unitInterval, ↑(Sph n)) :=
  ⟨fun p => p.1, continuous_fst⟩

theorem slice_constHomotopy (r : unitInterval) :
    slice (constHomotopy (n := n)) r = ContinuousMap.id _ :=
  ContinuousMap.ext fun _ => rfl

/-- **`normalize : ℝⁿ ∖ 0 → Sⁿ⁻¹` induces an isomorphism on `Hₖ₊₁(·; ℤ/2)`** — the punctured space
deformation-retracts onto the sphere. -/
theorem homology_map_normalize_bijective (k : ℕ) :
    Function.Bijective (Homology.map (normalize (n := n)) (k + 1)) :=
  Homology.map_bijective_of_homotopyEquiv normalize incl puncHomotopy slice_puncHomotopy_zero
    slice_puncHomotopy_one constHomotopy
    ((slice_constHomotopy 0).trans normalize_comp_incl.symm) (slice_constHomotopy 1) k

end SKEFTHawking.SingularPuncturedRetract
