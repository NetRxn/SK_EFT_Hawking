import SKEFTHawking.ADW.FiniteDiracQuaternionSpecialization
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# The normalized executable quaternion sphere and SU(2)

The inverse reads the plus-i coordinates from the first row of a special unitary matrix.
Left multiplication is transported by a real-linear isometry of the ambient Euclidean space.
-/

noncomputable section
open Matrix
namespace SKEFTHawking.ADW.QuaternionSU2Sphere
open FiniteGrassmannCoframe FiniteDiracQuaternionSpecialization

abbrev Coordinates := EuclideanSpace ℝ (Fin 4)
abbrev UnitSphere := Metric.sphere (0 : Coordinates) 1

/-- The executable quaternion block on real coordinates. -/
abbrev realBlock (q : Fin 4 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  quaternionBlock Complex.I (fun i ↦ (q i : ℂ))

/-- Read the four real coordinates in the executable plus-i convention. -/
def coordinates (A : Matrix (Fin 2) (Fin 2) ℂ) : Fin 4 → ℝ :=
  ![(A 0 0).re, (A 0 1).im, (A 0 1).re, (A 0 0).im]

@[simp] theorem coordinates_block (q : Fin 4 → ℝ) : coordinates (realBlock q) = q := by
  funext i
  fin_cases i <;> simp [coordinates, quaternionBlock, Complex.mul_re, Complex.mul_im]

theorem block_det (q : Fin 4 → ℝ) :
    (realBlock q).det = ((∑ i, q i ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two]
  apply Complex.ext <;>
    simp [quaternionBlock, Fin.sum_univ_four, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, pow_two] <;> ring

private theorem star_eq_adjugate (A : SU2) :
    star (A : Matrix (Fin 2) (Fin 2) ℂ) = (A : Matrix (Fin 2) (Fin 2) ℂ).adjugate := by
  have hd := (Matrix.mem_specialUnitaryGroup_iff.mp A.property).2
  have h₁ := Matrix.mul_adjugate (A : Matrix (Fin 2) (Fin 2) ℂ)
  rw [hd, one_smul] at h₁
  have h₂ := (Unitary.mem_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp A.property).1).1
  calc
    star (A : Matrix (Fin 2) (Fin 2) ℂ) =
        star (A : Matrix (Fin 2) (Fin 2) ℂ) * ((A : Matrix (Fin 2) (Fin 2) ℂ) * _) := by
      rw [h₁, mul_one]
    _ = _ := by rw [← mul_assoc, h₂, one_mul]

theorem block_coordinates (A : SU2) : realBlock (coordinates A) = A := by
  have h := star_eq_adjugate A
  rw [Matrix.star_eq_conjTranspose, Matrix.adjugate_fin_two] at h
  have h₁ := congrFun (congrFun h 1) 1
  have h₂ := congrFun (congrFun h 1) 0
  simp [Matrix.conjTranspose_apply] at h₁ h₂
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [coordinates, quaternionBlock, Complex.mul_re, Complex.mul_im,
      ← h₁, ← neg_eq_iff_eq_neg.mpr h₂]

theorem unit_coordinates (A : SU2) : UnitQuaternion (coordinates A) := by
  have h := block_det (coordinates A)
  rw [block_coordinates, (Matrix.mem_specialUnitaryGroup_iff.mp A.property).2] at h
  have hr := congrArg Complex.re h.symm
  simpa only [Complex.ofReal_re, Complex.one_re, UnitQuaternion, Fin.sum_univ_four] using hr

theorem unit_ofLp_iff (x : Coordinates) : UnitQuaternion x.ofLp ↔ ‖x‖ = 1 := by
  have h := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 4 ↦ ℝ) x
  simp only [Real.norm_eq_abs, sq_abs, Fin.sum_univ_four] at h
  rw [UnitQuaternion, ← h]
  constructor
  · intro hsq
    nlinarith [norm_nonneg x]
  · intro hx
    simp [hx]

/-- The real coordinate inverse of the normalized realBlock map. -/
def sphereOfSU2 (A : SU2) : UnitSphere :=
  ⟨WithLp.toLp 2 (coordinates A), by
    rw [Metric.mem_sphere, dist_zero_right, ← unit_ofLp_iff]
    exact unit_coordinates A⟩

/-- A Euclidean unit vector gives the normalized executable block. -/
def su2OfSphere (x : UnitSphere) : SU2 :=
  quaternionSU2 x.val.ofLp ((unit_ofLp_iff x.val).2 (by
    simpa only [Metric.mem_sphere, dist_zero_right] using x.property))

private theorem continuous_block : Continuous (realBlock : (Fin 4 → ℝ) → _) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;>
    simp [quaternionBlock] <;> fun_prop

private theorem continuous_coordinates :
    Continuous (coordinates : Matrix (Fin 2) (Fin 2) ℂ → _) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [coordinates] <;> fun_prop

/-- The normalized plus-i quaternion block identifies the Euclidean unit sphere with SU(2). -/
def sphereHomeomorphSU2 : UnitSphere ≃ₜ SU2 where
  toFun := su2OfSphere
  invFun := sphereOfSU2
  left_inv x := Subtype.ext (by
    change WithLp.toLp 2 (coordinates (realBlock x.val.ofLp)) = x.val
    rw [coordinates_block])
  right_inv A := Subtype.ext (block_coordinates A)
  continuous_toFun := (continuous_block.comp
    ((PiLp.continuous_ofLp 2 (fun _ : Fin 4 ↦ ℝ)).comp continuous_subtype_val)).subtype_mk _
  continuous_invFun := ((PiLp.continuous_toLp 2 (fun _ : Fin 4 ↦ ℝ)).comp
    (continuous_coordinates.comp continuous_subtype_val)).subtype_mk _

private theorem block_coordinates_mul (p q : Fin 4 → ℝ) :
    realBlock (coordinates (realBlock p * realBlock q)) = realBlock p * realBlock q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [coordinates, quaternionBlock, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im] <;> ring

/-- Left multiplication in the real quaternion coordinates. -/
def leftMap (A : SU2) : Coordinates →ₗ[ℝ] Coordinates where
  toFun x := WithLp.toLp 2 (coordinates ((A : Matrix (Fin 2) (Fin 2) ℂ) * realBlock x.ofLp))
  map_add' x y := by
    apply WithLp.ofLp_injective
    funext i
    fin_cases i <;>
      simp [coordinates, quaternionBlock, Matrix.mul_apply, Fin.sum_univ_two,
        Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im] <;> ring
  map_smul' c x := by
    apply WithLp.ofLp_injective
    funext i
    fin_cases i <;>
      simp [coordinates, quaternionBlock, Matrix.mul_apply, Fin.sum_univ_two,
        Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im] <;> ring

theorem block_leftMap (A : SU2) (x : Coordinates) :
    realBlock (leftMap A x).ofLp = (A : Matrix (Fin 2) (Fin 2) ℂ) * realBlock x.ofLp := by
  change realBlock (coordinates ((A : Matrix (Fin 2) (Fin 2) ℂ) * realBlock x.ofLp)) = _
  rw [← block_coordinates A]
  exact block_coordinates_mul _ _

theorem leftMap_norm (A : SU2) (x : Coordinates) : ‖leftMap A x‖ = ‖x‖ := by
  have h := congrArg Matrix.det (block_leftMap A x)
  rw [Matrix.det_mul, (Matrix.mem_specialUnitaryGroup_iff.mp A.property).2, one_mul,
    block_det, block_det] at h
  have hr := congrArg Complex.re h
  simp only [Complex.ofReal_re] at hr
  have hsq (y : Coordinates) : ‖y‖ ^ 2 = ∑ i, y.ofLp i ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      PiLp.norm_sq_eq_of_L2 (fun _ : Fin 4 ↦ ℝ) y
  rw [← hsq, ← hsq] at hr
  nlinarith [norm_nonneg (leftMap A x), norm_nonneg x]

theorem leftMap_surjective (A : SU2) : Function.Surjective (leftMap A) := by
  intro x
  refine ⟨leftMap A⁻¹ x, ?_⟩
  have hb := block_leftMap A (leftMap A⁻¹ x)
  rw [block_leftMap A⁻¹ x, ← mul_assoc] at hb
  have hA : (A : Matrix (Fin 2) (Fin 2) ℂ) * (↑A⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    exact congrArg (fun g : SU2 ↦ (g : Matrix (Fin 2) (Fin 2) ℂ)) (mul_inv_cancel A)
  rw [hA, one_mul] at hb
  apply WithLp.ofLp_injective
  simpa only [coordinates_block] using congrArg coordinates hb

/-- The real-linear orthogonal action induced by physical left multiplication. -/
def leftIsometry (A : SU2) : Coordinates ≃ₗᵢ[ℝ] Coordinates :=
  LinearIsometryEquiv.ofSurjective ⟨leftMap A, leftMap_norm A⟩ (leftMap_surjective A)

/-- The orthogonal left action restricts to the Euclidean unit sphere. -/
def leftOnSphere (A : SU2) (x : UnitSphere) : UnitSphere :=
  ⟨leftIsometry A x.val, by
    have hx := x.property
    simpa only [Metric.mem_sphere, dist_zero_right, LinearIsometryEquiv.norm_map] using hx⟩

theorem sphereHomeomorphSU2_left (A : SU2) (x : UnitSphere) :
    sphereHomeomorphSU2 (leftOnSphere A x) = A * sphereHomeomorphSU2 x := by
  apply Subtype.ext
  exact block_leftMap A x.val

theorem leftOnSphere_one (x : UnitSphere) : leftOnSphere 1 x = x := by
  apply sphereHomeomorphSU2.injective
  rw [sphereHomeomorphSU2_left, one_mul]

theorem leftOnSphere_mul (A B : SU2) (x : UnitSphere) :
    leftOnSphere (A * B) x = leftOnSphere A (leftOnSphere B x) := by
  apply sphereHomeomorphSU2.injective
  simp only [sphereHomeomorphSU2_left, mul_assoc]

end SKEFTHawking.ADW.QuaternionSU2Sphere
