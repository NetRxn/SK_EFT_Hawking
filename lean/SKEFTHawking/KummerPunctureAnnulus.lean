/-
# Phase 5q.H — the puncture-MV piece homology tables: `H₊(D⁴) = 0`, `H₁(Ann⁴) = H₂(Ann⁴) = 0`

The integral homology value tables of the two puncture-MV piece models (`KummerPunctureBalls`):

* the closed chart ball `D⁴` is carried by the `E⁴` coordinate bridge (`KummerShellChart.toE4`)
  onto the convex `Metric.closedBall 0 (1/2)`, so `H_{k+1}(D⁴;ℤ) = 0`
  (`SingularConvexSubAcyclicInt`);
* the closed chart annulus `Ann⁴ = {ρ/2 ≤ ‖t‖ ≤ ρ}` is carried onto the Euclidean annulus,
  which deformation-retracts onto its outer sphere `‖w‖ = 1/2` by the straight-line radial
  normalization; scaling identifies that sphere with the banked unit `S³` (`Sph 3`), whose middle
  homology vanishes (`SingularSphereMiddleInt.sphere_homology_middleInt`). Hence
  `H_j(Ann⁴;ℤ) = 0` for `0 < j < 3` — the two vanishing inputs of the puncture MV window.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerPunctureBalls
import SKEFTHawking.SingularMayerVietorisLESInt
import SKEFTHawking.SingularConvexSubAcyclicInt
import SKEFTHawking.SingularSphereMiddleInt
import SKEFTHawking.SingularFiniteProdDiscreteHnInt

namespace SKEFTHawking.KummerPunctureAnnulus

open SKEFTHawking.KummerPunctureBalls
open SKEFTHawking.KummerShellChart (toE4 ofE4 norm_sq_toE4 sqNorm_ofE4 continuous_ofE4
  continuous_toE4 ofE4_toE4 toE4_ofE4)
open SKEFTHawking.KummerPuncturedTorus (sqNorm abs_le_of_sq_le_sq)
open SKEFTHawking.SingularHomologyInt (Homology)
open SKEFTHawking.SingularFunctorialityInt (Homology.mapInt)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularEuclideanAcyclic (Eucl)
open SKEFTHawking.SingularSphereAcyclic (Sph)
open SKEFTHawking.SingularFiniteProdDiscreteHnInt (homologyCongrInt)
open SKEFTHawking.SingularMayerVietorisLES (subIncl)

noncomputable section

/-! ## §1. The Euclidean models and the coordinate homeomorphisms -/

/-- The Euclidean closed annulus `{1/4 ≤ ‖w‖ ≤ 1/2} ⊆ E⁴`. -/
def annE : Set (EuclideanSpace ℝ (Fin 4)) := {w | 1 / 4 ≤ ‖w‖ ∧ ‖w‖ ≤ 1 / 2}

/-- The outer sphere `‖w‖ = 1/2` of the Euclidean annulus. -/
def sphHalf : Set (EuclideanSpace ℝ (Fin 4)) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 / 2)

theorem mem_annE_iff {w : EuclideanSpace ℝ (Fin 4)} :
    w ∈ annE ↔ 1 / 4 ≤ ‖w‖ ∧ ‖w‖ ≤ 1 / 2 := Iff.rfl

theorem mem_sphHalf_iff {w : EuclideanSpace ℝ (Fin 4)} : w ∈ sphHalf ↔ ‖w‖ = 1 / 2 :=
  mem_sphere_zero_iff_norm

theorem sphHalf_subset_annE : sphHalf ⊆ annE := fun w hw => by
  rw [mem_sphHalf_iff] at hw
  exact ⟨by rw [hw]; norm_num, le_of_eq hw⟩

/-- Squared-norm-to-norm conversion at the outer radius. -/
theorem norm_toE4_le_half {t : ℝ × ℝ × ℝ × ℝ} (ht : sqNorm t ≤ 1 / 4) : ‖toE4 t‖ ≤ 1 / 2 := by
  have h1 : ‖toE4 t‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    rw [norm_sq_toE4]
    norm_num
    linarith
  have h2 := abs_le_of_sq_le_sq (by norm_num) h1
  rwa [abs_of_nonneg (norm_nonneg _)] at h2

/-- Squared-norm-to-norm conversion at the inner radius. -/
theorem quarter_le_norm_toE4 {t : ℝ × ℝ × ℝ × ℝ} (ht : 1 / 16 ≤ sqNorm t) :
    1 / 4 ≤ ‖toE4 t‖ := by
  by_contra hlt
  rw [not_le] at hlt
  have h1 : ‖toE4 t‖ ^ 2 < (1 / 4 : ℝ) ^ 2 := by
    have := norm_nonneg (toE4 t)
    nlinarith
  rw [norm_sq_toE4] at h1
  norm_num at h1
  linarith

theorem toE4_mem_closedBall (t : ↥D4) :
    toE4 t.1 ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) (1 / 2) := by
  rw [Metric.mem_closedBall, dist_zero_right]
  exact norm_toE4_le_half t.2

theorem ofE4_mem_D4 (w : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) (1 / 2))) :
    ofE4 w.1 ∈ D4 := by
  have hw : ‖(w : EuclideanSpace ℝ (Fin 4))‖ ≤ 1 / 2 := by
    have := w.2
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  rw [D4, Set.mem_setOf_eq, sqNorm_ofE4]
  nlinarith [norm_nonneg (w : EuclideanSpace ℝ (Fin 4))]

theorem toE4_mem_annE (t : ↥ann4) : toE4 t.1 ∈ annE :=
  ⟨quarter_le_norm_toE4 t.2.1, norm_toE4_le_half t.2.2⟩

theorem ofE4_mem_ann4 (w : ↥annE) : ofE4 w.1 ∈ ann4 := by
  obtain ⟨h1, h2⟩ := w.2
  constructor
  · show 1 / 16 ≤ sqNorm (ofE4 (w : EuclideanSpace ℝ (Fin 4)))
    rw [sqNorm_ofE4]
    nlinarith
  · show sqNorm (ofE4 (w : EuclideanSpace ℝ (Fin 4))) ≤ 1 / 4
    rw [sqNorm_ofE4]
    nlinarith [norm_nonneg (w : EuclideanSpace ℝ (Fin 4))]

/-- **The coordinate homeomorphism** `D⁴ ≃ₜ Metric.closedBall 0 (1/2)` (in `E⁴`). -/
def d4HomeoBall : ↥D4 ≃ₜ ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) (1 / 2)) where
  toFun t := ⟨toE4 t.1, toE4_mem_closedBall t⟩
  invFun w := ⟨ofE4 w.1, ofE4_mem_D4 w⟩
  left_inv t := Subtype.ext (ofE4_toE4 t.1)
  right_inv w := Subtype.ext (toE4_ofE4 w.1)
  continuous_toFun :=
    (continuous_toE4.comp continuous_subtype_val).subtype_mk fun t => toE4_mem_closedBall t
  continuous_invFun :=
    (continuous_ofE4.comp continuous_subtype_val).subtype_mk fun w => ofE4_mem_D4 w

/-- **The coordinate homeomorphism** `Ann⁴ ≃ₜ annE` (in `E⁴`). -/
def ann4HomeoE : ↥ann4 ≃ₜ ↥annE where
  toFun t := ⟨toE4 t.1, toE4_mem_annE t⟩
  invFun w := ⟨ofE4 w.1, ofE4_mem_ann4 w⟩
  left_inv t := Subtype.ext (ofE4_toE4 t.1)
  right_inv w := Subtype.ext (toE4_ofE4 w.1)
  continuous_toFun :=
    (continuous_toE4.comp continuous_subtype_val).subtype_mk fun t => toE4_mem_annE t
  continuous_invFun :=
    (continuous_ofE4.comp continuous_subtype_val).subtype_mk fun w => ofE4_mem_ann4 w

/-! ## §2. The ball table: `H_{k+1}(D⁴;ℤ) = 0` -/

/-- **The closed chart ball is integrally acyclic in positive degrees** — the coordinate bridge
carries it onto the convex `closedBall 0 (1/2)`. -/
theorem d4_homology_vanish (k : ℕ) (x : Homology (TopCat.of ↥D4) (k + 1)) : x = 0 := by
  set e := homologyCongrInt (X := TopCat.of ↥D4)
    (Y := sub (X := Eucl 4) (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) (1 / 2)))
    d4HomeoBall (k + 1) with he
  have hx0 : e x = 0 :=
    SKEFTHawking.SingularConvexSubAcyclicInt.homology_convexSub_eq_zeroInt
      (convex_closedBall _ _) (Metric.mem_closedBall_self (by norm_num)) k _
  exact (LinearEquiv.map_eq_zero_iff e).mp hx0

/-! ## §3. The annulus retracts onto its outer sphere -/

theorem annE_norm_pos {w : ↥annE} : (0 : ℝ) < ‖(w : EuclideanSpace ℝ (Fin 4))‖ :=
  lt_of_lt_of_le (by norm_num) w.2.1

theorem annE_norm_ne {w : ↥annE} : ‖(w : EuclideanSpace ℝ (Fin 4))‖ ≠ 0 :=
  ne_of_gt annE_norm_pos

/-- The radial normalization lands on the outer sphere. -/
theorem radial_mem_sphHalf (w : ↥annE) :
    ((1 / 2) * ‖(w : EuclideanSpace ℝ (Fin 4))‖⁻¹) • (w : EuclideanSpace ℝ (Fin 4))
      ∈ sphHalf := by
  rw [mem_sphHalf_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    mul_assoc, inv_mul_cancel₀ annE_norm_ne, mul_one]

/-- The straight-line radial homotopy stays in the annulus: the time-`s` scaled norm is
`s‖w‖ + (1−s)ρ ∈ [ρ/2, ρ]`. -/
theorem radial_htpy_mem_annE (w : ↥annE) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (s + (1 - s) * ((1 / 2) * ‖(w : EuclideanSpace ℝ (Fin 4))‖⁻¹)) •
        (w : EuclideanSpace ℝ (Fin 4)) ∈ annE := by
  set a := ‖(w : EuclideanSpace ℝ (Fin 4))‖ with ha
  have ha1 : 1 / 4 ≤ a := w.2.1
  have ha2 : a ≤ 1 / 2 := w.2.2
  have hane : a ≠ 0 := by positivity
  have hf0 : (0 : ℝ) ≤ s + (1 - s) * ((1 / 2) * a⁻¹) :=
    add_nonneg hs0 (mul_nonneg (by linarith) (by positivity))
  have hnorm : ‖(s + (1 - s) * ((1 / 2) * a⁻¹)) • (w : EuclideanSpace ℝ (Fin 4))‖
      = s * a + (1 - s) * (1 / 2) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hf0, ← ha, add_mul, mul_assoc,
      mul_assoc, inv_mul_cancel₀ hane, mul_one]
  rw [mem_annE_iff, hnorm]
  constructor
  · nlinarith
  · nlinarith

/-- The sphere inclusion `sphHalf ↪ annE`. -/
def sphInclC : C(↑(sub (X := Eucl 4) sphHalf), ↑(sub (X := Eucl 4) annE)) :=
  subIncl sphHalf_subset_annE

/-- The radial normalization retraction `annE → sphHalf`, `w ↦ (ρ/‖w‖) w`. -/
def sphRetrC : C(↑(sub (X := Eucl 4) annE), ↑(sub (X := Eucl 4) sphHalf)) :=
  ⟨fun w => ⟨((1 / 2) * ‖(w : EuclideanSpace ℝ (Fin 4))‖⁻¹) •
      (w : EuclideanSpace ℝ (Fin 4)), radial_mem_sphHalf w⟩,
   ((continuous_const.mul ((continuous_norm.comp continuous_subtype_val).inv₀
      fun _ => annE_norm_ne)).smul continuous_subtype_val).subtype_mk
        fun w => radial_mem_sphHalf w⟩

/-- The trivial homotopy on the sphere. -/
def sphTrivHtpyC :
    C(↑(sub (X := Eucl 4) sphHalf) × unitInterval, ↑(sub (X := Eucl 4) sphHalf)) :=
  ⟨fun p => p.1, continuous_fst⟩

/-- The straight-line radial homotopy on the annulus: at time `s` the point `w` is scaled by
`s + (1−s)·(ρ/‖w‖)`. -/
def annHtpyC :
    C(↑(sub (X := Eucl 4) annE) × unitInterval, ↑(sub (X := Eucl 4) annE)) :=
  ⟨fun p =>
    ⟨((p.2 : ℝ) + (1 - (p.2 : ℝ)) * ((1 / 2) * ‖(p.1 : EuclideanSpace ℝ (Fin 4))‖⁻¹)) •
        (p.1 : EuclideanSpace ℝ (Fin 4)),
      radial_htpy_mem_annE p.1 p.2.2.1 p.2.2.2⟩,
   by
    have hn : Continuous fun p : ↑(sub (X := Eucl 4) annE) × unitInterval =>
        ‖((p.1 : ↑(sub (X := Eucl 4) annE)) : EuclideanSpace ℝ (Fin 4))‖⁻¹ :=
      (continuous_norm.comp (continuous_subtype_val.comp continuous_fst)).inv₀
        fun p => annE_norm_ne
    have hs : Continuous fun p : ↑(sub (X := Eucl 4) annE) × unitInterval => ((p.2 : ℝ)) :=
      continuous_subtype_val.comp continuous_snd
    exact ((hs.add ((continuous_const.sub hs).mul (continuous_const.mul hn))).smul
      (continuous_subtype_val.comp continuous_fst)).subtype_mk
        fun p => radial_htpy_mem_annE p.1 p.2.2.1 p.2.2.2⟩

/-- **The annulus deformation-retracts onto its outer sphere**: the inclusion induces a homology
isomorphism in every positive degree. -/
theorem sphIncl_mapInt_bijective (n : ℕ) :
    Function.Bijective (Homology.mapInt sphInclC (n + 1)) := by
  refine SKEFTHawking.SingularFunctorialityInt.Homology.mapInt_bijective_of_homotopyEquiv
    sphInclC sphRetrC sphTrivHtpyC ?_ ?_ annHtpyC ?_ ?_ n
  · refine ContinuousMap.ext fun x => Subtype.ext ?_
    have hx : ‖(x : EuclideanSpace ℝ (Fin 4))‖ = 1 / 2 := mem_sphHalf_iff.mp x.2
    dsimp only [SingularHomotopyInvariance.slice, sphTrivHtpyC, sphRetrC, sphInclC,
      ContinuousMap.comp_apply, ContinuousMap.coe_mk,
      SKEFTHawking.SingularMayerVietorisLES.subIncl, ContinuousMap.prodMk, ContinuousMap.const_apply,
      ContinuousMap.id_apply]
    rw [hx]
    norm_num
  · exact ContinuousMap.ext fun _ => rfl
  · refine ContinuousMap.ext fun x => Subtype.ext ?_
    dsimp only [SingularHomotopyInvariance.slice, annHtpyC, sphRetrC, sphInclC,
      ContinuousMap.comp_apply, ContinuousMap.coe_mk,
      SKEFTHawking.SingularMayerVietorisLES.subIncl, ContinuousMap.prodMk, ContinuousMap.const_apply,
      ContinuousMap.id_apply]
    norm_num [show ((0 : unitInterval) : ℝ) = 0 from rfl]
  · refine ContinuousMap.ext fun x => Subtype.ext ?_
    dsimp only [SingularHomotopyInvariance.slice, annHtpyC,
      ContinuousMap.comp_apply, ContinuousMap.coe_mk, ContinuousMap.prodMk, ContinuousMap.const_apply,
      ContinuousMap.id_apply]
    norm_num [show ((1 : unitInterval) : ℝ) = 1 from rfl]

/-! ## §4. The outer sphere is the banked `S³` -/

theorem smul_two_mem_unitSphere (x : ↥sphHalf) :
    (2 : ℝ) • (x : EuclideanSpace ℝ (Fin 4))
      ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 := by
  have hx : ‖(x : EuclideanSpace ℝ (Fin 4))‖ = 1 / 2 := mem_sphHalf_iff.mp x.2
  rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, hx]
  norm_num

theorem smul_half_mem_sphHalf (y : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) :
    (2⁻¹ : ℝ) • (y : EuclideanSpace ℝ (Fin 4)) ∈ sphHalf := by
  have hy : ‖(y : EuclideanSpace ℝ (Fin 4))‖ = 1 := mem_sphere_zero_iff_norm.mp y.2
  rw [mem_sphHalf_iff, norm_smul, Real.norm_eq_abs, hy]
  norm_num

/-- **The scaling homeomorphism** `{‖w‖ = 1/2} ≃ₜ S³` (the banked unit sphere `Sph 3`). -/
def sphHalfHomeoSph3 : ↑(sub (X := Eucl 4) sphHalf) ≃ₜ ↑(Sph 3) where
  toFun x := ⟨(2 : ℝ) • (x : EuclideanSpace ℝ (Fin 4)), smul_two_mem_unitSphere x⟩
  invFun y := ⟨(2⁻¹ : ℝ) • (y : EuclideanSpace ℝ (Fin 4)), smul_half_mem_sphHalf y⟩
  left_inv x := Subtype.ext (by
    show (2⁻¹ : ℝ) • ((2 : ℝ) • (x : EuclideanSpace ℝ (Fin 4)))
      = (x : EuclideanSpace ℝ (Fin 4))
    rw [smul_smul]
    norm_num)
  right_inv y := Subtype.ext (by
    show (2 : ℝ) • ((2⁻¹ : ℝ) • (y : EuclideanSpace ℝ (Fin 4)))
      = (y : EuclideanSpace ℝ (Fin 4))
    rw [smul_smul]
    norm_num)
  -- v4.32: `Continuous.smul` now concludes a Pi-smul, and unifying that against these pointwise
  -- `c • _` goals runs the whnf budget out. Both scalars here are constant, so
  -- `Continuous.const_smul` is the direct lemma.
  continuous_toFun :=
    (continuous_subtype_val.const_smul (2 : ℝ)).subtype_mk fun x => smul_two_mem_unitSphere x
  continuous_invFun :=
    (continuous_subtype_val.const_smul (2⁻¹ : ℝ)).subtype_mk fun y => smul_half_mem_sphHalf y

/-! ## §5. The annulus table: `H_j(Ann⁴;ℤ) = 0` for `0 < j < 3` -/

/-- **The middle homology of the closed chart annulus vanishes** — retraction to the outer
sphere, scaling to the unit `S³`, banked middle-sphere vanishing. The two degrees `j = 1, 2`
are the puncture-MV window inputs. -/
theorem ann4_homology_vanish {j : ℕ} (h0 : 0 < j) (h3 : j < 3)
    (x : Homology (TopCat.of ↥ann4) j) : x = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  set e := homologyCongrInt (X := TopCat.of ↥ann4) (Y := sub (X := Eucl 4) annE)
    ann4HomeoE (k + 1) with he
  refine (LinearEquiv.map_eq_zero_iff e).mp ?_
  obtain ⟨y, hy⟩ := (sphIncl_mapInt_bijective k).surjective (e x)
  have hy0 : y = 0 := by
    set e2 := homologyCongrInt (X := sub (X := Eucl 4) sphHalf) (Y := Sph 3)
      sphHalfHomeoSph3 (k + 1) with he2
    refine (LinearEquiv.map_eq_zero_iff e2).mp ?_
    exact SKEFTHawking.SingularSphereMiddleInt.sphere_homology_middleInt (k + 1) 3
      (Nat.succ_pos k) (by omega) _
  rw [hy0, map_zero] at hy
  exact hy.symm

end

end SKEFTHawking.KummerPunctureAnnulus
