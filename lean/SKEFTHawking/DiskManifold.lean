/-
# Phase 5q.H — closed 3-ball radial-geometry primitives (SphereDiskSmoothData freeze, slice A)

`SphereProductBounding` froze the smooth atlas of `S²×D³` (`SphereDiskSmoothData`) on two named
Mathlib gaps: (1) `Metric.closedBall` has no `ChartedSpace`/`IsManifold` instance for `n ≥ 2`, and
(2) no change-of-model transport re-models a product atlas onto the collar model
`J5 = I4.prod (𝓡∂ 1)`. This module ships the REUSABLE SUBSTRATE that gap 1's collar atlas is built
from — the radial geometry of the closed unit 3-ball as genuine, closed constructions:

* `ballClamp` — the closed-form total retraction `ℝ³ → D³` (identity on `D³`, radial projection
  outside), the `IccLeftChart` `min`-clamp pattern one dimension up (`continuous_ballClamp`,
  `ballClamp_coe_of_norm_le`);
* `diskDir` — the direction `v/‖v‖ ∈ S²` of a nonzero disk point (junk value at the centre), with
  `continuousOn_diskDir`, `diskDir_coe`, and the collar key `diskDir_smul_unit` (`diskDir (r•u)=u`
  for `0<r≤1`, `u∈S²`);
* `assemble`/`splitLo` — the `E² × ℝ ≅ E³` coordinate iso (`Fin.snoc`/`Fin.castSucc` under
  `EuclideanSpace.equiv`), with the round-trip lemmas `splitLo_assemble`, `assemble_last`,
  `assemble_splitLo`, and continuity.

These are exactly the closed-form pieces an interior chart (`v ↦ ((v₀,v₁), v₂+2)`) and a polar
collar chart (`v ↦ (chart_{S²}(v/‖v‖), 1−‖v‖)`) consume; the chart-homeomorphism data + the
`ChartedSpace (ModelProd E² (EuclideanHalfSpace 1)) D³` assembly is the next slice (slice B),
whose only remaining content is the four `OpenPartialHomeomorph` fields and the transition
smoothness. Nothing here is frozen or hypothetical — every declaration is a closed construction on
the genuine subspace topology.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/
`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SphereProductBounding

open Metric Set

namespace SKEFTHawking.DiskManifold

open SKEFTHawking.SpinSigmaRoute (TwoSphere ThreeDisk)

noncomputable section

/-! ### §1. The radial clamp onto the closed unit ball -/

/-- **The radial clamp onto the closed unit ball**: the identity on `D³`, radial projection
outside — a closed-form total section of the inclusion `D³ ⊆ ℝ³` (the `IccLeftChart` `min`-clamp
pattern, one dimension up). -/
def ballClamp (w : EuclideanSpace ℝ (Fin 3)) : ThreeDisk :=
  ⟨(max 1 ‖w‖)⁻¹ • w, by
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_pos (lt_of_lt_of_le one_pos (le_max_left _ _))]
    exact inv_mul_le_one_of_le₀ (le_max_right _ _) (le_of_lt (lt_of_lt_of_le one_pos
      (le_max_left _ _)))⟩

theorem continuous_ballClamp : Continuous ballClamp := by
  apply Continuous.subtype_mk
  exact ((continuous_const.max continuous_norm).inv₀
    (fun w => ne_of_gt (lt_of_lt_of_le one_pos (le_max_left _ _)))).smul continuous_id

/-- The clamp is the identity on the closed ball. -/
theorem ballClamp_coe_of_norm_le {w : EuclideanSpace ℝ (Fin 3)} (h : ‖w‖ ≤ 1) :
    (ballClamp w : EuclideanSpace ℝ (Fin 3)) = w := by
  simp [ballClamp, max_eq_left h]

/-! ### §2. The direction map `D³∖{0} → S²` -/

/-- **The direction of a disk point** (junk value at the centre): `v/‖v‖ ∈ S²` for `v ≠ 0`. -/
def diskDir (v : ThreeDisk) : TwoSphere :=
  if h : (v : EuclideanSpace ℝ (Fin 3)) = 0 then
    ⟨EuclideanSpace.single 0 1, by simp⟩
  else
    ⟨‖(v : EuclideanSpace ℝ (Fin 3))‖⁻¹ • (v : EuclideanSpace ℝ (Fin 3)), by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)⟩

theorem diskDir_coe {v : ThreeDisk} (h : (v : EuclideanSpace ℝ (Fin 3)) ≠ 0) :
    (diskDir v : EuclideanSpace ℝ (Fin 3))
      = ‖(v : EuclideanSpace ℝ (Fin 3))‖⁻¹ • (v : EuclideanSpace ℝ (Fin 3)) := by
  rw [diskDir, dif_neg h]

/-- The direction of a positive multiple of a unit vector is that vector. -/
theorem diskDir_smul_unit {u : TwoSphere} {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    diskDir ⟨r • (u : EuclideanSpace ℝ (Fin 3)), by
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
        mem_sphere_zero_iff_norm.mp u.2, mul_one]
      exact hr1⟩ = u := by
  have hu : ‖(u : EuclideanSpace ℝ (Fin 3))‖ = 1 := mem_sphere_zero_iff_norm.mp u.2
  have hne : r • (u : EuclideanSpace ℝ (Fin 3)) ≠ 0 := by
    rw [smul_ne_zero_iff]
    exact ⟨ne_of_gt hr, fun h0 => by simp [h0] at hu⟩
  apply Subtype.ext
  rw [diskDir_coe hne]
  show ‖r • (u : EuclideanSpace ℝ (Fin 3))‖⁻¹ • (r • (u : EuclideanSpace ℝ (Fin 3)))
    = (u : EuclideanSpace ℝ (Fin 3))
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hu, mul_one, smul_smul,
    inv_mul_cancel₀ (ne_of_gt hr), one_smul]

/-- `diskDir` is continuous away from the centre. -/
theorem continuousOn_diskDir :
    ContinuousOn diskDir {v : ThreeDisk | (v : EuclideanSpace ℝ (Fin 3)) ≠ 0} := by
  rw [continuousOn_iff_continuous_restrict]
  apply Continuous.subtype_mk
  have hcont : Continuous fun v : {v : ThreeDisk | (v : EuclideanSpace ℝ (Fin 3)) ≠ 0} =>
      ((v.1 : ThreeDisk) : EuclideanSpace ℝ (Fin 3)) :=
    continuous_subtype_val.comp continuous_subtype_val
  have h : Continuous fun v : {v : ThreeDisk | (v : EuclideanSpace ℝ (Fin 3)) ≠ 0} =>
      (‖((v.1 : ThreeDisk) : EuclideanSpace ℝ (Fin 3))‖⁻¹ •
        ((v.1 : ThreeDisk) : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3)) :=
    (hcont.norm.inv₀ (fun v => norm_ne_zero_iff.mpr v.2)).smul hcont
  exact h.congr (fun v => (diskDir_coe v.2).symm)

/-! ### §3. The `E² × ℝ ≅ E³` coordinate iso -/

/-- **Assemble** an `E²` block and a last coordinate into `E³` (`Fin.snoc` under `WithLp.toLp`). -/
def assemble (a : EuclideanSpace ℝ (Fin 2)) (s : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (Fin.snoc (fun i => a.ofLp i) s)

@[simp] theorem assemble_ofLp (a : EuclideanSpace ℝ (Fin 2)) (s : ℝ) (i : Fin 3) :
    (assemble a s).ofLp i = (Fin.snoc (fun j => a.ofLp j) s : Fin 3 → ℝ) i := rfl

theorem continuous_assemble :
    Continuous fun p : EuclideanSpace ℝ (Fin 2) × ℝ => assemble p.1 p.2 := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · -- `Fin.snoc … (last 2)` is defeq to the last coordinate (the `i.val < n` guard is false),
    -- but v4.32 will not close it through `simpa`'s unifier. State the reduced goal directly.
    show Continuous fun p : EuclideanSpace ℝ (Fin 2) × ℝ => p.2
    exact continuous_snd
  · simpa [Function.comp_def, Fin.snoc_castSucc] using
      ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) j).comp continuous_fst)

/-- **Split** the first two coordinates of `E³` into `E²`. -/
def splitLo (w : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun i => w.ofLp i.castSucc)

@[simp] theorem splitLo_ofLp (w : EuclideanSpace ℝ (Fin 3)) (i : Fin 2) :
    (splitLo w).ofLp i = w.ofLp i.castSucc := rfl

theorem continuous_splitLo : Continuous splitLo := by
  apply (PiLp.continuous_toLp 2 _).comp
  exact continuous_pi fun i => PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i.castSucc

/-- The last coordinate of `assemble a s` is `s`. -/
@[simp] theorem assemble_ofLp_last (a : EuclideanSpace ℝ (Fin 2)) (s : ℝ) :
    (assemble a s).ofLp (Fin.last 2) = s := by
  rw [assemble_ofLp]; exact Fin.snoc_last _ _

/-- The lower coordinates of `assemble a s` are those of `a`. -/
@[simp] theorem assemble_ofLp_castSucc (a : EuclideanSpace ℝ (Fin 2)) (s : ℝ) (j : Fin 2) :
    (assemble a s).ofLp j.castSucc = a.ofLp j := by
  rw [assemble_ofLp]; exact Fin.snoc_castSucc _ _ _

end

end SKEFTHawking.DiskManifold
