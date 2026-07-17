import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Cube ≅ Euclidean ball, matching boundaries (`EuclideanSpace ℝ (Fin n)`)

A reusable point-set topology brick: the closed sup-norm cube
`cube n = {x | ∀ i, |x i| ≤ 1}` in `EuclideanSpace ℝ (Fin n)` is homeomorphic to the closed
Euclidean unit ball `Metric.closedBall 0 1`, with the homeomorphism carrying the cube's frontier
onto the Euclidean sphere and the cube's interior onto the open Euclidean ball.

The construction reuses Mathlib's `gaugeRescaleHomeomorph`: both the cube and the ball are convex,
von Neumann bounded neighbourhoods of the origin, so the gauge-rescale map (radially rescale each
ray so its cube-gauge becomes its ball-gauge) is the required homeomorphism, and Mathlib already
proves it matches interiors and closures (`image_gaugeRescaleHomeomorph_interior/closure`); the
frontier match follows from `closure \ interior`.

## Headlines

* `cubeBallHomeo n : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n)` — the self-homeomorphism.
* `cubeBallHomeo_image_frontier` / `_interior` / `_cube` — the boundary/interior/whole-set image facts.
* `cubeBallSubtypeHomeo n : ↥(cube n) ≃ₜ ↥(Metric.closedBall 0 1)` — the subtype homeomorphism,
  packaged for `RelativeHomology.map_bijective_of_homotopyEquiv_pair`.

This is pure Mathlib point-set topology; it references nothing from the physics/bordism substrate.
-/

namespace SKEFTHawking.CubeBallHomeo

open Metric Set Bornology
open scoped Topology

variable (n : ℕ)

/-- The closed cube = sup-norm closed unit ball in `EuclideanSpace ℝ (Fin n)`. -/
def cube : Set (EuclideanSpace ℝ (Fin n)) := {x | ∀ i, |x i| ≤ 1}

lemma mem_cube {x : EuclideanSpace ℝ (Fin n)} : x ∈ cube n ↔ ∀ i, |x i| ≤ 1 := Iff.rfl

/-- `cube n` is convex. -/
lemma convex_cube : Convex ℝ (cube n) := by
  intro x hx y hy a b ha hb hab i
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hxi := hx i
  have hyi := hy i
  rw [abs_le] at hxi hyi ⊢
  constructor <;> nlinarith [hxi.1, hxi.2, hyi.1, hyi.2]

/-- The cube is a neighbourhood of the origin. -/
lemma cube_mem_nhds : cube n ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin n)) := by
  rw [Metric.mem_nhds_iff]
  refine ⟨1, one_pos, fun z hz i => ?_⟩
  rw [mem_ball_zero_iff] at hz
  have hb : |z i| ≤ ‖z‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le z i
  linarith [hb, hz]

/-- The cube is bounded. -/
lemma isBounded_cube : IsBounded (cube n) := by
  refine (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin n)))
    (r := Real.sqrt n)).subset ?_
  intro x hx
  rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  calc ∑ i, ‖x.ofLp i‖ ^ 2 ≤ ∑ _i : Fin n, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have hi : ‖x i‖ ≤ 1 := by rw [Real.norm_eq_abs]; exact hx i
        exact pow_le_one₀ (norm_nonneg _) hi
    _ = (n:ℝ) := by simp

lemma isVonNBounded_cube : IsVonNBounded ℝ (cube n) :=
  NormedSpace.isVonNBounded_of_isBounded _ (isBounded_cube n)

/-- `cube n` is closed (finite intersection of the closed coordinate slabs `|x i| ≤ 1`). -/
lemma isClosed_cube : IsClosed (cube n) := by
  have hEq : cube n = ⋂ i, {x : EuclideanSpace ℝ (Fin n) | |x i| ≤ 1} := by
    ext x; simp only [mem_cube, mem_iInter, mem_setOf_eq]
  rw [hEq]
  refine isClosed_iInter fun i => isClosed_le ?_ continuous_const
  exact continuous_abs.comp (by fun_prop)

/-- The gauge-rescale homeomorphism carrying the closed cube model to the closed Euclidean ball
model. Radially rescales each ray so its cube-gauge becomes its ball-gauge; fixes the origin. -/
noncomputable def cubeBallHomeo : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n) :=
  gaugeRescaleHomeomorph (cube n) (closedBall 0 1)
    (convex_cube n) (cube_mem_nhds n) (isVonNBounded_cube n)
    (convex_closedBall 0 1) (closedBall_mem_nhds 0 one_pos)
    (NormedSpace.isVonNBounded_closedBall ℝ _ 1)

/-- The homeomorphism carries the open cube (interior) onto the open Euclidean unit ball. -/
lemma cubeBallHomeo_image_interior :
    cubeBallHomeo n '' interior (cube n) = ball 0 1 := by
  rw [cubeBallHomeo, image_gaugeRescaleHomeomorph_interior, interior_closedBall _ one_ne_zero]

/-- The homeomorphism carries the closure of the cube onto the closed Euclidean unit ball. -/
lemma cubeBallHomeo_image_closure :
    cubeBallHomeo n '' closure (cube n) = closedBall 0 1 := by
  rw [cubeBallHomeo, image_gaugeRescaleHomeomorph_closure, isClosed_closedBall.closure_eq]

/-- The homeomorphism carries the whole closed cube onto the closed Euclidean unit ball. -/
lemma cubeBallHomeo_image_cube :
    cubeBallHomeo n '' cube n = closedBall 0 1 := by
  rw [← (isClosed_cube n).closure_eq, cubeBallHomeo_image_closure]

/-- The homeomorphism carries the cube frontier (its faces) onto the Euclidean unit sphere. -/
lemma cubeBallHomeo_image_frontier :
    cubeBallHomeo n '' frontier (cube n) = sphere 0 1 := by
  rw [frontier, image_diff (cubeBallHomeo n).injective, cubeBallHomeo_image_closure,
    cubeBallHomeo_image_interior, closedBall_diff_ball]

/-- The inverse homeomorphism carries the Euclidean sphere back onto the cube frontier. -/
lemma cubeBallHomeo_symm_image_sphere :
    (cubeBallHomeo n).symm '' sphere 0 1 = frontier (cube n) := by
  rw [← cubeBallHomeo_image_frontier n, ← Set.image_comp]
  simp

/-! ### `MapsTo` facts on the ambient space -/

/-- Boundary correspondence, forward: cube frontier ↦ Euclidean sphere. -/
lemma mapsTo_cubeBallHomeo_frontier :
    MapsTo (cubeBallHomeo n) (frontier (cube n)) (sphere 0 1) :=
  mapsTo_iff_image_subset.mpr (cubeBallHomeo_image_frontier n).subset

/-- Boundary correspondence, backward: Euclidean sphere ↦ cube frontier. -/
lemma mapsTo_cubeBallHomeo_symm_sphere :
    MapsTo (cubeBallHomeo n).symm (sphere 0 1) (frontier (cube n)) :=
  mapsTo_iff_image_subset.mpr (cubeBallHomeo_symm_image_sphere n).subset

/-- Interior correspondence, forward: open cube ↦ open Euclidean ball. -/
lemma mapsTo_cubeBallHomeo_interior :
    MapsTo (cubeBallHomeo n) (interior (cube n)) (ball 0 1) :=
  mapsTo_iff_image_subset.mpr (cubeBallHomeo_image_interior n).subset

/-- Whole-set correspondence, forward: closed cube ↦ closed Euclidean ball. -/
lemma mapsTo_cubeBallHomeo_cube :
    MapsTo (cubeBallHomeo n) (cube n) (closedBall 0 1) :=
  mapsTo_iff_image_subset.mpr (cubeBallHomeo_image_cube n).subset

/-! ### Subtype homeomorphism and boundary sets (packaged for the pair consumer)

`RelativeHomology.map_bijective_of_homotopyEquiv_pair` consumes `X Y : TopCat`, `A : Set ↑X`,
`B : Set ↑Y`, an `f : C(↑X, ↑Y)`, `g : C(↑Y, ↑X)`, `Set.MapsTo` facts, and pair homotopies. Take
`X = ↥(cube n)`, `Y = ↥(closedBall 0 1)`, `A = cubeBoundary n`, `B = ballBoundary n`,
`f = (cubeBallSubtypeHomeo n).toContinuousMap`, `g = (cubeBallSubtypeHomeo n).symm.toContinuousMap`.
Since `f` and `g` are two-sided inverses on the nose, the required homotopies are constant. -/

/-- The cube-to-ball homeomorphism as a homeomorphism of subtypes. -/
noncomputable def cubeBallSubtypeHomeo :
    ↥(cube n) ≃ₜ ↥(closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  ((cubeBallHomeo n).image (cube n)).trans (Homeomorph.setCongr (cubeBallHomeo_image_cube n))

@[simp] lemma cubeBallSubtypeHomeo_coe (p : ↥(cube n)) :
    (↑(cubeBallSubtypeHomeo n p) : EuclideanSpace ℝ (Fin n)) = cubeBallHomeo n ↑p := by
  simp [cubeBallSubtypeHomeo, Homeomorph.setCongr]

@[simp] lemma cubeBallSubtypeHomeo_symm_coe
    (q : ↥(closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) :
    (↑((cubeBallSubtypeHomeo n).symm q) : EuclideanSpace ℝ (Fin n)) = (cubeBallHomeo n).symm ↑q := by
  have h := cubeBallSubtypeHomeo_coe n ((cubeBallSubtypeHomeo n).symm q)
  rw [Homeomorph.apply_symm_apply] at h
  rw [h, Homeomorph.symm_apply_apply]

/-- The cube boundary (its faces) as a subset of the cube subtype. -/
def cubeBoundary : Set ↥(cube n) := {p | (↑p : EuclideanSpace ℝ (Fin n)) ∈ frontier (cube n)}

/-- The Euclidean unit sphere as a subset of the closed-ball subtype. -/
def ballBoundary : Set ↥(closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  {q | (↑q : EuclideanSpace ℝ (Fin n)) ∈ sphere 0 1}

/-- Subtype-level boundary correspondence, forward — the `hf` argument for the pair consumer. -/
lemma mapsTo_cubeBallSubtypeHomeo_boundary :
    MapsTo (cubeBallSubtypeHomeo n) (cubeBoundary n) (ballBoundary n) := by
  intro p hp
  simp only [ballBoundary, mem_setOf_eq, cubeBallSubtypeHomeo_coe]
  exact mapsTo_cubeBallHomeo_frontier n hp

/-- Subtype-level boundary correspondence, backward — the `hg` argument for the pair consumer. -/
lemma mapsTo_cubeBallSubtypeHomeo_symm_boundary :
    MapsTo (cubeBallSubtypeHomeo n).symm (ballBoundary n) (cubeBoundary n) := by
  intro q hq
  simp only [cubeBoundary, mem_setOf_eq, cubeBallSubtypeHomeo_symm_coe]
  exact mapsTo_cubeBallHomeo_symm_sphere n hq

end SKEFTHawking.CubeBallHomeo
