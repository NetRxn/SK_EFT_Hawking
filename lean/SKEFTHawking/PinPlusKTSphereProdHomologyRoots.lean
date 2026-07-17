/-
# Phase 5q.H close-out (#211, HOMOLOGY-ROOTS) — the two homology-vanishing roots of the
# `S²×D³` coboundary, on the FIXED `SphereDisk`/`sphereDiskBoundarySet`

`PinPlusKTSphereProdCohomology`'s reduced-atoms wiring consumes, for the abstract carrier `b.W`:
`Subsingleton (Homology (TopCat.of b.W) 1)` and
`Subsingleton (RelativeHomology (((𝓡 4).prod (𝓡∂ 1)).boundary b.W) 4)`. This module discharges
BOTH atoms on the CONCRETE `b.W := SphereDisk = S²×D³` (`SphereProductBounding`), where the abstract
statements become genuine homotopy-type facts:

* **Root 1** — `Subsingleton (Homology (TopCat.of SphereDisk) 1)`: `H₁(S²×D³;ℤ/2) = 0`. Route:
  `D³` is convex hence contracts radially to its centre, so the projection
  `S²×D³ → S²` is a homotopy equivalence (`SingularProdContractible`, ported here from the
  integral `SingularProdContractibleInt` mirror), transporting the already-banked
  `H₁(S²;ℤ/2) = 0` (`SingularSphereMiddle.sphere_homology_one`).
* **Bonus** (feeds Root 2) — `Subsingleton (Homology (TopCat.of SphereDisk) 4)`: same collapse,
  transporting `H₄(S²;ℤ/2) = 0` (`SingularSphereHighDegree.sphere_homology_high`, degree `4 > 2`).
* **Root 2** — `Subsingleton (RelativeHomology sphereDiskBoundarySet 4)`: `H₄(S²×D³,S²×S²;ℤ/2)=0`.
  Route: the pair long exact sequence (`SingularPairLES`) squeezes
  `H₄(W) → H₄(W,∂W) → H₃(∂W)`: the generic squeeze lemma
  `subsingleton_relativeHomology_of_squeeze` (§5, exactness-only, no sphere content) reduces this to
  `Subsingleton (Homology W 4)` (the Bonus above — DiSCHARGED) and
  `Subsingleton (Homology (sub sphereDiskBoundarySet) 3)`, i.e. `H₃(S²×S²;ℤ/2) = 0`.

  **This last fact is NOT yet available.** `∂W ≃ₜ SphereProd = S²×S²` (`range_sphereDiskIncl` +
  injectivity), so the missing input is a mod-2 computation of `H₃(S²×S²)`. The project's ONLY
  in-tree `S²×S²` product-homology computation is `SphereProdHOneInt`/`SphereProdHTwoInt`/
  `SphereProdHFourInt` — all **ℤ-coefficient** (a genuinely different computation: no Universal
  Coefficient bridge ℤ↔ℤ/2 exists in-tree, and `H₃(S²×S²;ℤ)=0` does not imply `H₃(S²×S²;ℤ/2)=0`
  without one). Porting the mod-2 analogue is NOT a small brick: the ℤ-coefficient computation's
  polar-cover Mayer–Vietoris argument bottoms out in `SphereProdPuncturedPlaneInt` (743 lines) via
  `SingularStarConvexSlit`/`SingularClopenSplitInt`/`SphereDoublyPuncturedPlane` — reproducing it in
  ℤ/2 is a project-scale sub-effort (~1000+ new lines across several modules), not a same-turn
  brick, and the project's own docstrings flag "No Künneth machinery" as the reason this cover
  argument (rather than a one-line Künneth formula) is needed at all. Root 2 is therefore reduced
  to, but NOT closed at, exactly this one fact — reported to the lead rather than rushed.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
new axiom.
-/
import Mathlib
import SKEFTHawking.SphereProductBounding
import SKEFTHawking.SingularProdContractible
import SKEFTHawking.SingularSphereMiddle
import SKEFTHawking.SingularSphereHighDegree
import SKEFTHawking.SingularPairLES

open SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularHomotopyInvariance (slice)
open SKEFTHawking.SingularProdContractible
open SKEFTHawking.SingularSphereMiddle (sphere_homology_one)
open SKEFTHawking.SingularSphereHighDegree (sphere_homology_high)
open SKEFTHawking.SingularPairLES

namespace SKEFTHawking.PinPlusKTSphereProdHomologyRoots

/-! ## §1. The radial contraction of `ThreeDisk` to its centre -/

/-- The centre of `D³` — the fixed point the radial contraction retracts onto. -/
def diskCenter : ThreeDisk := ⟨0, by simp⟩

/-- **The radial contraction of `D³`**: `(y, t) ↦ (1 - t) • y`, staying inside the closed unit ball
(a convex combination of `y` and the centre `0`, both in `closedBall 0 1`). At `t = 0` this is the
identity; at `t = 1` it collapses to the centre. -/
noncomputable def diskContract : C(↑(TopCat.of ThreeDisk) × unitInterval, ↑(TopCat.of ThreeDisk)) where
  toFun p := ⟨(1 - (p.2 : ℝ)) • (p.1 : EuclideanSpace ℝ (Fin 3)), by
    have hy : ‖(p.1 : EuclideanSpace ℝ (Fin 3))‖ ≤ 1 := by
      have := p.1.2
      rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at this
    have ht0 : 0 ≤ (1 - (p.2 : ℝ)) := by linarith [p.2.2.2]
    have ht1 : (1 - (p.2 : ℝ)) ≤ 1 := by linarith [p.2.2.1]
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    calc (1 - (p.2 : ℝ)) * ‖(p.1 : EuclideanSpace ℝ (Fin 3))‖
        ≤ 1 * 1 := by
          apply mul_le_mul ht1 hy (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1⟩
  continuous_toFun := by fun_prop

theorem slice_diskContract_zero : slice diskContract 0 = ContinuousMap.id ↑(TopCat.of ThreeDisk) := by
  refine ContinuousMap.ext fun y => ?_
  show (⟨(1 - (0 : unitInterval) : ℝ) • (y : EuclideanSpace ℝ (Fin 3)), _⟩ : ThreeDisk) = y
  exact Subtype.ext (by simp)

theorem slice_diskContract_one :
    slice diskContract 1 = ContinuousMap.const ↑(TopCat.of ThreeDisk) diskCenter := by
  refine ContinuousMap.ext fun y => ?_
  show (⟨(1 - (1 : unitInterval) : ℝ) • (y : EuclideanSpace ℝ (Fin 3)), _⟩ : ThreeDisk) = diskCenter
  exact Subtype.ext (by simp [diskCenter])

/-! ## §2. The contractible-factor collapse specialized: `SphereDisk ≃ TwoSphere` in homology -/

/-- **`SphereDisk` collapses onto `TwoSphere` in mod-2 homology** (every positive degree): `D³`
contracts radially, so the projection `S²×D³ → S²` is a homotopy equivalence. -/
noncomputable def sphereDiskCollapseEquiv (n : ℕ) :
    Homology (TopCat.of SphereDisk) (n + 1) ≃ₗ[ZMod 2] Homology (TopCat.of TwoSphere) (n + 1) :=
  prodContractibleEquiv (TopCat.of TwoSphere) (TopCat.of ThreeDisk) diskCenter diskContract
    slice_diskContract_zero slice_diskContract_one n

/-! ## §3. Root 1 — `H₁(S²×D³;ℤ/2) = 0` -/

/-- **Root 1.** `H₁(S²×D³;ℤ/2) = 0`: transported from `H₁(S²;ℤ/2) = 0`
(`sphere_homology_one`, at the concrete ambient dimension `n = 2`) across the `D³`-collapse. -/
theorem sphereDisk_homology_one_eq_zero (x : Homology (TopCat.of SphereDisk) 1) : x = 0 := by
  have h0 : sphereDiskCollapseEquiv 0 x = 0 := sphere_homology_one 2 (by norm_num) _
  have := congrArg (sphereDiskCollapseEquiv 0).symm h0
  simpa using this

instance : Subsingleton (Homology (TopCat.of SphereDisk) 1) :=
  ⟨fun a b => (sphereDisk_homology_one_eq_zero a).trans (sphereDisk_homology_one_eq_zero b).symm⟩

/-! ## §4. Bonus (feeds Root 2) — `H₄(S²×D³;ℤ/2) = 0` -/

/-- **Bonus.** `H₄(S²×D³;ℤ/2) = 0`: transported from `H₄(S²;ℤ/2) = 0`
(`sphere_homology_high`, `2 < 4`) across the same `D³`-collapse. Feeds the pair-LES squeeze (§5) for
Root 2. -/
theorem sphereDisk_homology_four_eq_zero (x : Homology (TopCat.of SphereDisk) 4) : x = 0 := by
  have h0 : sphereDiskCollapseEquiv 3 x = 0 := sphere_homology_high 2 4 (by norm_num) _
  have := congrArg (sphereDiskCollapseEquiv 3).symm h0
  simpa using this

instance : Subsingleton (Homology (TopCat.of SphereDisk) 4) :=
  ⟨fun a b => (sphereDisk_homology_four_eq_zero a).trans (sphereDisk_homology_four_eq_zero b).symm⟩

/-! ## §5. The generic pair-LES squeeze (partial progress toward Root 2) -/

/-- **The pair-LES squeeze**: if `Hₙ₊₁(X) = 0` and `Hₙ(S) = 0`, then `Hₙ₊₁(X,S) = 0`. Pure exactness
(`SingularPairLES.exact_homProj_connecting`, `Function.Exact (homProj S (n+1)) (connecting S n)`):
`Hₙ₊₁(X) = 0` forces `homProj` to be the zero map, so exactness makes `connecting` injective;
`Hₙ(S) = 0` then forces `connecting` to be the zero map, and an injective zero map has a trivial
domain. No sphere content — reusable for ANY pair `(X, S)`. -/
theorem subsingleton_relativeHomology_of_squeeze {X : TopCat} (S : Set X) (n : ℕ)
    [Subsingleton (Homology X (n + 1))] [Subsingleton (Homology (sub S) n)] :
    Subsingleton (RelativeHomology S (n + 1)) := by
  refine ⟨fun a b => ?_⟩
  have key : ∀ y : RelativeHomology S (n + 1), y = 0 := by
    intro y
    have h1 : connecting S n y = 0 := Subsingleton.elim _ _
    obtain ⟨x, hx⟩ := (exact_homProj_connecting S n y).mp h1
    rw [← hx, Subsingleton.elim x 0, map_zero]
  rw [key a, key b]

end SKEFTHawking.PinPlusKTSphereProdHomologyRoots
