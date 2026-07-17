/-
# Phase 5q.H close-out (#211) — `hincl_sphereDisk`, the Mayer–Vietoris completion

The SOLE remaining gap in the `S²×D³` relative-fundamental-class assembly: at every INTERIOR point
`x = (p₀, y₀)` of `SphereDisk = S²×D³`, the boundary inclusion `∂W = S²×S² ↪ {x}ᶜ = S²×D³ ∖ {x}` is
INJECTIVE on `H₄(·; ℤ/2)`.

Route (the docstring Mayer–Vietoris sketch of `PinPlusKTSphereProdRelFundWuRoots`, now discharged):
factor `∂W ⊆ A₀ ⊆ {x}ᶜ` with `A₀ = diskFactorSet y₀ = {p | p.2 ≠ y₀}`.
* **`∂W ↪ A₀`** is `H₄`-injective — BANKED
  (`PinPlusKTSphereProdRelFundWuRoots.injective_boundary_to_diskFactorSet`).
* **`A₀ ↪ {x}ᶜ`** is `H₄`-injective — the new work here, via Mayer–Vietoris over the ambient
  `sub {x}ᶜ` with the cover `A₀ ∪ B₀ = {x}ᶜ`, `B₀ = {p | p.1 ≠ p₀}`. Exactness at the middle
  (`SingularMayerVietorisLES.mv_exact_middle`) reduces injectivity of `H₄(A₀) → H₄({x}ᶜ)` to
  `H₄(A₀ ∩ B₀) = 0`, `A₀ ∩ B₀ = (S²∖p₀) × (D³∖y₀)`:
  - **`H₄(D³∖y₀) = 0`** (§1): a ray-exit deformation retraction of `D³∖y₀` onto its boundary
    `S² = ∂D³` (`PinPlusTraceDiskCorePair.rayExit` reused at `E³`), so `H₄(D³∖y₀) ≅ H₄(S²) = 0`.
  - **`H₄(A₀ ∩ B₀) = 0`** (§2): `sub (A₀∩B₀) ≃ₜ (D³∖y₀) × ℝ²` (rectangle homeo + the stereographic
    `S²∖p₀ ≃ₜ ℝ²`); the contractible `ℝ²` factor collapses (`prodContractibleHomologyEquiv`) to
    `H₄(D³∖y₀) = 0`.
  - **MV assembly** (§3): transport `A₀`, `B₀` into `Set ↥({x}ᶜ)` via `restr`/`flatSubHomeo`, fire
    `mv_exact_middle`, and match the composite against the literal `subIncl (∂W ⊆ {x}ᶜ)`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusKTSphereProdRelFundWuRoots
import SKEFTHawking.PinPlusKTSphereProdReassoc
import SKEFTHawking.PinPlusTraceDiskCorePair
import SKEFTHawking.SingularMayerVietorisLES
import SKEFTHawking.SingularFunctoriality
import SKEFTHawking.SingularSphereAcyclic
import SKEFTHawking.SingularSphereHighDegree
import SKEFTHawking.SingularEuclideanAcyclic
import SKEFTHawking.SingularHomotopyInvariance
import SKEFTHawking.SingularLocalHomology
import SKEFTHawking.SingularProdContractibleInt
import SKEFTHawking.PoincareLefschetzRelFundClassGeom
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderNumerics
import SKEFTHawking.PinPlusCharPairRealizationTied

open scoped Manifold
open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularFunctoriality (Homology.map)
open SKEFTHawking.SingularHomotopyInvariance (slice)
open SKEFTHawking.SingularSphereHighDegree (sphere_homology_high)
open SKEFTHawking.SingularMayerVietorisLES (subIncl)
open SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.PinPlusKTSphereProdRelFundWuRoots

attribute [local instance] SKEFTHawking.SpinSigmaRoute.chartW6
  SKEFTHawking.SpinSigmaRoute.sphereDisk_t2Space

namespace SKEFTHawking.PinPlusKTSphereProdHincl

noncomputable section

/-! ## §0. Ray-exit scalar positivity (over a general real inner-product space). -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The ray-exit scalar is strictly positive** for `‖x‖ < 1`, `v ≠ x`: the discriminant
`Δ = B² − 4AC` strictly exceeds `B²` (since `A > 0`, `C < 0`), so `√Δ > |B| ≥ B`, giving
`rayT = (−B + √Δ)/(2A) > 0`. Powers the "stays off `y₀`" leg of the disk deformation retraction. -/
theorem zero_lt_rayT (x v : E) (hx : ‖x‖ < 1) (hv : v ≠ x) :
    0 < PinPlusTraceDiskCorePair.rayT x v := by
  have hApos : 0 < ‖v - x‖ ^ 2 := pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hv)) 2
  have hCneg : ‖x‖ ^ 2 - 1 < 0 := by nlinarith [norm_nonneg x]
  have hΔgt : (2 * inner ℝ x (v - x)) ^ 2
      < (2 * inner ℝ x (v - x)) ^ 2 - 4 * ‖v - x‖ ^ 2 * (‖x‖ ^ 2 - 1) := by
    nlinarith [mul_pos hApos (neg_pos.mpr hCneg)]
  have hsqrt_gt : (2 * inner ℝ x (v - x))
      < Real.sqrt ((2 * inner ℝ x (v - x)) ^ 2 - 4 * ‖v - x‖ ^ 2 * (‖x‖ ^ 2 - 1)) := by
    have h1 := Real.sqrt_lt_sqrt (sq_nonneg (2 * inner ℝ x (v - x))) hΔgt
    rw [Real.sqrt_sq_eq_abs] at h1
    exact lt_of_le_of_lt (le_abs_self _) h1
  unfold PinPlusTraceDiskCorePair.rayT
  apply div_pos
  · linarith [hsqrt_gt]
  · positivity

/-- **The straight-line homotopy point stays off `y₀`.** `t•b + (1−t)•rayExit(y₀,b)` lies on the ray
`y₀ + c•(b−y₀)` with `c = t + (1−t)·rayT > 0` (for `b ≠ y₀`, `‖y₀‖ < 1`, `t ∈ [0,1]`), hence `≠ y₀`. -/
theorem diskHomotopy_ne (y0 b : E) (hy0 : ‖y0‖ < 1) (hbne : b ≠ y0) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t • b + (1 - t) • PinPlusTraceDiskCorePair.rayExit y0 b ≠ y0 := by
  have hrpos : 0 < PinPlusTraceDiskCorePair.rayT y0 b := zero_lt_rayT y0 b hy0 hbne
  have hre : PinPlusTraceDiskCorePair.rayExit y0 b
      = y0 + PinPlusTraceDiskCorePair.rayT y0 b • (b - y0) := rfl
  have hcpos : 0 < t + (1 - t) * PinPlusTraceDiskCorePair.rayT y0 b := by
    have h1 : 0 ≤ (1 - t) * PinPlusTraceDiskCorePair.rayT y0 b := mul_nonneg (by linarith) hrpos.le
    rcases eq_or_lt_of_le ht0 with h | h
    · subst h; simpa using hrpos
    · linarith
  have hkey : t • b + (1 - t) • (y0 + PinPlusTraceDiskCorePair.rayT y0 b • (b - y0))
      = y0 + (t + (1 - t) * PinPlusTraceDiskCorePair.rayT y0 b) • (b - y0) := by module
  rw [hre, hkey]
  intro hcontra
  have hz : (t + (1 - t) * PinPlusTraceDiskCorePair.rayT y0 b) • (b - y0) = 0 := by
    rwa [add_eq_left] at hcontra
  rcases smul_eq_zero.mp hz with hc0 | hbz
  · exact hcpos.ne' hc0
  · exact hbne (sub_eq_zero.mp hbz)

end

/-! ## §1. `H₄(D³ ∖ {y₀}) = 0` — the ray-exit deformation retraction onto `∂D³ = S²`. -/

noncomputable section

abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The disk-punctured set `D³ ∖ {y₀}` (interior point `y₀`). -/
def diskPuncSet (y0 : ThreeDisk) : Set ThreeDisk := {b : ThreeDisk | b ≠ y0}

/-- The disk-punctured space `D³ ∖ {y₀}` as a `TopCat`. -/
abbrev DiskPunc (y0 : ThreeDisk) : TopCat := sub (X := TopCat.of ThreeDisk) (diskPuncSet y0)

/-- **The ray-exit retraction** `r : D³∖{y₀} → S² = ∂D³`: ray-exit the disk coordinate from `y₀`
to the boundary sphere (`PinPlusTraceDiskCorePair.rayExit` at `E³`). -/
def diskPuncRetract (y0 : ThreeDisk) (hy0 : ‖(y0 : E3)‖ < 1) :
    C(↑(DiskPunc y0), (SingularSphereAcyclic.Sph 2 : Type)) where
  toFun b := ⟨PinPlusTraceDiskCorePair.rayExit (y0 : E3) ((b : ThreeDisk) : E3), by
    rw [mem_sphere_zero_iff_norm]
    exact PinPlusTraceDiskCorePair.rayExit_norm _ _ hy0 (fun h => b.2 (Subtype.ext h))⟩
  continuous_toFun := by
    have hg : Continuous (fun b : ↑(DiskPunc y0) => ((b : ThreeDisk) : E3)) := by fun_prop
    have hgx : ∀ b : ↑(DiskPunc y0), ((b : ThreeDisk) : E3) ≠ (y0 : E3) :=
      fun b h => b.2 (Subtype.ext h)
    exact Continuous.subtype_mk
      (PinPlusTraceDiskCorePair.continuous_rayExit_comp (y0 : E3) _ hg hgx) _

/-- **The boundary inclusion** `i : S² = ∂D³ → D³∖{y₀}` (a sphere point has norm `1 ≠ ‖y₀‖`, so
`≠ y₀`). -/
def sphereInclDiskPunc (y0 : ThreeDisk) (hy0 : ‖(y0 : E3)‖ < 1) :
    C((SingularSphereAcyclic.Sph 2 : Type), ↑(DiskPunc y0)) where
  toFun a := ⟨⟨(a : E3), Metric.sphere_subset_closedBall a.2⟩, by
    intro h
    have h' : (a : E3) = (y0 : E3) := congrArg Subtype.val h
    have h1 : ‖(a : E3)‖ = 1 := mem_sphere_zero_iff_norm.mp a.2
    rw [h'] at h1
    exact absurd h1 (ne_of_lt hy0)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    fun_prop

end

end SKEFTHawking.PinPlusKTSphereProdHincl
