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
open SKEFTHawking.SingularMayerVietorisLES
open SKEFTHawking.SingularExcisionIso (restr)
open SKEFTHawking.PoincareLefschetzRelFundClassGeom (homology_restrSub_eq_zero)
open SKEFTHawking.SingularProdContractibleInt (ProdSp)
open SKEFTHawking.SingularEuclideanAcyclic (Eucl)
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderNumerics (prodContractibleHomologyEquiv)
open SKEFTHawking.PinPlusCharPairRealizationTied (homeoHomologyEquiv)
open SKEFTHawking.SingularSphereAcyclic (puncturedHomeo)
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

/-- **The ray-exit deformation homotopy** `H(b, t) = t•b + (1−t)•rayExit(y₀,b)` on `D³∖{y₀}`
(a straight line inside `D³` off `y₀`), from `i ∘ r` (`t = 0`, full ray-exit) to `id` (`t = 1`). -/
def diskPuncHomotopy (y0 : ThreeDisk) (hy0 : ‖(y0 : E3)‖ < 1) :
    C(↑(DiskPunc y0) × unitInterval, ↑(DiskPunc y0)) where
  toFun p := ⟨⟨(p.2 : ℝ) • ((p.1 : ThreeDisk) : E3)
      + (1 - (p.2 : ℝ)) • PinPlusTraceDiskCorePair.rayExit (y0 : E3) ((p.1 : ThreeDisk) : E3), by
      refine convex_closedBall (0 : E3) 1 (p.1 : ThreeDisk).2 ?_ (unitInterval.nonneg p.2)
        (by linarith [unitInterval.le_one p.2]) (by ring)
      rw [mem_closedBall_zero_iff]
      exact le_of_eq (PinPlusTraceDiskCorePair.rayExit_norm _ _ hy0
        (fun h => (p.1).2 (Subtype.ext h)))⟩, by
      intro h
      exact diskHomotopy_ne (y0 : E3) ((p.1 : ThreeDisk) : E3) hy0
        (fun h' => (p.1).2 (Subtype.ext h')) (unitInterval.nonneg p.2)
        (unitInterval.le_one p.2) (congrArg Subtype.val h)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    have hb : Continuous (fun p : ↑(DiskPunc y0) × unitInterval => ((p.1 : ThreeDisk) : E3)) := by
      fun_prop
    have hbx : ∀ p : ↑(DiskPunc y0) × unitInterval, ((p.1 : ThreeDisk) : E3) ≠ (y0 : E3) :=
      fun p h => (p.1).2 (Subtype.ext h)
    have ht : Continuous (fun p : ↑(DiskPunc y0) × unitInterval => (p.2 : ℝ)) := by fun_prop
    exact (ht.smul hb).add ((continuous_const.sub ht).smul
      (PinPlusTraceDiskCorePair.continuous_rayExit_comp (y0 : E3) _ hb hbx))

/-- The retraction is a genuine left inverse of the boundary inclusion: `r ∘ i = id` on `S²`
(boundary points are their own ray-exits, `rayExit_of_norm_one`). -/
theorem diskPuncRetract_comp_incl (y0 : ThreeDisk) (hy0 : ‖(y0 : E3)‖ < 1) :
    (diskPuncRetract y0 hy0).comp (sphereInclDiskPunc y0 hy0)
      = ContinuousMap.id (SingularSphereAcyclic.Sph 2 : Type) := by
  apply ContinuousMap.ext
  intro a
  apply Subtype.ext
  show PinPlusTraceDiskCorePair.rayExit (y0 : E3) (a : E3) = (a : E3)
  have h1 : ‖(a : E3)‖ = 1 := mem_sphere_zero_iff_norm.mp a.2
  refine PinPlusTraceDiskCorePair.rayExit_of_norm_one _ _ hy0 (fun h => ?_) h1
  rw [h] at h1
  exact absurd h1 (ne_of_lt hy0)

/-- **`slice (diskPuncHomotopy) 0 = i ∘ r`** — the `t = 0` slice is the full ray-exit. -/
theorem slice_diskPuncHomotopy_zero (y0 : ThreeDisk) (hy0 : ‖(y0 : E3)‖ < 1) :
    slice (diskPuncHomotopy y0 hy0) 0
      = (sphereInclDiskPunc y0 hy0).comp (diskPuncRetract y0 hy0) := by
  apply ContinuousMap.ext
  intro b
  apply Subtype.ext
  apply Subtype.ext
  show (0 : ℝ) • ((b : ThreeDisk) : E3)
      + (1 - (0 : ℝ)) • PinPlusTraceDiskCorePair.rayExit (y0 : E3) ((b : ThreeDisk) : E3)
    = PinPlusTraceDiskCorePair.rayExit (y0 : E3) ((b : ThreeDisk) : E3)
  simp

/-- **`slice (diskPuncHomotopy) 1 = id`** — the `t = 1` slice is the identity. -/
theorem slice_diskPuncHomotopy_one (y0 : ThreeDisk) (hy0 : ‖(y0 : E3)‖ < 1) :
    slice (diskPuncHomotopy y0 hy0) 1 = ContinuousMap.id ↑(DiskPunc y0) := by
  apply ContinuousMap.ext
  intro b
  apply Subtype.ext
  apply Subtype.ext
  show (1 : ℝ) • ((b : ThreeDisk) : E3) + (1 - (1 : ℝ)) • _ = ((b : ThreeDisk) : E3)
  simp

/-- **`H₄(D³∖{y₀}; ℤ/2) = 0`** — the ray-exit retraction is a homotopy equivalence
`D³∖{y₀} ≃ S² = ∂D³`, so `H₄` transports to `H₄(S²) = 0` (`sphere_homology_high`, `4 > 2`). -/
theorem diskPunc_homology_four_eq_zero (y0 : ThreeDisk) (hy0 : ‖(y0 : E3)‖ < 1)
    (z : Homology (DiskPunc y0) 4) : z = 0 := by
  have hbij : Function.Bijective (Homology.map (diskPuncRetract y0 hy0) 4) :=
    SingularHomotopyInvariance.Homology.map_bijective_of_homotopyEquiv
      (diskPuncRetract y0 hy0) (sphereInclDiskPunc y0 hy0) (diskPuncHomotopy y0 hy0)
      (slice_diskPuncHomotopy_zero y0 hy0) (slice_diskPuncHomotopy_one y0 hy0)
      ⟨fun p => p.1, continuous_fst⟩
      (by
        apply ContinuousMap.ext; intro a
        exact congrFun (congrArg (fun f => f.toFun) (diskPuncRetract_comp_incl y0 hy0).symm) a)
      (ContinuousMap.ext fun _ => rfl) 3
  exact SingularLocalHomology.homology_trivial_of_bijective (diskPuncRetract y0 hy0) hbij
    (fun w => sphere_homology_high 2 4 (by norm_num) w) z

/-! ## §2. `H₄(A₀ ∩ B₀) = 0`, `A₀ ∩ B₀ = (S²∖p₀) × (D³∖y₀)`. -/

/-- **The sphere-factor-punctured set** `B₀ = {p ∈ S²×D³ | p.1 ≠ p₀}`. -/
def sphereFactorSet (p₀ : TwoSphere) : Set SphereDisk := {p : SphereDisk | p.1 ≠ p₀}

/-- The intersection `A₀ ∩ B₀` is the rectangle `(S²∖p₀) ×ˢ (D³∖y₀)`. -/
theorem inter_factor_eq (p₀ : TwoSphere) (y0 : ThreeDisk) :
    diskFactorSet y0 ∩ sphereFactorSet p₀ = (({p₀}ᶜ : Set TwoSphere) ×ˢ diskPuncSet y0) := by
  ext p
  simp only [diskFactorSet, sphereFactorSet, diskPuncSet, Set.mem_inter_iff, Set.mem_setOf_eq,
    Set.mem_prod, Set.mem_compl_iff, Set.mem_singleton_iff]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- **`sub (A₀ ∩ B₀) ≃ₜ (D³∖y₀) × ℝ²`** — the rectangle homeomorphism (`Homeomorph.Set.prod`) plus
the stereographic `S²∖p₀ ≃ₜ ℝ²` (`puncturedHomeo`), reordered so the contractible `ℝ²` is second. -/
def interHomeo (p₀ : TwoSphere) (y0 : ThreeDisk) :
    (sub (X := TopCat.of SphereDisk) (diskFactorSet y0 ∩ sphereFactorSet p₀) : Type)
      ≃ₜ (ProdSp (DiskPunc y0) (Eucl 2) : Type) :=
  (Homeomorph.setCongr (inter_factor_eq p₀ y0)).trans
    ((Homeomorph.Set.prod _ _).trans
      ((Homeomorph.prodCongr (puncturedHomeo 2 p₀) (Homeomorph.refl _)).trans
        (Homeomorph.prodComm _ _)))

/-- **`H₄(A₀ ∩ B₀; ℤ/2) = 0`** — transport across `interHomeo`, collapse the contractible `ℝ²`
factor (`prodContractibleHomologyEquiv`, Euclidean straight-line contraction), and land on
`H₄(D³∖y₀) = 0` (§1). -/
theorem interFactor_homology_four_eq_zero (p₀ : TwoSphere) (y0 : ThreeDisk)
    (hy0 : ‖(y0 : E3)‖ < 1)
    (z : Homology (sub (X := TopCat.of SphereDisk) (diskFactorSet y0 ∩ sphereFactorSet p₀)) 4) :
    z = 0 := by
  have e := (homeoHomologyEquiv (interHomeo p₀ y0) 4).trans
    (prodContractibleHomologyEquiv (DiskPunc y0) (Eucl 2) (0 : Eucl 2)
      (SingularEuclideanAcyclic.contraction 2) (SingularEuclideanAcyclic.slice_contraction_zero 2)
      (SingularEuclideanAcyclic.slice_contraction_one 2) 3)
  apply e.injective
  rw [map_zero]
  exact diskPunc_homology_four_eq_zero y0 hy0 (e z)

/-! ## §3. The disk-factor inclusion `A₀ ↪ {x}ᶜ` is `H₄`-injective — Mayer–Vietoris. -/

/-- **The subtype-of-subtype inclusion** `sub s → sub (restr s t)` for `s ⊆ t` (`restr s t = ↥s`
inside `↥t`): the flat picture of `s` becomes the two-layer picture inside `t`. -/
def flatIncl {X : TopCat} {s t : Set ↑X} (h : s ⊆ t) :
    C(↑(sub s), ↑(sub (restr s t))) where
  toFun a := ⟨⟨(a : ↑X), h a.2⟩, a.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk; apply Continuous.subtype_mk; fun_prop

/-- Its inverse `sub (restr s t) → sub s`. -/
def flatInclInv {X : TopCat} {s t : Set ↑X} (_h : s ⊆ t) :
    C(↑(sub (restr s t)), ↑(sub s)) where
  toFun q := ⟨((q : ↑(sub t)) : ↑X), q.2⟩
  continuous_toFun := by apply Continuous.subtype_mk; fun_prop

/-- **`flatIncl` is a homology isomorphism** (a two-sided continuous inverse). -/
theorem map_flatIncl_bijective {X : TopCat} {s t : Set ↑X} (h : s ⊆ t) (n : ℕ) :
    Function.Bijective (Homology.map (flatIncl h) n) :=
  SingularHomotopyInvariance.Homology.map_bijective_of_comp_id_all (flatIncl h) (flatInclInv h)
    (ContinuousMap.ext fun _ => rfl) (ContinuousMap.ext fun _ => Subtype.ext (Subtype.ext rfl)) n

/-- **`subIncl h` factors as `ambIncl (restr s t) ∘ flatIncl h`** (both send a point of `s` to itself
inside `t`). -/
theorem subIncl_eq_ambIncl_comp_flatIncl {X : TopCat} {s t : Set ↑X} (h : s ⊆ t) :
    subIncl h = (ambIncl (restr s t)).comp (flatIncl h) :=
  ContinuousMap.ext fun _ => rfl

/-- `A₀ = {p.2 ≠ y₀}` is open in `S²×D³`. -/
theorem isOpen_diskFactorSet (y0 : ThreeDisk) : IsOpen (diskFactorSet y0) :=
  isOpen_compl_singleton.preimage continuous_snd

/-- `B₀ = {p.1 ≠ p₀}` is open in `S²×D³`. -/
theorem isOpen_sphereFactorSet (p₀ : TwoSphere) : IsOpen (sphereFactorSet p₀) :=
  isOpen_compl_singleton.preimage continuous_fst

/-- **The disk-factor inclusion `A₀ ↪ {x}ᶜ` is `H₄`-injective** at an interior point `x`.
Mayer–Vietoris over the ambient `sub {x}ᶜ` with the open cover `A₀ ∪ B₀ = {x}ᶜ`,
`B₀ = {p.1 ≠ x.1}`: exactness at the middle (`mv_exact_middle`) plus `H₄(A₀∩B₀) = 0` (§2) force the
kernel of `H₄(A₀) → H₄({x}ᶜ)` to vanish; the `flatIncl` factorization moves it to `subIncl`. -/
theorem injective_diskFactorSet_to_compl (x : ↑(TopCat.of SphereDisk))
    (hy0 : ‖((x.2 : ThreeDisk) : E3)‖ < 1)
    (h2 : diskFactorSet x.2 ⊆ ({x}ᶜ : Set SphereDisk)) :
    Function.Injective (Homology.map (subIncl (X := TopCat.of SphereDisk) h2) 4) := by
  set A := restr (X := TopCat.of SphereDisk) (diskFactorSet x.2) {x}ᶜ with hA
  set B := restr (X := TopCat.of SphereDisk) (sphereFactorSet x.1) {x}ᶜ with hB
  have hAopen : IsOpen A := (isOpen_diskFactorSet x.2).preimage continuous_subtype_val
  have hBopen : IsOpen B := (isOpen_sphereFactorSet x.1).preimage continuous_subtype_val
  -- the open cover `A ∪ B = {x}ᶜ`
  have hcov : (⋃ U ∈ ({A, B} : Set (Set ↑(sub (X := TopCat.of SphereDisk) {x}ᶜ))), interior U)
      = Set.univ := by
    rw [Set.biUnion_pair, hAopen.interior_eq, hBopen.interior_eq, Set.eq_univ_iff_forall]
    intro q
    rw [Set.mem_union]
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hqA, hqB⟩ := hcon
    rw [hA, Set.mem_preimage] at hqA
    rw [hB, Set.mem_preimage] at hqB
    simp only [diskFactorSet, sphereFactorSet, Set.mem_setOf_eq, not_not] at hqA hqB
    exact q.2 (Prod.ext hqB hqA)
  -- `H₄(sub (A ∩ B)) = 0`
  have hInterZero : ∀ w : Homology (sub (A ∩ B)) 4, w = 0 := by
    have hz := homology_restrSub_eq_zero (Set.inter_subset_left.trans h2) 4
      (interFactor_homology_four_eq_zero x.1 x.2 hy0)
    exact fun w => hz w
  -- kernel-triviality of `H₄(A₀) → H₄({x}ᶜ)` (the ambient inclusion)
  have hker : ∀ u, Homology.map (ambIncl A) 4 u = 0 → u = 0 := by
    intro u hu
    have hsum : mvHomSum A B 4 (u, 0) = 0 := by
      rw [mvHomSum_apply]; simp [hu]
    obtain ⟨w, hw⟩ := (mv_exact_middle A B 3 hcov (u, 0)).mp hsum
    rw [hInterZero w, map_zero] at hw
    simpa using congrArg Prod.fst hw.symm
  have hInjAmb : Function.Injective ⇑(Homology.map (ambIncl A) 4) := by
    intro a b hab
    exact sub_eq_zero.mp (hker _ (by rw [map_sub, hab, sub_self]))
  -- transport back to `subIncl` via the `flatIncl` factorization
  rw [subIncl_eq_ambIncl_comp_flatIncl h2, SingularFunctoriality.Homology.map_comp,
    LinearMap.coe_comp]
  exact hInjAmb.comp (map_flatIncl_bijective h2 4).injective

/-! ## §4. `hincl_sphereDisk` — the boundary inclusion is `H₄`-injective at every interior point. -/

/-- The disk-factor set is inside `{x}ᶜ`: `p.2 ≠ y₀ ⟹ p ≠ (·, y₀)`. -/
theorem diskFactorSet_subset_compl (x : ↑(TopCat.of SphereDisk)) :
    diskFactorSet x.2 ⊆ ({x}ᶜ : Set SphereDisk) := by
  intro p hp hpx
  rw [Set.mem_singleton_iff] at hpx
  exact hp (by rw [hpx])

/-- **`hincl` over `sphereDiskBoundarySet`.** Factor `∂W ↪ A₀ ↪ {x}ᶜ` (`A₀ = diskFactorSet x.2`):
`∂W ↪ A₀` is the banked `injective_boundary_to_diskFactorSet`; `A₀ ↪ {x}ᶜ` is the §3 MV result. -/
theorem hincl_aux (x : ↑(TopCat.of SphereDisk)) (hy0 : ‖((x.2 : ThreeDisk) : E3)‖ < 1)
    (hsub : sphereDiskBoundarySet ⊆ ({x}ᶜ : Set SphereDisk)) :
    Function.Injective (Homology.map (subIncl (X := TopCat.of SphereDisk) hsub) 4) := by
  have h1 : sphereDiskBoundarySet ⊆ diskFactorSet x.2 :=
    sphereDiskBoundarySet_subset_diskFactorSet hy0
  have h2 : diskFactorSet x.2 ⊆ ({x}ᶜ : Set SphereDisk) := diskFactorSet_subset_compl x
  have hcomp : subIncl hsub = (subIncl (X := TopCat.of SphereDisk) h2).comp
      (subIncl (X := TopCat.of SphereDisk) h1) := ContinuousMap.ext fun _ => rfl
  rw [hcomp, SingularFunctoriality.Homology.map_comp, LinearMap.coe_comp]
  exact (injective_diskFactorSet_to_compl x hy0 h2).comp
    (injective_boundary_to_diskFactorSet x.2 hy0)

/-- **`hincl_sphereDisk`** — at every INTERIOR point `x` of `SphereDisk = S²×D³`, the boundary
inclusion `∂W = S²×S² ↪ {x}ᶜ = S²×D³ ∖ {x}` is `H₄(·; ℤ/2)`-injective. The Mayer–Vietoris completion
of the `S²×D³` relative-fundamental-class assembly. -/
theorem hincl_sphereDisk (x : ↑(TopCat.of SphereDisk))
    (hx : x ∉ ((𝓡 4).prod (𝓡∂ 1)).boundary SphereDisk) :
    Function.Injective (Homology.map (subIncl (X := TopCat.of SphereDisk)
      (Set.subset_compl_singleton_iff.mpr hx)) 4) := by
  have hy0 : ‖((x.2 : ThreeDisk) : E3)‖ < 1 := by
    have hle : ‖((x.2 : ThreeDisk) : E3)‖ ≤ 1 := mem_closedBall_zero_iff.mp x.2.2
    refine lt_of_le_of_ne hle (fun h => hx ?_)
    rw [sphereDisk_boundary_eq]
    exact mem_sphere_zero_iff_norm.mpr h
  revert hx
  rw [sphereDisk_boundary_eq]
  intro hx
  exact hincl_aux x hy0 (Set.subset_compl_singleton_iff.mpr hx)

end

end SKEFTHawking.PinPlusKTSphereProdHincl
