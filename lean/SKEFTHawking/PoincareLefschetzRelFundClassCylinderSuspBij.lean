/-
# Phase 5q.H Track 2 — `hbij` DISCHARGED: `cylCrossH` is bijective (the pair-suspension iso)

`…CylinderSuspDual.ofCapCross` consumes two pair-suspension iso witnesses `hbij23`/`hbij14`
(`cylCrossH` bijective at `p = 1, 2`) plus the two cap-cross projection values. This module
DISCHARGES the two `hbij` inputs entirely, so the residual of the pinned-`β` intertwining data
collapses to the projection values alone.

## The route — injectivity via the connecting map + boundary split, then finrank for surjectivity

`cylCrossH p : Hₚ₊₁(M) → Hₚ₊₂(W,∂W)` is `[z] ↦ [crossChain z] = [prismOp graphHom z]`, the honest
`× [I,∂I]`. Over the field `ℤ/2`:

* **Injectivity (`§2`).** The pair connecting map `δ = connecting ∂W` sends `crossH [z]` to
  `[∂(crossChain z)] = [end₀ z + end₁ z]` (the two endpoint slices, `chainBoundary_crossChain`),
  which under the clopen boundary split `∂W = (M×{⊥}) ⊔ (M×{⊤})` is
  `homIncl⊥ [z|₀] + homIncl⊤ [z|₁] = splitHn (·,·)`. If `crossH [z] = 0` then this is `0`, so by
  `splitHn_injective` the bottom class `[z|₀] = 0`; but the slice projection `ptPieceToM ⊥` sends
  `[z|₀]` back to `[z]` (the slice-then-project is `id_M`), forcing `[z] = 0`. This is the
  `∂W`-boundary mirror of the `αU ≠ 0` clopen-split detection (`…CrossLocalAlphaU`), reusing the
  same `connecting_relCycleToHom` / `boundaryExtract` opacity-clean value rules.
* **Surjectivity (`§3`).** The pair-suspension dimension count `dim Hₚ₊₂(W,∂W) = dim Hₚ₊₁(M)`
  (`…CylinderSuspension.cylinder_relHom_finrank`) makes source and target equal-finrank finite-dim
  `ℤ/2`-spaces, so an injective linear map is automatically surjective (rank–nullity).

## The payoff (`§4`)

`cylCrossH_bijective` (both consumed degrees), then `CylinderSuspIntertwineData.ofCapCrossProj` —
the `ofCapCross` successor that consumes ONLY the two cap-cross projection values (the `hbij` fields
discharged). The Track-2 residual after this module is the two projection values + the `hwu`
Wu-formula + `M`-intrinsic inputs.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
new `axiom`.
-/
import Mathlib
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspDual
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspension
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalAlphaU

open scoped Manifold
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularRelativeFunctoriality
open SKEFTHawking.SingularHomotopyInvariance (slice endMap_eq_mapChain)
open SKEFTHawking.SingularPrism
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.SingularPairLES
open SKEFTHawking.SingularCohomologyPairRestrict
open SKEFTHawking.SingularDisjointUnionHn
open SKEFTHawking.SingularFundamentalClass
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderNumerics
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCross
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalAlphaU
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspension
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderIntertwine
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspDual

namespace SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspBij

noncomputable section

/-! ## §1. A generic finrank helper: injective + equal finrank ⟹ bijective (over a field) -/

/-- **Injective + equal finite finrank ⟹ bijective** (over a field). A ℤ/2-linear map between two
finite-dimensional spaces of equal dimension that is injective is automatically surjective (hence
bijective) by rank–nullity. -/
theorem bijective_of_injective_of_finrank_eq {V W : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) V]
    [FiniteDimensional (ZMod 2) W] (f : V →ₗ[ZMod 2] W) (hinj : Function.Injective f)
    (hdim : Module.finrank (ZMod 2) V = Module.finrank (ZMod 2) W) : Function.Bijective f := by
  refine ⟨hinj, ?_⟩
  rw [← LinearMap.range_eq_top]
  have hker : LinearMap.ker f = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  have hrank : Module.finrank (ZMod 2) (LinearMap.range f) = Module.finrank (ZMod 2) W := by
    have hF := LinearMap.finrank_range_add_finrank_ker f
    rw [hker, finrank_bot, add_zero] at hF
    rw [hF, hdim]
  exact Submodule.eq_top_of_finrank_eq hrank

/-! ## §2. Injectivity of `cylCrossH` via the connecting map + clopen boundary split -/

section Injective

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]

/-- **The pinned cylinder boundary** `∂W = M × {⊥,⊤}` (a `def`, kept sealed so the `cyl`↔`cylW`
defeq checks don't repeatedly unfold `ModelWithCorners.boundary` — the `puncU`-style pinning the
`…CrossLocalAlphaU` arc relied on). -/
def bdW (M : Type) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M] :
    Set ↑(TopCat.of (cylW M)) := (cylModel 2).boundary (cylW M)

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- The top slice lands in the pinned boundary. -/
theorem slice1_bdW :
    Set.MapsTo (slice (graphHom (TopCat.of M)) 1) (Set.univ : Set ↑(TopCat.of M)) (bdW M) :=
  slice_one_mapsTo (M := M) (m' := 2)

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- The bottom slice lands in the pinned boundary. -/
theorem slice0_bdW :
    Set.MapsTo (slice (graphHom (TopCat.of M)) 0) (Set.univ : Set ↑(TopCat.of M)) (bdW M) :=
  slice_zero_mapsTo (M := M) (m' := 2)

/-- **The cylinder homology cross in the pinned boundary spelling** `Hₚ₊₁(M) → Hₚ₊₂(W, ∂W)`, defeq to
`cylCrossH` — the `crossH` engine at `S := bdW`. -/
def bdCrossH (p : ℕ) :
    Homology (TopCat.of M) (p + 1) →ₗ[ZMod 2] RelativeHomology (bdW M) (p + 1 + 1) :=
  crossH (M := TopCat.of M) (S := bdW M) (slice1_bdW (M := M)) (slice0_bdW (M := M)) p

/-- **The bottom-slice corestriction** `M → ↥(ptPiece ⊥)`, `m ↦ (m, ⊥)`. -/
def botCoreMap : C(↑(TopCat.of M), ↑(sub (ptPiece M ⊥))) := mToPtPiece ⊥ (by simp)

/-- **The top-slice corestriction** `M → ↥((ptPiece ⊥)ᶜ)`, `m ↦ (m, ⊤)` (landing in the complement
clopen half `(ptPiece ⊥)ᶜ = ptPiece ⊤`). -/
def topCoreMap : C(↑(TopCat.of M), ↑(sub ((ptPiece M ⊥)ᶜ))) :=
  ⟨fun m => ⟨mToBdryPt ⊤ (by simp) m,
      (ptPiece_bot_compl (M := M)).ge (mToBdryPt_mem_ptPiece ⊤ (by simp) m)⟩,
    (continuous_mToBdryPt ⊤ (by simp)).subtype_mk _⟩

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- **Composite-slice identity (bottom)** `↥(ptPiece ⊥) ↪ ↥∂W ↪ W` after `botCoreMap` is the absolute
bottom slice `slice 0` — every arrow is `Subtype.val`, so `rfl`. -/
theorem subIncl_botCoreMap_eq_slice0 :
    ((subInclCM (bdW M)).comp
        (subInclCM (ptPiece M ⊥))).comp (botCoreMap (M := M))
      = slice (graphHom (TopCat.of M)) 0 := by
  apply ContinuousMap.ext; intro m; rfl

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- **Composite-slice identity (top)** `↥((ptPiece ⊥)ᶜ) ↪ ↥∂W ↪ W` after `topCoreMap` is the absolute
top slice `slice 1`. -/
theorem subIncl_topCoreMap_eq_slice1 :
    ((subInclCM (bdW M)).comp
        (subInclCM ((ptPiece M ⊥)ᶜ))).comp (topCoreMap (M := M))
      = slice (graphHom (TopCat.of M)) 1 := by
  apply ContinuousMap.ext; intro m; rfl

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- The bottom half-chain re-included all the way to `W` is the absolute bottom-slice push `end₀ z`. -/
theorem chainIncl_chainIncl_botCore (p : ℕ) (z : cycles (TopCat.of M) (p + 1)) :
    chainIncl (bdW M) (p + 1)
        (chainIncl (ptPiece M ⊥) (p + 1)
          (mapChain (botCoreMap (M := M)) (p + 1) (z : SingularChain (TopCat.of M) (p + 1))))
      = mapChain (slice (graphHom (TopCat.of M)) 0) (p + 1)
          (z : SingularChain (TopCat.of M) (p + 1)) := by
  rw [← mapChain_subInclCM (ptPiece M ⊥) (p + 1),
    ← mapChain_subInclCM (bdW M) (p + 1), ← subIncl_botCoreMap_eq_slice0,
    mapChain_comp, mapChain_comp]
  rfl

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- The top half-chain re-included all the way to `W` is the absolute top-slice push `end₁ z`. -/
theorem chainIncl_chainIncl_topCore (p : ℕ) (z : cycles (TopCat.of M) (p + 1)) :
    chainIncl (bdW M) (p + 1)
        (chainIncl ((ptPiece M ⊥)ᶜ) (p + 1)
          (mapChain (topCoreMap (M := M)) (p + 1) (z : SingularChain (TopCat.of M) (p + 1))))
      = mapChain (slice (graphHom (TopCat.of M)) 1) (p + 1)
          (z : SingularChain (TopCat.of M) (p + 1)) := by
  rw [← mapChain_subInclCM ((ptPiece M ⊥)ᶜ) (p + 1),
    ← mapChain_subInclCM (bdW M) (p + 1), ← subIncl_topCoreMap_eq_slice1,
    mapChain_comp, mapChain_comp]
  rfl

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- The prism lift-chain of a cycle lies in the connecting-map lift submodule of `(W, ∂W)`. -/
theorem crossChain_mem_lift (p : ℕ) (z : cycles (TopCat.of M) (p + 1)) :
    crossChain (p + 1) (z : SingularChain (TopCat.of M) (p + 1))
      ∈ relCycleLift (bdW M) (p + 1) :=
  crossChain_mem_relCycleLift (slice1_bdW (M := M)) (slice0_bdW (M := M)) p
    (z : SingularChain (TopCat.of M) (p + 1)) (LinearMap.mem_ker.mp z.2)

/-- **The bottom-half boundary class** `[end₀ z] ∈ H_{p+1}(↥(ptPiece ⊥))`. -/
def botCls (p : ℕ) (z : cycles (TopCat.of M) (p + 1)) : Homology (sub (ptPiece M ⊥)) (p + 1) :=
  Homology.mk (sub (ptPiece M ⊥)) (p + 1)
    ⟨mapChain (botCoreMap (M := M)) (p + 1) (z : SingularChain (TopCat.of M) (p + 1)),
      mapChain_mem_cycles (botCoreMap (M := M)) z.2⟩

/-- **The top-half boundary class** `[end₁ z] ∈ H_{p+1}(↥((ptPiece ⊥)ᶜ))`. -/
def topCls (p : ℕ) (z : cycles (TopCat.of M) (p + 1)) : Homology (sub ((ptPiece M ⊥)ᶜ)) (p + 1) :=
  Homology.mk (sub ((ptPiece M ⊥)ᶜ)) (p + 1)
    ⟨mapChain (topCoreMap (M := M)) (p + 1) (z : SingularChain (TopCat.of M) (p + 1)),
      mapChain_mem_cycles (topCoreMap (M := M)) z.2⟩

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- **The extracted boundary chain splits** across the clopen `ptPiece ⊥ ⊔ (ptPiece ⊥)ᶜ` partition.
`crossChain` is unfolded ONCE here (via `chainBoundary_crossChain`), in isolation, then re-hidden
behind `chainIncl`-injectivity. -/
theorem boundaryExtract_crossChain_bd (p : ℕ) (z : cycles (TopCat.of M) (p + 1)) :
    boundaryExtract (bdW M) (p + 1)
        ⟨crossChain (p + 1) (z : SingularChain (TopCat.of M) (p + 1)), crossChain_mem_lift p z⟩
      = chainIncl (ptPiece M ⊥) (p + 1)
          (mapChain (botCoreMap (M := M)) (p + 1) (z : SingularChain (TopCat.of M) (p + 1)))
      + chainIncl ((ptPiece M ⊥)ᶜ) (p + 1)
          (mapChain (topCoreMap (M := M)) (p + 1) (z : SingularChain (TopCat.of M) (p + 1))) := by
  apply chainIncl_injective (bdW M) (p + 1)
  rw [chainIncl_boundaryExtract, chainBoundary_crossChain p
      (z : SingularChain (TopCat.of M) (p + 1)) (LinearMap.mem_ker.mp z.2)]
  erw [map_add]
  rw [chainIncl_chainIncl_botCore p z, chainIncl_chainIncl_topCore p z]
  exact add_comm _ _

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- **`bdCrossH [z]` is the `relCycleToHom` class of the OPAQUE prism lift-chain** `crossChain z`. A
`Subtype.ext rfl` on the shared underlying `RelativeChain.mk`. -/
theorem bdCrossH_eq_relCycleToHom (p : ℕ) (z : cycles (TopCat.of M) (p + 1)) :
    bdCrossH (M := M) p (Homology.mk (TopCat.of M) (p + 1) z)
      = relCycleToHom (bdW M) (p + 1)
          ⟨crossChain (p + 1) (z : SingularChain (TopCat.of M) (p + 1)), crossChain_mem_lift p z⟩ := by
  simp only [bdCrossH]
  rw [crossH_mk, relCycleToHom_apply]
  exact congrArg (RelativeHomology.mk _ (p + 1 + 1)) (Subtype.ext rfl)

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- **`δ(bdCrossH [z])` SPLITS** across the clopen `ptPiece ⊥ ⊔ (ptPiece ⊥)ᶜ` partition as
`homIncl⊥ [end₀ z] + homIncl⊤ [end₁ z]`. -/
theorem connecting_bdCrossH_eq_split (p : ℕ) (z : cycles (TopCat.of M) (p + 1)) :
    connecting (bdW M) (p + 1)
        (bdCrossH (M := M) p (Homology.mk (TopCat.of M) (p + 1) z))
      = homIncl (ptPiece M ⊥) (p + 1) (botCls p z)
        + homIncl ((ptPiece M ⊥)ᶜ) (p + 1) (topCls p z) := by
  rw [bdCrossH_eq_relCycleToHom, connecting_relCycleToHom, connectingLift_apply, botCls, topCls,
    homIncl_mk, homIncl_mk, ← homology_mk_add]
  exact congrArg (Homology.mk (sub (bdW M)) (p + 1))
    (Subtype.ext (boundaryExtract_crossChain_bd p z))

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- **`ptPieceToM ⊥` detects the bottom half as `[z]`**: projecting the bottom-slice push back to `M`
collapses to `z` (`ptPieceToM ⊥ ∘ botCoreMap = id_M`). -/
theorem ptPieceToM_map_botCls (p : ℕ) (z : cycles (TopCat.of M) (p + 1)) :
    Homology.map (ptPieceToM (M := M) ⊥) (p + 1) (botCls p z)
      = Homology.mk (TopCat.of M) (p + 1) z := by
  rw [botCls, Homology.map_mk]
  refine congrArg (Homology.mk (TopCat.of M) (p + 1)) (Subtype.ext ?_)
  rw [cyclesMap_coe, ← mapChain_comp, botCoreMap,
    ptPieceToM_comp_mToPtPiece ⊥ (by simp), mapChain_id]

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- **`bdCrossH` is injective.** If `bdCrossH [z] = 0` then `δ(bdCrossH [z]) = 0`, so by the clopen
split `splitHn (·, ·) = 0`; `splitHn_injective` forces the bottom class `[z|₀] = 0`, and
`ptPieceToM ⊥` sends it back to `[z]`, forcing `[z] = 0`. -/
theorem bdCrossH_injective (p : ℕ) : Function.Injective (bdCrossH (M := M) p) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show Homology.mk (TopCat.of M) (p + 1) z = 0
  have hx' : bdCrossH (M := M) p (Homology.mk (TopCat.of M) (p + 1) z) = 0 := hx
  have hsplit : splitHn (ptPiece M ⊥) (p + 1) (botCls p z, topCls p z) = 0 := by
    have hthis := connecting_bdCrossH_eq_split p z
    rw [hx', map_zero] at hthis
    rw [splitHn]
    exact hthis.symm
  have hpair0 : (botCls p z, topCls p z) = 0 :=
    splitHn_injective (isClopen_ptPiece_bot (M := M)) (p + 1) (by rw [hsplit, map_zero])
  have hbot0 : botCls p z = 0 := congrArg Prod.fst hpair0
  rw [← ptPieceToM_map_botCls p z, hbot0, map_zero]

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- **`cylCrossH` is injective** — `cylCrossH` is defeq to `bdCrossH` (same `crossH` engine, boundary
spelled `cylBd`/`bdW`), so `bdCrossH_injective` transfers directly. -/
theorem cylCrossH_injective (p : ℕ) : Function.Injective (cylCrossH (M := M) p) :=
  bdCrossH_injective p

/-! ## §3. Bijectivity of `cylCrossH` — injective + the pair-suspension finrank equality -/

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- **`cylCrossH` is bijective** in a degree where `Hₚ₊₁(M)` and `Hₚ₊₂(W,∂W)` are finite-dimensional:
injective (`cylCrossH_injective`) plus the pair-suspension dimension count
`dim Hₚ₊₂(W,∂W) = dim Hₚ₊₁(M)` (`…CylinderSuspension.cylinder_relHom_finrank`) over the field `ℤ/2`. -/
theorem cylCrossH_bijective (p : ℕ)
    (hV : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) (p + 1)))
    (hW : FiniteDimensional (ZMod 2) (RelativeHomology (bdW M) (p + 1 + 1))) :
    Function.Bijective (cylCrossH (M := M) p) := by
  haveI := hV
  haveI : FiniteDimensional (ZMod 2) (RelativeHomology (cylBd (M := M)) (p + 1 + 1)) := hW
  exact bijective_of_injective_of_finrank_eq (cylCrossH (M := M) p) (cylCrossH_injective p)
    (cylinder_relHom_finrank (M := M) p).symm

end Injective

/-! ## §4. The `hbij`-DISCHARGED constructors — `ofCapCross` residual = the two projection values -/

section Constructors

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M] [PreconnectedSpace M]

open SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularRelativePairing
open SKEFTHawking.SingularRelativeCup
open SKEFTHawking.SingularCapHomology
open SKEFTHawking.SingularManifoldFundamentalClass
open SKEFTHawking.PoincareLefschetzWu5
open SKEFTHawking.PinPlusCylinderWAdmPinned
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderWu

/-- **The `β`-pinned intertwining-data builder with `hbij` DISCHARGED.** Identical to
`…CylinderSuspDual.CylinderSuspIntertwineData.ofCapCross` except the two pair-suspension iso witnesses
`hbij23`/`hbij14` are supplied INTERNALLY (`cylCrossH_bijective`, via `cylCrossH_injective` + the
pair-suspension finrank equality). The residual is exactly the two cap-cross projection values
`hproj23`/`hproj14` (plus `M`-side homology finiteness for the dimension count). -/
def CylinderSuspIntertwineData.ofCapCrossProj
    (hM2 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 2))
    (hM3 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 3))
    (hM4 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 4))
    (hproj23 : ∀ (a : Cohomology (TopCat.of (cylW M)) 2)
        (b : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 3),
        (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu
            (relCupH23 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M)) a b)
          = relKroneckerH (cylBd (M := M)) b
              (cylCrossH (M := M) 1 (capH 2 1 (cylCollapse2 a) (fundamentalClass (m := 2) (M := M)))))
    (hproj14 : ∀ (a : Cohomology (TopCat.of (cylW M)) 1)
        (b : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 4),
        (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu
            (relCupH14 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M)) a b)
          = relKroneckerH (cylBd (M := M)) b
              (cylCrossH (M := M) 2 (capH 1 2 (cylCollapse1 a) (fundamentalClass (m := 2) (M := M))))) :
    CylinderSuspIntertwineData M :=
  CylinderSuspIntertwineData.ofCapCross
    (cylCrossH_bijective (M := M) 1 hM2 (cylinder_findimRelHom23_of_base hM3 hM2))
    (cylCrossH_bijective (M := M) 2 hM3 (cylinder_findimRelHom14_of_base hM4 hM3))
    hproj23 hproj14

/-- **The FIRE — the `nondeg`-free, `hbij`-free `CylinderWAdmPinned` constructor.** The
`…CylinderIntertwine.CylinderWAdmPinned.ofClosedPDSuspIntertwine` successor consuming NO intertwine
data: the bundled `CylinderSuspIntertwineData` is built INTERNALLY by `ofCapCrossProj` (α pinned to the
collapse, `β` pinned to the geometric suspension, `hbij` discharged by `cylCrossH_bijective`). The
Track-2 residual VISIBLY collapses to: the two **cap-cross projection values** `hproj23`/`hproj14`, the
`hwu` Wu-class vanishing, `basePD` (`M`'s own `b₁ = b₃`), and `M`-intrinsic homology/cohomology
finiteness — `nondeg14`/`nondeg23` and the pair-suspension iso witnesses no longer appear. -/
def CylinderWAdmPinned.ofClosedPDSuspIntertwineProj
    (findimM1 : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of M) 1))
    (findimM2 : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of M) 2))
    (hM2 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 2))
    (hM3 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 3))
    (hM4 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 4))
    (basePD : Module.finrank (ZMod 2) (Homology (TopCat.of M) 1)
      = Module.finrank (ZMod 2) (Homology (TopCat.of M) 3))
    (hproj23 : ∀ (a : Cohomology (TopCat.of (cylW M)) 2)
        (b : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 3),
        (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu
            (relCupH23 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M)) a b)
          = relKroneckerH (cylBd (M := M)) b
              (cylCrossH (M := M) 1 (capH 2 1 (cylCollapse2 a) (fundamentalClass (m := 2) (M := M)))))
    (hproj14 : ∀ (a : Cohomology (TopCat.of (cylW M)) 1)
        (b : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 4),
        (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu
            (relCupH14 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M)) a b)
          = relKroneckerH (cylBd (M := M)) b
              (cylCrossH (M := M) 2 (capH 1 2 (cylCollapse1 a) (fundamentalClass (m := 2) (M := M)))))
    (hwu : wuW2
      (cylinderP14 (hasRelFundClass_cylGen (m' := 2) (M := M)) (cylinder_findimAbs14 findimM1)
        (cylinder_findimRel14 (cylinder_findimRelHom14_of_base hM4 hM3))
        (CylinderSuspIntertwineData.ofCapCrossProj hM2 hM3 hM4 hproj23 hproj14).nondeg14
        (cylinder_dimeq14_of_basePD hM3 basePD))
      (cylinderP23 (hasRelFundClass_cylGen (m' := 2) (M := M)) (cylinder_findimAbs23 findimM2)
        (cylinder_findimRel23 (cylinder_findimRelHom23_of_base hM3 hM2))
        (CylinderSuspIntertwineData.ofCapCrossProj hM2 hM3 hM4 hproj23 hproj14).nondeg23
        (cylinder_dimeq23_holds hM2)) = 0) :
    CylinderWAdmPinned M :=
  CylinderWAdmPinned.ofClosedPDSuspIntertwine findimM1 findimM2 hM2 hM3 hM4
    (CylinderSuspIntertwineData.ofCapCrossProj hM2 hM3 hM4 hproj23 hproj14) basePD hwu

end Constructors

end

end SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspBij
