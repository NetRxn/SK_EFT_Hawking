import Mathlib
import SKEFTHawking.PinPlusCylDataDischargeDisconnected

/-!
# Phase 5q.H — THE COMPONENT DECOMPOSITION (Route 2, staged)

Building the five-field `DisconnectedCylCore M` (`D, hM4, nd14, nd23, hwu`) for a NONEMPTY
DISCONNECTED closed charted 4-manifold from the finite component decomposition.

The connectedness dependence of the connected engine is genuinely irreducible: it localises to the
punctured-top-vanishing `H₄(M∖σ) = 0` (`…CylinderOpenTopVanish.openManifold_top_homology_eq_zero`),
which is FALSE for disconnected `M` (the other closed components survive with nonzero top homology).
Route 2 routes around this via the finite clopen component decomposition + the binary clopen-split
engine `SingularDisjointUnionHn.splitHnEquiv`, peeling one component at a time.
-/

open scoped Manifold
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularRelativeCup
open SKEFTHawking.PoincareLefschetzWu5
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderWu
open SKEFTHawking.PinPlusCylDataDischarge
open SKEFTHawking.PinPlusCylDataDischargeDisconnected
open SKEFTHawking.SingularFundamentalClass
open SKEFTHawking.SingularChartBridge
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularRelativeMV
open SKEFTHawking.SingularRelativeEmpty

namespace SKEFTHawking.PinPlusCylDataDischargeDisconnectedComponents

noncomputable section

variable (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]

/-! ## §1. Finiteness of the connected components of a compact charted manifold. -/

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- **A charted space over a locally-connected model is locally connected** (the model
`EuclideanSpace ℝ (Fin 4)` is locally connected; `ChartedSpace.locallyConnectedSpace`). -/
theorem locallyConnected_charted : LocallyConnectedSpace M :=
  ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M

omit [T2Space M] [Nonempty M] in
/-- **A compact charted manifold has finitely many connected components** (locally connected +
compact; `instFiniteConnectedComponentsOfLocallyConnectedSpaceOfCompactSpace`). -/
theorem finite_connectedComponents : Finite (ConnectedComponents M) := by
  haveI := locallyConnected_charted M
  infer_instance

/-! ## §2. Top-homology finiteness for a (possibly disconnected) closed charted 4-manifold.

The connected case gets `H₄(M) ≅ ℤ/2` from the single-point restriction being injective
(`finiteDimensional_topHomology_of_closed_connected`, via the clopen vanishing set being `univ` by
connectedness). For disconnected `M` we generalise: the vanishing set of the per-point restriction is
clopen, hence a union of connected components; so a class restricting to `0` at ONE point per
component vanishes at EVERY point, hence is `0` (connectedness-free `determinedByPoints` tail). This
makes the multi-point restriction `H₄(M) → ∏_{c} H₄(M|x_c)` injective into a finite product of
`ℤ/2`'s (finite components), so `H₄(M)` is finite-dimensional — with NO per-component submanifold. -/

/-- **The connectedness-free tail**: a top class `α ∈ H₄(M)` that restricts to `0` at EVERY point is
`0`. Exactly the second half of `restrictHomologyToPoint_injective` (the `determinedByPoints`-on-`univ`
collapse), lifted out of the connectedness-dependent `S = univ` step. -/
theorem topHomology_eq_zero_of_forall_restrict_zero {α : Homology (TopCat.of M) 4}
    (hall : ∀ x : M, restrictHomologyToPoint (X := TopCat.of M) x 4 α = 0) : α = 0 := by
  have hdet := (SKEFTHawking.SingularGoodCompactManifold.goodCompact_univ (m := 2) (M := M)).2
  have hβ0 : restrictHomologyToSet (X := TopCat.of M) (Set.univ : Set ↑(TopCat.of M)) 4 α = 0 :=
    hdet (restrictHomologyToSet (Set.univ : Set ↑(TopCat.of M)) 4 α)
      (fun x hx => by rw [restrictToPoint_restrictHomologyToSet hx 4 α]; exact hall x)
  have huniv_empty : (Set.univ : Set ↑(TopCat.of M))ᶜ ⊆ (∅ : Set ↑(TopCat.of M)) :=
    Set.compl_univ.subset
  have hγ : (relHomologyEmptyEquiv (X := TopCat.of M) 4).symm α = 0 := by
    have hback : relIncl huniv_empty 4
        (restrictHomologyToSet (Set.univ : Set ↑(TopCat.of M)) 4 α)
        = (relHomologyEmptyEquiv (X := TopCat.of M) 4).symm α := by
      show relIncl huniv_empty 4
          (relIncl (Set.empty_subset (Set.univ : Set ↑(TopCat.of M))ᶜ) 4
            ((relHomologyEmptyEquiv (X := TopCat.of M) 4).symm α))
        = (relHomologyEmptyEquiv (X := TopCat.of M) 4).symm α
      rw [relIncl_trans, relIncl, SKEFTHawking.SingularRelativeFunctoriality.RelativeHomology.map_id]
      rfl
    rw [hβ0, map_zero] at hback
    exact hback.symm
  have hα := congrArg (relHomologyEmptyEquiv (X := TopCat.of M) 4) hγ
  rwa [LinearEquiv.apply_symm_apply, map_zero] at hα

omit [CompactSpace M] [Nonempty M] in
/-- **The per-point-restriction vanishing set is clopen** (the head of
`restrictHomologyToPoint_injective`, connectedness-free): `S = {y | ρ_y α = 0}`. -/
theorem isClopen_restrictZero (α : Homology (TopCat.of M) 4) :
    IsClopen {y : M | restrictHomologyToPoint (X := TopCat.of M) y 4 α = 0} := by
  have hSopen : IsOpen {y : M | restrictHomologyToPoint (X := TopCat.of M) y 4 α = 0} := by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨U, hUopen, hxU, hUconst⟩ := restrictHomologyToPoint_locally_constant (m := 2) α x
    exact ⟨U, fun y hy => (hUconst y hy).mpr hx, hUopen, hxU⟩
  have hScopen : IsOpen {y : M | restrictHomologyToPoint (X := TopCat.of M) y 4 α = 0}ᶜ := by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨U, hUopen, hxU, hUconst⟩ := restrictHomologyToPoint_locally_constant (m := 2) α x
    exact ⟨U, fun y hy hyS => hx ((hUconst y hy).mp hyS), hUopen, hxU⟩
  exact ⟨isOpen_compl_iff.mp hScopen, hSopen⟩

/-- **The disconnected top-homology finiteness `hM4`**: `H₄(M)` is finite-dimensional for a
(possibly disconnected) closed charted 4-manifold. The multi-point restriction
`Φ : H₄(M) → ∏_{c : ConnectedComponents M} H₄(M | x_c)` (one representative point `x_c` per component)
is injective — a class in `ker Φ` restricts to `0` at each `x_c`, its clopen vanishing set thus meets
every component and (clopen ⟹ union of components) is `univ`, so it is `0`
(`topHomology_eq_zero_of_forall_restrict_zero`). The codomain is a finite product (finite components,
`finite_connectedComponents`) of `ℤ/2`'s (`manifoldLocalIso`), hence finite-dimensional. -/
theorem topHomology_finite : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 4) := by
  haveI : Finite (ConnectedComponents M) := finite_connectedComponents M
  have hsurj : Function.Surjective (ConnectedComponents.mk : M → ConnectedComponents M) :=
    ConnectedComponents.surjective_coe
  set reps : ConnectedComponents M → M := Function.surjInv hsurj with hrepsdef
  have hreps : ∀ c, ConnectedComponents.mk (reps c) = c := fun c => Function.surjInv_eq hsurj c
  set Φ : Homology (TopCat.of M) 4 →ₗ[ZMod 2]
      (∀ c : ConnectedComponents M, RelativeHomology ({reps c}ᶜ : Set ↑(TopCat.of M)) 4) :=
    LinearMap.pi (fun c => restrictHomologyToPoint (X := TopCat.of M) (reps c) 4) with hΦ
  haveI : ∀ c, FiniteDimensional (ZMod 2)
      (RelativeHomology ({reps c}ᶜ : Set ↑(TopCat.of M)) 4) :=
    fun c => (manifoldLocalIso (m := 2) (reps c)).symm.finiteDimensional
  refine FiniteDimensional.of_injective Φ ?_
  rw [injective_iff_map_eq_zero]
  intro α hα
  have hc0 : ∀ c, restrictHomologyToPoint (X := TopCat.of M) (reps c) 4 α = 0 := by
    intro c
    have := congrFun (congrArg (fun f => f) hα) c
    simpa [hΦ, LinearMap.pi_apply] using this
  apply topHomology_eq_zero_of_forall_restrict_zero
  intro x
  have hSclopen := isClopen_restrictZero M α
  have hrep_mem : reps (ConnectedComponents.mk x) ∈
      {y : M | restrictHomologyToPoint (X := TopCat.of M) y 4 α = 0} := hc0 _
  have hcomp_sub := hSclopen.connectedComponent_subset hrep_mem
  have hx_comp : x ∈ connectedComponent (reps (ConnectedComponents.mk x)) := by
    have hcc : connectedComponent (reps (ConnectedComponents.mk x)) = connectedComponent x :=
      ConnectedComponents.coe_eq_coe.mp (by rw [hreps])
    rw [hcc]; exact mem_connectedComponent
  exact hcomp_sub hx_comp

end

end SKEFTHawking.PinPlusCylDataDischargeDisconnectedComponents
