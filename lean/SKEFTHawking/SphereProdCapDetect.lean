/-
# Route (c′) P4 — the cap-injectivity detection: `g ≠ 0 → g ⌢ [M] ≠ 0` on a closed 4-manifold,
# instantiated at `S²×S²`

The closed-4-manifold Poincaré duality (`SingularPD4Instances`) is, internally, *cap-with-[M]
injectivity*: `nondeg_of_closed` builds `Function.Injective (fun a ↦ capH 2 1 a [M])` (via
`capH_injective_of_fundamentalDuality_injective` at the `(2,1)` window) before wrapping it into the
cup-form nondeg. This module re-exposes that `(2,1)` cap-injectivity publicly (mirroring the private
`capH12_injective_of_closed`), instantiates it at the closed charted 4-manifold `S²×S²`, and delivers
the route-(c′) detection

  **`g ≠ 0 ⟹ capH 2 1 g [S²×S²] ≠ 0`   in   H₂(S²×S²)**

— the cap-injectivity route that replaces the mixed-cup strategy entirely.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
new `axiom`.
-/
import Mathlib
import SKEFTHawking.SingularPD4Instances
import SKEFTHawking.SingularCapMapChain
import SKEFTHawking.SingularCohomologyFunctoriality
import SKEFTHawking.PinPlusKTSphereProdRelFundWuRoots

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularCapHomology
open SKEFTHawking.SingularOpenDualityMVConnSquare SKEFTHawking.SingularPDWindow4
open SKEFTHawking.PoincareDualityConstruct
open SKEFTHawking.SingularUCFinite
open SKEFTHawking.SingularFundamentalClass SKEFTHawking.SingularChartBridge
open SKEFTHawking.SingularFundamentalDualityEndpoint
open SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularKroneckerFunctoriality
open SKEFTHawking.SingularCohomologyFunctoriality SKEFTHawking.SingularCapMapChain

namespace SKEFTHawking.SingularPD4Instances

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]

/-- **The `(2,1)`-window cap-with-[M] injectivity of a closed charted 4-manifold** —
`Function.Injective (fun a : H²(M) ↦ a ⌢ [M])`, `a ⌢ [M] = capH 2 1 a [M] ∈ H₂(M)`. Re-exposes the
internal `hinj` of `nondeg_of_closed` (the same `capH_injective_of_fundamentalDuality_injective` chain
at the `(2,1)` window that the cup-form nondeg wraps), the public companion of the private
`capH12_injective_of_closed`. -/
theorem capH21_injective_of_closed :
    Function.Injective (fun a : Cohomology (TopCat.of M) 2 =>
      capH 2 1 a (SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := M))) := by
  obtain ⟨zM, hzM, hcyc, hloc, hclass⟩ := exists_fundClass_P4_data (M := M)
  have hP4 := pdWindowP4_univ zM hzM hcyc hloc isOpen_univ
  have hbij := fundamentalDuality_bijective_of_openDuality_univ_bijective
    (M := TopCat.of M) (k := 2) (m := 1) isOpen_univ
    (castChain (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM)
    (chainBoundary_castChain_eq_zero (by omega) (by omega) zM hzM) hP4.1.1
  have hinj := capH_injective_of_fundamentalDuality_injective (M := TopCat.of M)
    (k := 2) (m := 1)
    (castChain (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM)
    (chainBoundary_castChain_eq_zero (by omega) (by omega) zM hzM) hbij.injective
  have hclass' : Homology.mk (TopCat.of M) (2 + 1 + 1)
      ⟨castChain (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM,
        SKEFTHawking.SingularDualityEmpty.cycle_of_subspaceChains_empty _
          (by rw [chainBoundary_castChain_eq_zero (by omega) (by omega) zM hzM]
              exact Submodule.zero_mem _)⟩
      = SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := M) :=
    (congrArg (Homology.mk (TopCat.of M) (2 + 1 + 1)) (Subtype.ext rfl)).trans hclass
  rwa [hclass'] at hinj

end SKEFTHawking.SingularPD4Instances

open SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.PinPlusKTSphereProdRelFundWuRoots
open SKEFTHawking.PinPlusCharPairRealizationTied

namespace SKEFTHawking.SphereProdCapDetect

/-- **Homology-level cap naturality (projection formula)** `a ⌢ (φ_* z) = φ_* ((φ^* a) ⌢ z)`. The
homology descent of the chain-level `SingularCapMapChain.cap_mapChain`, via `capH_mk_mk` /
`Homology.map_mk` / `cyclesMap_coe`. Generic and reusable. -/
theorem capH_map {X Y : TopCat} (φ : C(↑X, ↑Y)) (k m : ℕ)
    (a : Cohomology Y k) (z : Homology X (k + m + 1)) :
    capH k m a (Homology.map φ (k + m + 1) z)
      = Homology.map φ (m + 1) (capH k m (cohomologyPullback φ k a) z) := by
  obtain ⟨fa, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨zc, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [show (Submodule.Quotient.mk fa : Cohomology Y k) = Cohomology.mk Y k fa from rfl,
    show (Submodule.Quotient.mk zc : Homology X (k + m + 1)) = Homology.mk X (k + m + 1) zc from rfl,
    Homology.map_mk, capH_mk_mk, cohomologyPullback_mk, capH_mk_mk, Homology.map_mk]
  refine congrArg (Homology.mk Y (m + 1)) (Subtype.ext ?_)
  rw [capCyclesₗ_coe, cyclesMap_coe, cyclesMap_coe, capCyclesₗ_coe]
  exact cap_mapChain (k := k) (m := m + 1) φ fa.1 zc.1

/-- **The cap-injectivity detection on `S²×S²`.** `g ≠ 0 ⟹ g ⌢ [S²×S²] ≠ 0` in `H₂(S²×S²)`:
`S²×S²` is a closed charted 4-manifold (`chartedSpaceE4_SphereProd`), so `capH 2 1 · [S²×S²]` is
injective (`capH21_injective_of_closed`), and `[S²×S²] = sphereProdFundClass`. -/
theorem capH21_sphereProd_ne_zero (g : Cohomology (TopCat.of SphereProd) 2) (hg : g ≠ 0) :
    capH 2 1 g sphereProdFundClass ≠ 0 := by
  intro h
  apply hg
  refine @SingularPD4Instances.capH21_injective_of_closed SphereProd _ _ _ _
    chartedSpaceE4_SphereProd g 0 ?_
  show capH 2 1 g sphereProdFundClass = capH 2 1 0 sphereProdFundClass
  rw [h, map_zero, LinearMap.zero_apply]

/-- **The transported cap-injectivity detection on the closed boundary `∂W = sub sphereDiskBoundarySet
≃ₜ S²×S²`.** For a nonzero `g' ∈ H²(∂W)`, `capH 2 1 g' betaClass ≠ 0` in `H₂(∂W)` — the route-(c′)
detection in the exact shape P5 chains: `betaClass` is the transported fundamental class
(`= (sphereDiskInclHomeo)_* [S²×S²]`), and `capH_map` (cap naturality) + `capH21_sphereProd_ne_zero`
(closed-PD cap-injectivity on `S²×S²`) + `φ^*`/`φ_*` being isos under the homeomorphism combine. -/
theorem capH21_sub_ne_zero
    (g' : Cohomology (sub (X := TopCat.of SphereDisk) sphereDiskBoundarySet) 2) (hg' : g' ≠ 0) :
    capH 2 1 g' betaClass ≠ 0 := by
  let φ : C(↑(TopCat.of SphereProd), ↑(sub (X := TopCat.of SphereDisk) sphereDiskBoundarySet)) :=
    ⟨sphereDiskInclHomeo, sphereDiskInclHomeo.continuous⟩
  let ψ : C(↑(sub (X := TopCat.of SphereDisk) sphereDiskBoundarySet), ↑(TopCat.of SphereProd)) :=
    ⟨sphereDiskInclHomeo.symm, sphereDiskInclHomeo.symm.continuous⟩
  have hpb : cohomologyPullback φ 2 g' ≠ 0 := by
    intro h
    apply hg'
    have hcomp : φ.comp ψ = ContinuousMap.id _ :=
      ContinuousMap.ext fun y => sphereDiskInclHomeo.apply_symm_apply y
    have hid : cohomologyPullback ψ 2 (cohomologyPullback φ 2 g') = g' := by
      rw [← LinearMap.comp_apply, ← cohomologyPullback_comp, hcomp, cohomologyPullback_id,
        LinearMap.id_apply]
    rw [h, map_zero] at hid
    exact hid.symm
  have hbeta : betaClass = Homology.map φ 4 sphereProdFundClass :=
    homeoHomologyEquiv_apply sphereDiskInclHomeo 4 sphereProdFundClass
  rw [hbeta, capH_map φ 2 1 g' sphereProdFundClass]
  intro hmap
  refine capH21_sphereProd_ne_zero (cohomologyPullback φ 2 g') hpb
    ((homeoHomologyEquiv sphereDiskInclHomeo 2).injective ?_)
  rw [homeoHomologyEquiv_apply, map_zero]
  exact hmap

end SKEFTHawking.SphereProdCapDetect
