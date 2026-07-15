/-
# Phase 5q.H (W-A arm 4) — the terminal `αU ≠ 0`, the `hcls` FINISHER

This module discharges the ABSOLUTE residual isolated by `…CrossLocalDetect`:

  `αU = crossH_puncU([M]) ≠ 0`  (`alphaU x hx ≠ 0`)

— the prism of the closed manifold's fundamental class `[M]` rel the `I`-punctured piece
`puncU x = M×(I∖t)` is nonzero in `H_{m'+3}(M×I, puncU x)`, at every interior point `x`.

## The detection route (pair-LES connecting map, opacity-clean)

`αU ≠ 0 ⟸ δ_U(αU) ≠ 0` where `δ_U = connecting (puncU x) (m'+2)` is the pair connecting map
(`SingularPairLES`), which is linear so `0 ↦ 0`. The nonvanishing of `δ_U(αU)` is computed at the
**opacity boundary** that the interval-degree-0 twin (`SingularIntervalPairClass`) navigated:

* **`alphaU_eq_relCycleToHom`** rewrites `αU` (a `crossH_mk` class) as `relCycleToHom (puncU x)`
  of the OPAQUE prism lift-chain `crossChain z` — a `Subtype.ext rfl` on the shared underlying
  `RelativeChain.mk`, so `crossChain` is never whnf-ed inside the quotient.
* **`connecting_relCycleToHom` + `connectingLift_apply`** (from `SingularPairLES`) then give
  `δ_U(αU) = [boundaryExtract ⟨crossChain z, …⟩]` with `crossChain` still OPAQUE — the connecting-map
  value rule is hypothesis-parameterized on the boundary lift, so the kernel never normalizes the
  prism face-sum inside the connecting map.
* **`boundaryExtract_crossChain`** unfolds `crossChain` ONCE, in ISOLATION, characterizing the
  extracted chain via `chainIncl`-injectivity (`chainIncl_boundaryExtract` + `chainBoundary_crossChain`):
  `boundaryExtract ⟨crossChain z, …⟩ = end₀ z + end₁ z`, the two endpoint slices corestricted into the
  two clopen halves of `sub(puncU x)`.
* **`alphaU_boundary_ne_zero`** detects the class via the clopen `belowT ⊔ aboveT` split
  (`puncUSubHomEquiv`): the below-half projects (`projLeft ∘ botSecLeft = id`) to `[M] ≠ 0`.

This is the `(m'+2)`-dimensional mirror of `SingularIntervalPairClass.restrictBd_zGen_ne_zero`, with
the fundamental class in place of the `H₀` augmentation. Chaining through `…CrossLocalDetect` gives the
UNCONDITIONAL `hasRelFundClass_cylGen` (the terminal `hcls`), for any closed connected charted `M`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalDetect
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedPieceU

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
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedCover
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedPieceU
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalBridge
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalDetect

namespace SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalAlphaU

noncomputable section

/-! ## §1. Generic prism-chain lemmas — boundary and lift membership -/

section Generic

variable {M : TopCat}

/-- **The boundary of the cross-product chain** on a cycle: `∂(crossChain z) = end₁ z + end₀ z`,
the sum of the two endpoint slices. The prism chain homotopy `∂(Pz) + P(∂z) = end₁ z + end₀ z` with
`∂z = 0`. This is the isolated `crossChain`-UNFOLDING step (kept OUT of the relative-homology
quotient by the opacity architecture). -/
theorem chainBoundary_crossChain (p : ℕ) (z : SingularChain M (p + 1))
    (hz : chainBoundary M p z = 0) :
    chainBoundary (cyl M) (p + 1) (crossChain (p + 1) z)
      = mapChain (slice (graphHom M) 1) (p + 1) z + mapChain (slice (graphHom M) 0) (p + 1) z := by
  have hkey := prism_chainHomotopy (graphHom M) z
  rw [hz, map_zero, add_zero, endMap_eq_mapChain, endMap_eq_mapChain] at hkey
  exact hkey

/-- **The cross-product chain lies in the connecting-map lift submodule** `Z_{p+1} = {c | ∂c ∈ C(S)}`,
for any subspace `S` containing both endpoint slices. The two endpoint pushes are `S`-chains. -/
theorem crossChain_mem_relCycleLift {S : Set ↑(cyl M)}
    (h1 : Set.MapsTo (slice (graphHom M) 1) (Set.univ : Set ↑M) S)
    (h0 : Set.MapsTo (slice (graphHom M) 0) (Set.univ : Set ↑M) S)
    (p : ℕ) (z : SingularChain M (p + 1)) (hz : chainBoundary M p z = 0) :
    crossChain (p + 1) z ∈ relCycleLift S (p + 1) := by
  show chainBoundary (cyl M) (p + 1) (crossChain (p + 1) z) ∈ subspaceChains S (p + 1)
  rw [chainBoundary_crossChain p z hz]
  exact Submodule.add_mem _
    (mapChain_mem_subspaceChains (slice (graphHom M) 1) h1 (p + 1) z (mem_subspaceChains_univ _ z))
    (mapChain_mem_subspaceChains (slice (graphHom M) 0) h0 (p + 1) z (mem_subspaceChains_univ _ z))

end Generic

/-! ## §2. `αU` as a `relCycleToHom` class, and the opacity-clean connecting value -/

section Concrete

variable {m' : ℕ}
  {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m' + 2))) M]

omit [T2Space M] [CompactSpace M] [Nonempty M] [PreconnectedSpace M] in
/-- The prism lift-chain `crossChain z` of a fundamental cycle rep lies in the connecting-map lift
submodule `Z_{m'+2}` of the pair `(M×I, puncU x)`. -/
theorem crossChain_fund_mem_lift (x : ↑(TopCat.of (cylW M)))
    (hx : x ∉ (cylModel m').boundary (cylW M)) (z : cycles (TopCat.of M) (m' + 2)) :
    crossChain (m' + 2) (z : SingularChain (TopCat.of M) (m' + 2))
      ∈ relCycleLift (puncU (N := TopCat.of M) x) (m' + 2) :=
  crossChain_mem_relCycleLift (slice_one_maps_puncU x hx) (slice_zero_maps_puncU x hx)
    (m' + 1) (z : SingularChain (TopCat.of M) (m' + 2)) (LinearMap.mem_ker.mp z.2)

omit [PreconnectedSpace M] in
/-- **`αU` is the `relCycleToHom` class of the OPAQUE prism lift-chain** `crossChain z`. A
`Subtype.ext rfl` on the shared underlying `RelativeChain.mk` — `crossChain` is never whnf-ed inside
the relative-homology quotient (the opacity boundary the interval twin navigated). -/
theorem alphaU_eq_relCycleToHom (x : ↑(TopCat.of (cylW M)))
    (hx : x ∉ (cylModel m').boundary (cylW M)) (z : cycles (TopCat.of M) (m' + 2))
    (hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := m') (M := M)
      = Homology.mk (TopCat.of M) (m' + 2) z) :
    alphaU x hx = relCycleToHom (puncU (N := TopCat.of M) x) (m' + 2)
      ⟨crossChain (m' + 2) (z : SingularChain (TopCat.of M) (m' + 2)),
        crossChain_fund_mem_lift x hx z⟩ := by
  simp only [alphaU]
  rw [hz, crossH_mk, relCycleToHom_apply]
  exact congrArg (RelativeHomology.mk (puncU (N := TopCat.of M) x) (m' + 3)) (Subtype.ext rfl)

/-! ## §3. The extracted boundary chain — `crossChain` unfolded ONCE, in isolation -/

omit [T2Space M] [CompactSpace M] [Nonempty M] [PreconnectedSpace M] in
/-- **Composite-slice identity (bottom).** `sub(leftPieceU x) ↪ sub(puncU x) ↪ M×I` after `botSecLeft`
is the absolute bottom slice `slice 0` — every arrow is `Subtype.val` / the identity graph, so `rfl`. -/
theorem subIncl_botSecLeft_eq_slice0 (x : ↑(TopCat.of (cylW M)))
    (ht0 : (0 : ℝ) < (x.2 : ℝ)) :
    ((subInclCM (puncU (N := TopCat.of M) x)).comp
          (subInclCM (leftPieceU (N := TopCat.of M) x))).comp
        (botSecLeft (N := TopCat.of M) x ht0)
      = slice (graphHom (TopCat.of M)) 0 := by
  apply ContinuousMap.ext; intro a; rfl

omit [T2Space M] [CompactSpace M] [Nonempty M] [PreconnectedSpace M] in
/-- **Composite-slice identity (top).** `sub((leftPieceU x)ᶜ) ↪ sub(puncU x) ↪ M×I` after `topSecRight`
is the absolute top slice `slice 1`. -/
theorem subIncl_topSecRight_eq_slice1 (x : ↑(TopCat.of (cylW M)))
    (ht1 : (x.2 : ℝ) < 1) :
    ((subInclCM (puncU (N := TopCat.of M) x)).comp
          (subInclCM ((leftPieceU (N := TopCat.of M) x)ᶜ))).comp
        (topSecRight (N := TopCat.of M) x ht1)
      = slice (graphHom (TopCat.of M)) 1 := by
  apply ContinuousMap.ext; intro a; rfl

omit [T2Space M] [CompactSpace M] [Nonempty M] [PreconnectedSpace M] in
/-- The bottom half-chain re-included all the way to `M×I` is the absolute bottom-slice push
`end₀ z`. (`chainIncl = mapChain ∘ subInclCM`, functoriality, and the composite-slice identity.) -/
theorem chainIncl_chainIncl_botHalf (x : ↑(TopCat.of (cylW M)))
    (hx : x ∉ (cylModel m').boundary (cylW M)) (z : cycles (TopCat.of M) (m' + 2)) :
    chainIncl (puncU (N := TopCat.of M) x) (m' + 2)
        (chainIncl (leftPieceU (N := TopCat.of M) x) (m' + 2)
          (mapChain (botSecLeft (N := TopCat.of M) x (interior_real_bounds x hx).1) (m' + 2)
            (z : SingularChain (TopCat.of M) (m' + 2))))
      = mapChain (slice (graphHom (TopCat.of M)) 0) (m' + 2)
          (z : SingularChain (TopCat.of M) (m' + 2)) := by
  rw [← mapChain_subInclCM (leftPieceU (N := TopCat.of M) x) (m' + 2),
    ← mapChain_subInclCM (puncU (N := TopCat.of M) x) (m' + 2), ← mapChain_comp, ← mapChain_comp,
    subIncl_botSecLeft_eq_slice0 x (interior_real_bounds x hx).1]

omit [T2Space M] [CompactSpace M] [Nonempty M] [PreconnectedSpace M] in
/-- The top half-chain re-included all the way to `M×I` is the absolute top-slice push `end₁ z`. -/
theorem chainIncl_chainIncl_topHalf (x : ↑(TopCat.of (cylW M)))
    (hx : x ∉ (cylModel m').boundary (cylW M)) (z : cycles (TopCat.of M) (m' + 2)) :
    chainIncl (puncU (N := TopCat.of M) x) (m' + 2)
        (chainIncl ((leftPieceU (N := TopCat.of M) x)ᶜ) (m' + 2)
          (mapChain (topSecRight (N := TopCat.of M) x (interior_real_bounds x hx).2) (m' + 2)
            (z : SingularChain (TopCat.of M) (m' + 2))))
      = mapChain (slice (graphHom (TopCat.of M)) 1) (m' + 2)
          (z : SingularChain (TopCat.of M) (m' + 2)) := by
  rw [← mapChain_subInclCM ((leftPieceU (N := TopCat.of M) x)ᶜ) (m' + 2),
    ← mapChain_subInclCM (puncU (N := TopCat.of M) x) (m' + 2), ← mapChain_comp, ← mapChain_comp,
    subIncl_topSecRight_eq_slice1 x (interior_real_bounds x hx).2]

omit [T2Space M] [CompactSpace M] [Nonempty M] [PreconnectedSpace M] in
/-- **The extracted boundary chain**: `boundaryExtract ⟨crossChain z, …⟩ = (bottom half) + (top half)`,
the two endpoint slices corestricted into the two clopen halves of `sub(puncU x)`. `crossChain` is
unfolded ONCE here (via `chainBoundary_crossChain`), in ISOLATION from the relative-homology quotient
— then re-hidden behind `chainIncl`-injectivity. -/
theorem boundaryExtract_crossChain (x : ↑(TopCat.of (cylW M)))
    (hx : x ∉ (cylModel m').boundary (cylW M)) (z : cycles (TopCat.of M) (m' + 2)) :
    boundaryExtract (puncU (N := TopCat.of M) x) (m' + 2)
        ⟨crossChain (m' + 2) (z : SingularChain (TopCat.of M) (m' + 2)),
          crossChain_fund_mem_lift x hx z⟩
      = chainIncl (leftPieceU (N := TopCat.of M) x) (m' + 2)
          (mapChain (botSecLeft (N := TopCat.of M) x (interior_real_bounds x hx).1) (m' + 2)
            (z : SingularChain (TopCat.of M) (m' + 2)))
      + chainIncl ((leftPieceU (N := TopCat.of M) x)ᶜ) (m' + 2)
          (mapChain (topSecRight (N := TopCat.of M) x (interior_real_bounds x hx).2) (m' + 2)
            (z : SingularChain (TopCat.of M) (m' + 2))) := by
  apply chainIncl_injective (puncU (N := TopCat.of M) x) (m' + 2)
  rw [chainIncl_boundaryExtract, chainBoundary_crossChain (m' + 1)
      (z : SingularChain (TopCat.of M) (m' + 2)) (LinearMap.mem_ker.mp z.2), map_add,
    chainIncl_chainIncl_botHalf x hx z, chainIncl_chainIncl_topHalf x hx z]
  exact add_comm _ _

/-! ## §4. The clopen-split detection — `δ_U(αU) ≠ 0`, hence `αU ≠ 0` -/

/-- `Homology.mk` is additive (definitional — the quotient module structure lifts `+`). -/
theorem homology_mk_add {X : TopCat} (n : ℕ) (a b : cycles X n) :
    Homology.mk X n (a + b) = Homology.mk X n a + Homology.mk X n b := rfl

/-- **The below-`t` half class** `[end₀ z] ∈ H_{m'+2}(sub(leftPieceU x))`: the bottom endpoint slice
of the fundamental cycle, in the below-`t` clopen half. -/
def leftCls (x : ↑(TopCat.of (cylW M)))
    (hx : x ∉ (cylModel m').boundary (cylW M)) (z : cycles (TopCat.of M) (m' + 2)) :
    Homology (sub (leftPieceU (N := TopCat.of M) x)) (m' + 2) :=
  Homology.mk (sub (leftPieceU (N := TopCat.of M) x)) (m' + 2)
    ⟨mapChain (botSecLeft (N := TopCat.of M) x (interior_real_bounds x hx).1) (m' + 2)
        (z : SingularChain (TopCat.of M) (m' + 2)),
      mapChain_mem_cycles _ z.2⟩

/-- **The above-`t` half class** `[end₁ z] ∈ H_{m'+2}(sub((leftPieceU x)ᶜ))`. -/
def rightCls (x : ↑(TopCat.of (cylW M)))
    (hx : x ∉ (cylModel m').boundary (cylW M)) (z : cycles (TopCat.of M) (m' + 2)) :
    Homology (sub ((leftPieceU (N := TopCat.of M) x)ᶜ)) (m' + 2) :=
  Homology.mk (sub ((leftPieceU (N := TopCat.of M) x)ᶜ)) (m' + 2)
    ⟨mapChain (topSecRight (N := TopCat.of M) x (interior_real_bounds x hx).2) (m' + 2)
        (z : SingularChain (TopCat.of M) (m' + 2)),
      mapChain_mem_cycles _ z.2⟩

omit [PreconnectedSpace M] in
/-- **`δ_U(αU)` SPLITS across the clopen `belowT ⊔ aboveT` partition** as `homIncl [end₀ z] +
homIncl [end₁ z]`. The opacity-clean connecting value (`connecting_relCycleToHom` +
`connectingLift_apply`) followed by the isolated `boundaryExtract_crossChain` computation, repackaged
through `homIncl` on the two clopen halves. -/
theorem connecting_alphaU_eq_split (x : ↑(TopCat.of (cylW M)))
    (hx : x ∉ (cylModel m').boundary (cylW M)) (z : cycles (TopCat.of M) (m' + 2))
    (hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := m') (M := M)
      = Homology.mk (TopCat.of M) (m' + 2) z) :
    connecting (puncU (N := TopCat.of M) x) (m' + 2) (alphaU x hx)
      = homIncl (leftPieceU (N := TopCat.of M) x) (m' + 2) (leftCls x hx z)
        + homIncl ((leftPieceU (N := TopCat.of M) x)ᶜ) (m' + 2) (rightCls x hx z) := by
  rw [alphaU_eq_relCycleToHom x hx z hz, connecting_relCycleToHom, connectingLift_apply,
    leftCls, rightCls, homIncl_mk, homIncl_mk, ← homology_mk_add]
  exact congrArg (Homology.mk (sub (puncU (N := TopCat.of M) x)) (m' + 2))
    (Subtype.ext (boundaryExtract_crossChain x hx z))

omit [PreconnectedSpace M] in
/-- **`projLeft` detects the below-half as `[M]`**: `Hₘ₊₂(projLeft x)[end₀ z] = [M]`, since
`projLeft ∘ botSecLeft = id_M` collapses the bottom-slice push to `z`, whose class is `[M]`. -/
theorem projLeft_map_leftCls (x : ↑(TopCat.of (cylW M)))
    (hx : x ∉ (cylModel m').boundary (cylW M)) (z : cycles (TopCat.of M) (m' + 2))
    (hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := m') (M := M)
      = Homology.mk (TopCat.of M) (m' + 2) z) :
    Homology.map (projLeft (N := TopCat.of M) x) (m' + 2) (leftCls x hx z)
      = SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := m') (M := M) := by
  rw [leftCls, Homology.map_mk, hz]
  refine congrArg (Homology.mk (TopCat.of M) (m' + 2)) (Subtype.ext ?_)
  rw [cyclesMap_coe, ← mapChain_comp, projLeft_comp_botSecLeft, mapChain_id]

omit [PreconnectedSpace M] in
/-- **The terminal split detection**: `δ_U(αU) ≠ 0`. If it were `0`, the clopen split (via
`splitHnEquiv` injectivity) would force `[end₀ z] = 0`; but `projLeft` sends it to `[M] ≠ 0`. -/
theorem connecting_alphaU_ne_zero (x : ↑(TopCat.of (cylW M)))
    (hx : x ∉ (cylModel m').boundary (cylW M)) (z : cycles (TopCat.of M) (m' + 2))
    (hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := m') (M := M)
      = Homology.mk (TopCat.of M) (m' + 2) z) :
    connecting (puncU (N := TopCat.of M) x) (m' + 2) (alphaU x hx) ≠ 0 := by
  intro hzero
  have hpair : splitHn (leftPieceU (N := TopCat.of M) x) (m' + 2) (leftCls x hx z, rightCls x hx z)
      = 0 := by
    have := connecting_alphaU_eq_split x hx z hz
    rw [hzero] at this
    rw [splitHn]
    exact this.symm
  have hpair0 : (leftCls x hx z, rightCls x hx z) = 0 :=
    splitHn_injective (isClopen_leftPieceU (N := TopCat.of M) x) (m' + 2) (by
      rw [hpair, map_zero])
  have hleft0 : leftCls x hx z = 0 := congrArg Prod.fst hpair0
  refine SKEFTHawking.SingularFundamentalClass.fundamentalClass_ne_zero
    (m := m') (M := M) (Classical.arbitrary M) ?_
  rw [← projLeft_map_leftCls x hx z hz, hleft0, map_zero]

omit [PreconnectedSpace M] in
/-- **The terminal `αU ≠ 0`**: the connecting map is linear (`0 ↦ 0`), so `δ_U(αU) ≠ 0` forces
`αU ≠ 0`. This is the ABSOLUTE `crossH_puncU([M]) ≠ 0` — the sole obligation `…CrossLocalDetect`
reduced the concrete cylinder `hcls` to. -/
theorem alphaU_ne_zero (x : ↑(TopCat.of (cylW M)))
    (hx : x ∉ (cylModel m').boundary (cylW M)) (z : cycles (TopCat.of M) (m' + 2))
    (hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := m') (M := M)
      = Homology.mk (TopCat.of M) (m' + 2) z) :
    alphaU x hx ≠ 0 := by
  intro h0
  exact connecting_alphaU_ne_zero x hx z hz (by rw [h0, map_zero])

/-! ## §5. The UNCONDITIONAL terminal `hcls` — for any closed connected charted `M` -/

/-- **The UNCONDITIONAL concrete-cylinder `HasRelFundClass`** (the terminal `hcls`), for any closed
connected charted manifold `M`. Chains the ABSOLUTE `alphaU_ne_zero` (§4) through the reduction
`…CrossLocalDetect.hasRelFundClass_cylGen_of_alphaU_ne_zero` (which itself routes through the
chain-for-chain bridge `crossHloc = ι_U(αU)` and `ι_U` injective). The last hole of the concrete
product cross-product existence route `[W,∂W] = [M] × [I,∂I]` is discharged. -/
theorem hasRelFundClass_cylGen [T1Space (cylW M)] :
    HasRelFundClass (X := TopCat.of (cylW M)) ((cylModel m').boundary (cylW M))
      (cylGen (M := M) (m' := m')) := by
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _
    (SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := m') (M := M))
  refine hasRelFundClass_cylGen_of_alphaU_ne_zero z hz.symm
    (fun x hx => alphaU_ne_zero x hx z hz.symm)

end Concrete

end

end SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalAlphaU
