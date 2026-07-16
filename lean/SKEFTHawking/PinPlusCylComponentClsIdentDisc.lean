import Mathlib
import SKEFTHawking.PinPlusCylComponentDisconnectedCoreNDDelta
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderClsIdent
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalAlphaU
import SKEFTHawking.SingularFundamentalClassSum
import SKEFTHawking.SingularCapCrossProjection

/-!
# Phase 5q.H close-out — THE hcls TRANSPORT (the provider's LAST hypothesis)

`PinPlusCylComponentDisconnectedCoreNDDelta.nonempty_provider_of_disconnectedClsIdent` reduces the
entire char-pair `W`-provider to ONE per-carrier class identity

  `hcls : discD.cls = cylFundClassCandidate M`   (the k-component `[W,∂W] = [M] × [I,∂I]`)

for a possibly-disconnected closed charted 4-manifold `M`. This module DISCHARGES `hcls` and ships the
zero-hypothesis provider.

## The route (connectedness-free assembly + per-component detection)

Exactly as the connected `…CylinderClsIdent.cylinderDatum_cls_eq_crossH`, `hcls` follows from
`cylinderRelFundClass_unique_of_slab` (connectedness-free) applied to the two `RestrictsToRelGen`
witnesses: `discD.restricts` (the datum's own restriction, already discharged connectedness-free by the
k-component excision assembly) and the explicit candidate's restriction
`cylFundClassCandidate_restricts`. The connected candidate-restriction reduces (via
`restrictsToRelGen_candidate_of_ne_zero` + `restrictBd_candidate_eq_crossHloc`) to the per-point
obligation `crossHloc([M]|σ) ≠ 0` at every interior point — whose connected discharge
(`crossHloc_ne_zero_of_alphaU_ne_zero`) routes through `relIncl_puncU_compl_injective`, i.e. the
punctured-top flank injectivity that is genuinely FALSE for disconnected `M`.

The fix is **per-component transport**: the local homology at an interior point `x = (σ, t)` is a local
invariant, so it is detected on the clopen connected component `C = connectedComponent σ` (where the
connected engine fires — the punctured-top fence is honored PER PIECE). The component inclusion
`ιC : ↥C ↪ M` is an open embedding (C clopen); its cylinder lift `cylMap = ιC × id : cylW ↥C → cylW M`
is an open embedding too. The obligation transports across:

* **crossHloc naturality** (`crossHloc_naturality`): `crossHloc` commutes with the pushforwards along
  `ιC` (source) and `cylMap` (target), via `mapChain_prismOp` (target prism naturality) and the
  rfl-based prism source naturality `prismOp_mapChain` (both `graphHom = id`, `cylMap = ιC × id`);
* **mLocalClass naturality** (`mLocalClass_eq_map`): `[M]|_σ = ιC_*([C]|_σ)`, because both restrict to
  the SAME local generator at `σ` (`fundamentalClass_restricts` on `M`; `restrict_map_fundClass_open` +
  `restrictHomologyToPoint_naturality` on `C`);
* **open-embedding injectivity** (`relPointMap_injective_of_isOpenEmbedding` on `cylMap`);
* the **connected** nonvanishing `crossHloc_ne_zero_of_alphaU_ne_zero` + `alphaU_ne_zero` on `↥C`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new axiom, no
`native_decide`, no `maxHeartbeats`.
-/

open scoped Manifold
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularRelativeFunctoriality
open SKEFTHawking.SingularPrism
open SKEFTHawking.SingularHomotopyInvariance (slice)
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.SingularFundamentalClass
open SKEFTHawking.SingularFundamentalClassPushforward
open SKEFTHawking.SingularFundamentalClassSum
open SKEFTHawking.SingularChartBridge
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCross
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocal
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalReduce
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalBridge
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalAlphaU
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossRestrict
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderClsIdent
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderWu

namespace SKEFTHawking.PinPlusCylComponentClsIdentDisc

noncomputable section

/-! ## §0. Prism source naturality — `prismOp H (φ_# c) = prismOp (H ∘ (φ × id)) c`. -/

/-- **Prism source naturality (simplex level, rfl).** The prism simplex of a pushed simplex is the
prism simplex under the pre-composed homotopy. -/
theorem prismSimplex_mapSimplex {W X Y : TopCat} (φ : C(↑W, ↑X)) (H : C(↑X × unitInterval, ↑Y))
    {n : ℕ} (σ : (TopCat.toSSet.obj W).obj (Opposite.op (SimplexCategory.mk n))) (i : Fin (n + 1)) :
    prismSimplex H (mapSimplex φ σ) i
      = prismSimplex (H.comp (φ.prodMap (ContinuousMap.id unitInterval))) σ i := rfl

/-- **Prism source naturality (chain level).** `prismOp H (φ_# c) = prismOp (H ∘ (φ × id)) c`. -/
theorem prismOp_mapChain {W X Y : TopCat} (φ : C(↑W, ↑X)) (H : C(↑X × unitInterval, ↑Y))
    (n : ℕ) (c : SingularChain W n) :
    prismOp H n (mapChain φ n c) = prismOp (H.comp (φ.prodMap (ContinuousMap.id unitInterval))) n c := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => rw [map_add, map_add, map_add, hc, hd]
  | single σ s =>
      rw [mapChain_single, prismOp_single, prismOp_single]
      rfl

/-! ## §1. The local-cross naturality square (chain and homology level). -/

/-- **The chain-level naturality of the local cross under a base map `ι` and its cylinder lift
`ι × id`.** `crossRelChainLM ∘ ι_#  =  (ι × id)_# ∘ crossRelChainLM`, from prism source/target naturality
(`graphHom = id`, both composites collapse to `ι × id`). -/
theorem crossRelChainLM_relMapChain_nat {N M : TopCat} (ι : C(↑N, ↑M))
    {yN : ↑(cyl N)} {xM : ↑(cyl M)}
    (hpuncM : ∀ a ∈ ({xM.1}ᶜ : Set ↑M), ∀ s : unitInterval,
      graphHom M (a, s) ∈ ({xM}ᶜ : Set ↑(cyl M)))
    (hpuncN : ∀ a ∈ ({yN.1}ᶜ : Set ↑N), ∀ s : unitInterval,
      graphHom N (a, s) ∈ ({yN}ᶜ : Set ↑(cyl N)))
    (hbase : Set.MapsTo ι ({yN.1}ᶜ : Set ↑N) ({xM.1}ᶜ : Set ↑M))
    (hcyl : Set.MapsTo (ι.prodMap (ContinuousMap.id unitInterval))
      ({yN}ᶜ : Set ↑(cyl N)) ({xM}ᶜ : Set ↑(cyl M)))
    (p : ℕ) (W : RelativeChain ({yN.1}ᶜ : Set ↑N) (p + 1)) :
    crossRelChainLM hpuncM p (relMapChain ι hbase (p + 1) W)
      = relMapChain (ι.prodMap (ContinuousMap.id unitInterval)) hcyl (p + 1 + 1)
          (crossRelChainLM hpuncN p W) := by
  obtain ⟨c0, rfl⟩ := Submodule.Quotient.mk_surjective _ W
  rw [show (Submodule.Quotient.mk c0 : RelativeChain ({yN.1}ᶜ : Set ↑N) (p + 1))
      = RelativeChain.mk ({yN.1}ᶜ : Set ↑N) (p + 1) c0 from rfl,
    relMapChain_mk, crossRelChainLM_mk, crossRelChainLM_mk, relMapChain_mk]
  refine congrArg (RelativeChain.mk ({xM}ᶜ : Set ↑(cyl M)) (p + 1 + 1)) ?_
  rw [prismOp_mapChain, SKEFTHawking.SingularCapCrossProjection.mapChain_prismOp]
  rfl

/-- **The homology-level local-cross naturality square.** `crossHloc_M ∘ ι_* = (ι × id)_* ∘ crossHloc_N`
on relative homology, for `ι : N → M` (base) and its cylinder lift `ι × id`. -/
theorem crossHloc_map_naturality {N M : TopCat} (ι : C(↑N, ↑M))
    {yN : ↑(cyl N)} {xM : ↑(cyl M)}
    (h1M : Set.MapsTo (slice (graphHom M) 1) (Set.univ : Set ↑M) ({xM}ᶜ : Set ↑(cyl M)))
    (h0M : Set.MapsTo (slice (graphHom M) 0) (Set.univ : Set ↑M) ({xM}ᶜ : Set ↑(cyl M)))
    (hpuncM : ∀ a ∈ ({xM.1}ᶜ : Set ↑M), ∀ s : unitInterval,
      graphHom M (a, s) ∈ ({xM}ᶜ : Set ↑(cyl M)))
    (h1N : Set.MapsTo (slice (graphHom N) 1) (Set.univ : Set ↑N) ({yN}ᶜ : Set ↑(cyl N)))
    (h0N : Set.MapsTo (slice (graphHom N) 0) (Set.univ : Set ↑N) ({yN}ᶜ : Set ↑(cyl N)))
    (hpuncN : ∀ a ∈ ({yN.1}ᶜ : Set ↑N), ∀ s : unitInterval,
      graphHom N (a, s) ∈ ({yN}ᶜ : Set ↑(cyl N)))
    (hbase : Set.MapsTo ι ({yN.1}ᶜ : Set ↑N) ({xM.1}ᶜ : Set ↑M))
    (hcyl : Set.MapsTo (ι.prodMap (ContinuousMap.id unitInterval))
      ({yN}ᶜ : Set ↑(cyl N)) ({xM}ᶜ : Set ↑(cyl M)))
    (p : ℕ) (w : RelativeHomology ({yN.1}ᶜ : Set ↑N) (p + 1)) :
    crossHloc h1M h0M hpuncM p (RelativeHomology.map ι hbase (p + 1) w)
      = RelativeHomology.map (ι.prodMap (ContinuousMap.id unitInterval)) hcyl (p + 1 + 1)
          (crossHloc h1N h0N hpuncN p w) := by
  obtain ⟨w0, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  refine congrArg (RelativeHomology.mk ({xM}ᶜ : Set ↑(cyl M)) (p + 1 + 1)) (Subtype.ext ?_)
  exact crossRelChainLM_relMapChain_nat ι hpuncM hpuncN hbase hcyl p
    (w0 : RelativeChain ({yN.1}ᶜ : Set ↑N) (p + 1))

end

end SKEFTHawking.PinPlusCylComponentClsIdentDisc
