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

/-! ## §2. Per-point detection for disconnected `M` — the crossHloc obligation transported
per component. -/

/-- **The per-point local-cross detection, disconnected.** At every interior point `x = (σ, t)` of the
cylinder over a possibly-disconnected closed charted `M`, the local cross of `M`'s local fundamental
class is nonzero — the connectedness-free version of the connected
`crossHloc_ne_zero_of_alphaU_ne_zero`. Detected on the clopen connected component `C = connectedComponent σ`
(where the connected engine fires), transported back to `M` through the open embedding `↥C ↪ M` and its
cylinder lift (`crossHloc_map_naturality`, `mLocalClass` naturality, open-embedding injectivity). -/
theorem crossHloc_mLocalClass_ne_zero {m' : ℕ}
    {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m' + 2))) M]
    (x : ↑(TopCat.of (cylW M))) (hx : x ∉ (cylModel m').boundary (cylW M))
    (z : cycles (TopCat.of M) (m' + 2))
    (hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := m') (M := M)
      = Homology.mk (TopCat.of M) (m' + 2) z) :
    crossHloc (M := TopCat.of M) (interior_slice_one x hx) (interior_slice_zero x hx)
        (interior_punc x) (m' + 1) (mLocalClass x z) ≠ 0 := by
  -- the clopen connected component of the base point
  haveI : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin (m' + 2))) M
  haveI : T1Space (↑(cyl (TopCat.of M))) := inferInstance
  set σ : M := x.1 with hσ
  set C : Set M := connectedComponent σ with hCdef
  have hCclopen : IsClopen C := ⟨isClosed_connectedComponent, isOpen_connectedComponent⟩
  haveI : Nonempty ↥C := ⟨⟨σ, mem_connectedComponent⟩⟩
  haveI : PreconnectedSpace ↥C :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_connectedComponent
  letI : ChartedSpace (EuclideanSpace ℝ (Fin (m' + 2))) ↥C :=
    TopologicalSpace.Opens.instChartedSpace ⟨C, hCclopen.isOpen⟩
  haveI : CompactSpace ↥C := isCompact_iff_compactSpace.mp hCclopen.isClosed.isCompact
  haveI : T2Space ↥C := inferInstance
  haveI : T1Space (cylW ↥C) := inferInstance
  -- the inclusion `↥C ↪ M` and its cylinder lift, as open embeddings
  set ιC : C(↑(TopCat.of ↥C), ↑(TopCat.of M)) := ⟨Subtype.val, continuous_subtype_val⟩ with hιC
  have hιC_open : Topology.IsOpenEmbedding (⇑ιC) := hCclopen.isOpen.isOpenEmbedding_subtypeVal
  have hcylMap_open :
      Topology.IsOpenEmbedding (⇑(ιC.prodMap (ContinuousMap.id unitInterval))) :=
    hιC_open.prodMap Topology.IsOpenEmbedding.id
  -- the corresponding interior point of `cylW ↥C`
  set σC : ↥C := ⟨σ, mem_connectedComponent⟩ with hσC
  set yN : ↑(cyl (TopCat.of ↥C)) := (σC, x.2) with hyN
  have hy : yN ∉ (cylModel m').boundary (cylW ↥C) := by
    rw [SKEFTHawking.PinPlusCylComponentExcisionBridge.mem_cylBoundary_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact interior_snd_ne x hx
  have hxyN : (ιC.prodMap (ContinuousMap.id unitInterval)) yN = x := rfl
  -- base and cylinder pushforward domains
  have hbase : Set.MapsTo (⇑ιC) ({yN.1}ᶜ : Set ↑(TopCat.of ↥C)) ({x.1}ᶜ : Set ↑(TopCat.of M)) := by
    intro a ha hcon
    exact ha (Set.mem_singleton_iff.mpr (Subtype.ext (Set.mem_singleton_iff.mp hcon)))
  have hcyl : Set.MapsTo (⇑(ιC.prodMap (ContinuousMap.id unitInterval)))
      ({yN}ᶜ : Set ↑(cyl (TopCat.of ↥C))) ({x}ᶜ : Set ↑(cyl (TopCat.of M))) := by
    intro a ha hcon
    refine ha (Set.mem_singleton_iff.mpr (hcylMap_open.injective ?_))
    rw [hxyN]; exact Set.mem_singleton_iff.mp hcon
  -- the component's fundamental cycle rep
  obtain ⟨zC, hzC0⟩ := Submodule.Quotient.mk_surjective _
    (SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := m') (M := ↥C))
  have hzC : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := m') (M := ↥C)
      = Homology.mk (TopCat.of ↥C) (m' + 2) zC := hzC0.symm
  -- Step 2 — mLocalClass naturality: `[M]|_σ = ιC_*([C]|_σ)`
  have hStep2 : mLocalClass x z
      = RelativeHomology.map ιC hbase (m' + 2) (mLocalClass yN zC) := by
    rw [mLocalClass_eq x z hz, mLocalClass_eq yN zC hzC,
      ← restrictHomologyToPoint_naturality ιC yN.1 hbase (m' + 2)
        (SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := m') (M := ↥C)),
      restrict_map_fundClass_openEmbedding ιC hιC_open yN.1,
      SKEFTHawking.SingularFundamentalClass.fundamentalClass_restricts (m := m') (M := M) σ]
    rfl
  -- Step 1 + injectivity + connected nonvanishing
  rw [hStep2, crossHloc_map_naturality ιC (interior_slice_one x hx) (interior_slice_zero x hx)
    (interior_punc x) (interior_slice_one yN hy) (interior_slice_zero yN hy) (interior_punc yN)
    hbase hcyl (m' + 1) (mLocalClass yN zC)]
  have hcyl' : Set.MapsTo (⇑(ιC.prodMap (ContinuousMap.id unitInterval)))
      ({yN}ᶜ : Set ↑(cyl (TopCat.of ↥C)))
      ({(ιC.prodMap (ContinuousMap.id unitInterval)) yN}ᶜ : Set ↑(cyl (TopCat.of M))) := hcyl
  have hinj := relPointMap_injective_of_isOpenEmbedding
    (X := cyl (TopCat.of ↥C)) (Y := cyl (TopCat.of M))
    (ιC.prodMap (ContinuousMap.id unitInterval)) hcylMap_open yN (m' + 1) hcyl'
  have hcross_ne : crossHloc (M := TopCat.of ↥C) (interior_slice_one yN hy)
      (interior_slice_zero yN hy) (interior_punc yN) (m' + 1) (mLocalClass yN zC) ≠ 0 :=
    crossHloc_ne_zero_of_alphaU_ne_zero yN hy zC hzC (alphaU_ne_zero yN hy zC hzC)
  exact fun hcontra => hcross_ne (hinj (hcontra.trans (map_zero _).symm))

/-! ## §3. The disconnected candidate-restriction and the per-carrier class identity `hcls`. -/

/-- **The explicit cross candidate restricts to the interior generator, DISCONNECTED.** The
connectedness-free twin of `…CylinderClsIdent.cylFundClassCandidate_restricts`: at every interior point
the candidate's boundary restriction is the local cross of `M`'s local fundamental class
(`restrictBd_candidate_eq_crossHloc`), nonzero by the per-component transport `crossHloc_mLocalClass_ne_zero`
(NOT the connected `crossHloc_ne_zero_of_alphaU_ne_zero`, whose flank-injectivity route is false for
disconnected `M`). -/
theorem cylFundClassCandidate_restricts_disc {m' : ℕ}
    {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m' + 2))) M] [T1Space (cylW M)] :
    RestrictsToRelGen (X := TopCat.of (cylW M)) (m := m' + 1)
      ((cylModel m').boundary (cylW M)) (cylGen (M := M) (m' := m'))
      (cylFundClassCandidate (M := M) (m' := m')) := by
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _
    (SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := m') (M := M))
  refine restrictsToRelGen_candidate_of_ne_zero (fun x hx => ?_)
  rw [restrictBd_candidate_eq_crossHloc x hx z hz.symm]
  exact crossHloc_mLocalClass_ne_zero x hx z hz.symm

/-- **THE hcls IDENTITY (disconnected).** The `Classical.choose`-hidden k-component disconnected datum
class `discD.cls` EQUALS the explicit product candidate `cylFundClassCandidate = crossH [M] = [M] × [I,∂I]`,
for a possibly-disconnected closed charted 4-manifold. Both restrict to the cylinder interior generator
`cylGen` everywhere (the datum by its `.restricts` field — the k-component excision assembly; the candidate
by `cylFundClassCandidate_restricts_disc`); the relative fundamental class is unique given the closed
interior determinedness `cylinder_hdet` (`cylinderRelFundClass_unique_of_slab`, connectedness-free). This
is the disconnected twin of `cylinderDatum_cls_eq_crossH`, holding for ALL closed charted `M`. -/
theorem disc_cls_eq_crossH {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M] [T1Space (cylW M)] :
    (SKEFTHawking.PinPlusCylComponentDisconnectedCoreND.discD (M := M)).cls
      = cylFundClassCandidate (M := M) (m' := 2) :=
  cylinderRelFundClass_unique_of_slab (cylGen (M := M) (m' := 2))
    SKEFTHawking.PinPlusCylinderWAdmPinned.cylinder_hdet
    (SKEFTHawking.PinPlusCylComponentDisconnectedCoreND.discD (M := M)).restricts
    cylFundClassCandidate_restricts_disc

end

/-! ## §4. THE ZERO-HYPOTHESIS PROVIDER. -/

/-- **THE ZERO-HYPOTHESIS CHAR-PAIR `W`-PROVIDER.** The entire char-pair `W`-provider inhabitation, with
NO hypotheses beyond the carrier's standing instances: the last provider hypothesis — the per-carrier
disconnected class identity `hcls : discD.cls = crossH [M]` — is discharged unconditionally by
`disc_cls_eq_crossH` (per-component crossHloc transport). Specializes
`PinPlusCylComponentDisconnectedCoreNDDelta.nonempty_provider_of_disconnectedClsIdent`. -/
theorem nonempty_charPairWProviderPerOp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {k : WithTop ℕ∞} {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless] :
    Nonempty (SKEFTHawking.PinPlusCharPairBorTethered.CharPairWProviderPerOp I k) :=
  SKEFTHawking.PinPlusCylComponentDisconnectedCoreNDDelta.nonempty_provider_of_disconnectedClsIdent
    (fun {_s} _σ _ _ _ _hpc => disc_cls_eq_crossH)

end SKEFTHawking.PinPlusCylComponentClsIdentDisc
