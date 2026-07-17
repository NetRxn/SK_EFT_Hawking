/-
# Phase 5q.H close-out — THE EXPLICIT CO-ADAPTED DISK CHAIN (BLOCK #207): the disk detecting triple
# for an EXPLICIT `cHa`, freed from the anonymous `.choose`.

#204 walled route (a) — the chain-level construction from the disk chain's explicit `S`-face — with
the observation that the canonical detecting chain `diskDetectChain` (#166/#168) is an ANONYMOUS
`.choose` of `exists_detecting_chain_of_hasRelFundClass`, carrying NO named `S`-face subchain: there
is no face to pull back along `φ`. This module INVERTS that wall on the disk side, exactly as the
cylinder side's `crossChain` (#178) is already the explicit controlled representative:

**Detection is a relative-homology invariant** (`SingularRelClassHomologous.relClassOf_eq_of_homologous`).
So an EXPLICIT `cHa` need not BE `diskDetectChain`; it need only be *homologous rel the boundary
sphere* to it — `cHa = diskDetectChain + ∂w + e` with `e` supported on the sphere `{v | ‖v‖ = 1}`.
Any such `cHa` then satisfies BOTH hypotheses `hasClass_ofTransfer` demands of its disk chain:

* **§1 `explicitDiskChain_hc`** — its boundary is supported on the boundary sphere `∂D⁵`
  (`∂cHa = ∂diskDetectChain + ∂e`, both sphere-chains; `∂∂w = 0`).
* **§2 `explicitDiskChain_hdet`** — it detects the local interior generator at every interior point
  (`relClassOf {y}ᶜ 3 cHa = relClassOf {y}ᶜ 3 diskDetectChain ≠ 0`, the sphere-supported perturbation
  `e` dying off `{y}` and the boundary `∂w` being a relative boundary).

The pay-off: the disk detecting triple `{cHa, hcHa, hdetHa}` that `hasClass_ofTransfer` consumes is now
available for an EXPLICIT `cHa` with a *visible* boundary — so its `S`-face can be exposed (a named
`incl_# cSeam + vOut` split), which the anonymous `.choose` could not. This is the disk-side twin of the
cylinder controlled representative, completing the generality `capstoneSeamTransferSeam_ofSharedSeam`
(#204 §2) set up on the disk side but could not previously feed to the consumer (the consumer needed
the disk chain's `hc`/`hdet`, which only `diskDetectChain` supplied).

**What remains** (the honest residual, §3): to actually inhabit the capstone `hasClass`, one must
PRODUCE such an explicit `cHa` whose *visible* boundary splits as `incl_# cSeam + vOut` (`vOut` on the
free sphere `S⁴ ∖ S`) AND is homologous rel-sphere to `diskDetectChain`, with the SAME `cSeam`
serving the cylinder split `z@⊤ = φ_# cSeam + wOut`. The disk-side homology witness is the "class
characterization"; the shared-`cSeam` co-adaptation is the sole geometric residual (#204 §"What
remains"), walling at the CLOSED-`S` support barrier of the current open-cover/subdivision machinery —
NOT kernel-false (it holds for the actual collar of a genuine surgery), a machinery gap. No new
kernel no-go.

**Fences.** Additive module. No collar theorem proved; no completeness Prop minted; the single shared
`cSeam` is never split into independent cylinder/disk bridges. Kernel-pure
(`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no `native_decide`,
no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusTraceCapstoneSeamTransferSupply
import SKEFTHawking.PinPlusTraceSeamChainConstruct
import SKEFTHawking.SingularRelClassHomologous

open scoped Manifold
open SKEFTHawking.BordismTheory
open SKEFTHawking.SurgeryFoundation
open SKEFTHawking.SurgeryFoundation.HandleAttachment
open SKEFTHawking.DiskChartGeneric (D5)
open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularMayerVietoris
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularMayerVietorisLES
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.SingularHomotopyInvariance
open SKEFTHawking.SingularRelativeCoverMV
open SKEFTHawking.SingularRelativeCoverMVTransport
open SKEFTHawking.SingularRelClassHomologous
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassGeom
open SKEFTHawking.PinPlusTraceRelFundReduce
open SKEFTHawking.PinPlusTraceCapstoneInhabit
open SKEFTHawking.PinPlusTraceCapstoneCoverGlue
open SKEFTHawking.PinPlusTraceCapstoneCoverGlueDisk
open SKEFTHawking.PinPlusTraceCapstoneSeamTransfer
open SKEFTHawking.PinPlusTraceCapstoneSeamTransferSupply
open SKEFTHawking.PinPlusTraceDiskCorePair

namespace SKEFTHawking.PinPlusTraceExplicitDiskChain

noncomputable section

/-! ## §1. The explicit disk chain's boundary is supported on the boundary sphere.

We write the boundary sphere `∂D⁵` as the **literal** norm-one locus
`{v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1}` (the verbatim set of `diskDetectChain_hc`), NOT a
reducible abbreviation: a `subspaceChains`-membership defeq against the abbreviation forces
`subspaceChains` to `whnf`-unfold and blows the heartbeat budget, whereas syntactically-identical
literal sets short-circuit. -/

/-- **Boundary support of an explicit, homologous disk chain.** If `cHa = diskDetectChain + ∂w + e`
with the perturbation `e` supported on the boundary sphere, then `∂cHa` is supported on the boundary
sphere too: `∂cHa = ∂diskDetectChain + ∂∂w + ∂e = ∂diskDetectChain + ∂e`, and both `∂diskDetectChain`
(`diskDetectChain_hc`) and `∂e` (boundary of a sphere-chain) are sphere-chains. This is the `hcHa`
hypothesis of `hasClass_ofTransfer`, now available for an EXPLICIT `cHa`. -/
theorem explicitDiskChain_hc
    (cHa : SingularChain (TopCat.of D5) (3 + 2))
    (w : SingularChain (TopCat.of D5) (3 + 3))
    (e : SingularChain (TopCat.of D5) (3 + 2))
    (he : e ∈ subspaceChains (X := TopCat.of D5)
      {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} (3 + 2))
    (hcongr : cHa
      = diskDetectChain + chainBoundary (TopCat.of D5) (3 + 2) w + e) :
    chainBoundary (TopCat.of D5) (3 + 1) cHa
      ∈ subspaceChains (X := TopCat.of D5)
        {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} (3 + 1) := by
  subst hcongr
  rw [map_add, map_add, chainBoundary_chainBoundary_apply, add_zero]
  exact Submodule.add_mem _ diskDetectChain_hc
    (chainBoundary_mem_subspaceChains _ (3 + 1) e he)

/-! ## §2. The explicit disk chain detects every interior generator (homology transport). -/

/-- **Interior detection of an explicit, homologous disk chain.** For every interior point `y`
(`y ∉ ∂D⁵`), `relClassOf {y}ᶜ 3 cHa = relClassOf {y}ᶜ 3 diskDetectChain` by the homologous-perturbation
transfer (`relClassOf_eq_of_homologous`): the boundary `∂w` is a relative boundary and the
sphere-supported `e ⊆ {y}ᶜ` dies. The right side is nonzero (`diskDetectChain_hdet`), so the explicit
`cHa` detects. This is the `hdetHa` hypothesis of `hasClass_ofTransfer`, now available for an EXPLICIT
`cHa`. -/
theorem explicitDiskChain_hdet
    (cHa : SingularChain (TopCat.of D5) (3 + 2))
    (w : SingularChain (TopCat.of D5) (3 + 3))
    (e : SingularChain (TopCat.of D5) (3 + 2))
    (he : e ∈ subspaceChains (X := TopCat.of D5)
      {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} (3 + 2))
    (hcongr : cHa
      = diskDetectChain + chainBoundary (TopCat.of D5) (3 + 2) w + e)
    (y : D5) (hy : y ∉ {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1}) :
    relClassOf (X := TopCat.of D5) ({y}ᶜ) 3 cHa
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hy) (3 + 1)
          (explicitDiskChain_hc cHa w e he hcongr)) ≠ 0 := by
  rw [relClassOf_eq_of_homologous (Set.subset_compl_singleton_iff.mpr hy) 3 hcongr he
      (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hy) (3 + 1)
        (explicitDiskChain_hc cHa w e he hcongr))
      (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hy) (3 + 1) diskDetectChain_hc)]
  exact diskDetectChain_hdet y hy

/-! ## §2.5. The homology witness from a relative-class equality — the geometric form. -/

/-- **The homology witness is exactly `cHa` being a relative fundamental cycle.** If an explicit
almost-cycle `cHa` (boundary on the sphere) has the SAME relative `(D⁵, ∂D⁵)`-class as
`diskDetectChain` — i.e. `cHa` represents the disk's relative fundamental class — then it IS homologous
rel-sphere to `diskDetectChain`: `cHa = diskDetectChain + ∂w + e` with `e` on the sphere. This is the
"class characterization" that discharges the raw existential homology witness (`hcongr`) from a purely
geometric condition on the VISIBLE boundary: `cHa` need only be a relative fundamental cycle of the
disk. (`RelativeHomology.mk_eq_zero_iff`: equal classes differ by a relative boundary, which unfolds
mod 2 to `∂w + e`.) -/
theorem homologyWitness_of_relClass_eq
    (cHa : SingularChain (TopCat.of D5) (3 + 2))
    (hc : chainBoundary (TopCat.of D5) (3 + 1) cHa
      ∈ subspaceChains (X := TopCat.of D5) {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} (3 + 1))
    (hcl : relClassOf (X := TopCat.of D5)
        {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} 3 cHa hc
      = relClassOf (X := TopCat.of D5)
        {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} 3 diskDetectChain diskDetectChain_hc) :
    ∃ (w : SingularChain (TopCat.of D5) (3 + 3)) (e : SingularChain (TopCat.of D5) (3 + 2)),
      e ∈ subspaceChains (X := TopCat.of D5)
          {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} (3 + 2)
        ∧ cHa = diskDetectChain + chainBoundary (TopCat.of D5) (3 + 2) w + e := by
  -- The sum class `[cHa + diskDetectChain]` vanishes (equal classes, char 2).
  have hbdd : chainBoundary (TopCat.of D5) (3 + 1) (cHa + diskDetectChain)
      ∈ subspaceChains (X := TopCat.of D5)
        {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} (3 + 1) := by
    rw [map_add]; exact Submodule.add_mem _ hc diskDetectChain_hc
  have hsum : relClassOf (X := TopCat.of D5)
      {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} 3 (cHa + diskDetectChain) hbdd = 0 := by
    rw [relClassOf_add _ 3 cHa diskDetectChain hc diskDetectChain_hc, hcl]
    exact ZModModule.add_self _
  -- A vanishing class is a relative boundary: extract a relative-chain lift `W = [w]`.
  have hmem := (RelativeHomology.mk_eq_zero_iff _ (3 + 2)
    (relCycleOf (X := TopCat.of D5)
      {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} 3 (cHa + diskDetectChain) hbdd)).mp hsum
  rw [relBoundaries, LinearMap.mem_range] at hmem
  obtain ⟨W, hW⟩ := hmem
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ W
  rw [show (Submodule.Quotient.mk w :
        RelativeChain {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} (3 + 3))
      = RelativeChain.mk _ (3 + 3) w from rfl, relBoundary_mk] at hW
  -- `hW : mk (∂w) = mk (cHa + diskDetectChain)`; its difference is the sphere-supported remainder.
  have hsub := (Submodule.Quotient.eq _).mp hW
  refine ⟨w, chainBoundary (TopCat.of D5) (3 + 2) w + cHa + diskDetectChain, ?_, ?_⟩
  · -- `e = ∂w + cHa + diskDetectChain = ∂w - (cHa + diskDetectChain)` lies in the sphere chains.
    have hrw : chainBoundary (TopCat.of D5) (3 + 2) w + cHa + diskDetectChain
        = chainBoundary (TopCat.of D5) (3 + 2) w - (cHa + diskDetectChain) := by
      rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_right (ZModModule.add_self _)]
      abel
    rw [hrw]; exact hsub
  · -- `cHa = diskDetectChain + ∂w + e` by char-2 cancellation of the doubled terms.
    rw [show diskDetectChain + chainBoundary (TopCat.of D5) (3 + 2) w
          + (chainBoundary (TopCat.of D5) (3 + 2) w + cHa + diskDetectChain)
        = cHa + (diskDetectChain + diskDetectChain)
          + (chainBoundary (TopCat.of D5) (3 + 2) w + chainBoundary (TopCat.of D5) (3 + 2) w)
        from by abel, ZModModule.add_self, ZModModule.add_self, add_zero, add_zero]

/-! ## §3. The explicit-`cHa` capstone residual — the disk chain is now EXPLICIT with a visible face. -/

section Residual

variable (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
  [CompactSpace s.M] [Nonempty s.M] [PreconnectedSpace s.M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M]
  (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
  (hφ : Continuous φ) (hφinj : Function.Injective φ)
  (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
  (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
  (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)

/-- **The narrowed capstone residual, EXPLICIT-`cHa` form.** As `CapstoneSeamTransferResidual` (#184)
but with the disk chain freed from the anonymous `diskDetectChain`: an EXPLICIT `cHa` together with a
homology witness `cHa = diskDetectChain + ∂w + e` (`e` on the boundary sphere), so its detecting
triple `{hc, hdet}` is supplied by `explicitDiskChain_hc`/`explicitDiskChain_hdet` (§1/§2). The shared
seam core `seam` now runs over the EXPLICIT `cHa`, so the disk-boundary split `∂cHa = incl_# cSeam +
vOut` (its `hsplitHa`) is a split of an EXPLICIT, computable boundary — a *nameable* `S`-face, which
the anonymous `.choose` could not expose (#204 route (a) wall). This is the disk-side twin of the
cylinder controlled representative `crossChain` (#178). -/
structure CapstoneSeamTransferResidualExplicit where
  /-- a fundamental cycle of the closed source 4-manifold `M`. -/
  z : cycles (TopCat.of s.M) (2 + 2)
  /-- `z` represents the fundamental class. -/
  hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := s.M)
      = Homology.mk (TopCat.of s.M) (2 + 2) z
  /-- the EXPLICIT disk chain (typed at `D⁵ ≡ .Ha`). -/
  cHa : SingularChain (TopCat.of D5) (3 + 2)
  /-- the homology-witness chain (degree `3+3`). -/
  w : SingularChain (TopCat.of D5) (3 + 3)
  /-- the sphere-supported perturbation. -/
  e : SingularChain (TopCat.of D5) (3 + 2)
  /-- the perturbation is supported on the boundary sphere `∂D⁵`. -/
  he : e ∈ subspaceChains (X := TopCat.of D5)
    {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} (3 + 2)
  /-- the homology witness: `cHa` is homologous rel-sphere to `diskDetectChain`. -/
  hcongr : cHa = diskDetectChain + chainBoundary (TopCat.of D5) (3 + 2) w + e
  /-- the `htransfer`-free shared seam core over the EXPLICIT `cHa` (its `hsplitHa` is the visible
  `S`-face split `∂cHa = incl_# cSeam + vOut`). -/
  seam : CapstoneSeamTransferSeam s S hS φ hφ hφinj z cHa
  /-- the overlap-zone straddle detection over the glued (controlled cylinder ⊕ EXPLICIT disk) chain. -/
  hdetAB : ∀ (x : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
      (hx : x ∉ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)),
      x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl →
      x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle →
    relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) ({x}ᶜ) 3
      (closedEmbeddingChain
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
          (3 + 2) (capstoneCylChainT s S hS φ hφ hφinj z)
        + closedEmbeddingChain
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
          (3 + 2) cHa)
      (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hx) (3 + 1)
        (hbd_ofTransfer s t S hS φ hφ hφinj cd hseam d
          (CapstoneSeamTransferSeam.toTransfer s S hS φ hφ hφinj seam))) ≠ 0

/-- **The explicit-`cHa` residual fires the capstone `hasClass`.** Feeds `hasClass_ofTransfer` the
EXPLICIT disk chain `R.cHa` with its transported detecting triple (`explicitDiskChain_hc`/`_hdet`),
the transfer datum `R.seam.toTransfer` (its `htransfer` discharged, #184 §2), and the straddle
detection. So the deepest capstone atom reduces, for connected `s.M`, to inhabiting
`CapstoneSeamTransferResidualExplicit` — `{a fundamental cycle of M, an EXPLICIT disk chain homologous
rel-sphere to diskDetectChain with a VISIBLE `S`-face split, the shared seam, the straddle
detection}` — with the disk chain no longer an anonymous `.choose`. -/
def CapstoneSeamTransferResidualExplicit.toHasClass
    (R : CapstoneSeamTransferResidualExplicit s t S hS φ hφ hφinj cd hseam d) :
    letI := capstone_t1Space s t S hS φ hφ hφinj cd hseam d
    HasRelFundClass (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (interiorGenFamily (W := (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        ((𝓡 4).prod (𝓡∂ 1)) εtrace) :=
  hasClass_ofTransfer s t S hS φ hφ hφinj cd hseam d R.z R.hz
    R.cHa (explicitDiskChain_hc R.cHa R.w R.e R.he R.hcongr)
    (fun y hy => explicitDiskChain_hdet R.cHa R.w R.e R.he R.hcongr y hy)
    (CapstoneSeamTransferSeam.toTransfer s S hS φ hφ hφinj R.seam)
    R.hdetAB

/-! ## §4. The class-form residual — the disk condition is "`cHa` is a relative fundamental cycle". -/

/-- **The narrowed capstone residual, relative-class form.** The geometric-cleanest packaging: the raw
existential homology witness (`w`/`e`/`he`/`hcongr`) is replaced by the single condition that the
EXPLICIT disk chain `cHa` represents the disk's relative fundamental class — `relClassOf cHa =
relClassOf diskDetectChain` — a statement purely about `cHa`'s VISIBLE boundary
(`homologyWitness_of_relClass_eq` supplies the witness). So the disk side asks exactly: an explicit
`cHa` that (i) is a relative fundamental cycle of `(D⁵, ∂D⁵)` and (ii) carries the shared seam's
visible `S`-face split `∂cHa = incl_# cSeam + vOut`. -/
structure CapstoneSeamTransferResidualExplicitClass where
  /-- a fundamental cycle of the closed source 4-manifold `M`. -/
  z : cycles (TopCat.of s.M) (2 + 2)
  /-- `z` represents the fundamental class. -/
  hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := s.M)
      = Homology.mk (TopCat.of s.M) (2 + 2) z
  /-- the EXPLICIT disk chain (typed at `D⁵ ≡ .Ha`). -/
  cHa : SingularChain (TopCat.of D5) (3 + 2)
  /-- its boundary is supported on the boundary sphere `∂D⁵`. -/
  hc : chainBoundary (TopCat.of D5) (3 + 1) cHa
    ∈ subspaceChains (X := TopCat.of D5) {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} (3 + 1)
  /-- **the geometric disk condition**: `cHa` represents the disk's relative fundamental class. -/
  hcl : relClassOf (X := TopCat.of D5)
      {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} 3 cHa hc
    = relClassOf (X := TopCat.of D5)
      {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} 3 diskDetectChain diskDetectChain_hc
  /-- the `htransfer`-free shared seam core over the EXPLICIT `cHa` (its `hsplitHa` is the visible
  `S`-face split `∂cHa = incl_# cSeam + vOut`). -/
  seam : CapstoneSeamTransferSeam s S hS φ hφ hφinj z cHa
  /-- the overlap-zone straddle detection over the glued (controlled cylinder ⊕ EXPLICIT disk) chain. -/
  hdetAB : ∀ (x : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
      (hx : x ∉ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)),
      x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl →
      x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle →
    relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) ({x}ᶜ) 3
      (closedEmbeddingChain
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
          (3 + 2) (capstoneCylChainT s S hS φ hφ hφinj z)
        + closedEmbeddingChain
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
          (3 + 2) cHa)
      (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hx) (3 + 1)
        (hbd_ofTransfer s t S hS φ hφ hφinj cd hseam d
          (CapstoneSeamTransferSeam.toTransfer s S hS φ hφ hφinj seam))) ≠ 0

/-- **The class-form residual fires the capstone `hasClass`.** Discharges the homology witness from the
relative-class equality (`homologyWitness_of_relClass_eq`) and delegates to the explicit-`cHa` supplier.
So the deepest capstone atom reduces, for connected `s.M`, to inhabiting
`CapstoneSeamTransferResidualExplicitClass` — `{a fundamental cycle of M, an explicit disk chain that IS
a relative fundamental cycle of the disk carrying the shared seam's visible `S`-face split, the straddle
detection}`. The remaining GEOMETRIC residual is the shared `cSeam` serving BOTH the disk split (in
`seam`) and the cylinder split simultaneously — the co-adaptation to the attaching map `φ`, which walls
at the CLOSED-`S` support barrier (a machinery gap, not kernel-false; #204). -/
def CapstoneSeamTransferResidualExplicitClass.toHasClass
    (R : CapstoneSeamTransferResidualExplicitClass s t S hS φ hφ hφinj cd hseam d) :
    letI := capstone_t1Space s t S hS φ hφ hφinj cd hseam d
    HasRelFundClass (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (interiorGenFamily (W := (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        ((𝓡 4).prod (𝓡∂ 1)) εtrace) := by
  obtain ⟨w, e, he, hcongr⟩ := homologyWitness_of_relClass_eq R.cHa R.hc R.hcl
  exact hasClass_ofTransfer s t S hS φ hφ hφinj cd hseam d R.z R.hz
    R.cHa (explicitDiskChain_hc R.cHa w e he hcongr)
    (fun y hy => explicitDiskChain_hdet R.cHa w e he hcongr y hy)
    (CapstoneSeamTransferSeam.toTransfer s S hS φ hφ hφinj R.seam)
    R.hdetAB

end Residual

end

end SKEFTHawking.PinPlusTraceExplicitDiskChain
