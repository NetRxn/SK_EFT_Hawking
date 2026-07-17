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
open SKEFTHawking.SingularRelClassHomologous
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

end

end SKEFTHawking.PinPlusTraceExplicitDiskChain
