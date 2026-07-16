import Mathlib
import SKEFTHawking.SingularSurgeryCoreDetect
import SKEFTHawking.SingularRelativeCoverMVSeam

/-!
# Phase 5q.H close-out — THE SEAM DATUM ON THE TWO-CORE CARRIER (hbd + hdetAB, discharged from a collar chain)

The two-core assembly (`SingularSurgeryCoreDetect.hasRelFundClass_of_coreChains`) reduces the
handle-attachment carrier's `[W,∂W]` witness to two piece chains plus the two collar-chain residuals
`hbd`/`hdetAB` on the pushed sum. This module discharges BOTH from a single **seam
collar-decomposition datum** (`SingularRelativeCoverMVSeam.SeamCollarChainDatum`) instantiated at the
carrier with the canonical cores (`range fromCyl`/`range fromHandle`) and the two pushed piece chains
`closedEmbeddingChain fromCyl cCyl`, `closedEmbeddingChain fromHandle cHa`.

The datum names the honest geometric content once — the collar product chain `p` (the seam collar's
`S_att`-side chain × the interval, supplied by the `SeamCollarDatum` by construction), the away-error
`e`, the chain-level seam agreement `push cCyl + push cHa = p + e`, the boundary-in-`∂W` facts, and
the collar chain's overlap detection — and this module fires
`SeamCollarChainDatum.hbd`/`.hdetAB` into the two-core assembly. `hasRelFundClass_of_coreChains_ofSeam`
is the full carrier-level supplier: the two one-sided detections DISCHARGED (from the piece engines,
via §1 of `SingularSurgeryCoreDetect`) and the two collar-chain residuals DISCHARGED (from the seam
datum). The only genuinely-geometric residuals left are the seam datum's own concrete-chain fields —
never a completeness Prop, never detection at a closed piece's frontier.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/

open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularMayerVietoris
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.SingularRelativeCoverMV
open SKEFTHawking.SingularRelativeCoverMVTransport
open SKEFTHawking.SingularRelativeCoverMVSeam
open SKEFTHawking.SurgeryFoundation

namespace SKEFTHawking.SingularSurgeryCoreDetect

variable (HA : HandleAttachment.{0, 0})

/-- **The seam collar-decomposition datum on the two-core carrier**, abbreviating the instantiation
of `SeamCollarChainDatum` at the canonical cores (`range fromCyl`/`range fromHandle`) and the two
pushed piece chains. Its fields are the honest seam residuals: the collar product chain, the
away-error, the chain-level seam agreement, the boundary-in-`T` facts, and the overlap detection. -/
abbrev CoreSeamDatum (T : Set HA.carrier) (m : ℕ)
    (cCyl : SingularChain (TopCat.of HA.B) (m + 2))
    (cHa : SingularChain (TopCat.of HA.Ha) (m + 2)) : Type :=
  SeamCollarChainDatum (X := TopCat.of HA.carrier) T
    (Set.range HA.fromCyl) (Set.range HA.fromHandle) m
    (closedEmbeddingChain HA.isClosedEmbedding_fromCyl.isEmbedding (m + 2) cCyl)
    (closedEmbeddingChain HA.isClosedEmbedding_fromHandle.isEmbedding (m + 2) cHa)

/-- **The seam-cancellation `hbd`, discharged from the seam datum.** Exactly the `hbd` argument of
`hasRelFundClass_of_coreChains` — the boundary of the pushed sum lands in `T`. -/
theorem coreChains_hbd_of_seam {T : Set HA.carrier} {m : ℕ}
    {cCyl : SingularChain (TopCat.of HA.B) (m + 2)}
    {cHa : SingularChain (TopCat.of HA.Ha) (m + 2)}
    (D : CoreSeamDatum HA T m cCyl cHa) :
    chainBoundary (TopCat.of HA.carrier) (m + 1)
        (closedEmbeddingChain HA.isClosedEmbedding_fromCyl.isEmbedding (m + 2) cCyl
          + closedEmbeddingChain HA.isClosedEmbedding_fromHandle.isEmbedding (m + 2) cHa)
      ∈ subspaceChains (X := TopCat.of HA.carrier) T (m + 1) :=
  D.hbd

/-- **The overlap straddle detection `hdetAB`, discharged from the seam datum.** Exactly the
`hdetAB` argument of `hasRelFundClass_of_coreChains` (keyed on the same `hbd = D.hbd`). -/
theorem coreChains_hdetAB_of_seam {T : Set HA.carrier} {m : ℕ}
    {cCyl : SingularChain (TopCat.of HA.B) (m + 2)}
    {cHa : SingularChain (TopCat.of HA.Ha) (m + 2)}
    (D : CoreSeamDatum HA T m cCyl cHa)
    (x : HA.carrier) (hx : x ∉ T)
    (hxA : x ∈ Set.range HA.fromCyl) (hxB : x ∈ Set.range HA.fromHandle) :
    relClassOf (X := TopCat.of HA.carrier) ({x}ᶜ) m
        (closedEmbeddingChain HA.isClosedEmbedding_fromCyl.isEmbedding (m + 2) cCyl
          + closedEmbeddingChain HA.isClosedEmbedding_fromHandle.isEmbedding (m + 2) cHa)
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hx) (m + 1)
          (coreChains_hbd_of_seam HA D)) ≠ 0 :=
  D.hdetAB x hx hxA hxB

/-- **The two-core glued `HasRelFundClass`, with the two collar-chain residuals discharged from a
seam datum.** The full carrier-level supplier: the two one-sided detections discharged from the
piece engines (`hcCyl`/`hdetCyl`, `hcHa`/`hdetHa`) and the two boundary-absorb facts, plus the two
collar-chain residuals `hbd`/`hdetAB` discharged from the seam collar-decomposition datum `D`. The
residual geometric atoms are exactly {the two piece chains + supports + detections, the two absorbs,
the seam datum's own concrete-chain fields}. -/
theorem hasRelFundClass_of_coreChains_ofSeam (T : Set HA.carrier) (m : ℕ)
    (gen : ∀ x : HA.carrier, x ∉ T → (RelativeHomology (X := TopCat.of HA.carrier) ({x}ᶜ) (m + 2)
      ≃ₗ[ZMod 2] ZMod 2))
    (cCyl : SingularChain (TopCat.of HA.B) (m + 2))
    (cHa : SingularChain (TopCat.of HA.Ha) (m + 2))
    (D : CoreSeamDatum HA T m cCyl cHa)
    {BdB : Set HA.B} (habsorbB : ∀ y ∈ BdB, HA.fromCyl y ∈ T ∪ Set.range HA.fromHandle)
    (hcCyl : chainBoundary (TopCat.of HA.B) (m + 1) cCyl
      ∈ subspaceChains (X := TopCat.of HA.B) BdB (m + 1))
    (hdetCyl : ∀ (y : HA.B) (hy : y ∉ BdB),
      relClassOf (X := TopCat.of HA.B) ({y}ᶜ) m cCyl
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hy) (m + 1) hcCyl) ≠ 0)
    {BdHa : Set HA.Ha} (habsorbHa : ∀ y ∈ BdHa, HA.fromHandle y ∈ T ∪ Set.range HA.fromCyl)
    (hcHa : chainBoundary (TopCat.of HA.Ha) (m + 1) cHa
      ∈ subspaceChains (X := TopCat.of HA.Ha) BdHa (m + 1))
    (hdetHa : ∀ (y : HA.Ha) (hy : y ∉ BdHa),
      relClassOf (X := TopCat.of HA.Ha) ({y}ᶜ) m cHa
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hy) (m + 1) hcHa) ≠ 0) :
    HasRelFundClass (X := TopCat.of HA.carrier) T gen :=
  hasRelFundClass_of_coreChains HA T m gen cCyl cHa (coreChains_hbd_of_seam HA D)
    habsorbB hcCyl hdetCyl habsorbHa hcHa hdetHa
    (fun x hx hxA hxB => coreChains_hdetAB_of_seam HA D x hx hxA hxB)

end SKEFTHawking.SingularSurgeryCoreDetect
