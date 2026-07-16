import Mathlib
import SKEFTHawking.SingularSurgeryFoundation
import SKEFTHawking.SingularRelativeCoverMVTransport

/-!
# Phase 5q.H — THE TWO CORE-DETECTION SUPPLIERS on a handle-attachment carrier

The relative cover-MV glue's one-sided detection fields, discharged on the surgery-trace carrier
`W = B ⊔_φ Ha` from PIECE-INTRINSIC data. The two structure maps `fromCyl`/`fromHandle` are closed
embeddings whose ranges cover `W` (`SingularSurgeryFoundation`), so the closed-embedding
piece-detection keystone (`SingularRelativeCoverMVTransport`) instantiates verbatim on BOTH cores:

* `cylCore_relClassOf_ne_zero` — a cylinder-side chain (boundary supported in a set `Bd ⊆ B` whose
  carrier image is absorbed by `T ∪ range fromHandle`) with intrinsic detection off `Bd` pushes to
  an ambient chain detecting at every point off `T` and off the handle core — the glue's `hdetA`;
* `handleCore_relClassOf_ne_zero` — symmetric, the glue's `hdetB`;
* `chainBoundary_closedEmbeddingChain_mem_compl` — the pushed chain's boundary avoids every such
  point (the almost-cycle certificate the detection statements are typed by).

The intended feeds: `Bd` = the cylinder's manifold boundary `M × {⊥,⊤}` with the intrinsic
detection from the cylinder engine's class through a representative chain
(`exists_relClassOf_rep` + `relClassOf_rep_ne_zero_of_restrictsToRelGen`), and `Bd` = the disk's
boundary sphere region on the `D⁵` handle. The absorb hypotheses are per-instantiation boundary
bookkeeping (`∂W` plus the seam absorb the piece boundaries), honest geometric inputs derived from
the `SurgeredEndDatum`'s boundary decomposition. Kernel-pure
(`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new axiom, no `native_decide`, no
`maxHeartbeats`.
-/

open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularMayerVietoris
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.SingularRelativeCoverMV
open SKEFTHawking.SingularRelativeCoverMVTransport
open SKEFTHawking.SurgeryFoundation

namespace SKEFTHawking.SingularSurgeryCoreDetect

/-! ## §0. Generic: the pushed boundary avoids points off the absorbing set -/

/-- **The pushed chain is an almost-cycle at every point off the absorbing set**: if the ambient
absorbs the piece's boundary set into `T ∪ COther`, the pushed chain's boundary is supported away
from any `x ∉ T`, `x ∉ COther`. The almost-cycle certificate for the core detections. -/
theorem chainBoundary_closedEmbeddingChain_mem_compl {P : Type} [TopologicalSpace P] {Wc : Type}
    [TopologicalSpace Wc] {j : P → Wc} (hj : Topology.IsEmbedding j)
    {Bd : Set P} {T COther : Set Wc} (habsorb : ∀ y ∈ Bd, j y ∈ T ∪ COther) (m : ℕ)
    (c : SingularChain (TopCat.of P) (m + 2))
    (hc : chainBoundary (TopCat.of P) (m + 1) c ∈ subspaceChains (X := TopCat.of P) Bd (m + 1))
    {x : Wc} (hxT : x ∉ T) (hxO : x ∉ COther) :
    chainBoundary (TopCat.of Wc) (m + 1) (closedEmbeddingChain hj (m + 2) c)
      ∈ subspaceChains (X := TopCat.of Wc) ({x}ᶜ) (m + 1) := by
  refine subspaceChains_mono (X := TopCat.of Wc) (fun w hw => ?_) (m + 1)
    (chainBoundary_closedEmbeddingChain_mem hj m c hc)
  obtain ⟨y, hy, rfl⟩ := hw
  intro hwx
  rw [Set.mem_singleton_iff] at hwx
  exact (habsorb y hy).elim (fun h => hxT (hwx ▸ h)) (fun h => hxO (hwx ▸ h))

/-! ## §1. The two core-detection suppliers on the handle-attachment carrier -/

variable (HA : HandleAttachment.{0, 0})

/-- **The two cores cover the carrier**, pointwise form (from the opener's range-union fact). -/
theorem mem_range_fromCyl_or_fromHandle (w : HA.carrier) :
    w ∈ Set.range HA.fromCyl ∨ w ∈ Set.range HA.fromHandle := by
  have hw : w ∈ Set.range HA.fromCyl ∪ Set.range HA.fromHandle := by
    rw [HA.range_fromCyl_union_range_fromHandle]
    exact Set.mem_univ w
  exact hw

/-- **The cylinder-core detection supplier** — the glue's `hdetA` on the surgery-trace carrier. A
cylinder-side chain with boundary supported in `Bd ⊆ B` (carrier image absorbed by
`T ∪ range fromHandle`) and intrinsic detection off `Bd` pushes along the closed embedding
`fromCyl` to an ambient chain whose local class is nonzero at every `x ∉ T` off the handle core. -/
theorem cylCore_relClassOf_ne_zero {Bd : Set HA.B} {T : Set HA.carrier}
    (habsorb : ∀ y ∈ Bd, HA.fromCyl y ∈ T ∪ Set.range HA.fromHandle) (m : ℕ)
    (c : SingularChain (TopCat.of HA.B) (m + 2))
    (hc : chainBoundary (TopCat.of HA.B) (m + 1) c
      ∈ subspaceChains (X := TopCat.of HA.B) Bd (m + 1))
    (hdet : ∀ (y : HA.B) (hy : y ∉ Bd),
      relClassOf (X := TopCat.of HA.B) ({y}ᶜ) m c
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hy) (m + 1) hc) ≠ 0)
    {x : HA.carrier} (hxT : x ∉ T) (hxO : x ∉ Set.range HA.fromHandle)
    (hbd : chainBoundary (TopCat.of HA.carrier) (m + 1)
        (closedEmbeddingChain HA.isClosedEmbedding_fromCyl.isEmbedding (m + 2) c)
      ∈ subspaceChains (X := TopCat.of HA.carrier) ({x}ᶜ) (m + 1)) :
    relClassOf (X := TopCat.of HA.carrier) ({x}ᶜ) m
      (closedEmbeddingChain HA.isClosedEmbedding_fromCyl.isEmbedding (m + 2) c) hbd ≠ 0 :=
  closedEmbeddingChain_relClassOf_ne_zero HA.isClosedEmbedding_fromCyl
    HA.isClosedEmbedding_fromHandle.isClosed_range
    (mem_range_fromCyl_or_fromHandle HA) habsorb m c hc hdet hxT hxO hbd

/-- **The handle-core detection supplier** — the glue's `hdetB` on the surgery-trace carrier,
symmetric to the cylinder side (piece = `Ha` along `fromHandle`, other core = `range fromCyl`). -/
theorem handleCore_relClassOf_ne_zero {Bd : Set HA.Ha} {T : Set HA.carrier}
    (habsorb : ∀ y ∈ Bd, HA.fromHandle y ∈ T ∪ Set.range HA.fromCyl) (m : ℕ)
    (c : SingularChain (TopCat.of HA.Ha) (m + 2))
    (hc : chainBoundary (TopCat.of HA.Ha) (m + 1) c
      ∈ subspaceChains (X := TopCat.of HA.Ha) Bd (m + 1))
    (hdet : ∀ (y : HA.Ha) (hy : y ∉ Bd),
      relClassOf (X := TopCat.of HA.Ha) ({y}ᶜ) m c
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hy) (m + 1) hc) ≠ 0)
    {x : HA.carrier} (hxT : x ∉ T) (hxO : x ∉ Set.range HA.fromCyl)
    (hbd : chainBoundary (TopCat.of HA.carrier) (m + 1)
        (closedEmbeddingChain HA.isClosedEmbedding_fromHandle.isEmbedding (m + 2) c)
      ∈ subspaceChains (X := TopCat.of HA.carrier) ({x}ᶜ) (m + 1)) :
    relClassOf (X := TopCat.of HA.carrier) ({x}ᶜ) m
      (closedEmbeddingChain HA.isClosedEmbedding_fromHandle.isEmbedding (m + 2) c) hbd ≠ 0 :=
  closedEmbeddingChain_relClassOf_ne_zero HA.isClosedEmbedding_fromHandle
    HA.isClosedEmbedding_fromCyl.isClosed_range
    (fun w => (mem_range_fromCyl_or_fromHandle HA w).symm) habsorb m c hc hdet hxT hxO hbd

/-! ## §2. The two-core glue datum on the handle-attachment carrier -/

/-- **The two-core glue datum** — the relative cover-MV glue datum on the surgery-trace carrier
with the CANONICAL cores (`range fromCyl`/`range fromHandle`: closed, covering — the constructed
carrier's own decomposition, THE COLLAR FORK respected) and the two piece chains pushed along the
core embeddings. The only genuinely-geometric input at this level is the mod-2 seam-cancellation
`hbd` of the pushed sum — the chain-level "agreement on the overlap". -/
noncomputable def coreGlueData (T : Set HA.carrier) (m : ℕ)
    (cCyl : SingularChain (TopCat.of HA.B) (m + 2))
    (cHa : SingularChain (TopCat.of HA.Ha) (m + 2))
    (hbd : chainBoundary (TopCat.of HA.carrier) (m + 1)
        (closedEmbeddingChain HA.isClosedEmbedding_fromCyl.isEmbedding (m + 2) cCyl
          + closedEmbeddingChain HA.isClosedEmbedding_fromHandle.isEmbedding (m + 2) cHa)
      ∈ subspaceChains (X := TopCat.of HA.carrier) T (m + 1)) :
    RelCoverGlueData (X := TopCat.of HA.carrier) T m where
  CA := Set.range HA.fromCyl
  CB := Set.range HA.fromHandle
  hcover := mem_range_fromCyl_or_fromHandle HA
  cA := closedEmbeddingChain HA.isClosedEmbedding_fromCyl.isEmbedding (m + 2) cCyl
  cB := closedEmbeddingChain HA.isClosedEmbedding_fromHandle.isEmbedding (m + 2) cHa
  hcA := closedEmbeddingChain_mem_subspaceChains HA.isClosedEmbedding_fromCyl.isEmbedding
    (m + 2) cCyl
  hcB := closedEmbeddingChain_mem_subspaceChains HA.isClosedEmbedding_fromHandle.isEmbedding
    (m + 2) cHa
  hbd := hbd

/-- **The two-core datum's cylinder-side detection is DISCHARGED** from the piece-intrinsic data:
the cylinder chain's boundary support `BdB` (absorbed by `T ∪` the handle core) and its intrinsic
detection off `BdB`. Produces the exact `hdetA` shape the glue theorem consumes. -/
theorem coreGlueData_hdetA {T : Set HA.carrier} {m : ℕ}
    {cCyl : SingularChain (TopCat.of HA.B) (m + 2)}
    {cHa : SingularChain (TopCat.of HA.Ha) (m + 2)}
    (hbd : chainBoundary (TopCat.of HA.carrier) (m + 1)
        (closedEmbeddingChain HA.isClosedEmbedding_fromCyl.isEmbedding (m + 2) cCyl
          + closedEmbeddingChain HA.isClosedEmbedding_fromHandle.isEmbedding (m + 2) cHa)
      ∈ subspaceChains (X := TopCat.of HA.carrier) T (m + 1))
    {BdB : Set HA.B} (habsorb : ∀ y ∈ BdB, HA.fromCyl y ∈ T ∪ Set.range HA.fromHandle)
    (hcCyl : chainBoundary (TopCat.of HA.B) (m + 1) cCyl
      ∈ subspaceChains (X := TopCat.of HA.B) BdB (m + 1))
    (hdet : ∀ (y : HA.B) (hy : y ∉ BdB),
      relClassOf (X := TopCat.of HA.B) ({y}ᶜ) m cCyl
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hy) (m + 1) hcCyl) ≠ 0)
    (x : HA.carrier) (hx : x ∉ T) (hxB : x ∉ (coreGlueData HA T m cCyl cHa hbd).CB) :
    relClassOf (X := TopCat.of HA.carrier) ({x}ᶜ) m (coreGlueData HA T m cCyl cHa hbd).cA
      ((coreGlueData HA T m cCyl cHa hbd).hbdA_local hx hxB) ≠ 0 :=
  cylCore_relClassOf_ne_zero HA habsorb m cCyl hcCyl hdet hx hxB
    ((coreGlueData HA T m cCyl cHa hbd).hbdA_local hx hxB)

/-- **The two-core datum's handle-side detection is DISCHARGED** — symmetric to the cylinder
side. -/
theorem coreGlueData_hdetB {T : Set HA.carrier} {m : ℕ}
    {cCyl : SingularChain (TopCat.of HA.B) (m + 2)}
    {cHa : SingularChain (TopCat.of HA.Ha) (m + 2)}
    (hbd : chainBoundary (TopCat.of HA.carrier) (m + 1)
        (closedEmbeddingChain HA.isClosedEmbedding_fromCyl.isEmbedding (m + 2) cCyl
          + closedEmbeddingChain HA.isClosedEmbedding_fromHandle.isEmbedding (m + 2) cHa)
      ∈ subspaceChains (X := TopCat.of HA.carrier) T (m + 1))
    {BdHa : Set HA.Ha} (habsorb : ∀ y ∈ BdHa, HA.fromHandle y ∈ T ∪ Set.range HA.fromCyl)
    (hcHa : chainBoundary (TopCat.of HA.Ha) (m + 1) cHa
      ∈ subspaceChains (X := TopCat.of HA.Ha) BdHa (m + 1))
    (hdet : ∀ (y : HA.Ha) (hy : y ∉ BdHa),
      relClassOf (X := TopCat.of HA.Ha) ({y}ᶜ) m cHa
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hy) (m + 1) hcHa) ≠ 0)
    (x : HA.carrier) (hx : x ∉ T) (hxA : x ∉ (coreGlueData HA T m cCyl cHa hbd).CA) :
    relClassOf (X := TopCat.of HA.carrier) ({x}ᶜ) m (coreGlueData HA T m cCyl cHa hbd).cB
      ((coreGlueData HA T m cCyl cHa hbd).hbdB_local hx hxA) ≠ 0 :=
  handleCore_relClassOf_ne_zero HA habsorb m cHa hcHa hdet hx hxA
    ((coreGlueData HA T m cCyl cHa hbd).hbdB_local hx hxA)

/-- **The two-core glued `HasRelFundClass`** — the full assembly on the surgery-trace carrier: the
two piece chains (each with boundary support absorbed by `T ∪` the other core, each intrinsically
detecting off its support set), the mod-2 seam-cancellation of the pushed sum, and the overlap-zone
straddle detection produce a class of `H_{m+2}(W, T)` restricting to ANY interior generator family
at every point off `T`. The one-sided detections are DISCHARGED (§1); the residual geometric atoms
are exactly {the two piece chains + supports, the two absorb facts, the seam-cancellation, the
overlap detection}. -/
theorem hasRelFundClass_of_coreChains (T : Set HA.carrier) (m : ℕ)
    (gen : ∀ x : HA.carrier, x ∉ T → (RelativeHomology (X := TopCat.of HA.carrier) ({x}ᶜ) (m + 2)
      ≃ₗ[ZMod 2] ZMod 2))
    (cCyl : SingularChain (TopCat.of HA.B) (m + 2))
    (cHa : SingularChain (TopCat.of HA.Ha) (m + 2))
    (hbd : chainBoundary (TopCat.of HA.carrier) (m + 1)
        (closedEmbeddingChain HA.isClosedEmbedding_fromCyl.isEmbedding (m + 2) cCyl
          + closedEmbeddingChain HA.isClosedEmbedding_fromHandle.isEmbedding (m + 2) cHa)
      ∈ subspaceChains (X := TopCat.of HA.carrier) T (m + 1))
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
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hy) (m + 1) hcHa) ≠ 0)
    (hdetAB : ∀ (x : HA.carrier) (hx : x ∉ T),
      x ∈ Set.range HA.fromCyl → x ∈ Set.range HA.fromHandle →
      relClassOf (X := TopCat.of HA.carrier) ({x}ᶜ) m
        (closedEmbeddingChain HA.isClosedEmbedding_fromCyl.isEmbedding (m + 2) cCyl
          + closedEmbeddingChain HA.isClosedEmbedding_fromHandle.isEmbedding (m + 2) cHa)
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hx) (m + 1) hbd) ≠ 0) :
    HasRelFundClass (X := TopCat.of HA.carrier) T gen :=
  (coreGlueData HA T m cCyl cHa hbd).hasRelFundClass_of_glueData gen
    (fun x hx hxB => coreGlueData_hdetA HA hbd habsorbB hcCyl hdetCyl x hx hxB)
    (fun x hx hxA => coreGlueData_hdetB HA hbd habsorbHa hcHa hdetHa x hx hxA)
    (fun x hx hxA hxB => hdetAB x hx hxA hxB)

end SKEFTHawking.SingularSurgeryCoreDetect
