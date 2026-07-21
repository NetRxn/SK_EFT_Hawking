/-
# Phase 5q.H (#212) — the `hctrlH` lane: the handle-side co-adaptation, PRODUCED.

**Headline.** `hctrlH` does NOT need `ClosedSeamAttachedCollarBridge`. The bridge demands a
free-sphere correction supported in `sphere ∖ S` — a *closed-`S`* complement, which the open-cover
subdivision engine provably cannot reach. But the collar-pair row's `hctrlH` field does not ask for
that: its companion `houtH` asks for support in `sphere ∖ (Subtype.val '' K)` where `K` is the
**builder-chosen shrunk closed core** `K ⊂ int A` (a free field of `CollarPairBuild`). That is an
*open* complement of a closed set — exactly the granularity the engine delivers.

So the whole lane closes by composing bricks that already exist:

* take the cover `{U, Kᶜ}` of the boundary sphere, where `U` is any open set with `K ⊆ U` and
  `U ∩ sphere ⊆ S` (the ambient statement of "`K` sits in the sphere-relative interior of `S`" —
  which is literally the `#210` design intent of the shrunk core);
* fire `PinPlusTraceSeamResidualNarrow.exists_subtype_boundary_split_of_relCycle_inf` at
  `W = sphere`: the free remainder lands in `Kᶜ ∩ sphere = sphere ∖ K` on the nose, and the
  attached part is a pushforward from `↥(U ∩ sphere)`;
* **re-seat** the attached part along `U ∩ sphere ⊆ S` (`subspaceChains_mono`), which turns the
  pushforward-from-`↥(U ∩ sphere)` into a pushforward-from-`↥S` — the `seamLegHa` shape. No collar
  retraction, no closed-support barrier: the barrier only ever bit because the *bridge's* correction
  was demanded off `S` rather than off `K`.

§1 is the ambient producer over `D⁵`; §2 re-seats it verbatim onto the row's `ctrlHandle` /
`seamLegHa` shape, so the output is literally the `hctrlH` + `houtH` pair of `CollarPairBuild`.

**Sufficient vs equivalent.** The producer is *sufficient* for `hctrlH`/`houtH`, not equivalent to
them: it exhibits one admissible `(μH, cCore, outH)` triple. It does not claim the row's `cCore` is
unique, and it does not by itself supply the **co-adaptation** with `hctrlC` (the cylinder side must
be split against the *same* `cCore`); that coupling remains the `hctrlC` obligation.

Additive module. Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project
axiom, no `native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusTraceSeamResidualNarrow
import SKEFTHawking.PinPlusTraceCapstoneCollarPair

namespace SKEFTHawking.PinPlusTraceCapstoneCollarPairHandle

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularMayerVietoris
open SKEFTHawking.SingularMayerVietorisLES
open SKEFTHawking.SingularSubdivision
open SKEFTHawking.PinPlusTraceCapstoneSeamSplit
open SKEFTHawking.PinPlusTraceDiskCorePair
open SKEFTHawking.PinPlusTraceSeamResidualNarrow
open SKEFTHawking.DiskChartGeneric (D5)

noncomputable section

/-- The boundary sphere `S⁴ = ∂D⁵` as a subset of `D⁵`. -/
abbrev sphere5 : Set D5 := {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1}

/-! ## §1. The ambient producer — the disk-side split off a closed core `K`. -/

/-- **The handle-side co-adaptation, PRODUCED (ambient form).** For a closed core `K ⊆ D⁵` sitting
inside an open `U` whose sphere-part is contained in the seam `S`, some subdivision
`Sdᵘ diskDetectChain` has its boundary split EXACTLY as a pushforward from `↥S` plus a remainder
supported in `sphere ∖ K`. This is the `hctrlH`/`houtH` pair of `CollarPairBuild`, with no collar
bridge anywhere: the free remainder is demanded off the *core* `K` (an open complement), not off the
*seam* `S` (a closed complement), so the open-cover engine reaches it directly. -/
theorem exists_diskDetect_seam_split_offCore {S K U : Set D5} (hKcl : IsClosed K) (hU : IsOpen U)
    (hKU : K ⊆ U) (hUS : U ∩ sphere5 ⊆ S) :
    ∃ (μ : ℕ) (cCore : SingularChain (sub (X := TopCat.of D5) S) (3 + 1))
        (outH : SingularChain (TopCat.of D5) (3 + 1)),
      outH ∈ subspaceChains (X := TopCat.of D5) (sphere5 \ K) (3 + 1)
      ∧ chainBoundary (TopCat.of D5) (3 + 1)
            ((⇑(singularSd (TopCat.of D5) (3 + 2)))^[μ] diskDetectChain)
          = mapChain (ambIncl (X := TopCat.of D5) S) (3 + 1) cCore + outH := by
  have hcover : sphere5 ⊆ U ∪ Kᶜ := fun x _ => (em (x ∈ K)).imp (fun h => hKU h) id
  obtain ⟨μ, cU, vOut, hvOut, hsplit, _⟩ :=
    exists_subtype_boundary_split_of_relCycle_inf (X := TopCat.of D5) hU hKcl.isOpen_compl hcover
      diskDetectChain diskDetectChain_hc
  have hmem : mapChain (ambIncl (X := TopCat.of D5) (U ∩ sphere5)) (3 + 1) cU
      ∈ subspaceChains (X := TopCat.of D5) (U ∩ sphere5) (3 + 1) := by
    rw [mapChain_ambIncl]
    exact LinearMap.mem_range_self _ cU
  have hatt : mapChain (ambIncl (X := TopCat.of D5) (U ∩ sphere5)) (3 + 1) cU
      ∈ subspaceChains (X := TopCat.of D5) S (3 + 1) := subspaceChains_mono hUS (3 + 1) hmem
  obtain ⟨cCore, hcCore⟩ := hatt
  have hcore : mapChain (ambIncl (X := TopCat.of D5) S) (3 + 1) cCore
      = mapChain (ambIncl (X := TopCat.of D5) (U ∩ sphere5)) (3 + 1) cU := by
    rw [mapChain_ambIncl]; exact hcCore
  have hout : vOut ∈ subspaceChains (X := TopCat.of D5) (sphere5 \ K) (3 + 1) := by
    have hset : Kᶜ ∩ sphere5 = sphere5 \ K := by rw [Set.inter_comm, Set.diff_eq]
    rw [← hset]; exact hvOut
  exact ⟨μ, cCore, vOut, hout, by rw [hsplit, hcore]⟩

/-! ## §2. The row shape — the `hctrlH` + `houtH` pair of `CollarPairBuild`, verbatim. -/

section Row

open scoped Manifold
open SKEFTHawking.BordismTheory
open SKEFTHawking.SurgeryFoundation
open SKEFTHawking.SurgeryFoundation.HandleAttachment
open SKEFTHawking.PinPlusTraceCapstoneSeamTransferSupply
open SKEFTHawking.PinPlusTraceCapstoneCollarPair

variable (s : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
  [CompactSpace s.M] [Nonempty s.M] [PreconnectedSpace s.M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M]
  (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
  (hφ : Continuous φ) (hφinj : Function.Injective φ)

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **`hctrlH` AND `houtH`, SUPPLIED.** For any closed shrunk core `K ⊆ ↥S` that sits inside an open
`U ⊆ D⁵` whose sphere-part is contained in `S` — i.e. `K` lies in the sphere-relative interior of the
attaching region, which is exactly the `#210` design intent of the shrunk core `K ⊂ int A` — there
are a subdivision count `μH`, a seam core `cCore` on `↥S`, and a remainder `outH` supported in
`sphere ∖ (Subtype.val '' K)` satisfying the `hctrlH` equation of `CollarPairBuild` on the nose.

The only hypothesis beyond closedness is the interiority of `K`; no collar deformation-retraction and
no `ClosedSeamAttachedCollarBridge` is used or needed. This is *sufficient* for the two fields, not
equivalent to them: it exhibits one admissible triple and does not supply the co-adaptation with the
cylinder side (`hctrlC` must split against the SAME `cCore`), which remains open. -/
theorem exists_ctrlHandle_split_offCore {K : Set ↥S} (hKcl : IsClosed K) {U : Set D5}
    (hU : IsOpen U) (hKU : Subtype.val '' K ⊆ U) (hUS : U ∩ sphere5 ⊆ S) :
    ∃ (μH : ℕ) (cCore : SingularChain (TopCat.of ↥S) (3 + 1))
        (outH : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1)),
      outH ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
          ({q : D5 | ‖(q : EuclideanSpace ℝ (Fin 5))‖ = 1} \ Subtype.val '' K) (3 + 1)
      ∧ chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1)
            (ctrlHandle s S hS φ hφ hφinj μH)
          = mapChain (seamLegHa s S hS φ hφ hφinj) (3 + 1) cCore + outH := by
  have hKcl' : IsClosed (Subtype.val '' K) :=
    (hS.isClosedEmbedding_subtypeVal).isClosedMap _ hKcl
  exact exists_diskDetect_seam_split_offCore hKcl' hU hKU hUS

/-- **Non-vacuity of the interiority hypothesis.** `exists_ctrlHandle_split_offCore` is not a
statement about the empty core: whenever the open set `U` witnessing "`U ∩ sphere ⊆ S`" actually
meets the sphere, a NONEMPTY closed core `K ⊆ ↥S` satisfying its hypotheses exists (the singleton at
any such point). Since the row's `hcoreHit` rules the empty core out
(`PinPlusTraceCapstoneCollarPair.nonzero_of_genuine` fails at `K = ∅`), this is the certificate that
the supplied `hctrlH` lives at admissible cores. -/
theorem exists_nonempty_core_of_sphere_mem {U : Set D5} (hUS : U ∩ sphere5 ⊆ S) {x : D5}
    (hxU : x ∈ U) (hx : x ∈ sphere5) :
    ∃ K : Set ↥S, K.Nonempty ∧ IsClosed K ∧ Subtype.val '' K ⊆ U := by
  refine ⟨{(⟨x, hUS ⟨hxU, hx⟩⟩ : ↥S)}, Set.singleton_nonempty _, isClosed_singleton, ?_⟩
  rw [Set.image_singleton]
  exact Set.singleton_subset_iff.mpr hxU

end Row

end

end SKEFTHawking.PinPlusTraceCapstoneCollarPairHandle
