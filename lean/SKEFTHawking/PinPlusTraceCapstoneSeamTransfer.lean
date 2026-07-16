/-
# Phase 5q.H close-out — THE SEAM TRANSFER: `hbd` CONSTRUCTED for a controlled cylinder representative

The corrector interface (`PinPlusTraceCapstoneCoverGlueSeamCorrector.hasClass_ofCorrector`) demands,
through its facts `hpS` + `heS`, the mod-2 seam-cancellation `hbd : ∂(push cCyl + push cHa) ∈ C(∂W)`
(their submodule sum). For the OPAQUE `.choose` representative `capstoneCylChain`, the seam faces of
the two pieces are two independently-chosen 4-chains on the seam zone — homologous but never literally
equal — so `hbd` is not constructible there. **The mathematics forces route (iii): re-choose the
cylinder representative with a CONTROLLED top face.**

This module executes that re-choice end to end:

* **§1 — the controlled cylinder detecting triple.** The cross-product representative
  `crossChain z` of the cylinder's relative fundamental class (`z` a fundamental cycle of `M`) has
  `∂(crossChain z) = z@⊤ + z@⊥` — the top face a NAMED chain, not a `.choose` artifact. Its full
  detecting triple is derived from the in-tree alphaU tower: the candidate class
  `[M] × [I,∂I] = relClassOf ∂W (crossChain z)` (a `Subtype.ext rfl` bridge), so
  `restrictBd_candidate_eq_crossHloc` + `crossHloc_ne_zero_of_alphaU_ne_zero` give the local
  nonvanishing of the CHAIN `crossChain z` at every interior cylinder point.
* **§2 — the capstone re-read** `capstoneCylChainT` on `.B` (the `cylW s.M = .B` defeq bridge, the
  same bridge `capstoneCylChain` used).
* **§3 — the transfer datum + `hbd` CONSTRUCTED.** `CapstoneSeamTransfer` names the genuinely
  φ-geometric chain-level content: the top-face split `z@⊤ = wAtt + wOut` (attached + un-attached),
  the disk-boundary split `∂cHa = uAtt + vOut` (attached + free-sphere), and the LITERAL transfer
  `push_fromCyl wAtt = push_fromHandle uAtt` (the shared seam face). From it `hbd_ofTransfer` proves
  the seam-cancellation: the shared face cancels mod 2, and the three remainders land in `∂W` via
  `d.bdry` (bottom face = source end), `d.topFaceCovered` (un-attached top), and
  `d.sphereFaceCovered` (free sphere face).
* **§4 — the two `hasClass` entries.** `hasClass_ofTransfer` lands the capstone `hasClass` from
  {`z`, the disk triple, the transfer datum, the straddle detection `hdetAB`};
  `hasClass_ofTransferCorrector` is the #178 corrector shape with fact (2) DISCHARGED — the corrector
  `p`'s remaining inputs are exactly `hpS`/`hagree`/`hp_det` (fact (2) `heS` is derived from the
  constructed `hbd` via `heS_of_hbd`).

**Dimension discipline.** `M` is the closed source 4-manifold; `z` a 4-cycle (degree `2+2`); the
top/bottom faces and the transfer chains `wAtt`/`wOut`/`uAtt`/`vOut` are 4-chains (degree `3+1`);
the piece chains and the corrector are 5-chains (degree `3+2`); detection is in local degree `3`
(top degree `3+2 = 5`).

**Fences.** No general collar theorem; no completeness Prop; no detection at a closed piece's
frontier. The straddle detection `hdetAB` (fact (3) at `p := glued`) remains the named geometric
residual — the honest irreducible seam atom. Additive module. Kernel-pure
(`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no `native_decide`,
no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusTraceCapstoneCoverGlueDisk
import SKEFTHawking.SingularSurgeryCoreDetectSeam
import SKEFTHawking.SingularRelativeCoverMVSeamCorrector

open scoped Manifold
open SKEFTHawking.BordismTheory
open SKEFTHawking.SurgeryFoundation
open SKEFTHawking.SurgeryFoundation.HandleAttachment
open SKEFTHawking.DiskChartGeneric (D5)
open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularRelativeFunctoriality
open SKEFTHawking.SingularExcisionIso
open SKEFTHawking.SingularMayerVietoris
open SKEFTHawking.SingularHomotopyInvariance
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassGeom
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCross
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossRestrict
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalReduce
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalBridge
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalAlphaU
open SKEFTHawking.SingularRelativeCoverMV
open SKEFTHawking.SingularRelativeCoverMVTransport
open SKEFTHawking.SingularRelativeCoverMVSeam
open SKEFTHawking.SingularSurgeryCoreDetect
open SKEFTHawking.PinPlusTraceRelFundReduce
open SKEFTHawking.PinPlusTraceCapstoneInhabit
open SKEFTHawking.PinPlusTraceCapstoneCoverGlue
open SKEFTHawking.PinPlusTraceCapstoneCoverGlueCyl
open SKEFTHawking.PinPlusTraceCapstoneCoverGlueDisk

namespace SKEFTHawking.PinPlusTraceCapstoneSeamTransfer

noncomputable section

/-! ## §0. Generic closed-embedding chain helpers (additivity, boundary-commutation, support). -/

section GenericPush

variable {P : Type} [TopologicalSpace P] {Wc : Type} [TopologicalSpace Wc]

/-- The closed-embedding pushforward is additive (both constituent maps are linear). -/
theorem closedEmbeddingChain_add {j : P → Wc} (hj : Topology.IsEmbedding j) (n : ℕ)
    (a b : SingularChain (TopCat.of P) n) :
    closedEmbeddingChain hj n (a + b)
      = closedEmbeddingChain hj n a + closedEmbeddingChain hj n b := by
  rw [closedEmbeddingChain, closedEmbeddingChain, closedEmbeddingChain, map_add, map_add]

/-- The closed-embedding pushforward commutes with the chain boundary. -/
theorem chainBoundary_closedEmbeddingChain {j : P → Wc} (hj : Topology.IsEmbedding j) (n : ℕ)
    (c : SingularChain (TopCat.of P) (n + 1)) :
    chainBoundary (TopCat.of Wc) n (closedEmbeddingChain hj (n + 1) c)
      = closedEmbeddingChain hj n (chainBoundary (TopCat.of P) n c) := by
  rw [closedEmbeddingChain, closedEmbeddingChain, ← chainIncl_chainBoundary, chainBoundary_mapChain]

/-- A piece chain supported in `Bd` pushes to a chain supported in `j '' Bd` — the support twin of
`chainBoundary_closedEmbeddingChain_mem`. -/
theorem closedEmbeddingChain_mem_of_mem {j : P → Wc} (hj : Topology.IsEmbedding j) {Bd : Set P}
    (n : ℕ) (c : SingularChain (TopCat.of P) n)
    (hc : c ∈ subspaceChains (X := TopCat.of P) Bd n) :
    closedEmbeddingChain hj n c ∈ subspaceChains (X := TopCat.of Wc) (j '' Bd) n := by
  have hmem : mapChain (X := TopCat.of P) (Y := sub (X := TopCat.of Wc) (Set.range j))
      ⟨hj.toHomeomorph, hj.toHomeomorph.continuous⟩ n c
      ∈ subspaceChains (X := sub (X := TopCat.of Wc) (Set.range j))
          (restr (X := TopCat.of Wc) (j '' Bd) (Set.range j)) n := by
    refine mapChain_mem_subspaceChains _ (fun q hq => ?_) n _ hc
    show (hj.toHomeomorph q : Wc) ∈ j '' Bd
    exact ⟨q, hq, rfl⟩
  exact subspaceChains_mono Set.inter_subset_left n
    ((chainIncl_mem_inter_iff (X := TopCat.of Wc) (j '' Bd) (Set.range j) _).mpr hmem)

/-- **The abstract mod-2 seam cancellation**: in a `ZMod 2`-module, the shared face cancels —
`(wA + wO + z0) + (uA + vO) = wO + z0 + vO` once `wA = uA`. The char-2 heart of `hbd_ofTransfer`,
isolated abstractly (the concrete carriers are whnf-hostile). -/
theorem transfer_cancel {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {wA wO z0 uA vO : V} (huw : wA = uA) :
    wA + wO + z0 + (uA + vO) = wO + z0 + vO := by
  rw [← huw]
  calc wA + wO + z0 + (wA + vO) = wA + wA + (wO + z0 + vO) := by abel
    _ = wO + z0 + vO := by rw [ZModModule.add_self, zero_add]

end GenericPush

/-! ## §1. The controlled cylinder detecting triple — `crossChain z` with a NAMED top face. -/

section ControlledCyl

variable {m' : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [PreconnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m' + 2))) M]

omit [T2Space M] [CompactSpace M] [Nonempty M] [PreconnectedSpace M] in
/-- The controlled representative's boundary is supported in the cylinder boundary `M × {⊥,⊤}` —
the `hc` leg of the detecting triple, direct from the prism boundary formula. -/
theorem crossChain_boundary_mem (z : cycles (TopCat.of M) (m' + 2)) :
    chainBoundary (TopCat.of (cylW M)) (m' + 1 + 1)
        (crossChain (m' + 2) (z : SingularChain (TopCat.of M) (m' + 2)))
      ∈ subspaceChains (X := TopCat.of (cylW M)) ((cylModel m').boundary (cylW M)) (m' + 1 + 1) :=
  crossChain_mem_relCycleLift (slice_one_mapsTo (M := M) (m' := m'))
    (slice_zero_mapsTo (M := M) (m' := m')) (m' + 1)
    (z : SingularChain (TopCat.of M) (m' + 2)) (LinearMap.mem_ker.mp z.2)

omit [PreconnectedSpace M] in
/-- **The concrete candidate class is the class of the controlled chain**: `[M] × [I,∂I] =
relClassOf ∂W (crossChain z)` for any fundamental cycle representative `z`. A `Subtype.ext rfl` on
the shared underlying `RelativeChain.mk` (the opacity-clean bridge). -/
theorem cylFundClassCandidate_eq_relClassOf (z : cycles (TopCat.of M) (m' + 2))
    (hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := m') (M := M)
      = Homology.mk (TopCat.of M) (m' + 2) z) :
    cylFundClassCandidate (M := M) (m' := m')
      = relClassOf (X := TopCat.of (cylW M)) ((cylModel m').boundary (cylW M)) (m' + 1)
          (crossChain (m' + 2) (z : SingularChain (TopCat.of M) (m' + 2)))
          (crossChain_boundary_mem z) := by
  rw [cylFundClassCandidate, hz, crossH_mk]
  exact congrArg
    (RelativeHomology.mk (X := TopCat.of (cylW M)) ((cylModel m').boundary (cylW M)) (m' + 1 + 1 + 1))
    (Subtype.ext rfl)

/-- **The controlled representative detects at every interior cylinder point** — the `hdet` leg of
the detecting triple, for the NAMED chain `crossChain z` (not a `.choose` artifact). Routes the
chain's local class through the candidate bridge into the alphaU tower's interior local-Künneth
nonvanishing. -/
theorem crossChain_relClassOf_ne_zero [T1Space (cylW M)] (z : cycles (TopCat.of M) (m' + 2))
    (hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := m') (M := M)
      = Homology.mk (TopCat.of M) (m' + 2) z)
    (y : ↑(TopCat.of (cylW M))) (hy : y ∉ (cylModel m').boundary (cylW M)) :
    relClassOf (X := TopCat.of (cylW M)) ({y}ᶜ) (m' + 1)
        (crossChain (m' + 2) (z : SingularChain (TopCat.of M) (m' + 2)))
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hy) (m' + 1 + 1)
          (crossChain_boundary_mem z)) ≠ 0 := by
  have hrestr : RestrictsToRelGen (X := TopCat.of (cylW M)) (m := m' + 1)
      ((cylModel m').boundary (cylW M)) (cylGen (M := M) (m' := m'))
      (cylFundClassCandidate (M := M) (m' := m')) :=
    restrictsToRelGen_candidate_of_ne_zero (fun x hx => by
      rw [restrictBd_candidate_eq_crossHloc x hx z hz]
      exact crossHloc_ne_zero_of_alphaU_ne_zero x hx z hz (alphaU_ne_zero x hx z hz))
  exact relClassOf_rep_ne_zero_of_restrictsToRelGen
    (crossChain (m' + 2) (z : SingularChain (TopCat.of M) (m' + 2)))
    (crossChain_boundary_mem z) (cylFundClassCandidate_eq_relClassOf z hz ▸ hrestr) y hy

end ControlledCyl

/-! ## §2. The capstone re-read — the controlled representative on the cylinder end `.B`. -/

variable (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
  [CompactSpace s.M] [Nonempty s.M] [PreconnectedSpace s.M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M]
  (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
  (hφ : Continuous φ) (hφinj : Function.Injective φ)
  (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
  (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
  (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)

/-- **The controlled cylinder representative on the capstone's cylinder end** `.B = s.M × I`
(the `cylW s.M = .B` defeq bridge): the cross-product chain of a fundamental cycle `z` of the
source 4-manifold, degree `3 + 2`. Its top face is the NAMED 4-chain `z@⊤`. -/
def capstoneCylChainT (z : cycles (TopCat.of s.M) (2 + 2)) :
    SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 2) :=
  crossChain (2 + 2) (z : SingularChain (TopCat.of s.M) (2 + 2))

omit [Nonempty s.M] [PreconnectedSpace s.M] in
/-- The controlled representative's boundary is supported in `BdB = M × {⊥,⊤}`. -/
theorem capstoneCylT_hc (z : cycles (TopCat.of s.M) (2 + 2)) :
    chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)
        (capstoneCylChainT s S hS φ hφ hφinj z)
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
          (capstoneCylBdB s S hS φ hφ hφinj) (3 + 1) :=
  crossChain_boundary_mem (m' := 2) (M := s.M) z

/-- The controlled representative detects the local generator at every interior cylinder point. -/
theorem capstoneCylT_hdet (z : cycles (TopCat.of s.M) (2 + 2))
    (hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := s.M)
      = Homology.mk (TopCat.of s.M) (2 + 2) z)
    (y : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
    (hy : y ∉ capstoneCylBdB s S hS φ hφ hφinj) :
    relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) ({y}ᶜ) 3
        (capstoneCylChainT s S hS φ hφ hφinj z)
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hy) (3 + 1)
          (capstoneCylT_hc s S hS φ hφ hφinj z)) ≠ 0 :=
  crossChain_relClassOf_ne_zero (m' := 2) (M := s.M) z hz y hy

/-! ## §3. The seam-transfer datum and the CONSTRUCTED seam-cancellation `hbd`. -/

/-- **The capstone seam-transfer datum** — the genuinely φ-geometric chain-level content of the
mod-2 seam-cancellation, for the controlled cylinder representative `capstoneCylChainT z` and a
disk chain `cHa`. Bundles: the top-face split `z@⊤ = wAtt + wOut` into the attached part and the
un-attached part (supported in `M × {⊤} ∖ range φ`); the disk-boundary split `∂cHa = uAtt + vOut`
into the attached part and the free-sphere part (supported in `S⁴ ∖ S`); and the **literal seam-face
transfer** `push_fromCyl wAtt = push_fromHandle uAtt` — the shared 4-face of the two pieces through
the seam. Each field is a concrete-chain geometric atom; none is a completeness Prop. -/
structure CapstoneSeamTransfer (z : cycles (TopCat.of s.M) (2 + 2))
    (cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2)) where
  /-- the attached part of the cylinder's top face `z@⊤` (the cylinder-side seam face). Typed on
  the cross-product carrier `cyl M` (defeq `.B`) so the split equations stay homogeneous. -/
  wAtt : SingularChain (cyl (TopCat.of s.M)) (3 + 1)
  /-- the un-attached part of the cylinder's top face `z@⊤`. -/
  wOut : SingularChain (cyl (TopCat.of s.M)) (3 + 1)
  /-- the top-face split: `z@⊤ = wAtt + wOut`. -/
  hsplit : mapChain (slice (graphHom (TopCat.of s.M)) 1) (3 + 1)
      (z : SingularChain (TopCat.of s.M) (3 + 1)) = wAtt + wOut
  /-- the un-attached part is supported in the un-attached top face `M × {⊤} ∖ range φ`. -/
  hwOut : wOut ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
      ((Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1))) \ Set.range φ) (3 + 1)
  /-- the attached part of the disk boundary `∂cHa` (the handle-side seam face). -/
  uAtt : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1)
  /-- the free-sphere part of the disk boundary `∂cHa`. -/
  vOut : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1)
  /-- the disk-boundary split: `∂cHa = uAtt + vOut`. -/
  hsplitHa : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1) cHa
      = uAtt + vOut
  /-- the free-sphere part is supported in the free boundary sphere `S⁴ ∖ S`. -/
  hvOut : vOut ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
      ({q : D5 | ‖(q : EuclideanSpace ℝ (Fin 5))‖ = 1} \ S) (3 + 1)
  /-- **the literal seam-face transfer**: the two attached faces agree as carrier chains — the
  shared 4-face of the two pieces through the seam. This is THE genuinely φ-geometric atom. -/
  htransfer : closedEmbeddingChain
        (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
        (3 + 1) wAtt
      = closedEmbeddingChain
        (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
        (3 + 1) uAtt

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **The mod-2 seam-cancellation `hbd`, CONSTRUCTED from the transfer datum.** The boundary of the
glued sum `push (capstoneCylChainT z) + push cHa` decomposes as (shared face + shared face) +
un-attached top + bottom face + free sphere face; the shared face cancels mod 2, the bottom face is
the source end (`d.bdry`), the un-attached top lands in the surgered end (`d.topFaceCovered`), and
the free sphere face lands in the surgered end (`d.sphereFaceCovered`). The first of the two
collar-chain residuals, discharged. -/
theorem hbd_ofTransfer {z : cycles (TopCat.of s.M) (2 + 2)}
    {cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2)}
    (T : CapstoneSeamTransfer s S hS φ hφ hφinj z cHa) :
    chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
        (closedEmbeddingChain
            (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
            (3 + 2) (capstoneCylChainT s S hS φ hφ hφinj z)
          + closedEmbeddingChain
            (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
            (3 + 2) cHa)
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1) := by
  -- the prism boundary formula for the controlled representative, on `.B`
  have hcross : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)
      (capstoneCylChainT s S hS φ hφ hφinj z)
      = mapChain (slice (graphHom (TopCat.of s.M)) 1) (3 + 1)
          (z : SingularChain (TopCat.of s.M) (3 + 1))
        + mapChain (slice (graphHom (TopCat.of s.M)) 0) (3 + 1)
          (z : SingularChain (TopCat.of s.M) (3 + 1)) :=
    chainBoundary_crossChain 3 (z : SingularChain (TopCat.of s.M) (3 + 1))
      (LinearMap.mem_ker.mp z.2)
  -- the cylinder-side boundary, fully split (calc-style: exact-mode steps dodge cross-type keying)
  have hbC : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
      (closedEmbeddingChain
        (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
        (3 + 2) (capstoneCylChainT s S hS φ hφ hφinj z))
      = closedEmbeddingChain
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
          (3 + 1) T.wAtt
        + closedEmbeddingChain
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
          (3 + 1) T.wOut
        + closedEmbeddingChain
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
          (3 + 1) (mapChain (slice (graphHom (TopCat.of s.M)) 0) (3 + 1)
            (z : SingularChain (TopCat.of s.M) (3 + 1))) := by
    have hsplitB : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)
        (capstoneCylChainT s S hS φ hφ hφinj z)
        = T.wAtt + T.wOut + mapChain (slice (graphHom (TopCat.of s.M)) 0) (3 + 1)
            (z : SingularChain (TopCat.of s.M) (3 + 1)) := by
      rw [hcross, T.hsplit]
    exact (chainBoundary_closedEmbeddingChain
        (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
        (3 + 1) (capstoneCylChainT s S hS φ hφ hφinj z)).trans
      ((congrArg (closedEmbeddingChain
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
          (3 + 1)) hsplitB).trans
        ((closedEmbeddingChain_add
            (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
            (3 + 1) (T.wAtt + T.wOut) (mapChain (slice (graphHom (TopCat.of s.M)) 0) (3 + 1)
              (z : SingularChain (TopCat.of s.M) (3 + 1)))).trans
          (congrArg (fun w => w + closedEmbeddingChain
              (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
              (3 + 1) (mapChain (slice (graphHom (TopCat.of s.M)) 0) (3 + 1)
                (z : SingularChain (TopCat.of s.M) (3 + 1))))
            (closedEmbeddingChain_add
              (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
              (3 + 1) T.wAtt T.wOut))))
  -- the handle-side boundary, split
  have hbH : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
      (closedEmbeddingChain
        (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
        (3 + 2) cHa)
      = closedEmbeddingChain
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
          (3 + 1) T.uAtt
        + closedEmbeddingChain
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
          (3 + 1) T.vOut :=
    (chainBoundary_closedEmbeddingChain
        (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
        (3 + 1) cHa).trans
      ((congrArg (closedEmbeddingChain
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
          (3 + 1)) T.hsplitHa).trans
        (closedEmbeddingChain_add
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
          (3 + 1) T.uAtt T.vOut))
  -- the boundary of the glued sum, reduced to the three ∂W-supported remainders
  have key : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
      (closedEmbeddingChain
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
          (3 + 2) (capstoneCylChainT s S hS φ hφ hφinj z)
        + closedEmbeddingChain
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
          (3 + 2) cHa)
      = closedEmbeddingChain
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
          (3 + 1) T.wOut
        + closedEmbeddingChain
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
          (3 + 1) (mapChain (slice (graphHom (TopCat.of s.M)) 0) (3 + 1)
            (z : SingularChain (TopCat.of s.M) (3 + 1)))
        + closedEmbeddingChain
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
          (3 + 1) T.vOut := by
    rw [map_add, hbC, hbH]
    exact transfer_cancel T.htransfer
  rw [key]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · -- the un-attached top face lands in the surgered end `range eM' ⊆ ∂W`
    refine subspaceChains_mono ?_ (3 + 1)
      (closedEmbeddingChain_mem_of_mem _ (3 + 1) _ T.hwOut)
    intro w hw
    rw [capstone_boundary_eq s t S hS φ hφ hφinj cd hseam d]
    exact Set.mem_union_right _ (d.topFaceCovered hw)
  · -- the bottom face `z@⊥` is the source end `range ktSourceEnd ⊆ ∂W`
    have hz0 : mapChain (slice (graphHom (TopCat.of s.M)) 0) (3 + 1)
        (z : SingularChain (TopCat.of s.M) (3 + 1))
        ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
            (Set.univ ×ˢ ({⊥} : Set (Set.Icc (0 : ℝ) 1))) (3 + 1) := by
      refine mapChain_mem_subspaceChains _ (fun x _ => ?_) (3 + 1) _
        (mem_subspaceChains_univ (3 + 1) _)
      exact ⟨Set.mem_univ _, rfl⟩
    refine subspaceChains_mono ?_ (3 + 1)
      (closedEmbeddingChain_mem_of_mem _ (3 + 1) _ hz0)
    rintro w ⟨⟨mm, tt⟩, ⟨_, ht⟩, rfl⟩
    rw [capstone_boundary_eq s t S hS φ hφ hφinj cd hseam d]
    refine Set.mem_union_left _ ⟨mm, ?_⟩
    rw [ktSourceEnd]
    exact congrArg _ (Prod.ext rfl (by rw [Set.mem_singleton_iff.mp ht]; rfl))
  · -- the free sphere face lands in the surgered end `range eM' ⊆ ∂W`
    refine subspaceChains_mono ?_ (3 + 1)
      (closedEmbeddingChain_mem_of_mem _ (3 + 1) _ T.hvOut)
    intro w hw
    rw [capstone_boundary_eq s t S hS φ hφ hφinj cd hseam d]
    exact Set.mem_union_right _ (d.sphereFaceCovered hw)

/-! ## §4. The two `hasClass` entries — the deepest capstone atom from the transfer. -/

/-- **The capstone `hasClass` from the transfer datum + the straddle detection.** Fires
`capstone_hasClass_ofCoreChains` with the CONTROLLED cylinder representative (its detecting triple
supplied by §1–§2), `hbd` CONSTRUCTED from the transfer datum (§3), and both boundary-absorbs from
the surgered-end datum. So the deepest capstone atom reduces, for connected `s.M`, to exactly:
{a fundamental cycle `z` of `M`, the disk detecting triple, the chain-level seam-transfer datum,
the straddle detection `hdetAB`}. -/
def hasClass_ofTransfer (z : cycles (TopCat.of s.M) (2 + 2))
    (hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := s.M)
      = Homology.mk (TopCat.of s.M) (2 + 2) z)
    (cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2))
    (hcHa : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1) cHa
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
          {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} (3 + 1))
    (hdetHa : ∀ (y : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
        (hy : y ∉ {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1}),
      relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) ({y}ᶜ) 3 cHa
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hy) (3 + 1) hcHa) ≠ 0)
    (T : CapstoneSeamTransfer s S hS φ hφ hφinj z cHa)
    (hdetAB : ∀ (x : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
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
          (hbd_ofTransfer s t S hS φ hφ hφinj cd hseam d T)) ≠ 0) :
    letI := capstone_t1Space s t S hS φ hφ hφinj cd hseam d
    HasRelFundClass (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (interiorGenFamily (W := (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        ((𝓡 4).prod (𝓡∂ 1)) εtrace) :=
  capstone_hasClass_ofCoreChains s t S hS φ hφ hφinj cd hseam d
    (capstoneCylChainT s S hS φ hφ hφinj z) cHa
    (hbd_ofTransfer s t S hS φ hφ hφinj cd hseam d T)
    (capstone_habsorbB s t S hS φ hφ hφinj cd hseam d)
    (capstoneCylT_hc s S hS φ hφ hφinj z)
    (capstoneCylT_hdet s S hS φ hφ hφinj z hz)
    (capstone_habsorbHa s t S hS φ hφ hφinj cd hseam d)
    hcHa hdetHa hdetAB

/-- **The #178 corrector shape with fact (2) DISCHARGED.** The capstone `hasClass` from the
transfer datum + a corrector chain `p` with THREE facts — `hpS` (fact 1), `hagree` (fact 4), and
`hp_det` (fact 3). The seam-cancellation fact (2) `heS` is DERIVED: the transfer datum constructs
`hbd` (§3) and `heS_of_hbd` trades it. Routes through `SeamCollarChainDatum.ofCorrector_ofHbd` and
the carrier-level seam supplier `coreChains_hdetAB_of_seam` into `hasClass_ofTransfer`. -/
def hasClass_ofTransferCorrector (z : cycles (TopCat.of s.M) (2 + 2))
    (hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := s.M)
      = Homology.mk (TopCat.of s.M) (2 + 2) z)
    (cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2))
    (hcHa : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1) cHa
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
          {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} (3 + 1))
    (hdetHa : ∀ (y : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
        (hy : y ∉ {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1}),
      relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) ({y}ᶜ) 3 cHa
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hy) (3 + 1) hcHa) ≠ 0)
    (T : CapstoneSeamTransfer s S hS φ hφ hφinj z cHa)
    (p : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2))
    (hpS : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1) p
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1))
    (hagree : closedEmbeddingChain
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
          (3 + 2) (capstoneCylChainT s S hS φ hφ hφinj z)
        + closedEmbeddingChain
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
          (3 + 2) cHa - p
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl
            ∩ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle)ᶜ (3 + 2))
    (hp_det : ∀ (x : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
        (hx : x ∉ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)),
        x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl →
        x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle →
      relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) ({x}ᶜ) 3 p
          (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hx) (3 + 1) hpS) ≠ 0) :
    letI := capstone_t1Space s t S hS φ hφ hφinj cd hseam d
    HasRelFundClass (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (interiorGenFamily (W := (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        ((𝓡 4).prod (𝓡∂ 1)) εtrace) :=
  hasClass_ofTransfer s t S hS φ hφ hφinj cd hseam d z hz cHa hcHa hdetHa T
    (fun x hx hxA hxB =>
      coreChains_hdetAB_of_seam (ktHandleAttachment s.M D5 S hS φ hφ hφinj)
        (SeamCollarChainDatum.ofCorrector_ofHbd hpS
          (hbd_ofTransfer s t S hS φ hφ hφinj cd hseam d T) hagree hp_det)
        x hx hxA hxB)

end

end SKEFTHawking.PinPlusTraceCapstoneSeamTransfer
