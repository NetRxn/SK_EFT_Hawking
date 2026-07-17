/-
# Phase 5q.H — THE SEAM-TRANSFER NO-GO: the open-support transfer shape is UNINHABITABLE

**The #210 adjudication (road D), worked directly by the lead.** Three independent blocks
(#198, #204, #207) walled at "the shared cSeam serving both co-adapted splits" and recorded the
closed-S support barrier as *a machinery gap* ("not kernel-false — it holds for a genuine surgery
collar"). This module proves that intuition WRONG for the exact consumption shape as shipped:
`CapstoneSeamTransfer` (hence the shared-cSeam `CapstoneSeamTransferSeam`) is **provably
uninhabitable** whenever the top-face class of `z` is homologically nonzero and the two support
regions carry no top homology — which is exactly the genuine consumption (a fundamental cycle `z`,
a proper attaching region).

**The mechanism (three forced steps):**
1. *The transfer equation forces closed-seam support.* `htransfer : push_fromCyl wAtt =
   push_fromHandle uAtt` — both pushforwards are `mapChain`s of injective maps, so supports
   transport exactly (mod-2 coefficients admit no collision under an injective index map), and
   every `wAtt`-simplex is forced into `fromCyl⁻¹(range fromHandle) ⊆ range φ`
   (`fromCyl_image_compl_disjoint_range_fromHandle`).
2. *Char-2 boundary algebra forces both pieces to be cycles.* `∂wAtt + ∂wOut = ∂(z@⊤) = 0`, so
   `∂wAtt = ∂wOut` is supported in both `range φ` and its complement — hence zero
   (`subspaceChains_inf_compl_eq_bot`).
3. *The class decomposes and dies.* `z@⊤ = wAtt + wOut` with `wAtt` a seam-supported cycle and
   `wOut` an off-seam-supported cycle: if seam-supported 4-cycles bound and off-seam-supported
   4-cycles bound (the genuine situation: `H₄(S¹×D³;ℤ/2) = 0`, `H₄` of an open 4-region `= 0`),
   then `z@⊤` bounds — contradicting `z` fundamental.

**Consequence (the repair direction, for the follow-up):** the structure's `hwOut`/`hvOut` fields
demand support in the OPEN complements (`… \ range φ`, `sphere \ S`). The classical seam picture
(two rel-fundamental pieces sharing the interface face) satisfies only the CLOSED-complement
version (`… \ interior`): the off-piece touches the interface. The honest consumption shape must
carry closed-complement supports; the downstream `hbd`/coverage fields must then absorb the
interface mod 2 (it cancels: `∂wAtt = ∂wOut` at the interface). That repaired shape is a NEW
consumption shape — GATE-PENDING before anything consumes it (rounds 11–13 discipline).

**Fences.** Additive module; no existing statement touched. The hypotheses of the IsEmpty
theorems are honest homological facts about the REGIONS (never about the transfer); no
circularity. Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project
axiom, no `native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusTraceCapstoneSeamTransferSupply

open scoped Manifold
open SKEFTHawking.SurgeryFoundation
open SKEFTHawking.SurgeryFoundation.HandleAttachment
open SKEFTHawking.DiskChartGeneric (D5)
open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularExcision
open SKEFTHawking.SingularMayerVietoris
open SKEFTHawking.SingularDisjointUnion
open SKEFTHawking.SingularMayerVietorisLES
open SKEFTHawking.SingularHomotopyInvariance
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.SingularRelativeCoverMVTransport
open SKEFTHawking.PinPlusTraceCapstoneSeamTransfer
open SKEFTHawking.PinPlusTraceCapstoneSeamTransferSupply
open CategoryTheory Opposite

namespace SKEFTHawking
namespace PinPlusTraceSeamTransferNoGo

noncomputable section

/-! ## §0. The pushforward-support toolkit (generic, `mapChain`-level)

`mapChain ψ` of an injective continuous map transports Finsupp supports exactly (mod-2
coefficients admit no collision under an injective index map), and the pushed simplex's
point-set range is the `ψ`-image of the original's. Together these pull `subspaceChains`
membership back through any injective pushforward — the engine of forcing step 1. -/

section Toolkit

variable {X Y : TopCat}

/-- The equiv-conjugation identity for `mapSimplex`: the pushed simplex IS post-composition. -/
theorem toSSetObjEquiv_mapSimplex (ψ : C(↑X, ↑Y)) {n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) :
    Y.toSSetObjEquiv (op (SimplexCategory.mk n)) (mapSimplex ψ σ)
      = ψ.comp (X.toSSetObjEquiv (op (SimplexCategory.mk n)) σ) := by
  rw [mapSimplex, Equiv.apply_symm_apply]

/-- `mapSimplex` of an injective continuous map is injective on singular simplices. -/
theorem mapSimplex_injective (ψ : C(↑X, ↑Y)) (hψ : Function.Injective ψ) (n : ℕ) :
    Function.Injective (mapSimplex (X := X) (Y := Y) ψ (n := n)) := by
  intro σ τ h
  have h2 : ψ.comp (X.toSSetObjEquiv (op (SimplexCategory.mk n)) σ)
      = ψ.comp (X.toSSetObjEquiv (op (SimplexCategory.mk n)) τ) := by
    rw [← toSSetObjEquiv_mapSimplex, ← toSSetObjEquiv_mapSimplex, h]
  refine (X.toSSetObjEquiv (op (SimplexCategory.mk n))).injective (ContinuousMap.ext fun p => ?_)
  exact hψ (DFunLike.congr_fun h2 p)

/-- `mapChain` is the Finsupp `mapDomain` along `mapSimplex`. -/
theorem mapChain_eq_mapDomain (ψ : C(↑X, ↑Y)) (n : ℕ) (c : SingularChain X n) :
    mapChain ψ n c = Finsupp.mapDomain (mapSimplex ψ) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => rw [map_add, Finsupp.mapDomain_add, h₁, h₂]
  | single σ a => rw [mapChain_single, Finsupp.mapDomain_single]

/-- **Support transport**: for injective `ψ`, a support simplex of `c` pushes to a support
simplex of `mapChain ψ c` (mod-2 coefficients transport exactly). -/
theorem mapSimplex_mem_support_mapChain (ψ : C(↑X, ↑Y)) (hψ : Function.Injective ψ) (n : ℕ)
    (c : SingularChain X n) {σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))}
    (hσ : σ ∈ c.support) : mapSimplex ψ σ ∈ (mapChain ψ n c).support := by
  rw [Finsupp.mem_support_iff] at hσ ⊢
  rw [mapChain_eq_mapDomain, Finsupp.mapDomain_apply (mapSimplex_injective ψ hψ n)]
  exact hσ

/-- **The membership pullback**: `subspaceChains` membership pulls back through an injective
pushforward to the preimage subspace. The generic engine of forcing step 1. -/
theorem mem_subspaceChains_of_mapChain_mem (ψ : C(↑X, ↑Y)) (hψ : Function.Injective ψ)
    {T : Set ↑Y} {n : ℕ} {c : SingularChain X n}
    (h : mapChain ψ n c ∈ subspaceChains (X := Y) T n) :
    c ∈ subspaceChains (X := X) (ψ ⁻¹' T) n := by
  refine mem_subspaceChains_of_support fun τ hτ => ?_
  have hpush := range_of_mem_subspaceChains h (mapSimplex_mem_support_mapChain ψ hψ n c hτ)
  rw [toSSetObjEquiv_mapSimplex] at hpush
  intro x hx
  obtain ⟨p, rfl⟩ := hx
  exact hpush ⟨p, rfl⟩

/-- `closedEmbeddingChain` IS `mapChain` of the underlying map (the two-step
range-factorization composes away). -/
theorem closedEmbeddingChain_eq_mapChain {P : Type} [TopologicalSpace P] {Wc : Type}
    [TopologicalSpace Wc] {j : P → Wc} (hj : Topology.IsEmbedding j) (n : ℕ)
    (c : SingularChain (TopCat.of P) n) :
    closedEmbeddingChain hj n c = mapChain (X := TopCat.of P) (Y := TopCat.of Wc)
      ⟨j, hj.continuous⟩ n c := by
  rw [closedEmbeddingChain, ← mapChain_ambIncl, ← mapChain_comp]
  rfl

end Toolkit

/-! ## §1. The forcing — the transfer datum's pieces are seam-pinned cycles

In the seam-transfer context: `htransfer` pins `wAtt` into the closed attach image
`range φ` (step 1), and char-2 boundary algebra makes both split pieces cycles (step 2). -/

variable (s : SingularManifold PUnit.{1} 0 (𝓡 4)) [T2Space s.M] [CompactSpace s.M]
  (S : Set D5) (hS : IsClosed S) (φ : ↑S → s.M × Set.Icc (0 : ℝ) 1)
  (hφ : Continuous φ) (hφinj : Function.Injective φ)

/-- The carrier preimage of the handle end under the cylinder end is the attach image:
a cylinder point mapping into the handle range must come from `range φ`. -/
theorem fromCyl_preimage_range_fromHandle_subset :
    (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl ⁻¹'
        (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle)
      ⊆ Set.range φ := by
  intro b hb
  by_contra hbφ
  exact Set.disjoint_left.mp
    (fromCyl_image_compl_disjoint_range_fromHandle
      (HA := ktHandleAttachment s.M D5 S hS φ hφ hφinj))
    ⟨b, hbφ, rfl⟩ hb

variable {s S hS φ hφ hφinj} in
/-- **Forcing step 1 — the attached top face is supported in the CLOSED attach image.**
`htransfer` transports `wAtt`'s support through the injective pushforwards into
`fromCyl⁻¹(range fromHandle) ⊆ range φ`. -/
theorem wAtt_mem_subspaceChains_range_phi
    {z : cycles (TopCat.of s.M) (2 + 2)}
    {cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2)}
    (T : CapstoneSeamTransfer s S hS φ hφ hφinj z cHa) :
    T.wAtt ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
      (Set.range φ) (3 + 1) := by
  have hmem : closedEmbeddingChain
      (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
      (3 + 1) T.wAtt
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
        (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle) (3 + 1) := by
    rw [T.htransfer]
    exact closedEmbeddingChain_mem_subspaceChains
      (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
      (3 + 1) T.uAtt
  rw [closedEmbeddingChain_eq_mapChain] at hmem
  exact subspaceChains_mono (fromCyl_preimage_range_fromHandle_subset s S hS φ hφ hφinj) (3 + 1)
    (mem_subspaceChains_of_mapChain_mem _
      (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl_injective hmem)

variable {s S hS φ hφ hφinj} in
/-- The top face of the cycle `z` is a cycle (functoriality). Stated at the `.B` spelling
the split pieces carry; proven at the `cyl` spelling and bridged by defeq. -/
theorem boundary_topFace_eq_zero
    (z : cycles (TopCat.of s.M) (2 + 2)) :
    chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) 3
      (mapChain (slice (graphHom (TopCat.of s.M)) 1) (3 + 1)
        (z : SingularChain (TopCat.of s.M) (3 + 1))) = 0 := by
  have hz : chainBoundary (TopCat.of s.M) 3 (z : SingularChain (TopCat.of s.M) (3 + 1)) = 0 :=
    LinearMap.mem_ker.mp z.2
  have h1 := chainBoundary_mapChain (X := TopCat.of s.M)
    (Y := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (n := 3)
    (slice (graphHom (TopCat.of s.M)) 1) (z : SingularChain (TopCat.of s.M) (3 + 1))
  exact h1.trans (by rw [hz, map_zero])

variable {s S hS φ hφ hφinj} in
/-- **Forcing step 2 — the attached piece is a cycle.** `∂wAtt + ∂wOut = ∂(z@⊤) = 0`, and the
common value `∂wAtt = ∂wOut` is supported in both the attach image and (a subset of) its
complement — hence zero (`subspaceChains_inf_compl_eq_bot`). -/
theorem boundary_wAtt_eq_zero
    {z : cycles (TopCat.of s.M) (2 + 2)}
    {cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2)}
    (T : CapstoneSeamTransfer s S hS φ hφ hφinj z cHa) :
    chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) 3 T.wAtt = 0 := by
  have hsum : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) 3 T.wAtt
      + chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) 3 T.wOut = 0 := by
    have hsplit := congrArg
      (⇑(chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) 3)) T.hsplit
    have hadd := map_add
      (chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) 3) T.wAtt T.wOut
    exact hadd.symm.trans (hsplit.symm.trans (boundary_topFace_eq_zero z))
  have heq : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) 3 T.wAtt
      = chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) 3 T.wOut := by
    calc chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) 3 T.wAtt
        = chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) 3 T.wAtt
          + (chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) 3 T.wOut
            + chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) 3 T.wOut)
          := by rw [ZModModule.add_self, add_zero]
      _ = (chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) 3 T.wAtt
            + chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) 3 T.wOut)
          + chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) 3 T.wOut
          := by rw [add_assoc]
      _ = chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) 3 T.wOut
          := by rw [hsum, zero_add]
  have hA : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) 3 T.wAtt
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
        (Set.range φ) 3 :=
    chainBoundary_mem_subspaceChains
      (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (Set.range φ) 3 T.wAtt
      (wAtt_mem_subspaceChains_range_phi T)
  have hO : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) 3 T.wAtt
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
        ((Set.range φ)ᶜ) 3 := by
    rw [heq]
    refine subspaceChains_mono
      (Set.diff_subset_compl (Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1))) (Set.range φ)) 3 ?_
    exact chainBoundary_mem_subspaceChains
      (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
      ((Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1))) \ Set.range φ) 3 T.wOut T.hwOut
  have hbot : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) 3 T.wAtt
      ∈ (⊥ : Submodule (ZMod 2)
        (SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) 3)) := by
    rw [← subspaceChains_inf_compl_eq_bot
      (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (U := Set.range φ) 3]
    exact ⟨hA, hO⟩
  simpa using hbot

variable {s S hS φ hφ hφinj} in
/-- The un-attached piece is a cycle too (char 2, from `wAtt`'s and the split). -/
theorem boundary_wOut_eq_zero
    {z : cycles (TopCat.of s.M) (2 + 2)}
    {cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2)}
    (T : CapstoneSeamTransfer s S hS φ hφ hφinj z cHa) :
    chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) 3 T.wOut = 0 := by
  have hsum : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) 3 T.wAtt
      + chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) 3 T.wOut = 0 := by
    have hsplit := congrArg
      (⇑(chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) 3)) T.hsplit
    have hadd := map_add
      (chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) 3) T.wAtt T.wOut
    exact hadd.symm.trans (hsplit.symm.trans (boundary_topFace_eq_zero z))
  rw [boundary_wAtt_eq_zero T, zero_add] at hsum
  exact hsum

/-! ## §2. The uninhabitability

If seam-supported 4-cycles bound, off-seam-supported 4-cycles bound, and `z@⊤` does NOT
bound (the genuine consumption: `z` fundamental, the attach region a proper compact piece),
then no transfer datum exists. The hypotheses are honest homological facts about the two
REGIONS — they never mention the transfer, so nothing here is circular. -/

variable {s S hS φ hφ hφinj} in
/-- **THE SEAM-TRANSFER NO-GO.** The as-shipped open-complement transfer shape is
uninhabitable on any homologically nontrivial top face with null support regions. This is
the kernel adjudication of the three-block wall (#198/#204/#207): the barrier was not a
machinery gap — the shape itself is impossible. -/
theorem isEmpty_capstoneSeamTransfer_of_null
    {z : cycles (TopCat.of s.M) (2 + 2)}
    {cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2)}
    (hA : ∀ w : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1),
      w ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
        (Set.range φ) (3 + 1) →
      chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) 3 w = 0 →
      ∃ b : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 2),
        chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1) b = w)
    (hO : ∀ w : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1),
      w ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
        ((Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1))) \ Set.range φ) (3 + 1) →
      chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) 3 w = 0 →
      ∃ b : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 2),
        chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1) b = w)
    (hne : ¬ ∃ b : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 2),
      chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1) b
        = mapChain (slice (graphHom (TopCat.of s.M)) 1) (3 + 1)
            (z : SingularChain (TopCat.of s.M) (3 + 1))) :
    IsEmpty (CapstoneSeamTransfer s S hS φ hφ hφinj z cHa) := by
  refine ⟨fun T => hne ?_⟩
  obtain ⟨bA, hbA⟩ := hA T.wAtt (wAtt_mem_subspaceChains_range_phi T) (boundary_wAtt_eq_zero T)
  obtain ⟨bO, hbO⟩ := hO T.wOut T.hwOut (boundary_wOut_eq_zero T)
  refine ⟨bA + bO, ?_⟩
  have hadd := map_add
    (chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)) bA bO
  have hsum : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)
      bA + chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1) bO
      = T.wAtt + T.wOut := congrArg₂ (· + ·) hbA hbO
  exact (hadd.trans hsum).trans T.hsplit.symm

variable {s S hS φ hφ hφinj} in
/-- **The shared-cSeam corollary**: the round-13-audited `CapstoneSeamTransferSeam` (the
single-shared-field refactor) is equally uninhabitable — its `toTransfer` would inhabit the
dead shape. The 3×-circled "closed-S co-adaptation barrier" was the shadow of this
impossibility, not a missing engine. -/
theorem isEmpty_capstoneSeamTransferSeam_of_null
    [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M]
    {z : cycles (TopCat.of s.M) (2 + 2)}
    {cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2)}
    (hA : ∀ w : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1),
      w ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
        (Set.range φ) (3 + 1) →
      chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) 3 w = 0 →
      ∃ b : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 2),
        chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1) b = w)
    (hO : ∀ w : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1),
      w ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
        ((Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1))) \ Set.range φ) (3 + 1) →
      chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) 3 w = 0 →
      ∃ b : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 2),
        chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1) b = w)
    (hne : ¬ ∃ b : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 2),
      chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1) b
        = mapChain (slice (graphHom (TopCat.of s.M)) 1) (3 + 1)
            (z : SingularChain (TopCat.of s.M) (3 + 1))) :
    IsEmpty (CapstoneSeamTransferSeam s S hS φ hφ hφinj z cHa) := by
  refine ⟨fun R => ?_⟩
  exact (isEmpty_capstoneSeamTransfer_of_null hA hO hne).false
    (CapstoneSeamTransferSeam.toTransfer s S hS φ hφ hφinj R)

end

end PinPlusTraceSeamTransferNoGo
end SKEFTHawking
