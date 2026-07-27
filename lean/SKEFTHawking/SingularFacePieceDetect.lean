/-
# Phase 5q.H (#212) — §1 of the local-homology verdict: a chain supported in a face-flat subspace
has zero local class.

The generic mechanism by which "the boundary-face local homology of a piece vanishes" becomes "no
chain supported on that piece detects there": the excision map
`H_{m+2}(A, A∖x) → H_{m+2}(X, X∖x)` factors the class of an `A`-chain
(`SingularRelativeCoverMV.relClassOf_chainIncl`), so a vanishing source kills the class.

Split out from the carrier-level consumer (`…CollarPairSeamLocalHom`) because it is ambient-free and
reusable for any closed piece of any decomposition.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularRelativeCoverMV

open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularRelativeCoverMV

namespace SKEFTHawking.SingularFacePieceDetect

noncomputable section

/-- Vanishing of a relative homology transports across an equality of the relative subset. The
bookkeeping step that lets a statement proved at one description of the punctured set be used at a
propositionally equal one. -/
theorem relativeHomology_zero_congr {X : TopCat} {A B : Set ↑X} (hAB : A = B) (n : ℕ)
    (hz : ∀ β : RelativeHomology B n, β = 0) (α : RelativeHomology A n) : α = 0 := by
  cases hAB
  exact hz α

/-- **A CHAIN SUPPORTED IN A SUBSPACE WHOSE OWN LOCAL HOMOLOGY VANISHES HAS ZERO LOCAL CLASS.** If
`c` is an `A`-chain and the *intrinsic* local homology of `A` at `x ∈ A` vanishes, then the class of
`c` in `H_{m+2}(X, X∖x)` is `0`: `relClassOf_chainIncl` factors that class through the excision map
out of `H_{m+2}(A, A∖x)`, whose source is zero by hypothesis.

Applied at a boundary-face point (where the vanishing hypothesis is supplied by
`SingularFaceLocalHomologyVanish`), this says a piece meeting the point in its own boundary
contributes nothing to detection there. -/
theorem relClassOf_eq_zero_of_subspace_of_faceVanish {X : TopCat} {A : Set ↑X} {x : ↑X}
    (hxA : x ∈ A) {m : ℕ}
    (hvanish : ∀ β : RelativeHomology ({(⟨x, hxA⟩ : ↥A)}ᶜ : Set ↑(sub A)) (m + 2), β = 0)
    (c : SingularChain X (m + 2)) (hcA : c ∈ subspaceChains A (m + 2))
    (hbd : chainBoundary X (m + 1) c ∈ subspaceChains (X := X) ({x}ᶜ) (m + 1)) :
    relClassOf (X := X) ({x}ᶜ) m c hbd = 0 := by
  obtain ⟨c', rfl⟩ := hcA
  have hbdIncl : chainIncl A (m + 1) (chainBoundary (sub A) (m + 1) c')
      ∈ subspaceChains (X := X) ({x}ᶜ) (m + 1) := by
    rw [chainIncl_chainBoundary]; exact hbd
  have hbd' : chainBoundary (sub A) (m + 1) c'
      ∈ subspaceChains (SingularExcisionIso.restr (X := X) ({x}ᶜ) A) (m + 1) :=
    (SingularExcisionIso.chainIncl_mem_subspaceChains_iff ({x}ᶜ) A _).mp hbdIncl
  have hzero : ∀ β : RelativeHomology (SingularExcisionIso.restr (X := X) ({x}ᶜ) A) (m + 2),
      β = 0 := by
    refine relativeHomology_zero_congr (B := (({(⟨x, hxA⟩ : ↥A)}ᶜ) : Set ↑(sub A))) ?_ (m + 2)
      hvanish
    ext p
    simp only [SingularExcisionIso.restr, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff, Subtype.ext_iff]
  rw [relClassOf_chainIncl (X := X) ({x}ᶜ) A m c' hbd',
    hzero (relClassOf (SingularExcisionIso.restr (X := X) ({x}ᶜ) A) m c' hbd'), map_zero]

end

end SKEFTHawking.SingularFacePieceDetect
