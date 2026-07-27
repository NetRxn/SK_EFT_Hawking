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
import SKEFTHawking.SingularRelativeCoverMVTransport
import SKEFTHawking.SingularRelativeDisjointUnionFundClass

open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularRelativeCoverMV
open SKEFTHawking.SingularRelativeCoverMVTransport
open SKEFTHawking.SingularRelativeDisjointUnionFundClass
open SKEFTHawking.SingularExcisionIso (restr excisionMap)
open SKEFTHawking.PoincareLefschetzRelFundClass (restrictBd RestrictsToRelGen)

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

/-! ## §2. A FACE-FLAT PIECE CANNOT DETECT — the partition/split refutation core -/

/-- **THE FACE COMPANION OF `restrictBd_excisionMap_eq_zero`.** The banked
`SingularRelativeDisjointUnionLocal.restrictBd_excisionMap_eq_zero` kills a piece's contribution at a
point the piece MISSES (`x ∉ U`). This kills it at a point the piece CONTAINS but only in its own
boundary face: if the intrinsic local homology of `U` vanishes at `x ∈ U`, then **every** class
`α ∈ H_{m+2}(U, S ∩ U)` pushes forward to something that restricts to `0` at `x`.

Proof: represent `α` by a chain (`exists_relClassOf_rep`), push it forward (`relClassOf_chainIncl`),
restrict (`restrictBd_relClassOf`) — and the resulting local class is `0` because the chain is
supported in `U` (§1). -/
theorem restrictBd_excisionMap_eq_zero_of_faceVanish {X : TopCat} {S U : Set ↑X} {x : ↑X}
    (hxU : x ∈ U) (hxS : x ∉ S) {m : ℕ}
    (hvanish : ∀ β : RelativeHomology ({(⟨x, hxU⟩ : ↥U)}ᶜ : Set ↑(sub U)) (m + 2), β = 0)
    (α : RelativeHomology (restr S U) (m + 2)) :
    restrictBd S hxS (m + 2) (excisionMap S U (m + 2) α) = 0 := by
  obtain ⟨c', hc', rfl⟩ := exists_relClassOf_rep (X := sub U) (restr S U) m α
  rw [← relClassOf_chainIncl (X := X) S U m c' hc', restrictBd_relClassOf]
  exact relClassOf_eq_zero_of_subspace_of_faceVanish hxU hvanish _ ⟨c', rfl⟩ _

/-- **A FACE-FLAT PIECE CANNOT CARRY A DETECTING CLASS — the refutation.** `RestrictsToRelGenOn`
demands `restrictBd S hx α = (gen x hx).symm 1`, which is NONZERO (`gen` is a linear equivalence onto
`ℤ/2`). At a point `x` that the piece `U` contains only in its own boundary face — where the
intrinsic local homology of `U` vanishes — the left-hand side is `0` by
`restrictBd_excisionMap_eq_zero_of_faceVanish`. So no excision-pushforward from `U` can detect there,
for **any** `α`.

This is the kernel-encodable core of the `capstone-binary-partition-detection-uninhabitable` record:
a binary complementary split `{U, Uᶜ}` of a connected `W` has a closed piece whose frontier contains
`W`-interior points, and detection is demanded there. Note the statement is a genuine refutation, not
a vacuity: `gen` is *given* as an equivalence onto `ℤ/2`, so `(gen x hx).symm 1 ≠ 0` is forced. -/
theorem not_restrictsToRelGenOn_of_faceVanish {X : TopCat} {S U : Set ↑X} {x : ↑X}
    (hxU : x ∈ U) (hxS : x ∉ S) {m : ℕ}
    (gen : ∀ y : ↑X, y ∉ S → (RelativeHomology ({y}ᶜ) (m + 2) ≃ₗ[ZMod 2] ZMod 2))
    (hvanish : ∀ β : RelativeHomology ({(⟨x, hxU⟩ : ↥U)}ᶜ : Set ↑(sub U)) (m + 2), β = 0)
    (α : RelativeHomology (restr S U) (m + 2)) {P : ↑X → Prop} (hPx : P x) :
    ¬ RestrictsToRelGenOn S gen P (excisionMap S U (m + 2) α) := by
  intro H
  have h0 := restrictBd_excisionMap_eq_zero_of_faceVanish hxU hxS hvanish α
  rw [H x hxS hPx] at h0
  have h1 := congrArg (gen x hxS) h0
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.map_zero] at h1
  exact one_ne_zero h1

end

end SKEFTHawking.SingularFacePieceDetect
