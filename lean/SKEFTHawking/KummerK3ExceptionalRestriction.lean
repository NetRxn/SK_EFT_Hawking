/-
# Phase 5q.H — the `⟨−2⟩¹⁶` block, moved onto the PIECES

`KummerK3ExceptionalBlock.ExceptionalBlockGram` is the E-lane's whole target: cap-duals `α c` for the
16 exceptional classes whose Kronecker table is `−2` on the diagonal and `0` off it. Stated on `K3`
it is a 16 × 16 table of pairings in `H²(K3;ℤ) × H₂(K3;ℤ)` — 256 obligations against a rank-22 group.

This module moves every one of them onto the *piece*. The mechanism is one identity, not an
approximation: `excClass c` is by definition the pushforward `(eCopyC c)₊ eGen`
(`KummerK3ExceptionalClasses.excClass_def`), so the integral Kronecker adjunction
`⟨φ*ω, β⟩ = ⟨ω, φ₊β⟩` (`SingularCohomologyFunctorialityInt.kroneckerHInt_cohomologyPullbackInt`)
rewrites the `(c, d)` entry as

    ⟨α d, E_c⟩  =  ⟨(eCopyC c)* (α d), eGen⟩

— a pairing **on the `c`-th resolution piece**, against the *single* generator of `H₂(E;ℤ)`
(`span_eGen`). So the 16 × 16 table is exactly 16 × 16 evaluations of restricted classes on one
generator, and the geometry only ever has to be done one piece at a time.

Two consequences worth having separately:

* **§2 — the reduction is an equivalence at the level of the pairings** (`excBlockEntry_restrict` is
  an equality, so nothing is lost or added in moving to the pieces);
* **§3 — the natural geometric sufficient condition**: `α d` restricting to **zero** on the `c`-th
  piece for `c ≠ d` kills the off-diagonal outright. This is how the geometry actually supplies it —
  `α d` is dual to `E_d`, supported near the `d`-th piece — and it is strictly stronger than the
  pairing statement, so it is recorded as a criterion, not as the obligation.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/
import Mathlib
import SKEFTHawking.KummerK3ExceptionalBlock
import SKEFTHawking.SingularCohomologyFunctorialityInt

namespace SKEFTHawking.KummerK3ExceptionalRestriction

open scoped SKEFTHawking.KummerK3E1Package
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularCohomologyFunctorialityInt
open SKEFTHawking.KummerWeld (KummerK3 EIndex)
open SKEFTHawking.KummerK7Opener (KummerK3top)
open SKEFTHawking.KummerK3E1Package
open SKEFTHawking.KummerK3ExceptionalClasses
open SKEFTHawking.KummerK3ExceptionalBlock

noncomputable section

/-! ## §1. The restriction of an ambient class to the `c`-th piece -/

/-- **The restriction of `ω ∈ H²(K3;ℤ)` to the `c`-th resolution piece.** -/
def restrictToPiece (c : EIndex) (ω : Cohomology KummerK3top 2) : Cohomology EtopR 2 :=
  cohomologyPullbackInt (eCopyC c) 2 ω

/-! ## §2. THE ENTRY IDENTITY — every block entry is a pairing on one piece -/

/-- **THE REDUCTION, as an equality.** The `(c, d)` entry of the E-block table equals the pairing of
`α d`'s restriction to the `c`-th piece against that piece's `H₂` generator. Immediate from
`excClass_def` and the integral Kronecker adjunction — but it is what turns a 256-entry obligation on
a rank-22 group into 256 evaluations of restricted classes on a *single* generator. -/
theorem excBlockEntry_restrict (c : EIndex) (ω : Cohomology KummerK3top 2) :
    kroneckerHInt 2 ω (excClass c) = kroneckerHInt 2 (restrictToPiece c ω) eGen := by
  rw [excClass_def, restrictToPiece, kroneckerHInt_cohomologyPullbackInt]

/-- **The E-block obligation, restated on the pieces.** Same content as `ExceptionalBlockGram` by
§2's equality; every quantity now lives on a single resolution piece. -/
def ExceptionalBlockRestricted (o : IntOrientation KummerK3) : Prop :=
  ∃ α : EIndex → Cohomology KummerK3top 2,
    (∀ c, capHInt 2 1 (α c) o.fundClass = excClass c) ∧
      (∀ c, kroneckerHInt 2 (restrictToPiece c (α c)) eGen = -2) ∧
      (∀ c d, c ≠ d → kroneckerHInt 2 (restrictToPiece c (α d)) eGen = 0)

/-- **The restricted form DELIVERS `ExceptionalBlockGram`.** -/
theorem exceptionalBlockGram_of_restricted (o : IntOrientation KummerK3)
    (h : ExceptionalBlockRestricted o) : ExceptionalBlockGram o := by
  obtain ⟨α, hcap, hdiag, hoff⟩ := h
  refine ⟨α, hcap, fun c => ?_, fun c d hcd => ?_⟩
  · rw [excBlockEntry_restrict]; exact hdiag c
  · rw [excBlockEntry_restrict]; exact hoff c d hcd

/-- **…and conversely** — so §2 really is a change of venue, not a strengthening. Recorded in both
directions so that a later reader cannot mistake the piece-local form for a weaker obligation. -/
theorem exceptionalBlockRestricted_of_gram (o : IntOrientation KummerK3)
    (h : ExceptionalBlockGram o) : ExceptionalBlockRestricted o := by
  obtain ⟨α, hcap, hdiag, hoff⟩ := h
  refine ⟨α, hcap, fun c => ?_, fun c d hcd => ?_⟩
  · rw [← excBlockEntry_restrict]; exact hdiag c
  · rw [← excBlockEntry_restrict]; exact hoff c d hcd

/-- The two forms are the same obligation. -/
theorem exceptionalBlockRestricted_iff (o : IntOrientation KummerK3) :
    ExceptionalBlockRestricted o ↔ ExceptionalBlockGram o :=
  ⟨exceptionalBlockGram_of_restricted o, exceptionalBlockRestricted_of_gram o⟩

/-! ## §3. The geometric sufficient condition for the off-diagonal

`α d` is dual to `E_d` and is supplied by the geometry supported near the `d`-th piece; on a
*different* piece it restricts to zero. That is strictly stronger than "the pairing vanishes", so it
is recorded as a criterion feeding §2, never as the obligation itself. -/

/-- **Disjoint support kills the off-diagonal.** If `α d` restricts to `0` on the `c`-th piece then
the `(c, d)` entry vanishes — no computation on `K3` required. -/
theorem offDiagonal_of_restrict_eq_zero {c d : EIndex} {α : EIndex → Cohomology KummerK3top 2}
    (h : restrictToPiece c (α d) = 0) : kroneckerHInt 2 (α d) (excClass c) = 0 := by
  rw [excBlockEntry_restrict, h, map_zero]
  rfl

/-- **The block from ONE diagonal fact per piece plus disjoint support.** The E-lane's obligation in
the shape the geometry supplies it: a cap-dual family, the `−2` self-pairing computed *on the piece*,
and vanishing restriction across distinct pieces. -/
theorem exceptionalBlockGram_of_pieceLocal (o : IntOrientation KummerK3)
    (α : EIndex → Cohomology KummerK3top 2)
    (hcap : ∀ c, capHInt 2 1 (α c) o.fundClass = excClass c)
    (hdiag : ∀ c, kroneckerHInt 2 (restrictToPiece c (α c)) eGen = -2)
    (hsupp : ∀ c d, c ≠ d → restrictToPiece c (α d) = 0) :
    ExceptionalBlockGram o :=
  exceptionalBlockGram_of_restricted o
    ⟨α, hcap, hdiag, fun c d hcd => by rw [hsupp c d hcd, map_zero]; rfl⟩

/-! ## §4. Non-vacuity of the piece-local shape

The zero-geometric-input attack, run against §3's shape rather than §2's: an all-zero `α` satisfies
`hsupp` trivially, so `hsupp` alone is vacuous — but it cannot satisfy `hdiag`, because `−2 ≠ 0`.
The diagonal is the load-bearing conjunct and it is a *nonvanishing* assertion about the restriction
to each individual piece. -/

/-- **The diagonal forces every restriction to be nonzero on its own piece.** So `hdiag` is not
satisfiable by a degenerate family, and in particular the all-zero `α` — which trivially satisfies
`hsupp` — is excluded. -/
theorem restrictToPiece_ne_zero_of_diagonal {c : EIndex} {α : EIndex → Cohomology KummerK3top 2}
    (hdiag : kroneckerHInt 2 (restrictToPiece c (α c)) eGen = -2) :
    restrictToPiece c (α c) ≠ 0 := by
  intro h
  rw [h] at hdiag
  simp only [map_zero] at hdiag
  exact absurd hdiag (by decide)

/-- **…and hence that `eGen` itself survives**: a class pairing to `−2` against `eGen` cannot exist if
`eGen = 0`. Together with `KummerK3ExceptionalBlock.excClass_ne_zero_of_block` this pins that the
obligation asserts genuine content on both sides of the pairing. -/
theorem eGen_ne_zero_of_diagonal {c : EIndex} {α : EIndex → Cohomology KummerK3top 2}
    (hdiag : kroneckerHInt 2 (restrictToPiece c (α c)) eGen = -2) :
    (eGen : Homology EtopR 2) ≠ 0 := by
  intro h
  rw [h] at hdiag
  simp only [map_zero] at hdiag
  exact absurd hdiag (by decide)

/-! ## §5. WHAT THE BLOCK BUYS: the 16 exceptional classes are ℤ-INDEPENDENT

The `⟨−2⟩¹⁶` name is only honest if the 16 classes actually span a rank-16 sublattice; a family of
16 classes with that pairing table but a relation among them would not be a `⟨−2⟩¹⁶` block at all.
The block data forces independence outright, by the standard dual-basis argument: pair a putative
relation with `α d` and every term but the `d`-th dies, leaving `−2 · g d = 0`.

This is the E-lane's *payload*, and it is what the 22-selection needs in order to have full rank —
`KummerK3ExceptionalBlock.excClass_ne_zero_of_block` is the rank-1 shadow of it. -/

/-- **The block forces ℤ-linear independence of the 16 exceptional classes.** -/
theorem linearIndependent_excClass_of_block (o : IntOrientation KummerK3)
    (h : ExceptionalBlockGram o) : LinearIndependent ℤ (excClass : EIndex → _) := by
  obtain ⟨α, _, hdiag, hoff⟩ := h
  rw [Fintype.linearIndependent_iff]
  intro g hg d
  -- Pair the relation with `α d`; every off-diagonal term vanishes.
  have hpair : (kroneckerHInt 2 (α d)) (∑ c, g c • excClass c) = 0 := by
    rw [hg, map_zero]
  rw [map_sum] at hpair
  simp only [map_smul, smul_eq_mul] at hpair
  rw [Finset.sum_eq_single d (fun c _ hcd => by rw [hoff c d hcd, mul_zero])
      (fun hd => absurd (Finset.mem_univ d) hd)] at hpair
  rw [hdiag d] at hpair
  omega

/-- **…hence the 16 span a rank-16 free sublattice of `H₂(K3;ℤ)`** — stated as the submodule they
generate being free of rank 16, the form the 22-selection consumes. -/
theorem finrank_span_excClass_of_block (o : IntOrientation KummerK3)
    (h : ExceptionalBlockGram o) :
    Module.finrank ℤ (Submodule.span ℤ (Set.range (excClass : EIndex → _))) =
      Fintype.card EIndex :=
  finrank_span_eq_card (linearIndependent_excClass_of_block o h)

end

end SKEFTHawking.KummerK3ExceptionalRestriction
