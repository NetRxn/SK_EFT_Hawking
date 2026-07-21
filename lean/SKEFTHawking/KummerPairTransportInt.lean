import Mathlib
import SKEFTHawking.SingularRelativeFiniteProdSplitInt
import SKEFTHawking.KummerPairTubeSeparation

/-!
# The pair-level transport `(ESub, S) → 16 × (ResE, Sᵢ)` — integrally

`KummerK7MVAssembly.eImageHomeo : (EIndex × ResE) ≃ₜ ↥eImage` says the exceptional set is sixteen
disjoint resolution pieces. On **absolute** integral homology that already splits
(`SingularFiniteProdDiscreteHnInt.eIndexProdHnEquivInt`, feeding
`KummerK7MVAssembly.eImageH2EquivInt : H₂(eImage; ℤ) ≅ ℤ¹⁶`).

The `b₂` residual, however, lives in the **pair** `(ESub, CollarInE)`
(`KummerPairTubeSeparation.PairH2`), and the collar is an *arbitrary* subspace of `ESub` with no
product structure. The absolute split cannot see it, and the mod-2 relative split
(`SingularRelativeDisjointUnionHn`) cannot see its ℤ-summands. The new integral relative engine
(`SingularRelativeClopenSplitInt` → `SingularRelativeFiniteProdSplitInt`) closes exactly that gap;
this module applies it:

`esubPairSplitInt : Hₙ(ESub, S; ℤ) ≅ (∀ i : EIndex, Hₙ(ResE, Sᵢ; ℤ))`

for **any** subspace `S ⊆ ESub`, with `Sᵢ = {y : ResE | eImageHomeo (i, y) ∈ S}` the `i`-th piece's
induced subspace. Specialised to `S = CollarInE` and `n = 2` this is
`pairH2SplitInt : PairH2 ≅ (∀ i, H₂(ResE, collarᵢ; ℤ))` — the sixteen per-piece relative groups the
`Halvable` witnesses of `KummerPairHalving.pairH2TwoTorsionFree_iff_exceptional_halvable` live in.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new axiom, no
`native_decide`, no `maxHeartbeats`.
-/

open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.KummerResolutionPiece (ResE)
open SKEFTHawking.KummerWeld (EIndex)
open SKEFTHawking.KummerK7MVAssembly (eImageHomeo)
open SKEFTHawking.KummerPairTubeSeparation (ESub CollarInE PairH2)
open SKEFTHawking.SingularRelativeFiniteProdSplitInt (relHomologyCongrInt eIndexProdRelHnEquivInt)

namespace SKEFTHawking.KummerPairTransportInt

noncomputable section

/-- The resolution piece as an ambient space. -/
abbrev ResEtop : TopCat := TopCat.of ResE

/-- The sixteen-fold product as an ambient space. -/
abbrev ProdTop : TopCat := TopCat.of (EIndex × ResE)

/-- The subspace of `EIndex × ResE` corresponding to a subspace `S` of `ESub`. -/
def pull (S : Set ↥ESub) : Set ↑ProdTop := {p | eImageHomeo p ∈ S}

/-- The `i`-th resolution piece's induced subspace. -/
def pieceSub (S : Set ↥ESub) (i : EIndex) : Set ↑ResEtop := {y | eImageHomeo (i, y) ∈ S}

/-- **The pair-level transport across the sixteen resolution pieces**
`Hₙ(ESub, S; ℤ) ≅ (∀ i : EIndex, Hₙ(ResE, Sᵢ; ℤ))`, for an **arbitrary** subspace `S ⊆ ESub`.

The two ingredients are the homeomorphism `eImageHomeo` (transported by `relHomologyCongrInt`, the
relative mirror of the absolute development's `homologyCongrInt`) and the integral **relative**
finite disjoint-union splitting `eIndexProdRelHnEquivInt`, which is what the on-main pair could not
supply. -/
def esubPairSplitInt (S : Set ↥ESub) (n : ℕ) :
    RelHomologyInt (X := ESub) S n
      ≃ₗ[ℤ] (∀ i : EIndex, RelHomologyInt (pieceSub S i) n) :=
  (relHomologyCongrInt (X := ESub) (Y := ProdTop) eImageHomeo.symm
      (B := pull S)
      (fun x => by
        show eImageHomeo (eImageHomeo.symm x) ∈ S ↔ x ∈ S
        rw [Homeomorph.apply_symm_apply]) n).trans
    (eIndexProdRelHnEquivInt ResEtop (pull S) n)

/-- **The `b₂`-residual group, split into its sixteen per-piece factors**:
`PairH2 = H₂(ESub, CollarInE; ℤ) ≅ (∀ i : EIndex, H₂(ResE, collarᵢ; ℤ))`.

`KummerPairHalving.pairH2TwoTorsionFree_iff_exceptional_halvable` reduces the `b₂` target to sixteen
`Halvable (exceptional i)` witnesses; this equivalence is the statement that those sixteen witnesses
really are sixteen *independent, per-piece* relative-homology facts about one `ResE` at a time —
the pair-level counterpart of the absolute `eImageH2EquivInt : H₂(eImage; ℤ) ≅ ℤ¹⁶`. -/
def pairH2SplitInt :
    PairH2 ≃ₗ[ℤ] (∀ i : EIndex, RelHomologyInt (pieceSub CollarInE i) 2) :=
  esubPairSplitInt CollarInE 2

/-- **Two-torsion-freeness is per-piece.** `PairH2TwoTorsionFree` holds iff each of the sixteen
per-piece relative groups `H₂(ResE, collarᵢ; ℤ)` is 2-torsion-free — the transport turned a global
statement about the 16-fold exceptional set into sixteen statements about a single resolution piece.
This is the pair-level analogue of `KummerPairHalving.pairH2TwoTorsionFree_iff_exceptional_halvable`
(which reduced the *witnesses* to 16) and is what makes a per-piece geometric construction on `ResE`
sufficient for the whole `b₂` target. -/
theorem pairH2TwoTorsionFree_iff_pieces :
    SKEFTHawking.KummerPairTubeSeparation.PairH2TwoTorsionFree
      ↔ ∀ (i : EIndex) (m : RelHomologyInt (pieceSub CollarInE i) 2),
          (2 : ℤ) • m = 0 → m = 0 := by
  classical
  constructor
  · intro h i m hm
    set w : ∀ j : EIndex, RelHomologyInt (pieceSub CollarInE j) 2 := Pi.single i m with hw
    have hker : (2 : ℤ) • pairH2SplitInt.symm w = 0 := by
      apply pairH2SplitInt.injective
      rw [map_smul, map_zero, LinearEquiv.apply_symm_apply]
      funext j
      show (2 : ℤ) • w j = 0
      rw [hw]
      by_cases hij : j = i
      · subst hij; simpa using hm
      · simp [Pi.single_apply, hij]
    have hv0 := h _ hker
    have hzero : w = 0 := by
      rw [← LinearEquiv.apply_symm_apply pairH2SplitInt w, hv0, map_zero]
    have := congrFun hzero i
    rw [hw] at this
    simpa using this
  · intro h v hv
    apply pairH2SplitInt.injective
    rw [map_zero]
    funext i
    refine h i _ ?_
    have := congrArg pairH2SplitInt hv
    rw [map_smul, map_zero] at this
    exact congrFun this i

end

end SKEFTHawking.KummerPairTransportInt
