/-
# Phase 5q.H — the K3 E1 ledger with the lattice input DISCHARGED

`PlaneReductionDescent.stableNegRank16Two_holds` proves `StableNegRank16Two` outright (via
`PlaneReduction → UnitCancellation → StableNegRank16Two`, all four Eichler transvections realised by
actual isometries and the residual `AxisReturnBound` discharged by `axisReturnBound`). Every
consumer in the Kummer chain therefore loses its `hstable` hypothesis. This file is exactly that
substitution — no new mathematics, one hypothesis fewer everywhere.

The K3 lane's E1 ledger before this file:

    hstable  (pure lattice theory)  +  ONE geometric datum

and after it:

    ONE geometric datum.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/
import Mathlib
import SKEFTHawking.PlaneReductionDescent
import SKEFTHawking.KummerK3EvenFromSpanningFamily

namespace SKEFTHawking.KummerK3E1Unconditional

open scoped SKEFTHawking.KummerK3E1Package
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.KummerWeld (KummerK3)
open SKEFTHawking.KummerK7Opener (KummerK3top)
open SKEFTHawking.KummerK3E1Package
open SKEFTHawking.SpinSigmaRoute (k3Form)
open SKEFTHawking.LatticeSigFullRank
open SKEFTHawking.KummerK3GramFromLattice
open SKEFTHawking.KummerK3GeometricFamily
open SKEFTHawking.KummerK3CapDualFamily
open SKEFTHawking.KummerK3EvenFromSpanningFamily

/-! ## §1. The lattice consumer -/

/-- **`IntCongr M k3Form` for ANY even unimodular rank-22 form of signature `−16`, unconditionally.**
`UnitBlockCancellation.hk3_of_stable16_two` with its single hypothesis discharged. -/
theorem hk3_holds (M : Matrix (Fin 22) (Fin 22) ℤ) (heu : IsEvenUnimodular M)
    (hsig : latticeSig M = -16) : IntCongr M k3Form :=
  hk3_of_stable16_two stableNegRank16Two_holds M heu hsig

/-! ## §2. The welded Kummer `K3`'s E1 atoms, at each of the four supply shapes

Four entry points, in increasing order of how little the geometric side has to supply. Each is the
corresponding `*_of_stable_*` theorem with `hstable` removed. -/

/-- **The welded `K3`'s Gram congruence, per orientation, unconditionally.** -/
theorem kummerK3_hk3_holds
    (o : IntOrientation KummerK3) (heu : IsEvenUnimodular (kummerK3Gram o))
    (hsig : latticeSig (kummerK3Gram o) = -16) : IntCongr (kummerK3Gram o) k3Form :=
  kummerK3_hk3_of_stable stableNegRank16Two_holds o heu hsig

/-- **E1 atoms from the two Gram facts, unconditionally.** -/
theorem nonempty_kummerK3E1Atoms_of_gramFacts
    (heu : ∀ o : IntOrientation KummerK3, IsEvenUnimodular (kummerK3Gram o))
    (hsig : ∀ o : IntOrientation KummerK3, latticeSig (kummerK3Gram o) = -16) :
    Nonempty KummerK3E1Atoms :=
  nonempty_kummerK3E1Atoms_of_stable stableNegRank16Two_holds heu hsig

/-- **E1 atoms from the three geometric inputs `hpd`, `heven`, `hfam` — unconditionally.** -/
theorem nonempty_kummerK3E1Atoms_of_geometric
    (hpd : ∀ o : IntOrientation KummerK3,
      Nonempty (IntPoincareDuality (intFundamentalClassOfIntOrientation o)))
    (heven : ∀ (o : IntOrientation KummerK3) (a : Cohomology KummerK3top 2),
      (2 : ℤ) ∣ interFormInt (intFundamentalClassOfIntOrientation o) a a)
    (hfam : ∀ o : IntOrientation KummerK3, ∃ v : Fin 22 → Cohomology KummerK3top 2,
      ∀ i j, interFormInt (intFundamentalClassOfIntOrientation o) (v i) (v j)
        = kummerSubForm i j) :
    Nonempty KummerK3E1Atoms :=
  nonempty_kummerK3E1Atoms_of_stable_of_geometric stableNegRank16Two_holds hpd heven hfam

/-- **E1 atoms with `hfam` weakened to a nondegenerate signature-`−16` family — unconditionally.** -/
theorem nonempty_kummerK3E1Atoms_of_geometric_nondegenerate
    (hpd : ∀ o : IntOrientation KummerK3,
      Nonempty (IntPoincareDuality (intFundamentalClassOfIntOrientation o)))
    (heven : ∀ (o : IntOrientation KummerK3) (a : Cohomology KummerK3top 2),
      (2 : ℤ) ∣ interFormInt (intFundamentalClassOfIntOrientation o) a a)
    (hfamGen : ∀ o : IntOrientation KummerK3, ∃ (G : Matrix (Fin 22) (Fin 22) ℤ)
        (v : Fin 22 → Cohomology KummerK3top 2),
        (∀ i j, interFormInt (intFundamentalClassOfIntOrientation o) (v i) (v j) = G i j)
          ∧ G.det ≠ 0 ∧ latticeSig G = -16) :
    Nonempty KummerK3E1Atoms :=
  nonempty_kummerK3E1Atoms_of_stable_of_geometric_nondegenerate stableNegRank16Two_holds
    hpd heven hfamGen

/-- **E1 atoms from Wu-evenness plus ONE geometric datum — unconditionally.** -/
theorem nonempty_kummerK3E1Atoms_of_geoData
    (heven : ∀ (o : IntOrientation KummerK3) (a : Cohomology KummerK3top 2),
      (2 : ℤ) ∣ interFormInt (intFundamentalClassOfIntOrientation o) a a)
    (hgeo : ∀ o : IntOrientation KummerK3, ∃ (ι : Type) (a : ι → Cohomology KummerK3top 2)
        (c : ι → Homology KummerK3top 2) (sel : Fin 22 → ι),
        (∀ i, capHInt 2 1 (a i) o.fundClass = c i)
          ∧ Submodule.span ℤ (Set.range c) = ⊤
          ∧ ∀ i j, kroneckerHInt 2 (a (sel j)) (c (sel i)) = kummerSubForm i j) :
    Nonempty KummerK3E1Atoms :=
  nonempty_kummerK3E1Atoms_of_stable_of_geoData stableNegRank16Two_holds heven hgeo

/-- **THE TERMINAL E1 ENTRY POINT, UNCONDITIONAL.** The welded Kummer `K3`'s E1 atoms from ONE
geometric datum and nothing else: classes `a`, their cap-duals `c` spanning `H₂`, an even Kronecker
diagonal, and a selected 22 whose Kronecker table is `⟨−2⟩¹⁶ ⊕ 3H`. The lattice half of the ledger
— `StableNegRank16Two`, the only input that was not a statement about classes and cup products —
is gone, discharged by `stableNegRank16Two_holds`. -/
theorem nonempty_kummerK3E1Atoms_of_geoDataEven
    (hgeo : ∀ o : IntOrientation KummerK3, ∃ (ι : Type) (a : ι → Cohomology KummerK3top 2)
        (c : ι → Homology KummerK3top 2) (sel : Fin 22 → ι),
        (∀ i, capHInt 2 1 (a i) o.fundClass = c i)
          ∧ Submodule.span ℤ (Set.range c) = ⊤
          ∧ (∀ i, (2 : ℤ) ∣ kroneckerHInt 2 (a i) (c i))
          ∧ ∀ i j, kroneckerHInt 2 (a (sel j)) (c (sel i)) = kummerSubForm i j) :
    Nonempty KummerK3E1Atoms :=
  nonempty_kummerK3E1Atoms_of_stable_of_geoDataEven stableNegRank16Two_holds hgeo

end SKEFTHawking.KummerK3E1Unconditional
