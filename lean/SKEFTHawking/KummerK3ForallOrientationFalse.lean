/-
# ADJUDICATED: the K3 ledger's `∀ o` Gram hypothesis is FALSE

`KummerK3GramFromLattice.nonempty_kummerK3E1Atoms_of_stable_of_geometric` consumes

    hfam : ∀ o : IntOrientation KummerK3, ∃ v : Fin 22 → H²(K3;ℤ),
             ∀ i j, interFormInt (fundClass o) (v i) (v j) = kummerSubForm i j

quantified over **all** orientations with a **fixed** Gram. This module proves that hypothesis is
**unsatisfiable** — so every consumer taking it is vacuously true and cannot be discharged.

## The argument

1. `IntOrientationReverse.IntOrientation.reverse` is a genuine second orientation: `redCompat`
   cannot see a sign (reduction is additive, the mod-2 target has characteristic 2), and reversal
   **negates** `interFormInt`.
2. Hence `hfam` at `o.reverse` yields, *from `o` itself*, a family whose Gram is `−kummerSubForm`
   (`exists_family_neg_of_forall_orientation`).
3. The signature-transport engine `latticeSig_interMatrix_eq_of_fullRank_family` is general in the
   target value `s`: a full-rank family with Gram `G` forces `latticeSig (kummerK3Gram o) = latticeSig G`.
4. Applying it to both families: `latticeSig (kummerK3Gram o) = −16` **and** `= +16`
   (`latticeSig_neg` and `kummerSubForm_latticeSig`). Contradiction.

Geometrically this is just Sylvester: `kummerSubForm = ⟨−2⟩¹⁶ ⊕ 3H` has signature `−16`, its
negative has signature `+16`, and one fixed lattice cannot have both.

## The fix this forces

`hfam` must **not** be `∀ o` with a sign-carrying Gram. It has to either fix/pin one orientation
(thread a chosen `o` through the E1 chain), or quantify existentially, or carry the Gram up to sign.
⛔ Do **not** build the `⟨−2⟩¹⁶` block's diagonal against the current `∀ o` shape — it discharges
into a dead hypothesis. See `KummerK3ExceptionalRestriction` for the off-diagonal machinery, which is
orientation-agnostic and therefore unaffected.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/
import Mathlib
import SKEFTHawking.IntOrientationReverse
import SKEFTHawking.KummerK3GramFromLattice

namespace SKEFTHawking.KummerK3ForallOrientationFalse

open scoped SKEFTHawking.KummerK3E1Package
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.KummerK3E1Package
open SKEFTHawking.KummerWeld (KummerK3)
open SKEFTHawking.KummerK7Opener (KummerK3top)
open SKEFTHawking.LatticeSigFullRank
open SKEFTHawking.IntersectionSigFullRankFamily
open SKEFTHawking.KummerK3GramFromLattice
open SKEFTHawking.IntOrientationReverse

noncomputable section

/-- **`−kummerSubForm` is nondegenerate** — `det (−A) = (−1)²² det A = det A`. -/
theorem neg_kummerSubForm_det_ne_zero : (-kummerSubForm).det ≠ 0 := by
  rw [Matrix.det_neg]
  simpa using kummerSubForm_det_ne_zero

/-- **`−kummerSubForm` has signature `+16`** — the whole point: it is NOT `kummerSubForm`. -/
theorem neg_kummerSubForm_latticeSig : latticeSig (-kummerSubForm) = 16 := by
  rw [latticeSig_neg, kummerSubForm_latticeSig]; norm_num

/-- **THE ADJUDICATION: the `∀ o` Gram hypothesis is FALSE.**

Given any orientation at all, the hypothesis forces `latticeSig (kummerK3Gram o)` to be both `−16`
(from the family at `o`) and `+16` (from the family at `o.reverse`, whose Gram is `−kummerSubForm`).
-/
theorem forall_orientation_kummerSubForm_family_false
    (hfam : ∀ o : IntOrientation KummerK3, ∃ v : Fin 22 → Cohomology KummerK3top 2,
      ∀ i j, interFormInt (intFundamentalClassOfIntOrientation o) (v i) (v j) = kummerSubForm i j)
    (o : IntOrientation KummerK3) : False := by
  -- The family at `o`: signature `−16`.
  obtain ⟨v, hv⟩ := hfam o
  have h1 : latticeSig (kummerK3Gram o) = -16 :=
    latticeSig_interMatrix_eq_of_fullRank_family (intFundamentalClassOfIntOrientation o)
      kummerK3IntH2Basis kummerK3IntH2Basis_rank v kummerSubForm hv
      kummerSubForm_det_ne_zero kummerSubForm_latticeSig
  -- The family at `o.reverse`, read back at `o`: Gram `−kummerSubForm`, signature `+16`.
  obtain ⟨v', hv'⟩ := exists_family_neg_of_forall_orientation hfam o
  have hv'' : ∀ i j, interFormInt (intFundamentalClassOfIntOrientation o) (v' i) (v' j)
      = (-kummerSubForm) i j := by
    intro i j; rw [hv' i j, Matrix.neg_apply]
  have h2 : latticeSig (kummerK3Gram o) = 16 :=
    latticeSig_interMatrix_eq_of_fullRank_family (intFundamentalClassOfIntOrientation o)
      kummerK3IntH2Basis kummerK3IntH2Basis_rank v' (-kummerSubForm) hv''
      neg_kummerSubForm_det_ne_zero neg_kummerSubForm_latticeSig
  omega

/-- **…hence the hypothesis is uninhabited outright**, given that `K3` admits an orientation at all. -/
theorem not_forall_orientation_kummerSubForm_family (o : IntOrientation KummerK3) :
    ¬ (∀ o : IntOrientation KummerK3, ∃ v : Fin 22 → Cohomology KummerK3top 2,
        ∀ i j, interFormInt (intFundamentalClassOfIntOrientation o) (v i) (v j)
          = kummerSubForm i j) :=
  fun hfam => forall_orientation_kummerSubForm_family_false hfam o

end

end SKEFTHawking.KummerK3ForallOrientationFalse
