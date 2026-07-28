/-
# `IntOrientation` does not pin the fundamental class — every `∀ o` unimodularity claim is FALSE

`IntOrientation M` has exactly two fields: `fundClass : H₄(M;ℤ)` and

    redCompat : redHomology _ 4 fundClass = [M]₂   (the canonical mod-2 class)

`redCompat` was meant to make `fundClass` "not a free `H₄(M;ℤ)` element but the integral lift of the
canonical class". It does **less** than that. Reduction is a ℤ-linear map into a `ZMod 2`-module, so
for **every odd** `n : ℤ`,

    red (n • fundClass) = n • red fundClass = red fundClass,

i.e. `n • [M]` satisfies `redCompat` too. `IntOrientation.smulOdd` below constructs it. (`n = −1` is
`IntOrientationReverse.IntOrientation.reverse`; this module is the general statement, and `n = 3` is
what makes it *destructive* rather than merely a sign.)

## The consequence: `∀ o`-quantified nondegeneracy is unsatisfiable

Scaling the fundamental class scales the intersection form, hence scales the Gram matrix, hence
multiplies its determinant by `n ^ rank`. So for a rank `> 0` basis,

    ∀ o : IntOrientation M, IsUnimodular (interMatrix [M]_o B)

is **FALSE** as soon as ONE orientation exists: apply it at `o` and at `o.smulOdd 3` to get
`det = ±1` and `3 ^ rank · det = ±1` simultaneously (`not_forall_intOrientation_isUnimodular`).

At the welded `K3` an orientation exists unconditionally
(`KummerK3SeamTransport.nonempty_intOrientation_kummerK3_uncond`), so the refutation is
**unconditional** there — and since integral PD *is* unimodularity of the Gram
(`KummerK3PoincareDuality.nonempty_intPD_iff_isUnit_det`), the ledger field

    pdInput : ∀ o : IntOrientation KummerK3, Nonempty (IntPoincareDuality [K3]_o)

is false, `KummerK3E1Residuals` is uninhabitable, and **every `∀ o`-shaped route into
`Nonempty KummerK3E1Atoms` is vacuous**: `_of_pd`, `_of_gram`, `_of_hk3`,
`_of_stable_of_geometric`, and the `KummerK3E1Unconditional` entry points.

## What is NOT wrong: the target

`KummerK3E1Atoms` bundles **one** orientation together with PD *against that orientation*. That is
the correct existential shape and is untouched. Only the routes were over-quantified.
`KummerK3E1Repair` builds the pinned-orientation replacements.

## Relation to the sign defect

`KummerK3ForallOrientationFalse` refuted the `∀ o` *Gram* hypothesis via signature reversal. That
defect is **irreducible** — `o.reverse` is a genuine orientation, so no strengthening of
`IntOrientation` can rescue a `∀ o` statement with a sign-carrying Gram. The scaling defect here is
**definitional**: it would be repaired by adding a generator field to `IntOrientation`. Both force
the same fix on the consumers — pin one orientation — so the repair is done there.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/
import Mathlib
import SKEFTHawking.IntOrientationReverse
import SKEFTHawking.IntersectionMatrixInt

namespace SKEFTHawking.IntOrientationScaling

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt

noncomputable section

/-- **Odd integer multiples act trivially on a mod-2 class.** The target is a `ZMod 2`-module, so
`n • x = (n : ZMod 2) • x = 1 • x = x` for odd `n`. Generalizes
`IntOrientationReverse.neg_eq_self_mod2` (`n = −1`). -/
theorem zsmul_eq_self_mod2 {M : Type} [TopologicalSpace M] {n : ℤ} (hn : Odd n)
    (x : SKEFTHawking.SingularHomologyMod2.Homology (TopCat.of M) 4) : n • x = x := by
  obtain ⟨k, rfl⟩ := hn
  rw [← Int.cast_smul_eq_zsmul (ZMod 2) (2 * k + 1) x]
  push_cast
  rw [show ((2 : ZMod 2)) = 0 from by decide]
  simp

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]

/-- **THE SCALED ORIENTATION.** For odd `n`, `n • [M]` satisfies `redCompat`, so it is another
`IntOrientation M`. Unlike `reverse` (`n = −1`) this changes the *magnitude* of the fundamental
class, which is what makes every `∀ o` nondegeneracy claim false. -/
def IntOrientation.smulOdd (o : IntOrientation M) {n : ℤ} (hn : Odd n) : IntOrientation M where
  fundClass := n • o.fundClass
  redCompat := by
    rw [map_zsmul, o.redCompat, zsmul_eq_self_mod2 hn]

@[simp] theorem smulOdd_fundClass (o : IntOrientation M) {n : ℤ} (hn : Odd n) :
    (IntOrientation.smulOdd o hn).fundClass = n • o.fundClass := rfl

/-- **Scaling the fundamental class scales the intersection form**, by linearity of the Kronecker
pairing in the homology slot. -/
theorem interFormInt_smulOdd (o : IntOrientation M) {n : ℤ} (hn : Odd n)
    (a b : Cohomology (TopCat.of M) 2) :
    interFormInt (intFundamentalClassOfIntOrientation (IntOrientation.smulOdd o hn)) a b
      = n * interFormInt (intFundamentalClassOfIntOrientation o) a b := by
  show ((kroneckerHInt 4).flip (n • o.fundClass)) (cupH24 a b)
      = n * ((kroneckerHInt 4).flip o.fundClass) (cupH24 a b)
  simp only [LinearMap.flip_apply, map_zsmul, LinearMap.smul_apply, smul_eq_mul]

/-- **…hence scales the Gram matrix.** -/
theorem interMatrix_smulOdd (o : IntOrientation M) {n : ℤ} (hn : Odd n)
    (B : IntH2Basis (TopCat.of M)) :
    interMatrix (intFundamentalClassOfIntOrientation (IntOrientation.smulOdd o hn)) B
      = n • interMatrix (intFundamentalClassOfIntOrientation o) B := by
  ext i j
  simp [interMatrix]

/-- **THE REFUTATION — a `∀ o` unimodularity claim is FALSE the moment one orientation exists.**

Apply the hypothesis at `o` (giving `det = ±1`) and at `o.smulOdd 3` (giving `3 ^ rank · det = ±1`).
For `rank > 0` these are incompatible. Nothing about `M` beyond "an orientation exists and `H²` has
positive rank" is used — this is a defect of the `IntOrientation` *structure*, not of any carrier. -/
theorem not_forall_intOrientation_isUnimodular (o : IntOrientation M) (B : IntH2Basis (TopCat.of M))
    (hrank : 0 < B.rank) :
    ¬ (∀ o' : IntOrientation M,
        IsUnimodular (interMatrix (intFundamentalClassOfIntOrientation o') B)) := by
  intro h
  have h1 : IsUnimodular (interMatrix (intFundamentalClassOfIntOrientation o) B) := h o
  have h3 := h (IntOrientation.smulOdd o (by decide : Odd (3 : ℤ)))
  rw [interMatrix_smulOdd, IsUnimodular, Matrix.det_smul, Fintype.card_fin] at h3
  have hp : (3 : ℤ) ≤ 3 ^ B.rank := by
    calc (3 : ℤ) = 3 ^ 1 := (pow_one 3).symm
      _ ≤ 3 ^ B.rank := pow_le_pow_right₀ (by norm_num) hrank
  obtain ⟨p, hp3, hpe⟩ : ∃ p : ℤ, 3 ≤ p ∧ (3 : ℤ) ^ B.rank = p := ⟨_, hp, rfl⟩
  rw [hpe] at h3
  rcases h1 with h1 | h1 <;> rw [h1] at h3 <;> rcases h3 with h3 | h3 <;> omega

end

end SKEFTHawking.IntOrientationScaling
