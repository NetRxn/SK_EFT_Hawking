/-
# Phase 5q.H — the `⟨−2⟩¹⁶` block's obligation, stated at the ACTUAL exceptional classes

`KummerK3GeometricFamily` split the welded `K3`'s `hfam` into three tabulations;
`KummerK3ExceptionalClasses` built the 16 classes `excClass c ∈ H₂(K3;ℤ)` the first tabulation is
about. This module states that tabulation as **one named `Prop` about those very classes**, and
closes the loop back to the block interface.

    ExceptionalBlockGram o  :=  ∃ α : EIndex → H²(K3;ℤ),
        (∀ c, α c ⌢ [K3]_o = excClass c)
        ∧ (∀ c, ⟨α c, excClass c⟩ = −2)  ∧  (∀ c d, c ≠ d → ⟨α d, excClass c⟩ = 0)

i.e. *the 16 exceptional homology classes admit cap-duals, and the pairing table of those duals
against them is `⟨−2⟩¹⁶`*. Through the cap–cup adjunction
(`IntCapProductInt.interFormInt_eq_kroneckerHInt_capHInt`) that is exactly the `hself`/`hoff` pair
that `KummerK3GeometricFamily.exists_kummerSubForm_family_of_eIndex_blocks` consumes — proved here
(`interFormInt_exc_of_block`), so the E-lane's target is *verifiably* the right one and not a
lookalike.

## Why the statement is about `excClass` and not about "some 16 classes"

`KummerK3ExceptionalClasses.range_eCopy_eq_span_excClass` says the `c`-th resolution piece
contributes exactly `ℤ · excClass c` to `H₂(K3;ℤ)`. So a 16-block "coming from the `E`-pieces" has no
freedom beyond integer multiples, and a self-intersection of `−2` pins those multiples to `±1`
(`selfIntersection_smul_eq_neg_two`, stated on the intersection form where the scaling is `n²`).
Naming the classes therefore loses nothing and gains a target that cannot drift.

## Non-vacuity

`ExceptionalBlockGram` cannot be satisfied without geometry: the diagonal `−2 ≠ 0` forces
`excClass c ≠ 0` for every `c` (`excClass_ne_zero_of_block`), i.e. every resolution piece's `H₂`
survives into `H₂(K3;ℤ)` — a genuine (and, for the real Kummer surface, true) assertion about the
weld that no degenerate witness supplies.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/
import Mathlib
import SKEFTHawking.KummerK3ExceptionalClasses
import SKEFTHawking.KummerK3CapDualFamily

namespace SKEFTHawking.KummerK3ExceptionalBlock

open scoped SKEFTHawking.KummerK3E1Package
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.KummerWeld (KummerK3 EIndex)
open SKEFTHawking.KummerK7Opener (KummerK3top)
open SKEFTHawking.KummerK3E1Package
open SKEFTHawking.KummerK3ExceptionalClasses

noncomputable section

/-! ## §1. The E-block obligation as a named `Prop` -/

/-- **THE `⟨−2⟩¹⁶` BLOCK'S OBLIGATION, at the constructed exceptional classes.**

The 16 exceptional classes `excClass c` admit cohomological cap-duals `α c`, whose Kronecker pairing
table against the `excClass`'s is `−2` on the diagonal and `0` off it. This is the E-lane's entire
target: everything else about the `⟨−2⟩¹⁶` block is already discharged
(`KummerK3GeometricFamily`, `KummerK3CapDualFamily`). -/
def ExceptionalBlockGram (o : IntOrientation KummerK3) : Prop :=
  ∃ α : EIndex → Cohomology KummerK3top 2,
    (∀ c, capHInt 2 1 (α c) o.fundClass = excClass c) ∧
      (∀ c, kroneckerHInt 2 (α c) (excClass c) = -2) ∧
      (∀ c d, c ≠ d → kroneckerHInt 2 (α d) (excClass c) = 0)

/-! ## §2. It really is the block interface's `hself` / `hoff` pair -/

/-- **The cap–cup adjunction at an arbitrary index type.**
`IntCapProductInt.interFormInt_eq_kroneckerHInt_capHInt` in the "family with known cap-duals" form,
without the `Fin n` packaging of `IntersectionMatrixBasisChange.interFormInt_capDual`. -/
theorem interFormInt_of_cap {X : TopCat} {ι : Type*} (zM : Homology X 4)
    (α : ι → Cohomology X 2) (c : ι → Homology X 2) (hcap : ∀ i, capHInt 2 1 (α i) zM = c i)
    (i j : ι) :
    interFormInt (intFundamentalClassOfHomology zM) (α i) (α j) = kroneckerHInt 2 (α j) (c i) := by
  rw [interFormInt_eq_kroneckerHInt_capHInt, hcap]

/-- **`ExceptionalBlockGram` delivers exactly the `hself`/`hoff` hypotheses of
`KummerK3GeometricFamily.exists_kummerSubForm_family_of_eIndex_blocks`.** The closing of the loop:
what the E-lane is asked to prove is provably what the block assembler consumes. -/
theorem interFormInt_exc_of_block (o : IntOrientation KummerK3) (h : ExceptionalBlockGram o) :
    ∃ x : EIndex → Cohomology KummerK3top 2,
      (∀ c, interFormInt (intFundamentalClassOfIntOrientation o) (x c) (x c) = -2) ∧
        ∀ c d, c ≠ d →
          interFormInt (intFundamentalClassOfIntOrientation o) (x c) (x d) = 0 := by
  obtain ⟨α, hcap, hdiag, hoff⟩ := h
  refine ⟨α, fun c => ?_, fun c d hcd => ?_⟩
  · rw [show intFundamentalClassOfIntOrientation o
      = intFundamentalClassOfHomology o.fundClass from rfl,
      interFormInt_of_cap o.fundClass α excClass hcap c c]
    exact hdiag c
  · rw [show intFundamentalClassOfIntOrientation o
      = intFundamentalClassOfHomology o.fundClass from rfl,
      interFormInt_of_cap o.fundClass α excClass hcap c d]
    exact hoff c d hcd

/-! ## §3. Non-vacuity and rigidity -/

/-- **`ExceptionalBlockGram` forces every exceptional class to be nonzero.** The zero-geometric-input
attack: a diagonal entry `⟨α c, excClass c⟩ = −2 ≠ 0` is impossible if `excClass c = 0`. So the
obligation asserts that each of the 16 resolution pieces' `H₂` genuinely survives into `H₂(K3;ℤ)` —
content about the weld, not bookkeeping. -/
theorem excClass_ne_zero_of_block (o : IntOrientation KummerK3) (h : ExceptionalBlockGram o)
    (c : EIndex) : excClass c ≠ 0 := by
  obtain ⟨α, _, hdiag, _⟩ := h
  intro hzero
  have h2 := hdiag c
  rw [hzero, map_zero] at h2
  exact absurd h2 (by norm_num)

/-- **A self-intersection of `−2` pins an integer multiple to `±1`.**

Combined with `KummerK3ExceptionalClasses.range_eCopy_eq_span_excClass` (the `c`-th piece
contributes exactly `ℤ · excClass c`), this is the E-block's rigidity: the intersection form scales
as `n²` on `n • a`, so `−2 n² = −2` forces `n² = 1`. There is therefore no choice of exceptional
class beyond an overall sign, and the sign is absorbed by the Gram (`⟨−2⟩¹⁶` is sign-symmetric). -/
theorem selfIntersection_smul_eq_neg_two {X : TopCat} (fc : IntFundamentalClass X)
    (a : Cohomology X 2) (n : ℤ) (ha : interFormInt fc a a = -2)
    (hn : interFormInt fc (n • a) (n • a) = -2) : n * n = 1 := by
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, ha] at hn
  nlinarith [hn]

end

end SKEFTHawking.KummerK3ExceptionalBlock
