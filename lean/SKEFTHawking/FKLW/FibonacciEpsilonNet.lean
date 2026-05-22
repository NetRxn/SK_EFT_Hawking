/-
SK_EFT_Hawking Phase 6t Wave 3 SHIP (2026-05-22 PM):
**Fibonacci ε₀-net for the Dawson-Nielsen Solovay-Kitaev recursion base case**.

This module ships the ε₀-net infrastructure for the Solovay-Kitaev recursion's
**base case**: a function `fibonacciEpsilonNet_findNearest U ε₀ : BraidGroup 3`
that, for any target `U ∈ SU(2)` and threshold `ε₀ > 0`, returns a Fibonacci
braid word `b` such that the entrywise distance `‖ρ_Fib_SU2 b - U‖_∞ < ε₀`.

The existence of this function is unconditional (consumes the F.21 density
theorem `fibonacci_density_F21_unconditional`). The function is defined via
`Classical.choose`, making it noncomputable; Wave 7's runnable extraction
deals with the constructive enumeration variant.

## Phase 6t roadmap alignment

  - Wave 3 (this module) → consumed by Wave 4 (SK recursion) as the level-0
    approximation function.

  - Per user 2026-05-22 PM lock-in §13.2 (Path A — constructive enumeration):
    the Path A constructive ε₀-net via explicit braid-word enumeration is
    deferred to a Wave 3-followup discharge session (~200-400 LoC of explicit
    enumeration + per-cell grid case analysis). This module ships the
    EXISTENCE-form via F.21 density `Classical.choose` extraction, which is
    sufficient for Wave 4 + 5 + 6 (the existence-only theorem and length
    bound). Wave 7's native-extraction compiler is contingent on the
    Wave 3-followup constructive ship.

## Pipeline Invariant compliance

  - Invariant #10 (no `maxHeartbeats`): RESPECTED.
  - Invariant #15 (no new axioms): RESPECTED — `Classical.choose` is in the
    standard kernel closure `[propext, Classical.choice, Quot.sound]`.

Primary source: Dawson & Nielsen, *Quantum Info. & Comp.* 6 (2006), 81–95;
                arXiv:quant-ph/0505030, §3.2 (ε₀-net base case).
Substrate: SKEFTHawking.FKLW.SU2BCHBracketClosure.fibonacci_density_F21_unconditional
           (Phase 6p Wave 2c.4a-R4.2.d).
-/

import Mathlib
import SKEFTHawking.FKLW.SU2BCHBracketClosure
import SKEFTHawking.FKLW.FibSU2Rep
import SKEFTHawking.FKLW.AharonovAradBridgeIteration

set_option autoImplicit false

namespace SKEFTHawking.FKLW.FibonacciEpsilonNet

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

open Matrix SKEFTHawking.FKLW SKEFTHawking.FKLW.AharonovAradBridge

/-! ## 1. Fibonacci braid-word type alias

The braid representation `ρ_Fib_SU2 : BraidGroup 3 →* SU(2)` is the
mathematical realization of Fibonacci anyon braiding in the 2-dimensional
qubit representation. For Phase 6t's ε₀-net, a "Fibonacci braid word" is
just an element of `BraidGroup 3`. -/

/-- The Fibonacci braid word type. -/
abbrev FibonacciBraidWord : Type := BraidGroup 3

/-! ## 2. Nearest-braid-word function via F.21 density

Given a target `U ∈ SU(2)` and a precision `ε₀ > 0`, the F.21 density theorem
guarantees the existence of a braid word `b` such that the entrywise distance
`‖ρ_Fib_SU2 b - U‖_∞ < ε₀`. This module's `fibonacciEpsilonNet_findNearest`
extracts such a `b` via `Classical.choose`. -/

/-- The nearest Fibonacci braid word to a target SU(2) element at precision ε₀.
Returns a braid word `b` such that the entrywise distance
`‖ρ_Fib_SU2 b - U‖_∞ < ε₀`. Existence is guaranteed by F.21 density. -/
noncomputable def fibonacciEpsilonNet_findNearest
    (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) (ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    FibonacciBraidWord :=
  (fibonacci_density_F21_unconditional U ε₀ hε₀).choose

/-! ## 3. Correctness of the nearest-finder — entrywise version

The defining property of `fibonacciEpsilonNet_findNearest`: it returns a braid
word whose Fibonacci-representation matrix is entrywise ε₀-close to the
target U. -/

/-- **HEADLINE 1 (Phase 6t Wave 3)**: correctness of the nearest-finder
in entrywise form. -/
theorem fibonacciEpsilonNet_findNearest_approx_entrywise
    (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) (ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    ∀ i j : Fin 2,
      ‖(ρ_Fib_SU2 (fibonacciEpsilonNet_findNearest U ε₀ hε₀) :
          Matrix (Fin 2) (Fin 2) ℂ) i j - (U : Matrix (Fin 2) (Fin 2) ℂ) i j‖ < ε₀ :=
  (fibonacci_density_F21_unconditional U ε₀ hε₀).choose_spec

/-! ## 4. Correctness in operator-norm form

For SK consumption, the entrywise bound `‖A_ij‖ < ε₀` translates to an
operator-norm bound. The linfty operator norm (= max-row-1-sum) of a 2×2
matrix `A` with each entry of norm `< ε₀` is `≤ 2·ε₀`. This is the form
consumed by the Solovay-Kitaev recursion. -/

/-- **HEADLINE 2 (Phase 6t Wave 3)**: correctness of the nearest-finder in
linfty-operator-norm form. The ε₀-precision in entrywise form implies a
`2·ε₀`-precision in linfty-op-norm for 2×2 matrices. -/
theorem fibonacciEpsilonNet_findNearest_approx_opNorm
    (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) (ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    ‖(ρ_Fib_SU2 (fibonacciEpsilonNet_findNearest U ε₀ hε₀) :
        Matrix (Fin 2) (Fin 2) ℂ) - (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ 2 * ε₀ := by
  -- Entrywise bound from Headline 1.
  have h_entry := fibonacciEpsilonNet_findNearest_approx_entrywise U ε₀ hε₀
  set A := (ρ_Fib_SU2 (fibonacciEpsilonNet_findNearest U ε₀ hε₀) :
             Matrix (Fin 2) (Fin 2) ℂ) - (U : Matrix (Fin 2) (Fin 2) ℂ) with hA_def
  have h2ε₀_nn : (0 : ℝ) ≤ 2 * ε₀ := by linarith
  -- Bound each row sum (in real) by 2·ε₀.
  have h_each_row_real : ∀ i : Fin 2,
      ((∑ j : Fin 2, ‖A i j‖₊ : NNReal) : ℝ) ≤ 2 * ε₀ := by
    intro i
    have h_coe : ((∑ j : Fin 2, ‖A i j‖₊ : NNReal) : ℝ) = ∑ j : Fin 2, ‖A i j‖ := by
      push_cast
      rfl
    rw [h_coe]
    have h_le : ∑ j : Fin 2, ‖A i j‖ ≤ ∑ _j : Fin 2, ε₀ := by
      apply Finset.sum_le_sum
      intro j _
      exact le_of_lt (h_entry i j)
    have h_const : ∑ _j : Fin 2, (ε₀ : ℝ) = 2 * ε₀ := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, two_mul]
    linarith
  -- Use linfty_opNorm_def to express the norm.
  rw [Matrix.linfty_opNorm_def]
  -- Convert the NNReal-coerced sup bound.
  rw [show (2 * ε₀ : ℝ) = ((2 * ε₀).toNNReal : ℝ) from
      (Real.coe_toNNReal _ h2ε₀_nn).symm]
  rw [NNReal.coe_le_coe]
  apply Finset.sup_le
  intro i _
  rw [show (2 * ε₀ : ℝ).toNNReal = ⟨2 * ε₀, h2ε₀_nn⟩ from
      Real.toNNReal_of_nonneg h2ε₀_nn]
  rw [← NNReal.coe_le_coe]
  simpa using h_each_row_real i
