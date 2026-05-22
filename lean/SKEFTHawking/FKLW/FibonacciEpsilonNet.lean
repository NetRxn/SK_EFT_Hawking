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

/-! ## 0. Generic substrate (Mathlib upstream-PR candidate, Phase 6t Wave 3
    strengthening 2026-05-22 PM post-compact)

For any matrix with entrywise norm bound `M`, the linfty operator norm
(= max row sum of absolute values) satisfies `‖A‖ ≤ (Fintype.card n) · M`,
where `n` is the column-index type. This is the natural generalization of
the 2×2 specialization originally shipped in Wave 3 (Task #33). -/

/-- **Generic substrate** (Mathlib upstream-PR candidate): for any matrix
`A : Matrix m n ℂ` with each entry bounded by `M` in norm, the linfty
operator norm is bounded by `(Fintype.card n) · M`.

Proof: `‖A‖ = sup_i (∑_j ‖A i j‖)` (from `Matrix.linfty_opNorm_def`).
For each row `i`, `∑_j ‖A i j‖ ≤ ∑_j M = (card n) · M`. Hence the sup is
also bounded by `(card n) · M`. -/
theorem linftyOpNorm_le_card_mul_of_entries_le
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) (M : ℝ) (hM_nn : 0 ≤ M)
    (h_entries : ∀ i j, ‖A i j‖ ≤ M) :
    ‖A‖ ≤ (Fintype.card n : ℝ) * M := by
  have h_card_M_nn : (0 : ℝ) ≤ (Fintype.card n : ℝ) * M := by positivity
  rw [Matrix.linfty_opNorm_def]
  rw [show ((Fintype.card n : ℝ) * M : ℝ) =
      (((Fintype.card n : ℝ) * M).toNNReal : ℝ) from
      (Real.coe_toNNReal _ h_card_M_nn).symm]
  rw [NNReal.coe_le_coe]
  apply Finset.sup_le
  intro i _
  rw [show ((Fintype.card n : ℝ) * M).toNNReal =
      ⟨(Fintype.card n : ℝ) * M, h_card_M_nn⟩ from
      Real.toNNReal_of_nonneg h_card_M_nn]
  rw [← NNReal.coe_le_coe]
  -- Goal: (∑ j, ‖A i j‖₊ : ℝ) ≤ (Fintype.card n : ℝ) * M
  have h_coe : ((∑ j : n, ‖A i j‖₊ : NNReal) : ℝ) = ∑ j : n, ‖A i j‖ := by
    push_cast
    rfl
  rw [h_coe]
  calc ∑ j : n, ‖A i j‖
      ≤ ∑ _j : n, M := Finset.sum_le_sum (fun j _ => h_entries i j)
    _ = (Fintype.card n) • M := by
        rw [Finset.sum_const, Finset.card_univ]
    _ = (Fintype.card n : ℝ) * M := by rw [nsmul_eq_mul]

/-- **Strict-inequality variant** (convenience form for downstream consumers):
if entries are strictly bounded by `M`, the operator norm is bounded by
`(Fintype.card n) · M`. -/
theorem linftyOpNorm_le_card_mul_of_entries_lt
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) (M : ℝ) (hM_nn : 0 ≤ M)
    (h_entries : ∀ i j, ‖A i j‖ < M) :
    ‖A‖ ≤ (Fintype.card n : ℝ) * M :=
  linftyOpNorm_le_card_mul_of_entries_le A M hM_nn
    (fun i j => le_of_lt (h_entries i j))

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
`2·ε₀`-precision in linfty-op-norm for 2×2 matrices.

Refactored 2026-05-22 PM post-compact to consume the generic substrate
`linftyOpNorm_le_card_mul_of_entries_lt` (Wave 3 strengthening, Task #33). -/
theorem fibonacciEpsilonNet_findNearest_approx_opNorm
    (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) (ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    ‖(ρ_Fib_SU2 (fibonacciEpsilonNet_findNearest U ε₀ hε₀) :
        Matrix (Fin 2) (Fin 2) ℂ) - (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ 2 * ε₀ := by
  have h_entry := fibonacciEpsilonNet_findNearest_approx_entrywise U ε₀ hε₀
  set A := (ρ_Fib_SU2 (fibonacciEpsilonNet_findNearest U ε₀ hε₀) :
             Matrix (Fin 2) (Fin 2) ℂ) - (U : Matrix (Fin 2) (Fin 2) ℂ) with hA_def
  -- Apply the generic Fin d substrate with d = 2.
  have h_gen := linftyOpNorm_le_card_mul_of_entries_lt A ε₀ (le_of_lt hε₀) h_entry
  -- Specialize `Fintype.card (Fin 2) = 2`:
  have h_card : (Fintype.card (Fin 2) : ℝ) = 2 := by
    rw [Fintype.card_fin]; norm_num
  rw [h_card] at h_gen
  exact h_gen
