/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x′ Phase 2 (A) — the `sde₂`-valued measure on ℂ-matrices

The unconditional Toffoli lower bound `T^of(U) ≥ sde₂(Û)` instantiates the parametric
`toffoliCost_ge_measure` at `μ = matrixSde2 ∘ channelRep`. This file builds that measure:

  * `sde2ℂ : ℂ → ℕ` — the dyadic smallest-denominator exponent of a complex number, extracted via its
    rational value (`0` when `z` is not a rational scalar). Mukhopadhyay guarantees channel-rep entries
    are real (and, for Clifford+CCZ words, dyadic — Lemma 3.10), so this is the right total extension.
  * `matrixSde2 : Matrix L L ℂ → ℕ` — the max of `sde2ℂ` over entries (porting the shipped `KMM.sdeC`
    `Finset.univ.sup … denExp` pattern).
  * `channelSde2 U := matrixSde2 (channelRep U)` and `channelSde2 1 = 0` (the `μ 1 = 0` hypothesis).

**Key subtlety (the half-sum bound is CONDITIONAL).** The ℂ-lift `sde2ℂ_half_sum_le` of Fact 3.14
(`sde2_half_sum_le`) holds only when the four summands are rational scalars. A *universal* ℂ bound is
false: cancellation of irrational parts can leave a high-exponent dyadic residue (e.g.
`(1/4+√2) + (1/4−√2)` halves to `1/4`). The downstream `hCCZ` therefore threads dyadic-ness of the
channel rep (Lemma 3.10), which is exactly where these rationality hypotheses are discharged. The final
headline `T^of(U) ≥ sde₂(Û)` stays unconditional, because an exactly-Clifford+CCZ `U` has a dyadic `Û`.

The measure is **non-vacuous** (`sde2ℂ (1/2) = 1`), guarding against the trivial `μ ≡ 0` that would
self-satisfy the telescoping hypotheses.

PUBLIC math layer only.

## Pipeline invariants
- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected. Kernel-pure.

-/

import SKEFTHawking.FKLW.MukhopadhyaySde2
import SKEFTHawking.FKLW.MukhopadhyayChannelRep

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SKEFTHawking.FKLW.MukhopadhyayCCZ

open scoped Matrix

/-! ## 1. `sde₂` on ℚ: negation invariance -/

/-- `sde₂(−q) = sde₂ q` (the dyadic exponent ignores sign). -/
theorem sde2_neg (q : ℚ) : sde2 (-q) = sde2 q := by
  rw [sde2, sde2, padicValRat.neg]

/-- `sde₂(1/2) = 1` — the smallest nontrivial dyadic exponent (used for non-vacuity). -/
theorem sde2_half : sde2 ((1 : ℚ) / 2) = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : padicValRat 2 ((1 : ℚ) / 2) = -1 := by
    have h := padicValRat_two_pow_mul (q := (1 : ℚ) / 2) (by norm_num) 1
    rw [show (2 : ℚ) ^ 1 * ((1 : ℚ) / 2) = 1 from by ring, padicValRat.one] at h
    omega
  rw [sde2, key]
  decide

/-! ## 2. `sde₂` on ℂ: extraction via the rational value -/

open Classical in
/-- **`sde₂` of a complex number**, via its rational value: `sde₂ q` when `z = (q : ℂ)`, else `0`.
(`Rat.cast` is injective, so the rational value is unique when it exists.) -/
noncomputable def sde2ℂ (z : ℂ) : ℕ := if h : ∃ q : ℚ, (q : ℂ) = z then sde2 h.choose else 0

/-- On a rational scalar, `sde2ℂ` recovers the ℚ-level `sde₂`. -/
theorem sde2ℂ_ratCast (q : ℚ) : sde2ℂ (q : ℂ) = sde2 q := by
  have hex : ∃ q' : ℚ, (q' : ℂ) = (q : ℂ) := ⟨q, rfl⟩
  rw [sde2ℂ, dif_pos hex]
  congr 1
  exact Rat.cast_injective hex.choose_spec

@[simp] theorem sde2ℂ_zero : sde2ℂ 0 = 0 := by
  rw [show (0 : ℂ) = ((0 : ℚ) : ℂ) from by norm_num, sde2ℂ_ratCast, sde2_zero]

@[simp] theorem sde2ℂ_one : sde2ℂ 1 = 0 := by
  rw [show (1 : ℂ) = ((1 : ℚ) : ℂ) from by norm_num, sde2ℂ_ratCast, sde2, padicValRat.one]
  decide

/-- **Non-vacuity witness**: `sde2ℂ (1/2) = 1 ≠ 0`, so the measure is not the trivial constant. -/
theorem sde2ℂ_half : sde2ℂ ((1 : ℂ) / 2) = 1 := by
  rw [show (1 : ℂ) / 2 = (((1 : ℚ) / 2 : ℚ) : ℂ) from by push_cast; ring, sde2ℂ_ratCast, sde2_half]

/-- `sde2ℂ` ignores sign. -/
theorem sde2ℂ_neg (z : ℂ) : sde2ℂ (-z) = sde2ℂ z := by
  by_cases h : ∃ q : ℚ, (q : ℂ) = z
  · obtain ⟨q, rfl⟩ := h
    rw [show -((q : ℚ) : ℂ) = ((-q : ℚ) : ℂ) from by push_cast; ring, sde2ℂ_ratCast, sde2ℂ_ratCast,
      sde2_neg]
  · have h' : ¬ ∃ q : ℚ, (q : ℂ) = -z := by
      rintro ⟨q, hq⟩
      exact h ⟨-q, by rw [Rat.cast_neg, hq, neg_neg]⟩
    rw [sde2ℂ, sde2ℂ, dif_neg h', dif_neg h]

/-- **Fact 3.14 lifted to ℂ (rationality-conditional).** For four *rational* scalars, the half-sum
raises `sde2ℂ` by at most one. (The rationality hypotheses are discharged downstream via Lemma 3.10's
dyadic channel-rep entries; a universal ℂ bound is false — see the module docstring.) -/
theorem sde2ℂ_half_sum_le {z₁ z₂ z₃ z₄ : ℂ}
    (h₁ : ∃ q : ℚ, (q : ℂ) = z₁) (h₂ : ∃ q : ℚ, (q : ℂ) = z₂)
    (h₃ : ∃ q : ℚ, (q : ℂ) = z₃) (h₄ : ∃ q : ℚ, (q : ℂ) = z₄) :
    sde2ℂ ((z₁ + z₂ + z₃ + z₄) / 2)
      ≤ max (max (sde2ℂ z₁) (sde2ℂ z₂)) (max (sde2ℂ z₃) (sde2ℂ z₄)) + 1 := by
  obtain ⟨q₁, rfl⟩ := h₁
  obtain ⟨q₂, rfl⟩ := h₂
  obtain ⟨q₃, rfl⟩ := h₃
  obtain ⟨q₄, rfl⟩ := h₄
  rw [show ((q₁ : ℂ) + q₂ + q₃ + q₄) / 2 = (((q₁ + q₂ + q₃ + q₄) / 2 : ℚ) : ℂ) from by push_cast; ring]
  simp only [sde2ℂ_ratCast]
  exact sde2_half_sum_le q₁ q₂ q₃ q₄

/-! ## 3. The matrix measure -/

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- **`matrixSde2`** — the max of `sde2ℂ` over all entries (porting `KMM.sdeC`). -/
noncomputable def matrixSde2 (X : Matrix L L ℂ) : ℕ :=
  Finset.univ.sup fun i => Finset.univ.sup fun j => sde2ℂ (X i j)

/-- Every entry's `sde2ℂ` is bounded by the matrix measure. -/
theorem sde2ℂ_le_matrixSde2 (X : Matrix L L ℂ) (i j : L) : sde2ℂ (X i j) ≤ matrixSde2 X := by
  show sde2ℂ (X i j) ≤ Finset.univ.sup fun i => Finset.univ.sup fun j => sde2ℂ (X i j)
  refine le_trans (Finset.le_sup (f := fun j => sde2ℂ (X i j)) (Finset.mem_univ j)) ?_
  exact Finset.le_sup (f := fun i => Finset.univ.sup fun j => sde2ℂ (X i j)) (Finset.mem_univ i)

/-- The identity matrix has measure `0` (entries are `0`/`1`). -/
@[simp] theorem matrixSde2_one : matrixSde2 (1 : Matrix L L ℂ) = 0 := by
  refine le_antisymm ?_ (Nat.zero_le _)
  refine Finset.sup_le fun i _ => Finset.sup_le fun j _ => ?_
  rw [Matrix.one_apply]
  by_cases h : i = j <;> simp [h]

/-! ## 4. The channel-rep measure `μ = matrixSde2 ∘ channelRep` -/

/-- **The Toffoli measure** `μ(U) = sde₂` of the channel rep `Û` (max over its `64×64` entries). -/
noncomputable def channelSde2 (U : Matrix (Fin 8) (Fin 8) ℂ) : ℕ := matrixSde2 (channelRep U)

/-- `μ(1) = 0` — the `h1` hypothesis of `toffoliCost_ge_measure`. -/
@[simp] theorem channelSde2_one : channelSde2 1 = 0 := by
  rw [channelSde2, channelRep_one, matrixSde2_one]

end SKEFTHawking.FKLW.MukhopadhyayCCZ
