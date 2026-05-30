/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Item L.B/L.C — Mukhopadhyay dyadic `sde₂` invariant + Fact 3.14 (increment L.B.2a)

Mukhopadhyay 2024 (arXiv:2401.08950) measures Toffoli/CS-count via the **dyadic smallest-denominator
exponent `sde₂`** of the channel representation (Definition 3.13): for a nonzero `v ∈ ℤ[1/2]`, the
least `k ∈ ℕ` with `v = a/2^k` and `a` odd; `sde₂(0) = 0`. The channel rep of a Clifford+Toffoli
unitary has entries in the dyadic ring `ℤ[1/2] ⊂ ℚ` (Lemma 3.10), so `sde₂` is exactly the negated
`2`-adic valuation clamped at `0` — the `√2 → 2` analog of the shipped `√2`-`sde` T-count invariant.

This increment ships the **scalar layer** (`sde₂` on `ℚ`, the dyadic model), independent of the
channel-rep entry analysis:

  - `sde2 q := (-(padicValRat 2 q)).toNat` (Definition 3.13) and `sde2_le_iff`.
  - **Fact 3.14** (`sde2_half_sum_le`): for any `v₁, v₂, v₃, v₄ ∈ ℚ`,
    `sde₂((v₁ + v₂ + v₃ + v₄)/2) ≤ max sde₂(vᵢ) + 1` — the half-sum-of-four monotonicity that
    underpins Lemma 3.16's per-step `+1` increase bound (the row-addition trick, §3.4 / Theorem
    3.8.3: each entry of `Ĝ·Û` is `(1/2)·(±` up to four entries of `Û`)`)`.

The matrix-level `sde₂`, the per-step `+1` bound for the channel rep, and the telescoping Toffoli
lower bound `T^of(U) ≥ sde₂(Û)` are the next increments (L.B.2b / L.C). Note (dossier Q2.3 +
mechanism check): the lower bound `T^of ≥ sde₂` *does* follow from the per-step `+1` bound by
telescoping from a Clifford base (`sde₂ = 0`); it is a valid lower bound (though NOT proved tight —
full Toffoli minimality needs the exhaustive meet-in-the-middle search, Lemma 4.5 / Conjecture 4.8,
which is not Lean-tractable; that residual is documented in L.C).

PUBLIC math layer only (per the Item-L brief): no private-repo content.

## Pipeline invariants
- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.

-/

import Mathlib.NumberTheory.Padics.PadicVal.Basic

set_option autoImplicit false

namespace SKEFTHawking.FKLW.MukhopadhyayCCZ

/-- **Mukhopadhyay's dyadic smallest-denominator exponent `sde₂`** (arXiv:2401.08950 Definition
3.13): for `q ∈ ℤ[1/2] ⊂ ℚ`, the least `k` with `q = a/2^k` (`a` odd); `sde₂(0) = 0`. Realized as the
negated `2`-adic valuation clamped at `0`. -/
noncomputable def sde2 (q : ℚ) : ℕ := (-(padicValRat 2 q)).toNat

@[simp] theorem sde2_zero : sde2 0 = 0 := by
  simp [sde2]

/-- `sde₂ q ≤ n` iff the `2`-adic valuation of `q` is at least `-n` (the dyadic denominator has
exponent at most `n`). Note `sde₂` clamps at `0`, so this holds for all `q` (including `q = 0`). -/
theorem sde2_le_iff {q : ℚ} {n : ℕ} : sde2 q ≤ n ↔ (-(n : ℤ)) ≤ padicValRat 2 q := by
  rw [sde2, Int.toNat_le]
  omega

/-- The `2`-adic-integer property (`0 ≤ padicValRat 2 q`, or `q = 0`) is closed under addition:
`ℤ[1/2]`'s `2`-adic integers are a subring. The non-archimedean step behind Fact 3.14. -/
theorem padicValRat_add_nonneg {a b : ℚ} (ha : 0 ≤ padicValRat 2 a) (hb : 0 ≤ padicValRat 2 b) :
    0 ≤ padicValRat 2 (a + b) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases eq_or_ne (a + b) 0 with h | h
  · simp [h]
  · exact le_trans (le_min ha hb) (padicValRat.min_le_padicValRat_add h)

/-- Scaling by `2^n` raises the `2`-adic valuation by `n`: `padicValRat 2 (2^n * q) = n + padicValRat
2 q` for `q ≠ 0`. -/
theorem padicValRat_two_pow_mul {q : ℚ} (hq : q ≠ 0) (n : ℕ) :
    padicValRat 2 ((2 : ℚ) ^ n * q) = n + padicValRat 2 q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : padicValRat 2 (2 : ℚ) = 1 := padicValRat.self (by norm_num)
  rw [padicValRat.mul (by positivity) hq, padicValRat.pow (by norm_num : (2 : ℚ) ≠ 0), h2]
  ring

/-- `sde₂ q ≤ n` exactly says `2^n · q` is a `2`-adic integer (or `q = 0`). -/
theorem sde2_le_iff_two_pow_mul {q : ℚ} {n : ℕ} :
    sde2 q ≤ n ↔ (0 ≤ padicValRat 2 ((2 : ℚ) ^ n * q) ∨ q = 0) := by
  rcases eq_or_ne q 0 with hq | hq
  · simp [hq]
  · rw [sde2_le_iff, padicValRat_two_pow_mul hq]
    constructor
    · intro h; left; omega
    · rintro (h | h)
      · omega
      · exact absurd h hq

/-- **Fact 3.14** (arXiv:2401.08950 §3.4): the half-sum of four dyadic numbers raises `sde₂` by at
most one — `sde₂((v₁ + v₂ + v₃ + v₄)/2) ≤ max sde₂(vᵢ) + 1`. This is the per-step `+1` increase bound
behind Lemma 3.16: each entry of `Ĝ·Û` is `(1/2)·(±v₁ ± v₂ ± v₃ ± v₄)` of four entries of `Û` (the
row-addition trick, Theorem 3.8.3). -/
theorem sde2_half_sum_le (v₁ v₂ v₃ v₄ : ℚ) :
    sde2 ((v₁ + v₂ + v₃ + v₄) / 2)
      ≤ max (max (sde2 v₁) (sde2 v₂)) (max (sde2 v₃) (sde2 v₄)) + 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := max (max (sde2 v₁) (sde2 v₂)) (max (sde2 v₃) (sde2 v₄)) with hK
  -- each vᵢ has 2^K-scaling a 2-adic integer (or is 0); their (signed) sum does too
  have hbnd : ∀ v : ℚ, sde2 v ≤ K → 0 ≤ padicValRat 2 ((2 : ℚ) ^ K * v) ∨ v = 0 := fun v hv =>
    (sde2_le_iff_two_pow_mul).mp hv
  have h1 : sde2 v₁ ≤ K := le_trans (le_max_left _ _) (le_max_left _ _)
  have h2 : sde2 v₂ ≤ K := le_trans (le_max_right _ _) (le_max_left _ _)
  have h3 : sde2 v₃ ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have h4 : sde2 v₄ ≤ K := le_trans (le_max_right _ _) (le_max_right _ _)
  -- the "2-adic integer or 0" predicate, closed under addition
  have Padd : ∀ a b : ℚ, (0 ≤ padicValRat 2 ((2:ℚ)^K * a) ∨ a = 0) →
      (0 ≤ padicValRat 2 ((2:ℚ)^K * b) ∨ b = 0) →
      (0 ≤ padicValRat 2 ((2:ℚ)^K * (a + b)) ∨ a + b = 0) := by
    intro a b ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · left; rw [mul_add]; exact padicValRat_add_nonneg ha hb
    · subst hb; simpa using Or.inl ha
    · subst ha; simpa using Or.inl hb
    · subst ha; subst hb; right; ring
  have hsum := Padd _ _ (Padd _ _ (Padd _ _ (hbnd v₁ h1) (hbnd v₂ h2)) (hbnd v₃ h3)) (hbnd v₄ h4)
  -- conclude: sde2 ((sum)/2) ≤ K + 1
  rw [sde2_le_iff_two_pow_mul]
  rcases hsum with hsum | hsum
  · left
    rw [show ((2:ℚ)^(K+1)) * ((v₁ + v₂ + v₃ + v₄)/2) = (2:ℚ)^K * (v₁ + v₂ + v₃ + v₄) from by
      rw [pow_succ]; ring]
    exact hsum
  · right; rw [hsum]; ring

end SKEFTHawking.FKLW.MukhopadhyayCCZ
