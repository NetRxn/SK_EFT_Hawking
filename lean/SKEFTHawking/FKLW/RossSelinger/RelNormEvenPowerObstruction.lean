/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 1(c), increment 4 — the even-power obstruction (Lemmas C.20/C.21, negative half)

Ross–Selinger arXiv:1403.2975v3 Lemma C.20's `p ≡ 7 (mod 8)` impossibility and Lemma C.21's
odd-power half: a †-decomposable `ξ` has `N_{ℤ[√2]}(ξ) = ±(a² + b²)` — because
`ξ ~ t†t` makes `N(ξ) = ±N(t†t) = ±N_{ℤ[ω]}(t)`, and the `ℤ[i]`-graded Gauss form of the
absolute norm (`norm_eq_gauss`, `ZOmegaEuclideanDomain.lean`) is **manifestly a sum of two
squares** (`a = (t·σ5 t).d`, `b = (t·σ5 t).b` — the paper's `t•t = a + bi ∈ ℤ[i]`).
Sums of two squares are `≢ 7 (mod 8)`, so no `ξ` with `N(ξ) = ±p^m`, `p ≡ 7 (mod 8)`, `m` odd
is †-decomposable. Also the structural positives: even powers are always †-decomposable
(`ξ^{2k} = (embed ξ^k)†(embed ξ^k)`), and †-decomposability is closed under powers.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide`. Kernel-pure `{propext, Classical.choice, Quot.sound}`.

## References

  * Ross–Selinger, arXiv:1403.2975v3, Appendix C.5 (Lemmas C.20 `p ≡ 7` case, C.21).
-/

import SKEFTHawking.FKLW.RossSelinger.RelNormMultiplicativity

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

/-! ### Structural positives -/

/-- The relative norm of an embedded real is its square. -/
theorem relNormZsqrt2_embed (γ : Zsqrtd 2) :
    relNormZsqrt2 (zsqrt2ToZOmega γ) = γ * γ := by
  apply zsqrt2ToZOmega_injective
  rw [zsqrt2ToZOmega_relNormZsqrt2, map_mul]
  show zsqrt2ToZOmega γ * ZOmega.conj (zsqrt2ToZOmega γ) = _
  rw [conj_zsqrt2ToZOmega]

/-- Squares are †-decomposable. -/
theorem daggerDecomposable_sq (ξ : Zsqrtd 2) : DaggerDecomposable (ξ * ξ) :=
  ⟨zsqrt2ToZOmega ξ, 1, isUnit_one, by rw [relNormZsqrt2_embed, one_mul]⟩

/-- †-decomposability is closed under powers. -/
theorem DaggerDecomposable.pow {ξ : Zsqrtd 2} (h : DaggerDecomposable ξ) (m : ℕ) :
    DaggerDecomposable (ξ ^ m) := by
  induction m with
  | zero =>
    exact ⟨1, 1, isUnit_one, by
      rw [pow_zero]
      show 1 * relNormZsqrt2 1 = 1
      rw [show relNormZsqrt2 1 = 1 from by
        apply zsqrt2ToZOmega_injective
        rw [zsqrt2ToZOmega_relNormZsqrt2, map_one]
        exact ZOmega.normSq_one, mul_one]⟩
  | succ n ih =>
    rw [pow_succ]
    exact ih.mul h

/-- **Even powers are always †-decomposable** (Lemma C.21, even case): `ξ^{2k} = (ξ^k)². -/
theorem daggerDecomposable_pow_even (ξ : Zsqrtd 2) {m : ℕ} (hm : Even m) :
    DaggerDecomposable (ξ ^ m) := by
  obtain ⟨k, hk⟩ := hm
  have : ξ ^ m = (ξ ^ k) * (ξ ^ k) := by rw [hk, ← pow_add]
  rw [this]
  exact daggerDecomposable_sq _

/-! ### The norm of a †-decomposable element is `±(a² + b²)` -/

/-- **The sum-of-two-squares form** (the paper's `t•t = a + bi` argument, via the `ℤ[i]`-graded
Gauss form of the `ℤ[ω]`-norm): a †-decomposable `ξ` has `N(ξ) = ±(a² + b²)`. -/
theorem exists_sq_add_sq_of_daggerDecomposable {ξ : Zsqrtd 2} (h : DaggerDecomposable ξ) :
    ∃ a b : ℤ, Zsqrtd.norm ξ = a ^ 2 + b ^ 2 ∨ Zsqrtd.norm ξ = -(a ^ 2 + b ^ 2) := by
  obtain ⟨t, u, hu, heq⟩ := h
  refine ⟨(t * ZOmega.σ5 t).d, (t * ZOmega.σ5 t).b, ?_⟩
  have hnm : Zsqrtd.norm ξ = Zsqrtd.norm u * Zsqrtd.norm (relNormZsqrt2 t) := by
    rw [← heq, Zsqrtd.norm_mul]
  have htower : Zsqrtd.norm (relNormZsqrt2 t)
      = (t * ZOmega.σ5 t).d ^ 2 + (t * ZOmega.σ5 t).b ^ 2 := by
    rw [zsqrtd_norm_relNormZsqrt2]
    exact ZOmega.norm_eq_gauss t
  have habs : (Zsqrtd.norm u).natAbs = 1 := Zsqrtd.norm_eq_one_iff.mpr hu
  rcases Int.natAbs_eq_iff.mp habs with h1 | h1
  · left
    rw [hnm, h1, htower]
    push_cast
    ring
  · right
    rw [hnm, h1, htower]
    push_cast
    ring

/-! ### Sums of two squares are `≢ 7 (mod 8)` -/

theorem sq_emod_eight (c : ℤ) : c ^ 2 % 8 = 0 ∨ c ^ 2 % 8 = 1 ∨ c ^ 2 % 8 = 4 := by
  have hm : c ^ 2 % 8 = (c % 8) ^ 2 % 8 := by
    rw [pow_two, pow_two, Int.mul_emod]
  have h0 : 0 ≤ c % 8 := Int.emod_nonneg c (by norm_num)
  have h8 : c % 8 < 8 := Int.emod_lt_of_pos c (by norm_num)
  have hcases : c % 8 = 0 ∨ c % 8 = 1 ∨ c % 8 = 2 ∨ c % 8 = 3 ∨ c % 8 = 4 ∨ c % 8 = 5 ∨
      c % 8 = 6 ∨ c % 8 = 7 := by omega
  rcases hcases with h | h | h | h | h | h | h | h <;> rw [hm, h] <;> norm_num

/-- Sums of two squares avoid `7 (mod 8)`. -/
theorem sq_add_sq_emod_eight_ne_seven (a b : ℤ) : (a ^ 2 + b ^ 2) % 8 ≠ 7 := by
  have ha := sq_emod_eight a
  have hb := sq_emod_eight b
  have hsum : (a ^ 2 + b ^ 2) % 8 = (a ^ 2 % 8 + b ^ 2 % 8) % 8 := Int.add_emod _ _ _
  rcases ha with h1 | h1 | h1 <;> rcases hb with h2 | h2 | h2 <;>
    rw [hsum, h1, h2] <;> norm_num

/-- Powers of a `7 (mod 8)` number stay `7 (mod 8)` at odd exponents. -/
theorem pow_odd_emod_eight {p : ℤ} (hp : p % 8 = 7) {m : ℕ} (hm : Odd m) :
    p ^ m % 8 = 7 := by
  obtain ⟨k, hk⟩ := hm
  have hsq : p ^ 2 % 8 = 1 := by
    rw [pow_two, Int.mul_emod, hp]
    norm_num
  have hpow : ∀ j : ℕ, (p ^ 2) ^ j % 8 = 1 := by
    intro j
    induction j with
    | zero => norm_num
    | succ n ih =>
      rw [pow_succ, Int.mul_emod, ih, hsq]
      norm_num
  have hexp : p ^ m = (p ^ 2) ^ k * p := by
    rw [← pow_mul, ← pow_succ, hk]
  rw [hexp, Int.mul_emod, hpow k, hp]
  norm_num

/-! ### The even-power obstruction (Lemma C.21, odd case at `p ≡ 7 (mod 8)`) -/

/-- **The even-power obstruction**: if `N(ξ) = ±p^m` with `p ≡ 7 (mod 8)` and `m` odd, then `ξ`
is NOT †-decomposable — a †-decomposable element's norm is `±(a²+b²)`, the sign resolves to `+`
(positivity), and `a² + b² ≡ 7 (mod 8)` is impossible. -/
theorem not_daggerDecomposable_of_norm_pow_seven {ξ : Zsqrtd 2} {p : ℤ} {m : ℕ}
    (hppos : 0 < p) (hp7 : p % 8 = 7) (hm : Odd m)
    (hn : Zsqrtd.norm ξ = p ^ m ∨ Zsqrtd.norm ξ = -(p ^ m)) :
    ¬ DaggerDecomposable ξ := by
  intro h
  obtain ⟨a, b, hab⟩ := exists_sq_add_sq_of_daggerDecomposable h
  have hpm : 0 < p ^ m := pow_pos hppos m
  have hsq : 0 ≤ a ^ 2 + b ^ 2 := by positivity
  -- resolve the four sign combinations to `a² + b² = p^m`
  have hkey : a ^ 2 + b ^ 2 = p ^ m := by
    rcases hn with hn | hn <;> rcases hab with hab | hab
    · rw [hn] at hab
      linarith
    · rw [hn] at hab
      nlinarith
    · rw [hn] at hab
      nlinarith
    · rw [hn] at hab
      linarith
  have h7 := pow_odd_emod_eight hp7 hm
  rw [← hkey] at h7
  exact sq_add_sq_emod_eight_ne_seven a b h7

end SKEFTHawking.RossSelinger
