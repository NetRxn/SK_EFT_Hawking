/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 1(c), increment 6 — Lemma C.20 instances and the Lemma C.21 criterion

The Lemma C.20 engine (`daggerDecomposable_of_prime_dvd_normSq`) specialized to the paper's
witnesses, with the quadratic-residue inputs from Mathlib:

  * `p = 2`: `√2 = λ⁻¹·δ†δ` explicitly (`δ = 1 + ω`);
  * `w = u + i` (`normSq = u² + 1`, difference `2ω²`): primes over `p ≡ 1 (mod 4)`, via
    `ZMod.exists_sq_eq_neg_one_iff`;
  * `w = u + √2·i` (`normSq = u² + 2`, difference `2√2·ω²`): primes over `p ≡ 3 (mod 8)`, via
    `ZMod.exists_sq_eq_neg_two_iff`;

and **Lemma C.21** in iff form at the obstructed primes: for `N(ξ) = ±p`, `p ≡ 7 (mod 8)`,
`ξ^m` is †-decomposable **iff `m` is even** (the even half from
`daggerDecomposable_pow_even`, the odd half from the shipped norm obstruction).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide`. Kernel-pure `{propext, Classical.choice, Quot.sound}`.

## References

  * Ross–Selinger, arXiv:1403.2975v3, Appendix C.5 (Lemmas C.20, C.21, Remark C.22).
-/

import SKEFTHawking.FKLW.RossSelinger.RelNormPrimeCase
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

/-! ### `p = 2`: `√2` is †-decomposable -/

/-- `√2 = λ⁻¹·δ†δ` (`δ = 1 + ω`, `δ†δ = 2 + √2 = λ·√2`). -/
theorem daggerDecomposable_sqrt2 : DaggerDecomposable (⟨0, 1⟩ : Zsqrtd 2) := by
  refine ⟨⟨0, 0, 1, 1⟩, ⟨-1, 1⟩, ?_, ?_⟩
  · exact IsUnit.of_mul_eq_one (⟨1, 1⟩ : Zsqrtd 2) (by decide)
  · have hτ : relNormZsqrt2 (⟨0, 0, 1, 1⟩ : ZOmega) = ⟨2, 1⟩ := by
      apply zsqrt2ToZOmega_injective
      rw [zsqrt2ToZOmega_relNormZsqrt2]
      decide
    rw [hτ]
    decide

/-! ### The `u + i` instance (primes over `p ≡ 1 (mod 4)`) -/

/-- A prime `ξ ∤ 2` of `ℤ[√2]` dividing `u² + 1` is †-decomposable (Lemma C.20, `p ≡ 1 (mod 4)`
mechanism, with `w = u + i`). -/
theorem daggerDecomposable_of_prime_dvd_sq_add_one {ξ : Zsqrtd 2} {u : ℤ}
    (hprime : Prime ξ) (h2 : ¬ ξ ∣ (2 : Zsqrtd 2))
    (hdvd : ξ ∣ ((u ^ 2 + 1 : ℤ) : Zsqrtd 2)) : DaggerDecomposable ξ := by
  refine daggerDecomposable_of_prime_dvd_normSq (w := ⟨0, 1, 0, u⟩) hprime ?_ ?_
  · -- normSq ⟨0,1,0,u⟩ = u² + 1 (as an integer constant of ℤ[ω])
    have hns : ZOmega.normSq ⟨0, 1, 0, u⟩ = ((u ^ 2 + 1 : ℤ) : ZOmega) := by
      rw [normSq_coords]
      show (⟨-(0*1 - 0*u + 0*1 + 0*u), 0, 0*1 - 0*u + 0*1 + 0*u, 0^2 + 1^2 + 0^2 + u^2⟩ : ZOmega)
        = ZOmega.ofInt (u ^ 2 + 1)
      ext <;> simp [ZOmega.ofInt] <;> ring
    rw [hns, show ((u ^ 2 + 1 : ℤ) : ZOmega) = zsqrt2ToZOmega ((u ^ 2 + 1 : ℤ) : Zsqrtd 2) from
      (map_intCast zsqrt2ToZOmega _).symm]
    exact map_dvd zsqrt2ToZOmega hdvd
  · -- the difference is 2ω²; ξ ∣ 2ω² would force ξ ∣ 2
    intro hcon
    have hdiffval : (⟨0, 1, 0, u⟩ : ZOmega) - ZOmega.conj ⟨0, 1, 0, u⟩ = ⟨0, 2, 0, 0⟩ := by
      ext <;> simp [ZOmega.conj]
    rw [hdiffval] at hcon
    have hkill : (⟨0, 2, 0, 0⟩ : ZOmega) * ⟨0, 1, 0, 0⟩ = ((-2 : ℤ) : ZOmega) := by decide
    have h2' : zsqrt2ToZOmega ξ ∣ ((-2 : ℤ) : ZOmega) := by
      rw [← hkill]
      exact Dvd.dvd.mul_right hcon _
    have h2'' : ξ ∣ ((-2 : ℤ) : Zsqrtd 2) := by
      refine zsqrt2_dvd_descent ?_
      rwa [map_intCast]
    have : ξ ∣ (2 : Zsqrtd 2) := by
      have := h2''.neg_right
      simpa using this
    exact h2 this

/-! ### The `u + √2·i` instance (primes over `p ≡ 3 (mod 8)`) -/

/-- A prime `ξ ∤ 2` of `ℤ[√2]` dividing `u² + 2` is †-decomposable (Lemma C.20, `p ≡ 3 (mod 8)`
mechanism, with `w = u + √2·i`). -/
theorem daggerDecomposable_of_prime_dvd_sq_add_two {ξ : Zsqrtd 2} {u : ℤ}
    (hprime : Prime ξ) (h2 : ¬ ξ ∣ (2 : Zsqrtd 2))
    (hdvd : ξ ∣ ((u ^ 2 + 2 : ℤ) : Zsqrtd 2)) : DaggerDecomposable ξ := by
  refine daggerDecomposable_of_prime_dvd_normSq (w := ⟨1, 0, 1, u⟩) hprime ?_ ?_
  · have hns : ZOmega.normSq ⟨1, 0, 1, u⟩ = ((u ^ 2 + 2 : ℤ) : ZOmega) := by
      rw [normSq_coords]
      show (⟨-(1*0 - 1*u + 1*0 + 1*u), 0, 1*0 - 1*u + 1*0 + 1*u, 1^2 + 0^2 + 1^2 + u^2⟩ : ZOmega)
        = ZOmega.ofInt (u ^ 2 + 2)
      ext <;> simp [ZOmega.ofInt] <;> ring
    rw [hns, show ((u ^ 2 + 2 : ℤ) : ZOmega) = zsqrt2ToZOmega ((u ^ 2 + 2 : ℤ) : Zsqrtd 2) from
      (map_intCast zsqrt2ToZOmega _).symm]
    exact map_dvd zsqrt2ToZOmega hdvd
  · intro hcon
    have hdiffval : (⟨1, 0, 1, u⟩ : ZOmega) - ZOmega.conj ⟨1, 0, 1, u⟩ = ⟨2, 0, 2, 0⟩ := by
      ext <;> simp [ZOmega.conj]
    rw [hdiffval] at hcon
    -- (2√2)·√2 = 4
    have hkill : (⟨2, 0, 2, 0⟩ : ZOmega) * ⟨-1, 0, -1, 0⟩ = ((4 : ℤ) : ZOmega) := by decide
    have h4' : zsqrt2ToZOmega ξ ∣ ((4 : ℤ) : ZOmega) := by
      rw [← hkill]
      exact Dvd.dvd.mul_right hcon _
    have h4 : ξ ∣ ((4 : ℤ) : Zsqrtd 2) := by
      refine zsqrt2_dvd_descent ?_
      rwa [map_intCast]
    have h22 : ξ ∣ (2 : Zsqrtd 2) * (2 : Zsqrtd 2) := by
      have : ((4 : ℤ) : Zsqrtd 2) = (2 : Zsqrtd 2) * 2 := by norm_num
      rwa [this] at h4
    rcases hprime.dvd_mul.mp h22 with h | h <;> exact h2 h

/-! ### The quadratic-residue inputs (Remark C.22) -/

/-- Odd primes don't meet `2` in `ℤ[√2]` once they divide an embedded odd rational prime. -/
theorem not_dvd_two_of_dvd_odd_prime {ξ : Zsqrtd 2} {p : ℕ}
    (hprime : Prime ξ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvdp : ξ ∣ ((p : ℤ) : Zsqrtd 2)) : ¬ ξ ∣ (2 : Zsqrtd 2) := by
  intro h2
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
  -- 1 = p − 2m: Bezout in ℤ[√2]
  have hbez : (1 : Zsqrtd 2) = ((p : ℤ) : Zsqrtd 2) - ((m : ℤ) : Zsqrtd 2) * 2 := by
    have : ((p : ℤ) : Zsqrtd 2) = 2 * ((m : ℤ) : Zsqrtd 2) + 1 := by
      have hpz : (p : ℤ) = 2 * (m : ℤ) + 1 := by exact_mod_cast hm
      rw [show ((p : ℤ) : Zsqrtd 2) = (((2 * (m : ℤ) + 1) : ℤ) : Zsqrtd 2) from by rw [← hpz]]
      push_cast
      ring
    rw [this]
    ring
  have h1 : ξ ∣ (1 : Zsqrtd 2) := by
    rw [hbez]
    exact dvd_sub hdvdp (Dvd.dvd.mul_left h2 _)
  exact hprime.not_unit (isUnit_of_dvd_one h1)

/-- **Lemma C.20, `p ≡ 1 (mod 4)`**: a prime of `ℤ[√2]` over a rational prime `p ≡ 1 (mod 4)`
is †-decomposable. -/
theorem daggerDecomposable_of_dvd_prime_one_mod_four {ξ : Zsqrtd 2} {p : ℕ} [hF : Fact p.Prime]
    (hprime : Prime ξ) (hdvdp : ξ ∣ ((p : ℤ) : Zsqrtd 2)) (hp4 : p % 4 = 1) :
    DaggerDecomposable ξ := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨s, hs⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mpr (by omega)
  obtain ⟨u, hus⟩ := ZMod.intCast_surjective s
  have hcast : ((u ^ 2 + 1 : ℤ) : ZMod p) = 0 := by
    push_cast
    rw [hus, pow_two, ← hs]
    ring
  have hpdvd : (p : ℤ) ∣ u ^ 2 + 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hcast
  exact daggerDecomposable_of_prime_dvd_sq_add_one hprime
    (not_dvd_two_of_dvd_odd_prime hprime hF.out hp2 hdvdp)
    (dvd_trans hdvdp (map_dvd (Int.castRingHom (Zsqrtd 2)) hpdvd))

/-- **Lemma C.20, `p ≡ 3 (mod 8)`**: a prime of `ℤ[√2]` over a rational prime `p ≡ 3 (mod 8)`
is †-decomposable. -/
theorem daggerDecomposable_of_dvd_prime_three_mod_eight {ξ : Zsqrtd 2} {p : ℕ}
    [hF : Fact p.Prime] (hprime : Prime ξ) (hdvdp : ξ ∣ ((p : ℤ) : Zsqrtd 2))
    (hp8 : p % 8 = 3) : DaggerDecomposable ξ := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨s, hs⟩ := (ZMod.exists_sq_eq_neg_two_iff (p := p) hp2).mpr (Or.inr hp8)
  obtain ⟨u, hus⟩ := ZMod.intCast_surjective s
  have hcast : ((u ^ 2 + 2 : ℤ) : ZMod p) = 0 := by
    push_cast
    rw [hus, pow_two, ← hs]
    ring
  have hpdvd : (p : ℤ) ∣ u ^ 2 + 2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hcast
  exact daggerDecomposable_of_prime_dvd_sq_add_two hprime
    (not_dvd_two_of_dvd_odd_prime hprime hF.out hp2 hdvdp)
    (dvd_trans hdvdp (map_dvd (Int.castRingHom (Zsqrtd 2)) hpdvd))

/-! ### Lemma C.21 at the obstructed primes -/

/-- The `ℤ[√2]`-norm is multiplicative on powers. -/
theorem zsqrtd_norm_pow (z : Zsqrtd 2) (k : ℕ) :
    Zsqrtd.norm (z ^ k) = (Zsqrtd.norm z) ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    exact Zsqrtd.norm_one
  | succ n ih =>
    rw [pow_succ, pow_succ, Zsqrtd.norm_mul, ih]

/-- **Lemma C.21 at the obstructed primes** (the even-power criterion in iff form): for an
element of norm `±p` with `p ≡ 7 (mod 8)`, the power `ξ^m` is †-decomposable **iff `m` is
even**. (Slightly more general than the paper's statement: `ξ`-primality is not needed, only
the norm value. Connecting an abstract prime `ξ ∣ p` to the `norm ξ = ±p` hypothesis uses the
paper's Lemma C.6 split/inert dichotomy, which is not formalized here — supply the norm
directly, as the compiled witnesses do.) -/
theorem daggerDecomposable_pow_iff_seven {ξ : Zsqrtd 2} {p : ℤ} (hppos : 0 < p)
    (hp7 : p % 8 = 7) (hn : Zsqrtd.norm ξ = p ∨ Zsqrtd.norm ξ = -p) (m : ℕ) :
    DaggerDecomposable (ξ ^ m) ↔ Even m := by
  constructor
  · intro h
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    refine not_daggerDecomposable_of_norm_pow_seven (ξ := ξ ^ m) hppos hp7 hodd ?_ h
    rcases hn with hn | hn
    · left
      rw [zsqrtd_norm_pow, hn]
    · right
      rw [zsqrtd_norm_pow, hn, hodd.neg_pow]
  · exact daggerDecomposable_pow_even ξ

end SKEFTHawking.RossSelinger
