/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 1(c), increment 5 — Lemma C.20, the positive prime cases

Ross–Selinger arXiv:1403.2975v3 **Lemma C.20** (constructive halves): a prime `ξ` of `ℤ[√2]` is
†-decomposable when it divides a relative norm non-trivially. The paper's `t = gcd(ξ, u + i)`
arguments for `p ≡ 1 (mod 4)` (from `u² ≡ −1`) and `p ≡ 3 (mod 8)` (from `u² ≡ −2`) are both
instances of one **engine**:

> if `ξ` is prime, `ξ ∣ w·w† = normSq w`, and `ξ ∤ (w − w†)`, then `ξ` is †-decomposable

— with `t := gcd(embed ξ, w)` and the three-possibilities analysis `t†t ∣ ξ²` via
`dvd_prime_pow`: the unit case forces `ξ` coprime to both `w` and `w†` hence to `normSq w`
(contradiction), the `ξ²` case forces `embed ξ ∣ w` and (conjugating) `∣ w†`, contradicting
`ξ ∤ (w − w†)`; the middle case is exactly †-decomposability. The divisibility bookkeeping
descends between `ℤ[ω]` and `ℤ[√2]` through conj-fixedness (`exists_zsqrt2_of_conj_fixed`).

Specializations: `w = u + i` (`normSq = u² + 1`, `w − w† = 2ω²`) and `w = u + √2·i`
(`normSq = u² + 2`, `w − w† = 2√2·ω²`), plus the explicit `p = 2` case `√2 = λ⁻¹·δ†δ`.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide`. Kernel-pure `{propext, Classical.choice, Quot.sound}`.

## References

  * Ross–Selinger, arXiv:1403.2975v3, Appendix C.5 (Lemma C.20, constructive cases).
-/

import SKEFTHawking.FKLW.RossSelinger.RelNormEvenPowerObstruction
import Mathlib.RingTheory.EuclideanDomain

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

/-! ### Divisibility descent between `ℤ[ω]` and `ℤ[√2]` -/

/-- Divisibility of embedded elements descends to `ℤ[√2]` (the quotient is conj-fixed). -/
theorem zsqrt2_dvd_descent {a b : Zsqrtd 2}
    (h : zsqrt2ToZOmega a ∣ zsqrt2ToZOmega b) : a ∣ b := by
  obtain ⟨c, hc⟩ := h
  by_cases ha0 : a = 0
  · rw [ha0, map_zero, zero_mul] at hc
    have hb0 : b = 0 := zsqrt2ToZOmega_injective (by rw [hc, map_zero])
    rw [ha0, hb0]
  have hane : zsqrt2ToZOmega a ≠ 0 := fun h0 =>
    ha0 (zsqrt2ToZOmega_injective (by rw [h0, map_zero]))
  have hcconj : ZOmega.conj c = c := by
    have h1 := congrArg ZOmega.conj hc
    rw [conj_zsqrt2ToZOmega, ZOmega.conj_mul, conj_zsqrt2ToZOmega] at h1
    exact (mul_left_cancel₀ hane (hc.symm.trans h1)).symm
  obtain ⟨γ, hγ⟩ := exists_zsqrt2_of_conj_fixed hcconj
  refine ⟨γ, zsqrt2ToZOmega_injective ?_⟩
  rw [map_mul, hγ, hc]

/-- Unitness of an embedded element descends to `ℤ[√2]`. -/
theorem zsqrt2_isUnit_descent {a : Zsqrtd 2}
    (h : IsUnit (zsqrt2ToZOmega a)) : IsUnit a := by
  obtain ⟨z, hz⟩ := h.exists_right_inv
  have hane : zsqrt2ToZOmega a ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hz
    exact one_ne_zero hz.symm
  have hzconj : ZOmega.conj z = z := by
    have h1 := congrArg ZOmega.conj hz
    rw [ZOmega.conj_mul, conj_zsqrt2ToZOmega, ZOmega.conj_one] at h1
    exact mul_left_cancel₀ hane (h1.trans hz.symm)
  obtain ⟨ζ, hζ⟩ := exists_zsqrt2_of_conj_fixed hzconj
  refine IsUnit.of_mul_eq_one ζ (zsqrt2ToZOmega_injective ?_)
  rw [map_mul, hζ, map_one, hz]

/-! ### The three-possibilities engine -/

/-- **The Lemma C.20 engine**: a prime `ξ ∈ ℤ[√2]` dividing a relative norm `w·w†` but not the
difference `w − w†` is †-decomposable, via `t = gcd(embed ξ, w)`. -/
theorem daggerDecomposable_of_prime_dvd_normSq {ξ : Zsqrtd 2} {w : ZOmega}
    (hprime : Prime ξ) (hdvd : zsqrt2ToZOmega ξ ∣ ZOmega.normSq w)
    (hdiff : ¬ zsqrt2ToZOmega ξ ∣ (w - ZOmega.conj w)) :
    DaggerDecomposable ξ := by
  set Ξ : ZOmega := zsqrt2ToZOmega ξ with hΞ
  have hΞconj : ZOmega.conj Ξ = Ξ := conj_zsqrt2ToZOmega ξ
  have hξne : ξ ≠ 0 := hprime.ne_zero
  have hΞne : Ξ ≠ 0 := by
    rw [hΞ]
    intro h0
    exact hξne (zsqrt2ToZOmega_injective (by rw [h0, map_zero]))
  set t : ZOmega := EuclideanDomain.gcd Ξ w with ht
  have htΞ : t ∣ Ξ := EuclideanDomain.gcd_dvd_left Ξ w
  have htw : t ∣ w := EuclideanDomain.gcd_dvd_right Ξ w
  -- t·t† ∣ ξ², descended to ℤ[√2]
  have htt : zsqrt2ToZOmega (relNormZsqrt2 t) ∣ zsqrt2ToZOmega (ξ * ξ) := by
    rw [zsqrt2ToZOmega_relNormZsqrt2, map_mul]
    exact mul_dvd_mul htΞ (by simpa [hΞconj] using map_dvd conjHom htΞ)
  have hττ : relNormZsqrt2 t ∣ ξ * ξ := zsqrt2_dvd_descent htt
  have hττ' : relNormZsqrt2 t ∣ ξ ^ 2 := by rwa [pow_two]
  rcases (dvd_prime_pow hprime 2).mp hττ' with ⟨i, hi, hassoc⟩
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  · -- τ unit ⟹ ξ coprime to w and w† ⟹ ξ ∣ normSq w forces ξ unit: contradiction
    exfalso
    have hτunit : IsUnit (relNormZsqrt2 t) := by
      rw [pow_zero] at hassoc
      exact hassoc.symm.isUnit isUnit_one
    have httunit : IsUnit (t * ZOmega.conj t) := by
      have h1 := hτunit.map zsqrt2ToZOmega
      rwa [zsqrt2ToZOmega_relNormZsqrt2] at h1
    have htunit : IsUnit t := isUnit_of_mul_isUnit_left httunit
    have hcop : IsCoprime Ξ w := EuclideanDomain.gcd_isUnit_iff.mp htunit
    have hcop' : IsCoprime Ξ (ZOmega.conj w) := by
      have h1 := hcop.map conjHom
      simpa [hΞconj] using h1
    have hcopn : IsCoprime Ξ (ZOmega.normSq w) := hcop.mul_right hcop'
    obtain ⟨x, y, hxy⟩ := hcopn
    have hΞ1 : Ξ ∣ 1 := by
      rw [← hxy]
      exact dvd_add (Dvd.dvd.mul_left (dvd_refl Ξ) x) (Dvd.dvd.mul_left hdvd y)
    exact hprime.not_unit (zsqrt2_isUnit_descent (isUnit_of_dvd_one hΞ1))
  · -- the middle case IS †-decomposability
    obtain ⟨u, hu⟩ := hassoc
    rw [pow_one] at hu
    exact ⟨t, (u : Zsqrtd 2), u.isUnit, by rw [mul_comm]; exact hu⟩
  · -- τ ~ ξ² ⟹ embed ξ ∣ w and ∣ w†: contradicts ξ ∤ (w − w†)
    exfalso
    obtain ⟨s, hsdef⟩ := htΞ
    -- ξ² = τ(t)·τ(s) at the ℤ[√2] level
    have hfact : ξ * ξ = relNormZsqrt2 t * relNormZsqrt2 s := by
      apply zsqrt2ToZOmega_injective
      rw [map_mul, map_mul, zsqrt2ToZOmega_relNormZsqrt2, zsqrt2ToZOmega_relNormZsqrt2]
      have hΞΞ : zsqrt2ToZOmega ξ * zsqrt2ToZOmega ξ = Ξ * ZOmega.conj Ξ := by
        rw [hΞconj]
      rw [hΞΞ, hsdef, ZOmega.conj_mul]
      show t * s * (ZOmega.conj t * ZOmega.conj s)
          = t * ZOmega.conj t * (s * ZOmega.conj s)
      ring
    obtain ⟨u, hu⟩ := hassoc
    rw [pow_two] at hu
    have hτne : relNormZsqrt2 t ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hu
      exact hprime.ne_zero (mul_self_eq_zero.mp hu.symm)
    have huval : (u : Zsqrtd 2) = relNormZsqrt2 s := by
      have h1 : relNormZsqrt2 t * (u : Zsqrtd 2) = relNormZsqrt2 t * relNormZsqrt2 s := by
        rw [hu, hfact]
      exact mul_left_cancel₀ hτne h1
    have hsunit : IsUnit s := by
      have h1 : IsUnit (relNormZsqrt2 s) := huval ▸ u.isUnit
      have h2 : IsUnit (ZOmega.normSq s) := by
        have h3 := h1.map zsqrt2ToZOmega
        rwa [zsqrt2ToZOmega_relNormZsqrt2] at h3
      exact isUnit_of_mul_isUnit_left h2
    obtain ⟨z, hz⟩ := hsunit.exists_right_inv
    have hΞt : Ξ ∣ t := ⟨z, by rw [hsdef, mul_assoc, hz, mul_one]⟩
    have hΞw : Ξ ∣ w := dvd_trans hΞt htw
    have hΞcw : Ξ ∣ ZOmega.conj w := by
      have h1 := map_dvd conjHom hΞw
      simpa [hΞconj] using h1
    exact hdiff (dvd_sub hΞw hΞcw)

end SKEFTHawking.RossSelinger
