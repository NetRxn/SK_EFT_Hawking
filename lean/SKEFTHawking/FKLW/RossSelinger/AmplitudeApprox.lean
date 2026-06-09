/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 2 (increment 8) — the unconditional amplitude approximation (rounding → ε)

Increments 1–7 built the *number-theoretic* core of the KMM (arXiv:1212.0822) ≤2-ancilla z-rotation
synthesis: the keystone Diophantine completion (`exists_two_relativeNorms_of_nat`) and the normalized
ancilla *state* `(u, t₁, t₂)/√2^{2k}` whose existence is **unconditional** (`kmm_ancilla_state_exists`).
What was missing — flagged by the gate as the open headline content — is the **quantitative `ε`**: that
the prepared `|00⟩`-amplitude `u/2^k` actually approximates the continuous target `e^{iφ}`, and how the
denominator exponent `k` controls the error. This file ships that bridge, **unconditionally**.

The KMM rounding picks the Gaussian approximant `u = m₁ + m₂·i` with `m₁ = round(2^k cos φ)`,
`m₂ = round(2^k sin φ)`. Rounding *toward zero* keeps the approximant inside the disk
(`m₁² + m₂² ≤ 4^k`, the §5 constraint that `kmm_ancilla_state_exists` consumes) while bounding each
coordinate error by `1`. Pushed through the shipped `ZOmegaSqrt2 →+* ℂ` embedding (`toComplex`,
`s2C = √2`, `ω² = i`), this gives the exact amplitude `(m₁ + m₂ i)/2^k` and the **operator-relevant
amplitude bound `‖u/2^k − e^{iφ}‖ ≤ √2/2^k`** (error `O(2^{−k})`).

## Headlines

  * `exists_round_toward_zero` — round-toward-zero existence: `∃ m, m² ≤ x² ∧ |x − m| ≤ 1`.
  * `toComplex_gaussian_approx` — `toComplex (mk (m₁ + m₂·ω²) (2k)) = (m₁ + m₂·i)/2^k` (the embedding
    sends the KMM Gaussian approximant to its analytic amplitude).
  * `kmm_amplitude_approx` — **for every `φ : ℝ` and `k : ℕ` there is a disk-bounded Gaussian
    approximant whose amplitude is within `√2/2^k` of `e^{iφ}`, UNCONDITIONALLY.**
  * `kmm_ancilla_state_approx` — **the milestone**: combines the unconditional normalized ancilla
    state (inc 7) with this amplitude bound — the KMM ancilla state realizing an amplitude within
    `√2/2^k` of `e^{iφ}` exists for *every* `(φ, k)`, with NO prime-density / relative-norm hypothesis.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide`. Kernel-pure `{propext, Classical.choice, Quot.sound}`.
-/

import SKEFTHawking.FKLW.RossSelinger.AncillaState
import SKEFTHawking.FKLW.RossSelinger.ComplexEmbeddingSqrt2

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

open ZOmegaSqrt2

/-- **Round toward zero.** For every real `x` there is an integer `m` whose magnitude does not exceed
`|x|` (`m² ≤ x²`) and which is within distance `1` of `x`. The toward-zero choice (`⌊x⌋` for `x ≥ 0`,
`⌈x⌉` for `x < 0`) is exactly what keeps the KMM approximant inside the disk `m₁² + m₂² ≤ 4^k`. -/
theorem exists_round_toward_zero (x : ℝ) :
    ∃ m : ℤ, (m : ℝ) ^ 2 ≤ x ^ 2 ∧ |x - (m : ℝ)| ≤ 1 := by
  rcases le_or_gt 0 x with hx | hx
  · refine ⟨⌊x⌋, ?_, ?_⟩
    · have h0 : (0 : ℝ) ≤ (⌊x⌋ : ℝ) := by exact_mod_cast Int.floor_nonneg.mpr hx
      have h1 : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
      nlinarith [h0, h1]
    · have h1 : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
      have h2 : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
      rw [abs_le]; constructor <;> linarith
  · refine ⟨⌈x⌉, ?_, ?_⟩
    · have h0 : (⌈x⌉ : ℝ) ≤ 0 := by
        have hc : ⌈x⌉ ≤ (0 : ℤ) := Int.ceil_le.mpr (by exact_mod_cast le_of_lt hx)
        exact_mod_cast hc
      have h1 : x ≤ (⌈x⌉ : ℝ) := Int.le_ceil x
      nlinarith [h0, h1]
    · have h1 : x ≤ (⌈x⌉ : ℝ) := Int.le_ceil x
      have h2 : (⌈x⌉ : ℝ) < x + 1 := Int.ceil_lt_add_one x
      rw [abs_le]; constructor <;> linarith

/-- **`ω² ↦ i` under the embedding.** `ZOmega.toComplex (ω²) = Complex.I` (`ω = e^{iπ/4}`,
`ω² = e^{iπ/2} = i`). -/
theorem toComplex_omega_sq : ZOmega.toComplex (ZOmega.ω ^ 2) = Complex.I := by
  rw [map_pow, show ZOmega.toComplex ZOmega.ω = ZOmega.omegaC from by simp [ZOmega.ω],
    ZOmega.omegaC_sq]

/-- **The embedding sends the KMM Gaussian approximant to its analytic amplitude.**
`toComplex (mk (m₁ + m₂·ω²) (2k)) = (m₁ + m₂·i)/2^k` — combines `toComplex_mk`, `s2C² = 2`
(so `s2C^{2k} = 2^k`), and `ω² ↦ i`. -/
theorem toComplex_gaussian_approx (m₁ m₂ : ℤ) (k : ℕ) :
    ZOmegaSqrt2.toComplex
        (ZOmegaSqrt2.mk ((m₁ : ZOmega) + (m₂ : ZOmega) * ZOmega.ω ^ 2) (2 * k))
      = ((m₁ : ℂ) + (m₂ : ℂ) * Complex.I) / (2 : ℂ) ^ k := by
  rw [ZOmegaSqrt2.toComplex_mk,
    show ZOmegaSqrt2.s2C ^ (2 * k) = (2 : ℂ) ^ k from by rw [pow_mul, ZOmegaSqrt2.s2C_sq]]
  congr 1
  simp only [map_add, map_mul, map_intCast, toComplex_omega_sq]

/-- **Unconditional amplitude approximation (the headline `ε`).** For every phase `φ` and denominator
exponent `k`, there is a Gaussian approximant `u = m₁ + m₂·ω²` that (i) lies in the KMM disk
`m₁² + m₂² ≤ 4^k` (the §5 rounding constraint `kmm_ancilla_state_exists` consumes) and (ii) whose
cleared amplitude `u/2^k` is within `√2/2^k` of the target `e^{iφ}` — error `O(2^{−k})`,
**UNCONDITIONALLY** (no relative-norm / prime-density hypothesis). -/
theorem kmm_amplitude_approx (φ : ℝ) (k : ℕ) :
    ∃ m₁ m₂ : ℤ, m₁ ^ 2 + m₂ ^ 2 ≤ 4 ^ k ∧
      ‖ZOmegaSqrt2.toComplex
            (ZOmegaSqrt2.mk ((m₁ : ZOmega) + (m₂ : ZOmega) * ZOmega.ω ^ 2) (2 * k))
          - Complex.exp ((φ : ℂ) * Complex.I)‖ ≤ Real.sqrt 2 / (2 : ℝ) ^ k := by
  obtain ⟨m₁, hm₁sq, hm₁err⟩ := exists_round_toward_zero ((2 : ℝ) ^ k * Real.cos φ)
  obtain ⟨m₂, hm₂sq, hm₂err⟩ := exists_round_toward_zero ((2 : ℝ) ^ k * Real.sin φ)
  have h4 : ((2 : ℝ) ^ k) ^ 2 = (4 : ℝ) ^ k := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  refine ⟨m₁, m₂, ?_, ?_⟩
  · have key : (m₁ : ℝ) ^ 2 + (m₂ : ℝ) ^ 2 ≤ (4 : ℝ) ^ k := by
      have e1 : ((2 : ℝ) ^ k * Real.cos φ) ^ 2 + ((2 : ℝ) ^ k * Real.sin φ) ^ 2 = (4 : ℝ) ^ k := by
        rw [mul_pow, mul_pow, h4]
        linear_combination (4 : ℝ) ^ k * Real.sin_sq_add_cos_sq φ
      linarith [hm₁sq, hm₂sq]
    exact_mod_cast key
  · rw [toComplex_gaussian_approx]
    have hexp : Complex.exp ((φ : ℂ) * Complex.I)
        = (Real.cos φ : ℂ) + (Real.sin φ : ℂ) * Complex.I := by
      rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have hA0 : (2 : ℂ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
    have hApos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    set P : ℝ := (m₁ : ℝ) - (2 : ℝ) ^ k * Real.cos φ with hP
    set Q : ℝ := (m₂ : ℝ) - (2 : ℝ) ^ k * Real.sin φ with hQ
    have hkey : ((m₁ : ℂ) + (m₂ : ℂ) * Complex.I) / (2 : ℂ) ^ k
          - Complex.exp ((φ : ℂ) * Complex.I)
        = ((P : ℂ) + (Q : ℂ) * Complex.I) / (2 : ℂ) ^ k := by
      rw [hexp, hP, hQ]; field_simp; push_cast; ring
    have hnorm2 : ‖(2 : ℂ) ^ k‖ = (2 : ℝ) ^ k := by rw [norm_pow]; norm_num
    have hPQnorm : ‖(P : ℂ) + (Q : ℂ) * Complex.I‖ = Real.sqrt (P ^ 2 + Q ^ 2) := by
      rw [Complex.norm_add_mul_I]
    have hP1 : |P| ≤ 1 := by rw [hP, abs_sub_comm]; exact hm₁err
    have hQ1 : |Q| ≤ 1 := by rw [hQ, abs_sub_comm]; exact hm₂err
    have hPQ2 : P ^ 2 + Q ^ 2 ≤ 2 := by
      nlinarith [sq_abs P, sq_abs Q, hP1, hQ1, abs_nonneg P, abs_nonneg Q]
    rw [hkey, norm_div, hnorm2, hPQnorm]
    gcongr

/-- **Milestone — the unconditional KMM ancilla state that approximates `e^{iφ}`.** For *every* phase
`φ` and denominator exponent `k`, there exist a Gaussian approximant `u = m₁ + m₂·ω²` and ancilla
completion entries `t₁, t₂ ∈ ℤ[ω]` such that:

  * `(u, t₁, t₂)/√2^{2k}` is a genuine **normalized** (system + 2-ancilla) state (`Σ|·|² = 1`); and
  * the prepared `|00⟩`-amplitude `u/2^k` is within `√2/2^k` of the continuous target `e^{iφ}`.

This is the KMM z-rotation ancilla state, **existing unconditionally** (the completion `t₁, t₂` always
exist by Lagrange four-squares; the approximation error is controlled by the rounding) — NO
prime-density / relative-norm hypothesis. The remaining headline brick is circuit `C`'s O(k)
Clifford+T synthesis of this state plus the controlled-`C`/leakage operator-norm bound. -/
theorem kmm_ancilla_state_approx (φ : ℝ) (k : ℕ) :
    ∃ (m₁ m₂ : ℤ) (t₁ t₂ : ZOmega),
      normSq (mk ((m₁ : ZOmega) + (m₂ : ZOmega) * ZOmega.ω ^ 2) (2 * k))
          + normSq (mk t₁ (2 * k)) + normSq (mk t₂ (2 * k)) = 1
        ∧ ‖ZOmegaSqrt2.toComplex (mk ((m₁ : ZOmega) + (m₂ : ZOmega) * ZOmega.ω ^ 2) (2 * k))
              - Complex.exp ((φ : ℂ) * Complex.I)‖ ≤ Real.sqrt 2 / (2 : ℝ) ^ k := by
  obtain ⟨m₁, m₂, hdisk, hamp⟩ := kmm_amplitude_approx φ k
  obtain ⟨t₁, t₂, hnorm⟩ := kmm_ancilla_state_exists m₁ m₂ k hdisk
  exact ⟨m₁, m₂, t₁, t₂, hnorm, hamp⟩

end SKEFTHawking.RossSelinger
