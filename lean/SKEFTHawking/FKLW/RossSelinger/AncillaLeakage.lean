/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 2 (increment 9) — the KMM leakage bound (the dominant `O(2^{−k/2})` error)

The KMM (arXiv:1212.0822) circuit is **deterministic**: the ancilla-`|1⟩` part of the prepared state
`|v⟩ = (u, t₁, t₂)/√2^{2k}` is *not* post-selected away — it is the **leakage** `|g⟩`, a bounded
approximation error folded into `ε`. This file ships that bound. The leakage's squared norm is exactly
`1 − |amplitude|²` (the prepared state is normalized — inc 7), and inc 8's amplitude accuracy
`‖u/2^k − e^{iφ}‖ ≤ √2/2^k` forces `|amplitude|² ≥ 1 − 2·√2/2^k` (reverse triangle, `‖e^{iφ}‖ = 1`).
Hence the leakage `Σ_{ancilla≠00}|·|² ≤ 2·√2/2^k`, i.e. `O(2^{−k})` in the squared norm and the
**`O(2^{−0.5k})` leakage amplitude** the KMM error estimate quotes.

This completes the *error budget* half of the headline `‖W − Λ(e^{iφ})⊗I‖ ≤ ε`: both the amplitude
error (inc 8) and the leakage (here) are now quantitative and unconditional. The remaining headline
brick is purely the **circuit synthesis** of `|v⟩` (the `O(k)` Clifford+T word) and its assembly.

## Headlines

  * `toComplex_normSq` — the ring norm maps to the complex squared modulus:
    `toComplex (normSq z) = ↑(Complex.normSq (toComplex z))` (`toComplex` is a `*`-hom).
  * `kmm_ancilla_state_full` — **for every `φ, k`: a normalized KMM ancilla state whose `|00⟩`
    amplitude is within `√2/2^k` of `e^{iφ}` AND whose total leakage (ancilla-`|1⟩` mass) is
    `≤ 2·√2/2^k`, UNCONDITIONALLY** (no prime-density / relative-norm hypothesis).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide`. Kernel-pure `{propext, Classical.choice, Quot.sound}`.
-/

import SKEFTHawking.FKLW.RossSelinger.AmplitudeApprox
import SKEFTHawking.FKLW.RossSelinger.GridCompileCorrect

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

open ZOmegaSqrt2

/-- **The ring norm maps to the complex squared modulus.** `toComplex (normSq z) =
↑(Complex.normSq (toComplex z))` — `normSq z = z · conj z` and `toComplex` intertwines the ring
conjugation with complex conjugation (`toComplex_conj`). -/
theorem toComplex_normSq (z : ZOmegaSqrt2) :
    ZOmegaSqrt2.toComplex (ZOmegaSqrt2.normSq z)
      = (Complex.normSq (ZOmegaSqrt2.toComplex z) : ℂ) := by
  rw [show ZOmegaSqrt2.normSq z = z * ZOmegaSqrt2.conj z from rfl, map_mul,
    ZOmegaSqrt2.toComplex_conj,
    show star (ZOmegaSqrt2.toComplex z) = (starRingEnd ℂ) (ZOmegaSqrt2.toComplex z) from rfl,
    Complex.mul_conj]

/-- **The full unconditional KMM ancilla state: normalized, amplitude-accurate, bounded leakage.**
For every phase `φ` and denominator exponent `k`, there exist a Gaussian approximant `u = m₁ + m₂·ω²`
and ancilla completion entries `t₁, t₂ ∈ ℤ[ω]` such that the cleared column `(u, t₁, t₂)/√2^{2k}`:

  * is a **normalized** (system + 2-ancilla) state (`Σ|·|² = 1`);
  * has `|00⟩` amplitude within `√2/2^k` of the target `e^{iφ}` (inc 8); and
  * has **total leakage `‖t₁/√2^{2k}‖² + ‖t₂/√2^{2k}‖² ≤ 2·√2/2^k`** — the ancilla-`|1⟩` mass folded
    into the KMM `ε` (the `O(2^{−0.5k})` leakage amplitude), bounded *deterministically* (no
    post-selection).

**UNCONDITIONALLY** — `t₁, t₂` exist by Lagrange four-squares (the keystone) and both error terms are
controlled by the rounding; NO prime-density / relative-norm hypothesis. -/
theorem kmm_ancilla_state_full (φ : ℝ) (k : ℕ) :
    ∃ (m₁ m₂ : ℤ) (t₁ t₂ : ZOmega),
      normSq (mk ((m₁ : ZOmega) + (m₂ : ZOmega) * ZOmega.ω ^ 2) (2 * k))
          + normSq (mk t₁ (2 * k)) + normSq (mk t₂ (2 * k)) = 1
        ∧ ‖ZOmegaSqrt2.toComplex (mk ((m₁ : ZOmega) + (m₂ : ZOmega) * ZOmega.ω ^ 2) (2 * k))
              - Complex.exp ((φ : ℂ) * Complex.I)‖ ≤ Real.sqrt 2 / (2 : ℝ) ^ k
        ∧ Complex.normSq (ZOmegaSqrt2.toComplex (mk t₁ (2 * k)))
              + Complex.normSq (ZOmegaSqrt2.toComplex (mk t₂ (2 * k)))
            ≤ 2 * (Real.sqrt 2 / (2 : ℝ) ^ k) := by
  obtain ⟨m₁, m₂, hdisk, hamp⟩ := kmm_amplitude_approx φ k
  obtain ⟨t₁, t₂, hnorm⟩ := kmm_ancilla_state_exists m₁ m₂ k hdisk
  refine ⟨m₁, m₂, t₁, t₂, hnorm, hamp, ?_⟩
  set u : ZOmega := (m₁ : ZOmega) + (m₂ : ZOmega) * ZOmega.ω ^ 2 with hu
  set δ : ℝ := Real.sqrt 2 / (2 : ℝ) ^ k with hδ
  set au : ℂ := ZOmegaSqrt2.toComplex (mk u (2 * k)) with hau
  have hmap : Complex.normSq au
        + Complex.normSq (ZOmegaSqrt2.toComplex (mk t₁ (2 * k)))
        + Complex.normSq (ZOmegaSqrt2.toComplex (mk t₂ (2 * k))) = 1 := by
    have h := congrArg ZOmegaSqrt2.toComplex hnorm
    rw [map_add, map_add, toComplex_normSq, toComplex_normSq, toComplex_normSq, map_one] at h
    exact_mod_cast h
  have hnnδ : (0 : ℝ) ≤ δ := by rw [hδ]; positivity
  have he1 : ‖Complex.exp ((φ : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I φ
  have hge : 1 - δ ≤ ‖au‖ := by
    have h1 := norm_sub_norm_le (Complex.exp ((φ : ℂ) * Complex.I)) au
    rw [he1, norm_sub_rev] at h1
    linarith [hamp]
  have hnn : (0 : ℝ) ≤ ‖au‖ := norm_nonneg _
  have hsq : Complex.normSq au = ‖au‖ ^ 2 := by
    rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg au)]
  have hkey : 1 - 2 * δ ≤ Complex.normSq au := by
    rw [hsq]; nlinarith [hge, hnn, hnnδ, sq_nonneg (‖au‖ - 1 + δ)]
  linarith [hmap, hkey]

end SKEFTHawking.RossSelinger
