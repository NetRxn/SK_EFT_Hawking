/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y (D) witness substrate — closed form of `exp` on idempotents and involutions

In any complex Banach algebra `𝔸`:

  * **idempotent** (`P² = P`): `exp(z • P) = 1 + (exp z − 1) • P`.
  * **scalar** : `exp(c • 1) = (exp c) • 1`.
  * **involution** (`J² = 1`): `exp(z • J) = (cosh z) • 1 + (sinh z) • J`.

These are the missing-from-Mathlib closed forms needed to put the Mølmer-Sørensen gate
`MSGate_SU4(θ) = exp(−iθ/2 • (σ_x ⊗ σ_x))` in explicit form (`σ_x ⊗ σ_x` is an involution), which
in turn drives the entangling tangent flow `Ad_{MS(π/2)}(X₃₀) = −X₂₁` of the trapped-ion SU(4)
`ClosureDenseWitness`.

Proof of the idempotent case: split `1 = P + (1 − P)` and use that `(z•P)·(1−P) = 0` while
`(z•P)^n · P = z^n • P`, so `exp(z•P)·P = (exp z)•P` and `exp(z•P)·(1−P) = 1−P`.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A1′ provenance

Phase 6y Roadmap §"Track T-A1′ detail" sub-wave T-A1′.2 PROPER — (D) witness exp-of-involution
substrate. 2026-05-28.
-/

import Mathlib

set_option autoImplicit false

namespace SKEFTHawking.FKLW

open NormedSpace

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]

/-- **exp of a scaled idempotent**: `exp(z • P) = 1 + (exp z − 1) • P` for `P² = P`. -/
theorem exp_smul_idempotent (P : 𝔸) (hP : P * P = P) (z : ℂ) :
    NormedSpace.exp (z • P) = 1 + (Complex.exp z - 1) • P := by
  have hsum : Summable (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • (z • P) ^ n) :=
    NormedSpace.expSeries_summable' (𝕂 := ℂ) (z • P)
  have htsum : NormedSpace.exp (z • P) = ∑' n : ℕ, ((n.factorial : ℂ)⁻¹) • (z • P) ^ n := by
    rw [NormedSpace.exp_eq_tsum ℂ]
  have hpow : ∀ n : ℕ, 0 < n → (z • P) ^ n = z ^ n • P := by
    intro n hn
    induction n with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simp
      · rw [pow_succ', ih hk, smul_mul_smul_comm, hP, ← pow_succ']
  have hterm : ∀ n : ℕ, (z • P) ^ n * P = z ^ n • P := by
    intro n
    induction n with
    | zero => simp
    | succ k ih => rw [pow_succ', mul_assoc, ih, smul_mul_smul_comm, hP, ← pow_succ']
  have hexpz : ∑' n : ℕ, ((n.factorial : ℂ)⁻¹) * z ^ n = Complex.exp z := by
    have h1 : NormedSpace.exp z = Complex.exp z := Complex.exp_eq_exp_ℂ ▸ rfl
    rw [← h1, NormedSpace.exp_eq_tsum ℂ]; simp [smul_eq_mul]
  have hgsum : Summable (fun n : ℕ => ((n.factorial : ℂ)⁻¹) * z ^ n) := by
    simpa [smul_eq_mul] using (NormedSpace.expSeries_summable' (𝕂 := ℂ) z)
  have hPmul : NormedSpace.exp (z • P) * P = (Complex.exp z) • P := by
    rw [htsum, ← Summable.tsum_mul_right P hsum]
    rw [show (fun n : ℕ => ((n.factorial : ℂ)⁻¹ • (z • P) ^ n) * P)
          = (fun n => (((n.factorial : ℂ)⁻¹ * z ^ n)) • P) from by
        funext n; rw [smul_mul_assoc, hterm, smul_smul]]
    rw [Summable.tsum_smul_const hgsum, hexpz]
  have h1Pmul : NormedSpace.exp (z • P) * (1 - P) = 1 - P := by
    rw [htsum, ← Summable.tsum_mul_right (1 - P) hsum]
    rw [tsum_eq_single 0 (fun n hn => ?_)]
    · simp
    · rw [smul_mul_assoc, hpow n (Nat.pos_of_ne_zero hn), smul_mul_assoc, mul_sub, mul_one, hP,
        sub_self, smul_zero, smul_zero]
  have hsplit : NormedSpace.exp (z • P)
      = NormedSpace.exp (z • P) * P + NormedSpace.exp (z • P) * (1 - P) := by
    rw [← mul_add]; simp
  rw [hsplit, hPmul, h1Pmul, sub_smul, one_smul]; abel

/-- **exp of a scalar**: `exp(c • 1) = (exp c) • 1`. -/
theorem exp_smul_one (c : ℂ) :
    NormedSpace.exp (c • (1 : 𝔸)) = (Complex.exp c) • (1 : 𝔸) := by
  rw [exp_smul_idempotent (1 : 𝔸) (one_mul 1) c, sub_smul, one_smul]; abel

/-- **exp of a scaled involution**: `exp(z • J) = (cosh z) • 1 + (sinh z) • J` for `J² = 1`. -/
theorem exp_smul_involution [NormedAlgebra ℚ 𝔸] (J : 𝔸) (hJ : J * J = 1) (z : ℂ) :
    NormedSpace.exp (z • J) = (Complex.cosh z) • (1 : 𝔸) + (Complex.sinh z) • J := by
  set P : 𝔸 := (2⁻¹ : ℂ) • ((1 : 𝔸) + J) with hP_def
  have hPidem : P * P = P := by
    have h : ((1 : 𝔸) + J) * (1 + J) = ((1 : 𝔸) + J) + (1 + J) := by
      rw [mul_add, add_mul, add_mul]; simp only [one_mul, mul_one, hJ]; abel
    rw [hP_def, smul_mul_smul_comm, h, ← two_smul ℂ, smul_smul]
    norm_num
  have hzJ : z • J = (2 * z) • P + (-z) • (1 : 𝔸) := by
    rw [hP_def, smul_smul, show (2 * z) * 2⁻¹ = z from by ring, smul_add, neg_smul]; abel
  have hcomm : Commute ((2 * z) • P) ((-z) • (1 : 𝔸)) :=
    ((Commute.one_right P).smul_left (2 * z)).smul_right (-z)
  have h2z : Complex.exp (2 * z) = Complex.exp z * Complex.exp z := by
    rw [show (2 : ℂ) * z = z + z from by ring, Complex.exp_add]
  have ha : Complex.exp z ≠ 0 := Complex.exp_ne_zero z
  rw [hzJ, NormedSpace.exp_add_of_commute hcomm, exp_smul_idempotent P hPidem, exp_smul_one,
    mul_smul_comm, mul_one, smul_add, smul_smul, hP_def, smul_smul, smul_add,
    ← add_assoc, ← add_smul]
  congr 1
  · congr 1; rw [Complex.cosh, h2z, Complex.exp_neg]; field_simp; ring
  · congr 1; rw [Complex.sinh, h2z, Complex.exp_neg]; field_simp

/-- **exp at the quarter-turn of an involution**: `exp((i·π/2) • J) = i • J` for `J² = 1`.

Generic form of the `xKronX` quarter-turn (`exp_iHalfPi_xKronX`); the single-qubit Clifford
conjugations `exp(−iπ/4·σ_c)·σ_a·exp(iπ/4·σ_c)` factor through this. -/
theorem exp_iHalfPi_involution [NormedAlgebra ℚ 𝔸] (J : 𝔸) (hJ : J * J = 1) :
    NormedSpace.exp ((Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) • J) = Complex.I • J := by
  rw [exp_smul_involution J hJ]
  rw [show Complex.cosh (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) = 0 by
        rw [mul_comm, Complex.cosh_mul_I]; simp [Complex.cos_pi_div_two]]
  rw [show Complex.sinh (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) = Complex.I by
        rw [mul_comm, Complex.sinh_mul_I]; simp [Complex.sin_pi_div_two]]
  rw [zero_smul, zero_add]

/-- **exp through an anticommuting element**: if `A * B = −(B * A)` then
`exp A * B = B * exp(−A)`. (Each `A` moved past `B` flips its sign: `Aⁿ·B = B·(−A)ⁿ`.) -/
theorem exp_mul_of_anticommute (A B : 𝔸) (hAB : A * B = -(B * A)) :
    NormedSpace.exp A * B = B * NormedSpace.exp (-A) := by
  have hpow : ∀ n : ℕ, A ^ n * B = B * (-A) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ k ih => rw [pow_succ', mul_assoc, ih, ← mul_assoc, hAB, pow_succ']; noncomm_ring
  have hsumA : Summable (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • A ^ n) :=
    NormedSpace.expSeries_summable' (𝕂 := ℂ) A
  have hsumnA : Summable (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • (-A) ^ n) :=
    NormedSpace.expSeries_summable' (𝕂 := ℂ) (-A)
  have hA : NormedSpace.exp A = ∑' n : ℕ, ((n.factorial : ℂ)⁻¹) • A ^ n := by
    rw [NormedSpace.exp_eq_tsum ℂ]
  have hnA : NormedSpace.exp (-A) = ∑' n : ℕ, ((n.factorial : ℂ)⁻¹) • (-A) ^ n := by
    rw [NormedSpace.exp_eq_tsum ℂ]
  rw [hA, hnA, ← Summable.tsum_mul_right B hsumA, ← Summable.tsum_mul_left B hsumnA]
  congr 1
  funext n
  rw [smul_mul_assoc, hpow, mul_smul_comm]

end SKEFTHawking.FKLW
