/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 3, increment 2 — the structural `μ ≤ 3 ⟹ kSO3 ≤ 3` bridge (per-entry bounds)

The Bloch entries of `reconstruct x y k` under the unit-column equation `|x|² + |y|² = √2⁴` and
the `μ ≤ 3` condition `√2 ∣ |x|²` all have `denExp ≤ 3` — proved STRUCTURALLY (no finite check):
each entry's cleared `ℤ[ω]` numerator carries `√2³`, by the `BridgeParity` toolkit:

  * the five `z`-row/column entries have an explicit factor `2 = √2²` and a conjugate-pair
    `(w ± w̄)` (`+1`);
  * the four `x/y`-block entries are `(w ± w̄)` with `w = ω-phase·(x² ∓ y²)`, and
    `√2² ∣ (x² ± y²)` is the `BridgeParity` core (`sqrt2_sq_dvd_sq_add_sub`).

One lemma per Bloch entry (per-declaration heartbeat budgets — invariant #10 decomposition).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide`. Kernel-pure `{propext, Classical.choice, Quot.sound}`.
-/

import SKEFTHawking.FKLW.RossSelinger.BridgeParity
import SKEFTHawking.FKLW.RossSelinger.KMMBridge

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger
namespace KMM

open ZOmegaSqrt2 CliffordTGate

/-- `ωS^k = mk (ω^k) 0` (the phase stays a `ZOmega`-numerator). -/
theorem omegaS_pow_mk (k : ℕ) : (ωS : ZOmegaSqrt2) ^ k = mk (ZOmega.ω ^ k) 0 := by
  induction k with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, ih]
    show mk (ZOmega.ω ^ n) 0 * mk ZOmega.ω 0 = _
    rw [mk_mul, ← pow_succ]

/-- The phase–conjugate-phase product is `1`: `ω^k · conj (ω^k) = 1`. -/
theorem omega_pow_mul_conj (k : ℕ) : ZOmega.ω ^ k * ZOmega.conj (ZOmega.ω ^ k) = 1 := by
  show ZOmega.normSq (ZOmega.ω ^ k) = 1
  exact ZOmega.normSq_omega_pow k

/-- `iS = mk (ω·ω) 0` (the `i = ω²` phase as a cleared numerator). -/
theorem iS_mk : iS = mk (ZOmega.ω * ZOmega.ω) 0 := rfl

/-- `ω⁴ = −1` in `ℤ[ω]`. -/
theorem omega_pow_four : ZOmega.ω ^ 4 = -1 := by decide

/-- `dvdSqrt2Pow` is additive at a fixed level. -/
theorem dvdSqrt2Pow_add {A B : ZOmega} {m : ℕ} (hA : ZOmega.dvdSqrt2Pow A m)
    (hB : ZOmega.dvdSqrt2Pow B m) : ZOmega.dvdSqrt2Pow (A + B) m := by
  rw [ZOmega.dvdSqrt2Pow_iff] at hA hB ⊢
  exact dvd_add hA hB

/-- **The cleared-numerator workhorse**: `denExp (mk N L) ≤ 3` once the numerator factors as
`N = √2^(L−6) · M` with `√2³ ∣ M` (and `6 ≤ L`). -/
theorem denExp_mk_le_three {N M : ZOmega} {L : ℕ} (hL : 6 ≤ L)
    (hNM : N = ZOmega.sqrt2 ^ (L - 6) * M) (hM : ZOmega.dvdSqrt2Pow M 3) :
    denExp (mk N L) ≤ 3 := by
  rw [denExp_le_iff]
  obtain ⟨w, hw⟩ := (ZOmega.dvdSqrt2Pow_iff M 3).mp hM
  refine ⟨w, ?_⟩
  rw [sqrt2_pow_eq, mk_mul, Nat.zero_add, of_def, mk_eq_mk_iff, hNM, hw]
  conv_rhs => rw [show L = 3 + (L - 6) + 3 from by omega]
  rw [pow_add, pow_add]
  ring

/-- `√2`-divisibility of the partner column norm. -/
theorem dividesSqrt2_normSq_snd {x y : ZOmega}
    (hsum : ZOmega.normSq x + ZOmega.normSq y = ZOmega.sqrt2 ^ 4)
    (hdvd : ZOmega.dividesSqrt2 (ZOmega.normSq x)) :
    ZOmega.dividesSqrt2 (ZOmega.normSq y) := by
  rw [ZOmega.dividesSqrt2_iff_dvd] at hdvd ⊢
  have h4 : ZOmega.sqrt2 ∣ ZOmega.sqrt2 ^ 4 := ⟨ZOmega.sqrt2 ^ 3, by ring⟩
  have hyeq : ZOmega.normSq y = ZOmega.sqrt2 ^ 4 - ZOmega.normSq x := by rw [← hsum]; ring
  rw [hyeq]
  exact dvd_sub h4 hdvd

/-- `dvdSqrt2Pow` transports along negation. -/
theorem dvdSqrt2Pow_neg {z : ZOmega} {m : ℕ} (h : ZOmega.dvdSqrt2Pow z m) :
    ZOmega.dvdSqrt2Pow (-z) m := by
  rw [ZOmega.dvdSqrt2Pow_iff] at h ⊢
  exact h.neg_right

/-- `dvdSqrt2Pow` transports along any left factor. -/
theorem dvdSqrt2Pow_mul_left {z : ZOmega} {m : ℕ} (u : ZOmega) (h : ZOmega.dvdSqrt2Pow z m) :
    ZOmega.dvdSqrt2Pow (u * z) m := by
  rw [ZOmega.dvdSqrt2Pow_iff] at h ⊢
  exact Dvd.dvd.mul_left h u

/-- `√2³ ∣ 2·D` once `√2 ∣ D` (the factor-`2` entries' divisibility shape). -/
theorem dvdSqrt2Pow_two_mul {D : ZOmega} (hD : ZOmega.dividesSqrt2 D) :
    ZOmega.dvdSqrt2Pow (2 * D) 3 := by
  rw [show (2 : ZOmega) * D = ZOmega.sqrt2 * (ZOmega.sqrt2 * D) from by
    rw [show (2 : ZOmega) = ZOmega.sqrt2 * ZOmega.sqrt2 from by decide]
    ring]
  rw [show (3 : ℕ) = 1 + 1 + 1 from rfl, ZOmega.dvdSqrt2Pow_sqrt2_mul,
    ZOmega.dvdSqrt2Pow_sqrt2_mul, show (1 : ℕ) = 0 + 1 from rfl, ZOmega.dvdSqrt2Pow_succ]
  exact ⟨hD, trivial⟩

/-! ### The nine per-entry bounds (one declaration each — invariant #10 budgets) -/

set_option maxRecDepth 4000 in
/-- Bloch `(Z,Z)`: numerator `2(|x|² − |y|²)`. -/
theorem denExp_bloch_zz {x y : ZOmega}
    (hsum : ZOmega.normSq x + ZOmega.normSq y = ZOmega.sqrt2 ^ 4)
    (hdvd : ZOmega.dividesSqrt2 (ZOmega.normSq x)) (k : ℕ) :
    denExp (blochEntry (reconstruct x y k) 2 2) ≤ 3 := by
  have hy := dividesSqrt2_normSq_snd hsum hdvd
  have hM : ZOmega.dvdSqrt2Pow
      (2 * (x * ZOmega.conj x - y * ZOmega.conj y)) 3 := by
    refine dvdSqrt2Pow_two_mul ?_
    rw [ZOmega.dividesSqrt2_iff_dvd] at hdvd hy ⊢
    exact dvd_sub hdvd hy
  rw [blochEntry]
  simp only [reconstruct, pauliMat, gateMatrix, Matrix.trace_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two, adjoint_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
    omegaS_pow_mk, conj_mk, half, zero_mul, one_mul, mul_zero, mul_one,
    neg_mul, mul_neg, neg_one_mul, mul_neg_one, add_zero, zero_add, neg_zero, neg_neg,
    ZOmega.conj_neg, ZOmega.conj_mul, ZOmega.conj_conj, mk_mul, mk_add, mk_neg]
  refine denExp_mk_le_three (by norm_num) ?_ hM
  linear_combination (ZOmega.sqrt2 ^ 12
    * (ZOmega.conj x * x - ZOmega.conj y * y)) * omega_pow_mul_conj k


/-- `√2 ∣ (v − conj v)` always (the level-0 `−`-pair). -/
theorem dividesSqrt2_sub_conj (v : ZOmega) : ZOmega.dividesSqrt2 (v - ZOmega.conj v) := by
  have h := ZOmega.dvdSqrt2Pow_sub_conj (w := v) (m := 0) trivial
  rw [show (0 : ℕ) + 1 = 0 + 1 from rfl, ZOmega.dvdSqrt2Pow_succ] at h
  exact h.1

set_option maxRecDepth 4000 in
/-- Bloch `(X,Z)` — UNCONDITIONAL: the factor-2 conjugate-pair form carries `√2³` for all `x y k`. -/
theorem denExp_bloch_xz {x y : ZOmega} (k : ℕ) :
    denExp (blochEntry (reconstruct x y k) 0 2) ≤ 3 := by
  have hM : ZOmega.dvdSqrt2Pow
      (2 * (ZOmega.conj x * y + x * ZOmega.conj y)) 3 := by
    have h0 := dvdSqrt2Pow_two_mul (ZOmega.dividesSqrt2_add_conj (ZOmega.conj x * y))
    rwa [show ZOmega.conj x * y + ZOmega.conj (ZOmega.conj x * y)
        = ZOmega.conj x * y + x * ZOmega.conj y from by
      rw [ZOmega.conj_mul, ZOmega.conj_conj]] at h0
  rw [blochEntry]
  simp only [reconstruct, pauliMat, gateMatrix, Matrix.trace_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two, adjoint_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
    omegaS_pow_mk, conj_mk, half, zero_mul, one_mul, mul_zero, mul_one,
    neg_mul, mul_neg, mul_neg_one, add_zero, zero_add, neg_neg,
    ZOmega.conj_neg, ZOmega.conj_mul, ZOmega.conj_conj, mk_mul, mk_add, mk_neg]
  refine denExp_mk_le_three (by norm_num) ?_ hM
  linear_combination (ZOmega.sqrt2 ^ 12
    * (ZOmega.conj x * y + x * ZOmega.conj y)) * omega_pow_mul_conj k

set_option maxRecDepth 4000 in
/-- Bloch `(Z,X)` — UNCONDITIONAL: the factor-2 conjugate-pair form carries `√2³` for all `x y k`. -/
theorem denExp_bloch_zx {x y : ZOmega} (k : ℕ) :
    denExp (blochEntry (reconstruct x y k) 2 0) ≤ 3 := by
  have hM : ZOmega.dvdSqrt2Pow
      (-(2 * (ZOmega.conj (ZOmega.ω ^ k) * (x * y)
        + ZOmega.ω ^ k * (ZOmega.conj x * ZOmega.conj y)))) 3 := by
    have h0 := dvdSqrt2Pow_neg (dvdSqrt2Pow_two_mul
      (ZOmega.dividesSqrt2_add_conj (ZOmega.conj (ZOmega.ω ^ k) * (x * y))))
    rwa [show ZOmega.conj (ZOmega.ω ^ k) * (x * y)
          + ZOmega.conj (ZOmega.conj (ZOmega.ω ^ k) * (x * y))
        = ZOmega.conj (ZOmega.ω ^ k) * (x * y)
          + ZOmega.ω ^ k * (ZOmega.conj x * ZOmega.conj y) from by
      rw [ZOmega.conj_mul, ZOmega.conj_conj, ZOmega.conj_mul]] at h0
  rw [blochEntry]
  simp only [reconstruct, pauliMat, gateMatrix, Matrix.trace_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two, adjoint_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
    omegaS_pow_mk, conj_mk, half, zero_mul, one_mul, mul_zero, mul_one,
    neg_mul, mul_neg, neg_one_mul, add_zero, zero_add, neg_zero,
    ZOmega.conj_neg, ZOmega.conj_mul, ZOmega.conj_conj, mk_mul, mk_add, mk_neg]
  refine denExp_mk_le_three (by norm_num) ?_ hM
  linear_combination (0 : ZOmega) * omega_pow_mul_conj k

set_option maxRecDepth 4000 in
/-- Bloch `(Y,Z)` — UNCONDITIONAL: the factor-2 conjugate-pair form carries `√2³` for all `x y k`. -/
theorem denExp_bloch_yz {x y : ZOmega} (k : ℕ) :
    denExp (blochEntry (reconstruct x y k) 1 2) ≤ 3 := by
  have hM : ZOmega.dvdSqrt2Pow (2 * (ZOmega.ω ^ 2
      * (x * ZOmega.conj y - ZOmega.conj x * y))) 3 := by
    refine dvdSqrt2Pow_two_mul ?_
    have h0 := dividesSqrt2_sub_conj (x * ZOmega.conj y)
    rw [show x * ZOmega.conj y - ZOmega.conj (x * ZOmega.conj y)
        = x * ZOmega.conj y - ZOmega.conj x * y from by
      rw [ZOmega.conj_mul, ZOmega.conj_conj]] at h0
    rw [ZOmega.dividesSqrt2_iff_dvd] at h0 ⊢
    exact Dvd.dvd.mul_left h0 _
  rw [blochEntry]
  simp only [reconstruct, pauliMat, gateMatrix, Matrix.trace_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two, adjoint_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
    omegaS_pow_mk, conj_mk, half, iS_mk, zero_mul, one_mul, mul_zero, mul_one,
    neg_mul, mul_neg, mul_neg_one, add_zero, zero_add, neg_neg,
    ZOmega.conj_neg, ZOmega.conj_mul, ZOmega.conj_conj, mk_mul, mk_add, mk_neg]
  refine denExp_mk_le_three (by norm_num) ?_ hM
  linear_combination (ZOmega.sqrt2 ^ 12 * ZOmega.ω ^ 2
    * (x * ZOmega.conj y - ZOmega.conj x * y)) * omega_pow_mul_conj k

set_option maxRecDepth 4000 in
/-- Bloch `(Z,Y)` — UNCONDITIONAL: the factor-2 conjugate-pair form carries `√2³` for all `x y k`. -/
theorem denExp_bloch_zy {x y : ZOmega} (k : ℕ) :
    denExp (blochEntry (reconstruct x y k) 2 1) ≤ 3 := by
  have hM : ZOmega.dvdSqrt2Pow (2 * (ZOmega.ω ^ 2
      * (ZOmega.conj (ZOmega.ω ^ k) * (x * y)
        - ZOmega.ω ^ k * (ZOmega.conj x * ZOmega.conj y)))) 3 := by
    refine dvdSqrt2Pow_two_mul ?_
    have h0 := dividesSqrt2_sub_conj (ZOmega.conj (ZOmega.ω ^ k) * (x * y))
    rw [show ZOmega.conj (ZOmega.ω ^ k) * (x * y)
          - ZOmega.conj (ZOmega.conj (ZOmega.ω ^ k) * (x * y))
        = ZOmega.conj (ZOmega.ω ^ k) * (x * y)
          - ZOmega.ω ^ k * (ZOmega.conj x * ZOmega.conj y) from by
      rw [ZOmega.conj_mul, ZOmega.conj_conj, ZOmega.conj_mul]] at h0
    rw [ZOmega.dividesSqrt2_iff_dvd] at h0 ⊢
    exact Dvd.dvd.mul_left h0 _
  rw [blochEntry]
  simp only [reconstruct, pauliMat, gateMatrix, Matrix.trace_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two, adjoint_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
    omegaS_pow_mk, conj_mk, half, iS_mk, zero_mul, one_mul, mul_zero,
    neg_mul, mul_neg, neg_one_mul, add_zero, zero_add, neg_zero, neg_neg,
    ZOmega.conj_neg, ZOmega.conj_mul, ZOmega.conj_conj, mk_mul, mk_add, mk_neg]
  refine denExp_mk_le_three (by norm_num) ?_ hM
  linear_combination (0 : ZOmega) * omega_pow_mul_conj k

/-- `conj` distributes over `x·x ∓ y·y` (atom-basis form). -/
theorem conj_sq_sub (x y : ZOmega) : ZOmega.conj (x * x - y * y)
    = ZOmega.conj x * ZOmega.conj x - ZOmega.conj y * ZOmega.conj y := by
  rw [show x * x - y * y = x * x + -(y * y) from by ring, ZOmega.conj_add, ZOmega.conj_neg,
    ZOmega.conj_mul, ZOmega.conj_mul]
  ring

theorem conj_sq_add (x y : ZOmega) : ZOmega.conj (x * x + y * y)
    = ZOmega.conj x * ZOmega.conj x + ZOmega.conj y * ZOmega.conj y := by
  rw [ZOmega.conj_add, ZOmega.conj_mul, ZOmega.conj_mul]

set_option maxRecDepth 4000 in
/-- Bloch `(X,X)`. -/
theorem denExp_bloch_xx {x y : ZOmega}
    (hsum : ZOmega.normSq x + ZOmega.normSq y = ZOmega.sqrt2 ^ 4)
    (hdvd : ZOmega.dividesSqrt2 (ZOmega.normSq x)) (k : ℕ) :
    denExp (blochEntry (reconstruct x y k) 0 0) ≤ 3 := by
  obtain ⟨hsub2, -⟩ := ZOmega.sqrt2_sq_dvd_sq_add_sub hsum hdvd
  have hM : ZOmega.dvdSqrt2Pow
      (ZOmega.conj (ZOmega.ω ^ k) * (x * x - y * y)
        + ZOmega.ω ^ k * (ZOmega.conj x * ZOmega.conj x
          - ZOmega.conj y * ZOmega.conj y)) 3 := by
    have h0 := ZOmega.dvdSqrt2Pow_add_conj
      (dvdSqrt2Pow_mul_left (ZOmega.conj (ZOmega.ω ^ k)) hsub2)
    rwa [show ZOmega.conj (ZOmega.conj (ZOmega.ω ^ k) * (x * x - y * y))
        = ZOmega.ω ^ k * (ZOmega.conj x * ZOmega.conj x
          - ZOmega.conj y * ZOmega.conj y) from by
      rw [ZOmega.conj_mul, ZOmega.conj_conj, conj_sq_sub]] at h0
  rw [blochEntry]
  simp only [reconstruct, pauliMat, gateMatrix, Matrix.trace_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two, adjoint_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
    omegaS_pow_mk, conj_mk, half, zero_mul, one_mul, mul_zero, mul_one,
    neg_mul, mul_neg, add_zero, zero_add,
    ZOmega.conj_neg, ZOmega.conj_mul, ZOmega.conj_conj, mk_mul, mk_add, mk_neg]
  refine denExp_mk_le_three (by norm_num) ?_ hM
  linear_combination (0 : ZOmega) * omega_pow_mul_conj k

set_option maxRecDepth 4000 in
/-- Bloch `(Y,Y)`. -/
theorem denExp_bloch_yy {x y : ZOmega}
    (hsum : ZOmega.normSq x + ZOmega.normSq y = ZOmega.sqrt2 ^ 4)
    (hdvd : ZOmega.dividesSqrt2 (ZOmega.normSq x)) (k : ℕ) :
    denExp (blochEntry (reconstruct x y k) 1 1) ≤ 3 := by
  obtain ⟨-, hadd2⟩ := ZOmega.sqrt2_sq_dvd_sq_add_sub hsum hdvd
  have hM : ZOmega.dvdSqrt2Pow
      (ZOmega.conj (ZOmega.ω ^ k) * (x * x + y * y)
        + ZOmega.ω ^ k * (ZOmega.conj x * ZOmega.conj x
          + ZOmega.conj y * ZOmega.conj y)) 3 := by
    have h0 := ZOmega.dvdSqrt2Pow_add_conj
      (dvdSqrt2Pow_mul_left (ZOmega.conj (ZOmega.ω ^ k)) hadd2)
    rwa [show ZOmega.conj (ZOmega.conj (ZOmega.ω ^ k) * (x * x + y * y))
        = ZOmega.ω ^ k * (ZOmega.conj x * ZOmega.conj x
          + ZOmega.conj y * ZOmega.conj y) from by
      rw [ZOmega.conj_mul, ZOmega.conj_conj, conj_sq_add]] at h0
  rw [blochEntry]
  simp only [reconstruct, pauliMat, gateMatrix, Matrix.trace_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two, adjoint_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
    omegaS_pow_mk, conj_mk, half, iS_mk, zero_mul, one_mul, mul_zero,
    neg_mul, mul_neg, add_zero, zero_add, neg_neg,
    ZOmega.conj_neg, ZOmega.conj_mul, ZOmega.conj_conj, mk_mul, mk_add, mk_neg]
  refine denExp_mk_le_three (by norm_num) ?_ hM
  linear_combination (-(ZOmega.sqrt2 ^ 12)
    * (ZOmega.ω ^ k * (ZOmega.conj x * ZOmega.conj x + ZOmega.conj y * ZOmega.conj y)
      + ZOmega.conj (ZOmega.ω ^ k) * (x * x + y * y))) * omega_pow_four

set_option maxRecDepth 4000 in
/-- Bloch `(X,Y)`. -/
theorem denExp_bloch_xy {x y : ZOmega}
    (hsum : ZOmega.normSq x + ZOmega.normSq y = ZOmega.sqrt2 ^ 4)
    (hdvd : ZOmega.dividesSqrt2 (ZOmega.normSq x)) (k : ℕ) :
    denExp (blochEntry (reconstruct x y k) 0 1) ≤ 3 := by
  obtain ⟨hsub2, -⟩ := ZOmega.sqrt2_sq_dvd_sq_add_sub hsum hdvd
  have hM : ZOmega.dvdSqrt2Pow (ZOmega.ω ^ 2
      * (ZOmega.conj (ZOmega.ω ^ k) * (x * x - y * y)
        - ZOmega.ω ^ k * (ZOmega.conj x * ZOmega.conj x
          - ZOmega.conj y * ZOmega.conj y))
      + 2 * (ZOmega.ω ^ 2 * (ZOmega.ω ^ k * (ZOmega.conj x * ZOmega.conj x
          - ZOmega.conj y * ZOmega.conj y)
        - ZOmega.conj (ZOmega.ω ^ k) * (x * x - y * y)))) 3 := by
    have h0 := dvdSqrt2Pow_mul_left (ZOmega.ω ^ 2) (ZOmega.dvdSqrt2Pow_sub_conj
      (dvdSqrt2Pow_mul_left (ZOmega.conj (ZOmega.ω ^ k)) hsub2))
    rw [show ZOmega.conj (ZOmega.conj (ZOmega.ω ^ k) * (x * x - y * y))
        = ZOmega.ω ^ k * (ZOmega.conj x * ZOmega.conj x
          - ZOmega.conj y * ZOmega.conj y) from by
      rw [ZOmega.conj_mul, ZOmega.conj_conj, conj_sq_sub]] at h0
    refine dvdSqrt2Pow_add h0 ?_
    have h1 : ZOmega.dividesSqrt2 (ZOmega.ω ^ 2
        * (ZOmega.ω ^ k * (ZOmega.conj x * ZOmega.conj x - ZOmega.conj y * ZOmega.conj y)
          - ZOmega.conj (ZOmega.ω ^ k) * (x * x - y * y))) := by
      have h2 := dividesSqrt2_sub_conj
        (ZOmega.ω ^ k * (ZOmega.conj x * ZOmega.conj x - ZOmega.conj y * ZOmega.conj y))
      rw [show ZOmega.conj (ZOmega.ω ^ k
            * (ZOmega.conj x * ZOmega.conj x - ZOmega.conj y * ZOmega.conj y))
          = ZOmega.conj (ZOmega.ω ^ k) * (x * x - y * y) from by
        rw [ZOmega.conj_mul, conj_sq_sub, ZOmega.conj_conj, ZOmega.conj_conj]] at h2
      rw [ZOmega.dividesSqrt2_iff_dvd] at h2 ⊢
      exact Dvd.dvd.mul_left h2 _
    exact dvdSqrt2Pow_two_mul h1
  rw [blochEntry]
  simp only [reconstruct, pauliMat, gateMatrix, Matrix.trace_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two, adjoint_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
    omegaS_pow_mk, conj_mk, half, iS_mk, zero_mul, one_mul, mul_zero,
    neg_mul, mul_neg, add_zero, zero_add, neg_neg,
    ZOmega.conj_neg, ZOmega.conj_mul, ZOmega.conj_conj, mk_mul, mk_add, mk_neg]
  refine denExp_mk_le_three (by norm_num) ?_ hM
  linear_combination (0 : ZOmega) * omega_pow_mul_conj k

set_option maxRecDepth 4000 in
/-- Bloch `(Y,X)`. -/
theorem denExp_bloch_yx {x y : ZOmega}
    (hsum : ZOmega.normSq x + ZOmega.normSq y = ZOmega.sqrt2 ^ 4)
    (hdvd : ZOmega.dividesSqrt2 (ZOmega.normSq x)) (k : ℕ) :
    denExp (blochEntry (reconstruct x y k) 1 0) ≤ 3 := by
  obtain ⟨-, hadd2⟩ := ZOmega.sqrt2_sq_dvd_sq_add_sub hsum hdvd
  have hM : ZOmega.dvdSqrt2Pow (ZOmega.ω ^ 2
      * (ZOmega.conj (ZOmega.ω ^ k) * (x * x + y * y)
        - ZOmega.ω ^ k * (ZOmega.conj x * ZOmega.conj x
          + ZOmega.conj y * ZOmega.conj y))) 3 := by
    have h0 := dvdSqrt2Pow_mul_left (ZOmega.ω ^ 2) (ZOmega.dvdSqrt2Pow_sub_conj
      (dvdSqrt2Pow_mul_left (ZOmega.conj (ZOmega.ω ^ k)) hadd2))
    rwa [show ZOmega.conj (ZOmega.conj (ZOmega.ω ^ k) * (x * x + y * y))
        = ZOmega.ω ^ k * (ZOmega.conj x * ZOmega.conj x
          + ZOmega.conj y * ZOmega.conj y) from by
      rw [ZOmega.conj_mul, ZOmega.conj_conj, conj_sq_add]] at h0
  rw [blochEntry]
  simp only [reconstruct, pauliMat, gateMatrix, Matrix.trace_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two, adjoint_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
    omegaS_pow_mk, conj_mk, half, iS_mk, zero_mul, one_mul, mul_zero, mul_one,
    neg_mul, mul_neg, add_zero, zero_add, neg_neg,
    ZOmega.conj_neg, ZOmega.conj_mul, ZOmega.conj_conj, mk_mul, mk_add, mk_neg]
  refine denExp_mk_le_three (by norm_num) ?_ hM
  linear_combination (0 : ZOmega) * omega_pow_mul_conj k

/-! ### The assembled structural bridge -/

/-- **The structural `kSO3`-bound**: every reconstruction from a unit column (`|x|²+|y|² = √2⁴`)
with `√2 ∣ |x|²` (the `μ ≤ 3` condition) has `kSO3 ≤ 3` — for EVERY `x, y, k`, with no finite
check. This replaces the former `bridge_box_core` `native_decide`. -/
theorem kSO3_reconstruct_le_three {x y : ZOmega}
    (hsum : ZOmega.normSq x + ZOmega.normSq y = ZOmega.sqrt2 ^ 4)
    (hdvd : ZOmega.dividesSqrt2 (ZOmega.normSq x)) (k : ℕ) :
    kSO3 (reconstruct x y k) ≤ 3 := by
  rw [kSO3]
  refine Finset.sup_le ?_
  rintro ⟨i, j⟩ -
  fin_cases i <;> fin_cases j
  · exact denExp_bloch_xx hsum hdvd k
  · exact denExp_bloch_xy hsum hdvd k
  · exact denExp_bloch_xz k
  · exact denExp_bloch_yx hsum hdvd k
  · exact denExp_bloch_yy hsum hdvd k
  · exact denExp_bloch_yz k
  · exact denExp_bloch_zx k
  · exact denExp_bloch_zy k
  · exact denExp_bloch_zz hsum hdvd k

/-- The literal-form variant (`⟨0,0,0,4⟩ = √2⁴`), matching the clearing lemmas' output. -/
theorem kSO3_reconstruct_le_three' {x y : ZOmega}
    (hsum : ZOmega.normSq x + ZOmega.normSq y = (⟨0, 0, 0, 4⟩ : ZOmega))
    (hdvd : ZOmega.dividesSqrt2 (ZOmega.normSq x)) (k : ℕ) :
    kSO3 (reconstruct x y k) ≤ 3 :=
  kSO3_reconstruct_le_three
    (by rw [hsum]; decide) hdvd k

/-- **The `μ ≤ 3 ⟹ kSO3 ≤ 3` bridge** (Giles–Selinger Cor 7.11), now fully STRUCTURAL: every
realizable matrix with squared-modulus sde `μ(M) ≤ 3` has SO(3) Bloch least-denominator exponent
(= Matsumoto–Amano T-count) `kSO3 M ≤ 3`. The proof rewrites `M` as `reconstruct x y k` (column 0
cleared at exponent 2; column 1 `realizable_col1`-determined) and applies the structural
`kSO3_reconstruct_le_three` — no finite check, no `native_decide`. -/
theorem bridge (M : Mat2) (hM : IsCliffordTRealizable M) (hμ : muMeasure M ≤ 3) :
    kSO3 M ≤ 3 := by
  have hu : IsUnitaryT M := by obtain ⟨gs, rfl⟩ := hM; exact interp_isUnitaryT gs
  obtain ⟨x, y, hx, hy, hxd, hyd⟩ := column0_cleared_bounded hu hμ
  obtain ⟨k, hcol01, hcol11⟩ := realizable_col1 hM
  have h00 : M 0 0 = mk x 2 := eq_mk_of_sqrt2_pow_mul hx
  have h10 : M 1 0 = mk y 2 := eq_mk_of_sqrt2_pow_mul hy
  have hMrec : M = reconstruct x y k := by
    rw [Matrix.eta_fin_two M, hcol01, hcol11, h00, h10]; rfl
  have hsum : ZOmega.normSq x + ZOmega.normSq y = (⟨0, 0, 0, 4⟩ : ZOmega) := by
    have h := clearedCol_normSq_sum hx hy (unitary_col0_normSq hu)
    rwa [show ZOmega.sqrt2 ^ (2 * 2) = (⟨0, 0, 0, 4⟩ : ZOmega) from by decide] at h
  have hdvd : ZOmega.dividesSqrt2 (ZOmega.normSq x) := by
    obtain ⟨w, hw⟩ := denExp_le_iff.mp (show denExp (normSq (M 0 0)) ≤ 3 from hμ)
    have hns : ZOmega.normSq x = ZOmega.sqrt2 * w := by
      apply of_inj
      rw [of_mul, ← (sqrt2_pow_normSq_clearing hx), show 2 * 2 = 1 + 3 from rfl,
        pow_add, mul_assoc, hw, pow_one]
      simp only [sqrt2_def, of_def]
    exact (ZOmega.dividesSqrt2_iff_dvd _).mpr ⟨w, hns⟩
  rw [hMrec]
  exact kSO3_reconstruct_le_three' hsum hdvd k

end KMM
end SKEFTHawking.RossSelinger
