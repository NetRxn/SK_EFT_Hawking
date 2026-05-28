/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — Concrete-radius regime substrate (re-point R0/R1, θ-bound)

The super-quad regime hypothesis `h_regime` (carried by S102's (B) discharge + the
cascade) is stated with the **IFT** `matrixLog d` and the IFT `target` — both
irreducibly existential (`HasStrictFDerivAt.toOpenPartialHomeomorph`, no quantitative
IFT in Mathlib). The concrete-radius Mercator logarithm
(`GenericSUdMatrixMercatorLog.lean`, with the round-trip `exp_matrixMercatorLog` on
the named ball `‖X‖<1`) cannot bridge to the IFT log on a *concrete* ball (the
agreement requires `matrixMercatorLog(Δ−1) ∈ source`, existential — see the Phase 6y
roadmap §"BRICK-3 ARCHITECTURAL FINDING"). The route to an UNCONDITIONAL regime is to
**re-point** `dnStepFG_sud` + the (B) discharge + `h_regime` to
`matrixLogConcrete d Δ := matrixMercatorLog (Δ − 1)`, whose regime conjuncts hold on a
*named* ball. This file ships the concrete regime substrate brick by brick (R0–R4).

## Substantive content shipped (this wave)

  * `regime_thetabound_concrete` — the **θ-bound conjunct, concrete-radius**:
    `‖(-i)·matrixMercatorLog((V⁻¹U).val − 1)‖ ≤ 2·d·‖V − U‖` whenever
    `d·‖V − U‖ ≤ 1/2`. Composes the K=2 Mercator bound
    (`norm_matrixMercatorLog_le_two_mul`, S109) with the SU(d) residual bound
    (`residual_norm_le_d_mul`, S60). This is the concrete-radius analog of the
    existential `regime_thetabound_herm_traceless_on_residual_nhd` (S106).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Re-point sub-brick breakdown (R0–R4)" — R0/R1 θ-bound for the
concrete-radius regime.

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdMatrixMercatorLog
import SKEFTHawking.FKLW.GenericSUdSuperQuadSubstrate
import SKEFTHawking.FKLW.GenericSUdMatrixLogTraceless

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- **Concrete-radius regime θ-bound**: for `V, U ∈ SU(d)` with
`d·‖V − U‖ ≤ 1/2`, the concrete Mercator log of the residual satisfies the regime's
θ-bound

  `‖(-i)·matrixMercatorLog((V⁻¹U).val − 1)‖ ≤ 2·d·‖V − U‖`.

Composes the concrete-radius K=2 Lipschitz bound `norm_matrixMercatorLog_le_two_mul`
(S109; the `(-i)` scalar has norm 1) with the SU(d) residual bound
`residual_norm_le_d_mul` (S60; `‖(V⁻¹U).val − 1‖ ≤ d·‖V − U‖`). The hypothesis
`d·‖V − U‖ ≤ 1/2` keeps the residual inside the named ball `‖·‖ ≤ 1/2` where the K=2
bound holds; on the calibration ball `‖V − U‖ ≤ 2·ε₀_sud` (with `ε₀_sud` tiny) this is
automatic. This is the concrete-radius analog of the existential S106 θ-bound — the
first conjunct of the re-pointed (concrete) regime. -/
theorem regime_thetabound_concrete {d : ℕ} [Nonempty (Fin d)]
    (V U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))
    (hVU : (d : ℝ) * ‖(V : Matrix (Fin d) (Fin d) ℂ) - (U : Matrix (Fin d) (Fin d) ℂ)‖ ≤ 1 / 2) :
    ‖((-Complex.I) • matrixMercatorLog
        ((V⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val - 1) :
        Matrix (Fin d) (Fin d) ℂ)‖
      ≤ 2 * (d : ℝ) * ‖(V : Matrix (Fin d) (Fin d) ℂ) - (U : Matrix (Fin d) (Fin d) ℂ)‖ := by
  have hres := residual_norm_le_d_mul V U
  have hΔm_half : ‖((V⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val - 1)‖ ≤ 1 / 2 :=
    le_trans hres hVU
  have hmlog := norm_matrixMercatorLog_le_two_mul
    ((V⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val - 1) hΔm_half
  rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
  calc ‖matrixMercatorLog ((V⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val - 1)‖
      ≤ 2 * ‖((V⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val - 1)‖ := hmlog
    _ ≤ 2 * ((d : ℝ) * ‖(V : Matrix (Fin d) (Fin d) ℂ) - (U : Matrix (Fin d) (Fin d) ℂ)‖) := by
        linarith [hres]
    _ = 2 * (d : ℝ) * ‖(V : Matrix (Fin d) (Fin d) ℂ) - (U : Matrix (Fin d) (Fin d) ℂ)‖ := by ring

/-- **Conjugate-transpose commutes with the Mercator log** (re-point R2 part a):
`(matrixMercatorLog Y)ᴴ = matrixMercatorLog Yᴴ`, unconditionally. Conjugate-transpose
is a continuous additive map (so it commutes with the tsum, `conjTranspose_tsum`), is
multiplicative on powers of a single element (`conjTranspose_pow`), and fixes the real
coefficients `c_n = (-1)^n/(n+1)` (`star` on ℝ-valued `ℂ`). Holds for all `Y` (when the
series diverges both sides are the junk `0`, since `conjTranspose` is a homeomorphism).

Toward the re-pointed regime's **Hermitian** conjunct: for unitary `Δ` (so `Δᴴ = Δ⁻¹`),
this gives `(matrixMercatorLog (Δ−1))ᴴ = matrixMercatorLog (Δᴴ − 1) = matrixMercatorLog
(Δ⁻¹ − 1)`; combined with `matrixMercatorLog (Δ⁻¹−1) = −matrixMercatorLog (Δ−1)` (R2 part b,
`log(Δ⁻¹)=−log(Δ)`, pending R3 concrete exp-injectivity) this yields skew-Hermiticity of
`matrixMercatorLog (Δ−1)`, hence Hermiticity of `(-i)·matrixMercatorLog (Δ−1)`. -/
theorem matrixMercatorLog_conjTranspose {d : ℕ} (Y : Matrix (Fin d) (Fin d) ℂ) :
    (matrixMercatorLog Y)ᴴ = matrixMercatorLog Yᴴ := by
  unfold matrixMercatorLog
  rw [conjTranspose_tsum]
  refine tsum_congr (fun n => ?_)
  rw [conjTranspose_smul, conjTranspose_pow]
  congr 1
  simp [star_div₀, star_pow]

/-- **Concrete-radius regime `‖H‖ ≤ 1` conjunct**: for `V, U ∈ SU(d)` with
`d·‖V − U‖ ≤ 1/2`, the concrete log-derived `H = (-i)·matrixMercatorLog((V⁻¹U).val − 1)`
satisfies `‖H‖ ≤ 1`. Immediate from the θ-bound `regime_thetabound_concrete`
(`‖H‖ ≤ 2·d·‖V − U‖`) since `2·d·‖V − U‖ ≤ 1`. The second concrete regime conjunct
(after the θ-bound), holding on the named ball — automatic on the calibration ball
`‖V − U‖ ≤ 2·ε₀_sud`. -/
theorem regime_normH_le_one_concrete {d : ℕ} [Nonempty (Fin d)]
    (V U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))
    (hVU : (d : ℝ) * ‖(V : Matrix (Fin d) (Fin d) ℂ) - (U : Matrix (Fin d) (Fin d) ℂ)‖ ≤ 1 / 2) :
    ‖((-Complex.I) • matrixMercatorLog
        ((V⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val - 1) :
        Matrix (Fin d) (Fin d) ℂ)‖ ≤ 1 := by
  calc ‖((-Complex.I) • matrixMercatorLog
          ((V⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val - 1) :
          Matrix (Fin d) (Fin d) ℂ)‖
      ≤ 2 * (d : ℝ) * ‖(V : Matrix (Fin d) (Fin d) ℂ) - (U : Matrix (Fin d) (Fin d) ℂ)‖ :=
        regime_thetabound_concrete V U hVU
    _ ≤ 1 := by nlinarith [hVU]

/-- **Banach exp remainder bound** (re-point R3 foundation): for any
`A : Matrix (Fin d) (Fin d) ℂ`,

  `‖NormedSpace.exp A − 1 − A‖ ≤ ‖A‖² · Real.exp ‖A‖`.

Mathlib has this only for scalar `ℝ`/`ℂ` (`Real.norm_exp_sub_one_sub_id_le`,
`Complex.exp_bound_sq`), not for a general Banach algebra. **Proof**: split the exp
series off its first two terms (`exp A = 1 + A + ∑' i, ((i+2)!)⁻¹ • A^(i+2)` via
`Summable.sum_add_tsum_nat_add 2`), bound the tail termwise (`((i+2)!)⁻¹ ≤ (i!)⁻¹`,
`‖A^(i+2)‖ ≤ ‖A‖^(i+2)`), factor out `‖A‖²`, and match the real exp series
(`Real.exp_eq_exp_ℝ` + `NormedSpace.exp_eq_tsum_div`).

This is the key brick for R3/R2b: combined with `exp S = 1` (which makes
`exp S − 1 − S = −S`), it gives `‖S‖ ≤ ‖S‖²·exp‖S‖`, forcing `S = 0` for `‖S‖`
small (since `‖S‖·exp‖S‖ < 1` for `‖S‖ ≤ 1/2`) — the concrete exp-injectivity-at-0
that discharges `matrixMercatorLog(Δ⁻¹−1) = −matrixMercatorLog(Δ−1)` (regime's
skew-Hermitian conjunct, R2b). -/
theorem norm_exp_sub_one_sub_self_le {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    ‖NormedSpace.exp A - 1 - A‖ ≤ ‖A‖ ^ 2 * Real.exp ‖A‖ := by
  have hHasSum := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A
  have hsumm := hHasSum.summable
  have hsplit := Summable.sum_add_tsum_nat_add 2 hsumm
  have hrange : (∑ i ∈ Finset.range 2, ((i.factorial : ℂ)⁻¹ • A ^ i)) = 1 + A := by
    simp [Finset.sum_range_succ]
  rw [hrange, hHasSum.tsum_eq] at hsplit
  have htail : NormedSpace.exp A - 1 - A
      = ∑' i : ℕ, ((i + 2).factorial : ℂ)⁻¹ • A ^ (i + 2) := by
    rw [← hsplit]; abel
  rw [htail]
  have hsumm_tail : Summable (fun i : ℕ => ((i + 2).factorial : ℂ)⁻¹ • A ^ (i + 2)) :=
    (summable_nat_add_iff 2).mpr hsumm
  have hbound : ∀ i : ℕ, ‖((i + 2).factorial : ℂ)⁻¹ • A ^ (i + 2)‖
      ≤ ((i.factorial : ℝ))⁻¹ * ‖A‖ ^ (i + 2) := by
    intro i
    rw [norm_smul]
    have h1 : ‖((i + 2).factorial : ℂ)⁻¹‖ = ((i + 2).factorial : ℝ)⁻¹ := by
      rw [norm_inv]; congr 1; rw [Complex.norm_natCast]
    have h2 : ‖A ^ (i + 2)‖ ≤ ‖A‖ ^ (i + 2) := norm_pow_le' A (by omega)
    have h3 : ((i + 2).factorial : ℝ)⁻¹ ≤ ((i.factorial : ℝ))⁻¹ :=
      inv_anti₀ (by positivity) (by exact_mod_cast Nat.factorial_le (by omega))
    rw [h1]
    calc ((i + 2).factorial : ℝ)⁻¹ * ‖A ^ (i + 2)‖
        ≤ ((i + 2).factorial : ℝ)⁻¹ * ‖A‖ ^ (i + 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ ((i.factorial : ℝ))⁻¹ * ‖A‖ ^ (i + 2) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
  have hsumm_rhs : Summable (fun i : ℕ => ((i.factorial : ℝ))⁻¹ * ‖A‖ ^ (i + 2)) := by
    have hb : Summable (fun i : ℕ => ‖A‖ ^ i / (i.factorial : ℝ)) :=
      Real.summable_pow_div_factorial ‖A‖
    have heq : (fun i : ℕ => ((i.factorial : ℝ))⁻¹ * ‖A‖ ^ (i + 2))
        = fun i => ‖A‖ ^ 2 * (‖A‖ ^ i / (i.factorial : ℝ)) := by
      funext i; rw [pow_add]; ring
    rw [heq]; exact hb.mul_left _
  calc ‖∑' i : ℕ, ((i + 2).factorial : ℂ)⁻¹ • A ^ (i + 2)‖
      ≤ ∑' i : ℕ, ‖((i + 2).factorial : ℂ)⁻¹ • A ^ (i + 2)‖ :=
        norm_tsum_le_tsum_norm hsumm_tail.norm
    _ ≤ ∑' i : ℕ, ((i.factorial : ℝ))⁻¹ * ‖A‖ ^ (i + 2) :=
        Summable.tsum_le_tsum hbound hsumm_tail.norm hsumm_rhs
    _ = ‖A‖ ^ 2 * Real.exp ‖A‖ := by
        rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div, ← tsum_mul_left]
        refine tsum_congr (fun i => ?_)
        rw [pow_add]; ring

/-- **Concrete exp-injectivity at 0** (re-point R3): if `NormedSpace.exp S = 1` and
`‖S‖ ≤ 1/2`, then `S = 0`. From `exp S = 1` we get `exp S − 1 − S = −S`, so the Banach
exp-remainder bound (`norm_exp_sub_one_sub_self_le`) gives `‖S‖ ≤ ‖S‖²·exp‖S‖`, i.e.
`1 ≤ ‖S‖·exp‖S‖`; but `‖S‖·exp‖S‖ ≤ (1/2)·exp(1/2) < (1/2)·2 = 1` (using `exp(1/2)² = exp 1
< 2.72 < 4`), a contradiction unless `‖S‖ = 0`. This is the concrete-radius substitute for
the existential IFT local injectivity — the key to R2b. -/
theorem eq_zero_of_exp_eq_one_of_norm_le {d : ℕ} (S : Matrix (Fin d) (Fin d) ℂ)
    (hexp : NormedSpace.exp S = 1) (hS : ‖S‖ ≤ 1 / 2) : S = 0 := by
  have hrem := norm_exp_sub_one_sub_self_le S
  have hes : NormedSpace.exp S - 1 - S = -S := by rw [hexp]; abel
  rw [hes, norm_neg] at hrem
  rw [← norm_eq_zero]
  by_contra hne
  have hpos : 0 < ‖S‖ := lt_of_le_of_ne (norm_nonneg S) (Ne.symm hne)
  have hexpS_pos := Real.exp_pos ‖S‖
  have hexp_half : Real.exp (1 / 2 : ℝ) < 2 := by
    have hsq : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
      rw [sq, ← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1 / 2 : ℝ), hsq]
  have heS : Real.exp ‖S‖ ≤ Real.exp (1 / 2 : ℝ) := Real.exp_le_exp.mpr hS
  have h_ge1 : 1 ≤ ‖S‖ * Real.exp ‖S‖ := by
    have hh : ‖S‖ * 1 ≤ ‖S‖ * (‖S‖ * Real.exp ‖S‖) := by
      calc ‖S‖ * 1 = ‖S‖ := mul_one _
        _ ≤ ‖S‖ ^ 2 * Real.exp ‖S‖ := hrem
        _ = ‖S‖ * (‖S‖ * Real.exp ‖S‖) := by ring
    exact le_of_mul_le_mul_left hh hpos
  have h_lt1 : ‖S‖ * Real.exp ‖S‖ < 1 := by
    calc ‖S‖ * Real.exp ‖S‖
        ≤ (1 / 2) * Real.exp (1 / 2 : ℝ) :=
          mul_le_mul hS heS (le_of_lt hexpS_pos) (by norm_num)
      _ < (1 / 2) * 2 := mul_lt_mul_of_pos_left hexp_half (by norm_num)
      _ = 1 := by norm_num
  linarith

/-- **Mercator log of the inverse is the negative** (re-point R2b): for commuting
`A, B` with `(1 + A)·(1 + B) = 1` (i.e. `1 + B = (1 + A)⁻¹`) and both `‖A‖, ‖B‖ ≤ 1/8`,

  `matrixMercatorLog B = -matrixMercatorLog A`.

This is the matrix analog of `log(Δ⁻¹) = -log(Δ)` on the concrete calibration ball.
**Proof**: the two logs commute (`matrixMercatorLog_commute_mercatorLog`, both power
series in their commuting arguments), so by `exp_add_of_commute` and the two round-trips
(`exp_matrixMercatorLog`),

  `exp (matrixMercatorLog A + matrixMercatorLog B) = (1 + A)·(1 + B) = 1`;

the K=2 Lipschitz bound (`norm_matrixMercatorLog_le_two_mul`) gives
`‖matrixMercatorLog A + matrixMercatorLog B‖ ≤ 2‖A‖ + 2‖B‖ ≤ 1/2`, so the concrete
exp-injectivity-at-0 (`eq_zero_of_exp_eq_one_of_norm_le`, R3) forces the sum to vanish.

For unitary `Δ` (`Δᴴ = Δ⁻¹`) take `A = Δ−1`, `B = Δ⁻¹−1 = (Δ−1)ᴴ`: combined with
`matrixMercatorLog_conjTranspose` (R2a) this yields skew-Hermiticity of
`matrixMercatorLog (Δ−1)`, hence Hermiticity of `(-i)·matrixMercatorLog (Δ−1)` — the
re-pointed regime's **Hermitian** conjunct. -/
theorem matrixMercatorLog_inv_eq_neg {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℂ)
    (hAB : Commute A B)
    (hmul : (1 + A) * (1 + B) = 1)
    (hA : ‖A‖ ≤ 1 / 8) (hB : ‖B‖ ≤ 1 / 8) :
    matrixMercatorLog B = -matrixMercatorLog A := by
  have hA1 : ‖A‖ < 1 := by linarith
  have hB1 : ‖B‖ < 1 := by linarith
  have hexpA := exp_matrixMercatorLog A hA1
  have hexpB := exp_matrixMercatorLog B hB1
  have hcomm : Commute (matrixMercatorLog A) (matrixMercatorLog B) :=
    matrixMercatorLog_commute_mercatorLog A B hA1 hB1 hAB
  have hexpS : NormedSpace.exp (matrixMercatorLog A + matrixMercatorLog B) = 1 := by
    rw [NormedSpace.exp_add_of_commute hcomm, hexpA, hexpB, hmul]
  have hnormA := norm_matrixMercatorLog_le_two_mul A (by linarith : ‖A‖ ≤ 1 / 2)
  have hnormB := norm_matrixMercatorLog_le_two_mul B (by linarith : ‖B‖ ≤ 1 / 2)
  have hnormS : ‖matrixMercatorLog A + matrixMercatorLog B‖ ≤ 1 / 2 := by
    calc ‖matrixMercatorLog A + matrixMercatorLog B‖
        ≤ ‖matrixMercatorLog A‖ + ‖matrixMercatorLog B‖ := norm_add_le _ _
      _ ≤ 2 * ‖A‖ + 2 * ‖B‖ := by linarith
      _ ≤ 1 / 2 := by linarith
  have hS0 := eq_zero_of_exp_eq_one_of_norm_le _ hexpS hnormS
  rw [add_comm] at hS0
  exact eq_neg_of_add_eq_zero_left hS0

/-- **Skew-Hermiticity of the concrete log for a unitary** (re-point R2, skew-Hermitian
conjunct): for a two-sided unitary `Δ` (`Δ·Δᴴ = 1` and `Δᴴ·Δ = 1`) with
`‖Δ − 1‖, ‖Δᴴ − 1‖ ≤ 1/8`, `(matrixMercatorLog (Δ − 1)).IsSkewHermitian`. **Proof**: by
`matrixMercatorLog_conjTranspose` (R2a) the conjugate-transpose is
`matrixMercatorLog ((Δ−1)ᴴ) = matrixMercatorLog (Δᴴ − 1)`, and since `Δᴴ = Δ⁻¹` (unitary)
the R2b identity `matrixMercatorLog_inv_eq_neg` (`A = Δ−1`, `B = Δᴴ−1`,
`(1+A)(1+B) = Δ·Δᴴ = 1`) gives `matrixMercatorLog (Δᴴ − 1) = −matrixMercatorLog (Δ − 1)`. -/
theorem matrixMercatorLog_isSkewHermitian_of_unitary {d : ℕ}
    (Δ : Matrix (Fin d) (Fin d) ℂ)
    (hΔΔH : Δ * Δᴴ = 1) (hΔHΔ : Δᴴ * Δ = 1)
    (hΔ : ‖Δ - 1‖ ≤ 1 / 8) (hΔH : ‖Δᴴ - 1‖ ≤ 1 / 8) :
    (matrixMercatorLog (Δ - 1)).IsSkewHermitian := by
  have hcΔ : Commute Δ Δᴴ := by rw [Commute, SemiconjBy, hΔΔH, hΔHΔ]
  have hcomm : Commute (Δ - 1) (Δᴴ - 1) :=
    (hcΔ.sub_right (Commute.one_right Δ)).sub_left (Commute.one_left (Δᴴ - 1))
  have hmul : (1 + (Δ - 1)) * (1 + (Δᴴ - 1)) = 1 := by
    have e1 : (1 : Matrix (Fin d) (Fin d) ℂ) + (Δ - 1) = Δ := by abel
    have e2 : (1 : Matrix (Fin d) (Fin d) ℂ) + (Δᴴ - 1) = Δᴴ := by abel
    rw [e1, e2]; exact hΔΔH
  have hR2b := matrixMercatorLog_inv_eq_neg (Δ - 1) (Δᴴ - 1) hcomm hmul hΔ hΔH
  show (matrixMercatorLog (Δ - 1))ᴴ = -matrixMercatorLog (Δ - 1)
  rw [matrixMercatorLog_conjTranspose, conjTranspose_sub, conjTranspose_one]
  exact hR2b

/-- **Hermiticity of the concrete log-generator for a unitary** (re-point R2, full
Hermitian conjunct): for a two-sided unitary `Δ` (`Δ·Δᴴ = 1` and `Δᴴ·Δ = 1`) with
`‖Δ − 1‖ ≤ 1/8` and `‖Δᴴ − 1‖ ≤ 1/8`,

  `((-i) • matrixMercatorLog (Δ − 1)).IsHermitian`.

This is the re-pointed regime's **Hermitian** conjunct on the concrete calibration ball
(replacing the existential IFT version). Scaling the skew-Hermitian
`matrixMercatorLog (Δ − 1)` (`matrixMercatorLog_isSkewHermitian_of_unitary`) by `-i`
(with `star(-i) = i`) turns skew-Hermiticity into Hermiticity:
`((-i)•L)ᴴ = i•(−L) = −(i•L) = (-i)•L`. -/
theorem isHermitian_neg_I_smul_matrixMercatorLog_of_unitary {d : ℕ}
    (Δ : Matrix (Fin d) (Fin d) ℂ)
    (hΔΔH : Δ * Δᴴ = 1) (hΔHΔ : Δᴴ * Δ = 1)
    (hΔ : ‖Δ - 1‖ ≤ 1 / 8) (hΔH : ‖Δᴴ - 1‖ ≤ 1 / 8) :
    ((-Complex.I) • matrixMercatorLog (Δ - 1)).IsHermitian := by
  have hskew : (matrixMercatorLog (Δ - 1))ᴴ = -matrixMercatorLog (Δ - 1) :=
    matrixMercatorLog_isSkewHermitian_of_unitary Δ hΔΔH hΔHΔ hΔ hΔH
  show ((-Complex.I) • matrixMercatorLog (Δ - 1))ᴴ = (-Complex.I) • matrixMercatorLog (Δ - 1)
  rw [conjTranspose_smul, hskew, show star (-Complex.I) = Complex.I from by simp,
    smul_neg, neg_smul]

/-- **SU(d) re-pointed regime Hermitian conjunct** (re-point R2 at SU(d)): for
`V, U ∈ SU(d)` with `d²·‖V − U‖ ≤ 1/8`, the concrete log-generator of the residual
`Δ = V⁻¹U` is Hermitian:

  `((-i) • matrixMercatorLog ((V⁻¹U).val − 1)).IsHermitian`.

Instantiates the generic `isHermitian_neg_I_smul_matrixMercatorLog_of_unitary` at the
SU(d) residual `Δ = (V⁻¹U).val`. The unitary relations `Δ·Δᴴ = 1`, `Δᴴ·Δ = 1` come from
`specialUnitaryGroup_le_unitaryGroup`; the residual norm bound `‖Δ − 1‖ ≤ d·‖V − U‖`
from `residual_norm_le_d_mul` (S60), and the inverse-residual bound `‖Δᴴ − 1‖ ≤ d·‖Δ − 1‖`
from `Δᴴ − 1 = −Δᴴ·(Δ − 1)` (`Δᴴ·Δ = 1`) plus `‖Δᴴ‖ ≤ d` (`linftyOpNorm_unitary_le`, `Δᴴ`
also unitary). The `d²` hypothesis (vs. `d` for the θ-bound) absorbs the extra `‖Δᴴ‖ ≤ d`
factor on the inverse residual; on the tiny calibration ball `‖V − U‖ ≤ 2·ε₀_sud` it is
automatic. This is the concrete-radius replacement for the existential IFT Hermitian
guard `regime_thetabound_herm_traceless_on_residual_nhd` (S106). -/
theorem isHermitian_regime_concrete_sud {d : ℕ} [Nonempty (Fin d)]
    (V U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))
    (hVU : (d : ℝ) ^ 2 *
        ‖(V : Matrix (Fin d) (Fin d) ℂ) - (U : Matrix (Fin d) (Fin d) ℂ)‖ ≤ 1 / 8) :
    ((-Complex.I) • matrixMercatorLog
        ((V⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val - 1) :
        Matrix (Fin d) (Fin d) ℂ).IsHermitian := by
  set Δ : Matrix (Fin d) (Fin d) ℂ :=
    (V⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val with hΔ
  have hu : Δ ∈ Matrix.unitaryGroup (Fin d) ℂ :=
    Matrix.specialUnitaryGroup_le_unitaryGroup (V⁻¹ * U).property
  have hΔΔH : Δ * Δᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff).mp hu
  have hΔHΔ : Δᴴ * Δ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff').mp hu
  have hdpos : 0 < d := Fin.pos_iff_nonempty.mpr inferInstance
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdpos
  have hnn : (0 : ℝ) ≤ ‖(V : Matrix (Fin d) (Fin d) ℂ) - (U : Matrix (Fin d) (Fin d) ℂ)‖ :=
    norm_nonneg _
  have hres : ‖Δ - 1‖ ≤ (d : ℝ) *
      ‖(V : Matrix (Fin d) (Fin d) ℂ) - (U : Matrix (Fin d) (Fin d) ℂ)‖ := by
    rw [hΔ]; exact residual_norm_le_d_mul V U
  have hdd : (d : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith [hd1, sq_nonneg ((d : ℝ) - 1)]
  have hΔ_le : ‖Δ - 1‖ ≤ 1 / 8 := by
    calc ‖Δ - 1‖
        ≤ (d : ℝ) * ‖(V : Matrix (Fin d) (Fin d) ℂ) - (U : Matrix (Fin d) (Fin d) ℂ)‖ := hres
      _ ≤ (d : ℝ) ^ 2 * ‖(V : Matrix (Fin d) (Fin d) ℂ) - (U : Matrix (Fin d) (Fin d) ℂ)‖ :=
          mul_le_mul_of_nonneg_right hdd hnn
      _ ≤ 1 / 8 := hVU
  have huH : Δᴴ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose]
    exact hΔHΔ
  have hΔH_norm : ‖Δᴴ‖ ≤ (d : ℝ) := linftyOpNorm_unitary_le ⟨Δᴴ, huH⟩
  have hfactor : Δᴴ - 1 = -(Δᴴ * (Δ - 1)) := by
    rw [Matrix.mul_sub, mul_one, hΔHΔ, neg_sub]
  have hΔH_le : ‖Δᴴ - 1‖ ≤ 1 / 8 := by
    rw [hfactor, norm_neg]
    calc ‖Δᴴ * (Δ - 1)‖
        ≤ ‖Δᴴ‖ * ‖Δ - 1‖ := norm_mul_le _ _
      _ ≤ (d : ℝ) * ((d : ℝ) *
            ‖(V : Matrix (Fin d) (Fin d) ℂ) - (U : Matrix (Fin d) (Fin d) ℂ)‖) :=
          mul_le_mul hΔH_norm hres (norm_nonneg _) (le_trans zero_le_one hd1)
      _ = (d : ℝ) ^ 2 * ‖(V : Matrix (Fin d) (Fin d) ℂ) - (U : Matrix (Fin d) (Fin d) ℂ)‖ := by
          ring
      _ ≤ 1 / 8 := hVU
  exact isHermitian_neg_I_smul_matrixMercatorLog_of_unitary Δ hΔΔH hΔHΔ hΔ_le hΔH_le

/-- **Tracelessness of the concrete log for a special-unitary** (re-point R1): for a
two-sided unitary `Δ` with `det Δ = 1`, `‖Δ − 1‖, ‖Δᴴ − 1‖ ≤ 1/8`, and `d·‖Δ − 1‖ < π`,

  `(matrixMercatorLog (Δ − 1)).trace = 0`.

The concrete-radius analog of the existential `matrixLog_trace_eq_zero_on_nhd_one`, now on
a **named** ball. **Proof**: `Y := matrixMercatorLog (Δ − 1)` is skew-Hermitian
(`matrixMercatorLog_isSkewHermitian_of_unitary`), so the Jacobi formula
`det_exp_skewHermitian` (Track S.2d) gives `det(exp Y) = exp(tr Y)`; the round-trip
`exp_matrixMercatorLog` gives `exp Y = 1 + (Δ − 1) = Δ`, so `exp(tr Y) = det Δ = 1`, hence
`tr Y ∈ 2πi·ℤ` (`Complex.exp_eq_one_iff`). The trace bound `‖tr Y‖ ≤ d·‖Y‖ ≤ d·2‖Δ − 1‖ < 2π`
(`norm_trace_le_dim_mul_norm` + K=2 `norm_matrixMercatorLog_le_two_mul`) forces the integer
multiple to be `0`. -/
theorem matrixMercatorLog_trace_eq_zero_of_unitary {d : ℕ} [Nonempty (Fin d)]
    (Δ : Matrix (Fin d) (Fin d) ℂ)
    (hΔΔH : Δ * Δᴴ = 1) (hΔHΔ : Δᴴ * Δ = 1) (hdet : Δ.det = 1)
    (hΔ : ‖Δ - 1‖ ≤ 1 / 8) (hΔH : ‖Δᴴ - 1‖ ≤ 1 / 8)
    (hsmall : (d : ℝ) * ‖Δ - 1‖ < Real.pi) :
    (matrixMercatorLog (Δ - 1)).trace = 0 := by
  have hskew : (matrixMercatorLog (Δ - 1)).IsSkewHermitian :=
    matrixMercatorLog_isSkewHermitian_of_unitary Δ hΔΔH hΔHΔ hΔ hΔH
  have hΔ1 : ‖Δ - 1‖ < 1 := by linarith
  have hexp : NormedSpace.exp (matrixMercatorLog (Δ - 1)) = Δ := by
    rw [exp_matrixMercatorLog (Δ - 1) hΔ1]; abel
  have hjac := det_exp_skewHermitian (matrixMercatorLog (Δ - 1)) hskew
  rw [hexp, hdet] at hjac
  have hexp1 : Complex.exp (matrixMercatorLog (Δ - 1)).trace = 1 := hjac.symm
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp1
  have htr_bound : ‖(matrixMercatorLog (Δ - 1)).trace‖ < 2 * Real.pi := by
    calc ‖(matrixMercatorLog (Δ - 1)).trace‖
        ≤ (d : ℝ) * ‖matrixMercatorLog (Δ - 1)‖ := norm_trace_le_dim_mul_norm _
      _ ≤ (d : ℝ) * (2 * ‖Δ - 1‖) :=
          mul_le_mul_of_nonneg_left (norm_matrixMercatorLog_le_two_mul (Δ - 1) (by linarith))
            (by positivity)
      _ = 2 * ((d : ℝ) * ‖Δ - 1‖) := by ring
      _ < 2 * Real.pi := by linarith
  rw [hn, norm_int_mul_two_pi_I] at htr_bound
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have habs : (|n| : ℝ) < 1 := by
    rcases lt_or_ge (|n| : ℝ) 1 with h | h
    · exact h
    · exfalso
      have hge : (1 : ℝ) * (2 * Real.pi) ≤ (|n| : ℝ) * (2 * Real.pi) :=
        mul_le_mul_of_nonneg_right h (le_of_lt h2pi)
      linarith
  have hint : (|n| : ℤ) < 1 := by exact_mod_cast habs
  have hn0 : n = 0 := Int.abs_lt_one_iff.mp hint
  rw [hn, hn0]; push_cast; ring

/-- **SU(d) re-pointed regime Hermitian-AND-traceless conjunct** (re-point R1 + R2 at
SU(d)): for `V, U ∈ SU(d)` with `d²·‖V − U‖ ≤ 1/8`, the concrete log-generator
`H = (-i)·matrixMercatorLog ((V⁻¹U).val − 1)` is **both Hermitian and traceless**, i.e.
`H ∈ 𝔰𝔲(d)`. This is the concrete-radius replacement for the existential IFT regime guard
`negI_matrixLog_herm_traceless_on_residual_nhd` (S105) — the substrate the re-pointed
super-quad regime needs. Hermitian half via `isHermitian_regime_concrete_sud` (S127);
traceless half via `matrixMercatorLog_trace_eq_zero_of_unitary` (R1) — the SU(d) det `= 1`
comes from `mem_specialUnitaryGroup_iff`, and `d·‖Δ − 1‖ ≤ d²·‖V − U‖ ≤ 1/8 < π` supplies
the trace-smallness bound. `trace ((-i)•Y) = (-i)·trace Y = 0`. -/
theorem regime_herm_traceless_concrete_sud {d : ℕ} [Nonempty (Fin d)]
    (V U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))
    (hVU : (d : ℝ) ^ 2 *
        ‖(V : Matrix (Fin d) (Fin d) ℂ) - (U : Matrix (Fin d) (Fin d) ℂ)‖ ≤ 1 / 8) :
    ((-Complex.I) • matrixMercatorLog
        ((V⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val - 1) :
        Matrix (Fin d) (Fin d) ℂ).IsHermitian ∧
    ((-Complex.I) • matrixMercatorLog
        ((V⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val - 1) :
        Matrix (Fin d) (Fin d) ℂ).trace = 0 := by
  refine ⟨isHermitian_regime_concrete_sud V U hVU, ?_⟩
  set Δ : Matrix (Fin d) (Fin d) ℂ :=
    (V⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val with hΔ
  have hu : Δ ∈ Matrix.unitaryGroup (Fin d) ℂ :=
    Matrix.specialUnitaryGroup_le_unitaryGroup (V⁻¹ * U).property
  have hΔΔH : Δ * Δᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff).mp hu
  have hΔHΔ : Δᴴ * Δ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff').mp hu
  have hdet : Δ.det = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp (V⁻¹ * U).property).2
  have hdpos : 0 < d := Fin.pos_iff_nonempty.mpr inferInstance
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdpos
  have hnn : (0 : ℝ) ≤ ‖(V : Matrix (Fin d) (Fin d) ℂ) - (U : Matrix (Fin d) (Fin d) ℂ)‖ :=
    norm_nonneg _
  have hres : ‖Δ - 1‖ ≤ (d : ℝ) *
      ‖(V : Matrix (Fin d) (Fin d) ℂ) - (U : Matrix (Fin d) (Fin d) ℂ)‖ := by
    rw [hΔ]; exact residual_norm_le_d_mul V U
  have hdd : (d : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith [hd1, sq_nonneg ((d : ℝ) - 1)]
  have hΔ_le : ‖Δ - 1‖ ≤ 1 / 8 := by
    calc ‖Δ - 1‖
        ≤ (d : ℝ) * ‖(V : Matrix (Fin d) (Fin d) ℂ) - (U : Matrix (Fin d) (Fin d) ℂ)‖ := hres
      _ ≤ (d : ℝ) ^ 2 * ‖(V : Matrix (Fin d) (Fin d) ℂ) - (U : Matrix (Fin d) (Fin d) ℂ)‖ :=
          mul_le_mul_of_nonneg_right hdd hnn
      _ ≤ 1 / 8 := hVU
  have huH : Δᴴ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose]
    exact hΔHΔ
  have hΔH_norm : ‖Δᴴ‖ ≤ (d : ℝ) := linftyOpNorm_unitary_le ⟨Δᴴ, huH⟩
  have hfactor : Δᴴ - 1 = -(Δᴴ * (Δ - 1)) := by
    rw [Matrix.mul_sub, mul_one, hΔHΔ, neg_sub]
  have hΔH_le : ‖Δᴴ - 1‖ ≤ 1 / 8 := by
    rw [hfactor, norm_neg]
    calc ‖Δᴴ * (Δ - 1)‖
        ≤ ‖Δᴴ‖ * ‖Δ - 1‖ := norm_mul_le _ _
      _ ≤ (d : ℝ) * ((d : ℝ) *
            ‖(V : Matrix (Fin d) (Fin d) ℂ) - (U : Matrix (Fin d) (Fin d) ℂ)‖) :=
          mul_le_mul hΔH_norm hres (norm_nonneg _) (le_trans zero_le_one hd1)
      _ = (d : ℝ) ^ 2 * ‖(V : Matrix (Fin d) (Fin d) ℂ) - (U : Matrix (Fin d) (Fin d) ℂ)‖ := by
          ring
      _ ≤ 1 / 8 := hVU
  have hsmall : (d : ℝ) * ‖Δ - 1‖ < Real.pi := by
    have hpi : (1 : ℝ) / 8 < Real.pi := by
      have := Real.pi_gt_three; linarith
    calc (d : ℝ) * ‖Δ - 1‖
        ≤ (d : ℝ) * ((d : ℝ) *
            ‖(V : Matrix (Fin d) (Fin d) ℂ) - (U : Matrix (Fin d) (Fin d) ℂ)‖) :=
          mul_le_mul_of_nonneg_left hres (le_trans zero_le_one hd1)
      _ = (d : ℝ) ^ 2 * ‖(V : Matrix (Fin d) (Fin d) ℂ) - (U : Matrix (Fin d) (Fin d) ℂ)‖ := by
          ring
      _ ≤ 1 / 8 := hVU
      _ < Real.pi := hpi
  have hYtr : (matrixMercatorLog (Δ - 1)).trace = 0 :=
    matrixMercatorLog_trace_eq_zero_of_unitary Δ hΔΔH hΔHΔ hdet hΔ_le hΔH_le hsmall
  rw [Matrix.trace_smul, hYtr, smul_zero]

end SKEFTHawking.FKLW.GenericSUd
