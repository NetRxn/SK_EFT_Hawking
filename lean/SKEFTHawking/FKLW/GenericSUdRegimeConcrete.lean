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

end SKEFTHawking.FKLW.GenericSUd
