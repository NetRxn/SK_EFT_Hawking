/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — Concrete-radius matrix logarithm (Mercator series), brick 1

The IFT-derived `matrixLog d` (= `(expAmbientPartialHomeo d).symm`) is only
controlled on an **existential** neighborhood of `1`: Mathlib's
`HasStrictFDerivAt.toOpenPartialHomeomorph` produces a local inverse whose
domain `target` is an existential open set with no nameable radius. The
super-quad **regime hypothesis** `h_regime`, however, needs control on the
**concrete calibration ball** `‖Δ − 1‖ ≤ 2·ε₀_sud` (a *named* radius). This
gap — the existential IFT radius vs. the concrete calibration ball — is the
last blocker to an UNCONDITIONAL S.6 / T-A1′.5 / T-A2′.5 headline (the (B)
super-quad bound is already discharged at S102, fed into the cascade at S103).

This module begins the concrete-radius substrate: the **Mercator power series**
matrix logarithm

  `matrixMercatorLog X = ∑' n, ((-1)^n / (n+1)) • X^(n+1)`
                       = X − X²/2 + X³/3 − …    (the series for `log (1 + X)`)

which converges on the **named** ball `‖X‖ < 1` with the **explicit** bound
`‖matrixMercatorLog X‖ ≤ ‖X‖ / (1 − ‖X‖)`, giving in particular the Lipschitz
bound `‖matrixMercatorLog X‖ ≤ 2·‖X‖` on the concrete ball `‖X‖ ≤ 1/2`. This is
the concrete-radius analog of the existential `matrixLog_lipschitz_K_two_near_one`
(S.4), with the radius now a *named* `1/2` rather than an unnameable `∃ δ`.

## Substantive content shipped (brick 1)

  * `matrixMercatorLog` — the series definition.
  * `summable_matrixMercatorLog` — termwise summability for `‖X‖ < 1`.
  * `norm_matrixMercatorLog_le` — `‖matrixMercatorLog X‖ ≤ ‖X‖ / (1 − ‖X‖)`.
  * `norm_matrixMercatorLog_le_two_mul` — `‖matrixMercatorLog X‖ ≤ 2·‖X‖`
    for `‖X‖ ≤ 1/2` (the concrete-radius K = 2 Lipschitz bound).

Subsequent bricks (later sessions): `exp (matrixMercatorLog X) = 1 + X` on the
ball (the exp/log round-trip via the BCH/series composition), and agreement
`matrixMercatorLog (Δ − 1) = matrixLog d Δ` for `Δ ∈ target` (via local
injectivity of `exp` near `0`), which together discharge the regime θ-bound and
`Δ ∈ target` conjuncts on the concrete calibration ball.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" — concrete-radius regime substrate (brick 1
of the Mercator-series matrix log replacing the existential IFT log).

-/

import Mathlib

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. The Mercator-series matrix logarithm -/

/-- **Mercator power-series matrix logarithm**: `matrixMercatorLog X` is the
Banach-algebra sum of the series `∑_{k≥1} (-1)^{k+1} X^k / k`, reindexed with
`k = n+1`:

  `matrixMercatorLog X = ∑' n, ((-1)^n / (n+1)) • X^(n+1)`.

For `‖X‖ < 1` this converges and equals `log (1 + X)`; the series gives a
**concrete-radius** matrix logarithm (named ball `‖X‖ < 1`), unlike the IFT
`matrixLog d` whose domain is an existential neighborhood. -/
noncomputable def matrixMercatorLog {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  ∑' n : ℕ, (((-1 : ℂ) ^ n / (n + 1 : ℂ))) • X ^ (n + 1)

/-! ## 2. Termwise norm bound -/

/-- Each Mercator term is norm-bounded by `‖X‖^(n+1)`:
`‖((-1)^n/(n+1)) • X^(n+1)‖ ≤ ‖X‖^(n+1)`. The scalar has norm `1/(n+1) ≤ 1`
and `‖X^(n+1)‖ ≤ ‖X‖^(n+1)` by submultiplicativity. -/
theorem norm_matrixMercatorLog_term_le {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ)
    (n : ℕ) :
    ‖(((-1 : ℂ) ^ n / (n + 1 : ℂ))) • X ^ (n + 1)‖ ≤ ‖X‖ ^ (n + 1) := by
  rw [norm_smul]
  have h_scalar : ‖((-1 : ℂ) ^ n / (n + 1 : ℂ))‖ = 1 / (n + 1 : ℝ) := by
    rw [norm_div, norm_pow, norm_neg, norm_one, one_pow]
    congr 1
    rw [show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
    push_cast; ring
  have h_pow : ‖X ^ (n + 1)‖ ≤ ‖X‖ ^ (n + 1) := norm_pow_le' X (Nat.succ_pos n)
  rw [h_scalar]
  have h_scalar_le_one : 1 / (n + 1 : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  calc 1 / (n + 1 : ℝ) * ‖X ^ (n + 1)‖
      ≤ 1 * ‖X ^ (n + 1)‖ := by
        apply mul_le_mul_of_nonneg_right h_scalar_le_one (norm_nonneg _)
    _ = ‖X ^ (n + 1)‖ := one_mul _
    _ ≤ ‖X‖ ^ (n + 1) := h_pow

/-! ## 3. Summability on the named ball `‖X‖ < 1` -/

/-- **Summability of the Mercator series for `‖X‖ < 1`** (named radius). By
comparison with the geometric series `∑ ‖X‖^(n+1)` (convergent since
`0 ≤ ‖X‖ < 1`), using the termwise bound `norm_matrixMercatorLog_term_le`. -/
theorem summable_matrixMercatorLog {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ)
    (hX : ‖X‖ < 1) :
    Summable (fun n : ℕ => (((-1 : ℂ) ^ n / (n + 1 : ℂ))) • X ^ (n + 1)) := by
  apply Summable.of_norm_bounded (g := fun n : ℕ => ‖X‖ ^ (n + 1))
  · have h_geom : Summable (fun n : ℕ => ‖X‖ ^ n) :=
      summable_geometric_of_lt_one (norm_nonneg X) hX
    simpa [pow_succ, mul_comm] using h_geom.mul_left ‖X‖
  · exact fun n => norm_matrixMercatorLog_term_le X n

/-! ## 4. Concrete-radius norm bounds -/

/-- **Explicit norm bound `‖matrixMercatorLog X‖ ≤ ‖X‖ / (1 − ‖X‖)`** for
`‖X‖ < 1` (named radius). Triangle inequality over the series + the geometric
tsum `∑ ‖X‖^(n+1) = ‖X‖ / (1 − ‖X‖)`. -/
theorem norm_matrixMercatorLog_le {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ)
    (hX : ‖X‖ < 1) :
    ‖matrixMercatorLog X‖ ≤ ‖X‖ / (1 - ‖X‖) := by
  have h_summable := summable_matrixMercatorLog X hX
  have h_norm_summable : Summable (fun n : ℕ => ‖X‖ ^ (n + 1)) := by
    have h_geom : Summable (fun n : ℕ => ‖X‖ ^ n) :=
      summable_geometric_of_lt_one (norm_nonneg X) hX
    simpa [pow_succ, mul_comm] using h_geom.mul_left ‖X‖
  calc ‖matrixMercatorLog X‖
      = ‖∑' n : ℕ, (((-1 : ℂ) ^ n / (n + 1 : ℂ))) • X ^ (n + 1)‖ := rfl
    _ ≤ ∑' n : ℕ, ‖(((-1 : ℂ) ^ n / (n + 1 : ℂ))) • X ^ (n + 1)‖ :=
        norm_tsum_le_tsum_norm (h_summable.norm)
    _ ≤ ∑' n : ℕ, ‖X‖ ^ (n + 1) :=
        Summable.tsum_le_tsum (fun n => norm_matrixMercatorLog_term_le X n)
          h_summable.norm h_norm_summable
    _ = ‖X‖ / (1 - ‖X‖) := by
        have h_geom : Summable (fun n : ℕ => ‖X‖ ^ n) :=
          summable_geometric_of_lt_one (norm_nonneg X) hX
        rw [show (fun n : ℕ => ‖X‖ ^ (n + 1)) = (fun n : ℕ => ‖X‖ * ‖X‖ ^ n) from by
          funext n; rw [pow_succ, mul_comm]]
        rw [tsum_mul_left, tsum_geometric_of_lt_one (norm_nonneg X) hX]
        rw [div_eq_mul_inv]

/-- **Concrete-radius Lipschitz bound `‖matrixMercatorLog X‖ ≤ 2·‖X‖`** on the
named ball `‖X‖ ≤ 1/2`. This is the concrete-radius analog of the existential
`matrixLog_lipschitz_K_two_near_one` (S.4): same constant `K = 2`, but the
radius is now a *named* `1/2` rather than an unnameable `∃ δ`. -/
theorem norm_matrixMercatorLog_le_two_mul {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ)
    (hX : ‖X‖ ≤ 1 / 2) :
    ‖matrixMercatorLog X‖ ≤ 2 * ‖X‖ := by
  have hX_lt : ‖X‖ < 1 := by linarith
  have h_le := norm_matrixMercatorLog_le X hX_lt
  have h_denom_pos : 0 < 1 - ‖X‖ := by linarith
  have h_half_le_denom : (1 : ℝ) / 2 ≤ 1 - ‖X‖ := by linarith
  calc ‖matrixMercatorLog X‖
      ≤ ‖X‖ / (1 - ‖X‖) := h_le
    _ ≤ ‖X‖ / (1 / 2) := by
        apply div_le_div_of_nonneg_left (norm_nonneg X) (by norm_num) h_half_le_denom
    _ = 2 * ‖X‖ := by ring

/-! ## 5. Commutation (substrate for the exp/log round-trip, brick 2)

The next brick (`exp (matrixMercatorLog X) = 1 + X`) is proved by a derivative
argument `d/dt [exp(−matrixMercatorLog(t•X)) · (1 + t•X)] = 0`, which needs
`matrixMercatorLog X` to commute with `X` (so that `d/dt exp(A(t)) =
exp(A(t))·A'(t)` applies, both `A(t)` and `A'(t)` being power series in `X`).
Since every Mercator term `c_n • X^(n+1)` commutes with `X` (powers of `X`
commute with `X`), so does the series sum. -/

/-- **`matrixMercatorLog X` commutes with `X`** (for `‖X‖ < 1`). The Mercator
sum is a limit of polynomials in `X`, each commuting with `X`; the
left/right-multiplication `HasSum` images coincide termwise
(`X · X^(n+1) = X^(n+2) = X^(n+1) · X`), so the two sums are equal. -/
theorem matrixMercatorLog_commute_self {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ)
    (hX : ‖X‖ < 1) :
    Commute X (matrixMercatorLog X) := by
  have h_sum : HasSum (fun n : ℕ => (((-1 : ℂ) ^ n / (n + 1 : ℂ))) • X ^ (n + 1))
      (matrixMercatorLog X) := (summable_matrixMercatorLog X hX).hasSum
  have h_left := h_sum.mul_left X
  have h_right := h_sum.mul_right X
  have h_eq : (fun n : ℕ => X * ((((-1 : ℂ) ^ n / (n + 1 : ℂ))) • X ^ (n + 1))) =
              (fun n : ℕ => ((((-1 : ℂ) ^ n / (n + 1 : ℂ))) • X ^ (n + 1)) * X) := by
    funext n
    rw [mul_smul_comm, smul_mul_assoc, ← pow_succ', ← pow_succ]
  rw [h_eq] at h_left
  exact h_left.unique h_right

/-- **`matrixMercatorLog X` commutes with `1 + X`** (for `‖X‖ < 1`). Combines
`matrixMercatorLog_commute_self` with the trivial commutation of `1`. -/
theorem matrixMercatorLog_commute_one_add {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ)
    (hX : ‖X‖ < 1) :
    Commute (1 + X) (matrixMercatorLog X) :=
  (Commute.one_left (matrixMercatorLog X)).add_left (matrixMercatorLog_commute_self X hX)

/-- **`matrixMercatorLog X` commutes with any `Y` that commutes with `X`**
(for `‖X‖ < 1`). The general commutation workhorse for the brick-2 round-trip:
the exp-path derivative `d/dt exp(A(t)) = exp(A(t))·A'(t)` needs `A(t) =
matrixMercatorLog(t•X)` to commute with `A'(t) = X·(1+t•X)⁻¹` and with the other
`matrixMercatorLog(s•X)` — all of which commute with `X`. Each Mercator term
`c_n • X^(n+1)` commutes with `Y` (since `X` does), so the series sum does. -/
theorem matrixMercatorLog_commute_of_commute {d : ℕ} (X Y : Matrix (Fin d) (Fin d) ℂ)
    (hX : ‖X‖ < 1) (hXY : Commute X Y) :
    Commute (matrixMercatorLog X) Y := by
  have h_sum : HasSum (fun n : ℕ => (((-1 : ℂ) ^ n / (n + 1 : ℂ))) • X ^ (n + 1))
      (matrixMercatorLog X) := (summable_matrixMercatorLog X hX).hasSum
  have h_right := h_sum.mul_right Y
  have h_left := h_sum.mul_left Y
  have h_eq : (fun n : ℕ => ((((-1 : ℂ) ^ n / (n + 1 : ℂ))) • X ^ (n + 1)) * Y) =
              (fun n : ℕ => Y * ((((-1 : ℂ) ^ n / (n + 1 : ℂ))) • X ^ (n + 1))) := by
    funext n
    rw [smul_mul_assoc, mul_smul_comm]
    congr 1
    exact hXY.pow_left (n + 1)
  rw [h_eq] at h_right
  exact (h_left.unique h_right).symm

/-- **`matrixMercatorLog X` commutes with `matrixMercatorLog Y`** when `X, Y`
commute (and `‖X‖, ‖Y‖ < 1`). Pairwise commutation of the Mercator-log path —
used in the brick-2 round-trip to commute `matrixMercatorLog(s•X)` with
`matrixMercatorLog(t•X)`. Two applications of
`matrixMercatorLog_commute_of_commute`. -/
theorem matrixMercatorLog_commute_mercatorLog {d : ℕ} (X Y : Matrix (Fin d) (Fin d) ℂ)
    (hX : ‖X‖ < 1) (hY : ‖Y‖ < 1) (hXY : Commute X Y) :
    Commute (matrixMercatorLog X) (matrixMercatorLog Y) :=
  matrixMercatorLog_commute_of_commute X (matrixMercatorLog Y) hX
    (matrixMercatorLog_commute_of_commute Y X hY hXY.symm).symm

/-! ## 6. Per-term derivative of the Mercator-log path (brick 2, crux iii input)

The brick-2 round-trip `exp (matrixMercatorLog X) = 1 + X` differentiates the path
`t ↦ matrixMercatorLog ((↑t)•X)` term by term (via `hasDerivAt_tsum_of_isPreconnected`
on a ball `‖t‖ < 1/‖X‖`). This is the per-term input.

**Instance-diamond note**: the naive `HasDerivAt.smul_const` route fails — it resolves
the ℝ-module on `Matrix ℂ` through the local `Matrix.linftyOpNormedAddCommGroup` path,
which is a non-defeq diamond with the standard `Matrix.addCommGroup`/Pi module the goal
uses (surfaced misleadingly as an `IsScalarTower` synthesis failure). The fix used here
**bundles the ℂ-smul into a continuous ℝ-linear map** `g : ℂ →L[ℝ] Matrix ℂ`,
`g z = z • X^(n+1)` (`(id ℂ).smulRight (X^(n+1)) |>.restrictScalars ℝ`), and differentiates
via `g.hasFDerivAt.comp_hasDerivAt` — sidestepping the module diamond entirely. -/

/-- **Per-term derivative of the Mercator-log path**: for each `n`,
`d/dt [c_n • ((↑t)•X)^(n+1)] = ((-1)^n · (↑t)^n) • X^(n+1)` (the coefficient
`(n+1)·c_n = (-1)^n` collapse). Differentiated via a bundled ℝ-linear `g z = z • X^(n+1)`
composed with the smooth scalar path `s ↦ c_n·(↑s)^(n+1)`, avoiding the
`linftyOp`-vs-standard ℝ-module diamond that defeats `HasDerivAt.smul_const`. -/
theorem hasDerivAt_matrixMercatorLog_term {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ)
    (n : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (((-1 : ℂ) ^ n / (n + 1 : ℂ))) • ((↑s : ℂ) • X) ^ (n + 1))
      ((((-1 : ℂ) ^ n) * (↑t : ℂ) ^ n) • X ^ (n + 1)) t := by
  set M : Matrix (Fin d) (Fin d) ℂ := X ^ (n + 1) with hM
  set g : ℂ →L[ℝ] Matrix (Fin d) (Fin d) ℂ :=
    (ContinuousLinearMap.id ℂ ℂ).smulRight M |>.restrictScalars ℝ with hg
  have hpath : HasDerivAt (fun s : ℝ => ((-1 : ℂ) ^ n / (n + 1 : ℂ)) * (↑s : ℂ) ^ (n + 1))
      (((-1 : ℂ) ^ n / (n + 1 : ℂ)) * (((n : ℂ) + 1) * (↑t : ℂ) ^ n)) t := by
    have h_ofReal : HasDerivAt (fun s : ℝ => (↑s : ℂ)) 1 t := by
      simpa using Complex.ofRealCLM.hasDerivAt (x := t)
    have h_pow := h_ofReal.pow (n + 1)
    simpa [Nat.cast_add, Nat.cast_one, mul_comm] using
      h_pow.const_mul ((-1 : ℂ) ^ n / (n + 1 : ℂ))
  have hcomp := g.hasFDerivAt.comp_hasDerivAt t hpath
  have hg_apply : ∀ z : ℂ, g z = z • M := by
    intro z
    simp only [hg, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.coe_id', id_eq]
  have hfun : (⇑g ∘ fun s : ℝ => ((-1 : ℂ) ^ n / (n + 1 : ℂ)) * (↑s : ℂ) ^ (n + 1))
      = (fun s : ℝ => (((-1 : ℂ) ^ n / (n + 1 : ℂ))) • ((↑s : ℂ) • X) ^ (n + 1)) := by
    funext s
    rw [Function.comp_apply, hg_apply, hM, smul_pow, smul_smul]
  rw [hfun] at hcomp
  rw [hg_apply] at hcomp
  convert hcomp using 1
  have hn1 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  congr 1
  field_simp

/-- **Summability of the Mercator-log derivative series** `∑ ((-1)^n (↑t)^n) • X^(n+1)`
for `|t|·‖X‖ < 1`. Comparison with the geometric series `∑ (|t|‖X‖)^n · ‖X‖`. -/
theorem summable_matrixMercatorLog_deriv_series {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ)
    (t : ℝ) (ht : |t| * ‖X‖ < 1) :
    Summable (fun n : ℕ => (((-1 : ℂ) ^ n * (↑t : ℂ) ^ n)) • X ^ (n + 1)) := by
  apply Summable.of_norm_bounded (g := fun n : ℕ => (|t| * ‖X‖) ^ n * ‖X‖)
  · exact (summable_geometric_of_lt_one (by positivity) ht).mul_right ‖X‖
  · intro n
    rw [norm_smul]
    have hsc : ‖((-1 : ℂ) ^ n * (↑t : ℂ) ^ n)‖ = |t| ^ n := by
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow,
        Complex.norm_real, Real.norm_eq_abs]
    have hpow : ‖X ^ (n + 1)‖ ≤ ‖X‖ ^ (n + 1) := norm_pow_le' X (Nat.succ_pos n)
    rw [hsc]
    calc |t| ^ n * ‖X ^ (n + 1)‖ ≤ |t| ^ n * ‖X‖ ^ (n + 1) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = (|t| * ‖X‖) ^ n * ‖X‖ := by rw [mul_pow, pow_succ]; ring

/-- **Derivative series = resolvent form**: `∑ ((-1)^n (↑t)^n) • X^(n+1) =
(1 + (↑t)•X)⁻¹ · X` for `|t|·‖X‖ < 1`. This identifies the term-by-term derivative
of `matrixMercatorLog((↑t)•X)` (the sum of `hasDerivAt_matrixMercatorLog_term` values)
with the **resolvent** `(1+(↑t)•X)⁻¹·X` — exactly the form `d/dt log(1+tX) = X(1+tX)⁻¹`
needed for the brick-2 round-trip `f(t)=exp(−mLog(t•X))·(1+t•X)`, `f'=0`. Via the
termwise factoring `((-1)^n(↑t)^n)•X^(n+1) = (-(↑t)•X)^n·X`, `HasSum.mul_right`, and
the Neumann series `geom_series_eq_inverse`. -/
theorem tsum_matrixMercatorLog_deriv_eq {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) (t : ℝ)
    (ht : |t| * ‖X‖ < 1) :
    (∑' n : ℕ, (((-1 : ℂ) ^ n * (↑t : ℂ) ^ n)) • X ^ (n + 1))
      = Ring.inverse (1 + (↑t : ℂ) • X) * X := by
  have hY : ‖(-((↑t : ℂ) • X))‖ < 1 := by
    rw [norm_neg, norm_smul, Complex.norm_real, Real.norm_eq_abs]; exact ht
  have hterm : ∀ n : ℕ, (((-1 : ℂ) ^ n * (↑t : ℂ) ^ n)) • X ^ (n + 1)
      = (-((↑t : ℂ) • X)) ^ n * X := by
    intro n
    rw [← neg_smul, smul_pow, smul_mul_assoc, ← pow_succ]
    congr 1
    conv_rhs => rw [neg_pow]
  rw [tsum_congr hterm]
  have hsummY : Summable (fun n : ℕ => (-((↑t : ℂ) • X)) ^ n) :=
    summable_geometric_of_norm_lt_one hY
  rw [(hsummY.hasSum.mul_right X).tsum_eq, geom_series_eq_inverse _ hY, sub_neg_eq_add]

/-! ## 7. The path derivative (brick 2, crux iii COMPLETE) -/

/-- **Path derivative of the Mercator log** (crux iii): for `|t|·‖X‖ < 1`,

  `d/dt [matrixMercatorLog ((↑t)•X)] = (1 + (↑t)•X)⁻¹ · X`.

This is the matrix analog of `d/dt log(1 + tX) = X(1+tX)⁻¹`. Assembled by
term-by-term differentiation: `hasDerivAt_tsum_of_isPreconnected` on the ball
`‖s‖ < R` (`|t| < R < 1/‖X‖`), with per-term derivatives from
`hasDerivAt_matrixMercatorLog_term`, the uniform geometric bound
`‖g' n s‖ ≤ R^n‖X‖^(n+1)` (summable since `R‖X‖ < 1`), and the derivative-series
sum identified via `tsum_matrixMercatorLog_deriv_eq` with the resolvent
`(1+(↑t)•X)⁻¹·X`. The `X = 0` case is handled separately (both sides `0`).

This is the analytic core of the brick-2 exp/log round-trip
`exp (matrixMercatorLog X) = 1 + X`: the round-trip is proved by showing
`f(t) = exp(−matrixMercatorLog(t•X))·(1+t•X)` has `f'(t) = 0` (using this path
derivative + the exp-path derivative, crux iv) and `f(0) = 1`. -/
theorem hasDerivAt_matrixMercatorLog_path {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ)
    (t : ℝ) (ht : |t| * ‖X‖ < 1) :
    HasDerivAt (fun s : ℝ => matrixMercatorLog ((↑s : ℂ) • X))
      (Ring.inverse (1 + (↑t : ℂ) • X) * X) t := by
  by_cases hX0 : X = 0
  · subst hX0
    have hf : (fun s : ℝ => matrixMercatorLog ((↑s : ℂ) • (0 : Matrix (Fin d) (Fin d) ℂ)))
        = fun _ : ℝ => (0 : Matrix (Fin d) (Fin d) ℂ) := by
      funext s; rw [smul_zero]
      show matrixMercatorLog 0 = 0
      unfold matrixMercatorLog; simp [zero_pow]
    rw [hf, mul_zero]
    exact hasDerivAt_const t 0
  · have hXpos : (0 : ℝ) < ‖X‖ := norm_pos_iff.mpr hX0
    have htX : |t| < 1 / ‖X‖ := (lt_div_iff₀ hXpos).mpr ht
    set R : ℝ := (|t| + 1 / ‖X‖) / 2 with hRdef
    have htR : |t| < R := by rw [hRdef]; linarith
    have hRlt : R < 1 / ‖X‖ := by rw [hRdef]; linarith
    have hRX : R * ‖X‖ < 1 := (lt_div_iff₀ hXpos).mp hRlt
    have hu : Summable (fun n : ℕ => R ^ n * ‖X‖ ^ (n + 1)) := by
      have heq : (fun n : ℕ => R ^ n * ‖X‖ ^ (n + 1)) = fun n => ‖X‖ * (R * ‖X‖) ^ n := by
        funext n; rw [mul_pow, pow_succ]; ring
      rw [heq]
      exact (summable_geometric_of_lt_one (by positivity) hRX).mul_left ‖X‖
    have hbound : ∀ (n : ℕ), ∀ s ∈ Metric.ball (0 : ℝ) R,
        ‖(((-1 : ℂ) ^ n * (↑s : ℂ) ^ n)) • X ^ (n + 1)‖ ≤ R ^ n * ‖X‖ ^ (n + 1) := by
      intro n s hs
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hs
      rw [norm_smul]
      have hsc : ‖((-1 : ℂ) ^ n * (↑s : ℂ) ^ n)‖ = |s| ^ n := by
        rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow,
          Complex.norm_real, Real.norm_eq_abs]
      rw [hsc]
      exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg s) hs.le n)
        (norm_pow_le' X (Nat.succ_pos n)) (norm_nonneg _) (by positivity)
    have h0mem : (0 : ℝ) ∈ Metric.ball (0 : ℝ) R := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_zero]
      exact lt_of_le_of_lt (abs_nonneg t) htR
    have hgsum : Summable
        (fun n : ℕ => (((-1 : ℂ) ^ n / (n + 1 : ℂ))) • ((↑(0 : ℝ) : ℂ) • X) ^ (n + 1)) := by
      have hz : (fun n : ℕ => (((-1 : ℂ) ^ n / (n + 1 : ℂ))) • ((↑(0 : ℝ) : ℂ) • X) ^ (n + 1))
          = fun _ : ℕ => (0 : Matrix (Fin d) (Fin d) ℂ) := by
        funext n; simp [zero_pow]
      rw [hz]; exact summable_zero
    have htmem : t ∈ Metric.ball (0 : ℝ) R := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero]; exact htR
    have hmain := hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
      (convex_ball (0 : ℝ) R).isPreconnected
      (fun n s _ => hasDerivAt_matrixMercatorLog_term X n s) hbound h0mem hgsum htmem
    rw [tsum_matrixMercatorLog_deriv_eq X t ht] at hmain
    exact hmain

/-! ## 8. The commuting-path exp derivative (brick 2, crux iv) -/

/-- **Exp-path derivative for a commuting path** (crux iv): if `A : ℝ → Matrix ℂ`
has derivative `A'` at `t₀` and, *eventually near* `t₀`, each value `A t` commutes
with `A t₀` (so `Commute (A t₀) (A t − A t₀)`), then

  `d/dt [exp (A t)] = exp (A t₀) · A'`  at `t₀`.

Mathlib has the non-commutative exp Fréchet derivative only for `NormedCommRing`
(`hasFDerivAt_exp`) or the linear path `u•x` (`hasDerivAt_exp_smul_const`); the
general commuting-path version is built here. **Proof**: by `exp_add_of_commute`,
`exp (A t) = exp (A t₀) · exp (A t − A t₀)` *eventually near* `t₀`; the factor
`exp (A t − A t₀)` has derivative `A'` at `t₀` (since `A − A t₀` vanishes at `t₀`
and `exp`'s Fréchet derivative at `0` is the identity, `hasStrictFDerivAt_exp_zero`);
left-multiplying by the constant `exp (A t₀)` (continuous-linear) + `congr_of_eventuallyEq`
gives the result. The *eventual* (vs. global) commute hypothesis is essential: for
`A t = −matrixMercatorLog((↑t)•X)` the commute only holds where `‖(↑t)•X‖ < 1`. -/
theorem hasDerivAt_exp_path {d : ℕ} (A : ℝ → Matrix (Fin d) (Fin d) ℂ)
    (A' : Matrix (Fin d) (Fin d) ℂ) (t₀ : ℝ) (hA : HasDerivAt A A' t₀)
    (hcomm : ∀ᶠ t in nhds t₀, Commute (A t₀) (A t - A t₀)) :
    HasDerivAt (fun t => NormedSpace.exp (A t)) (NormedSpace.exp (A t₀) * A') t₀ := by
  have hB : HasDerivAt (fun t => A t - A t₀) A' t₀ := hA.sub_const (A t₀)
  have hBzero : (fun t => A t - A t₀) t₀ = 0 := sub_self _
  have hexpB : HasDerivAt (fun t => NormedSpace.exp (A t - A t₀)) A' t₀ := by
    have hfd : HasFDerivAt (NormedSpace.exp : Matrix (Fin d) (Fin d) ℂ → _)
        (1 : Matrix (Fin d) (Fin d) ℂ →L[ℝ] Matrix (Fin d) (Fin d) ℂ)
        ((fun t => A t - A t₀) t₀) := by
      rw [hBzero]
      exact (hasStrictFDerivAt_exp_zero (𝕂 := ℝ)).hasFDerivAt
    simpa using hfd.comp_hasDerivAt t₀ hB
  refine (hexpB.const_mul (NormedSpace.exp (A t₀))).congr_of_eventuallyEq ?_
  filter_upwards [hcomm] with t ht
  rw [← NormedSpace.exp_add_of_commute ht]
  congr 1
  abel

/-- **Derivative of `exp(−matrixMercatorLog((↑t)•X))`** (the `u(t)` factor of the
brick-2 round-trip `f(t) = exp(−mLog(t•X))·(1+t•X)`): for `|t₀|·‖X‖ < 1`,

  `d/dt [exp(−matrixMercatorLog((↑t)•X))] = exp(−mLog((↑t₀)•X)) · (−(1+(↑t₀)•X)⁻¹·X)`.

Composes the path derivative (crux iii, negated) with the commuting-path exp
derivative (crux iv). The eventual-commute hypothesis is supplied from the
continuity of `t ↦ |t|·‖X‖` (so `‖(↑t)•X‖ < 1` near `t₀`) + pairwise log
commutation `matrixMercatorLog_commute_mercatorLog` (all values are power series
in `X`). -/
theorem hasDerivAt_exp_neg_matrixMercatorLog_path {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ)
    (t₀ : ℝ) (ht₀ : |t₀| * ‖X‖ < 1) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (-(matrixMercatorLog ((↑t : ℂ) • X))))
      (NormedSpace.exp (-(matrixMercatorLog ((↑t₀ : ℂ) • X)))
        * (-(Ring.inverse (1 + (↑t₀ : ℂ) • X) * X))) t₀ := by
  have hpath : HasDerivAt (fun t : ℝ => -(matrixMercatorLog ((↑t : ℂ) • X)))
      (-(Ring.inverse (1 + (↑t₀ : ℂ) • X) * X)) t₀ :=
    (hasDerivAt_matrixMercatorLog_path X t₀ ht₀).neg
  have hev : ∀ᶠ t in nhds t₀, |t| * ‖X‖ < 1 := by
    have hcont : ContinuousAt (fun t : ℝ => |t| * ‖X‖) t₀ :=
      (continuous_abs.continuousAt).mul continuousAt_const
    exact hcont.eventually_lt continuousAt_const ht₀
  refine hasDerivAt_exp_path _ _ t₀ hpath ?_
  filter_upwards [hev] with t ht
  have hXt₀ : ‖(↑t₀ : ℂ) • X‖ < 1 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]; exact ht₀
  have hXt : ‖(↑t : ℂ) • X‖ < 1 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]; exact ht
  have hcXX : Commute ((↑t₀ : ℂ) • X) ((↑t : ℂ) • X) :=
    ((Commute.refl X).smul_left _).smul_right _
  have hmm : Commute (matrixMercatorLog ((↑t₀ : ℂ) • X)) (matrixMercatorLog ((↑t : ℂ) • X)) :=
    matrixMercatorLog_commute_mercatorLog _ _ hXt₀ hXt hcXX
  exact (hmm.neg_left.neg_right).sub_right (Commute.refl _).neg_left.neg_right

/-! ## 9. The round-trip factor derivative (brick 2, toward `exp∘mLog = id`) -/

/-- **Derivative of `t ↦ 1 + (↑t)•X`** (the `v(t)` factor of the round-trip):
`d/dt [1 + (↑t)•X] = X`. The `(↑t)•X` smul is differentiated via the bundled
ℝ-linear map `z ↦ z • X` composed with `Complex.ofReal` (deriv 1), avoiding the
`linftyOp` module diamond (same technique as `hasDerivAt_matrixMercatorLog_term`). -/
theorem hasDerivAt_one_add_smul {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (1 : Matrix (Fin d) (Fin d) ℂ) + (↑s : ℂ) • X) X t := by
  have hofR : HasDerivAt (fun s : ℝ => (↑s : ℂ)) 1 t := by
    simpa using Complex.ofRealCLM.hasDerivAt (x := t)
  have hg : HasDerivAt (fun s : ℝ => (↑s : ℂ) • X) X t := by
    have := (((ContinuousLinearMap.id ℂ ℂ).smulRight X).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
      t hofR
    simpa using this
  simpa using hg.const_add (1 : Matrix (Fin d) (Fin d) ℂ)

/-- **The round-trip factor has zero derivative**: for `|t|·‖X‖ < 1`,

  `d/dt [exp(−matrixMercatorLog((↑t)•X)) · (1 + (↑t)•X)] = 0`.

This is the heart of the brick-2 round-trip `exp(matrixMercatorLog X) = 1 + X`:
by the product rule (`u'` from `hasDerivAt_exp_neg_matrixMercatorLog_path`, `v' = X`
from `hasDerivAt_one_add_smul`), the derivative is
`exp(−mLog)·(−(1+Y)⁻¹·X)·(1+Y) + exp(−mLog)·X` with `Y = (↑t)•X`; since `X` commutes
with `1+Y` (both functions of `X`) and `1+Y` is a unit (Neumann, `‖Y‖<1`),
`(1+Y)⁻¹·X·(1+Y) = X`, so the two terms cancel. Combined with `f(0) = exp(0)·1 = 1`
and a constancy argument on the ball `|t| < 1/‖X‖`, this yields the round-trip. -/
theorem hasDerivAt_round_trip_factor {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ)
    (t : ℝ) (ht : |t| * ‖X‖ < 1) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (-(matrixMercatorLog ((↑s : ℂ) • X)))
        * (1 + (↑s : ℂ) • X)) 0 t := by
  have hf := (hasDerivAt_exp_neg_matrixMercatorLog_path X t ht).mul (hasDerivAt_one_add_smul X t)
  have hunit : IsUnit (1 + (↑t : ℂ) • X) := by
    have h : ‖(-((↑t : ℂ) • X))‖ < 1 := by
      rw [norm_neg, norm_smul, Complex.norm_real, Real.norm_eq_abs]; exact ht
    simpa [sub_neg_eq_add] using (Units.oneSub (-((↑t : ℂ) • X)) h).isUnit
  have hX1Y : Commute X (1 + (↑t : ℂ) • X) :=
    (Commute.one_right X).add_right ((Commute.refl X).smul_right _)
  have hkey : Ring.inverse (1 + (↑t : ℂ) • X) * X * (1 + (↑t : ℂ) • X) = X := by
    rw [mul_assoc, hX1Y.eq, ← mul_assoc, Ring.inverse_mul_cancel _ hunit, one_mul]
  convert hf using 1
  symm
  rw [mul_neg, neg_mul,
    mul_assoc (NormedSpace.exp (-(matrixMercatorLog ((↑t : ℂ) • X))))
      (Ring.inverse (1 + (↑t : ℂ) • X) * X) (1 + (↑t : ℂ) • X),
    hkey, neg_add_cancel]

end SKEFTHawking.FKLW.GenericSUd
