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

end SKEFTHawking.FKLW.GenericSUd
