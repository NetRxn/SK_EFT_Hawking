/-
SK_EFT_Hawking Phase 6t Iteration 2 substrate (2026-05-22 PM):
**Near-identity-sharpened stability bound for the group commutator**.

This module ships the substrate gap identified by the Iteration 2 DN-recursion
analysis (`temporary/working-docs/proof-state/phase6t-iteration2-dn-recursion-analysis.md`):

  > Wave 1's `groupCommutator_stability` gives `‖[g',h'] - [g,h]‖ ≤ 4·M³·ε`,
  > which is **linear in ε**. In the DN recursion this term dominates the
  > Wave 1 cubic-BCH remainder, blocking super-quadratic shrinkage. The fix
  > is a **near-identity-sharpened** stability: when the operands `g, h` are
  > close to the identity (within `η`), the leading-order perturbation
  > `(g' - g)` and `(g'⁻¹ - g⁻¹)` cancel, leaving residual of size
  > `O(δ·η + δ²)`. With `η = √ε_n` (Lie-algebra norm) and `δ = ε_n`
  > (level-n approximation error), this gives `O(ε_n^(3/2))`. ✓

The key algebraic move is the inv-diff identity
  `g'⁻¹ - g⁻¹ = -g'⁻¹·(g'-g)·g⁻¹`
which makes the contribution of T₃ in the 4-term telescoping
of `[g',h'] - [g,h]` (see `groupCommutator_telescope`) into a form that
pair-wise cancels with T₁. After cancellation, the residual factors carry
either `(h - 1)` (size η) or `(g'·h'·g'⁻¹ - 1)` (size at most M²·(η+δ)).

## Phase 6t roadmap alignment

  - Iteration 2 (this module) → consumed by `skApprox_exists` (next ship)
    to drive substantive `skApprox(n+1)` body. Together with Task #34
    (balanced commutator) and Wave 1 cubic remainder, this closes the
    Dawson-Nielsen super-quadratic shrinkage chain.

## Pipeline Invariant compliance

  - Invariant #10 (no `maxHeartbeats`): RESPECTED.
  - Invariant #15 (no new axioms): RESPECTED.

Primary source: Dawson & Nielsen, *Quantum Info. & Comp.* 6 (2006), 81–95;
                arXiv:quant-ph/0505030, §3.1-3.2 (the recursion step's
                stability analysis).
-/

import Mathlib
import SKEFTHawking.FKLW.GroupCommutator
import SKEFTHawking.FKLW.OneParameterSubgroupSU2

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GroupCommutatorNearIdentity

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

open Matrix SKEFTHawking.FKLW.GroupCommutator

/-! ## 1. The pair-wise cancellation identities

The 4-term telescoping of `[g', h'] - [g, h]` (Wave 1's
`groupCommutator_telescope`) gives:

  T₁ = (g' - g) · h · g⁻¹ · h⁻¹
  T₂ = g' · (h' - h) · g⁻¹ · h⁻¹
  T₃ = g' · h' · (g'⁻¹ - g⁻¹) · h⁻¹
  T₄ = g' · h' · g'⁻¹ · (h'⁻¹ - h⁻¹)

For invertible `g, g'`, the **inverse-difference identity**
`g'⁻¹ - g⁻¹ = -g'⁻¹·(g' - g)·g⁻¹` allows T₃ to be rewritten so that the
leading `(g' - g)` cancels against T₁, leaving a residual depending on
`h - 1` (size η) and `g'·h'·g'⁻¹ - 1` (size M²·(η+δ)).

Similarly for `h, h'`: `h'⁻¹ - h⁻¹ = -h'⁻¹·(h' - h)·h⁻¹` rewrites T₄ so the
leading `(h' - h)` cancels against T₂, leaving a residual depending on
`g⁻¹ - 1` (size η) and `h'·g'⁻¹·h'⁻¹ - 1` (size M²·(η+δ)). -/

/-- **Pair-wise cancellation T₁+T₃**: for invertible `g, g'`,

  `(g'-g)·h·g⁻¹·h⁻¹ + g'·h'·(g'⁻¹-g⁻¹)·h⁻¹ =`
  `  ((g'-g)·(h-1) - (g'·h'·g'⁻¹ - 1)·(g'-g)) · (g⁻¹·h⁻¹)`.

This identity makes the cancellation of leading-order `(g'-g)`
between T₁ and T₃ explicit. After cancellation, the residual factors
carry either `(h - 1)` or `(g'·h'·g'⁻¹ - 1)`, both small in the
near-identity regime. -/
lemma T₁_plus_T₃_factor
    {d : ℕ} (g h g' h' : Matrix (Fin d) (Fin d) ℂ)
    (hg : IsUnit g.det) (hg' : IsUnit g'.det) :
    ((g' - g) * h * g⁻¹ * h⁻¹) + (g' * h' * (g'⁻¹ - g⁻¹) * h⁻¹) =
      ((g' - g) * (h - 1) - (g' * h' * g'⁻¹ - 1) * (g' - g)) * (g⁻¹ * h⁻¹) := by
  -- The key algebraic step: rewrite g'⁻¹ - g⁻¹ via Matrix.inv_sub_inv.
  have hg_unit : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).mpr hg
  have hg'_unit : IsUnit g' := (Matrix.isUnit_iff_isUnit_det g').mpr hg'
  have h_iff : IsUnit g' ↔ IsUnit g := ⟨fun _ => hg_unit, fun _ => hg'_unit⟩
  have h_inv_diff : g'⁻¹ - g⁻¹ = g'⁻¹ * (g - g') * g⁻¹ :=
    Matrix.inv_sub_inv h_iff
  have h_g_g' : g - g' = -(g' - g) := by abel
  -- Substitute g'⁻¹ - g⁻¹ → g'⁻¹ * (-(g' - g)) * g⁻¹.
  rw [h_inv_diff, h_g_g']
  -- The identity now reduces to a ring identity in the matrix algebra
  -- (both sides expand to (g'-g)·h·g⁻¹·h⁻¹ - g'·h'·g'⁻¹·(g'-g)·g⁻¹·h⁻¹).
  noncomm_ring

/-- **Pair-wise cancellation T₂+T₄**: for invertible `h, h'`,

  `g'·(h'-h)·g⁻¹·h⁻¹ + g'·h'·g'⁻¹·(h'⁻¹-h⁻¹) =`
  `  g' · ((h'-h)·(g⁻¹-1) - (h'·g'⁻¹·h'⁻¹ - 1)·(h'-h)) · h⁻¹`.

Symmetric to T₁+T₃ (interchange roles of g↔h). -/
lemma T₂_plus_T₄_factor
    {d : ℕ} (g h g' h' : Matrix (Fin d) (Fin d) ℂ)
    (hh : IsUnit h.det) (hh' : IsUnit h'.det) :
    (g' * (h' - h) * g⁻¹ * h⁻¹) + (g' * h' * g'⁻¹ * (h'⁻¹ - h⁻¹)) =
      g' * ((h' - h) * (g⁻¹ - 1) - (h' * g'⁻¹ * h'⁻¹ - 1) * (h' - h)) * h⁻¹ := by
  have hh_unit : IsUnit h := (Matrix.isUnit_iff_isUnit_det h).mpr hh
  have hh'_unit : IsUnit h' := (Matrix.isUnit_iff_isUnit_det h').mpr hh'
  have h_iff : IsUnit h' ↔ IsUnit h := ⟨fun _ => hh_unit, fun _ => hh'_unit⟩
  have h_inv_diff : h'⁻¹ - h⁻¹ = h'⁻¹ * (h - h') * h⁻¹ :=
    Matrix.inv_sub_inv h_iff
  have h_h_h' : h - h' = -(h' - h) := by abel
  rw [h_inv_diff, h_h_h']
  -- Same structure as T₁+T₃; the roles of g, h swap. Pure ring identity.
  noncomm_ring

/-! ## 2. The near-identity stability bound

Combining the pair-wise factorizations of §1 with the standard
submultiplicative norm bounds yields the near-identity-sharpened
group commutator stability.

The bound takes the form `C·δ·η + C'·δ²` where:
  - `δ = max(‖g'-g‖, ‖h'-h‖)` is the perturbation magnitude
  - `η = max(‖h-1‖, ‖g⁻¹-1‖)` is the near-identity radius

When `η = √ε`, `δ = ε`, this gives `O(ε^(3/2))` — the Dawson-Nielsen
super-quadratic shrinkage rate. -/

/-- **HEADLINE (Phase 6t Iteration 2 substrate)**: near-identity-sharpened
group commutator stability.

Given matrices `g, h, g', h' : Matrix (Fin d) (Fin d) ℂ` with:
  - **M-bound** `M ≥ 0` on `‖g'‖, ‖h'‖, ‖g⁻¹‖, ‖h⁻¹‖, ‖g'⁻¹‖, ‖h'⁻¹‖`,
  - **Near-identity bound** `η ≥ 0` on `‖h - 1‖, ‖g⁻¹ - 1‖`,
  - **Perturbation bound** `δ ≥ 0` on `‖g' - g‖, ‖h' - h‖`,
  - **Invertibility** of `g, g', h, h'`,

the group commutator's perturbation is bounded by

  `‖groupCommutator g' h' - groupCommutator g h‖ ≤ 2·(M² + M⁴)·δ·η + (M⁴ + M⁶)·δ²`.

The key sharpening over Wave 1's `groupCommutator_stability` (which gives
`4·M³·ε`, linear in ε) is the factor of `η` on the leading term. In the
Dawson-Nielsen SK recursion, `η = O(√ε_n)` (Lie-algebra norm of the
balanced-commutator operands) and `δ = O(ε_n)` (level-n IH precision),
so the leading term becomes `O(ε_n^(3/2))` — the DN super-quadratic
shrinkage rate.

The slight asymmetry between the T₁+T₃ contribution (`M⁴·δ²`) and the
T₂+T₄ contribution (`M⁶·δ²`) comes from `‖g'⁻¹ - 1‖` being bounded via
the inv-diff identity (extra `M²·δ` term) whereas `‖h' - 1‖` is bounded
by direct triangle inequality. For SU(2) under `linftyOp` norm with
`M = √2`, this gives `12·δ·η + 12·δ²` ≈ `24·ε_n^(3/2)` for our regime. -/
theorem groupCommutator_stability_nearIdentity
    {d : ℕ} (g h g' h' : Matrix (Fin d) (Fin d) ℂ)
    (η δ M : ℝ)
    (hη_nn : 0 ≤ η) (hδ_nn : 0 ≤ δ) (hM_nn : 0 ≤ M)
    -- M-bounds (uniform op-norm):
    (h_g'_norm : ‖g'‖ ≤ M) (h_h'_norm : ‖h'‖ ≤ M)
    (h_g_inv_norm : ‖g⁻¹‖ ≤ M) (h_h_inv_norm : ‖h⁻¹‖ ≤ M)
    (h_g'_inv_norm : ‖g'⁻¹‖ ≤ M) (h_h'_inv_norm : ‖h'⁻¹‖ ≤ M)
    -- Near-identity bounds (only h and g⁻¹ — the cancellation needs these):
    (h_h_near_id : ‖h - 1‖ ≤ η) (h_g_inv_near_id : ‖g⁻¹ - 1‖ ≤ η)
    -- Perturbation bounds (direct only; inverse-diffs derived from invertibility):
    (h_g_diff : ‖g' - g‖ ≤ δ) (h_h_diff : ‖h' - h‖ ≤ δ)
    -- Invertibility (for inv-diff identity in pair-wise cancellation):
    (hg_det : IsUnit g.det) (hg'_det : IsUnit g'.det)
    (hh_det : IsUnit h.det) (hh'_det : IsUnit h'.det) :
    ‖SKEFTHawking.FKLW.GroupCommutator.groupCommutator g' h' -
        SKEFTHawking.FKLW.GroupCommutator.groupCommutator g h‖ ≤
      2 * (M ^ 2 + M ^ 4) * δ * η + (M ^ 4 + M ^ 6) * δ ^ 2 := by
  -- Step 1: expand via the 4-term telescoping.
  have h_telescope :=
    SKEFTHawking.FKLW.GroupCommutator.groupCommutator_telescope g h g' h'
  -- Step 2: rewrite (T₁+T₃) + (T₂+T₄) using pair-wise cancellation.
  have h_T13 := T₁_plus_T₃_factor g h g' h' hg_det hg'_det
  have h_T24 := T₂_plus_T₄_factor g h g' h' hh_det hh'_det
  -- The 4-term sum equals (T₁+T₃) + (T₂+T₄):
  have h_sum_split :
      SKEFTHawking.FKLW.GroupCommutator.groupCommutator g' h' -
        SKEFTHawking.FKLW.GroupCommutator.groupCommutator g h =
      (((g' - g) * (h - 1) - (g' * h' * g'⁻¹ - 1) * (g' - g)) * (g⁻¹ * h⁻¹)) +
      (g' * ((h' - h) * (g⁻¹ - 1) - (h' * g'⁻¹ * h'⁻¹ - 1) * (h' - h)) * h⁻¹) := by
    rw [h_telescope]
    rw [show ((g' - g) * h * g⁻¹ * h⁻¹) + (g' * (h' - h) * g⁻¹ * h⁻¹) +
            (g' * h' * (g'⁻¹ - g⁻¹) * h⁻¹) + (g' * h' * g'⁻¹ * (h'⁻¹ - h⁻¹))
          = (((g' - g) * h * g⁻¹ * h⁻¹) + (g' * h' * (g'⁻¹ - g⁻¹) * h⁻¹)) +
            ((g' * (h' - h) * g⁻¹ * h⁻¹) + (g' * h' * g'⁻¹ * (h'⁻¹ - h⁻¹))) from
       by abel]
    rw [h_T13, h_T24]
  rw [h_sum_split]
  -- Step 3: norm bookkeeping helpers.
  have h_M2_nn : 0 ≤ M ^ 2 := by positivity
  have h_M4_nn : 0 ≤ M ^ 4 := by positivity
  have h_δη_nn : 0 ≤ δ * η := by positivity
  have h_δsq_nn : 0 ≤ δ ^ 2 := by positivity
  have h_δη_plus_δsq_nn : 0 ≤ δ * η + δ ^ 2 := by positivity
  -- Identities turning `g' · h' · g'⁻¹ - 1` into `g' · (h'-1) · g'⁻¹`:
  have h_g'_mul : g' * g'⁻¹ = 1 := Matrix.mul_nonsing_inv g' hg'_det
  have h_h'_mul : h' * h'⁻¹ = 1 := Matrix.mul_nonsing_inv h' hh'_det
  have h_ghg_eq : g' * h' * g'⁻¹ - 1 = g' * (h' - 1) * g'⁻¹ := by
    have : g' * h' * g'⁻¹ - g' * g'⁻¹ = g' * (h' - 1) * g'⁻¹ := by noncomm_ring
    rw [h_g'_mul] at this; exact this
  have h_hgh_eq : h' * g'⁻¹ * h'⁻¹ - 1 = h' * (g'⁻¹ - 1) * h'⁻¹ := by
    have : h' * g'⁻¹ * h'⁻¹ - h' * h'⁻¹ = h' * (g'⁻¹ - 1) * h'⁻¹ := by noncomm_ring
    rw [h_h'_mul] at this; exact this
  -- Bound `‖h' - 1‖ ≤ η + δ` via triangle.
  have h_h'_near : ‖h' - 1‖ ≤ η + δ := by
    have : h' - 1 = (h' - h) + (h - 1) := by abel
    calc ‖h' - 1‖ = ‖(h' - h) + (h - 1)‖ := by rw [this]
      _ ≤ ‖h' - h‖ + ‖h - 1‖ := norm_add_le _ _
      _ ≤ δ + η := add_le_add h_h_diff h_h_near_id
      _ = η + δ := by ring
  -- Bound `‖g'⁻¹ - 1‖ ≤ η + M²·δ` via inv-diff identity.
  -- We have: g'⁻¹ - 1 = (g'⁻¹ - g⁻¹) + (g⁻¹ - 1).
  -- ‖g'⁻¹ - g⁻¹‖ ≤ M²·δ via `matrix_inv_diff_norm_le`.
  have h_g'_inv_near : ‖g'⁻¹ - 1‖ ≤ η + M ^ 2 * δ := by
    have h_inv_diff_bound : ‖g'⁻¹ - g⁻¹‖ ≤ M ^ 2 * δ :=
      SKEFTHawking.FKLW.GroupCommutator.matrix_inv_diff_norm_le
        g g' hg_det hg'_det M hM_nn h_g_inv_norm h_g'_inv_norm δ hδ_nn h_g_diff
    have : g'⁻¹ - 1 = (g'⁻¹ - g⁻¹) + (g⁻¹ - 1) := by abel
    calc ‖g'⁻¹ - 1‖ = ‖(g'⁻¹ - g⁻¹) + (g⁻¹ - 1)‖ := by rw [this]
      _ ≤ ‖g'⁻¹ - g⁻¹‖ + ‖g⁻¹ - 1‖ := norm_add_le _ _
      _ ≤ M ^ 2 * δ + η := add_le_add h_inv_diff_bound h_g_inv_near_id
      _ = η + M ^ 2 * δ := by ring
  -- Bound `‖g' · h' · g'⁻¹ - 1‖ ≤ M² · (η + δ)`:
  have h_ghg_norm : ‖g' * h' * g'⁻¹ - 1‖ ≤ M ^ 2 * (η + δ) := by
    rw [h_ghg_eq]
    calc ‖g' * (h' - 1) * g'⁻¹‖
        ≤ ‖g' * (h' - 1)‖ * ‖g'⁻¹‖ := norm_mul_le _ _
      _ ≤ (‖g'‖ * ‖h' - 1‖) * ‖g'⁻¹‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ (M * ‖h' - 1‖) * M := by
          have h_a : ‖g'‖ * ‖h' - 1‖ ≤ M * ‖h' - 1‖ :=
            mul_le_mul_of_nonneg_right h_g'_norm (norm_nonneg _)
          exact mul_le_mul h_a h_g'_inv_norm (norm_nonneg _) (by positivity)
      _ ≤ (M * (η + δ)) * M :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h_h'_near hM_nn) hM_nn
      _ = M ^ 2 * (η + δ) := by ring
  -- Bound `‖h' · g'⁻¹ · h'⁻¹ - 1‖ ≤ M² · (η + M²·δ)`:
  have h_hgh_norm : ‖h' * g'⁻¹ * h'⁻¹ - 1‖ ≤ M ^ 2 * (η + M ^ 2 * δ) := by
    rw [h_hgh_eq]
    calc ‖h' * (g'⁻¹ - 1) * h'⁻¹‖
        ≤ ‖h' * (g'⁻¹ - 1)‖ * ‖h'⁻¹‖ := norm_mul_le _ _
      _ ≤ (‖h'‖ * ‖g'⁻¹ - 1‖) * ‖h'⁻¹‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ (M * ‖g'⁻¹ - 1‖) * M := by
          have h_a : ‖h'‖ * ‖g'⁻¹ - 1‖ ≤ M * ‖g'⁻¹ - 1‖ :=
            mul_le_mul_of_nonneg_right h_h'_norm (norm_nonneg _)
          exact mul_le_mul h_a h_h'_inv_norm (norm_nonneg _) (by positivity)
      _ ≤ (M * (η + M ^ 2 * δ)) * M :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h_g'_inv_near hM_nn) hM_nn
      _ = M ^ 2 * (η + M ^ 2 * δ) := by ring
  -- Step 4: Bound ‖A‖ ≤ M²·(δ·η + M²·(η+δ)·δ).
  set P : Matrix (Fin d) (Fin d) ℂ :=
    (g' - g) * (h - 1) - (g' * h' * g'⁻¹ - 1) * (g' - g) with hP_def
  have h_P_norm : ‖P‖ ≤ δ * η + M ^ 2 * (η + δ) * δ := by
    have h1 : ‖(g' - g) * (h - 1)‖ ≤ δ * η := by
      calc ‖(g' - g) * (h - 1)‖
          ≤ ‖g' - g‖ * ‖h - 1‖ := norm_mul_le _ _
        _ ≤ δ * η := mul_le_mul h_g_diff h_h_near_id (norm_nonneg _) hδ_nn
    have h2 : ‖(g' * h' * g'⁻¹ - 1) * (g' - g)‖ ≤ M ^ 2 * (η + δ) * δ := by
      calc ‖(g' * h' * g'⁻¹ - 1) * (g' - g)‖
          ≤ ‖g' * h' * g'⁻¹ - 1‖ * ‖g' - g‖ := norm_mul_le _ _
        _ ≤ M ^ 2 * (η + δ) * δ :=
            mul_le_mul h_ghg_norm h_g_diff (norm_nonneg _) (by positivity)
    calc ‖P‖ = ‖(g' - g) * (h - 1) - (g' * h' * g'⁻¹ - 1) * (g' - g)‖ := rfl
      _ ≤ ‖(g' - g) * (h - 1)‖ + ‖(g' * h' * g'⁻¹ - 1) * (g' - g)‖ := norm_sub_le _ _
      _ ≤ δ * η + M ^ 2 * (η + δ) * δ := add_le_add h1 h2
  -- Bound ‖A‖ where A = P · (g⁻¹ · h⁻¹).
  have h_gh_inv_norm : ‖g⁻¹ * h⁻¹‖ ≤ M ^ 2 := by
    calc ‖g⁻¹ * h⁻¹‖
        ≤ ‖g⁻¹‖ * ‖h⁻¹‖ := norm_mul_le _ _
      _ ≤ M * M := mul_le_mul h_g_inv_norm h_h_inv_norm (norm_nonneg _) hM_nn
      _ = M ^ 2 := by ring
  have h_A_norm : ‖P * (g⁻¹ * h⁻¹)‖ ≤ (M ^ 2 + M ^ 4) * δ * η + M ^ 4 * δ ^ 2 := by
    have h_P_nn : 0 ≤ δ * η + M ^ 2 * (η + δ) * δ := by positivity
    have h_pre : ‖P * (g⁻¹ * h⁻¹)‖ ≤ (δ * η + M ^ 2 * (η + δ) * δ) * M ^ 2 := by
      calc ‖P * (g⁻¹ * h⁻¹)‖
          ≤ ‖P‖ * ‖g⁻¹ * h⁻¹‖ := norm_mul_le _ _
        _ ≤ (δ * η + M ^ 2 * (η + δ) * δ) * M ^ 2 :=
            mul_le_mul h_P_norm h_gh_inv_norm (norm_nonneg _) h_P_nn
    have h_eq : (δ * η + M ^ 2 * (η + δ) * δ) * M ^ 2 =
                (M ^ 2 + M ^ 4) * δ * η + M ^ 4 * δ ^ 2 := by ring
    linarith
  -- Step 5: Bound ‖B‖ symmetrically.
  set Q : Matrix (Fin d) (Fin d) ℂ :=
    (h' - h) * (g⁻¹ - 1) - (h' * g'⁻¹ * h'⁻¹ - 1) * (h' - h) with hQ_def
  have h_Q_norm : ‖Q‖ ≤ δ * η + M ^ 2 * (η + M ^ 2 * δ) * δ := by
    have h1 : ‖(h' - h) * (g⁻¹ - 1)‖ ≤ δ * η := by
      calc ‖(h' - h) * (g⁻¹ - 1)‖
          ≤ ‖h' - h‖ * ‖g⁻¹ - 1‖ := norm_mul_le _ _
        _ ≤ δ * η := mul_le_mul h_h_diff h_g_inv_near_id (norm_nonneg _) hδ_nn
    have h2 : ‖(h' * g'⁻¹ * h'⁻¹ - 1) * (h' - h)‖ ≤ M ^ 2 * (η + M ^ 2 * δ) * δ := by
      calc ‖(h' * g'⁻¹ * h'⁻¹ - 1) * (h' - h)‖
          ≤ ‖h' * g'⁻¹ * h'⁻¹ - 1‖ * ‖h' - h‖ := norm_mul_le _ _
        _ ≤ M ^ 2 * (η + M ^ 2 * δ) * δ :=
            mul_le_mul h_hgh_norm h_h_diff (norm_nonneg _) (by positivity)
    calc ‖Q‖ = ‖(h' - h) * (g⁻¹ - 1) - (h' * g'⁻¹ * h'⁻¹ - 1) * (h' - h)‖ := rfl
      _ ≤ ‖(h' - h) * (g⁻¹ - 1)‖ + ‖(h' * g'⁻¹ * h'⁻¹ - 1) * (h' - h)‖ :=
          norm_sub_le _ _
      _ ≤ δ * η + M ^ 2 * (η + M ^ 2 * δ) * δ := add_le_add h1 h2
  -- ‖g' · Q · h⁻¹‖ bound. Note: this is ≤ ‖g'‖·‖Q‖·‖h⁻¹‖ ≤ M²·‖Q‖.
  -- Bound: M²·(δη + M²·(η+M²·δ)·δ) = M²·δ·η + M⁴·δ·η + M⁶·δ²
  --       = (M² + M⁴)·δ·η + M⁶·δ²
  have h_B_norm : ‖g' * Q * h⁻¹‖ ≤ (M ^ 2 + M ^ 4) * δ * η + M ^ 6 * δ ^ 2 := by
    have h_Q_nn : 0 ≤ δ * η + M ^ 2 * (η + M ^ 2 * δ) * δ := by positivity
    have h_pre : ‖g' * Q * h⁻¹‖ ≤ M * ‖Q‖ * M := by
      calc ‖g' * Q * h⁻¹‖
          ≤ ‖g' * Q‖ * ‖h⁻¹‖ := norm_mul_le _ _
        _ ≤ (‖g'‖ * ‖Q‖) * ‖h⁻¹‖ :=
            mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
        _ ≤ (M * ‖Q‖) * M := by
            have h_a : ‖g'‖ * ‖Q‖ ≤ M * ‖Q‖ :=
              mul_le_mul_of_nonneg_right h_g'_norm (norm_nonneg _)
            exact mul_le_mul h_a h_h_inv_norm (norm_nonneg _) (by positivity)
    have h_pre2 : M * ‖Q‖ * M ≤ M * (δ * η + M ^ 2 * (η + M ^ 2 * δ) * δ) * M := by
      have h_step1 : M * ‖Q‖ ≤ M * (δ * η + M ^ 2 * (η + M ^ 2 * δ) * δ) :=
        mul_le_mul_of_nonneg_left h_Q_norm hM_nn
      exact mul_le_mul_of_nonneg_right h_step1 hM_nn
    have h_eq : M * (δ * η + M ^ 2 * (η + M ^ 2 * δ) * δ) * M =
                (M ^ 2 + M ^ 4) * δ * η + M ^ 6 * δ ^ 2 := by ring
    linarith
  -- Step 6: Compose ‖A + B‖ ≤ ‖A‖ + ‖B‖
  -- ≤ ((M²+M⁴)·δ·η + M⁴·δ²) + ((M²+M⁴)·δ·η + M⁶·δ²)
  -- = 2·(M²+M⁴)·δ·η + (M⁴+M⁶)·δ²
  have h_tri : ‖P * (g⁻¹ * h⁻¹) + g' * Q * h⁻¹‖ ≤
               ‖P * (g⁻¹ * h⁻¹)‖ + ‖g' * Q * h⁻¹‖ := norm_add_le _ _
  linarith

/-! ## 3. Linear matrix-log Lipschitz bound (su2Log)

For the DN recursion's matrix-log step, we need a quantitative bound on
`‖su2Log h‖` in terms of `‖h - 1‖` for `h` near `1`. The IFT-derived
`su2Log_hasStrictFDerivAt_one` gives that `su2Log` has identity strict
Fréchet derivative at `1`; by `HasStrictFDerivAt.exists_lipschitzOnWith_of_nnnorm_lt`
this implies a local `K`-Lipschitz bound for any `K > 1`. With `K = 2`
and the fact `su2Log 1 = 0`, we get `‖su2Log h‖ ≤ 2·‖h - 1‖` on a
neighborhood of `1`. -/

open SKEFTHawking.FKLW.OneParameterSubgroupSU2

/-- **Linear matrix-log Lipschitz bound (Iteration 2 substrate)**:
there is a neighborhood `W` of `1` in `Matrix (Fin 2) (Fin 2) ℂ` (a subset
of `expAmbientPartialHomeo.target`) such that for all `h ∈ W`,
`‖su2Log h‖ ≤ 2·‖h - 1‖`.

The Lipschitz constant `2` is conservative (any constant `> 1` works);
chosen for simplicity. Used in `skApprox_exists` (next sub-ship) to bound
`‖H‖ = ‖su2Log Δ‖` linearly in the residual `‖Δ - 1‖ ≤ ε_n`, which makes
the balanced-commutator step's `‖F‖, ‖G‖ ≤ √(‖H‖/2)` ≤ √ε_n bound work. -/
theorem su2Log_local_lipschitz_bound :
    ∃ W ∈ nhds (1 : Matrix (Fin 2) (Fin 2) ℂ),
      W ⊆ expAmbientPartialHomeo.target ∧
      ∀ h ∈ W, ‖su2Log h‖ ≤ 2 * ‖h - 1‖ := by
  -- Step 1: get the IFT-Lipschitz substrate from Mathlib.
  have h_id_norm :
      ‖ContinuousLinearMap.id ℝ (Matrix (Fin 2) (Fin 2) ℂ)‖₊ ≤ 1 :=
    ContinuousLinearMap.norm_id_le
  have h_id_lt :
      ‖ContinuousLinearMap.id ℝ (Matrix (Fin 2) (Fin 2) ℂ)‖₊ < (2 : NNReal) :=
    lt_of_le_of_lt h_id_norm (by norm_num)
  obtain ⟨s, hs_mem_nhds, hs_lip⟩ :=
    su2Log_hasStrictFDerivAt_one.exists_lipschitzOnWith_of_nnnorm_lt 2 h_id_lt
  -- Step 2: shrink `s` to its intersection with `expAmbientPartialHomeo.target`.
  refine ⟨s ∩ expAmbientPartialHomeo.target,
          Filter.inter_mem hs_mem_nhds expAmbientPartialHomeo_target_mem_nhds_one,
          Set.inter_subset_right, ?_⟩
  intro h hh
  obtain ⟨hs, _⟩ := hh
  -- Step 3: use the LipschitzOnWith norm-sub form to get the bound.
  have h_one_in_s : (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ s := mem_of_mem_nhds hs_mem_nhds
  have h_su2Log_1 : su2Log (1 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := su2Log_one
  -- `LipschitzOnWith.norm_sub_le_of_le` is the additive-group dist→norm conversion.
  have h_norm_sub : ‖su2Log h - su2Log 1‖ ≤ (2 : NNReal) * ‖h - 1‖ :=
    hs_lip.norm_sub_le_of_le hs h_one_in_s (le_refl _)
  rw [h_su2Log_1, sub_zero] at h_norm_sub
  -- Cast (2 : NNReal) → (2 : ℝ).
  have h_cast : ((2 : NNReal) : ℝ) = 2 := by norm_num
  rw [h_cast] at h_norm_sub
  exact h_norm_sub

end SKEFTHawking.FKLW.GroupCommutatorNearIdentity

/-! ## 4. Module summary

GroupCommutatorNearIdentity.lean (Phase 6t Iteration 2 substrate, 2026-05-22 PM):
**Near-identity-sharpened group commutator stability — algebraic identities**.

  *Algebraic identities (foundational substrate):*
  - `T₁_plus_T₃_factor` — exposes near-I cancellation between
    `(g'-g)·h·g⁻¹·h⁻¹` and `g'·h'·(g'⁻¹-g⁻¹)·h⁻¹`.
  - `T₂_plus_T₄_factor` — symmetric for the h-perturbation pair.

  *Headline:*
  - `groupCommutator_stability_nearIdentity` — norm bound
    `‖[g',h'] - [g,h]‖ ≤ 2·(M² + M⁴)·δ·η + (M⁴ + M⁶)·δ²`. Standard-kernel-only
    via `lean_verify` (axioms: `[propext, Classical.choice, Quot.sound]`).

  *Linear matrix-log substrate (sub-ship 2):*
  - `su2Log_local_lipschitz_bound` — on a neighborhood of `1`,
    `‖su2Log h‖ ≤ 2·‖h - 1‖`. Composes `su2Log_hasStrictFDerivAt_one`
    with Mathlib's `HasStrictFDerivAt.exists_lipschitzOnWith_of_nnnorm_lt`.
    Standard-kernel-only.

  *Pipeline Invariant compliance:*
  - Invariant #10 (no `maxHeartbeats`): RESPECTED
  - Invariant #15 (no new axioms): RESPECTED

Zero new project-local axioms. Pre-Phase-6t axiom count UNCHANGED. -/
