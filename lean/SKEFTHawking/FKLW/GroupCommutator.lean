/-
SK_EFT_Hawking Phase 6t Wave 1 SHIP (2026-05-22 PM):
**Group-commutator substrate for the Solovay-Kitaev recursion (Dawson-Nielsen 2006)**.

This module ships the abstract group-commutator definition `groupCommutator g h`
and the three load-bearing operator-norm estimates consumed by the Solovay-Kitaev
recursion: quadratic shrinkage, cubic Lie-bracket linearization, and stability
under perturbation.

The three headlines are direct compositions of the substrate already shipped
under Phase 6p Wave 2d.2 in `SKEFTHawking.MatrixBCHCubic`:
  - `bch_group_commutator_quadratic_shrinkage` → `groupCommutator_norm_le_quadratic`
  - `bch_order_2_cubic_thm` → `groupCommutator_lie_bracket_cubic_remainder`
  - submultiplicativity + 4-term telescoping → `groupCommutator_stability`

## Phase 6t roadmap alignment

  - Wave 1 (this module) → consumed by Wave 2 (balanced commutator) for the
    `[A, B] = V` decomposition's group-commutator identity, by Wave 4 (recursion)
    for per-step shrinkage in the recursion step, and by Wave 7 (applications)
    for the worked-example correctness statements.

## Pipeline Invariant compliance

  - Invariant #10 (no `maxHeartbeats`): RESPECTED.
  - Invariant #15 (no new axioms): RESPECTED.

Primary source: Dawson & Nielsen, *Quantum Info. & Comp.* 6 (2006), 81–95;
                arXiv:quant-ph/0505030.
-/

import Mathlib
import SKEFTHawking.MatrixBCHCubic

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GroupCommutator

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

open Matrix MatrixBCHCubic NormedSpace

/-! ## 1. Abstract definition

The group commutator `g·h·g⁻¹·h⁻¹` on matrices. For invertible `g, h` this is
the standard group commutator; the Solovay-Kitaev recursion uses this on
unitary `(g, h) ∈ U(d) × U(d)`, where invertibility is automatic. -/

/-- The group commutator `g·h·g⁻¹·h⁻¹` on matrices. -/
noncomputable def groupCommutator {d : ℕ} (g h : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  g * h * g⁻¹ * h⁻¹

/-- The group-commutator unfolding. -/
lemma groupCommutator_eq {d : ℕ} (g h : Matrix (Fin d) (Fin d) ℂ) :
    groupCommutator g h = g * h * g⁻¹ * h⁻¹ := rfl

/-! ## 2. Bridge: matrix-inverse of `exp(iF)` is `exp(-iF)`

`(exp(iF))⁻¹ = exp(-iF)` via `Matrix.nonsing_inv_eq_ringInverse` +
`Ring.inverse_exp` (Mathlib's exponential inversion theorem in the ring-inverse
form). -/

/-- `(NormedSpace.exp(iF))⁻¹ = NormedSpace.exp(-iF)` for matrices, via
`Matrix.nonsing_inv_eq_ringInverse` + `Ring.inverse_exp`. -/
lemma exp_smul_I_inv {d : ℕ} (F : Matrix (Fin d) (Fin d) ℂ) :
    (NormedSpace.exp (Complex.I • F))⁻¹ = NormedSpace.exp (-(Complex.I • F)) := by
  rw [Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_exp]

/-- The group commutator on exp form unfolds to the BCH 4-fold product. -/
lemma groupCommutator_exp_eq {d : ℕ} (F G : Matrix (Fin d) (Fin d) ℂ) :
    groupCommutator (NormedSpace.exp (Complex.I • F)) (NormedSpace.exp (Complex.I • G)) =
    NormedSpace.exp (Complex.I • F) * NormedSpace.exp (Complex.I • G) *
    NormedSpace.exp (-(Complex.I • F)) * NormedSpace.exp (-(Complex.I • G)) := by
  unfold groupCommutator
  rw [exp_smul_I_inv F, exp_smul_I_inv G]

/-! ## 3. Headline 1 — quadratic shrinkage of the group commutator

`‖groupCommutator(exp(iF), exp(iG)) - 1‖ ≤ 338·δ²` for `‖F‖, ‖G‖ ≤ δ ≤ 1`. -/

/-- **HEADLINE 1 (Phase 6t Wave 1)**: quadratic shrinkage of the group commutator
in exp coordinates.

For `F, G : Matrix (Fin d) (Fin d) ℂ` with `‖F‖, ‖G‖ ≤ δ ≤ 1`:

  `‖groupCommutator(exp(iF), exp(iG)) - 1‖ ≤ 338·δ²`.

This is the Dawson-Nielsen quadratic-shrinkage estimate: starting from "scale δ"
Lie-algebra elements, the group commutator at the matrix-group level is at
"scale δ²". Iterating this estimate drives the Solovay-Kitaev recursion's
super-quadratic convergence. -/
theorem groupCommutator_norm_le_quadratic
    {d : ℕ} [Nonempty (Fin d)]
    (δ : ℝ) (hδ_nn : 0 ≤ δ) (hδ_le_one : δ ≤ 1)
    (F G : Matrix (Fin d) (Fin d) ℂ) (hF : ‖F‖ ≤ δ) (hG : ‖G‖ ≤ δ) :
    ‖groupCommutator (NormedSpace.exp (Complex.I • F))
        (NormedSpace.exp (Complex.I • G)) - 1‖ ≤ 338 * δ ^ 2 := by
  rw [groupCommutator_exp_eq]
  exact bch_group_commutator_quadratic_shrinkage δ hδ_nn hδ_le_one F G hF hG

/-! ## 4. Headline 2 — cubic Lie-bracket linearization remainder

`‖groupCommutator(exp(iF), exp(iG)) - exp(-⁅F,G⁆)‖ ≤ 320·δ³` for
`‖F‖, ‖G‖ ≤ δ ≤ 1`. -/

/-- **HEADLINE 2 (Phase 6t Wave 1)**: cubic Lie-bracket linearization remainder
of the group commutator in exp coordinates.

For `F, G : Matrix (Fin d) (Fin d) ℂ` with `‖F‖, ‖G‖ ≤ δ ≤ 1`:

  `‖groupCommutator(exp(iF), exp(iG)) - exp(-⁅F, G⁆)‖ ≤ 320·δ³`.

This is the cubic-remainder content of the BCH series: the group commutator's
leading-order direction is `exp(-⁅F, G⁆)`, with cubic error in δ. -/
theorem groupCommutator_lie_bracket_cubic_remainder
    {d : ℕ} [Nonempty (Fin d)]
    (δ : ℝ) (hδ_nn : 0 ≤ δ) (hδ_le_one : δ ≤ 1)
    (F G : Matrix (Fin d) (Fin d) ℂ) (hF : ‖F‖ ≤ δ) (hG : ‖G‖ ≤ δ) :
    ‖groupCommutator (NormedSpace.exp (Complex.I • F))
        (NormedSpace.exp (Complex.I • G)) -
        NormedSpace.exp (-⁅F, G⁆)‖ ≤ 320 * δ ^ 3 := by
  rw [groupCommutator_exp_eq]
  exact bch_order_2_cubic_thm δ hδ_nn hδ_le_one F G hF hG

/-! ## 5. Headline 3 — stability of the group commutator under perturbation

The four-term telescoping decomposition

  `[g',h'] - [g,h] = (g'-g)·h·g⁻¹·h⁻¹ + g'·(h'-h)·g⁻¹·h⁻¹`
                      `+ g'·h'·(g'⁻¹-g⁻¹)·h⁻¹ + g'·h'·g'⁻¹·(h'⁻¹-h⁻¹)`

followed by submultiplicativity gives a clean perturbation bound parameterized
by an upper bound `M` on the eight operator norms involved. -/

/-- The four-term telescoping decomposition of `[g', h'] - [g, h]`. Pure
algebraic identity, no hypotheses. -/
lemma groupCommutator_telescope
    {d : ℕ} (g h g' h' : Matrix (Fin d) (Fin d) ℂ) :
    groupCommutator g' h' - groupCommutator g h =
      ((g' - g) * h * g⁻¹ * h⁻¹)
        + (g' * (h' - h) * g⁻¹ * h⁻¹)
        + (g' * h' * (g'⁻¹ - g⁻¹) * h⁻¹)
        + (g' * h' * g'⁻¹ * (h'⁻¹ - h⁻¹)) := by
  unfold groupCommutator
  noncomm_ring

/-- **HEADLINE 3 (Phase 6t Wave 1)**: stability of the group commutator under
perturbation, parameterized by uniform upper bounds on all the relevant norms.

Given matrices `g, h, g', h' : Matrix (Fin d) (Fin d) ℂ` with uniform bound `M`
on operator norms and bounds `‖g' - g‖, ‖h' - h‖, ‖g'⁻¹ - g⁻¹‖, ‖h'⁻¹ - h⁻¹‖ ≤ ε`:

  `‖groupCommutator g' h' - groupCommutator g h‖ ≤ 4·M³·ε`.

For the Solovay-Kitaev application this is consumed in the unitary specialization
where `M = √d` (for `d × d` unitary matrices) and the inverse-difference bounds
reduce to direct-difference bounds (`‖U⁻¹ - V⁻¹‖ = ‖U - V‖` for unitaries via
the adjoint isometry). -/
theorem groupCommutator_stability
    {d : ℕ} (g h g' h' : Matrix (Fin d) (Fin d) ℂ)
    (ε M : ℝ)
    (hM_nn : 0 ≤ M)
    (h_h_norm : ‖h‖ ≤ M)
    (h_g'_norm : ‖g'‖ ≤ M) (h_h'_norm : ‖h'‖ ≤ M)
    (h_g_inv_norm : ‖g⁻¹‖ ≤ M) (h_h_inv_norm : ‖h⁻¹‖ ≤ M)
    (h_g'_inv_norm : ‖g'⁻¹‖ ≤ M)
    (h_g_diff : ‖g' - g‖ ≤ ε) (h_h_diff : ‖h' - h‖ ≤ ε)
    (h_g_inv_diff : ‖g'⁻¹ - g⁻¹‖ ≤ ε) (h_h_inv_diff : ‖h'⁻¹ - h⁻¹‖ ≤ ε)
    (hε_nn : 0 ≤ ε) :
    ‖groupCommutator g' h' - groupCommutator g h‖ ≤ 4 * M ^ 3 * ε := by
  rw [groupCommutator_telescope]
  -- The 4 terms each bounded by M³·ε.
  have hM2_nn : 0 ≤ M ^ 2 := by positivity
  have hM3_nn : 0 ≤ M ^ 3 := by positivity
  -- Norm-nonneg helpers.
  have h_h_nn : 0 ≤ ‖h‖ := norm_nonneg _
  have h_g'_nn : 0 ≤ ‖g'‖ := norm_nonneg _
  have h_h'_nn : 0 ≤ ‖h'‖ := norm_nonneg _
  have h_g_inv_nn : 0 ≤ ‖g⁻¹‖ := norm_nonneg _
  have h_h_inv_nn : 0 ≤ ‖h⁻¹‖ := norm_nonneg _
  have h_g'_inv_nn : 0 ≤ ‖g'⁻¹‖ := norm_nonneg _
  have h_gd_nn : 0 ≤ ‖g' - g‖ := norm_nonneg _
  have h_hd_nn : 0 ≤ ‖h' - h‖ := norm_nonneg _
  have h_gid_nn : 0 ≤ ‖g'⁻¹ - g⁻¹‖ := norm_nonneg _
  have h_hid_nn : 0 ≤ ‖h'⁻¹ - h⁻¹‖ := norm_nonneg _
  -- Triangle inequality on the 4-term sum.
  set T1 := ((g' - g) * h * g⁻¹ * h⁻¹)
  set T2 := (g' * (h' - h) * g⁻¹ * h⁻¹)
  set T3 := (g' * h' * (g'⁻¹ - g⁻¹) * h⁻¹)
  set T4 := (g' * h' * g'⁻¹ * (h'⁻¹ - h⁻¹))
  -- ‖T1‖ ≤ ‖g'-g‖·‖h‖·‖g⁻¹‖·‖h⁻¹‖ ≤ ε·M³
  have h_T1 : ‖T1‖ ≤ ε * M ^ 3 := by
    have h_step1 : ‖T1‖ ≤ ‖g' - g‖ * ‖h‖ * ‖g⁻¹‖ * ‖h⁻¹‖ := by
      calc ‖T1‖
          = ‖(g' - g) * h * g⁻¹ * h⁻¹‖ := rfl
        _ ≤ ‖(g' - g) * h * g⁻¹‖ * ‖h⁻¹‖ := norm_mul_le _ _
        _ ≤ (‖(g' - g) * h‖ * ‖g⁻¹‖) * ‖h⁻¹‖ :=
            mul_le_mul_of_nonneg_right (norm_mul_le _ _) h_h_inv_nn
        _ ≤ ((‖g' - g‖ * ‖h‖) * ‖g⁻¹‖) * ‖h⁻¹‖ := by
            have h2 : ‖(g' - g) * h‖ * ‖g⁻¹‖ ≤ ‖g' - g‖ * ‖h‖ * ‖g⁻¹‖ :=
              mul_le_mul_of_nonneg_right (norm_mul_le _ _) h_g_inv_nn
            exact mul_le_mul_of_nonneg_right h2 h_h_inv_nn
        _ = ‖g' - g‖ * ‖h‖ * ‖g⁻¹‖ * ‖h⁻¹‖ := by ring
    -- Chain the bounds: ε·M·M·M = ε·M³
    have h_a : ‖g' - g‖ * ‖h‖ ≤ ε * M :=
      mul_le_mul h_g_diff h_h_norm h_h_nn hε_nn
    have h_εM_nn : 0 ≤ ε * M := by positivity
    have h_b : ‖g' - g‖ * ‖h‖ * ‖g⁻¹‖ ≤ ε * M * M :=
      mul_le_mul h_a h_g_inv_norm h_g_inv_nn h_εM_nn
    have h_εMM_nn : 0 ≤ ε * M * M := by positivity
    have h_c : ‖g' - g‖ * ‖h‖ * ‖g⁻¹‖ * ‖h⁻¹‖ ≤ ε * M * M * M :=
      mul_le_mul h_b h_h_inv_norm h_h_inv_nn h_εMM_nn
    have h_eq : ε * M * M * M = ε * M ^ 3 := by ring
    linarith
  -- ‖T2‖ ≤ ‖g'‖·‖h'-h‖·‖g⁻¹‖·‖h⁻¹‖ ≤ M·ε·M·M = ε·M³
  have h_T2 : ‖T2‖ ≤ ε * M ^ 3 := by
    have h_step1 : ‖T2‖ ≤ ‖g'‖ * ‖h' - h‖ * ‖g⁻¹‖ * ‖h⁻¹‖ := by
      calc ‖T2‖
          = ‖g' * (h' - h) * g⁻¹ * h⁻¹‖ := rfl
        _ ≤ ‖g' * (h' - h) * g⁻¹‖ * ‖h⁻¹‖ := norm_mul_le _ _
        _ ≤ (‖g' * (h' - h)‖ * ‖g⁻¹‖) * ‖h⁻¹‖ :=
            mul_le_mul_of_nonneg_right (norm_mul_le _ _) h_h_inv_nn
        _ ≤ ((‖g'‖ * ‖h' - h‖) * ‖g⁻¹‖) * ‖h⁻¹‖ := by
            have h2 : ‖g' * (h' - h)‖ * ‖g⁻¹‖ ≤ ‖g'‖ * ‖h' - h‖ * ‖g⁻¹‖ :=
              mul_le_mul_of_nonneg_right (norm_mul_le _ _) h_g_inv_nn
            exact mul_le_mul_of_nonneg_right h2 h_h_inv_nn
        _ = ‖g'‖ * ‖h' - h‖ * ‖g⁻¹‖ * ‖h⁻¹‖ := by ring
    have h_a : ‖g'‖ * ‖h' - h‖ ≤ M * ε :=
      mul_le_mul h_g'_norm h_h_diff h_hd_nn hM_nn
    have h_Mε_nn : 0 ≤ M * ε := by positivity
    have h_b : ‖g'‖ * ‖h' - h‖ * ‖g⁻¹‖ ≤ M * ε * M :=
      mul_le_mul h_a h_g_inv_norm h_g_inv_nn h_Mε_nn
    have h_MεM_nn : 0 ≤ M * ε * M := by positivity
    have h_c : ‖g'‖ * ‖h' - h‖ * ‖g⁻¹‖ * ‖h⁻¹‖ ≤ M * ε * M * M :=
      mul_le_mul h_b h_h_inv_norm h_h_inv_nn h_MεM_nn
    have h_eq : M * ε * M * M = ε * M ^ 3 := by ring
    linarith
  -- ‖T3‖ ≤ ‖g'‖·‖h'‖·‖g'⁻¹-g⁻¹‖·‖h⁻¹‖ ≤ M·M·ε·M = ε·M³
  have h_T3 : ‖T3‖ ≤ ε * M ^ 3 := by
    have h_step1 : ‖T3‖ ≤ ‖g'‖ * ‖h'‖ * ‖g'⁻¹ - g⁻¹‖ * ‖h⁻¹‖ := by
      calc ‖T3‖
          = ‖g' * h' * (g'⁻¹ - g⁻¹) * h⁻¹‖ := rfl
        _ ≤ ‖g' * h' * (g'⁻¹ - g⁻¹)‖ * ‖h⁻¹‖ := norm_mul_le _ _
        _ ≤ (‖g' * h'‖ * ‖g'⁻¹ - g⁻¹‖) * ‖h⁻¹‖ :=
            mul_le_mul_of_nonneg_right (norm_mul_le _ _) h_h_inv_nn
        _ ≤ ((‖g'‖ * ‖h'‖) * ‖g'⁻¹ - g⁻¹‖) * ‖h⁻¹‖ := by
            have h2 : ‖g' * h'‖ * ‖g'⁻¹ - g⁻¹‖ ≤ ‖g'‖ * ‖h'‖ * ‖g'⁻¹ - g⁻¹‖ :=
              mul_le_mul_of_nonneg_right (norm_mul_le _ _) h_gid_nn
            exact mul_le_mul_of_nonneg_right h2 h_h_inv_nn
        _ = ‖g'‖ * ‖h'‖ * ‖g'⁻¹ - g⁻¹‖ * ‖h⁻¹‖ := by ring
    have h_a : ‖g'‖ * ‖h'‖ ≤ M * M :=
      mul_le_mul h_g'_norm h_h'_norm h_h'_nn hM_nn
    have h_MM_nn : 0 ≤ M * M := by positivity
    have h_b : ‖g'‖ * ‖h'‖ * ‖g'⁻¹ - g⁻¹‖ ≤ M * M * ε :=
      mul_le_mul h_a h_g_inv_diff h_gid_nn h_MM_nn
    have h_MMε_nn : 0 ≤ M * M * ε := by positivity
    have h_c : ‖g'‖ * ‖h'‖ * ‖g'⁻¹ - g⁻¹‖ * ‖h⁻¹‖ ≤ M * M * ε * M :=
      mul_le_mul h_b h_h_inv_norm h_h_inv_nn h_MMε_nn
    have h_eq : M * M * ε * M = ε * M ^ 3 := by ring
    linarith
  -- ‖T4‖ ≤ ‖g'‖·‖h'‖·‖g'⁻¹‖·‖h'⁻¹-h⁻¹‖ ≤ M·M·M·ε = ε·M³
  have h_T4 : ‖T4‖ ≤ ε * M ^ 3 := by
    have h_step1 : ‖T4‖ ≤ ‖g'‖ * ‖h'‖ * ‖g'⁻¹‖ * ‖h'⁻¹ - h⁻¹‖ := by
      calc ‖T4‖
          = ‖g' * h' * g'⁻¹ * (h'⁻¹ - h⁻¹)‖ := rfl
        _ ≤ ‖g' * h' * g'⁻¹‖ * ‖h'⁻¹ - h⁻¹‖ := norm_mul_le _ _
        _ ≤ (‖g' * h'‖ * ‖g'⁻¹‖) * ‖h'⁻¹ - h⁻¹‖ :=
            mul_le_mul_of_nonneg_right (norm_mul_le _ _) h_hid_nn
        _ ≤ ((‖g'‖ * ‖h'‖) * ‖g'⁻¹‖) * ‖h'⁻¹ - h⁻¹‖ := by
            have h2 : ‖g' * h'‖ * ‖g'⁻¹‖ ≤ ‖g'‖ * ‖h'‖ * ‖g'⁻¹‖ :=
              mul_le_mul_of_nonneg_right (norm_mul_le _ _) h_g'_inv_nn
            exact mul_le_mul_of_nonneg_right h2 h_hid_nn
        _ = ‖g'‖ * ‖h'‖ * ‖g'⁻¹‖ * ‖h'⁻¹ - h⁻¹‖ := by ring
    have h_a : ‖g'‖ * ‖h'‖ ≤ M * M :=
      mul_le_mul h_g'_norm h_h'_norm h_h'_nn hM_nn
    have h_MM_nn : 0 ≤ M * M := by positivity
    have h_b : ‖g'‖ * ‖h'‖ * ‖g'⁻¹‖ ≤ M * M * M :=
      mul_le_mul h_a h_g'_inv_norm h_g'_inv_nn h_MM_nn
    have h_MMM_nn : 0 ≤ M * M * M := by positivity
    have h_c : ‖g'‖ * ‖h'‖ * ‖g'⁻¹‖ * ‖h'⁻¹ - h⁻¹‖ ≤ M * M * M * ε :=
      mul_le_mul h_b h_h_inv_diff h_hid_nn h_MMM_nn
    have h_eq : M * M * M * ε = ε * M ^ 3 := by ring
    linarith
  -- Combine: ‖T1 + T2 + T3 + T4‖ ≤ ‖T1‖ + ‖T2‖ + ‖T3‖ + ‖T4‖ ≤ 4·ε·M³
  have h_tri12 : ‖T1 + T2‖ ≤ ‖T1‖ + ‖T2‖ := norm_add_le _ _
  have h_tri123 : ‖T1 + T2 + T3‖ ≤ ‖T1 + T2‖ + ‖T3‖ := norm_add_le _ _
  have h_tri1234 : ‖T1 + T2 + T3 + T4‖ ≤ ‖T1 + T2 + T3‖ + ‖T4‖ := norm_add_le _ _
  have h_eq : 4 * M ^ 3 * ε = ε * M ^ 3 + ε * M ^ 3 + ε * M ^ 3 + ε * M ^ 3 := by ring
  linarith

/-! ## 5b. Matrix-inverse difference bound + invertible-specialized stability
    (Phase 6t Wave 1 strengthening 2026-05-22 PM post-compact)

For invertible matrices `g, g'`, the algebraic identity
`g'⁻¹ - g⁻¹ = g'⁻¹·(g - g')·g⁻¹` (Mathlib's `Matrix.inv_sub_inv`) combined
with operator-norm submultiplicativity yields:
  `‖g'⁻¹ - g⁻¹‖ ≤ ‖g'⁻¹‖ · ‖g - g'‖ · ‖g⁻¹‖ ≤ M · ε · M = M² · ε`.

This drops 2 of the 4 ε-bound hypotheses from `groupCommutator_stability`
when the matrices are invertible, at the cost of the stability constant
going from `4·M³·ε` to `4·M⁵·ε` (for `M ≥ 1`, the typical case for
unitary matrices in `d`-dim SU(d) with `M = √d`).

Note: the original Task #42 framing ("‖U⁻¹ - V⁻¹‖ = ‖U - V‖ via adjoint
isometry") was incorrect for `Matrix.linftyOpNorm` — that's the row-sum
operator norm, NOT the l2 spectral norm. The correct bound (factor of M²,
not equality) is what we ship here. -/

/-- **Matrix-inverse difference bound (Mathlib upstream-PR candidate)**.
For invertible matrices `g, g' : Matrix (Fin d) (Fin d) ℂ`, the difference
of inverses is bounded by the direct difference scaled by the product of
inverse-norms:

  `‖g'⁻¹ - g⁻¹‖ ≤ ‖g'⁻¹‖ · ‖g' - g‖ · ‖g⁻¹‖`.

Specialized to a uniform bound `‖g⁻¹‖, ‖g'⁻¹‖ ≤ M` and `‖g' - g‖ ≤ ε`:

  `‖g'⁻¹ - g⁻¹‖ ≤ M² · ε`. -/
lemma matrix_inv_diff_norm_le
    {d : ℕ} (g g' : Matrix (Fin d) (Fin d) ℂ)
    (hg : IsUnit g.det) (hg' : IsUnit g'.det)
    (M : ℝ) (hM_nn : 0 ≤ M)
    (h_g_inv : ‖g⁻¹‖ ≤ M) (h_g'_inv : ‖g'⁻¹‖ ≤ M)
    (ε : ℝ) (hε_nn : 0 ≤ ε) (h_diff : ‖g' - g‖ ≤ ε) :
    ‖g'⁻¹ - g⁻¹‖ ≤ M ^ 2 * ε := by
  -- Bridge: `IsUnit g ↔ IsUnit g'.det` via `Matrix.isUnit_iff_isUnit_det`.
  have hg_unit : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).mpr hg
  have hg'_unit : IsUnit g' := (Matrix.isUnit_iff_isUnit_det g').mpr hg'
  have h_iff : IsUnit g' ↔ IsUnit g := ⟨fun _ => hg_unit, fun _ => hg'_unit⟩
  -- Algebraic identity from Mathlib:
  have h_id : g'⁻¹ - g⁻¹ = g'⁻¹ * (g - g') * g⁻¹ := Matrix.inv_sub_inv h_iff
  rw [h_id]
  -- Direct-diff sign normalization.
  have h_g_neg : ‖g - g'‖ = ‖g' - g‖ := by
    rw [show g - g' = -(g' - g) from by abel, norm_neg]
  -- Submultiplicativity chain.
  have h_g_inv_nn : 0 ≤ ‖g⁻¹‖ := norm_nonneg _
  have h_g'_inv_nn : 0 ≤ ‖g'⁻¹‖ := norm_nonneg _
  have h_step1 : ‖g'⁻¹ * (g - g') * g⁻¹‖ ≤ ‖g'⁻¹ * (g - g')‖ * ‖g⁻¹‖ :=
    norm_mul_le _ _
  have h_step2 : ‖g'⁻¹ * (g - g')‖ ≤ ‖g'⁻¹‖ * ‖g - g'‖ :=
    norm_mul_le _ _
  have h_step2' : ‖g'⁻¹ * (g - g')‖ ≤ ‖g'⁻¹‖ * ‖g' - g‖ := by
    rw [h_g_neg] at h_step2; exact h_step2
  -- Chain numerical bounds.
  have h_a : ‖g'⁻¹‖ * ‖g' - g‖ ≤ M * ε :=
    mul_le_mul h_g'_inv h_diff (norm_nonneg _) hM_nn
  have h_Mε_nn : 0 ≤ M * ε := by positivity
  have h_b : ‖g'⁻¹ * (g - g')‖ * ‖g⁻¹‖ ≤ M * ε * M := by
    have h_step3 : ‖g'⁻¹ * (g - g')‖ * ‖g⁻¹‖ ≤ (M * ε) * ‖g⁻¹‖ :=
      mul_le_mul_of_nonneg_right (h_step2'.trans h_a) h_g_inv_nn
    have h_step4 : (M * ε) * ‖g⁻¹‖ ≤ M * ε * M :=
      mul_le_mul_of_nonneg_left h_g_inv h_Mε_nn
    linarith
  have h_eq : M * ε * M = M ^ 2 * ε := by ring
  linarith

/-- **HEADLINE 4 (Phase 6t Wave 1 strengthening — invertible-specialized
stability)**: drops 2 of the 4 ε-bound hypotheses from
`groupCommutator_stability` for invertible `g, h, g', h'`.

Given uniform norm bound `M` on all 8 forward + inverse norms,
`M ≥ 1` (typical for unitary matrices), and direct-diff bounds
`‖g' - g‖, ‖h' - h‖ ≤ ε`:

  `‖groupCommutator g' h' - groupCommutator g h‖ ≤ 4 · M⁵ · ε`.

The constant is `M⁵` (instead of `M³` in the generic stability) because the
inverse-difference bounds are derived (not assumed) via
`matrix_inv_diff_norm_le`, giving `‖g'⁻¹ - g⁻¹‖ ≤ M² · ε` per inverse.

For SU(2) (the Solovay-Kitaev application) with `M = √2`, this gives
`‖[g',h'] - [g,h]‖ ≤ 4 · 4√2 · ε ≈ 22.6 · ε`. -/
theorem groupCommutator_stability_invertible
    {d : ℕ} (g h g' h' : Matrix (Fin d) (Fin d) ℂ)
    (ε M : ℝ)
    (hM_nn : 0 ≤ M) (hM_ge_one : 1 ≤ M)
    (h_h_norm : ‖h‖ ≤ M)
    (h_g'_norm : ‖g'‖ ≤ M) (h_h'_norm : ‖h'‖ ≤ M)
    (h_g_inv_norm : ‖g⁻¹‖ ≤ M) (h_h_inv_norm : ‖h⁻¹‖ ≤ M)
    (h_g'_inv_norm : ‖g'⁻¹‖ ≤ M) (h_h'_inv_norm : ‖h'⁻¹‖ ≤ M)
    (hg_det : IsUnit g.det) (hg'_det : IsUnit g'.det)
    (hh_det : IsUnit h.det) (hh'_det : IsUnit h'.det)
    (h_g_diff : ‖g' - g‖ ≤ ε) (h_h_diff : ‖h' - h‖ ≤ ε)
    (hε_nn : 0 ≤ ε) :
    ‖groupCommutator g' h' - groupCommutator g h‖ ≤ 4 * M ^ 5 * ε := by
  -- Derive inverse-difference bounds via `matrix_inv_diff_norm_le`.
  have h_g_inv_diff : ‖g'⁻¹ - g⁻¹‖ ≤ M ^ 2 * ε :=
    matrix_inv_diff_norm_le g g' hg_det hg'_det M hM_nn
      h_g_inv_norm h_g'_inv_norm ε hε_nn h_g_diff
  have h_h_inv_diff : ‖h'⁻¹ - h⁻¹‖ ≤ M ^ 2 * ε :=
    matrix_inv_diff_norm_le h h' hh_det hh'_det M hM_nn
      h_h_inv_norm h_h'_inv_norm ε hε_nn h_h_diff
  -- Apply generic stability with ε' = M² · ε (which is ≥ ε for M ≥ 1).
  have h_M2_nn : 0 ≤ M ^ 2 := by positivity
  have h_M2_ge_one : 1 ≤ M ^ 2 := by nlinarith
  have h_M2_eps : ε ≤ M ^ 2 * ε := by nlinarith
  have h_g_diff' : ‖g' - g‖ ≤ M ^ 2 * ε := le_trans h_g_diff h_M2_eps
  have h_h_diff' : ‖h' - h‖ ≤ M ^ 2 * ε := le_trans h_h_diff h_M2_eps
  have h_M2_eps_nn : 0 ≤ M ^ 2 * ε := by positivity
  have h_stability :=
    groupCommutator_stability g h g' h' (M ^ 2 * ε) M hM_nn h_h_norm
      h_g'_norm h_h'_norm h_g_inv_norm h_h_inv_norm h_g'_inv_norm
      h_g_diff' h_h_diff' h_g_inv_diff h_h_inv_diff h_M2_eps_nn
  -- 4·M³·(M²·ε) = 4·M⁵·ε.
  have h_eq : 4 * M ^ 3 * (M ^ 2 * ε) = 4 * M ^ 5 * ε := by ring
  linarith

end SKEFTHawking.FKLW.GroupCommutator

/-! ## 6. Module summary

GroupCommutator.lean (Phase 6t Wave 1 SHIP 2026-05-22 PM
+ Wave 1 strengthening 2026-05-22 PM post-compact):
**Group-commutator substrate for the Dawson-Nielsen Solovay-Kitaev recursion**.

  *Definitions:*
  - `groupCommutator g h := g * h * g⁻¹ * h⁻¹`

  *Bridge lemmas:*
  - `exp_smul_I_inv` — `(exp(iF))⁻¹ = exp(-iF)`
  - `groupCommutator_exp_eq` — bridge to the BCH 4-fold product
  - `groupCommutator_telescope` — 4-term algebraic decomposition for stability
  - **`matrix_inv_diff_norm_le`** — Mathlib upstream-PR candidate:
    `‖g'⁻¹ - g⁻¹‖ ≤ M² · ε` for invertible `g, g'` with inverse-norms ≤ M
    and direct difference ≤ ε.

  *Headline theorems (4 total):*
  - **`groupCommutator_norm_le_quadratic`** — quadratic shrinkage `≤ 338·δ²`
  - **`groupCommutator_lie_bracket_cubic_remainder`** — cubic linearization `≤ 320·δ³`
  - **`groupCommutator_stability`** — generic perturbation bound `≤ 4·M³·ε`
    (consumes 4 explicit ε-bounds)
  - **`groupCommutator_stability_invertible`** (Wave 1 strengthening) —
    invertible-specialized perturbation bound `≤ 4·M⁵·ε` (consumes only
    2 direct-diff bounds + invertibility hyps; derives inv-diff bounds
    from `matrix_inv_diff_norm_le`)

  *Pipeline Invariant compliance:*
  - Invariant #10 (no `maxHeartbeats`): RESPECTED
  - Invariant #15 (no new axioms): RESPECTED

Zero new project-local axioms. Pre-Phase-6t axiom count UNCHANGED. -/
