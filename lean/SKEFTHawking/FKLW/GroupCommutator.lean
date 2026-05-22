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

end SKEFTHawking.FKLW.GroupCommutator

/-! ## 6. Module summary

GroupCommutator.lean (Phase 6t Wave 1 SHIP, 2026-05-22 PM):
**Group-commutator substrate for the Dawson-Nielsen Solovay-Kitaev recursion**.

  *Definitions:*
  - `groupCommutator g h := g * h * g⁻¹ * h⁻¹`

  *Bridge lemmas:*
  - `exp_smul_I_inv` — `(exp(iF))⁻¹ = exp(-iF)`
  - `groupCommutator_exp_eq` — bridge to the BCH 4-fold product
  - `groupCommutator_telescope` — 4-term algebraic decomposition for stability

  *Headline theorems (3 total):*
  - **`groupCommutator_norm_le_quadratic`** — quadratic shrinkage `≤ 338·δ²`
  - **`groupCommutator_lie_bracket_cubic_remainder`** — cubic linearization `≤ 320·δ³`
  - **`groupCommutator_stability`** — perturbation bound `≤ 4·M³·ε`

  *Pipeline Invariant compliance:*
  - Invariant #10 (no `maxHeartbeats`): RESPECTED
  - Invariant #15 (no new axioms): RESPECTED

Zero new project-local axioms. Pre-Phase-6t axiom count UNCHANGED. -/
