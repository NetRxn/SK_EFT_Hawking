/-
SK_EFT_Hawking Phase 6t Path A SHIP (2026-05-22 PM):
**Constructive Dawson-Nielsen Solovay-Kitaev recursion** for the Fibonacci-anyon
braid representation in SU(2).

This module ships the CONSTRUCTIVE variant of the per-step Solovay-Kitaev
refinement: instead of `Classical.choose`-based existence (used by
`SolovayKitaevRecursion.solovayKitaev_compile_strict`), the output braid
word is a VISIBLE Dawson-Nielsen composition

    skApproxC (n+1) U = V_n_braid * groupCommutator A_F_braid A_G_braid

where `V_n_braid = skApproxC n U`, and `A_F_braid, A_G_braid` are recursive
approximations of `exp(i•F)` and `exp(i•G)` respectively, with `F, G`
provided by the traceless balanced commutator construction
(`balanced_commutator_general_axis_lie_traceless`, Path A Step 1).

## Path A overview

  - Step 1 (SHIPPED in SU2BalancedCommutator.lean):
    `balanced_commutator_general_axis_lie_traceless` — traceless companion.
  - Step 2 (this module §1): SU(2) lifting helper `expIsu2`.
  - Step 3 (this module §2): Constructive `skApproxC` definition.
  - Step 4 (this module §3): 11-step inductive error bound proof.
  - Step 5 (this module §4): Constructive strict headline.

## Pipeline Invariant compliance

  - Invariant #10 (no `maxHeartbeats`): RESPECTED.
  - Invariant #15 (no new axioms): RESPECTED.

Primary source: Dawson & Nielsen, *Quantum Info. & Comp.* 6 (2006), 81–95;
                arXiv:quant-ph/0505030, §3.1-3.2 (the recursion).
-/

import Mathlib
import SKEFTHawking.FKLW.SolovayKitaevRecursion
import SKEFTHawking.FKLW.OneParameterSubgroupSU2

set_option autoImplicit false

namespace SKEFTHawking.FKLW.SolovayKitaevPathA

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

open Matrix SKEFTHawking SKEFTHawking.FKLW
  SKEFTHawking.FKLW.SU2BalancedCommutator
  SKEFTHawking.FKLW.FibonacciEpsilonNet
  SKEFTHawking.FKLW.SolovayKitaevRecursion
  SKEFTHawking.FKLW.OneParameterSubgroupSU2

/-! ## 1. SU(2) lifting helper for traceless Hermitian Lie-algebra elements

For `F : Matrix (Fin 2) (Fin 2) ℂ` Hermitian + traceless, `Complex.I • F` is
in the Lie algebra `𝔰𝔲(2) = tracelessSkewHermitian (Fin 2)` and therefore
`exp(I • F) ∈ SU(2)` via the unconditionally-discharged determinant lemma
`DetExpZeroOnSu2_SU2_discharged` (shipped 2026-05-22 PM). -/

/-- For `F : Matrix (Fin 2) (Fin 2) ℂ` Hermitian and traceless,
`Complex.I • F ∈ tracelessSkewHermitian (Fin 2)`. -/
lemma I_smul_mem_tracelessSkewHermitian_of_hermitian_traceless
    {F : Matrix (Fin 2) (Fin 2) ℂ} (hF : F.IsHermitian) (htr : F.trace = 0) :
    (Complex.I • F) ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2) := by
  refine ⟨?_, ?_⟩
  · -- (Complex.I • F).conjTranspose = -(Complex.I • F)
    show (Complex.I • F).conjTranspose = -(Complex.I • F)
    rw [Matrix.conjTranspose_smul]
    rw [show F.conjTranspose = F from hF]
    rw [show (star Complex.I : ℂ) = -Complex.I from by
        rw [Complex.star_def]; rw [Complex.conj_I]]
    rw [neg_smul]
  · -- (Complex.I • F).trace = 0
    show (Complex.I • F).trace = 0
    rw [Matrix.trace_smul, htr, smul_zero]

/-- **Path A Step 2 — SU(2) lift of `exp(I • F)` for F Hermitian + traceless**.

For F Hermitian and traceless in `Matrix (Fin 2) (Fin 2) ℂ`, the matrix
exponential `exp(I • F)` lies in `SU(2)`. This is the constructive lift
needed by `skApproxC`'s recursive case to call itself on the SU(2)-valued
intermediates `exp(I • F)` and `exp(I • G)` produced by the traceless
balanced commutator. -/
noncomputable def expIsu2
    (F : Matrix (Fin 2) (Fin 2) ℂ) (hF : F.IsHermitian) (htr : F.trace = 0) :
    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  ⟨SU2MatrixExp.expAmbient (Complex.I • F),
   expAmbient_mem_specialUnitary_of_DetExpZeroOnSu2
     DetExpZeroOnSu2_SU2_discharged
     (I_smul_mem_tracelessSkewHermitian_of_hermitian_traceless hF htr)⟩

/-- `expIsu2` value equals `expAmbient (I • F)`. -/
@[simp]
theorem expIsu2_val (F : Matrix (Fin 2) (Fin 2) ℂ) (hF : F.IsHermitian)
    (htr : F.trace = 0) :
    (expIsu2 F hF htr : Matrix (Fin 2) (Fin 2) ℂ) =
      SU2MatrixExp.expAmbient (Complex.I • F) := rfl

/-! ## 2. Small substrate for the per-step Dawson-Nielsen composition

Helper lemmas for normalizing the residual matrix log into the unit-norm
Hermitian traceless form required by `balanced_commutator_general_axis_lie_traceless`. -/

/-- Real-scalar multiplication preserves the Hermitian property. -/
lemma IsHermitian_real_smul {M : Matrix (Fin 2) (Fin 2) ℂ}
    (hM : M.IsHermitian) (c : ℝ) : ((c : ℂ) • M).IsHermitian := by
  show ((c : ℂ) • M).conjTranspose = (c : ℂ) • M
  rw [Matrix.conjTranspose_smul,
      show star (c : ℂ) = (c : ℂ) from by
        rw [Complex.star_def, Complex.conj_ofReal],
      show M.conjTranspose = M from hM]

/-- Scalar multiplication of a traceless matrix is traceless. -/
lemma smul_trace_zero {M : Matrix (Fin 2) (Fin 2) ℂ}
    (htr : M.trace = 0) (c : ℂ) : (c • M).trace = 0 := by
  rw [Matrix.trace_smul, htr, smul_zero]

/-- Norm of a real-scalar multiple. -/
lemma norm_real_smul (c : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    ‖((c : ℂ) • M)‖ = |c| * ‖M‖ := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]

/-- Normalizing a nonzero matrix gives unit norm. -/
lemma norm_normalize {M : Matrix (Fin 2) (Fin 2) ℂ} (h : 0 < ‖M‖) :
    ‖((1 / ‖M‖ : ℝ) : ℂ) • M‖ = 1 := by
  rw [norm_real_smul, abs_of_pos (by positivity : (0:ℝ) < 1 / ‖M‖)]
  field_simp

/-- For `h ∈ SU(2)`, `(-Complex.I) • Y_h h` is Hermitian.

The Bloch-sphere matrix log `Y_h h` lands in `tracelessSkewHermitian (Fin 2)`
(per `SU2_Y_h_mem_tracelessSkewHermitian`). Multiplying by `-i` flips
skew-Hermitian to Hermitian. -/
lemma neg_I_smul_Y_h_isHermitian
    {h : Matrix (Fin 2) (Fin 2) ℂ}
    (hh : h ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ((-Complex.I) • Y_h h).IsHermitian := by
  have hY_skew : (Y_h h).IsSkewHermitian :=
    (SU2_Y_h_mem_tracelessSkewHermitian hh).1
  show ((-Complex.I) • Y_h h).conjTranspose = ((-Complex.I) • Y_h h)
  rw [Matrix.conjTranspose_smul,
      show (star (-Complex.I) : ℂ) = Complex.I from by
        rw [star_neg, Complex.star_def, Complex.conj_I, neg_neg],
      show (Y_h h).conjTranspose = -(Y_h h) from hY_skew,
      smul_neg, neg_smul]

/-- For `h ∈ SU(2)`, `(-Complex.I) • Y_h h` is traceless. -/
lemma neg_I_smul_Y_h_trace_zero
    {h : Matrix (Fin 2) (Fin 2) ℂ}
    (hh : h ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ((-Complex.I) • Y_h h).trace = 0 := by
  have hY_tr : (Y_h h).trace = 0 :=
    (SU2_Y_h_mem_tracelessSkewHermitian hh).2
  rw [Matrix.trace_smul, hY_tr, smul_zero]

/-! ## 3. (next ship) Constructive `skApproxC`

Step 3 of Path A. To be shipped next session.

Design plan:
  - Use `Classical.propDecidable` to allow `if-then-else` on undecidable Props
  - Define `pauliFG H θ : Matrix × Matrix` extracting (F, G) from
    `balanced_commutator_general_axis_lie_traceless` when valid, else `(0, 0)`
  - Define `skApproxC_dnStep rec V_n_braid U` doing one DN composition:
    - Compute Δ = U · (ρ_Fib_SU2 V_n_braid)⁻¹
    - Compute H_skew = Y_h Δ, H = -i • H_skew, θ = ‖H‖
    - Normalize H_unit = (1/θ) • H (if θ > 0)
    - Extract (F, G) via `pauliFG H_unit θ`
    - Recurse: A_F = rec (expIsu2 F), A_G = rec (expIsu2 G)
    - Return V_n_braid · groupCommutator A_F A_G
  - Define `skApproxC : ℕ → SU(2) → FibonacciBraidWord` via Nat-rec, using
    skApproxC_dnStep for the inductive case.

Substrate ready (shipped in §1+§2):
  - `expIsu2` — SU(2) lift for traceless Hermitian (§1)
  - `IsHermitian_real_smul`, `smul_trace_zero`, `norm_normalize` (§2)
  - `neg_I_smul_Y_h_isHermitian`, `neg_I_smul_Y_h_trace_zero` (§2) -/

/-! ## 4. (next ship) Inductive error bound

Step 4 of Path A. To be shipped after Step 3.

Per-step error bound chain (per memory file `project_phase6t_strict_headline_2026_05_22.md`):

  1. IH: ‖V_n - U‖ ≤ ε_n
  2. ‖Δ - 1‖ ≤ √2·ε_n via `SU2_linftyOpNorm_le_sqrt_two` on V_n⁻¹
  3. Verify ‖Δ - 1‖ < 1/4 (holds since √2·ε_n ≤ √2·2·ε₀ ≪ 1/4)
  4. §82: ‖H_skew‖ ≤ 4·‖Δ-1‖ ≤ 4√2·ε_n  (via `Y_h_norm_le_four_norm_sub_one`)
  5. H = -i·H_skew Hermitian + traceless (via §2 substrate)
  6. θ := ‖H‖ ≤ 4√2·ε_n
  7. Verify θ ≤ 1 (holds for ε_n ≪ 1/(4√2) ≈ 0.177)
  8. Task #34 (strengthened, §1 Step 1): F, G with ‖F‖,‖G‖ ≤ √(θ/2)
  9. Recurse: ‖ρ A_F - exp(iF)‖ ≤ ε_n, ‖ρ A_G - exp(iG)‖ ≤ ε_n via IH
  10. Compose: ρ A_{n+1} = V_n · groupCommutator(ρ A_F, ρ A_G)
  11. Error: ‖result - U‖ ≤ cubic + stability ≤ K_compose · ε_n^(3/2)
-/

/-! ## 5. (next ship) Constructive strict headline

Step 5 of Path A. -/

end SKEFTHawking.FKLW.SolovayKitaevPathA
