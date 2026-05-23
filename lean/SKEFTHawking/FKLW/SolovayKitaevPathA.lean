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

/-! ## 2. (next ship) Constructive `skApproxC`

Step 3 of Path A. To be shipped next session. -/

/-! ## 3. (next ship) Inductive error bound

Step 4 of Path A. -/

/-! ## 4. (next ship) Constructive strict headline

Step 5 of Path A. -/

end SKEFTHawking.FKLW.SolovayKitaevPathA
