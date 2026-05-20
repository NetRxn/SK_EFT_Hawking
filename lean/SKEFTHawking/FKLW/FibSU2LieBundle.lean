/-
Phase 6p Wave 2c.4a-R4.2.d.R5.4 Layer F.13 (FibSU2LieBundle, session 48):
bridge SU2LieAlgebra's general Ad-action API to the σ_Fib_*_SU-specific
3-bundle used by the H_Fib spanning argument.

## What this module ships (~80 LoC)

  - **`tracelessSkewHermitian_conj_σ_Fib_1_SU_mat`** and
    **`..._σ_Fib_2_SU_mat`** — the σ_Fib_*-instances of the general
    `tracelessSkewHermitian_conj_specialUnitary` (Layer F.12).

  - **`σ_Fib_lie_bundle (X : Matrix _ _ ℂ)`** — the 3-element bundle
    `(X, σ_Fib_1_SU_mat·X·σ_Fib_1_SU_mat†, σ_Fib_2_SU_mat·X·σ_Fib_2_SU_mat†)`
    of Ad-rotated Lie directions. For X ∈ 𝔰𝔲(2) all three components
    are also in 𝔰𝔲(2).

  - **`σ_Fib_lie_bundle_mem_tracelessSkewHermitian`** — combined
    membership: triple Ad-conjugates stay in 𝔰𝔲(2).

  - **`σ_Fib_lie_bundle_pauliDet`** — shortcut def for the load-bearing
    `pauliDet` of the 3-bundle. Used in Layer F.14+ to apply F.8's
    Cramer-rule lin-indep criterion.

## Pipeline Invariant compliance

  - #10 (no `maxHeartbeats`): RESPECTED.
  - #15 (no new project-local axioms): RESPECTED.
  - ADR-003 (zero sorry): RESPECTED.
-/

import Mathlib
import SKEFTHawking.FKLW.SU2LieAlgebra
import SKEFTHawking.FKLW.FibSU2Rep

set_option autoImplicit false

namespace SKEFTHawking.FKLW.FibSU2LieBundle

open SKEFTHawking SKEFTHawking.FKLW SKEFTHawking.FKLW.SU2LieAlgebra

/-- **σ_Fib_1_SU_mat Ad-conjugation preserves 𝔰𝔲(2)** (Layer F.13). -/
theorem tracelessSkewHermitian_conj_σ_Fib_1_SU_mat
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X ∈ tracelessSkewHermitian (Fin 2)) :
    σ_Fib_1_SU_mat * X * σ_Fib_1_SU_mat.conjTranspose ∈
      tracelessSkewHermitian (Fin 2) :=
  tracelessSkewHermitian_conj_specialUnitary σ_Fib_1_SU hX

/-- **σ_Fib_2_SU_mat Ad-conjugation preserves 𝔰𝔲(2)** (Layer F.13). -/
theorem tracelessSkewHermitian_conj_σ_Fib_2_SU_mat
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X ∈ tracelessSkewHermitian (Fin 2)) :
    σ_Fib_2_SU_mat * X * σ_Fib_2_SU_mat.conjTranspose ∈
      tracelessSkewHermitian (Fin 2) :=
  tracelessSkewHermitian_conj_specialUnitary σ_Fib_2_SU hX

/-- **The σ_Fib 3-bundle of Lie directions** for X ∈ 𝔰𝔲(2):
`(X, Ad(σ_Fib_1) X, Ad(σ_Fib_2) X)`. Each component lies in 𝔰𝔲(2)
when X does (see `σ_Fib_lie_bundle_mem_tracelessSkewHermitian`).

This is the load-bearing tuple for the H_Fib spanning argument:
its `pauliDet` measures ℝ-linear independence (via Layer F.8), and
non-zero `pauliDet` translates to "the three Lie-direction conjugates
span 𝔰𝔲(2)". -/
noncomputable def σ_Fib_lie_bundle (X : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ × Matrix (Fin 2) (Fin 2) ℂ ×
      Matrix (Fin 2) (Fin 2) ℂ :=
  (X,
   σ_Fib_1_SU_mat * X * σ_Fib_1_SU_mat.conjTranspose,
   σ_Fib_2_SU_mat * X * σ_Fib_2_SU_mat.conjTranspose)

/-- **All three components of `σ_Fib_lie_bundle X` are in 𝔰𝔲(2)**
when X is. -/
theorem σ_Fib_lie_bundle_mem_tracelessSkewHermitian
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X ∈ tracelessSkewHermitian (Fin 2)) :
    (σ_Fib_lie_bundle X).1 ∈ tracelessSkewHermitian (Fin 2) ∧
    (σ_Fib_lie_bundle X).2.1 ∈ tracelessSkewHermitian (Fin 2) ∧
    (σ_Fib_lie_bundle X).2.2 ∈ tracelessSkewHermitian (Fin 2) :=
  ⟨hX,
   tracelessSkewHermitian_conj_σ_Fib_1_SU_mat hX,
   tracelessSkewHermitian_conj_σ_Fib_2_SU_mat hX⟩

/-- **`pauliDet` of the σ_Fib Lie bundle** for X ∈ 𝔰𝔲(2). Shortcut def
for the determinant criterion: `σ_Fib_lie_bundle_pauliDet X ≠ 0` ↔
the 3-bundle is ℝ-linearly independent in 𝔰𝔲(2) (via Layer F.8). -/
noncomputable def σ_Fib_lie_bundle_pauliDet
    (X : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  pauliDet (σ_Fib_lie_bundle X).1
           (σ_Fib_lie_bundle X).2.1
           (σ_Fib_lie_bundle X).2.2

/-- **Unfold form** for `σ_Fib_lie_bundle_pauliDet`. -/
theorem σ_Fib_lie_bundle_pauliDet_eq (X : Matrix (Fin 2) (Fin 2) ℂ) :
    σ_Fib_lie_bundle_pauliDet X =
      pauliDet X
        (σ_Fib_1_SU_mat * X * σ_Fib_1_SU_mat.conjTranspose)
        (σ_Fib_2_SU_mat * X * σ_Fib_2_SU_mat.conjTranspose) := rfl

end SKEFTHawking.FKLW.FibSU2LieBundle
