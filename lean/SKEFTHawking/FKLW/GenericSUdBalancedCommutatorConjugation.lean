/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.3 substrate — Unitary conjugation invariance for balanced commutator

The d-generic substrate lemmas for the "spectral-then-conjugate" approach to
the Aharonov-Arad SU(d) balanced commutator (Phase 6y S.3 PROPER):

If `(F, G)` is a balanced commutator for diagonal `H = D = U† H U` (i.e.,
`F · G - G · F = -iθ · D`), then `(U·F·U*, U·G·U*)` is a balanced commutator
for `H = U · D · U*` (i.e., `(UFU*) · (UGU*) - (UGU*) · (UFU*) = -iθ · H`).
Hermiticity and tracelessness are preserved.

## Substantive content shipped

  * `unitary_conjugation_commutator_invariance` — the commutator identity
    is preserved under unitary conjugation.
  * `unitary_conjugation_isHermitian` — Hermiticity is preserved.
  * `unitary_conjugation_trace_invariance` — trace is preserved.

## Norm-bridging caveat (linftyOp vs spectral)

The project's `BalancedCommutator_SUd` predicate uses the `Matrix.linftyOp`
norm, which is **NOT unitary-conjugation-invariant** in general. The spectral
norm IS unitary-invariant, and the two are related by
`‖A‖_spec ≤ ‖A‖_linftyOp ≤ √d · ‖A‖_spec` (Mathlib bound).

For the S.3 d≥3 PROPER full discharge via the spectral-then-conjugate
approach, the norm-preservation step requires either:
  (a) Reformulating `BalancedCommutator_SUd` to use spectral norm
      (changes the predicate signature; downstream consumers must adapt), OR
  (b) Bridging via the `√d` factor (introduces dimension-dependent looseness).

This module ships the algebraic conjugation invariance; the norm-bridging
substrate is shipped in a follow-on commit.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.3 substrate (spectral-pair
conjugation approach to the Aharonov-Arad balanced commutator).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdBalancedCommutatorTwoBlock

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. Commutator invariance under unitary conjugation

For any unitary `U ∈ U(d)` (and a fortiori for `U ∈ SU(d)`), the commutator
`F · G - G · F` is conjugation-equivariant: `U(F·G - G·F)U* = (UFU*)(UGU*) - (UGU*)(UFU*)`.

This is the algebraic backbone of the "spectral diagonal + conjugate" approach
to the d-generic balanced commutator. -/

/-- **Commutator equivariance under unitary conjugation**. -/
theorem unitary_conjugation_commutator_invariance {d : ℕ}
    (U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))
    (F G H : Matrix (Fin d) (Fin d) ℂ) (hFG : F * G - G * F = H) :
    (U.val * F * star U.val) * (U.val * G * star U.val) -
      (U.val * G * star U.val) * (U.val * F * star U.val) =
        U.val * H * star U.val := by
  have hUU' : star U.val * U.val = 1 := U.2.1.1
  -- Key telescoping: U·M·U* · U·N·U* = U·(M·N)·U* since U*U = 1
  have hkey : ∀ (M N : Matrix (Fin d) (Fin d) ℂ),
      (U.val * M * star U.val) * (U.val * N * star U.val) = U.val * (M * N) * star U.val := by
    intros M N
    calc (U.val * M * star U.val) * (U.val * N * star U.val)
        = U.val * M * (star U.val * U.val) * N * star U.val := by noncomm_ring
      _ = U.val * M * 1 * N * star U.val := by rw [hUU']
      _ = U.val * (M * N) * star U.val := by noncomm_ring
  rw [hkey, hkey]
  rw [show U.val * (F * G) * star U.val - U.val * (G * F) * star U.val =
        U.val * (F * G - G * F) * star U.val from by noncomm_ring]
  rw [hFG]

/-- **Scaled commutator equivariance**: for any scalar `c : ℂ`,
if `F·G - G·F = c • H`, then `(UFU*)(UGU*) - (UGU*)(UFU*) = c • (U·H·U*)`. -/
theorem unitary_conjugation_smul_commutator_invariance {d : ℕ}
    (U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))
    (F G H : Matrix (Fin d) (Fin d) ℂ) (c : ℂ)
    (hFG : F * G - G * F = c • H) :
    (U.val * F * star U.val) * (U.val * G * star U.val) -
      (U.val * G * star U.val) * (U.val * F * star U.val) =
        c • (U.val * H * star U.val) := by
  have h := unitary_conjugation_commutator_invariance U F G (c • H) hFG
  rw [h]
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-! ## 2. Hermiticity preservation under unitary conjugation

If `F` is Hermitian, then so is `U·F·U*` for any unitary `U`. -/

/-- **Hermiticity is preserved under unitary conjugation by SU(d)**. -/
theorem unitary_conjugation_isHermitian {d : ℕ}
    (U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))
    (F : Matrix (Fin d) (Fin d) ℂ) (hF : F.IsHermitian) :
    (U.val * F * star U.val).IsHermitian := by
  show (U.val * F * star U.val).conjTranspose = U.val * F * star U.val
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  simp [star_eq_conjTranspose]
  rw [mul_assoc, hF]

/-! ## 3. Trace preservation under unitary conjugation

`tr(U·F·U*) = tr(F)` for any unitary `U` (cyclicity of trace). -/

/-- **Trace is unitary-conjugation-invariant**. -/
theorem unitary_conjugation_trace_invariance {d : ℕ}
    (U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))
    (F : Matrix (Fin d) (Fin d) ℂ) :
    (U.val * F * star U.val).trace = F.trace := by
  rw [Matrix.trace_mul_cycle, show star U.val * U.val = 1 from U.2.1.1, Matrix.one_mul]

/-- **Trace zero is preserved under unitary conjugation**. -/
theorem unitary_conjugation_traceless {d : ℕ}
    (U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))
    (F : Matrix (Fin d) (Fin d) ℂ) (hF : F.trace = 0) :
    (U.val * F * star U.val).trace = 0 := by
  rw [unitary_conjugation_trace_invariance, hF]

/-! ## 4. Composite invariance: balanced commutator is conjugation-equivariant

Combines §1-§3: if `(F, G)` is a balanced commutator structure for `H` (i.e.,
F, G Hermitian traceless with `F·G - G·F = -iθ·H`), then `(UFU*, UGU*)` is a
balanced commutator structure for `U·H·U*` for any `U ∈ SU(d)`.

The norm-bound conjunct is **NOT** automatically preserved under conjugation
since `Matrix.linftyOpNorm` is not unitary-invariant; that bridge ships
separately. -/

/-- **Composite conjugation invariance**: a balanced commutator structure
(Hermitian + traceless + commutator identity) is preserved under unitary
conjugation.

For the norm-bound conjunct of `BalancedCommutator_SUd`, see the
norm-bridging note in the module docstring. -/
theorem unitary_conjugation_balanced_commutator_structure {d : ℕ}
    (U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))
    (F G H : Matrix (Fin d) (Fin d) ℂ) (θ : ℝ)
    (hF_herm : F.IsHermitian) (hG_herm : G.IsHermitian)
    (hF_tr : F.trace = 0) (hG_tr : G.trace = 0)
    (hcomm : F * G - G * F = -((θ : ℂ) * Complex.I) • H) :
    let F' := U.val * F * star U.val
    let G' := U.val * G * star U.val
    let H' := U.val * H * star U.val
    F'.IsHermitian ∧ G'.IsHermitian ∧ F'.trace = 0 ∧ G'.trace = 0 ∧
    F' * G' - G' * F' = -((θ : ℂ) * Complex.I) • H' := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact unitary_conjugation_isHermitian U F hF_herm
  · exact unitary_conjugation_isHermitian U G hG_herm
  · exact unitary_conjugation_traceless U F hF_tr
  · exact unitary_conjugation_traceless U G hG_tr
  · exact unitary_conjugation_smul_commutator_invariance U F G H _ hcomm

end SKEFTHawking.FKLW.GenericSUd
