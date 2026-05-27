/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A1′.1 — MS(θ) gate SU(4) membership via exp/Jacobi route

The Mølmer-Sørensen gate `MS(θ) := exp(-iθ/2 • (X⊗X))` shipped at the
*generator-exponential* level, with kernel-verified SU(4) membership
proved via the S.2d Jacobi formula + skew-Hermitian-exp-is-unitary.

This closes the long-standing T-A1′.1 MS-gate substrate gap (multiple
prior failed attempts at entry-wise verification of the explicit 4×4
matrix). The exp/Jacobi route is fundamentally cleaner because:

  * `(X⊗X)` is Hermitian (kronecker of Hermitians) and traceless
    (kronecker trace identity + `trace(X) = 0`).
  * `-iθ/2 • (X⊗X)` is skew-Hermitian (i·real-imag scalar of Hermitian)
    and traceless (scalar · 0 = 0).
  * `exp(skew-Hermitian)` is unitary (Mathlib + project's
    `Matrix.IsSkewHermitian.exp_mem_unitaryGroup`).
  * `det(exp Y) = exp(tr Y)` for skew-Hermitian Y (Phase 6y S.2d
    `det_exp_skewHermitian`); applied here with `tr Y = 0` gives `det = 1`.

## Headline shape

  * `xKronX : Matrix (Fin 4) (Fin 4) ℂ` — `σ_x ⊗ σ_x` reindexed to `Fin 4`.
  * `xKronX_isHermitian` — Hermitian preservation through kronecker + reindex.
  * `xKronX_trace_zero` — `tr(X⊗X) = tr(X)·tr(X) = 0` via reindex + kronecker.
  * `msGenerator (θ : ℝ) : Matrix (Fin 4) (Fin 4) ℂ` — the skew-Hermitian generator.
  * `msGenerator_isSkewHermitian` — i·real scalar × Hermitian is skew-Hermitian.
  * `msGenerator_trace_zero` — scalar of traceless is traceless.
  * `MSGateExp (θ : ℝ) : Matrix (Fin 4) (Fin 4) ℂ` — the exp.
  * `MSGateExp_mem_unitaryGroup` — via `Matrix.IsSkewHermitian.exp_mem_unitaryGroup`.
  * `MSGateExp_det_eq_one` — via S.2d Jacobi + tr = 0.
  * `MSGateExp_mem_specialUnitaryGroup` — combined SU(4) headline.
  * `MSGate_SU4 (θ : ℝ) : ↥(specialUnitaryGroup (Fin 4) ℂ)` — packaged subtype.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A1′ provenance

Phase 6y Roadmap §"Track T-A1′ detail" sub-wave T-A1′.1 (MS generator
+ SU(4) membership; closes the long-standing gap).

-/

import Mathlib
import SKEFTHawking.FKLW.TrappedIonSU4Substrate
import SKEFTHawking.FKLW.GenericSUdDetExpSkewHerm
import SKEFTHawking.FKLW.SU2MatrixExp
import SKEFTHawking.PauliMatrices

set_option autoImplicit false

namespace SKEFTHawking.FKLW.TrappedIonSU4

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. `xKronX = σ_x ⊗ σ_x` reindexed to `Fin 4` -/

/-- **X⊗X as a 4×4 matrix**: `kronSU4 σ_x σ_x : Matrix (Fin 4) (Fin 4) ℂ`. -/
noncomputable def xKronX : Matrix (Fin 4) (Fin 4) ℂ :=
  kronSU4 SKEFTHawking.σ_x SKEFTHawking.σ_x

/-- **`xKronX` is Hermitian** (substantive).

`σ_x` is Hermitian (`σ_x_hermitian`); kronecker preserves Hermitian
(`Matrix.conjTranspose_kronecker`); reindex preserves Hermitian
(`Matrix.IsHermitian.reindex`). -/
theorem xKronX_isHermitian : xKronX.IsHermitian := by
  unfold xKronX kronSU4
  apply Matrix.IsHermitian.reindex
  -- Goal: `(σ_x ⊗ₖ σ_x).IsHermitian`.
  show (Matrix.kroneckerMap (fun x1 x2 => x1 * x2)
      SKEFTHawking.σ_x SKEFTHawking.σ_x).conjTranspose
      = Matrix.kroneckerMap (fun x1 x2 => x1 * x2)
          SKEFTHawking.σ_x SKEFTHawking.σ_x
  rw [Matrix.conjTranspose_kronecker]
  rw [SKEFTHawking.σ_x_hermitian]

/-- **Trace is preserved under `reindex` with a single equiv** (helper). -/
private theorem trace_reindex_same {m n : Type*} [Fintype m] [Fintype n]
    {α : Type*} [AddCommMonoid α] (e : m ≃ n) (M : Matrix m m α) :
    (Matrix.reindex e e M).trace = M.trace := by
  show ∑ i, (Matrix.reindex e e M) i i = ∑ j, M j j
  -- (reindex e e M) i i = M (e.symm i) (e.symm i).
  have h : ∀ i, (Matrix.reindex e e M) i i = M (e.symm i) (e.symm i) := by
    intro i; rfl
  simp_rw [h]
  -- Goal: ∑ i, M (e.symm i) (e.symm i) = ∑ j, M j j.
  exact Function.Bijective.sum_comp e.symm.bijective (fun j => M j j)

/-- **`xKronX.trace = 0`** (substantive).

`trace(A ⊗ B) = trace(A) · trace(B)` (`Matrix.trace_kronecker`);
`trace(σ_x) = 0` (`σ_x_trace`); reindex preserves trace via
`trace_reindex_same`. -/
theorem xKronX_trace_zero : xKronX.trace = 0 := by
  unfold xKronX kronSU4
  rw [trace_reindex_same]
  -- Goal: (σ_x ⊗ₖ σ_x).trace = 0.
  show (Matrix.kroneckerMap (fun x1 x2 => x1 * x2)
      SKEFTHawking.σ_x SKEFTHawking.σ_x).trace = 0
  rw [Matrix.trace_kronecker]
  rw [SKEFTHawking.σ_x_trace]
  ring

/-! ## 2. The MS generator: `msGen(θ) = -i·θ/2 • (X⊗X)` -/

/-- **MS generator** `msGen(θ) := -i·θ/2 • (X⊗X)`.

The Lie-algebra-level Mølmer-Sørensen generator at angle `θ : ℝ`.
Lives in `𝔰𝔲(4)` (skew-Hermitian + traceless). -/
noncomputable def msGenerator (θ : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (-(Complex.I * (θ : ℂ) / 2)) • xKronX

/-- **`msGenerator θ` is skew-Hermitian** (substantive).

For Hermitian `M` and `c : ℂ` with `star c = -c` (purely imaginary),
`(c • M)† = star(c) • M† = -c • M = -(c • M)`. -/
theorem msGenerator_isSkewHermitian (θ : ℝ) :
    (msGenerator θ).IsSkewHermitian := by
  show ((-(Complex.I * (θ : ℂ) / 2)) • xKronX).conjTranspose
       = -((-(Complex.I * (θ : ℂ) / 2)) • xKronX)
  rw [Matrix.conjTranspose_smul, xKronX_isHermitian]
  -- Goal: star (-(I·θ/2)) • xKronX = -((-(I·θ/2)) • xKronX)
  rw [show star (-(Complex.I * (θ : ℂ) / 2)) = -(-(Complex.I * (θ : ℂ) / 2)) by
        -- Direct calculation: star(c) = -c for purely imaginary c = -(I·θ/2).
        have h_rw : (Complex.I * (θ : ℂ) / 2) = ((θ / 2 : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [h_rw, star_neg, StarMul.star_mul]
        -- Goal: -(star I * star ↑(θ/2)) = - -(↑(θ/2) * I)
        rw [show star (Complex.I) = -Complex.I from Complex.conj_I]
        rw [show star ((↑(θ / 2) : ℂ)) = ((θ / 2 : ℝ) : ℂ) from Complex.conj_ofReal _]
        ring]
  -- Goal: -(-(I·θ/2)) • xKronX = -((-(I·θ/2)) • xKronX)
  rw [neg_smul]

/-- **`msGenerator θ` has trace 0** (scalar of traceless is traceless). -/
theorem msGenerator_trace_zero (θ : ℝ) : (msGenerator θ).trace = 0 := by
  unfold msGenerator
  rw [Matrix.trace_smul, xKronX_trace_zero, smul_zero]

/-! ## 3. The MS gate via matrix exp -/

/-- **MS gate via matrix exponential**: `MSGateExp θ := exp(msGenerator θ)`.

The Mølmer-Sørensen gate as the matrix exponential of `-iθ/2 • (X⊗X)`,
matching the physical definition `MS(θ) := exp(-iθ X⊗X / 2)`. -/
noncomputable def MSGateExp (θ : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  NormedSpace.exp (msGenerator θ)

/-- **`MSGateExp θ` is unitary** (substantive).

Via `Matrix.IsSkewHermitian.exp_mem_unitaryGroup` applied to
`msGenerator_isSkewHermitian θ`. -/
theorem MSGateExp_mem_unitaryGroup (θ : ℝ) :
    MSGateExp θ ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
  Matrix.IsSkewHermitian.exp_mem_unitaryGroup (msGenerator_isSkewHermitian θ)

/-- **`MSGateExp θ` has determinant 1** (substantive).

Via Phase 6y S.2d Jacobi formula `det_exp_skewHermitian`:
`det(exp Y) = exp(tr Y)` for skew-Hermitian Y. Combined with
`msGenerator_trace_zero`: `exp(0) = 1`. -/
theorem MSGateExp_det_eq_one (θ : ℝ) :
    (MSGateExp θ : Matrix (Fin 4) (Fin 4) ℂ).det = 1 := by
  show (NormedSpace.exp (msGenerator θ) : Matrix (Fin 4) (Fin 4) ℂ).det = 1
  rw [SKEFTHawking.FKLW.GenericSUd.det_exp_skewHermitian _
      (msGenerator_isSkewHermitian θ)]
  rw [msGenerator_trace_zero, Complex.exp_zero]

/-- **`MSGateExp θ ∈ SU(4)`** (full headline) (substantive).

Combines `MSGateExp_mem_unitaryGroup` (unitarity) + `MSGateExp_det_eq_one`
(det = 1) via `Matrix.mem_specialUnitaryGroup_iff`. -/
theorem MSGateExp_mem_specialUnitaryGroup (θ : ℝ) :
    MSGateExp θ ∈ Matrix.specialUnitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  exact ⟨MSGateExp_mem_unitaryGroup θ, MSGateExp_det_eq_one θ⟩

/-- **MS gate as SU(4) subtype element** (packaged headline). -/
noncomputable def MSGate_SU4 (θ : ℝ) : ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ) :=
  ⟨MSGateExp θ, MSGateExp_mem_specialUnitaryGroup θ⟩

/-- `MSGate_SU4 0 = 1` (identity at zero angle). -/
@[simp]
theorem MSGate_SU4_zero : MSGate_SU4 0 = 1 := by
  apply Subtype.ext
  show MSGateExp 0 = 1
  unfold MSGateExp msGenerator
  -- At θ = 0: -(I·0/2) = 0, so msGenerator 0 = 0 • xKronX = 0.
  rw [show (-(Complex.I * ((0 : ℝ) : ℂ) / 2)) = 0 from by push_cast; ring]
  rw [zero_smul]
  exact NormedSpace.exp_zero

end SKEFTHawking.FKLW.TrappedIonSU4
