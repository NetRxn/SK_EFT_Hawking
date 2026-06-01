import Mathlib.Tactic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef

/-!
# General mixed-state certification layer (Phase 6AE-A, foundation)

The general density-matrix metrics the Bell-diagonal/Werner substrate (Phases
6AA–6AD) deliberately avoided, built concretely on `Matrix (Fin n) (Fin n) ℂ` using
Mathlib's spectral theorem and positive-semidefinite machinery (no abstract
C*-algebra detour, no Stinespring).

* `IsDensityOperator ρ` — positive semidefinite, unit trace.
* `traceNorm A = ∑ √eigenvalues(AᴴA)` — the Schatten-1 / nuclear norm `tr|A|`
  (sum of singular values).
* `traceDist ρ σ = ½‖ρ − σ‖₁` — the trace distance.

This increment establishes the definitions and their cleanly-provable structural
properties (nonnegativity, symmetry, vanishing on equality). The deep functional-
analytic theorems (trace-norm triangle inequality, CPTP contractivity, Uhlmann
fidelity / Fuchs–van de Graaf) are subsequent increments.

Invariants: kernel-pure, zero sorry, zero project-local axioms, no `maxHeartbeats`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder

variable {n : ℕ}

/-- A **density operator**: positive semidefinite with unit trace. -/
def IsDensityOperator (ρ : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

/-- Sum of singular values of a positive-semidefinite witness `∑ √eigenvalues(M)`.
Factored on the PSD witness (proof-irrelevant in `M`) so that trace-norm identities
reduce to matrix equalities. -/
noncomputable def traceNormOf {M : Matrix (Fin n) (Fin n) ℂ} (_hM : M.PosSemidef) : ℝ :=
  ∑ i, Real.sqrt (_hM.isHermitian.eigenvalues i)

/-- The trace-norm-of-witness depends only on the matrix, not the PSD proof. -/
theorem traceNormOf_congr {M M' : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosSemidef)
    (hM' : M'.PosSemidef) (h : M = M') : traceNormOf hM = traceNormOf hM' := by
  subst h; rfl

theorem traceNormOf_nonneg {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosSemidef) :
    0 ≤ traceNormOf hM :=
  Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _

/-- **Trace norm** `‖A‖₁ = tr|A|`, as the sum of singular values
`∑ √eigenvalues(AᴴA)`. -/
noncomputable def traceNorm (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  traceNormOf (Matrix.posSemidef_conjTranspose_mul_self A)

/-- The trace norm is nonnegative. -/
theorem traceNorm_nonneg (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ traceNorm A :=
  traceNormOf_nonneg _

/-- The trace norm is invariant under negation (`AᴴA = (−A)ᴴ(−A)`). -/
theorem traceNorm_neg (A : Matrix (Fin n) (Fin n) ℂ) : traceNorm (-A) = traceNorm A :=
  traceNormOf_congr _ _ (by rw [conjTranspose_neg, neg_mul_neg])

/-- The trace norm of the zero matrix is zero. -/
@[simp] theorem traceNorm_zero : traceNorm (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  have hz : Matrix.PosSemidef (0 : Matrix (Fin n) (Fin n) ℂ) := Matrix.PosSemidef.zero
  rw [traceNorm, traceNormOf_congr _ hz (by simp)]
  unfold traceNormOf
  have he : hz.isHermitian.eigenvalues = 0 :=
    (Matrix.IsHermitian.eigenvalues_eq_zero_iff _).mpr rfl
  simp [he]

/-- **Trace distance** `D(ρ,σ) = ½‖ρ − σ‖₁`. -/
noncomputable def traceDist (ρ σ : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  (1 / 2) * traceNorm (ρ - σ)

/-- The trace distance is nonnegative. -/
theorem traceDist_nonneg (ρ σ : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ traceDist ρ σ := by
  unfold traceDist
  have := traceNorm_nonneg (ρ - σ)
  linarith

/-- **The trace distance is symmetric.** -/
theorem traceDist_comm (ρ σ : Matrix (Fin n) (Fin n) ℂ) : traceDist ρ σ = traceDist σ ρ := by
  unfold traceDist
  rw [← neg_sub ρ σ, traceNorm_neg]

/-- **The trace distance vanishes on equal states.** -/
@[simp] theorem traceDist_self (ρ : Matrix (Fin n) (Fin n) ℂ) : traceDist ρ ρ = 0 := by
  unfold traceDist
  rw [sub_self, traceNorm_zero, mul_zero]

end SKEFTHawking.QuantumNetwork
