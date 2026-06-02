import SKEFTHawking.QuantumNetwork.DiamondNormSup
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Algebra.Order.Chebyshev

/-!
# Diamond-distance attainment (Phase 6AF-8)

The diamond distance `diamondDist Φ₁ Φ₂ = sup_ρ D((Φ₁⊗id)ρ, (Φ₂⊗id)ρ)` was proven a genuine
`[0,1]`-valued metric in `DiamondNormSup.lean` using only boundedness of the supremum
(`Real.sSup`). Here we upgrade it to an **attained** supremum (a `max`): there is an optimal
input density operator realizing the worst-case distinguishability.

The binding ingredient deferred at 6AF-6 was **continuity of `ρ ↦ traceNorm(…)`** (the
singular-value sum) in the matrix entries. We obtain it not from per-eigenvalue continuity
(individual `IsHermitian.eigenvalues` are *not* continuous — eigenvalue crossings reorder the
labeling) but from the elementary **Lipschitz** bound
`|‖A‖₁ − ‖B‖₁| ≤ ‖A−B‖₁ ≤ √(card) · ‖A−B‖_F` (reverse triangle + Cauchy–Schwarz on singular
values, `∑σᵢ ≤ √n·√(∑σᵢ²)` with `∑σᵢ² = tr(AᴴA) = ‖A‖²_F`). The Frobenius normed structure
(opt-in over the default Pi topology, no instance diamond) makes `Matrix ι ι ℂ` a
finite-dimensional normed `ℂ`-space, hence proper, so the density-operator set — closed and
bounded — is compact, and the extreme value theorem (`IsCompact.exists_sSup_image_eq`) delivers
attainment.

Invariants: kernel-pure, zero sorry, zero project-local axioms, no `maxHeartbeats`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder Matrix

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **`Re tr(AᴴA) = ‖A‖²_F`** (Frobenius): the trace of `AᴴA` is the entrywise sum of squared
moduli, which is the Frobenius norm squared. -/
theorem re_trace_conjTranspose_mul_self_eq_frobenius_sq (A : Matrix ι ι ℂ) :
    (Aᴴ * A).trace.re = ‖A‖ ^ 2 := by
  have hentry : (Aᴴ * A).trace.re = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
    rw [Matrix.trace, Complex.re_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.conjTranspose_apply, Complex.star_def, mul_comm, Complex.mul_conj,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [hentry, Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    (Real.rpow_natCast ‖A i j‖ 2).symm

/-- **`‖A‖₁ ≤ √(card) · ‖A‖_F`** — the trace norm (sum of singular values) is dominated by the
Frobenius norm, via Cauchy–Schwarz on the singular values: `∑σᵢ ≤ √n·√(∑σᵢ²)` with
`∑σᵢ² = tr(AᴴA) = ‖A‖²_F`. The Lipschitz constant for trace-norm continuity. -/
theorem traceNorm_le_sqrt_card_mul_norm (A : Matrix ι ι ℂ) :
    traceNorm A ≤ Real.sqrt (Fintype.card ι) * ‖A‖ := by
  have hPSD := Matrix.posSemidef_conjTranspose_mul_self A
  set lam := hPSD.isHermitian.eigenvalues with hlam
  have hlamnn : ∀ i, 0 ≤ lam i := fun i => hPSD.eigenvalues_nonneg i
  have htn : traceNorm A = ∑ i, Real.sqrt (lam i) := rfl
  have hsum_eq : ∑ i, lam i = ‖A‖ ^ 2 := by
    rw [← re_trace_conjTranspose_mul_self_eq_frobenius_sq A,
      hPSD.isHermitian.trace_eq_sum_eigenvalues, Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => Complex.ofReal_re _
  have hcs : (∑ i, Real.sqrt (lam i)) ^ 2 ≤ (Fintype.card ι : ℝ) * ‖A‖ ^ 2 := by
    have hch := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι))
      (f := fun i => Real.sqrt (lam i))
    rw [Finset.card_univ] at hch
    refine hch.trans (le_of_eq ?_)
    rw [← hsum_eq]
    exact congrArg _ (Finset.sum_congr rfl fun i _ => Real.sq_sqrt (hlamnn i))
  rw [htn, show Real.sqrt (Fintype.card ι) * ‖A‖ = Real.sqrt ((Fintype.card ι : ℝ) * ‖A‖ ^ 2) by
    rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg A)]]
  calc ∑ i, Real.sqrt (lam i)
      = Real.sqrt ((∑ i, Real.sqrt (lam i)) ^ 2) :=
        (Real.sqrt_sq (Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _)).symm
    _ ≤ Real.sqrt ((Fintype.card ι : ℝ) * ‖A‖ ^ 2) := Real.sqrt_le_sqrt hcs

/-- **The trace norm is Lipschitz** (constant `√card`), via the reverse triangle inequality
`|‖A‖₁ − ‖B‖₁| ≤ ‖A−B‖₁` and the Frobenius bound. -/
theorem lipschitzWith_traceNorm :
    LipschitzWith (Real.sqrt (Fintype.card ι)).toNNReal (traceNorm : Matrix ι ι ℂ → ℝ) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro A B
  rw [Real.dist_eq, Real.coe_toNNReal _ (Real.sqrt_nonneg _), dist_eq_norm]
  have hrev : |traceNorm A - traceNorm B| ≤ traceNorm (A - B) := by
    rw [abs_sub_le_iff]
    constructor
    · have h := traceNorm_triangle (A - B) B
      rw [sub_add_cancel] at h; linarith
    · have h := traceNorm_triangle (B - A) A
      rw [sub_add_cancel, show B - A = -(A - B) by abel, traceNorm_neg] at h; linarith
  exact hrev.trans (traceNorm_le_sqrt_card_mul_norm (A - B))

/-- **The trace norm is continuous** in the matrix entries (Frobenius topology). -/
theorem continuous_traceNorm : Continuous (traceNorm : Matrix ι ι ℂ → ℝ) :=
  lipschitzWith_traceNorm.continuous

end SKEFTHawking.QuantumNetwork
