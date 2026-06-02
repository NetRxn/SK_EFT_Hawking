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

/-- `{z : ℂ | 0 ≤ z}` is closed (`0 ≤ z ↔ z.re ≥ 0 ∧ z.im = 0`, an intersection of closed sets). -/
theorem isClosed_complex_nonneg : IsClosed {z : ℂ | 0 ≤ z} := by
  have : {z : ℂ | 0 ≤ z} = {z | 0 ≤ z.re} ∩ {z | z.im = 0} := by
    ext z; simp [Complex.le_def, Complex.zero_re, Complex.zero_im, eq_comm]
  rw [this]
  exact (isClosed_le continuous_const Complex.continuous_re).inter
    (isClosed_eq Complex.continuous_im continuous_const)

omit [DecidableEq ι] in
/-- **The density-operator set is closed** (Frobenius topology): an intersection of the closed
Hermitian condition, the closed quadratic-form-nonneg conditions, and the closed trace-`1`
condition. -/
theorem isClosed_isDensityOperator :
    IsClosed {ρ : Matrix ι ι ℂ | IsDensityOperator ρ} := by
  have key : {ρ : Matrix ι ι ℂ | IsDensityOperator ρ}
      = ({ρ | ρᴴ = ρ} ∩ ⋂ x : ι → ℂ, {ρ | 0 ≤ star x ⬝ᵥ ρ.mulVec x}) ∩ {ρ | ρ.trace = 1} := by
    ext ρ
    simp only [IsDensityOperator, Matrix.posSemidef_iff_dotProduct_mulVec, Matrix.IsHermitian,
      Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [key]
  refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
  · exact isClosed_eq (by fun_prop) continuous_id
  · refine isClosed_iInter fun x => ?_
    exact isClosed_complex_nonneg.preimage (by fun_prop)
  · exact isClosed_eq (Matrix.traceLinearMap ι ℂ ℂ).continuous_of_finiteDimensional continuous_const

/-- **The Frobenius norm is dominated by the trace norm**: `‖A‖_F ≤ ‖A‖₁` (since
`‖A‖²_F = ∑σᵢ² ≤ (∑σᵢ)² = ‖A‖₁²`). -/
theorem frobenius_le_traceNorm (A : Matrix ι ι ℂ) : ‖A‖ ≤ traceNorm A := by
  have hPSD := Matrix.posSemidef_conjTranspose_mul_self A
  set lam := hPSD.isHermitian.eigenvalues with hlam
  have hlamnn : ∀ i, 0 ≤ lam i := fun i => hPSD.eigenvalues_nonneg i
  have hfrob : ‖A‖ ^ 2 = ∑ i, lam i := by
    rw [← re_trace_conjTranspose_mul_self_eq_frobenius_sq A,
      hPSD.isHermitian.trace_eq_sum_eigenvalues, Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => Complex.ofReal_re _
  have hsq : ‖A‖ ^ 2 ≤ (traceNorm A) ^ 2 := by
    rw [hfrob, show traceNorm A = ∑ i, Real.sqrt (lam i) from rfl]
    refine le_trans (le_of_eq ?_)
      (Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => Real.sqrt_nonneg (lam i))
    exact Finset.sum_congr rfl fun i _ => (Real.sq_sqrt (hlamnn i)).symm
  calc ‖A‖ = Real.sqrt (‖A‖ ^ 2) := (Real.sqrt_sq (norm_nonneg A)).symm
    _ ≤ Real.sqrt ((traceNorm A) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = traceNorm A := Real.sqrt_sq (traceNorm_nonneg A)

/-- A density operator has Frobenius norm `≤ 1` (`‖ρ‖_F ≤ ‖ρ‖₁ = tr ρ = 1`). -/
theorem norm_le_one_of_isDensityOperator {ρ : Matrix ι ι ℂ} (hρ : IsDensityOperator ρ) :
    ‖ρ‖ ≤ 1 :=
  calc ‖ρ‖ ≤ traceNorm ρ := frobenius_le_traceNorm ρ
    _ = ρ.trace.re := traceNorm_posSemidef hρ.1
    _ = 1 := by rw [hρ.2, Complex.one_re]

/-- **The density-operator set is compact** (finite-dimensional ⇒ proper; closed + bounded). -/
theorem isCompact_isDensityOperator :
    IsCompact {ρ : Matrix ι ι ℂ | IsDensityOperator ρ} := by
  haveI : ProperSpace (Matrix ι ι ℂ) := FiniteDimensional.proper ℂ _
  refine Metric.isCompact_of_isClosed_isBounded isClosed_isDensityOperator ?_
  refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨1, fun ρ hρ => ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact norm_le_one_of_isDensityOperator hρ

omit [DecidableEq ι] in
/-- The Kraus map `ρ ↦ ∑ₖ Kₖ ρ Kₖᴴ` is continuous (a finite sum of two-sided multiplications,
each continuous in finite dimension). -/
theorem continuous_krausMap {m : ℕ} (K : Fin m → Matrix ι ι ℂ) :
    Continuous (krausMap K) := by
  unfold krausMap
  exact continuous_finset_sum _ fun k _ => by fun_prop

/-- The **maximally mixed state** `(card ι)⁻¹ • 1` is a density operator (when the index is
nonempty), giving a witness that the density-operator set is nonempty. -/
theorem isDensityOperator_maximallyMixed [Nonempty ι] :
    IsDensityOperator (((Fintype.card ι : ℂ))⁻¹ • (1 : Matrix ι ι ℂ)) := by
  have hcard : (Fintype.card ι : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := ι))
  have hdiag : ((Fintype.card ι : ℂ))⁻¹ • (1 : Matrix ι ι ℂ)
      = diagonal (fun _ => ((Fintype.card ι : ℂ))⁻¹) := by
    ext i j; by_cases h : i = j <;> simp [Matrix.smul_apply, h]
  have hpos : (0 : ℂ) ≤ ((Fintype.card ι : ℂ))⁻¹ := by
    rw [show ((Fintype.card ι : ℂ))⁻¹ = (((Fintype.card ι : ℝ))⁻¹ : ℝ) by push_cast; ring,
      Complex.zero_le_real]
    positivity
  refine ⟨?_, ?_⟩
  · rw [hdiag]
    exact Matrix.PosSemidef.diagonal fun _ => hpos
  · rw [hdiag, Matrix.trace_diagonal, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_inv_cancel₀ hcard]

/-- **Diamond-distance attainment** — the supremum defining `diamondDist` is achieved by an
optimal input density operator `ρ` (so the `sSup` is a genuine maximum). Combines compactness of
the density-operator set with continuity of `ρ ↦ D((Φ₁⊗id)ρ,(Φ₂⊗id)ρ)`, via the extreme value
theorem `IsCompact.exists_sSup_image_eq`. -/
theorem exists_diamondDist_eq {m n : ℕ} [Nonempty (Fin n)]
    {K₁ K₂ : Fin m → Matrix (Fin n) (Fin n) ℂ} :
    ∃ ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ, IsDensityOperator ρ ∧
      diamondDist K₁ K₂
        = traceDist (krausMap (tensorKraus K₁) ρ) (krausMap (tensorKraus K₂) ρ) := by
  set f : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ → ℝ :=
    fun ρ => traceDist (krausMap (tensorKraus K₁) ρ) (krausMap (tensorKraus K₂) ρ) with hf
  have hcont : Continuous f := by
    have : f = fun ρ => (1 / 2 : ℝ) *
        traceNorm (krausMap (tensorKraus K₁) ρ - krausMap (tensorKraus K₂) ρ) := by
      funext ρ; simp only [hf, traceDist]
    rw [this]
    exact continuous_const.mul (continuous_traceNorm.comp
      ((continuous_krausMap _).sub (continuous_krausMap _)))
  have hne : {ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ | IsDensityOperator ρ}.Nonempty :=
    ⟨_, isDensityOperator_maximallyMixed⟩
  obtain ⟨ρ, hρ, hsup⟩ := isCompact_isDensityOperator.exists_sSup_image_eq hne hcont.continuousOn
  refine ⟨ρ, hρ, ?_⟩
  have hset : {d | ∃ σ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ, IsDensityOperator σ ∧
      d = traceDist (krausMap (tensorKraus K₁) σ) (krausMap (tensorKraus K₂) σ)}
      = f '' {σ | IsDensityOperator σ} := by
    ext d
    simp only [Set.mem_image, Set.mem_setOf_eq, hf]
    constructor
    · rintro ⟨σ, hσ, rfl⟩; exact ⟨σ, hσ, rfl⟩
    · rintro ⟨σ, hσ, rfl⟩; exact ⟨σ, hσ, rfl⟩
  rw [diamondDist, hset, hsup]

end SKEFTHawking.QuantumNetwork
