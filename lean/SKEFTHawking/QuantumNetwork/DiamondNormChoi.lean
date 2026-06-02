import SKEFTHawking.QuantumNetwork.DiamondNormSup
import SKEFTHawking.QuantumNetwork.DiamondNorm
import SKEFTHawking.QuantumNetwork.TraceNormCauchySchwarz

/-!
# Diamond norm: the Choi / maximally-entangled primal bound (Phase 6AF-9)

The Watrous SDP characterization of the diamond norm pairs a primal program (a maximization over
input states of the stabilized output distinguishability) with a dual program over the Choi
matrix. The full primal=dual identity needs conic strong duality (a `ProperCone`/`PointedCone`
convex-duality substrate absent at pin) — see the deferred-frontier note in `DiamondNorm.lean`.

This file delivers the **primal (one-sided) bound**: a concrete feasible point of the primal
program — the **maximally-entangled (Choi) state** `Ω = (1/n)|Ω⟩⟨Ω|` — gives a computable lower
bound on the diamond distance,

  `diamondDist Φ₁ Φ₂ ≥ D((Φ₁⊗id)Ω, (Φ₂⊗id)Ω)`,

via the least-upper-bound property `le_diamondDist`. The maximally-entangled state is the
canonical primal point of the Watrous program (it is the state whose stabilized output is the
normalized Choi matrix), so this is the primal-feasibility half of the Choi-SDP characterization.

Invariants: kernel-pure, zero sorry, zero project-local axioms, no `maxHeartbeats`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder

variable {m n : ℕ}

/-- The unnormalized maximally-entangled vector `|Ω⟩ = ∑ᵢ |i,i⟩` as a column matrix on the
doubled index `Fin n × Fin n`: `omegaVec (i,j) = ⟦i = j⟧`. -/
noncomputable def omegaVec (n : ℕ) : Matrix (Fin n × Fin n) (Fin 1) ℂ :=
  fun p _ => if p.1 = p.2 then 1 else 0

/-- The **maximally-entangled (Choi) state** `Ω = (1/n)|Ω⟩⟨Ω|` on `Fin n × Fin n`. -/
noncomputable def maxEntangled (n : ℕ) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  ((n : ℂ))⁻¹ • (omegaVec n * (omegaVec n)ᴴ)

/-- **The maximally-entangled state is a density operator** (`n ≥ 1`): it is `(1/n)` times the
rank-one PSD outer product `|Ω⟩⟨Ω|`, and `tr|Ω⟩⟨Ω| = n`. -/
theorem isDensityOperator_maxEntangled [NeZero n] :
    IsDensityOperator (maxEntangled n) := by
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hpos : (0 : ℂ) ≤ ((n : ℂ))⁻¹ := by
    rw [show ((n : ℂ))⁻¹ = (((n : ℝ))⁻¹ : ℝ) by push_cast; ring, Complex.zero_le_real]
    positivity
  refine ⟨?_, ?_⟩
  · exact (Matrix.posSemidef_self_mul_conjTranspose _).smul hpos
  · rw [maxEntangled, Matrix.trace_smul, smul_eq_mul]
    have htr : (omegaVec n * (omegaVec n)ᴴ).trace = (n : ℂ) := by
      rw [Matrix.trace_mul_comm, Matrix.trace]
      simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, omegaVec,
        Finset.univ_unique, Finset.sum_singleton]
      have hterm : ∀ p : Fin n × Fin n,
          star (if p.1 = p.2 then (1:ℂ) else 0) * (if p.1 = p.2 then 1 else 0)
            = if p.1 = p.2 then (1:ℂ) else 0 := fun p => by split <;> simp
      simp_rw [hterm]
      rw [Fintype.sum_prod_type]
      simp [Finset.sum_ite_eq, Finset.sum_const, Finset.card_univ]
    rw [htr, inv_mul_cancel₀ hn]

/-- **Choi / maximally-entangled primal bound** — the diamond distance is bounded below by the
distinguishability of the channels on the maximally-entangled (Choi) input state. A concrete
feasible point of the Watrous primal program, hence the primal (one-sided) half of the Choi-SDP
characterization, with no SDP duality required. -/
theorem diamondDist_ge_maxEntangled [NeZero n]
    {K₁ K₂ : Fin m → Matrix (Fin n) (Fin n) ℂ}
    (hK₁ : IsKrausChannel K₁) (hK₂ : IsKrausChannel K₂) :
    traceDist (krausMap (tensorKraus K₁) (maxEntangled n))
        (krausMap (tensorKraus K₂) (maxEntangled n))
      ≤ diamondDist K₁ K₂ :=
  le_diamondDist hK₁ hK₂ isDensityOperator_maxEntangled

/-- **Trace norm is invariant under reindexing rows and columns by the same bijection.**
`‖M.submatrix e e‖₁ = ‖M‖₁` — the trace norm depends only on the singular charpoly, which is
preserved by simultaneous row/column reindexing (`charpoly_reindex`). -/
theorem traceNorm_submatrix_equiv {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι ≃ ι)
    (M : Matrix ι ι ℂ) : traceNorm (M.submatrix e e) = traceNorm M := by
  rw [traceNorm_eq_sqrtRootSum, traceNorm_eq_sqrtRootSum, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv]
  congr 1
  rw [show (Mᴴ * M).submatrix (⇑e) (⇑e) = Matrix.reindex e.symm e.symm (Mᴴ * M) by
        simp [Matrix.reindex_apply], Matrix.charpoly_reindex]

/-- **Uniqueness of the positive-semidefinite square root** (elementary trace argument, no CFC
instance): if `P, Q` are PSD and `P² = Q²`, then `P = Q`. With `D = P − Q`: `PD + DQ = P²−Q² = 0`,
so `tr(DPD) = −tr(DQD)`; both are traces of PSD matrices, hence `≥ 0`, forcing both to `0`; a
trace-zero PSD matrix is `0`, so `√P·D = 0 ⟹ PD = 0` (and `QD = 0`), giving `D² = DP − DQ = 0`
and `D = 0`. -/
theorem posSemidef_eq_of_mul_self_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P Q : Matrix ι ι ℂ} (hP : P.PosSemidef) (hQ : Q.PosSemidef) (h : P * P = Q * Q) : P = Q := by
  have hPh := hP.isHermitian
  have hQh := hQ.isHermitian
  set D := P - Q with hDdef
  have hDh : Dᴴ = D := by rw [hDdef, Matrix.conjTranspose_sub, hPh.eq, hQh.eq]
  have hkey : P * D + D * Q = 0 := by rw [hDdef, Matrix.mul_sub, Matrix.sub_mul, h]; abel
  have hPD : P * D = -(D * Q) := eq_neg_of_add_eq_zero_left hkey
  have hDPD : (D * P * D).PosSemidef := by
    have := hP.conjTranspose_mul_mul_same D; rwa [hDh] at this
  have hDQD : (D * Q * D).PosSemidef := by
    have := hQ.conjTranspose_mul_mul_same D; rwa [hDh] at this
  have htr : (D * P * D).trace = -(D * Q * D).trace := by
    have e1 : D * P * D = -(D * (D * Q)) := by rw [Matrix.mul_assoc, hPD, Matrix.mul_neg]
    rw [e1, Matrix.trace_neg, Matrix.trace_mul_comm D (D * Q)]
  have hDPD0 : (D * P * D).trace = 0 :=
    le_antisymm (by rw [htr]; exact neg_nonpos.mpr hDQD.trace_nonneg) hDPD.trace_nonneg
  have hDQD0 : (D * Q * D).trace = 0 := by
    have := hDPD0; rw [htr, neg_eq_zero] at this; exact this
  have hsqPmul : psdSqrt hP * D = 0 := by
    refine Matrix.conjTranspose_mul_self_eq_zero.mp ?_
    rw [Matrix.conjTranspose_mul, (psdSqrt_isHermitian hP).eq, hDh, Matrix.mul_assoc,
      ← Matrix.mul_assoc (psdSqrt hP) (psdSqrt hP) D, psdSqrt_mul_self hP, ← Matrix.mul_assoc]
    exact (hDPD.trace_eq_zero_iff.mp hDPD0)
  have hsqQmul : psdSqrt hQ * D = 0 := by
    refine Matrix.conjTranspose_mul_self_eq_zero.mp ?_
    rw [Matrix.conjTranspose_mul, (psdSqrt_isHermitian hQ).eq, hDh, Matrix.mul_assoc,
      ← Matrix.mul_assoc (psdSqrt hQ) (psdSqrt hQ) D, psdSqrt_mul_self hQ, ← Matrix.mul_assoc]
    exact (hDQD.trace_eq_zero_iff.mp hDQD0)
  have hPD0 : P * D = 0 := by
    rw [← psdSqrt_mul_self hP, Matrix.mul_assoc, hsqPmul, Matrix.mul_zero]
  have hQD0 : Q * D = 0 := by
    rw [← psdSqrt_mul_self hQ, Matrix.mul_assoc, hsqQmul, Matrix.mul_zero]
  have hDP0 : D * P = 0 := by
    have e : (P * D)ᴴ = D * P := by rw [Matrix.conjTranspose_mul, hPh.eq, hDh]
    rw [← e, hPD0, Matrix.conjTranspose_zero]
  have hDQ0 : D * Q = 0 := by
    have e : (Q * D)ᴴ = D * Q := by rw [Matrix.conjTranspose_mul, hQh.eq, hDh]
    rw [← e, hQD0, Matrix.conjTranspose_zero]
  have hD2 : D * D = 0 := by
    nth_rewrite 2 [hDdef]; rw [Matrix.mul_sub, hDP0, hDQ0, sub_zero]
  have hD0 : D = 0 := by
    rw [← Matrix.conjTranspose_mul_self_eq_zero (A := D), hDh]; exact hD2
  have : P - Q = 0 := by rw [← hDdef]; exact hD0
  exact sub_eq_zero.mp this

/-- **Trace-norm homogeneity under a nonnegative real scalar**: `‖c·M‖₁ = c·‖M‖₁` for `0 ≤ c`.
Via `‖A‖₁ = (tr|A|).re` and `|c·M| = c·|M|` — both `|c·M|` and `c·|M|` are PSD and square to
`(c·M)ᴴ(c·M) = c²·(MᴴM)`, so they coincide by `posSemidef_eq_of_mul_self_eq`. -/
theorem traceNorm_smul_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {c : ℝ} (hc : 0 ≤ c) (M : Matrix ι ι ℂ) :
    traceNorm ((c : ℂ) • M) = c * traceNorm M := by
  have hcC : (0 : ℂ) ≤ (c : ℂ) := Complex.zero_le_real.mpr hc
  have habs : absOp ((c : ℂ) • M) = (c : ℂ) • absOp M := by
    refine posSemidef_eq_of_mul_self_eq (absOp_posSemidef _) ((absOp_posSemidef M).smul hcC) ?_
    rw [absOp_mul_self, Matrix.conjTranspose_smul, smul_mul_smul, smul_mul_smul, absOp_mul_self]
    congr 1
    simp [Complex.conj_ofReal]
  rw [traceNorm_eq_trace_absOp, habs, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul,
    ← traceNorm_eq_trace_absOp]

end SKEFTHawking.QuantumNetwork
