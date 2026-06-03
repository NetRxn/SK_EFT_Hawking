import SKEFTHawking.QuantumNetwork.DiamondSDP
import SKEFTHawking.QuantumNetwork.DiamondNormChoiUpper
import SKEFTHawking.QuantumNetwork.OpNormHolder

/-!
# Toward attainment of the Choi-SDP dual value (Phase 6AI — `≥` direction, foundational lemmas)

Two reusable facts feeding the dual-attainment / strong-duality `≥` argument for
`diamondDist_eq_choiSDP`:

* `trace_ptrace2` — the partial trace `Tr₂` preserves the trace (`tr(Tr₂ W) = tr W`); the
  entrywise identity `(Tr₂ W) a a = ∑_x W (a,x)(a,x)` summed over `a` is the full trace over
  `Fin n × Fin n`.
* `dualObjective_trace_bound` — for a PSD dual witness `W`, the trace is controlled by the dual
  objective: `tr W = tr(Tr₂ W) ≤ card · ‖Tr₂ W‖`. This is the seed of the boundedness half of
  dual-sublevel compactness (`‖Tr₂ W‖ ≤ B ⇒ tr W ≤ card · B`).

The remaining attainment bricks (the `opNorm ≤ traceNorm` Frobenius bridge bounding `‖W‖` itself,
closedness of the feasible cone, finite-dimensional compactness, and `IsCompact.exists_isMinOn`),
followed by the Hahn–Banach separation against the attained primal optimum, complete the
strong-duality `≥` direction `choiDualValue ≤ diamondDist`.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

variable {n : ℕ}

/-- **`‖K‖ ≤ c` from the Loewner bound `K·Kᴴ ⪯ c²·1`** (`c²•1 − K·Kᴴ ⪰ 0`, `c ≥ 0`). The `c = 1`
case is `opNorm_le_one_of_mul_conjTranspose_le_one`; the general `c` is the same EuclideanLin
operator picture: `‖K‖ = ‖Kᴴ‖ = ‖toEuclideanCLM Kᴴ‖`, reduce by `opNNNorm_le_iff` to
`∀ x, ‖toEuclideanCLM Kᴴ x‖ ≤ c‖x‖`, and `‖toEuclideanCLM Kᴴ x‖² = re⟪x,(KKᴴ)x⟫ ≤ c²‖x‖²` from
`Matrix.isPositive_toEuclideanLin_iff` on `c²•1 − KKᴴ`. -/
theorem opNorm_le_of_mul_conjTranspose_le_sq {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {K : Matrix ι ι ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : (((c : ℂ) ^ 2) • (1 : Matrix ι ι ℂ) - K * Kᴴ).PosSemidef) : ‖K‖ ≤ c := by
  have hKstar : ‖K‖ = ‖Kᴴ‖ := by rw [← Matrix.star_eq_conjTranspose, norm_star]
  rw [hKstar, show c = ((c.toNNReal : ℝ)) from (Real.coe_toNNReal c hc).symm, ← coe_nnnorm,
    NNReal.coe_le_coe, Matrix.cstar_nnnorm_def, ContinuousLinearMap.opNNNorm_le_iff]
  intro x
  rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_mul, coe_nnnorm, Real.coe_toNNReal c hc]
  set S := Matrix.toEuclideanCLM (𝕜 := ℂ) Kᴴ with hS
  have hadj : ContinuousLinearMap.adjoint S = Matrix.toEuclideanCLM (𝕜 := ℂ) K := by
    rw [hS, ← ContinuousLinearMap.star_eq_adjoint, ← map_star]
    congr 1; rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  have hmul : (toEuclideanLin (K * Kᴴ)) x = (ContinuousLinearMap.adjoint S) (S x) := by
    rw [hadj, hS]
    show (Matrix.toEuclideanCLM (𝕜 := ℂ) (K * Kᴴ)) x = _
    rw [map_mul, ContinuousLinearMap.mul_apply]
  have hpos := (Matrix.isPositive_toEuclideanLin_iff (A := ((c : ℂ) ^ 2) • 1 - K * Kᴴ)).mpr h
  have h0 := hpos.2 x
  rw [map_sub, LinearMap.sub_apply, inner_sub_left, hmul, ContinuousLinearMap.adjoint_inner_left,
    map_smul, LinearMap.smul_apply,
    show (toEuclideanLin (1 : Matrix ι ι ℂ)) x = x from by simp, inner_smul_left,
    map_pow, Complex.conj_ofReal, ← Complex.ofReal_pow, map_sub,
    show ((c ^ 2 : ℝ) : ℂ) = RCLike.ofReal (c ^ 2) from rfl,
    RCLike.re_ofReal_mul, inner_self_eq_norm_sq, inner_self_eq_norm_sq] at h0
  have hsq : ‖S x‖ ^ 2 ≤ c ^ 2 * ‖x‖ ^ 2 := by linarith [h0]
  calc ‖S x‖ = Real.sqrt (‖S x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (c ^ 2 * ‖x‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = c * ‖x‖ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hc, Real.sqrt_sq (norm_nonneg _)]

/-- **Operator norm of a PSD matrix is bounded by its trace norm:** `‖W‖ ≤ traceNorm W` for
`W ⪰ 0` (the largest eigenvalue is at most the eigenvalue sum). Built from the Loewner bound
`W*W ⪯ (traceNorm W)²•1` (eigenvalues `λᵢ² ≤ (∑ⱼ λⱼ)²` since `0 ≤ λᵢ ≤ ∑ⱼ λⱼ`, via CFC) and
`opNorm_le_of_mul_conjTranspose_le_sq` with `Wᴴ = W`. -/
theorem l2opNorm_le_traceNorm_psd {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {W : Matrix ι ι ℂ} (hW : W.PosSemidef) : ‖W‖ ≤ traceNorm W := by
  have hHerm := hW.isHermitian
  have hcnn : 0 ≤ traceNorm W := traceNorm_nonneg W
  have hsumeig : ∑ i, hHerm.eigenvalues i = traceNorm W := by
    have h2 : (W.trace).re = ∑ i, hHerm.eigenvalues i := by
      rw [hHerm.trace_eq_sum_eigenvalues, Complex.re_sum]; simp
    rw [traceNorm_posSemidef hW, h2]
  have heigle : ∀ i, hHerm.eigenvalues i ≤ traceNorm W := fun i => by
    rw [← hsumeig]
    exact Finset.single_le_sum (fun j _ => hW.eigenvalues_nonneg j) (Finset.mem_univ i)
  apply opNorm_le_of_mul_conjTranspose_le_sq hcnn
  rw [hHerm.eq]
  have hcfc : ((traceNorm W : ℂ) ^ 2) • (1 : Matrix ι ι ℂ) - W * W
      = hHerm.cfc (fun x => (traceNorm W) ^ 2 - x ^ 2) := by
    rw [← cfc_sub hHerm (fun _ => (traceNorm W) ^ 2) (fun x => x ^ 2),
      cfc_const hHerm ((traceNorm W) ^ 2), ← isHermitian_mul_self_eq_cfc_sq hHerm,
      Complex.ofReal_pow]
  rw [hcfc]
  exact cfc_posSemidef hHerm fun i => by
    have h1 := heigle i; have h2 := hW.eigenvalues_nonneg i; nlinarith

/-- **Partial trace preserves the trace:** `tr(Tr₂ W) = tr W`. The diagonal entry
`(Tr₂ W) a a = ∑_x W (a,x)(a,x)`, and summing over `a` re-assembles the trace over `Fin n × Fin n`
(`Fintype.sum_prod_type`). -/
theorem trace_ptrace2 (W : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    (ptrace2 W).trace = W.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, ptrace2, Fintype.sum_prod_type]

/-- **Trace control by the dual objective.** For a positive-semidefinite dual witness `W`, the
trace is bounded by the dual objective `‖Tr₂ W‖` up to the dimension factor:
`tr W = tr(Tr₂ W) ≤ card · ‖Tr₂ W‖` (real parts). Uses `traceNorm_posSemidef`
(PSD ⇒ `traceNorm = Re tr`) on both `W` and `Tr₂ W`, the partial-trace trace identity, and the
shipped `traceNorm_le_card_mul_l2opNorm`. -/
theorem dualObjective_trace_bound [NeZero n]
    {W : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ} (hW : W.PosSemidef) :
    (W.trace).re ≤ (Fintype.card (Fin n) : ℝ) * ‖ptrace2 W‖ := by
  have hpt : (ptrace2 W).PosSemidef := ptrace2_posSemidef hW
  calc (W.trace).re = (ptrace2 W).trace.re := by rw [trace_ptrace2]
    _ = traceNorm (ptrace2 W) := (traceNorm_posSemidef hpt).symm
    _ ≤ (Fintype.card (Fin n) : ℝ) * ‖ptrace2 W‖ := traceNorm_le_card_mul_l2opNorm (ptrace2 W)

/-- **Dual-witness norm bound (the boundedness half of dual-sublevel compactness).** A PSD dual
witness `W` whose objective `‖Tr₂ W‖` is at most `B` is itself norm-bounded: `‖W‖ ≤ card · B`.
Chains `l2opNorm_le_traceNorm_psd` (op-norm ≤ trace-norm for PSD) with the dual-objective trace
control `dualObjective_trace_bound`. -/
theorem l2opNorm_bound_of_dual_feasible [NeZero n]
    {W : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ} (hW : W.PosSemidef) {B : ℝ}
    (hB : ‖ptrace2 W‖ ≤ B) : ‖W‖ ≤ (Fintype.card (Fin n) : ℝ) * B := by
  calc ‖W‖ ≤ traceNorm W := l2opNorm_le_traceNorm_psd hW
    _ = (W.trace).re := traceNorm_posSemidef hW
    _ ≤ (Fintype.card (Fin n) : ℝ) * ‖ptrace2 W‖ := dualObjective_trace_bound hW
    _ ≤ (Fintype.card (Fin n) : ℝ) * B := by
        apply mul_le_mul_of_nonneg_left hB (by positivity)

end SKEFTHawking.QuantumNetwork
