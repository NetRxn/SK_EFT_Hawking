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

/-- **The positive-semidefinite set is closed** (Frobenius topology): an intersection of the
closed Hermitian condition and the closed quadratic-form-nonneg conditions. Mirrors
`isClosed_isDensityOperator` without the trace-`1` constraint. -/
theorem isClosed_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι] :
    IsClosed {W : Matrix ι ι ℂ | W.PosSemidef} := by
  have key : {W : Matrix ι ι ℂ | W.PosSemidef}
      = {W | Wᴴ = W} ∩ ⋂ x : ι → ℂ, {W | 0 ≤ star x ⬝ᵥ W.mulVec x} := by
    ext W
    simp only [Matrix.posSemidef_iff_dotProduct_mulVec, Matrix.IsHermitian,
      Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [key]
  refine IsClosed.inter (isClosed_eq (by fun_prop) continuous_id) (isClosed_iInter fun x => ?_)
  exact isClosed_complex_nonneg.preimage (by fun_prop)

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

/-- **The second-factor partial trace is continuous** (each output entry is a finite sum of input
coordinate projections). -/
theorem continuous_ptrace2 :
    Continuous (ptrace2 : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) := by
  apply continuous_matrix
  intro a b
  simp only [ptrace2]
  exact continuous_finset_sum _ fun x _ => continuous_apply_apply (a, x) (b, x)

/-- **The Choi-SDP dual infimum is attained.** There is a dual-feasible witness `W*` (`W* ⪰ 0`,
`W* ⪰ C`) whose objective `‖Tr₂ W*‖` equals `choiDualValue`. The dual sublevel
`{W ⪰ 0, W ⪰ C, ‖Tr₂ W‖ ≤ ‖Tr₂ C₊‖}` is closed (PSD-set closedness + continuity of `‖Tr₂ ·‖`),
bounded (`l2opNorm_bound_of_dual_feasible`), hence compact; the continuous objective attains its
minimum there, and that minimum is the infimum over all feasible witnesses. -/
theorem exists_choiDualValue_eq {m : ℕ} [NeZero n] (K₁ K₂ : Fin m → Matrix (Fin n) (Fin n) ℂ) :
    ∃ W : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ, W.PosSemidef ∧
      (W - (choiMatrix (krausMap K₁) - choiMatrix (krausMap K₂))).PosSemidef ∧
      ‖ptrace2 W‖ = choiDualValue K₁ K₂ := by
  set C := choiMatrix (krausMap K₁) - choiMatrix (krausMap K₂) with hC
  set Cp := posPart (choiDiff_isHermitian K₁ K₂) with hCp
  have hCp_psd : Cp.PosSemidef := posPart_posSemidef _
  have hCp_feas : (Cp - C).PosSemidef := posPart_choiDiff_sub_posSemidef K₁ K₂
  set B₀ := ‖ptrace2 Cp‖ with hB₀
  -- the dual sublevel
  set S : Set (Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :=
    {W | W.PosSemidef ∧ (W - C).PosSemidef ∧ ‖ptrace2 W‖ ≤ B₀} with hS
  have hCpS : Cp ∈ S := ⟨hCp_psd, hCp_feas, le_refl _⟩
  have hSne : S.Nonempty := ⟨Cp, hCpS⟩
  have hS_closed : IsClosed S := by
    have heq : S = ({W : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ | W.PosSemidef}
        ∩ {W | (W - C).PosSemidef}) ∩ {W | ‖ptrace2 W‖ ≤ B₀} := by
      ext W; simp only [hS, Set.mem_inter_iff, Set.mem_setOf_eq, and_assoc]
    rw [heq]
    exact ((isClosed_posSemidef).inter (isClosed_posSemidef.preimage (by fun_prop))).inter
      (isClosed_le continuous_ptrace2.norm continuous_const)
  have hS_bdd : Bornology.IsBounded S := by
    refine (Metric.isBounded_iff_subset_closedBall 0).mpr
      ⟨(Fintype.card (Fin n) : ℝ) * B₀, fun W hW => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact l2opNorm_bound_of_dual_feasible hW.1 hW.2.2
  have hS_compact : IsCompact S := Metric.isCompact_of_isClosed_isBounded hS_closed hS_bdd
  obtain ⟨W, hWS, hWmin⟩ :=
    hS_compact.exists_isMinOn hSne (Continuous.continuousOn continuous_ptrace2.norm)
  refine ⟨W, hWS.1, hWS.2.1, le_antisymm ?_ ?_⟩
  · refine le_csInf (choiDualValue_set_nonempty K₁ K₂) ?_
    rintro r ⟨V, hV, hVC, rfl⟩
    by_cases hVB : ‖ptrace2 V‖ ≤ B₀
    · exact isMinOn_iff.mp hWmin V ⟨hV, hVC, hVB⟩
    · exact hWS.2.2.trans (not_le.mp hVB).le
  · exact csInf_le ⟨0, by rintro r ⟨V, _, _, rfl⟩; exact norm_nonneg _⟩
      ⟨W, hWS.1, hWS.2.1, rfl⟩

/-- **The input marginal of a density operator is Loewner-bounded by `1`:** `inMarginal ρ ⪯ 1`
for `IsDensityOperator ρ`. Its eigenvalues are at most `‖inMarginal ρ‖ ≤ traceNorm = tr ρ = 1`
(`l2opNorm_le_traceNorm_psd`), so `1 − inMarginal ρ = cfc(1 − x)` is PSD. Feeds the dual-feasibility
brick of the strong-duality `≥` direction (the Hölder step's tightness witness). -/
theorem inMarginal_le_one [NeZero n] {ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ}
    (hρ : IsDensityOperator ρ) :
    ((1 : Matrix (Fin n) (Fin n) ℂ) - inMarginal ρ).PosSemidef := by
  have hpsd : (inMarginal ρ).PosSemidef := inMarginal_posSemidef hρ.1
  have hHerm := hpsd.isHermitian
  have hnorm : ‖inMarginal ρ‖ ≤ 1 := by
    calc ‖inMarginal ρ‖ ≤ traceNorm (inMarginal ρ) := l2opNorm_le_traceNorm_psd hpsd
      _ = (inMarginal ρ).trace.re := traceNorm_posSemidef hpsd
      _ = 1 := by rw [trace_inMarginal, hρ.2, Complex.one_re]
  have hc : hHerm.cfc (fun x => 1 - x) = (1 : Matrix (Fin n) (Fin n) ℂ) - inMarginal ρ := by
    rw [← cfc_sub hHerm (fun _ => (1 : ℝ)) (fun x => x), cfc_id hHerm, cfc_const hHerm 1,
      Complex.ofReal_one, one_smul]
  rw [← hc]
  exact cfc_posSemidef hHerm fun i => by
    have := (eigenvalue_le_l2opNorm hHerm i).trans hnorm; linarith

/-- **Strong-duality reduction.** The zero-gap `≥` direction `choiDualValue ≤ diamondDist` reduces
to exhibiting a *single* dual-feasible witness `W` whose objective is below the diamond distance
(`csInf_le`, the value set bounded below by `0`). This isolates the entire remaining content of
`diamondDist_eq_choiSDP` into the Watrous optimal-witness existence. -/
theorem choiDualValue_le_of_witness {m : ℕ} [NeZero n] {K₁ K₂ : Fin m → Matrix (Fin n) (Fin n) ℂ}
    (hW : ∃ W : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ, W.PosSemidef ∧
      (W - (choiMatrix (krausMap K₁) - choiMatrix (krausMap K₂))).PosSemidef ∧
      ‖ptrace2 W‖ ≤ diamondDist K₁ K₂) :
    choiDualValue K₁ K₂ ≤ diamondDist K₁ K₂ := by
  obtain ⟨W, hWpsd, hWC, hWle⟩ := hW
  exact le_trans (csInf_le ⟨0, by rintro r ⟨V, _, _, rfl⟩; exact norm_nonneg _⟩
    ⟨W, hWpsd, hWC, rfl⟩) hWle

end SKEFTHawking.QuantumNetwork
