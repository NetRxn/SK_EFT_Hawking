import SKEFTHawking.QuantumNetwork.FidelityForwardBound
import SKEFTHawking.QuantumNetwork.DiamondNormAttainment
import SKEFTHawking.QuantumNetwork.TraceNormCauchySchwarz

/-!
# Alberti attainment for positive-SEMIdefinite states (Phase 6AJ.4 — unconditional fidelity DP)

Relaxes the attainment half of the Alberti characterization
`exists_block_re_trace_eq_sqrtFidelity` from positive-DEFINITE to positive-SEMIdefinite `ρ,σ`. This is
the **linchpin** that makes fidelity data processing fully unconditional (all density operators / all
CPTP networks): the forward Alberti bound is already PSD-valid (`re_trace_block_le_sqrtFidelity_psd`),
so once attainment is PSD-valid too, the single-step DP, Loewner monotonicity, and the chain all drop
the full-rank hypotheses.

The optimal witness is `X* = √ρ·W·√σ` with `W` the **unitary** maximizer of `Re tr(·M)`,
`M = √σ√ρ`. For invertible `M` this is the polar unitary (`exists_unitary_traceNorm_eq_re_trace`); for
singular `M` (the PSD-input case) the partial-isometry polar still *extends* to a unitary, obtained
here as a **compactness limit**: perturb `M` to invertible, take the polar unitary `W_ε`, and extract a
convergent subsequence from the (closed + bounded ⟹ compact) unitary set. The block-PSD then comes from
the factorization `[[1,W],[Wᴴ,1]] = A·Aᴴ` (using `WᴴW=1`) conjugated by `diag(√ρ,√σ)` — **no Schur
complement on `ρ,σ`, no invertibility**.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix Filter Topology
open scoped ComplexOrder

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **General unitary polar witness.** For *any* matrix `M` (no invertibility) there is a unitary `W`
(`Wᴴ W = 1`) with `‖M‖₁ = Re tr(W·M)`. For singular `M` the polar partial isometry extends to a
unitary, obtained as a compactness limit of the invertible-case polar unitaries: perturb `M` to
invertible (`eventually_isUnit_perturb`), take `W_ε` from `exists_unitary_traceNorm_eq_re_trace`, and
extract a convergent subsequence from the compact unitary set `{W : Wᴴ W = 1}`. -/
theorem exists_unitary_traceNorm_eq_re_trace_general (M : Matrix ι ι ℂ) :
    ∃ W : Matrix ι ι ℂ, Wᴴ * W = 1 ∧ traceNorm M = (W * M).trace.re := by
  classical
  set Mk : ℕ → Matrix ι ι ℂ := fun k => M + diagonal (fun _ : ι => ((k : ℂ) + 1)⁻¹) with hMk
  have hc : Tendsto (fun k : ℕ => ((k : ℂ) + 1)⁻¹) atTop (𝓝 0) := by
    have hr : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hr
    simp only [Function.comp_def, Complex.ofReal_zero] at h2
    exact h2.congr (fun n => by push_cast; rw [one_div])
  have hMtend : Tendsto Mk atTop (𝓝 M) := by
    have hdiagc : Continuous fun z : ℂ => diagonal (fun _ : ι => z) :=
      Continuous.matrix_diagonal (continuous_pi fun _ => continuous_id)
    have hd0 : Tendsto (fun k : ℕ => diagonal (fun _ : ι => ((k : ℂ) + 1)⁻¹)) atTop (𝓝 0) := by
      have := (hdiagc.tendsto 0).comp hc; simpa using this
    simpa [hMk] using tendsto_const_nhds.add hd0
  set Wseq : ℕ → Matrix ι ι ℂ :=
    fun k => if h : IsUnit (Mk k) then (exists_unitary_traceNorm_eq_re_trace h).choose else 1
    with hWseq
  have hWunit : ∀ k, (Wseq k)ᴴ * Wseq k = 1 := by
    intro k; by_cases h : IsUnit (Mk k)
    · simp only [hWseq, dif_pos h]; exact (exists_unitary_traceNorm_eq_re_trace h).choose_spec.1
    · simp only [hWseq, dif_neg h, Matrix.conjTranspose_one, Matrix.one_mul]
  have hWtr : ∀ᶠ k in atTop, traceNorm (Mk k) = (Wseq k * Mk k).trace.re := by
    filter_upwards [eventually_isUnit_perturb M] with k hk
    have hk' : IsUnit (Mk k) := hk
    simp only [hWseq, dif_pos hk']
    exact (exists_unitary_traceNorm_eq_re_trace hk').choose_spec.2
  set Kset : Set (Matrix ι ι ℂ) := {W | Wᴴ * W = 1} with hKset
  have hKclosed : IsClosed Kset :=
    isClosed_eq ((continuous_id.matrix_conjTranspose).matrix_mul continuous_id) continuous_const
  have hKbdd : Bornology.IsBounded Kset := by
    refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨Real.sqrt (Fintype.card ι), ?_⟩
    intro W hW
    rw [Metric.mem_closedBall, dist_zero_right]
    have hfs := re_trace_conjTranspose_mul_self_eq_frobenius_sq W
    rw [hKset, Set.mem_setOf_eq] at hW
    rw [hW] at hfs
    have hsq : ‖W‖ ^ 2 = (Fintype.card ι : ℝ) := by rw [← hfs, Matrix.trace_one]; simp
    nlinarith [norm_nonneg W, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (Fintype.card ι : ℝ)),
      Real.sqrt_nonneg (Fintype.card ι : ℝ)]
  have hKcompact : IsCompact Kset := Metric.isCompact_of_isClosed_isBounded hKclosed hKbdd
  obtain ⟨Wstar, hWstarK, φ, hφ, hWφ⟩ := hKcompact.tendsto_subseq (fun k => hWunit k)
  refine ⟨Wstar, hWstarK, ?_⟩
  have hMφ : Tendsto (fun k => Mk (φ k)) atTop (𝓝 M) := hMtend.comp hφ.tendsto_atTop
  have hL : Tendsto (fun k => traceNorm (Mk (φ k))) atTop (𝓝 (traceNorm M)) :=
    (continuous_traceNorm.tendsto M).comp hMφ
  have hR : Tendsto (fun k => (Wseq (φ k) * Mk (φ k)).trace.re) atTop (𝓝 (Wstar * M).trace.re) :=
    ((Complex.continuous_re.comp continuous_id.matrix_trace).tendsto (Wstar * M)).comp (hWφ.mul hMφ)
  have heq : ∀ᶠ k in atTop, traceNorm (Mk (φ k)) = (Wseq (φ k) * Mk (φ k)).trace.re :=
    hφ.tendsto_atTop.eventually hWtr
  exact tendsto_nhds_unique hL (hR.congr' (heq.mono fun k h => h.symm))

omit [Nonempty ι] in
/-- `[[1,W],[Wᴴ,1]] ⪰ 0` for a unitary `W` (`WᴴW=1`), via the factorization
`[[1,W],[Wᴴ,WᴴW]] = A·Aᴴ` with `A = [[1,0],[Wᴴ,0]]`. -/
theorem fidelityBlock_one_unitary_posSemidef {W : Matrix ι ι ℂ} (hW : Wᴴ * W = 1) :
    (fidelityBlock (1 : Matrix ι ι ℂ) W 1).PosSemidef := by
  have hfac : fidelityBlock (1 : Matrix ι ι ℂ) W 1
      = (fromBlocks 1 0 Wᴴ 0) * (fromBlocks 1 0 Wᴴ 0)ᴴ := by
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    unfold fidelityBlock
    simp only [Matrix.conjTranspose_one, Matrix.conjTranspose_zero,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_one, Matrix.mul_zero, Matrix.one_mul,
      add_zero, hW]
  rw [hfac]; exact Matrix.posSemidef_self_mul_conjTranspose _

omit [DecidableEq ι] [Nonempty ι] in
/-- Conjugating a fidelity block by the block-diagonal `diag(P,Q)` (`P,Q` Hermitian):
`diag(P,Q)·[[ρ,X],[Xᴴ,σ]]·diag(P,Q)ᴴ = [[PρP, PXQ],[QXᴴP, QσQ]]`. -/
theorem diagBlock_conj_fidelityBlock {P Q : Matrix ι ι ℂ} (hP : Pᴴ = P) (hQ : Qᴴ = Q)
    (ρ X σ : Matrix ι ι ℂ) :
    fromBlocks P 0 0 Q * fidelityBlock ρ X σ * (fromBlocks P 0 0 Q)ᴴ
      = fidelityBlock (P * ρ * P) (P * X * Q) (Q * σ * Q) := by
  rw [Matrix.fromBlocks_conjTranspose, hP, hQ]
  unfold fidelityBlock
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_assoc, Matrix.conjTranspose_mul, hP, hQ]

/-- **Attainment of the Alberti maximum for positive-SEMIdefinite states.** For PSD `ρ,σ` the polar
witness `X* = √ρ·W·√σ` (`W` the general unitary polar witness of `√σ√ρ`) is block-feasible with
`Re tr X* = F(ρ,σ)`. The PosDef restriction of `exists_block_re_trace_eq_sqrtFidelity` is removed:
block-PSD via the congruence `diag(√ρ,√σ)·[[1,W],[Wᴴ,1]]·diag(√ρ,√σ)ᴴ` (no Schur, no invertibility). -/
theorem exists_block_re_trace_eq_sqrtFidelity_psd {ρ σ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    ∃ X, (fidelityBlock ρ X σ).PosSemidef ∧ X.trace.re = sqrtFidelity hρ hσ := by
  obtain ⟨W, hWW, hWtr⟩ := exists_unitary_traceNorm_eq_re_trace_general (psdSqrt hσ * psdSqrt hρ)
  refine ⟨psdSqrt hρ * W * psdSqrt hσ, ?_, ?_⟩
  · have hcong := diagBlock_conj_fidelityBlock (psdSqrt_isHermitian hρ).eq (psdSqrt_isHermitian hσ).eq
      1 W 1
    rw [Matrix.mul_one, Matrix.mul_one, psdSqrt_mul_self, psdSqrt_mul_self] at hcong
    rw [← hcong]
    exact posSemidef_unitary_conj _ (fidelityBlock_one_unitary_posSemidef hWW)
  · rw [sqrtFidelity, hWtr]
    congr 1
    rw [show psdSqrt hρ * W * psdSqrt hσ = psdSqrt hρ * (W * psdSqrt hσ) by noncomm_ring,
      Matrix.trace_mul_comm,
      show W * psdSqrt hσ * psdSqrt hρ = W * (psdSqrt hσ * psdSqrt hρ) by noncomm_ring]

end SKEFTHawking.QuantumNetwork
