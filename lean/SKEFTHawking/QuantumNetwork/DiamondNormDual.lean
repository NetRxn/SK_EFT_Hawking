import SKEFTHawking.QuantumNetwork.DiamondNormChoiUpper

/-!
# Watrous dual (weak-duality) upper bound on the diamond distance (Phase 6AG, Ask 2 tight upper)

The diamond-distance *lower* bounds (`diamondDist_ge_choi_traceNorm`, `diamondDist_ge_maxEntangled`)
and the loose Choi operator-norm *upper* bound (`diamondDist_le_choi_opNorm`, `≤ n‖C‖`) leave the
two-sided envelope wide. The genuinely tight upper bound is the Watrous semidefinite-program dual.
Its *strong*-duality (primal = dual) form needs conic strong duality (Slater / a zero-gap SDP
theorem), which is absent from Mathlib at this pin. **But the upper-bounding direction is *weak*
duality**, which needs none of that: *any* dual-feasible witness gives an upper bound.

Concretely, for the Choi difference `C = J(Φ₁) − J(Φ₂)`, any Hermitian witness `W` with `W ≥ 0`
and `W ≥ C` (Loewner order, i.e. `W − C` PSD) yields

  `diamondDist Φ₁ Φ₂ ≤ ‖W's input-marginal‖`.

The shipped `diamondDist_le_choi_opNorm` (`≤ n‖C‖`) is exactly this dual evaluated at the *trivial*
witness `W = ‖C‖·1`; a non-trivial witness is strictly tighter, and the *optimal* witness for a
Pauli-covariant channel reproduces the lower bound, closing the envelope to an exact value with no
twirl machinery — one only exhibits `W`.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; zero project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {n m : ℕ}

/-- **Loewner monotonicity of the Choi pairing.** If `C ≤ W` in the Loewner order (`W − C` PSD)
and the contraction `M` is positive semidefinite, then `Re tr(C·M) ≤ Re tr(W·M)`. This is the
weak-duality step: replacing the Choi difference by a dominating witness can only raise the
distinguishability pairing. -/
theorem re_trace_mul_le_of_loewner {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C W M : Matrix ι ι ℂ} (hCW : (W - C).PosSemidef) (hM : M.PosSemidef) :
    (C * M).trace.re ≤ (W * M).trace.re := by
  have h0 : (0 : ℂ) ≤ ((W - C) * M).trace := trace_mul_nonneg hCW hM
  have hsplit : ((W - C) * M).trace = (W * M).trace - (C * M).trace := by
    rw [sub_mul, Matrix.trace_sub]
  rw [hsplit] at h0
  have hre : 0 ≤ ((W * M).trace - (C * M).trace).re := (Complex.le_def.mp h0).1
  rw [Complex.sub_re] at hre
  linarith

/-- Partial trace over the **second** tensor factor: `(ptrace2 W) a b = ∑ x, W (a,x) (b,x)`. -/
noncomputable def ptrace2 (W : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := fun a b => ∑ x, W (a, x) (b, x)

/-- The input marginal of `ρ` that pairs against `ptrace2 W` in the dual bound:
`(inMarginal ρ) a b = ∑ α, ρ (b,α) (a,α)` (the entrywise conjugate of the second-factor partial
trace of a Hermitian `ρ`). -/
noncomputable def inMarginal (ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := fun a b => ∑ α, ρ (b, α) (a, α)

open scoped Kronecker in
/-- `M(1,ρ) = choiContraction 1 ρ` is `inMarginal ρ ⊗ 1` (identity on the output factor). -/
theorem choiContraction_one_eq (ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    choiContraction 1 ρ = inMarginal ρ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) := by
  ext p q
  simp only [choiContraction, Matrix.one_apply, inMarginal, Matrix.kroneckerMap_apply,
    Prod.mk.injEq, ite_and]
  rw [Finset.sum_comm]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [mul_comm]
  by_cases h : p.2 = q.2 <;> simp [h]

open scoped Kronecker in
/-- Standard partial-trace identity: `tr(W · (G ⊗ 1)) = tr(ptrace2 W · G)`. -/
theorem trace_mul_kronecker_one (W : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (G : Matrix (Fin n) (Fin n) ℂ) :
    (W * (G ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))).trace = (ptrace2 W * G).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, ptrace2,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

/-- **Linchpin contraction identity.** `tr(W · M(1,ρ)) = tr(ptrace2 W · inMarginal ρ)`. -/
theorem trace_mul_choiContraction_one (W ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    (W * choiContraction 1 ρ).trace = (ptrace2 W * inMarginal ρ).trace := by
  rw [choiContraction_one_eq, trace_mul_kronecker_one]

/-- The isometric embedding `a ↦ (a, x)` of the first factor. -/
noncomputable def embed2 (x : Fin n) : Matrix (Fin n × Fin n) (Fin n) ℂ :=
  fun p a => if p = (a, x) then 1 else 0

theorem ptrace2_eq_sum_conj (ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    ptrace2 ρ = ∑ x, (embed2 x)ᴴ * ρ * (embed2 x) := by
  ext a b
  simp only [ptrace2, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, embed2]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [apply_ite (star : ℂ → ℂ), star_one, star_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_ite, mul_one, mul_zero]

theorem ptrace2_posSemidef {ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ} (hρ : ρ.PosSemidef) :
    (ptrace2 ρ).PosSemidef := by
  rw [ptrace2_eq_sum_conj]
  exact Matrix.posSemidef_sum _ fun x _ => hρ.conjTranspose_mul_mul_same (embed2 x)

theorem inMarginal_eq_transpose (ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    inMarginal ρ = (ptrace2 ρ)ᵀ := by
  ext a b; simp only [inMarginal, ptrace2, Matrix.transpose_apply]

theorem inMarginal_posSemidef {ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ} (hρ : ρ.PosSemidef) :
    (inMarginal ρ).PosSemidef := by
  rw [inMarginal_eq_transpose]; exact (ptrace2_posSemidef hρ).transpose

theorem trace_inMarginal (ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    (inMarginal ρ).trace = ρ.trace := by
  simp only [inMarginal, Matrix.trace, Matrix.diag_apply]
  rw [Fintype.sum_prod_type]

/-- `choiContraction` is additive (hence subtractive) in its first argument. -/
theorem choiContraction_sub (W W' ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    choiContraction (W - W') ρ = choiContraction W ρ - choiContraction W' ρ := by
  ext p q
  simp only [choiContraction, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- **`P ≤ 1` step.** For `W ≥ 0`, `1 − P ≥ 0`, `ρ ≥ 0`, replacing the projection `P` by the
identity can only raise the dual pairing: `Re tr(W·M(P,ρ)) ≤ Re tr(W·M(1,ρ))`. -/
theorem re_trace_mul_choiContraction_proj_le_one
    {W P ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ} (hW : W.PosSemidef)
    (hP1 : ((1 : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) - P).PosSemidef) (hρ : ρ.PosSemidef) :
    (W * choiContraction P ρ).trace.re ≤ (W * choiContraction 1 ρ).trace.re := by
  have h0 : (0 : ℂ) ≤ (W * choiContraction (1 - P) ρ).trace :=
    trace_mul_nonneg hW (choiContraction_posSemidef hP1 hρ)
  have hsplit : (W * choiContraction (1 - P) ρ).trace
      = (W * choiContraction 1 ρ).trace - (W * choiContraction P ρ).trace := by
    rw [choiContraction_sub, mul_sub, Matrix.trace_sub]
  rw [hsplit] at h0
  have hre : 0 ≤ ((W * choiContraction 1 ρ).trace - (W * choiContraction P ρ).trace).re :=
    (Complex.le_def.mp h0).1
  rw [Complex.sub_re] at hre; linarith

/-- **Watrous weak-dual upper bound on the diamond distance.** For any Hermitian witness `W` with
`W ≥ 0` and `W ≥ C` (Loewner, `C = J(Φ₁) − J(Φ₂)`), the diamond distance is bounded by the
operator norm of `W`'s second-factor partial trace:

  `diamondDist Φ₁ Φ₂ ≤ ‖ptrace2 W‖`.

This is *weak* duality — no conic strong duality is used. The shipped `diamondDist_le_choi_opNorm`
(`≤ n‖C‖`) is the special case `W = ‖C‖·1` (then `ptrace2 W = n‖C‖·1`); a tighter witness gives a
tighter bound, and the optimal witness for a covariant channel closes the envelope exactly. -/
theorem diamondDist_le_dual_witness [NeZero n]
    {K₁ K₂ : Fin m → Matrix (Fin n) (Fin n) ℂ}
    (hK₁ : IsKrausChannel K₁) (hK₂ : IsKrausChannel K₂)
    {W : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ} (hW : W.PosSemidef)
    (hWC : (W - (choiMatrix (krausMap K₁) - choiMatrix (krausMap K₂))).PosSemidef) :
    diamondDist K₁ K₂ ≤ ‖ptrace2 W‖ := by
  set C := choiMatrix (krausMap K₁) - choiMatrix (krausMap K₂) with hCdef
  refine Real.sSup_le ?_ (norm_nonneg _)
  rintro d ⟨ρ, hρ, rfl⟩
  set T := krausMap (tensorKraus K₁) ρ - krausMap (tensorKraus K₂) ρ with hTdef
  have hTh : T.IsHermitian :=
    (krausMap_isHermitian _ hρ.1.isHermitian).sub (krausMap_isHermitian _ hρ.1.isHermitian)
  have hT0 : T.trace.re = 0 := by
    rw [hTdef, Matrix.trace_sub, trace_krausMap (isKrausChannel_tensorKraus hK₁),
      trace_krausMap (isKrausChannel_tensorKraus hK₂), sub_self, Complex.zero_re]
  set P := hTh.cfc (fun x => if 0 < x then (1 : ℝ) else 0) with hPdef
  have hPpsd : P.PosSemidef :=
    cfc_posSemidef hTh fun i => by by_cases h : 0 < hTh.eigenvalues i <;> simp [h]
  have hP1 : ((1 : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) - P).PosSemidef := by
    have hc1 : hTh.cfc (fun _ => (1 : ℝ)) = 1 := by rw [cfc_const]; simp
    have h1 : (1 : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) - P
        = hTh.cfc (fun x => 1 - if 0 < x then (1 : ℝ) else 0) := by
      rw [hPdef, ← hc1, cfc_sub hTh]
    rw [h1]
    exact cfc_posSemidef hTh fun i => by by_cases h : 0 < hTh.eigenvalues i <;> simp [h]
  have hchain : eigPosSum hTh ≤ ‖ptrace2 W‖ := by
    rw [eigPosSum_eq_re_trace_posProj, ← hPdef, hTdef, trace_mul_krausMap_sub, ← hCdef]
    calc (C * choiContraction P ρ).trace.re
        ≤ (W * choiContraction P ρ).trace.re :=
          re_trace_mul_le_of_loewner hWC (choiContraction_posSemidef hPpsd hρ.1)
      _ ≤ (W * choiContraction 1 ρ).trace.re :=
          re_trace_mul_choiContraction_proj_le_one hW hP1 hρ.1
      _ = (ptrace2 W * inMarginal ρ).trace.re := by rw [trace_mul_choiContraction_one]
      _ ≤ ‖ptrace2 W‖ * (inMarginal ρ).trace.re :=
          re_trace_mul_le_l2opNorm_mul_trace (ptrace2_posSemidef hW).isHermitian
            (inMarginal_posSemidef hρ.1)
      _ = ‖ptrace2 W‖ := by rw [trace_inMarginal, hρ.2, Complex.one_re, mul_one]
  unfold traceDist
  rw [← hTdef, traceNorm_hermitian_eq hTh, hT0, sub_zero,
    show (1 : ℝ) / 2 * (2 * eigPosSum hTh) = eigPosSum hTh by ring]
  exact hchain

end SKEFTHawking.QuantumNetwork
