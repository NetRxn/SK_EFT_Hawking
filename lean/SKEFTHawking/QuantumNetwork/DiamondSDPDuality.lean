import SKEFTHawking.QuantumNetwork.DiamondSDPCone
import SKEFTHawking.QuantumNetwork.DiamondSDPAttainment
import SKEFTHawking.QuantumNetwork.FidelityBounds
import Mathlib.Analysis.Convex.Cone.InnerDual

/-!
# PSD-cone self-duality on the diamond-SDP carrier (Phase 6AI — `≥` direction, Farkas brick A)

The conic Farkas lemma (`ProperCone.relative_hyperplane_separation`) expresses dual feasibility of
the diamond-SDP as membership of a target point in the (closed) image of the PSD product cone, and
its separating certificate lives in the **inner dual** of that cone. To decode both sides we need
the **self-duality of the PSD cone** under the real Frobenius inner product
`⟪A,B⟫ = Re tr(A·B)` on `HermCarrier ι`:

`Y ∈ innerDual psdProperCone ↔ Y.toSA.1.PosSemidef`.

* `←` (`le_innerDual`): for PSD `Y`, every PSD `X` has `0 ≤ Re tr(X·Y)` — this is `trace_mul_nonneg`.
* `→` (`innerDual_le`): if `0 ≤ Re tr(X·Y)` for every PSD `X`, then testing against the rank-one
  PSD matrices `X = v vᴴ` (`Matrix.posSemidef_vecMulVec_self_star`) gives `0 ≤ ⟪v, Y v⟫` for all `v`,
  which (with `Y` Hermitian) is the quadratic-form characterization of `Y ⪰ 0`
  (`Matrix.posSemidef_iff_dotProduct_mulVec`).

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder

namespace HermCarrier

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **Trace of a rank-one times `M`:** `tr(v vᴴ · M) = ⟨v, M v⟩ = star v ⬝ᵥ (M *ᵥ v)`. -/
theorem trace_vecMulVec_mul (v : ι → ℂ) (M : Matrix ι ι ℂ) :
    (vecMulVec v (star v) * M).trace = star v ⬝ᵥ (M *ᵥ v) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.vecMulVec_apply,
    dotProduct, Matrix.mulVec, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

omit [DecidableEq ι] in
/-- **The imaginary part of the Hermitian quadratic form vanishes:** for `M` Hermitian,
`⟨v, M v⟩ = star v ⬝ᵥ (M *ᵥ v)` is real. -/
theorem im_dotProduct_mulVec_hermitian {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (v : ι → ℂ) :
    (star v ⬝ᵥ (M *ᵥ v)).im = 0 :=
  hM.im_star_dotProduct_mulVec_self v

/-- **PSD-cone self-duality (membership form).** A carrier element lies in the inner dual of the PSD
cone exactly when it is positive semidefinite. -/
theorem mem_innerDual_psdProperCone {Y : HermCarrier ι} :
    Y ∈ ProperCone.innerDual ((psdProperCone : ProperCone ℝ (HermCarrier ι)) : Set (HermCarrier ι))
      ↔ Y.toSA.1.PosSemidef := by
  rw [ProperCone.mem_innerDual]
  constructor
  · intro h
    have hHerm : Y.toSA.1.IsHermitian := by
      have := Y.toSA.2; rwa [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose] at this
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨hHerm, fun v => ?_⟩
    -- rank-one PSD test matrix X₀ = v vᴴ
    have hX0psd : (vecMulVec v (star v)).PosSemidef := Matrix.posSemidef_vecMulVec_self_star v
    set X0 : HermCarrier ι := ⟨⟨vecMulVec v (star v), by
      rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose]; exact hX0psd.isHermitian.eq⟩⟩ with hX0
    have hX0mem : X0 ∈ (psdProperCone : ProperCone ℝ (HermCarrier ι)) := hX0psd
    have hre := h hX0mem
    rw [inner_eq] at hre
    -- ⟪X0, Y⟫ = Re tr(v vᴴ · Y) = Re ⟨v, Y v⟩
    have hval : (X0.toSA.1 * Y.toSA.1).trace = star v ⬝ᵥ (Y.toSA.1 *ᵥ v) := by
      show (vecMulVec v (star v) * Y.toSA.1).trace = _
      exact trace_vecMulVec_mul v Y.toSA.1
    rw [hval] at hre
    rw [Complex.le_def]
    refine ⟨?_, ?_⟩
    · simpa using hre
    · simpa using (im_dotProduct_mulVec_hermitian hHerm v).symm
  · intro hY X hX
    rw [SetLike.mem_coe, mem_psdProperCone] at hX
    rw [inner_eq]
    exact (Complex.le_def.mp (trace_mul_nonneg hX hY)).1

end HermCarrier

open scoped Kronecker

variable {n : ℕ}

/-- **`Tr₂` adjoint identity (Farkas brick B):** `tr((Tr₂ W)·Y) = tr(W·(Y ⊗ 1))`. The Hilbert–Schmidt
adjoint of the second-factor partial trace is tensoring with the identity on the traced-out factor.
Used to decode the conic Farkas separator: the dual-feasibility constraint `Y₁ + Tr₂†(Y₂) ⪰ 0`
becomes `Y₂ ⊗ 1 − X ⪰ 0`. -/
theorem trace_ptrace2_mul (W : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (Y : Matrix (Fin n) (Fin n) ℂ) :
    (ptrace2 W * Y).trace = (W * (Y ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, ptrace2, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]

open scoped Matrix.Norms.L2Operator ComplexOrder in
/-- **Primal-side weak duality (Farkas brick C′).** For a dual-feasible witness `W` (`W ⪰ 0`,
`W ⪰ C`) and a primal-feasible `X` (`X ⪰ 0`, `X ⪯ σ ⊗ 1` with `σ ⪰ 0`):
`Re tr(C·X) ≤ ‖Tr₂ W‖ · Re tr σ`. The chain `Re tr(C X) ≤ Re tr(W X) ≤ Re tr(W (σ⊗1))
= Re tr((Tr₂ W) σ) ≤ ‖Tr₂ W‖ · Re tr σ` (Loewner monotonicity ×2 via `trace_mul_nonneg`, the
`Tr₂` adjoint identity brick B, and the operator-norm trace bound). Taking the dual infimum over
`W` gives `Re tr(C X) ≤ choiDualValue · Re tr σ` — the primal weak-duality bound that any feasible
primal point obeys. (Strong duality strengthens `choiDualValue` to `diamondDist`.) -/
theorem re_trace_mul_le_l2opNorm_ptrace2_mul_trace [NeZero n]
    {C W X : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ} (hW : W.PosSemidef)
    (hWC : (W - C).PosSemidef) (hX : X.PosSemidef) {σ : Matrix (Fin n) (Fin n) ℂ}
    (hσ : σ.PosSemidef) (hle : (σ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) - X).PosSemidef) :
    (C * X).trace.re ≤ ‖ptrace2 W‖ * σ.trace.re := by
  have h1 : (C * X).trace.re ≤ (W * X).trace.re := by
    have h := (Complex.le_def.mp (trace_mul_nonneg hWC hX)).1
    rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re] at h
    simp only [Complex.zero_re] at h; linarith
  have h2 : (W * X).trace.re ≤ (W * (σ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))).trace.re := by
    have h := (Complex.le_def.mp (trace_mul_nonneg hW hle)).1
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at h
    simp only [Complex.zero_re] at h; linarith
  have h4 : ((ptrace2 W) * σ).trace.re ≤ ‖ptrace2 W‖ * σ.trace.re :=
    re_trace_mul_le_l2opNorm_mul_trace (ptrace2_posSemidef hW).isHermitian hσ
  calc (C * X).trace.re ≤ (W * X).trace.re := h1
    _ ≤ (W * (σ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))).trace.re := h2
    _ = ((ptrace2 W) * σ).trace.re := by rw [← trace_ptrace2_mul W σ]
    _ ≤ ‖ptrace2 W‖ * σ.trace.re := h4

/-- **Primal feasibility of the Choi contraction (Farkas brick C″).** For an effect `Q` (`0 ⪯ Q ⪯ 1`)
and a state `ρ ⪰ 0`, the Choi contraction `M(Q,ρ) = choiContraction Q ρ` is dominated by
`(inMarginal ρ) ⊗ 1`: `M(Q,ρ) ⪯ (inMarginal ρ) ⊗ 1`. Together with `choiContraction_posSemidef`
this shows every `M(Q,ρ)` is a feasible point of the diamond-SDP primal `{X ⪰ 0, X ⪯ σ ⊗ 1}`
with `σ = inMarginal ρ` (a density when `ρ` is). Since `Re tr(C · M(P,ρ))` equals `traceDist` at
input `ρ` (`traceDist_eq_re_trace_choiContraction_posProj`), this is the `primal ≥ diamondDist`
support: the diamond distance is attained inside the primal-feasible set. -/
theorem choiContraction_le_inMarginal_kron_one
    {Q ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ}
    (hQ1 : ((1 : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) - Q).PosSemidef) (hρ : ρ.PosSemidef) :
    (inMarginal ρ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) - choiContraction Q ρ).PosSemidef := by
  rw [← choiContraction_one_eq, ← choiContraction_sub]
  exact choiContraction_posSemidef hQ1 hρ

open scoped Matrix.Norms.L2Operator ComplexOrder in
/-- **Slater strict feasibility of the diamond-SDP dual (brick D).** For any Hermitian `C`, the dual
feasible region `{W : W ⪰ 0, W ⪰ C}` has a strictly-interior point: `W = ‖C‖•1 + C + 1` is
positive-DEFINITE and `W − C = ‖C‖•1 + 1 ≻ 0`. (Uses `C ⪰ −‖C‖•1`, i.e. `‖C‖•1 + C ⪰ 0`, the
companion of `norm_smul_one_sub_self_posSemidef`.) Slater's constraint qualification — the input to
finite-dimensional conic strong duality (zero gap), hence `choiDualValue ≤ diamondDist`. -/
theorem exists_dual_strictly_feasible {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {C : Matrix ι ι ℂ} (hC : C.IsHermitian) :
    ∃ W : Matrix ι ι ℂ, W.PosDef ∧ (W - C).PosDef := by
  have hcomp : (((‖C‖ : ℂ)) • (1 : Matrix ι ι ℂ) + C).PosSemidef := by
    have h := norm_smul_one_sub_self_posSemidef hC.neg
    rwa [norm_neg, sub_neg_eq_add] at h
  have hsmul : (((‖C‖ : ℂ)) • (1 : Matrix ι ι ℂ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (by rw [Complex.zero_le_real]; exact norm_nonneg C)
  refine ⟨(‖C‖ : ℂ) • 1 + C + 1, ?_, ?_⟩
  · have he : ((‖C‖ : ℂ) • 1 + C + 1 : Matrix ι ι ℂ) = ((‖C‖ : ℂ) • 1 + C) + 1 := by abel
    rw [he]; exact Matrix.PosDef.posSemidef_add hcomp Matrix.PosDef.one
  · have he : ((‖C‖ : ℂ) • 1 + C + 1 : Matrix ι ι ℂ) - C = (‖C‖ : ℂ) • 1 + 1 := by abel
    rw [he]; exact Matrix.PosDef.posSemidef_add hsmul Matrix.PosDef.one

variable {m : ℕ}

/-- **The diamond-SDP primal value.** `primalSDPValue K₁ K₂ = sup{ Re tr(C·X) : X ⪰ 0, X ⪯ σ⊗1,
`σ` a density }`, `C = J(Φ₁) − J(Φ₂)`. This is the object the strong-duality `≥` direction is
built around: `choiDualValue ≤ primalSDPValue` is the conic-Farkas / Slater strong-duality direction
(piece 2), and `primalSDPValue ≤ diamondDist` is the Watrous primal reduction (piece 3); together
with the shipped weak directions they collapse `diamondDist = choiDualValue`. -/
noncomputable def primalSDPValue (K₁ K₂ : Fin m → Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  sSup {r | ∃ (X : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (σ : Matrix (Fin n) (Fin n) ℂ),
    X.PosSemidef ∧ IsDensityOperator σ ∧ (σ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) - X).PosSemidef ∧
    r = ((choiMatrix (krausMap K₁) - choiMatrix (krausMap K₂)) * X).trace.re}

open scoped Matrix.Norms.L2Operator in
/-- **Primal ≤ dual (weak duality on the SDP values).** Every diamond-SDP primal value is at most
the dual value: `primalSDPValue ≤ choiDualValue`. Each feasible primal point `(X ⪯ σ⊗1, σ density)`
is bounded by every dual-feasible objective via brick C′ (`Re tr(C·X) ≤ ‖Tr₂ W‖·tr σ = ‖Tr₂ W‖`),
hence by the dual infimum. (The matching `≥` is the Slater strong-duality direction, piece 2.) -/
theorem primalSDPValue_le_choiDualValue [NeZero n] (K₁ K₂ : Fin m → Matrix (Fin n) (Fin n) ℂ) :
    primalSDPValue K₁ K₂ ≤ choiDualValue K₁ K₂ := by
  apply csSup_le
  · exact ⟨0, 0, _, Matrix.PosSemidef.zero, isDensityOperator_maximallyMixed,
      by rw [sub_zero]; exact (isDensityOperator_maximallyMixed.1).kronecker Matrix.PosSemidef.one,
      by simp⟩
  · rintro r ⟨X, σ, hX, hσ, hle, rfl⟩
    refine le_csInf (choiDualValue_set_nonempty K₁ K₂) ?_
    rintro s ⟨W, hW, hWC, rfl⟩
    have h := re_trace_mul_le_l2opNorm_ptrace2_mul_trace hW hWC hX hσ.1 hle
    rwa [hσ.2, Complex.one_re, mul_one] at h

open scoped Matrix.Norms.L2Operator in
/-- **Dual infeasibility below the optimum (piece 2, alternatives precondition).** For any
`δ < choiDualValue`, no dual witness `W` (`W ⪰ 0`, `W ⪰ C`) achieves objective `‖Tr₂ W‖ ≤ δ` — the
dual-feasible objective-sublevel at level `δ` is empty. This is the infeasibility hypothesis fed to
the conic theorem-of-alternatives (Slater ⟹ exact certificate): an infeasible dual system at level
`δ` yields a primal-feasible `X` with `Re tr(C·X) ≥ δ`, so `primalSDPValue ≥ δ`; letting
`δ → choiDualValue` gives `choiDualValue ≤ primalSDPValue`. -/
theorem dual_infeasible_of_lt_choiDualValue [NeZero n] {K₁ K₂ : Fin m → Matrix (Fin n) (Fin n) ℂ}
    {δ : ℝ} (hδ : δ < choiDualValue K₁ K₂) :
    ¬ ∃ W : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ, W.PosSemidef ∧
      (W - (choiMatrix (krausMap K₁) - choiMatrix (krausMap K₂))).PosSemidef ∧
      ‖ptrace2 W‖ ≤ δ := by
  rintro ⟨W, hW, hWC, hle⟩
  have hge : choiDualValue K₁ K₂ ≤ ‖ptrace2 W‖ :=
    csInf_le ⟨0, by rintro r ⟨V, _, _, rfl⟩; exact norm_nonneg _⟩ ⟨W, hW, hWC, rfl⟩
  linarith

end SKEFTHawking.QuantumNetwork
