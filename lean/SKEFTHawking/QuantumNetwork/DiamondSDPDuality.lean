import SKEFTHawking.QuantumNetwork.DiamondSDPCone
import SKEFTHawking.QuantumNetwork.DiamondSDPAttainment
import SKEFTHawking.QuantumNetwork.FidelityBounds
import SKEFTHawking.QuantumNetwork.FidelityForwardBound
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

open scoped Matrix.Norms.L2Operator in
/-- **Conditional strong-duality headline (`diamondDist_eq_choiSDP` modulo the optimal witness).**
The diamond-SDP strong-duality equality `diamondDist = choiDualValue` follows from the existence of
a *single* dual witness `W` (`W ⪰ 0`, `W ⪰ C`) whose objective meets the diamond distance,
`‖Tr₂ W‖ ≤ diamondDist`: weak duality (`diamondDist_le_choiDualValue`) gives `≤`, and the witness
(`choiDualValue_le_of_witness`) gives `≥`. This isolates the entire remaining content of 6AI into
the Watrous optimal-witness construction (the Jordan–Hahn `W*` of the Choi-mapped optimal state) —
discharge `hwit` and the headline closes by `le_antisymm`. -/
theorem diamondDist_eq_choiSDP_of_witness [NeZero n] {K₁ K₂ : Fin m → Matrix (Fin n) (Fin n) ℂ}
    (hK₁ : IsKrausChannel K₁) (hK₂ : IsKrausChannel K₂)
    (hwit : ∃ W : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ, W.PosSemidef ∧
      (W - (choiMatrix (krausMap K₁) - choiMatrix (krausMap K₂))).PosSemidef ∧
      ‖ptrace2 W‖ ≤ diamondDist K₁ K₂) :
    diamondDist K₁ K₂ = choiDualValue K₁ K₂ :=
  le_antisymm (diamondDist_le_choiDualValue hK₁ hK₂) (choiDualValue_le_of_witness hwit)

/-- `Tr₂` is additive on differences (it is a finite sum of entries). -/
theorem ptrace2_sub (A B : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    ptrace2 (A - B) = ptrace2 A - ptrace2 B := by
  ext a b; simp only [ptrace2, Matrix.sub_apply, Matrix.sub_apply, Finset.sum_sub_distrib]

/-- **Input marginal of a Kraus channel's Choi matrix is the identity** (trace preservation).
`(Tr₂ J(Φ))(a,b) = Σ_x J(Φ)((a,x),(b,x)) = tr(Φ(E_{ab})) = tr(E_{ab}) = δ_{ab}`, using
`trace_krausMap` (CPTP ⟹ trace-preserving) and `trace_single`. The Choi convention here is
input-factor-first, so `Tr₂` (tracing the second/output factor) is the input marginal. -/
theorem ptrace2_choiMatrix_krausMap {K : Fin m → Matrix (Fin n) (Fin n) ℂ} (hK : IsKrausChannel K) :
    ptrace2 (choiMatrix (krausMap K)) = 1 := by
  ext a b
  have htr : ptrace2 (choiMatrix (krausMap K)) a b = (krausMap K (Matrix.single a b 1)).trace := by
    simp only [ptrace2, choiMatrix, Matrix.trace, Matrix.diag_apply]
  rw [htr, trace_krausMap hK, Matrix.one_apply]
  rcases eq_or_ne a b with h | h
  · subst h; simp
  · simp [h]

/-- **The Choi difference is trace-annihilated:** `Tr₂ C = 0` for `C = J(Φ₁) − J(Φ₂)` with both
trace-preserving — the input marginals are both `1_X` and cancel. (DR F1; used in the optimal-witness
attainment computation, Stage 5.) -/
theorem ptrace2_choiDiff_eq_zero {K₁ K₂ : Fin m → Matrix (Fin n) (Fin n) ℂ}
    (hK₁ : IsKrausChannel K₁) (hK₂ : IsKrausChannel K₂) :
    ptrace2 (choiMatrix (krausMap K₁) - choiMatrix (krausMap K₂)) = 0 := by
  rw [ptrace2_sub, ptrace2_choiMatrix_krausMap hK₁, ptrace2_choiMatrix_krausMap hK₂, sub_self]

open scoped Kronecker in
/-- **The contracted Choi operator** `M = (√σ ⊗ 1)·C·(√σ ⊗ 1)` (DR F4 Step 3, project convention:
`√σ` on the input/first factor). For the optimal input `σ = ρ*`, the positive-eigenspace projector
`Π* = posProj` of this operator is the spectral data defining the optimal dual witness
`W* = (√σ⊗1)·Π*·C·Π*·(√σ⊗1)`. Its Jordan–Hahn decomposition (`posPart`/`negPart`, both PSD with
`posPart − M = negPart ⪰ 0`) is the substrate of the witness construction (Stage 4). -/
noncomputable def contractedChoi {σ : Matrix (Fin n) (Fin n) ℂ} (hσ : σ.PosSemidef)
    (C : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  (psdSqrt hσ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) * C * (psdSqrt hσ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))

open scoped Kronecker in
/-- The contracted Choi operator is Hermitian (conjugation of the Hermitian `C` by the Hermitian
`√σ ⊗ 1`), so its `posProj`/`posPart`/`negPart` Jordan–Hahn data is well-defined. -/
theorem contractedChoi_isHermitian {σ : Matrix (Fin n) (Fin n) ℂ} (hσ : σ.PosSemidef)
    {C : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ} (hC : C.IsHermitian) :
    (contractedChoi hσ C).IsHermitian := by
  have hB : (psdSqrt hσ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ
      = psdSqrt hσ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [Matrix.conjTranspose_kronecker, (psdSqrt_isHermitian hσ).eq, Matrix.conjTranspose_one]
  have h := isHermitian_mul_mul_conjTranspose (psdSqrt hσ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) hC
  rwa [hB] at h

open scoped Kronecker in
/-- **The optimal dual witness** `W* = (√σ⁻¹ ⊗ 1)·M₊·(√σ⁻¹ ⊗ 1)`, where `M₊ = posPart` of the
contracted Choi `M = (√σ⊗1)C(√σ⊗1)`. (Corrected form: the conjugating factor is `√σ⁻¹`, not the
`√σ` of the DR's stated formula, which fails `W*⪰C`.) For PosDef `σ` it is the optimal Watrous dual
witness; `W*⪰0` holds for any PosSemidef `σ` (conjugation of the PSD positive part). -/
noncomputable def diamondWitness {σ : Matrix (Fin n) (Fin n) ℂ} (hσ : σ.PosSemidef)
    {C : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ} (hC : C.IsHermitian) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  ((psdSqrt hσ)⁻¹ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) *
      posPart (contractedChoi_isHermitian hσ hC) *
    ((psdSqrt hσ)⁻¹ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))

open scoped Kronecker in
/-- **`W* ⪰ 0`** — the witness is positive semidefinite (conjugation of the PSD `posPart M₊` by the
Hermitian `√σ⁻¹ ⊗ 1`). Holds for any PosSemidef `σ`. -/
theorem diamondWitness_posSemidef {σ : Matrix (Fin n) (Fin n) ℂ} (hσ : σ.PosSemidef)
    {C : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ} (hC : C.IsHermitian) :
    (diamondWitness hσ hC).PosSemidef := by
  have hBh : ((psdSqrt hσ)⁻¹ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ
      = (psdSqrt hσ)⁻¹ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      Matrix.conjTranspose_nonsing_inv, (psdSqrt_isHermitian hσ).eq]
  have h := (posPart_posSemidef (contractedChoi_isHermitian hσ hC)).mul_mul_conjTranspose_same
    ((psdSqrt hσ)⁻¹ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))
  rw [hBh] at h
  exact h

open scoped Kronecker in
/-- **`W* ⪰ C`** — the witness is dual-feasible. With `M = contractedChoi = (√σ⊗1)C(√σ⊗1)` and
`B = √σ⁻¹⊗1`, the cancellation `B·(√σ⊗1) = (√σ⊗1)·B = 1` (PosDef ⟹ `√σ` invertible) gives
`C = B·M·B`, so `W* − C = B·(M₊ − M)·B = B·negPart(M)·B ⪰ 0`. Requires PosDef `σ`. -/
theorem diamondWitness_sub_posSemidef [NeZero n] {σ : Matrix (Fin n) (Fin n) ℂ} (hσ : σ.PosDef)
    {C : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ} (hC : C.IsHermitian) :
    (diamondWitness hσ.posSemidef hC - C).PosSemidef := by
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  have hsdet : IsUnit (psdSqrt hσ.posSemidef).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_psdSqrt _ hσ.isUnit)
  set s := psdSqrt hσ.posSemidef with hs
  set B := s⁻¹ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) with hBdef
  set A := s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) with hAdef
  have hBA : B * A = 1 := by
    rw [hBdef, hAdef, ← Matrix.mul_kronecker_mul, Matrix.nonsing_inv_mul _ hsdet, Matrix.mul_one,
      Matrix.one_kronecker_one]
  have hAB : A * B = 1 := by
    rw [hBdef, hAdef, ← Matrix.mul_kronecker_mul, Matrix.mul_nonsing_inv _ hsdet, Matrix.mul_one,
      Matrix.one_kronecker_one]
  have hWdef : diamondWitness hσ.posSemidef hC
      = B * posPart (contractedChoi_isHermitian hσ.posSemidef hC) * B := rfl
  have hMdef : contractedChoi hσ.posSemidef C = A * C * A := rfl
  have hCeq : C = B * contractedChoi hσ.posSemidef C * B := by
    rw [hMdef]
    have h1 : B * (A * C * A) * B = B * A * C * (A * B) := by noncomm_ring
    rw [h1, hBA, hAB, Matrix.one_mul, Matrix.mul_one]
  have hsub : diamondWitness hσ.posSemidef hC - C
      = B * negPart (contractedChoi_isHermitian hσ.posSemidef hC) * B := by
    rw [hWdef]
    have hneg : negPart (contractedChoi_isHermitian hσ.posSemidef hC)
        = posPart (contractedChoi_isHermitian hσ.posSemidef hC) - contractedChoi hσ.posSemidef C :=
      (posPart_sub_self_eq_negPart _).symm
    rw [hneg, Matrix.mul_sub, Matrix.sub_mul, ← hCeq]
  rw [hsub]
  have hBh : Bᴴ = B := by
    rw [hBdef, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      Matrix.conjTranspose_nonsing_inv, (psdSqrt_isHermitian hσ.posSemidef).eq]
  have h := (negPart_posSemidef (contractedChoi_isHermitian hσ.posSemidef hC)).mul_mul_conjTranspose_same B
  rwa [hBh] at h

open scoped Kronecker in
/-- **Partial trace of a first-factor conjugation:** `Tr₂((A⊗1)·Z·(A⊗1)) = A·(Tr₂ Z)·A`. Pushing the
first-factor operator `A` through the second-factor partial trace. The Stage-5 step that turns
`Tr₂ W* = Tr₂((√σ⁻¹⊗1)·M₊·(√σ⁻¹⊗1))` into `√σ⁻¹·(Tr₂ M₊)·√σ⁻¹`. -/
theorem ptrace2_kron_one_conj (A : Matrix (Fin n) (Fin n) ℂ)
    (Z : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    ptrace2 ((A ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) * Z * (A ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)))
      = A * ptrace2 Z * A := by
  ext a b
  simp only [ptrace2, Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_eq, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]

open scoped Kronecker in
/-- **The contracted Choi is traceless** when `Tr₂ C = 0`: `tr M = tr((√σ⊗1)C(√σ⊗1))
= tr(C·(σ⊗1)) = tr((Tr₂ C)·σ) = tr(0·σ) = 0` (trace-cyclicity, `(√σ⊗1)² = σ⊗1`, the `Tr₂` adjoint
brick B, and `ptrace2 C = 0`). Since `M` is Hermitian and traceless, `tr(M₊) = ½‖M‖₁` — the bridge
from the witness objective to the trace distance (Stage 5). -/
theorem trace_contractedChoi_eq_zero {σ : Matrix (Fin n) (Fin n) ℂ} (hσ : σ.PosSemidef)
    {C : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ} (hC2 : ptrace2 C = 0) :
    (contractedChoi hσ C).trace = 0 := by
  have hsq : (psdSqrt hσ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))
        * (psdSqrt hσ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))
      = σ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← Matrix.mul_kronecker_mul, psdSqrt_mul_self hσ, Matrix.mul_one]
  unfold contractedChoi
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hsq, Matrix.trace_mul_comm,
    ← trace_ptrace2_mul, hC2, Matrix.zero_mul, Matrix.trace_zero]

/-- **Trace of the positive part of a traceless Hermitian operator is half its trace norm:**
`tr(M₊) = ½‖M‖₁` when `tr M = 0`. From `‖M‖₁ = tr M₊ + tr M₋` and `tr M = tr M₊ − tr M₋ = 0`
(so `tr M₊ = tr M₋`). The Stage-5 step turning `tr(M₊)` into `½‖M‖₁ = traceDist`. -/
theorem trace_posPart_eq_half_traceNorm {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (h0 : M.trace.re = 0) :
    (posPart hM).trace.re = (1 / 2 : ℝ) * traceNorm M := by
  have htr : M.trace.re = (posPart hM).trace.re - (negPart hM).trace.re := by
    conv_lhs => rw [self_eq_posPart_sub_negPart hM]
    rw [Matrix.trace_sub, Complex.sub_re]
  have heq : (posPart hM).trace.re = (negPart hM).trace.re := by rw [h0] at htr; linarith
  rw [traceNorm_hermitian_eq_pos_add_neg hM, ← heq]; ring

open scoped Kronecker in
/-- **`(1⊗A)` pulls through the stabilized channel** (Stage-5b core): for Hermitian `A`,
`(Φ⊗id)((1⊗A)·ρ·(1⊗A)) = (1⊗A)·(Φ⊗id)(ρ)·(1⊗A)`. The ancilla-side operator `1⊗A` commutes with
each Kraus operator `Kₖ⊗1` (different tensor factors), so it factors out of `krausMap (tensorKraus K)`.
With the `ω↔Choi` identity this yields the σ-weighted vec-J identity relating the output difference
at the purification input `(1⊗√σ)|Ω⟩` to the contracted Choi `M = (√σ⊗1)C(√σ⊗1)`. -/
theorem krausMap_tensorKraus_conj_kron_one (K : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ)
    (ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    krausMap (tensorKraus K) (((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ A) * ρ
        * ((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ A))
      = ((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ A) * krausMap (tensorKraus K) ρ
          * ((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ A) := by
  unfold krausMap tensorKraus
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hcomm : (K k ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) * ((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ A)
      = ((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ A) * (K k ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_one, Matrix.one_mul]
  have hKh : (K k ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ
      = (K k)ᴴ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  have hcomm2 : ((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ A) * ((K k)ᴴ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))
      = ((K k)ᴴ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) * ((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ A) := by
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_one, Matrix.one_mul]
  rw [hKh,
    show (K k ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))
        * (((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ A) * ρ * ((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ A))
        * ((K k)ᴴ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))
      = (K k ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) * ((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ A) * ρ
          * (((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ A) * ((K k)ᴴ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)))
        from by noncomm_ring,
    hcomm, hcomm2,
    show ((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ A) * (K k ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) * ρ
          * (((K k)ᴴ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) * ((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ A))
      = ((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ A)
          * ((K k ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) * ρ * ((K k)ᴴ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)))
          * ((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ A) from by noncomm_ring]

open scoped Kronecker in
/-- **σ-weighted ω↔Choi identity** (Stage-5b): the stabilized output at the weighted
maximally-entangled vector `(1⊗s)|Ω⟩` is the `(1⊗s)`-conjugated (swapped) Choi matrix.
Composes the `(1⊗s)` pull-through with the shipped `krausMap_tensorKraus_omegaVec`. With `s = √σ`
this is the purification-input output, whose trace norm equals `‖(√σ⊗1)C(√σ⊗1)‖₁ = ‖M‖₁`. -/
theorem krausMap_tensorKraus_weighted_omega (K : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (s : Matrix (Fin n) (Fin n) ℂ) :
    krausMap (tensorKraus K) (((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ s)
        * (omegaVec n * (omegaVec n)ᴴ) * ((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ s))
      = ((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ s)
          * (choiMatrix (krausMap K)).submatrix (Equiv.prodComm (Fin n) (Fin n))
              (Equiv.prodComm (Fin n) (Fin n))
          * ((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ s) := by
  rw [krausMap_tensorKraus_conj_kron_one, krausMap_tensorKraus_omegaVec]

open scoped Kronecker in
/-- **Kronecker tensor-factor swap:** `(s ⊗ 1).submatrix swap swap = 1 ⊗ s`. Swapping both index
factors of `s ⊗ 1` moves the operator to the other tensor slot. -/
theorem kron_one_submatrix_prodComm (s : Matrix (Fin n) (Fin n) ℂ) :
    (s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)).submatrix (Equiv.prodComm (Fin n) (Fin n))
        (Equiv.prodComm (Fin n) (Fin n))
      = (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ s := by
  ext p q
  simp only [Matrix.submatrix_apply, Equiv.prodComm_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Prod.fst_swap, Prod.snd_swap]
  exact mul_comm _ _

open scoped Kronecker in
/-- **Contracted Choi under the tensor-factor swap:** `M.submatrix swap swap = (1⊗√σ)·(C
swap)·(1⊗√σ)`. Moving the `√σ` factor from the input slot (`√σ⊗1` in `M`) to the ancilla slot
(`1⊗√σ`), matching the purification-input output difference. Hence (next lemma)
`‖(1⊗√σ)(C swap)(1⊗√σ)‖₁ = ‖M‖₁`. -/
theorem contractedChoi_submatrix_swap {σ : Matrix (Fin n) (Fin n) ℂ} (hσ : σ.PosSemidef)
    (C : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    (contractedChoi hσ C).submatrix (Equiv.prodComm (Fin n) (Fin n))
        (Equiv.prodComm (Fin n) (Fin n))
      = ((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ psdSqrt hσ)
          * C.submatrix (Equiv.prodComm (Fin n) (Fin n)) (Equiv.prodComm (Fin n) (Fin n))
          * ((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ psdSqrt hσ) := by
  unfold contractedChoi
  rw [← Matrix.submatrix_mul_equiv (e₂ := Equiv.prodComm (Fin n) (Fin n)),
    ← Matrix.submatrix_mul_equiv (e₂ := Equiv.prodComm (Fin n) (Fin n)),
    kron_one_submatrix_prodComm]

open scoped Kronecker in
/-- **Trace-norm of the purification-input output equals the contracted-Choi trace norm:**
`‖(1⊗√σ)·(C swap)·(1⊗√σ)‖₁ = ‖M‖₁` (`M = contractedChoi`). Via `contractedChoi_submatrix_swap` +
trace-norm swap-invariance. -/
theorem traceNorm_kron_one_conj_swap {σ : Matrix (Fin n) (Fin n) ℂ} (hσ : σ.PosSemidef)
    (C : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    traceNorm (((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ psdSqrt hσ)
        * C.submatrix (Equiv.prodComm (Fin n) (Fin n)) (Equiv.prodComm (Fin n) (Fin n))
        * ((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ psdSqrt hσ))
      = traceNorm (contractedChoi hσ C) := by
  rw [← contractedChoi_submatrix_swap, traceNorm_submatrix_equiv]

open scoped Kronecker in
/-- **The σ-weighted maximally-entangled state is a density** (for `σ` a density): `ρ_σ =
(1⊗√σ)·ωωᴴ·(1⊗√σ) = ψ_σψ_σᴴ` is PSD (conjugation of the rank-one `ωωᴴ`), and `tr ρ_σ = tr σ = 1`
(`tr((1⊗σ)ωωᴴ) = tr σ`). A valid doubled-space input, so `traceDist(ρ_σ) ≤ diamondDist` directly. -/
theorem isDensityOperator_weighted_omega [NeZero n] {σ : Matrix (Fin n) (Fin n) ℂ}
    (hσ : IsDensityOperator σ) :
    IsDensityOperator (((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ psdSqrt hσ.1)
        * (omegaVec n * (omegaVec n)ᴴ) * ((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ psdSqrt hσ.1)) := by
  have hBh : ((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ psdSqrt hσ.1)ᴴ
      = (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ psdSqrt hσ.1 := by
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, (psdSqrt_isHermitian hσ.1).eq]
  have hBB : ((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ psdSqrt hσ.1)
        * ((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ psdSqrt hσ.1)
      = (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ σ := by
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, psdSqrt_mul_self hσ.1]
  refine ⟨?_, ?_⟩
  · have hP := (Matrix.posSemidef_self_mul_conjTranspose (omegaVec n)).mul_mul_conjTranspose_same
      ((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ psdSqrt hσ.1)
    rwa [hBh] at hP
  · rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hBB]
    -- tr((1⊗σ) * (ω ωᴴ)) = tr σ
    rw [Matrix.trace_mul_comm, Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, omegaVec,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Finset.univ_unique, Finset.sum_singleton,
      Fintype.sum_prod_type]
    simp only [apply_ite (star : ℂ → ℂ), star_one, star_zero, mul_ite, ite_mul, mul_one, one_mul,
      mul_zero, zero_mul, Finset.sum_const_zero, Finset.sum_ite_irrel, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact hσ.2

open scoped Kronecker in
/-- **Stage-5b capstone — the witness contracted-Choi trace bound:** `tr(M₊) ≤ diamondDist` for any
input density `σ`, `M = (√σ⊗1)·C·(√σ⊗1)` the contracted Choi. Proof: the σ-weighted
maximally-entangled state `ρ_σ` is a valid density (`isDensityOperator_weighted_omega`), its output
difference is `(1⊗√σ)·(C swap)·(1⊗√σ)` (σ-weighted ω↔Choi, factored), so
`traceDist(ρ_σ) = ½‖(1⊗√σ)(C swap)(1⊗√σ)‖₁ = ½‖M‖₁ = tr(M₊)` (`traceNorm_kron_one_conj_swap` + `tr M=0`
+ `trace_posPart_eq_half_traceNorm`), and `traceDist(ρ_σ) ≤ diamondDist` directly (`le_diamondDist`).
This is `tr(σ·Tr₂W*) = tr(M₊) ≤ diamondDist`, the weighted-average-eigenvalue bound feeding S5c. -/
theorem trace_posPart_contractedChoi_le_diamondDist [NeZero n]
    {K₁ K₂ : Fin m → Matrix (Fin n) (Fin n) ℂ} (hK₁ : IsKrausChannel K₁) (hK₂ : IsKrausChannel K₂)
    {σ : Matrix (Fin n) (Fin n) ℂ} (hσ : IsDensityOperator σ) :
    (posPart (contractedChoi_isHermitian hσ.1 (choiDiff_isHermitian K₁ K₂))).trace.re
      ≤ diamondDist K₁ K₂ := by
  set ρσ := ((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ psdSqrt hσ.1) * (omegaVec n * (omegaVec n)ᴴ)
    * ((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ psdSqrt hσ.1) with hρσ
  have hT : krausMap (tensorKraus K₁) ρσ - krausMap (tensorKraus K₂) ρσ
      = ((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ psdSqrt hσ.1)
          * (choiMatrix (krausMap K₁) - choiMatrix (krausMap K₂)).submatrix
              (Equiv.prodComm (Fin n) (Fin n)) (Equiv.prodComm (Fin n) (Fin n))
          * ((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ psdSqrt hσ.1) := by
    have hsub : (choiMatrix (krausMap K₁)).submatrix (Equiv.prodComm (Fin n) (Fin n))
            (Equiv.prodComm (Fin n) (Fin n))
          - (choiMatrix (krausMap K₂)).submatrix (Equiv.prodComm (Fin n) (Fin n))
            (Equiv.prodComm (Fin n) (Fin n))
        = (choiMatrix (krausMap K₁) - choiMatrix (krausMap K₂)).submatrix
            (Equiv.prodComm (Fin n) (Fin n)) (Equiv.prodComm (Fin n) (Fin n)) := by
      ext p q; simp [Matrix.submatrix_apply, Matrix.sub_apply]
    rw [hρσ, krausMap_tensorKraus_weighted_omega, krausMap_tensorKraus_weighted_omega,
      ← Matrix.sub_mul, ← Matrix.mul_sub, hsub]
  have hM0 : (contractedChoi hσ.1
      (choiMatrix (krausMap K₁) - choiMatrix (krausMap K₂))).trace.re = 0 := by
    rw [trace_contractedChoi_eq_zero hσ.1 (ptrace2_choiDiff_eq_zero hK₁ hK₂), Complex.zero_re]
  have htd : traceDist (krausMap (tensorKraus K₁) ρσ) (krausMap (tensorKraus K₂) ρσ)
      = (1 / 2 : ℝ) * traceNorm (contractedChoi hσ.1
          (choiMatrix (krausMap K₁) - choiMatrix (krausMap K₂))) := by
    rw [traceDist, hT, traceNorm_kron_one_conj_swap]
  rw [trace_posPart_eq_half_traceNorm _ hM0, ← htd]
  exact le_diamondDist hK₁ hK₂ (isDensityOperator_weighted_omega hσ)

open scoped Kronecker in
/-- **`Tr₂` of the witness:** `Tr₂ W* = √σ⁻¹·(Tr₂ M₊)·√σ⁻¹` — pushing the first-factor `√σ⁻¹` of
`W* = (√σ⁻¹⊗1)·M₊·(√σ⁻¹⊗1)` through the second-factor partial trace (`ptrace2_kron_one_conj`).
The witness objective `‖Tr₂ W*‖` is the operator norm of this; the Stage-5c attainment bounds it by
`diamondDist` at the optimal input. -/
theorem ptrace2_diamondWitness {σ : Matrix (Fin n) (Fin n) ℂ} (hσ : σ.PosSemidef)
    {C : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ} (hC : C.IsHermitian) :
    ptrace2 (diamondWitness hσ hC)
      = (psdSqrt hσ)⁻¹ * ptrace2 (posPart (contractedChoi_isHermitian hσ hC)) * (psdSqrt hσ)⁻¹ := by
  rw [diamondWitness, ptrace2_kron_one_conj]

open scoped Matrix.Norms.L2Operator in
/-- **Operator norm from a Loewner bound:** for PSD `A` with `A ⪯ c·1` (`c ≥ 0`), `‖A‖ ≤ c`.
Proof avoids eigenvalue extraction and cfc-commuting: `c²·1 − A² = c·(c·1−A) + √A·(c·1−A)·√A`, a sum
of two PSD operators (the second is `(c·1−A)` conjugated by the Hermitian `√A`, using
`√A·A·√A = A²`), then `opNorm_le_of_mul_conjTranspose_le_sq`. -/
theorem l2opNorm_le_of_loewner {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {A : Matrix ι ι ℂ} {c : ℝ} (hc : 0 ≤ c) (hA : A.PosSemidef)
    (hle : ((c : ℂ) • (1 : Matrix ι ι ℂ) - A).PosSemidef) : ‖A‖ ≤ c := by
  apply opNorm_le_of_mul_conjTranspose_le_sq hc
  rw [hA.isHermitian.eq]
  have hcc : (0 : ℂ) ≤ (c : ℂ) := by rw [Complex.zero_le_real]; exact hc
  have hsqA : psdSqrt hA * A * psdSqrt hA = A * A := by
    have h1 : psdSqrt hA * A * psdSqrt hA
        = psdSqrt hA * (psdSqrt hA * psdSqrt hA) * psdSqrt hA := by rw [psdSqrt_mul_self hA]
    have h2 : psdSqrt hA * (psdSqrt hA * psdSqrt hA) * psdSqrt hA
        = (psdSqrt hA * psdSqrt hA) * (psdSqrt hA * psdSqrt hA) := by noncomm_ring
    rw [h1, h2]; simp only [psdSqrt_mul_self hA]
  have hP2 : (psdSqrt hA * ((c : ℂ) • (1 : Matrix ι ι ℂ) - A) * psdSqrt hA).PosSemidef := by
    have h := hle.mul_mul_conjTranspose_same (psdSqrt hA)
    rwa [(psdSqrt_isHermitian hA).eq] at h
  have hsum : ((c : ℂ) ^ 2) • (1 : Matrix ι ι ℂ) - A * A
      = (c : ℂ) • ((c : ℂ) • (1 : Matrix ι ι ℂ) - A)
        + psdSqrt hA * ((c : ℂ) • (1 : Matrix ι ι ℂ) - A) * psdSqrt hA := by
    have e2 : psdSqrt hA * ((c : ℂ) • (1 : Matrix ι ι ℂ) - A) * psdSqrt hA
        = (c : ℂ) • A - A * A := by
      rw [Matrix.mul_sub, Matrix.sub_mul, hsqA, mul_smul_comm, smul_mul_assoc, Matrix.mul_one,
        psdSqrt_mul_self hA]
    rw [e2, smul_sub, smul_smul, sq]; abel
  rw [hsum]; exact (hle.smul hcc).add hP2

open scoped Matrix.Norms.L2Operator in
/-- **S5c congruence reduction:** the witness operator-norm bound `‖Tr₂ W*‖ ≤ d` follows from the
Loewner inequality `Tr₂(posPart M) ⪯ d·σ` (for PosDef `σ`, `d ≥ 0`). Congruence by the Hermitian
`√σ⁻¹` sends `d·σ − Tr₂M₊ ⪰ 0` to `d·1 − Tr₂W* ⪰ 0` (using `√σ⁻¹·σ·√σ⁻¹ = 1` and
`ptrace2_diamondWitness`), then `l2opNorm_le_of_loewner`. This isolates the headline to the single
inequality `Tr₂(posPart M) ⪯ diamondDist·σ` at the optimal input (the variational kernel). -/
theorem opNorm_ptrace2_diamondWitness_le [NeZero n] {σ : Matrix (Fin n) (Fin n) ℂ} (hσ : σ.PosDef)
    {C : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ} (hC : C.IsHermitian) {d : ℝ} (hd : 0 ≤ d)
    (hLoew : ((d : ℂ) • σ
        - ptrace2 (posPart (contractedChoi_isHermitian hσ.posSemidef hC))).PosSemidef) :
    ‖ptrace2 (diamondWitness hσ.posSemidef hC)‖ ≤ d := by
  have hsdet : IsUnit (psdSqrt hσ.posSemidef).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_psdSqrt _ hσ.isUnit)
  have hsih : ((psdSqrt hσ.posSemidef)⁻¹)ᴴ = (psdSqrt hσ.posSemidef)⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, (psdSqrt_isHermitian hσ.posSemidef).eq]
  have hss : psdSqrt hσ.posSemidef * psdSqrt hσ.posSemidef = σ := psdSqrt_mul_self hσ.posSemidef
  have h1 : ((psdSqrt hσ.posSemidef)⁻¹ * psdSqrt hσ.posSemidef)
        * (psdSqrt hσ.posSemidef * (psdSqrt hσ.posSemidef)⁻¹)
      = (psdSqrt hσ.posSemidef)⁻¹ * σ * (psdSqrt hσ.posSemidef)⁻¹ := by
    rw [show ((psdSqrt hσ.posSemidef)⁻¹ * psdSqrt hσ.posSemidef)
          * (psdSqrt hσ.posSemidef * (psdSqrt hσ.posSemidef)⁻¹)
        = (psdSqrt hσ.posSemidef)⁻¹ * (psdSqrt hσ.posSemidef * psdSqrt hσ.posSemidef)
          * (psdSqrt hσ.posSemidef)⁻¹ from by noncomm_ring, hss]
  have hinvσ : (psdSqrt hσ.posSemidef)⁻¹ * σ * (psdSqrt hσ.posSemidef)⁻¹ = 1 := by
    rw [← h1, Matrix.nonsing_inv_mul _ hsdet, Matrix.mul_nonsing_inv _ hsdet, Matrix.one_mul]
  have hTrPsd : (ptrace2 (diamondWitness hσ.posSemidef hC)).PosSemidef :=
    ptrace2_posSemidef (diamondWitness_posSemidef hσ.posSemidef hC)
  have hLoew1 : ((d : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)
      - ptrace2 (diamondWitness hσ.posSemidef hC)).PosSemidef := by
    have hcong := hLoew.mul_mul_conjTranspose_same (psdSqrt hσ.posSemidef)⁻¹
    rw [hsih] at hcong
    have halg : (psdSqrt hσ.posSemidef)⁻¹ * ((d : ℂ) • σ
          - ptrace2 (posPart (contractedChoi_isHermitian hσ.posSemidef hC)))
          * (psdSqrt hσ.posSemidef)⁻¹
        = (d : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)
          - ptrace2 (diamondWitness hσ.posSemidef hC) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, mul_smul_comm, smul_mul_assoc, hinvσ,
        ← ptrace2_diamondWitness]
    rwa [halg] at hcong
  exact l2opNorm_le_of_loewner hd hTrPsd hLoew1

open scoped Matrix.Norms.L2Operator in
/-- **Headline modulo the variational inequality.** `diamondDist = choiDualValue` follows from a
*single* operator inequality at some PosDef input `σ`: `Tr₂(posPart M) ⪯ diamondDist · σ`
(`M = (√σ⊗1)C(√σ⊗1)`). Assembles the witness feasibility (`diamondWitness_posSemidef`,
`diamondWitness_sub_posSemidef`) + the congruence reduction (`opNorm_ptrace2_diamondWitness_le`) +
the conditional headline. This isolates ALL remaining 6AI content into the Watrous first-order
optimality fact that the optimal input `σ*` makes this Loewner inequality hold (the trace version
`tr(M₊) ≤ diamondDist` is shipped unconditionally; upgrading to the operator inequality at `σ*` is
the sole remaining kernel). -/
theorem diamondDist_eq_choiSDP_of_loewner [NeZero n] {K₁ K₂ : Fin m → Matrix (Fin n) (Fin n) ℂ}
    (hK₁ : IsKrausChannel K₁) (hK₂ : IsKrausChannel K₂)
    (hwit : ∃ (σ : Matrix (Fin n) (Fin n) ℂ) (hσ : σ.PosDef),
      ((diamondDist K₁ K₂ : ℂ) • σ
        - ptrace2 (posPart (contractedChoi_isHermitian hσ.posSemidef
            (choiDiff_isHermitian K₁ K₂)))).PosSemidef) :
    diamondDist K₁ K₂ = choiDualValue K₁ K₂ := by
  obtain ⟨σ, hσ, hLoew⟩ := hwit
  exact diamondDist_eq_choiSDP_of_witness hK₁ hK₂
    ⟨diamondWitness hσ.posSemidef (choiDiff_isHermitian K₁ K₂),
     diamondWitness_posSemidef hσ.posSemidef (choiDiff_isHermitian K₁ K₂),
     diamondWitness_sub_posSemidef hσ (choiDiff_isHermitian K₁ K₂),
     opNorm_ptrace2_diamondWitness_le hσ (choiDiff_isHermitian K₁ K₂) diamondDist_nonneg hLoew⟩

/-- **Loewner bound from a quadratic-form bound:** for Hermitian `H`, if `Re⟨v,H v⟩ ≤ d·Re⟨v,v⟩` for
every `v`, then `H ⪯ d·1` (`d·1 − H ⪰ 0`). The mechanism behind the non-perturbative route to the
variational kernel: the optimal-projector operator `H_{P*}` satisfies `Re⟨v,H_{P*}v⟩ ≤ traceDist ≤
diamondDist·Re⟨v,v⟩`, giving `H_{P*} ⪯ diamondDist·1` with no derivatives. -/
theorem posSemidef_smul_one_sub_of_quadratic_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {d : ℝ}
    (h : ∀ v : ι → ℂ, (star v ⬝ᵥ (H *ᵥ v)).re ≤ d * (star v ⬝ᵥ v).re) :
    ((d : ℂ) • (1 : Matrix ι ι ℂ) - H).PosSemidef := by
  have hHerm : ((d : ℂ) • (1 : Matrix ι ι ℂ) - H).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_sub, hH.eq, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, Complex.star_def, Complex.conj_ofReal]
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨hHerm, fun v => ?_⟩
  have hval : star v ⬝ᵥ (((d : ℂ) • (1 : Matrix ι ι ℂ) - H) *ᵥ v)
      = (d : ℂ) * (star v ⬝ᵥ v) - star v ⬝ᵥ (H *ᵥ v) := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul]
  have hvv : (star v ⬝ᵥ v).im = 0 := by
    have := HermCarrier.im_dotProduct_mulVec_hermitian (Matrix.isHermitian_one (n := ι)) v
    rwa [Matrix.one_mulVec] at this
  have hHv : (star v ⬝ᵥ (H *ᵥ v)).im = 0 := HermCarrier.im_dotProduct_mulVec_hermitian hH v
  rw [hval, Complex.le_def]
  refine ⟨?_, ?_⟩
  · simp only [Complex.zero_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    nlinarith [h v, hvv]
  · simp [Complex.sub_im, Complex.mul_im, hvv, hHv]

/-- **Helstrom-type measurement bound: `Re tr(M·Q) ≤ tr(M₊)` for `0 ⪯ Q ⪯ 1`** (`M` Hermitian).
Split `M = M₊ − M₋`: `Re tr(M₋·Q) ≥ 0` (PSD·PSD, `trace_mul_nonneg`) and `Re tr(M₊·Q) ≤ Re tr(M₊·1)
= tr(M₊)` (since `M₊ ⪰ 0` and `1 − Q ⪰ 0`). The optimal measurement is the positive-eigenspace
projector; any sub-unit-interval `Q` does no better than the positive part. Feeds the SDP-primal
reduction (piece 3): `Re tr(C·X) = Re tr(M(σ)·Q′) ≤ tr(M(σ)₊)`. -/
theorem re_trace_mul_le_trace_posPart {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M Q : Matrix ι ι ℂ} (hM : M.IsHermitian) (hQ : Q.PosSemidef)
    (hQ1 : ((1 : Matrix ι ι ℂ) - Q).PosSemidef) :
    (M * Q).trace.re ≤ (posPart hM).trace.re := by
  have hsplit : M * Q = posPart hM * Q - negPart hM * Q := by
    rw [← Matrix.sub_mul, ← self_eq_posPart_sub_negPart hM]
  have hneg : (0 : ℝ) ≤ (negPart hM * Q).trace.re := by
    have := (Complex.le_def.mp (trace_mul_nonneg (negPart_posSemidef hM) hQ)).1; simpa using this
  have hpos : (posPart hM * Q).trace.re ≤ (posPart hM).trace.re := by
    have h := (Complex.le_def.mp (trace_mul_nonneg (posPart_posSemidef hM) hQ1)).1
    have he : (posPart hM * ((1 : Matrix ι ι ℂ) - Q)).trace
        = (posPart hM).trace - (posPart hM * Q).trace := by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub]
    rw [he] at h
    simp only [Complex.sub_re, Complex.zero_re] at h
    linarith [h]
  rw [hsplit, Matrix.trace_sub, Complex.sub_re]
  linarith

open scoped Kronecker Matrix.Norms.L2Operator in
/-- **SDP-primal per-point bound at a PosDef input (piece 3, core).** For a positive-DEFINITE density
`σ` and SDP-feasible `X` (`X ⪰ 0`, `σ⊗1 − X ⪰ 0`), `Re tr(C·X) ≤ diamondDist` (`C = J(Φ₁)−J(Φ₂)`).
Conjugating by `√σ⁻¹⊗1` writes `X = (√σ⊗1)·Q′·(√σ⊗1)` with `0 ⪯ Q′ ⪯ 1`
(`Q′ = (√σ⁻¹⊗1)·X·(√σ⁻¹⊗1)`, and `(√σ⁻¹⊗1)(σ⊗1)(√σ⁻¹⊗1) = 1`), so by trace-cyclicity
`Re tr(C·X) = Re tr(M(σ)·Q′) ≤ tr(M(σ)₊)` (Helstrom bound) `≤ diamondDist` (shipped
`trace_posPart_contractedChoi_le_diamondDist`). -/
theorem re_trace_choiDiff_mul_le_diamondDist_of_posDef [NeZero n]
    {K₁ K₂ : Fin m → Matrix (Fin n) (Fin n) ℂ} (hK₁ : IsKrausChannel K₁) (hK₂ : IsKrausChannel K₂)
    {σ : Matrix (Fin n) (Fin n) ℂ} (hσ : σ.PosDef) (hσ1 : σ.trace = 1)
    {X : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ} (hX : X.PosSemidef)
    (hle : (σ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) - X).PosSemidef) :
    ((choiMatrix (krausMap K₁) - choiMatrix (krausMap K₂)) * X).trace.re ≤ diamondDist K₁ K₂ := by
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  set C := choiMatrix (krausMap K₁) - choiMatrix (krausMap K₂) with hCdef
  have hC : C.IsHermitian := choiDiff_isHermitian K₁ K₂
  have hsdet : IsUnit (psdSqrt hσ.posSemidef).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_psdSqrt _ hσ.isUnit)
  set s := psdSqrt hσ.posSemidef with hs
  set B := s⁻¹ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) with hBdef
  set A := s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) with hAdef
  have hBA : B * A = 1 := by
    rw [hBdef, hAdef, ← Matrix.mul_kronecker_mul, Matrix.nonsing_inv_mul _ hsdet, Matrix.mul_one,
      Matrix.one_kronecker_one]
  have hAB : A * B = 1 := by
    rw [hBdef, hAdef, ← Matrix.mul_kronecker_mul, Matrix.mul_nonsing_inv _ hsdet, Matrix.mul_one,
      Matrix.one_kronecker_one]
  have hBh : Bᴴ = B := by
    rw [hBdef, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      Matrix.conjTranspose_nonsing_inv, (psdSqrt_isHermitian hσ.posSemidef).eq]
  set Q' := B * X * B with hQ'def
  have hQ'psd : Q'.PosSemidef := by
    have h := hX.mul_mul_conjTranspose_same B; rwa [hBh] at h
  have hBσB : B * (σ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) * B = 1 := by
    have hss : s⁻¹ * σ * s⁻¹ = 1 := by
      rw [← psdSqrt_mul_self hσ.posSemidef, ← hs,
        show s⁻¹ * (s * s) * s⁻¹ = (s⁻¹ * s) * (s * s⁻¹) from by noncomm_ring,
        Matrix.nonsing_inv_mul _ hsdet, Matrix.mul_nonsing_inv _ hsdet, Matrix.one_mul]
    rw [hBdef, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
      Matrix.one_mul, hss, Matrix.one_kronecker_one]
  have hQ'1 : ((1 : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) - Q').PosSemidef := by
    have h := hle.mul_mul_conjTranspose_same B
    rw [hBh, Matrix.mul_sub, Matrix.sub_mul, hBσB] at h
    rwa [← hQ'def] at h
  have hACA : A * C * A = contractedChoi hσ.posSemidef C := by rw [hAdef, hs]; rfl
  have hXeq : X = A * Q' * A := by
    rw [hQ'def, show A * (B * X * B) * A = (A * B) * X * (B * A) from by noncomm_ring, hAB, hBA,
      Matrix.one_mul, Matrix.mul_one]
  have htr : (C * X).trace = (contractedChoi hσ.posSemidef C * Q').trace := by
    rw [hXeq, show C * (A * Q' * A) = (C * A * Q') * A from by noncomm_ring, Matrix.trace_mul_comm,
      show A * (C * A * Q') = (A * C * A) * Q' from by noncomm_ring, hACA]
  rw [htr]
  calc (contractedChoi hσ.posSemidef C * Q').trace.re
      ≤ (posPart (contractedChoi_isHermitian hσ.posSemidef hC)).trace.re :=
        re_trace_mul_le_trace_posPart (contractedChoi_isHermitian hσ.posSemidef hC) hQ'psd hQ'1
    _ ≤ diamondDist K₁ K₂ :=
        trace_posPart_contractedChoi_le_diamondDist hK₁ hK₂ ⟨hσ.posSemidef, hσ1⟩

open scoped Kronecker Matrix.Norms.L2Operator in
/-- **SDP-primal per-point bound at ANY density (piece 3).** Drops the PosDef hypothesis of
`re_trace_choiDiff_mul_le_diamondDist_of_posDef` via a `(1−ε)`-regularization: for `σ` a (possibly
singular) density and feasible `X`, the perturbed pair `(σ_ε, X_ε) = ((1−ε)σ + (ε/n)·1, (1−ε)X)` is
feasible with `σ_ε ≻ 0`, giving `(1−ε)·Re tr(C·X) ≤ diamondDist` for all `ε ∈ (0,1)`; the algebraic
choice `ε₀ = (t−d)/(2t)` then forces `Re tr(C·X) ≤ diamondDist` (no limit needed). -/
theorem re_trace_choiDiff_mul_le_diamondDist [NeZero n]
    {K₁ K₂ : Fin m → Matrix (Fin n) (Fin n) ℂ} (hK₁ : IsKrausChannel K₁) (hK₂ : IsKrausChannel K₂)
    {σ : Matrix (Fin n) (Fin n) ℂ} (hσ : IsDensityOperator σ)
    {X : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ} (hX : X.PosSemidef)
    (hle : (σ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) - X).PosSemidef) :
    ((choiMatrix (krausMap K₁) - choiMatrix (krausMap K₂)) * X).trace.re ≤ diamondDist K₁ K₂ := by
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  set C := choiMatrix (krausMap K₁) - choiMatrix (krausMap K₂) with hCdef
  set t := (C * X).trace.re with ht
  have hd : (0 : ℝ) ≤ diamondDist K₁ K₂ := diamondDist_nonneg
  have hcard : (Fintype.card (Fin n) : ℂ) = (n : ℂ) := by simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have key : ∀ ε : ℝ, 0 < ε → ε < 1 → (1 - ε) * t ≤ diamondDist K₁ K₂ := by
    intro ε hε0 hε1
    have h1ε : (0 : ℝ) ≤ 1 - ε := by linarith
    have hεn : (0 : ℝ) < ε / n := div_pos hε0 hn0
    have hc1 : (0 : ℂ) ≤ ((1 - ε : ℝ) : ℂ) := Complex.zero_le_real.mpr h1ε
    have hc2 : (0 : ℂ) < ((ε / n : ℝ) : ℂ) := by
      rw [Complex.lt_def, Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, Complex.zero_im]
      exact ⟨hεn, rfl⟩
    set σε := ((1 - ε : ℝ) : ℂ) • σ + ((ε / n : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) with hσε
    have hσεpd : σε.PosDef := by
      rw [hσε, add_comm]
      exact ((Matrix.PosDef.one).smul hc2).add_posSemidef (hσ.1.smul hc1)
    have hσεtr : σε.trace = 1 := by
      rw [hσε, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one, hσ.2,
        smul_eq_mul, smul_eq_mul, hcard]
      push_cast
      field_simp
      ring
    set Xε := ((1 - ε : ℝ) : ℂ) • X with hXε
    have hXεpsd : Xε.PosSemidef := hX.smul hc1
    have hXεle : (σε ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) - Xε).PosSemidef := by
      have heq : σε ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) - Xε
          = ((1 - ε : ℝ) : ℂ) • (σ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) - X)
            + ((ε / n : ℝ) : ℂ) • (1 : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) := by
        rw [hσε, hXε, Matrix.add_kronecker, Matrix.smul_kronecker, Matrix.smul_kronecker,
          Matrix.one_kronecker_one, smul_sub]
        abel
      rw [heq]
      exact (hle.smul hc1).add ((Matrix.PosSemidef.one).smul hc2.le)
    have hbound := re_trace_choiDiff_mul_le_diamondDist_of_posDef hK₁ hK₂ hσεpd hσεtr hXεpsd hXεle
    have heval : (C * Xε).trace.re = (1 - ε) * t := by
      rw [hXε, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      rw [ht]
    rwa [heval] at hbound
  by_contra hlt
  rw [not_le] at hlt
  have ht0 : 0 < t := lt_of_le_of_lt hd hlt
  set ε₀ := (t - diamondDist K₁ K₂) / (2 * t) with hε₀
  have hε0 : 0 < ε₀ := div_pos (by linarith) (by linarith)
  have hε1 : ε₀ < 1 := by rw [hε₀, div_lt_one (by linarith)]; linarith
  have hb := key ε₀ hε0 hε1
  have hcomp : (1 - ε₀) * t = (t + diamondDist K₁ K₂) / 2 := by
    rw [hε₀]; field_simp; ring
  rw [hcomp] at hb
  linarith

open scoped Kronecker Matrix.Norms.L2Operator in
/-- **Piece 3 — `primalSDPValue ≤ diamondDist` (Watrous primal reduction).** The SDP-primal value is at
most the operational diamond distance: every feasible `(X, σ)` gives `Re tr(C·X) ≤ diamondDist`
(`re_trace_choiDiff_mul_le_diamondDist`), so the supremum is bounded. Together with the conic-Farkas
direction `choiDualValue ≤ primalSDPValue` (piece 2) and the shipped weak directions, this collapses
`diamondDist = choiDualValue`. -/
theorem primalSDPValue_le_diamondDist [NeZero n] {K₁ K₂ : Fin m → Matrix (Fin n) (Fin n) ℂ}
    (hK₁ : IsKrausChannel K₁) (hK₂ : IsKrausChannel K₂) :
    primalSDPValue K₁ K₂ ≤ diamondDist K₁ K₂ := by
  apply csSup_le
  · exact ⟨0, 0, _, Matrix.PosSemidef.zero, isDensityOperator_maximallyMixed,
      by rw [sub_zero]; exact (isDensityOperator_maximallyMixed.1).kronecker Matrix.PosSemidef.one,
      by simp⟩
  · rintro r ⟨X, σ, hX, hσ, hle, rfl⟩
    exact re_trace_choiDiff_mul_le_diamondDist hK₁ hK₂ hσ hX hle

open scoped Kronecker Matrix.Norms.L2Operator in
/-- **`diamondDist ≤ primalSDPValue` (primal attainment side).** The optimal input `ρ`
(`exists_diamondDist_eq`) together with the positive-eigenspace projector `P = posProj` of its output
difference yields a primal-feasible point `X = choiContraction P ρ` (`choiContraction_posSemidef` +
`choiContraction_le_inMarginal_kron_one`, with `σ = inMarginal ρ` a density) whose objective
`Re tr(C·X)` equals `traceDist(Φ₁ρ,Φ₂ρ) = diamondDist`
(`traceDist_eq_re_trace_choiContraction_posProj`). Hence the diamond distance is attained inside the
primal-feasible set, so `primalSDPValue ≥ diamondDist`. With `primalSDPValue_le_diamondDist`
(piece 3) this gives `primalSDPValue = diamondDist`; the `choiContraction`→primal-point bridge is the
reassembly step reused by the conic-Farkas direction (piece 2). -/
theorem diamondDist_le_primalSDPValue [NeZero n] {K₁ K₂ : Fin m → Matrix (Fin n) (Fin n) ℂ}
    (hK₁ : IsKrausChannel K₁) (hK₂ : IsKrausChannel K₂) :
    diamondDist K₁ K₂ ≤ primalSDPValue K₁ K₂ := by
  obtain ⟨ρ, hρ, hdd⟩ := exists_diamondDist_eq (K₁ := K₁) (K₂ := K₂)
  have hTh : (krausMap (tensorKraus K₁) ρ - krausMap (tensorKraus K₂) ρ).IsHermitian :=
    (krausMap_isDensityOperator (isKrausChannel_tensorKraus hK₁) hρ).1.isHermitian.sub
      (krausMap_isDensityOperator (isKrausChannel_tensorKraus hK₂) hρ).1.isHermitian
  have hPpsd : (posProj hTh).PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self (posProj hTh)
    rwa [(posProj_isHermitian hTh).eq, posProj_idem hTh] at h
  have h1P : ((1 : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) - posProj hTh).PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self
      ((1 : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) - posProj hTh)
    rwa [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, (posProj_isHermitian hTh).eq,
      one_sub_posProj_idem hTh] at h
  set X := choiContraction (posProj hTh) ρ with hX
  have hXpsd : X.PosSemidef := choiContraction_posSemidef hPpsd hρ.1
  have hσdens : IsDensityOperator (inMarginal ρ) :=
    ⟨inMarginal_posSemidef hρ.1, by rw [trace_inMarginal, hρ.2]⟩
  have hXle : (inMarginal ρ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) - X).PosSemidef :=
    choiContraction_le_inMarginal_kron_one h1P hρ.1
  have hval : diamondDist K₁ K₂
      = ((choiMatrix (krausMap K₁) - choiMatrix (krausMap K₂)) * X).trace.re := by
    rw [hdd, hX]; exact traceDist_eq_re_trace_choiContraction_posProj hK₁ hK₂ ρ hTh
  rw [hval]
  refine le_csSup ⟨diamondDist K₁ K₂, ?_⟩ ⟨X, inMarginal ρ, hXpsd, hσdens, hXle, rfl⟩
  rintro r ⟨X', σ', hX', hσ', hle', rfl⟩
  exact re_trace_choiDiff_mul_le_diamondDist hK₁ hK₂ hσ' hX' hle'

/-- **`primalSDPValue = diamondDist`** — the diamond-SDP primal value equals the operational diamond
distance (Watrous primal characterization), combining `primalSDPValue_le_diamondDist` (piece 3) and
`diamondDist_le_primalSDPValue` (attainment). The headline `diamondDist = choiDualValue` then needs
only `choiDualValue ≤ primalSDPValue` (piece 2, conic Farkas). -/
theorem primalSDPValue_eq_diamondDist [NeZero n] {K₁ K₂ : Fin m → Matrix (Fin n) (Fin n) ℂ}
    (hK₁ : IsKrausChannel K₁) (hK₂ : IsKrausChannel K₂) :
    primalSDPValue K₁ K₂ = diamondDist K₁ K₂ :=
  le_antisymm (primalSDPValue_le_diamondDist hK₁ hK₂) (diamondDist_le_primalSDPValue hK₁ hK₂)

open scoped Kronecker in
/-- `(√σ⁻¹⊗1)·(σ⊗1)·(√σ⁻¹⊗1) = 1` for PosDef `σ` (the `√σ`-cancellation, first-factor). -/
theorem kron_sqrtInv_conj_kron_self [NeZero n] {σ : Matrix (Fin n) (Fin n) ℂ} (hσ : σ.PosDef) :
    ((psdSqrt hσ.posSemidef)⁻¹ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))
        * (σ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))
        * ((psdSqrt hσ.posSemidef)⁻¹ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) = 1 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  have hsdet : IsUnit (psdSqrt hσ.posSemidef).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_psdSqrt _ hσ.isUnit)
  set s := psdSqrt hσ.posSemidef with hs
  have hss : s⁻¹ * σ * s⁻¹ = 1 := by
    rw [← psdSqrt_mul_self hσ.posSemidef, ← hs,
      show s⁻¹ * (s * s) * s⁻¹ = (s⁻¹ * s) * (s * s⁻¹) from by noncomm_ring,
      Matrix.nonsing_inv_mul _ hsdet, Matrix.mul_nonsing_inv _ hsdet, Matrix.one_mul]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, hss,
    Matrix.one_kronecker_one]

open scoped Kronecker in
/-- **The witness objective against its own input: `tr((σ⊗1)·W*) = tr(M₊)`** for PosDef `σ`,
`W* = diamondWitness = (√σ⁻¹⊗1)·M₊·(√σ⁻¹⊗1)`. By cyclicity `tr((σ⊗1)·W*) =
tr((√σ⁻¹⊗1)(σ⊗1)(√σ⁻¹⊗1)·M₊) = tr(1·M₊) = tr(M₊)` (`kron_sqrtInv_conj_kron_self`). This is the
saddle-value identity: paired with `trace_posPart_contractedChoi_le_diamondDist` it gives the optimal
witness `W*` objective `tr((σ⊗1)·W*) ≤ diamondDist`, the reassembly value bound for the conic-Farkas
direction (piece 2). -/
theorem trace_kron_one_mul_diamondWitness [NeZero n] {σ : Matrix (Fin n) (Fin n) ℂ} (hσ : σ.PosDef)
    {C : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ} (hC : C.IsHermitian) :
    ((σ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) * diamondWitness hσ.posSemidef hC).trace
      = (posPart (contractedChoi_isHermitian hσ.posSemidef hC)).trace := by
  set B := (psdSqrt hσ.posSemidef)⁻¹ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) with hBdef
  set Mp := posPart (contractedChoi_isHermitian hσ.posSemidef hC) with hMp
  have hWdef : diamondWitness hσ.posSemidef hC = B * Mp * B := rfl
  rw [hWdef]
  rw [show (σ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) * (B * Mp * B)
      = (σ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) * B * Mp * B from by noncomm_ring]
  rw [Matrix.trace_mul_comm]
  rw [show B * ((σ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) * B * Mp)
      = (B * (σ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) * B) * Mp from by noncomm_ring]
  rw [hBdef, kron_sqrtInv_conj_kron_self hσ, Matrix.one_mul]

open scoped Kronecker in
/-- **Optimal-witness saddle value ≤ diamondDist.** For a PosDef density `σ`,
`Re tr((σ⊗1)·diamondWitness) = tr(M₊) ≤ diamondDist` (`trace_kron_one_mul_diamondWitness` +
`trace_posPart_contractedChoi_le_diamondDist`). Since `Re tr((σ⊗1)·W) = Re tr(σ·Tr₂W)`, this is the
S-side value bound for the conic-Farkas separation: the achievable point `Tr₂(diamondWitness σ) ∈ S`
pairs with `σ` to at most `diamondDist`. -/
theorem re_trace_kron_one_mul_diamondWitness_le [NeZero n]
    {K₁ K₂ : Fin m → Matrix (Fin n) (Fin n) ℂ} (hK₁ : IsKrausChannel K₁) (hK₂ : IsKrausChannel K₂)
    {σ : Matrix (Fin n) (Fin n) ℂ} (hσ : σ.PosDef) (hσ1 : σ.trace = 1) :
    ((σ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))
        * diamondWitness hσ.posSemidef (choiDiff_isHermitian K₁ K₂)).trace.re
      ≤ diamondDist K₁ K₂ := by
  rw [trace_kron_one_mul_diamondWitness hσ (choiDiff_isHermitian K₁ K₂)]
  exact trace_posPart_contractedChoi_le_diamondDist hK₁ hK₂ ⟨hσ.posSemidef, hσ1⟩

open scoped Matrix.Norms.L2Operator in
/-- **Witness norm bounded by its partial-trace trace:** `‖W‖ ≤ Re tr(Tr₂ W)` for `W ⪰ 0`. Since
`Tr₂ W` has the same trace as `W` (`trace_ptrace2`) and `‖W‖ ≤ traceNorm W = Re tr W` for PSD `W`
(`l2opNorm_le_traceNorm_psd` + `traceNorm_posSemidef`). **This is the closedness lever for the
achievable set `S = {Tr₂ W : W⪰0, W⪰C}`:** every witness for a given `M = Tr₂ W` has `‖W‖ ≤ Re tr M`
(uniformly bounded), so a convergent `Mₖ → M` lifts to a bounded — hence subconvergent — witness
sequence, giving `M ∈ S`. No recession-cone theory needed; the partial-trace trace identity bounds
the witnesses automatically. -/
theorem l2opNorm_le_re_trace_ptrace2 [NeZero n] {W : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ}
    (hW : W.PosSemidef) : ‖W‖ ≤ (ptrace2 W).trace.re := by
  haveI : Nonempty (Fin n × Fin n) :=
    ⟨(⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩, ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩)⟩
  calc ‖W‖ ≤ traceNorm W := l2opNorm_le_traceNorm_psd hW
    _ = (W.trace).re := traceNorm_posSemidef hW
    _ = (ptrace2 W).trace.re := by rw [trace_ptrace2]

/-- `Tr₂` is additive. -/
theorem ptrace2_add (A B : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    ptrace2 (A + B) = ptrace2 A + ptrace2 B := by
  ext a b; simp only [ptrace2, Matrix.add_apply, Matrix.add_apply, Finset.sum_add_distrib]

/-- `Tr₂` commutes with real scalar multiplication. -/
theorem ptrace2_real_smul (r : ℝ) (A : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    ptrace2 (r • A) = r • ptrace2 A := by
  ext a b
  simp only [ptrace2, Matrix.smul_apply, Complex.real_smul]
  rw [Finset.mul_sum]

/-- **The achievable partial-trace set** `S = {Tr₂ W : W ⪰ 0, W ⪰ C}` as a set in the Hermitian
carrier — the convex set the conic-Farkas separation pairs against the operator-norm ball. -/
def achievableTr2 (C : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) : Set (HermCarrier (Fin n)) :=
  {Y | ∃ W : HermCarrier (Fin n × Fin n), W.toSA.1.PosSemidef ∧ (W.toSA.1 - C).PosSemidef ∧
    Y.toSA.1 = ptrace2 W.toSA.1}

open scoped ComplexOrder in
/-- **`achievableTr2 C` is convex** (linear image of the convex dual-feasible set under `Tr₂`). -/
theorem convex_achievableTr2 (C : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    Convex ℝ (achievableTr2 C) := by
  rintro Y₁ ⟨W₁, hW₁, hW₁C, hY₁⟩ Y₂ ⟨W₂, hW₂, hW₂C, hY₂⟩ a b ha hb hab
  refine ⟨a • W₁ + b • W₂, ?_, ?_, ?_⟩
  · have hval : (a • W₁ + b • W₂).toSA.1 = a • W₁.toSA.1 + b • W₂.toSA.1 := by
      rw [HermCarrier.add_toSA, HermCarrier.smul_toSA, HermCarrier.smul_toSA, AddSubgroup.coe_add,
        selfAdjoint.val_smul, selfAdjoint.val_smul]
    rw [hval]
    have e1 : a • W₁.toSA.1 = ((a : ℂ)) • W₁.toSA.1 := by
      ext i j; simp [Matrix.smul_apply, Complex.real_smul]
    have e2 : b • W₂.toSA.1 = ((b : ℂ)) • W₂.toSA.1 := by
      ext i j; simp [Matrix.smul_apply, Complex.real_smul]
    rw [e1, e2]
    exact (hW₁.smul (by rw [Complex.zero_le_real]; exact ha)).add
      (hW₂.smul (by rw [Complex.zero_le_real]; exact hb))
  · have hval0 : (a • W₁ + b • W₂).toSA.1 = a • W₁.toSA.1 + b • W₂.toSA.1 := by
      rw [HermCarrier.add_toSA, HermCarrier.smul_toSA, HermCarrier.smul_toSA, AddSubgroup.coe_add,
        selfAdjoint.val_smul, selfAdjoint.val_smul]
    have hb1 : b = 1 - a := by linarith
    have hval : (a • W₁ + b • W₂).toSA.1 - C = a • (W₁.toSA.1 - C) + b • (W₂.toSA.1 - C) := by
      rw [hval0, hb1]; module
    rw [hval]
    have e1 : a • (W₁.toSA.1 - C) = ((a : ℂ)) • (W₁.toSA.1 - C) := by
      ext i j; simp [Matrix.smul_apply, Complex.real_smul]
    have e2 : b • (W₂.toSA.1 - C) = ((b : ℂ)) • (W₂.toSA.1 - C) := by
      ext i j; simp [Matrix.smul_apply, Complex.real_smul]
    rw [e1, e2]
    exact (hW₁C.smul (by rw [Complex.zero_le_real]; exact ha)).add
      (hW₂C.smul (by rw [Complex.zero_le_real]; exact hb))
  · have hvalY : (a • Y₁ + b • Y₂).toSA.1 = a • Y₁.toSA.1 + b • Y₂.toSA.1 := by
      rw [HermCarrier.add_toSA, HermCarrier.smul_toSA, HermCarrier.smul_toSA, AddSubgroup.coe_add,
        selfAdjoint.val_smul, selfAdjoint.val_smul]
    have hvalW : (a • W₁ + b • W₂).toSA.1 = a • W₁.toSA.1 + b • W₂.toSA.1 := by
      rw [HermCarrier.add_toSA, HermCarrier.smul_toSA, HermCarrier.smul_toSA, AddSubgroup.coe_add,
        selfAdjoint.val_smul, selfAdjoint.val_smul]
    rw [hvalY, hY₁, hY₂, hvalW, ptrace2_add, ptrace2_real_smul, ptrace2_real_smul]

section FrobeniusBound
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-- **`Re tr(M²) ≤ (Re tr M)²` for PSD `M`** (`∑λ² ≤ (∑λ)²`). Via Frobenius: `Re tr(M²) =
Re tr(Mᴴ·M) = ‖M‖_F²` (`M` Hermitian) and `‖M‖_F ≤ traceNorm M = Re tr M` (PSD). -/
theorem re_trace_sq_le_sq_re_trace {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℂ}
    (hM : M.PosSemidef) : (M * M).trace.re ≤ ((M.trace).re) ^ 2 := by
  have h1 : (M * M).trace.re = ‖M‖ ^ 2 := by
    rw [← re_trace_conjTranspose_mul_self_eq_frobenius_sq, hM.isHermitian.eq]
  have h2 : ‖M‖ ≤ (M.trace).re :=
    le_trans (frobenius_le_traceNorm M) (le_of_eq (traceNorm_posSemidef hM))
  rw [h1]
  nlinarith [h2, norm_nonneg M]

end FrobeniusBound

/-- **Carrier-norm witness bound: `‖W‖ ≤ Re tr(W.toSA)` when `W` is PSD.** The Hermitian-carrier norm
(`= √(Re tr(W²))`) is bounded by the trace; combined with `tr(Tr₂ W) = tr W`, this bounds every
witness for a fixed `Tr₂ W = M` by `Re tr M`, making `achievableTr2` closed by bounded sequential
compactness. -/
theorem HermCarrier.norm_le_re_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : HermCarrier ι} (hW : W.toSA.1.PosSemidef) : ‖W‖ ≤ (W.toSA.1.trace).re := by
  have hns : (0 : ℝ) ≤ (W.toSA.1.trace).re := (Complex.le_def.mp hW.trace_nonneg).1
  have hsq : ‖W‖ ^ 2 ≤ ((W.toSA.1.trace).re) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, HermCarrier.inner_eq]
    exact re_trace_sq_le_sq_re_trace hW
  nlinarith [hsq, norm_nonneg W, hns]

open scoped Kronecker Topology in
/-- **`achievableTr2 C` is closed.** Every witness `W` for a point `M = Tr₂ W` is norm-bounded by
`Re tr M` (`HermCarrier.norm_le_re_trace` + `trace_ptrace2`); for a convergent `Yₖ → Y` in `S` the
trace bound is uniform, so the witnesses live in a compact PSD ball, a convergent subsequence
`W_{φ k} → W*` is feasible (PSD and `⪰ C` are closed), and `Tr₂` continuity gives
`Y.toSA = Tr₂ W*`. -/
theorem isClosed_achievableTr2 [NeZero n] (C : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    IsClosed (achievableTr2 C) := by
  rw [← isSeqClosed_iff_isClosed]
  intro Yseq Y hmem hconv
  choose W hW hWC hYeq using hmem
  have hcontTr : Continuous fun Z : HermCarrier (Fin n) => (Z.toSA.1.trace).re :=
    Complex.continuous_re.comp <| continuous_finset_sum _ fun i _ =>
      ((continuous_apply i).comp (continuous_apply i)).comp HermCarrier.continuous_toMat
  have htends : Filter.Tendsto (fun k => ((Yseq k).toSA.1.trace).re) Filter.atTop
      (𝓝 ((Y.toSA.1.trace).re)) := (hcontTr.tendsto Y).comp hconv
  obtain ⟨B, hB⟩ := htends.bddAbove_range
  have hbd : ∀ k, ‖W k‖ ≤ B := by
    intro k
    have h := HermCarrier.norm_le_re_trace (hW k)
    have heq : ((W k).toSA.1.trace).re = ((Yseq k).toSA.1.trace).re := by
      rw [hYeq k, trace_ptrace2]
    rw [heq] at h
    exact le_trans h (hB ⟨k, rfl⟩)
  set K : Set (HermCarrier (Fin n × Fin n)) := {Z | Z.toSA.1.PosSemidef ∧ ‖Z‖ ≤ B} with hKdef
  have hKclosed : IsClosed K := by
    refine IsClosed.inter (isClosed_posSemidef.preimage HermCarrier.continuous_toMat) ?_
    exact isClosed_le continuous_norm continuous_const
  have hKcompact : IsCompact K :=
    Metric.isCompact_of_isClosed_isBounded hKclosed
      ((Metric.isBounded_iff_subset_closedBall 0).2 ⟨B, fun Z hZ => by
        simpa [Metric.mem_closedBall, dist_zero_right] using hZ.2⟩)
  have hWK : ∀ k, W k ∈ K := fun k => ⟨hW k, hbd k⟩
  obtain ⟨Wstar, _hWstarK, φ, hφ, hWφ⟩ := hKcompact.tendsto_subseq hWK
  refine ⟨Wstar, ?_, ?_, ?_⟩
  · have hcl : IsClosed {Z : HermCarrier (Fin n × Fin n) | Z.toSA.1.PosSemidef} :=
      isClosed_posSemidef.preimage HermCarrier.continuous_toMat
    exact hcl.mem_of_tendsto hWφ (Filter.Eventually.of_forall fun k => hW (φ k))
  · have hcl : IsClosed {Z : HermCarrier (Fin n × Fin n) | (Z.toSA.1 - C).PosSemidef} :=
      isClosed_posSemidef.preimage (HermCarrier.continuous_toMat.sub continuous_const)
    exact hcl.mem_of_tendsto hWφ (Filter.Eventually.of_forall fun k => hWC (φ k))
  · have h1 : Filter.Tendsto (fun k => (Yseq (φ k)).toSA.1) Filter.atTop (𝓝 (Y.toSA.1)) :=
      (HermCarrier.continuous_toMat.tendsto Y).comp (hconv.comp hφ.tendsto_atTop)
    have h2 : Filter.Tendsto (fun k => ptrace2 (W (φ k)).toSA.1) Filter.atTop
        (𝓝 (ptrace2 Wstar.toSA.1)) :=
      ((continuous_ptrace2.comp HermCarrier.continuous_toMat).tendsto Wstar).comp hWφ
    have h3 : (fun k => (Yseq (φ k)).toSA.1) = fun k => ptrace2 (W (φ k)).toSA.1 := by
      funext k; exact hYeq (φ k)
    rw [h3] at h1
    exact tendsto_nhds_unique h1 h2

/-- `HermCarrier.toMatₗ` is injective (the carrier embeds into matrices). -/
theorem HermCarrier.toMatₗ_injective {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Function.Injective (HermCarrier.toMatₗ (ι := ι)) := by
  intro A B hAB
  have : A.toSA = B.toSA := Subtype.ext hAB
  exact HermCarrier.equivSA.injective this

open scoped Matrix.Norms.L2Operator in
/-- The operator-norm `δ`-ball in the Hermitian carrier — the compact convex set the conic-Farkas
separation pairs against the achievable set `S`. -/
def opBall (δ : ℝ) : Set (HermCarrier (Fin n)) := {Y | ‖Y.toSA.1‖ ≤ δ}

open scoped Matrix.Norms.L2Operator in
theorem opBall_eq_preimage (δ : ℝ) :
    opBall (n := n) δ
      = HermCarrier.toMatₗ ⁻¹' Metric.closedBall (0 : Matrix (Fin n) (Fin n) ℂ) δ := by
  ext Y
  simp only [opBall, Set.mem_setOf_eq, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
  rfl

open scoped Matrix.Norms.L2Operator in
/-- The op-norm ball is convex (linear preimage of a metric ball). -/
theorem convex_opBall (δ : ℝ) : Convex ℝ (opBall (n := n) δ) := by
  rw [opBall_eq_preimage]
  exact (convex_closedBall (0 : Matrix (Fin n) (Fin n) ℂ) δ).linear_preimage HermCarrier.toMatₗ

open scoped Matrix.Norms.L2Operator in
/-- The op-norm ball is compact: it is the preimage of a (compact) closed ball under the proper
closed embedding `toMatₗ` (injective ℝ-linear out of a finite-dimensional space). -/
theorem isCompact_opBall (δ : ℝ) : IsCompact (opBall (n := n) δ) := by
  rw [opBall_eq_preimage]
  exact (LinearMap.isClosedEmbedding_of_injective
    (LinearMap.ker_eq_bot.mpr HermCarrier.toMatₗ_injective)).isProperMap.isCompact_preimage
    (isCompact_closedBall 0 δ)

/-- `Tr₂` preserves Hermiticity. -/
theorem ptrace2_isHermitian {W : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ} (hW : W.IsHermitian) :
    (ptrace2 W).IsHermitian := by
  show (ptrace2 W)ᴴ = ptrace2 W
  ext a b
  rw [Matrix.conjTranspose_apply, ptrace2, ptrace2, star_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [show star (W (b, x) (a, x)) = Wᴴ (a, x) (b, x) from (Matrix.conjTranspose_apply W _ _).symm, hW]

/-- Lift a Hermitian matrix to the Hermitian carrier. -/
def HermCarrier.ofMat {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℂ}
    (hM : M.IsHermitian) : HermCarrier ι :=
  ⟨⟨M, by show star M = M; rw [Matrix.star_eq_conjTranspose]; exact hM⟩⟩

@[simp] theorem HermCarrier.ofMat_toSA {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℂ} (hM : M.IsHermitian) : (HermCarrier.ofMat hM).toSA.1 = M := rfl

/-- A feasible matrix witness `W` (`W ⪰ 0`, `W ⪰ C`) places `Tr₂ W` in the achievable set `S`. -/
theorem mem_achievableTr2_of_matrix {C W : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ}
    (hWh : W.IsHermitian) (hW : W.PosSemidef) (hWC : (W - C).PosSemidef) :
    HermCarrier.ofMat (ptrace2_isHermitian hWh) ∈ achievableTr2 C :=
  ⟨HermCarrier.ofMat hWh, by rw [HermCarrier.ofMat_toSA]; exact hW,
    by rw [HermCarrier.ofMat_toSA]; exact hWC, by rw [HermCarrier.ofMat_toSA, HermCarrier.ofMat_toSA]⟩

open scoped Kronecker in
/-- **`Tr₂(M ⊗ N) = (tr N) • M`** — partial-tracing the second factor of a Kronecker product. With
`N` a trace-1 output state, `Tr₂(M ⊗ N) = M`, so `Tr₂` is surjective onto Hermitian matrices: the
lever for `Y₀ ⪰ 0` in the separation (the achievable set `S` contains the full PSD-cone translate
`Tr₂(posPart C) + M`, so a separating functional bounded below on `S` is nonnegative on the PSD cone). -/
theorem ptrace2_kronecker_eq (M N : Matrix (Fin n) (Fin n) ℂ) :
    ptrace2 (M ⊗ₖ N) = N.trace • M := by
  ext a b
  simp only [ptrace2, Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum, mul_comm]
  rfl

open scoped Kronecker in
/-- The Kronecker product of PSD matrices is PSD (`M⊗N = (√M⊗√N)ᴴ(√M⊗√N)`). -/
theorem posSemidef_kronecker {M N : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosSemidef)
    (hN : N.PosSemidef) : (M ⊗ₖ N).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (psdSqrt hM ⊗ₖ psdSqrt hN)
  have he : (psdSqrt hM ⊗ₖ psdSqrt hN)ᴴ * (psdSqrt hM ⊗ₖ psdSqrt hN) = M ⊗ₖ N := by
    rw [Matrix.conjTranspose_kronecker, (psdSqrt_isHermitian hM).eq, (psdSqrt_isHermitian hN).eq,
      ← Matrix.mul_kronecker_mul, psdSqrt_mul_self hM, psdSqrt_mul_self hN]
  rwa [he] at h

/-- `Tr₂` commutes with complex scalar multiplication. -/
theorem ptrace2_smul (c : ℂ) (A : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    ptrace2 (c • A) = c • ptrace2 A := by
  ext a b
  simp only [ptrace2, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]

open scoped Matrix.Norms.L2Operator Kronecker Topology ComplexOrder in
/-- **Piece 2 — strong duality `choiDualValue ≤ diamondDist`** via geometric Hahn–Banach separation. -/
theorem choiDualValue_le_diamondDist [NeZero n] {K₁ K₂ : Fin m → Matrix (Fin n) (Fin n) ℂ}
    (hK₁ : IsKrausChannel K₁) (hK₂ : IsKrausChannel K₂) :
    choiDualValue K₁ K₂ ≤ diamondDist K₁ K₂ := by
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  set C := choiMatrix (krausMap K₁) - choiMatrix (krausMap K₂) with hCdef
  have hCh : C.IsHermitian := choiDiff_isHermitian K₁ K₂
  by_contra hcon
  rw [not_le] at hcon
  set δ := (diamondDist K₁ K₂ + choiDualValue K₁ K₂) / 2 with hδdef
  have hddnn : (0 : ℝ) ≤ diamondDist K₁ K₂ := diamondDist_nonneg
  have hδ1 : diamondDist K₁ K₂ < δ := by rw [hδdef]; linarith
  have hδ2 : δ < choiDualValue K₁ K₂ := by rw [hδdef]; linarith
  have hδnn : (0 : ℝ) ≤ δ := le_trans hddnn hδ1.le
  have hinfeas := dual_infeasible_of_lt_choiDualValue (K₁ := K₁) (K₂ := K₂) hδ2
  have hdisj : Disjoint (opBall (n := n) δ) (achievableTr2 C) := by
    rw [Set.disjoint_left]
    rintro Y hYball ⟨W, hWp, hWC, hYeq⟩
    exact hinfeas ⟨W.toSA.1, hWp, hWC, by rw [← hYeq]; exact hYball⟩
  obtain ⟨φ, u, v, hball, huv, hS⟩ := geometric_hahn_banach_compact_closed
    (convex_opBall δ) (isCompact_opBall δ) (convex_achievableTr2 C) (isClosed_achievableTr2 C) hdisj
  set Y₀ := (InnerProductSpace.toDual ℝ (HermCarrier (Fin n))).symm φ with hY₀def
  have hφeq : ∀ x, φ x = (Y₀.toSA.1 * x.toSA.1).trace.re := by
    intro x
    have hxx : φ x = (inner ℝ Y₀ x : ℝ) :=
      congrArg (· x) ((InnerProductSpace.toDual ℝ _).apply_symm_apply φ).symm
    rw [hxx, HermCarrier.inner_eq]
  set T := (Y₀.toSA.1.trace).re with hTdef
  have hPp : (posPart hCh).PosSemidef := posPart_posSemidef hCh
  have hPpC : (posPart hCh - C).PosSemidef := by
    rw [posPart_sub_self_eq_negPart hCh]; exact negPart_posSemidef hCh
  have hY₀psd : Y₀.toSA.1.PosSemidef := by
    rw [← HermCarrier.mem_innerDual_psdProperCone, ProperCone.mem_innerDual]
    intro X hX
    rw [SetLike.mem_coe, HermCarrier.mem_psdProperCone] at hX
    rw [HermCarrier.inner_eq, Matrix.trace_mul_comm]
    set M := X.toSA.1 with hMdef
    set N := ((n : ℂ)⁻¹) • (1 : Matrix (Fin n) (Fin n) ℂ) with hNdef
    have hNpsd : N.PosSemidef := by
      apply Matrix.PosSemidef.one.smul
      rw [show ((n : ℂ))⁻¹ = (((n : ℝ)⁻¹ : ℝ) : ℂ) from by
        rw [Complex.ofReal_inv, Complex.ofReal_natCast], Complex.zero_le_real]
      positivity
    have hNtr : N.trace = 1 := by
      rw [hNdef, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul,
        inv_mul_cancel₀ (show (n : ℂ) ≠ 0 by exact_mod_cast NeZero.ne n)]
    set B := (Y₀.toSA.1 * M).trace.re with hBdef
    set A := (Y₀.toSA.1 * ptrace2 (posPart hCh)).trace.re with hAdef
    have key : ∀ t : ℝ, 0 ≤ t → v < A + t * B := by
      intro t ht
      have htc : (0 : ℂ) ≤ (t : ℂ) := by
        rw [Complex.le_def]; exact ⟨by simpa using ht, by simp⟩
      have hMN : ((t : ℂ) • (M ⊗ₖ N)).PosSemidef := (posSemidef_kronecker hX hNpsd).smul htc
      have hWp : (posPart hCh + (t : ℂ) • (M ⊗ₖ N)).PosSemidef := hPp.add hMN
      have hWC : (posPart hCh + (t : ℂ) • (M ⊗ₖ N) - C).PosSemidef := by
        rw [add_sub_right_comm]; exact hPpC.add hMN
      have hmem := mem_achievableTr2_of_matrix (C := C) hWp.isHermitian hWp hWC
      have hlt := hS _ hmem
      rw [hφeq, HermCarrier.ofMat_toSA] at hlt
      have hpt : ptrace2 (posPart hCh + (t : ℂ) • (M ⊗ₖ N))
          = ptrace2 (posPart hCh) + (t : ℂ) • M := by
        rw [ptrace2_add, ptrace2_smul, ptrace2_kronecker_eq, hNtr, one_smul]
      rw [hpt, Matrix.mul_add, Matrix.trace_add, Complex.add_re, Matrix.mul_smul,
        Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero] at hlt
      rw [hAdef, hBdef]; exact hlt
    by_contra hBneg
    rw [not_le] at hBneg
    have hBne : B ≠ 0 := ne_of_lt hBneg
    have hABv : v < A := by simpa using key 0 le_rfl
    have hnB : (0 : ℝ) < -B := by linarith
    have ht0 : (0 : ℝ) ≤ (A - v) / (-B) + 1 :=
      add_nonneg (div_nonneg (by linarith) hnB.le) zero_le_one
    have hk := key _ ht0
    have hcomp : A + ((A - v) / (-B) + 1) * B = v + B := by field_simp [hBne]; ring
    rw [hcomp] at hk
    linarith
  have hTnn : (0 : ℝ) ≤ T := (Complex.le_def.mp hY₀psd.trace_nonneg).1
  have hballbound : δ * T ≤ u := by
    have hδherm : ((δ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
        Complex.star_def, Complex.conj_ofReal]
    have hZmem : HermCarrier.ofMat hδherm ∈ opBall (n := n) δ := by
      show ‖(HermCarrier.ofMat hδherm).toSA.1‖ ≤ δ
      rw [HermCarrier.ofMat_toSA]
      exact le_of_eq (by
        rw [norm_smul, norm_one, mul_one, Complex.norm_real, Real.norm_of_nonneg hδnn])
    have hlt := hball _ hZmem
    rw [hφeq, HermCarrier.ofMat_toSA] at hlt
    have heq : (Y₀.toSA.1 * ((δ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))).trace.re = δ * T := by
      rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, hTdef]; ring
    rw [heq] at hlt
    linarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have htr_real : Y₀.toSA.1.trace = (T : ℂ) := by
    have him : (Y₀.toSA.1.trace).im = 0 := by
      have h := Matrix.trace_conjTranspose Y₀.toSA.1
      rw [hY₀psd.isHermitian.eq] at h
      have h2 := congrArg Complex.im h
      simp only [Complex.star_def, Complex.conj_im] at h2
      linarith
    rw [Complex.ext_iff, Complex.ofReal_re, Complex.ofReal_im, hTdef]
    exact ⟨rfl, him⟩
  have hSbound : v ≤ T * diamondDist K₁ K₂ := by
    have key : ∀ ε : ℝ, 0 < ε → v < (T + ε * n) * diamondDist K₁ K₂ := by
      intro ε hε
      have hTεpos : (0 : ℝ) < T + ε * n := by positivity
      have hTεne : ((↑(T + ε * n) : ℂ)) ≠ 0 := by
        rw [Ne, Complex.ofReal_eq_zero]; exact ne_of_gt hTεpos
      have hεc : (0 : ℂ) < (ε : ℂ) := by rw [Complex.lt_def]; exact ⟨by simpa using hε, by simp⟩
      have hρε : (Y₀.toSA.1 + (ε : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef := by
        rw [add_comm]; exact (Matrix.PosDef.one.smul hεc).add_posSemidef hY₀psd
      set σε := ((↑(T + ε * n) : ℂ)⁻¹) •
        (Y₀.toSA.1 + (ε : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) with hσεdef
      have hσεpd : σε.PosDef := by
        apply hρε.smul
        rw [Complex.lt_def, Complex.inv_re, Complex.inv_im]
        rw [show Complex.normSq (↑(T + ε * n)) = (T + ε * n) ^ 2 from by
          rw [Complex.normSq_ofReal]; ring]
        refine ⟨by positivity, by simp⟩
      have hσεtr : σε.trace = 1 := by
        rw [hσεdef, Matrix.trace_smul, Matrix.trace_add, htr_real, Matrix.trace_smul,
          Matrix.trace_one, Fintype.card_fin, smul_eq_mul, smul_eq_mul,
          show ((T : ℂ) + (ε : ℂ) * (n : ℂ)) = ((T + ε * n : ℝ) : ℂ) from by push_cast; ring,
          inv_mul_cancel₀ hTεne]
      have hW₀p := diamondWitness_posSemidef hσεpd.posSemidef hCh
      have hW₀C := diamondWitness_sub_posSemidef hσεpd hCh
      have hmem := mem_achievableTr2_of_matrix (C := C) hW₀p.isHermitian hW₀p hW₀C
      have hlt := hS _ hmem
      rw [hφeq, HermCarrier.ofMat_toSA] at hlt
      have hYeq : Y₀.toSA.1
          = (↑(T + ε * n) : ℂ) • σε - (ε : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
        rw [hσεdef, smul_smul, mul_inv_cancel₀ hTεne, one_smul]; abel
      have hbound : (Y₀.toSA.1 *
          ptrace2 (diamondWitness hσεpd.posSemidef hCh)).trace.re
          ≤ (T + ε * n) * diamondDist K₁ K₂ := by
        set W₀ := diamondWitness hσεpd.posSemidef hCh with hW₀def
        have hle : (σε * ptrace2 W₀).trace.re ≤ diamondDist K₁ K₂ := by
          rw [Matrix.trace_mul_comm, trace_ptrace2_mul, Matrix.trace_mul_comm]
          exact re_trace_kron_one_mul_diamondWitness_le hK₁ hK₂ hσεpd hσεtr
        have hterm1 : (((↑(T + ε * n) : ℂ) • σε) * ptrace2 W₀).trace.re
            ≤ (T + ε * n) * diamondDist K₁ K₂ := by
          rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, zero_mul, sub_zero]
          exact mul_le_mul_of_nonneg_left hle hTεpos.le
        have hterm2 : (0 : ℝ) ≤
            (((ε : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) * ptrace2 W₀).trace.re := by
          rw [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, smul_eq_mul, Complex.mul_re,
            Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, trace_ptrace2]
          have hW₀tr : (0 : ℝ) ≤ (W₀.trace).re := (Complex.le_def.mp hW₀p.trace_nonneg).1
          positivity
        rw [hYeq, sub_mul, Matrix.trace_sub, Complex.sub_re]
        linarith [hterm1, hterm2]
      linarith [hlt, hbound]
    refine le_of_forall_pos_le_add fun η hη => ?_
    have hk := key (η / (n * diamondDist K₁ K₂ + 1)) (div_pos hη (by positivity))
    have hbnd : η / (n * diamondDist K₁ K₂ + 1) * n * diamondDist K₁ K₂ ≤ η := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [diamondDist_nonneg (K₁ := K₁) (K₂ := K₂), hη.le, mul_nonneg hnpos.le
        (diamondDist_nonneg (K₁ := K₁) (K₂ := K₂))]
    nlinarith [hk, hbnd]
  nlinarith [hballbound, huv, hSbound, hTnn, mul_le_mul_of_nonneg_left hδ1.le hTnn]

open scoped Matrix.Norms.L2Operator in
/-- **Watrous diamond-norm SDP strong duality (unconditional).**
`diamondDist Φ₁ Φ₂ = choiDualValue Φ₁ Φ₂ = inf{‖Tr₂ W‖ : W ⪰ 0, W ⪰ J(Φ₁)−J(Φ₂)}`. Combines weak
duality (`diamondDist_le_choiDualValue`) with the conic-Farkas/Hahn–Banach separation strong-duality
direction (`choiDualValue_le_diamondDist`). The Phase-6AI headline, proven kernel-pure with no
project-local axiom. -/
theorem diamondDist_eq_choiSDP [NeZero n] {K₁ K₂ : Fin m → Matrix (Fin n) (Fin n) ℂ}
    (hK₁ : IsKrausChannel K₁) (hK₂ : IsKrausChannel K₂) :
    diamondDist K₁ K₂ = choiDualValue K₁ K₂ :=
  le_antisymm (diamondDist_le_choiDualValue hK₁ hK₂) (choiDualValue_le_diamondDist hK₁ hK₂)

end SKEFTHawking.QuantumNetwork
