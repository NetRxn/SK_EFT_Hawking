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

end SKEFTHawking.QuantumNetwork
