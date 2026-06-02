import SKEFTHawking.QuantumNetwork.DiamondNormChoi
import SKEFTHawking.QuantumNetwork.FidelityBounds
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Diamond norm: the Choi operator-norm upper bound (Phase 6AF-11)

This file delivers the **one-sided primal upper bound** on the diamond distance in terms of the
operator norm of the (difference of) Choi matrices,

  `diamondDist Φ₁ Φ₂ ≤ C(n) · ‖J(Φ₁) − J(Φ₂)‖_∞`,

the companion to the maximally-entangled primal *lower* bound `diamondDist_ge_maxEntangled`
(`DiamondNormChoi.lean`). Together they sandwich the diamond distance by the Choi matrix
(`‖J‖₁ / d ≤ ‖·‖_◇ ≤ d · ‖J‖_∞` in the Watrous normalization), the formalizable content of the
Choi-SDP characterization without conic strong duality (the unformalizable piece).

The operator norm `‖·‖` in this file is the **ℓ²-operator norm** on matrices, activated by the
scoped instance `Matrix.Norms.L2Operator`. This file is deliberately separate from the
trace-norm / Frobenius-norm files so that this scoped norm instance never leaks into them.

Invariants: kernel-pure, zero sorry, zero project-local axioms, no `maxHeartbeats`.

## Proof blueprint (sharp constant `d = n`)

For the difference output `T = (Δ⊗id)ρ` (Hermitian, `Δ = Φ₁ − Φ₂` Hermiticity-preserving) with
Choi `C = choiMatrix Φ₁ − choiMatrix Φ₂`:

1. **Vectorization (entrywise).** From `krausMap (tensorKraus K) ρ = ∑ₖ (Kₖ⊗1) ρ (Kₖ⊗1)ᴴ` and
   `choiMatrix (krausMap K) (a,y) (b,y') = ∑ₖ Kₖ y a · conj (Kₖ y' b)`:

      `(krausMap (tensorKraus K) ρ) (y,α) (y',β) = ∑_{a,b} C (a,y) (b,y') · ρ (a,α) (b,β)`,   `C = choiMatrix (krausMap K)`.

2. **Trace–contraction identity.** For any `W` on the doubled (output) space,
   `tr(W · T) = tr(C · M(W,ρ))` where
   `M(W,ρ) (b,y') (a,y) := ∑_{α,β} W (y',β) (y,α) · ρ (a,α) (b,β)`.

3. **`M(W,ρ)` is PSD** when `W, ρ` are PSD (rank-1: `M(|w⟩⟨w|, |v⟩⟨v|) = |u⟩⟨u|`,
   `u (b,y') = ∑_β w (y',β) · conj (v (b,β))`; general by `posSemidef_sum`).

4. **`tr M(W,ρ) ≤ ‖W‖_∞ · n`** for `ρ` a density operator (reduces to
   `tr(W · (1_Y ⊗ ρ_X)) ≤ ‖W‖_∞ · n · tr ρ_X = ‖W‖_∞ · n`).

5. **Brick 2.** `tr(C · M) ≤ ‖C‖_∞ · tr M` for `M` PSD (via `M^{1/2} C M^{1/2} ≤ ‖C‖_∞ M`).
   With `P₊` the positive eigenprojection of `T` (a projection, `‖P₊‖_∞ ≤ 1`),
   `eigPosSum T = tr(P₊ · T) = tr(C · M(P₊,ρ)) ≤ n · ‖C‖_∞` (and likewise for `P₋ = 1 − P₊`).

6. `‖T‖₁ = tr(P₊T) − tr(P₋T) ≤ 2n‖C‖_∞`, hence `diamondDist ≤ ½ · 2n‖C‖_∞ = n · ‖C‖_∞`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

/-- **Brick 1 — trace norm bounded by dimension × operator norm.**
For any square matrix, `‖M‖₁ = ∑ √eig(MᴴM) ≤ (card) · ‖M‖_op`: each singular value
`√eig(MᴴM)` is bounded by `√‖MᴴM‖_op = ‖M‖_op`, since the eigenvalues of `MᴴM` lie in its
spectrum and are dominated by the operator norm. -/
theorem traceNorm_le_card_mul_l2opNorm {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Matrix ι ι ℂ) : traceNorm M ≤ (Fintype.card ι : ℝ) * ‖M‖ := by
  have hP := Matrix.posSemidef_conjTranspose_mul_self M
  have hbound : ∀ i, Real.sqrt (hP.isHermitian.eigenvalues i) ≤ ‖M‖ := by
    intro i
    have hmem : hP.isHermitian.eigenvalues i ∈ spectrum ℝ (Mᴴ * M) :=
      hP.isHermitian.eigenvalues_mem_spectrum_real i
    have hle : |hP.isHermitian.eigenvalues i| ≤ ‖Mᴴ * M‖ := by
      have h := spectrum.norm_le_norm_of_mem hmem
      simpa [Real.norm_eq_abs] using h
    have hnn : 0 ≤ hP.isHermitian.eigenvalues i := hP.eigenvalues_nonneg i
    rw [abs_of_nonneg hnn, l2_opNorm_conjTranspose_mul_self] at hle
    calc Real.sqrt (hP.isHermitian.eigenvalues i)
        ≤ Real.sqrt (‖M‖ * ‖M‖) := Real.sqrt_le_sqrt hle
      _ = ‖M‖ := Real.sqrt_mul_self (norm_nonneg M)
  calc traceNorm M = ∑ _i : ι, Real.sqrt (hP.isHermitian.eigenvalues _i) := rfl
    _ ≤ ∑ _i : ι, ‖M‖ := Finset.sum_le_sum (fun i _ => hbound i)
    _ = (Fintype.card ι : ℝ) * ‖M‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The custom matrix cfc of a constant function is the scalar matrix `c • 1`. -/
theorem cfc_const {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℂ}
    (hM : M.IsHermitian) (c : ℝ) : hM.cfc (fun _ => c) = (c : ℂ) • 1 := by
  have hd : Matrix.diagonal (RCLike.ofReal ∘ (fun _ : ℝ => c) ∘ hM.eigenvalues : ι → ℂ)
      = (c : ℂ) • (1 : Matrix ι ι ℂ) := by
    ext i j
    rw [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases h : i = j <;> simp [h]
  rw [Matrix.IsHermitian.cfc, hd, map_smul, map_one]

/-- Eigenvalues of a Hermitian matrix are bounded by its ℓ²-operator norm. -/
theorem eigenvalue_le_l2opNorm {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (i : ι) : hA.eigenvalues i ≤ ‖A‖ := by
  have h := spectrum.norm_le_norm_of_mem (hA.eigenvalues_mem_spectrum_real i)
  rw [Real.norm_eq_abs] at h
  exact le_trans (le_abs_self _) h

/-- **Loewner bound `A ≤ ‖A‖ • 1`**: for Hermitian `A`, `‖A‖ • 1 − A` is positive semidefinite
(its eigenvalues `‖A‖ − λᵢ` are nonnegative since `λᵢ ≤ ‖A‖`). -/
theorem norm_smul_one_sub_self_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) : (((‖A‖ : ℂ) • 1) - A).PosSemidef := by
  have hcfc : hA.cfc (fun x => ‖A‖ - x) = ((‖A‖ : ℂ) • 1) - A := by
    rw [← cfc_sub hA (fun _ => ‖A‖) (fun x => x), cfc_const hA, cfc_id hA]
  rw [← hcfc]
  exact cfc_posSemidef hA (fun i => by have := eigenvalue_le_l2opNorm hA i; linarith)

/-- **Brick 2 — `tr(A·B) ≤ ‖A‖ · tr B`** (real parts) for Hermitian `A` and PSD `B`.
Since `‖A‖•1 − A ≥ 0` and `B ≥ 0`, `tr((‖A‖•1 − A)·B) ≥ 0` (`trace_mul_nonneg`), which rearranges
to the bound. -/
theorem re_trace_mul_le_l2opNorm_mul_trace {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {A B : Matrix ι ι ℂ} (hA : A.IsHermitian) (hB : B.PosSemidef) :
    (A * B).trace.re ≤ ‖A‖ * (B.trace).re := by
  have hnn : 0 ≤ ((((‖A‖ : ℂ) • 1) - A) * B).trace.re := by
    have := (Complex.le_def.mp
      (trace_mul_nonneg (norm_smul_one_sub_self_posSemidef hA) hB)).1
    simpa using this
  have hexp : ((((‖A‖ : ℂ) • 1) - A) * B).trace = (‖A‖ : ℂ) * B.trace - (A * B).trace := by
    rw [sub_mul, smul_mul_assoc, one_mul, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
  rw [hexp, Complex.sub_re, Complex.mul_re] at hnn
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hnn
  linarith

variable {m n : ℕ}

/-- **Choi matrix of a Kraus channel, entrywise.**
`choiMatrix (krausMap K) (a,y) (b,y') = ∑ₖ Kₖ y a · conj(Kₖ y' b)`. -/
theorem choiMatrix_krausMap_apply (K : Fin m → Matrix (Fin n) (Fin n) ℂ) (a y b y' : Fin n) :
    choiMatrix (krausMap K) (a, y) (b, y')
      = ∑ k, K k y a * (starRingEnd ℂ) (K k y' b) := by
  simp only [choiMatrix, krausMap, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.single_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [ite_and, Finset.sum_ite_eq, Finset.mem_univ, if_true, ite_mul, zero_mul,
    mul_ite, mul_zero, starRingEnd_apply]
  rw [mul_one]

/-- **Step 1 — vectorization (entrywise).** The stabilized output `(Φ⊗id)ρ` expressed
through the Choi matrix `C = choiMatrix (krausMap K)`:
`(krausMap (tensorKraus K) ρ) (y,α) (y',β) = ∑_{a,b} C (a,y) (b,y') · ρ (a,α) (b,β)`. -/
theorem krausMap_tensorKraus_apply (K : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (y α y' β : Fin n) :
    krausMap (tensorKraus K) ρ (y, α) (y', β)
      = ∑ a, ∑ b, choiMatrix (krausMap K) (a, y) (b, y') * ρ (a, α) (b, β) := by
  simp_rw [choiMatrix_krausMap_apply]
  simp only [krausMap, tensorKraus, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, starRingEnd_apply]
  simp only [apply_ite (star : ℂ → ℂ), star_zero, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm, Finset.sum_congr rfl (fun b _ => Finset.sum_comm), Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **The Choi contraction `M(W,ρ)`** dual to the stabilized channel: the matrix on the doubled
space with `M(W,ρ) (b,y') (a,y) = ∑_{α,β} W (y',β) (y,α) · ρ (a,α) (b,β)`. It is the partner of
`W` under the trace–contraction identity `tr(W·(Φ⊗id)ρ) = tr(J(Φ)·M(W,ρ))`. -/
noncomputable def choiContraction (W ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  fun p q => ∑ α, ∑ β, W (p.2, β) (q.2, α) * ρ (q.1, α) (p.1, β)

/-- **Step 2 — the trace–contraction identity.** For any `W` on the doubled space,
`tr(W · (Φ⊗id)ρ) = tr(J(Φ) · M(W,ρ))`, moving the pairing from the (large) output side to the
Choi matrix paired against the contraction `M(W,ρ)`. -/
theorem trace_mul_krausMap_tensorKraus (K : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (W ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    (W * krausMap (tensorKraus K) ρ).trace
      = (choiMatrix (krausMap K) * choiContraction W ρ).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, choiContraction,
    Fintype.sum_prod_type]
  simp_rw [krausMap_tensorKraus_apply]
  simp only [Finset.mul_sum]
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type', ← Fintype.sum_prod_type',
    ← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type', ← Fintype.sum_prod_type',
    ← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv
    { toFun := fun x => (((((x.1.2, x.1.1.1.2), x.2), x.1.1.1.1.1), x.1.1.2), x.1.1.1.1.2),
      invFun := fun w => (((((w.1.1.2, w.2), w.1.1.1.1.2), w.1.2), w.1.1.1.1.1), w.1.1.1.2),
      left_inv := by rintro ⟨⟨⟨⟨⟨p, q⟩, r⟩, s⟩, t⟩, u⟩; rfl,
      right_inv := by rintro ⟨⟨⟨⟨⟨p, q⟩, r⟩, s⟩, t⟩, u⟩; rfl }
    _ _ (by rintro ⟨⟨⟨⟨⟨p, q⟩, r⟩, s⟩, t⟩, u⟩; dsimp only [Equiv.coe_fn_mk]; ring)

end SKEFTHawking.QuantumNetwork
