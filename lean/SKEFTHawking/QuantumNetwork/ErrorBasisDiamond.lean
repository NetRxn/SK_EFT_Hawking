import SKEFTHawking.QuantumNetwork.PauliChannel

/-!
# Exact diamond distance of a unitary-error-basis channel (Phase 6AK, Wave 6AK.3)

The single-qubit Pauli-channel exact diamond distance (`diamondDist_pauliKraus_eq`, 6AH.2) is a
special case of a dimension-general fact about **unitary error bases**. Let `{Uᵢ}_{i=0}^{M}` be a
family of unitary operators on `ℂ^n` with `U₀ = 1` and Hilbert–Schmidt orthogonality
`tr(Uᵢᴴ Uⱼ) = n·δᵢⱼ` (a Hermitian or non-Hermitian *nice error basis*). For nonnegative weights
`p : Fin (M+1) → ℝ` summing to `1` the **error-basis channel** `Φ_p(ρ) = ∑ᵢ pᵢ Uᵢ ρ Uᵢᴴ` has exact
diamond distance to the identity equal to its **total error probability**:

`diamondDist (errorBasisKraus E p) (idKrausPad M n) = 1 − p₀`.

The Choi matrix is block-diagonal in the vectorised basis (`J(Φ_p) = ∑ᵢ pᵢ Bᵢ`, `Bᵢ = vec(Uᵢ)vec(Uᵢ)ᴴ`)
with `Bᵢ Bⱼ = n·δᵢⱼ Bᵢ` and `tr Bᵢ = n`. Hence `‖J(Φ_p) − J(id)‖₁ = 2n(1 − p₀)`, the Choi trace-norm
lower bound gives `diamondDist ≥ (1/2n)·2n(1−p₀) = 1 − p₀`, and the optimal dual witness
`W = ∑_{i≥1} pᵢ Bᵢ` with `Tr₂ W = (1−p₀)·1` matches the upper bound. The single-qubit Pauli result is
the `n = 2` instance; the two-qubit Pauli result is the `n = 4` instance.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

/-- A **unitary error basis** of `M+1` operators on `ℂ^n`: a family `{Uᵢ}` of unitaries with
`U₀ = 1` and Hilbert–Schmidt orthogonality `tr(Uᵢᴴ Uⱼ) = n·δᵢⱼ`. (Completeness `M+1 = n²` is not
required; any orthonormal unitary family with distinguished identity works.) -/
structure UnitaryErrorBasis (n M : ℕ) where
  /-- The `M+1` basis operators. -/
  op : Fin (M + 1) → Matrix (Fin n) (Fin n) ℂ
  /-- The distinguished `0`-index operator is the identity. -/
  op_zero : op 0 = 1
  /-- Each operator is unitary (`Uᵢᴴ Uᵢ = 1`). -/
  op_unitary : ∀ i, (op i)ᴴ * op i = 1
  /-- Hilbert–Schmidt orthogonality: `tr(Uᵢᴴ Uⱼ) = n·δᵢⱼ`. -/
  op_orthonormal : ∀ i j, ((op i)ᴴ * op j).trace = if i = j then (n : ℂ) else 0

variable {n M : ℕ}

/-- **Error-basis channel** Kraus operators `√(pᵢ)·Uᵢ`. -/
noncomputable def errorBasisKraus (E : UnitaryErrorBasis n M) (p : Fin (M + 1) → ℝ) :
    Fin (M + 1) → Matrix (Fin n) (Fin n) ℂ :=
  fun i => (Real.sqrt (p i) : ℂ) • E.op i

/-- The error-basis channel is CPTP for nonnegative weights summing to `1`. -/
theorem isKrausChannel_errorBasisKraus (E : UnitaryErrorBasis n M) {p : Fin (M + 1) → ℝ}
    (h0 : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) : IsKrausChannel (errorBasisKraus E p) := by
  unfold IsKrausChannel errorBasisKraus
  have key : ∀ i, ((Real.sqrt (p i) : ℂ) • E.op i)ᴴ * ((Real.sqrt (p i) : ℂ) • E.op i)
      = ((p i : ℝ) : ℂ) • 1 := by
    intro i
    rw [Matrix.conjTranspose_smul, smul_mul_smul, E.op_unitary, Complex.star_def,
      Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (h0 i)]
  simp_rw [key, ← Finset.sum_smul]
  rw [← Complex.ofReal_sum, hsum, Complex.ofReal_one, one_smul]

/-! ## Vectorised basis blocks and their orthogonality -/

/-- The vectorisation column of `Uᵢ`: `aᵢ(p) = Uᵢ(p.2, p.1)`. -/
noncomputable def aVec (E : UnitaryErrorBasis n M) (i : Fin (M + 1)) :
    Matrix (Fin n × Fin n) (Fin 1) ℂ :=
  Matrix.of fun p _ => E.op i p.2 p.1

/-- The block `Bᵢ = aᵢ aᵢᴴ` (the Choi matrix of `ρ ↦ Uᵢ ρ Uᵢᴴ`). -/
noncomputable def ebBlock (E : UnitaryErrorBasis n M) (i : Fin (M + 1)) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  aVec E i * (aVec E i)ᴴ

theorem ebBlock_posSemidef (E : UnitaryErrorBasis n M) (i : Fin (M + 1)) :
    (ebBlock E i).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose _

theorem ebBlock_isHermitian (E : UnitaryErrorBasis n M) (i : Fin (M + 1)) :
    (ebBlock E i).IsHermitian :=
  (ebBlock_posSemidef E i).isHermitian

/-- The vectorised inner product is the Hilbert–Schmidt inner product: `aᵢᴴ aⱼ = tr(Uᵢᴴ Uⱼ)·1`. -/
theorem aVec_inner (E : UnitaryErrorBasis n M) (i j : Fin (M + 1)) :
    (aVec E i)ᴴ * aVec E j = (((E.op i)ᴴ * E.op j).trace) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext a b
  fin_cases a; fin_cases b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, aVec, Matrix.of_apply,
    Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

/-- **Orthogonality of the blocks:** `Bᵢ Bⱼ = n·δᵢⱼ Bᵢ`. -/
theorem ebBlock_mul (E : UnitaryErrorBasis n M) (i j : Fin (M + 1)) :
    ebBlock E i * ebBlock E j = (if i = j then (n : ℂ) else 0) • ebBlock E i := by
  simp only [ebBlock]
  rw [show aVec E i * (aVec E i)ᴴ * (aVec E j * (aVec E j)ᴴ)
        = aVec E i * ((aVec E i)ᴴ * aVec E j) * (aVec E j)ᴴ by simp only [Matrix.mul_assoc],
    aVec_inner, E.op_orthonormal]
  by_cases h : i = j
  · subst h; simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  · rw [if_neg h, zero_smul, Matrix.mul_zero, Matrix.zero_mul, zero_smul]

/-- **Trace of a block** `tr Bᵢ = n`. -/
theorem ebBlock_trace (E : UnitaryErrorBasis n M) (i : Fin (M + 1)) :
    (ebBlock E i).trace = (n : ℂ) := by
  show (aVec E i * (aVec E i)ᴴ).trace = _
  rw [Matrix.trace_mul_comm, aVec_inner, E.op_orthonormal i i, if_pos rfl, Matrix.trace_smul,
    Matrix.trace_one, smul_eq_mul]
  simp

/-- Entrywise form of a block: `Bᵢ(p',q') = Uᵢ(p'.2,p'.1)·conj(Uᵢ(q'.2,q'.1))`. -/
theorem ebBlock_apply (E : UnitaryErrorBasis n M) (i : Fin (M + 1)) (p' q' : Fin n × Fin n) :
    ebBlock E i p' q' = E.op i p'.2 p'.1 * star (E.op i q'.2 q'.1) := by
  show (aVec E i * (aVec E i)ᴴ) p' q' = _
  rw [Matrix.mul_apply, Fin.sum_univ_one]
  simp only [aVec, Matrix.conjTranspose_apply, Matrix.of_apply]

/-- **Partial trace of a block is the identity:** `Tr₂ Bᵢ = 1` (each `Uᵢ` is unitary). -/
theorem ptrace2_ebBlock (E : UnitaryErrorBasis n M) (i : Fin (M + 1)) :
    ptrace2 (ebBlock E i) = (1 : Matrix (Fin n) (Fin n) ℂ) := by
  ext a b
  simp only [ptrace2, ebBlock_apply]
  have hu := congrFun (congrFun (E.op_unitary i) b) a
  rw [Matrix.mul_apply] at hu
  simp only [Matrix.conjTranspose_apply] at hu
  rw [show (1 : Matrix (Fin n) (Fin n) ℂ) a b = (1 : Matrix (Fin n) (Fin n) ℂ) b a from by
      simp [Matrix.one_apply, eq_comm], ← hu]
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

/-! ## Choi matrix and Choi difference -/

/-- **The error-basis-channel Choi matrix is block-diagonal:** `J(Φ_p) = ∑ᵢ pᵢ Bᵢ`. -/
theorem eb_choiMatrix (E : UnitaryErrorBasis n M) {p : Fin (M + 1) → ℝ} (h0 : ∀ i, 0 ≤ p i) :
    choiMatrix (krausMap (errorBasisKraus E p)) = ∑ i, (p i : ℂ) • ebBlock E i := by
  ext p' q'
  rw [Matrix.sum_apply]
  simp only [choiMatrix, krausMap, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.smul_apply, ebBlock_apply, smul_eq_mul]
  simp only [Matrix.mul_apply, Matrix.single_apply, errorBasisKraus, Matrix.smul_apply,
    Matrix.conjTranspose_apply, smul_eq_mul, ite_and, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, star_mul', Complex.star_def,
    Complex.conj_ofReal]
  have hsq : (↑(Real.sqrt (p k)) : ℂ) * ↑(Real.sqrt (p k)) = ↑(p k) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (h0 k)]
  linear_combination (E.op k p'.2 p'.1 * (starRingEnd ℂ) (E.op k q'.2 q'.1)) * hsq

/-- **The identity-channel Choi matrix is `B₀`** (`U₀ = 1`). -/
theorem id_choiMatrix_eb (E : UnitaryErrorBasis n M) :
    choiMatrix (krausMap (idKrausPad M n)) = ebBlock E 0 := by
  ext p' q'
  rw [ebBlock_apply, E.op_zero]
  simp only [choiMatrix, krausMap, idKrausPad, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply]
  rw [Finset.sum_eq_single (0 : Fin (M + 1)) (fun b _ hb => by simp [hb]) (by simp)]
  simp only [if_true, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Matrix.one_apply, eq_comm]
  split_ifs <;> simp_all [Complex.ext_iff]

/-- **Choi difference** `J(Φ_p) − J(id) = ∑ᵢ cᵢ Bᵢ` with `cᵢ = pᵢ − ⟦i=0⟧`. -/
theorem eb_choi_diff (E : UnitaryErrorBasis n M) {p : Fin (M + 1) → ℝ} (h0 : ∀ i, 0 ≤ p i) :
    choiMatrix (krausMap (errorBasisKraus E p)) - choiMatrix (krausMap (idKrausPad M n))
      = ∑ i, ((p i - if i = 0 then 1 else 0 : ℝ) : ℂ) • ebBlock E i := by
  have hB0 : ebBlock E 0 = ∑ i, (if i = 0 then (1 : ℂ) else 0) • ebBlock E i := by
    rw [Finset.sum_eq_single (0 : Fin (M + 1)) (fun b _ hb => by simp [hb]) (by simp)]; simp
  rw [eb_choiMatrix E h0, id_choiMatrix_eb E, hB0, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← sub_smul]; congr 1
  split_ifs <;> push_cast <;> ring

/-! ## Trace norm of the Choi difference and the diamond distance -/

/-- **Block-combination product:** `(∑ᵢ aᵢ Bᵢ)(∑ⱼ bⱼ Bⱼ) = ∑ᵢ n·aᵢ bᵢ Bᵢ`. -/
theorem ebCombo_mul (E : UnitaryErrorBasis n M) (a b : Fin (M + 1) → ℂ) :
    (∑ i, a i • ebBlock E i) * (∑ j, b j • ebBlock E j)
      = ∑ i, ((n : ℂ) * a i * b i) • ebBlock E i := by
  rw [Finset.sum_mul_sum]
  rw [show (∑ i, ∑ j, (a i • ebBlock E i) * (b j • ebBlock E j))
        = ∑ i, ∑ j, (a i * b j) • (if i = j then (n : ℂ) else 0) • ebBlock E i by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.smul_mul, Matrix.mul_smul, ebBlock_mul, smul_smul]]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [if_neg (Ne.symm hj), zero_smul, smul_zero])
    (by simp)]
  rw [if_pos rfl, smul_smul]; congr 1; ring

/-- **Trace norm of a real block combination:** `‖∑ᵢ cᵢ Bᵢ‖₁ = n·∑ᵢ |cᵢ|`. -/
theorem traceNorm_ebCombo (E : UnitaryErrorBasis n M) (c : Fin (M + 1) → ℝ) :
    traceNorm (∑ i, (c i : ℂ) • ebBlock E i) = (n : ℝ) * ∑ i, |c i| := by
  set Δ := ∑ i, (c i : ℂ) • ebBlock E i with hΔ
  have hHerm : Δᴴ = Δ := by
    rw [hΔ, Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.conjTranspose_smul, (ebBlock_isHermitian E i).eq,
      show star (↑(c i) : ℂ) = ↑(c i) from Complex.conj_ofReal (c i)]
  have hQpsd : (∑ i, ((|c i| : ℝ) : ℂ) • ebBlock E i).PosSemidef := by
    refine Matrix.posSemidef_sum _ fun i _ => (ebBlock_posSemidef E i).smul ?_
    rw [Complex.le_def]; exact ⟨by simp [abs_nonneg], by simp⟩
  have habs : absOp Δ = ∑ i, ((|c i| : ℝ) : ℂ) • ebBlock E i := by
    refine posSemidef_eq_of_mul_self_eq (absOp_posSemidef Δ) hQpsd ?_
    rw [absOp_mul_self, hHerm, hΔ, ebCombo_mul, ebCombo_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [mul_assoc, mul_assoc, ← Complex.ofReal_mul, ← Complex.ofReal_mul, abs_mul_abs_self]
  rw [traceNorm_eq_trace_absOp, habs, Matrix.trace_sum]
  simp_rw [Matrix.trace_smul, ebBlock_trace, smul_eq_mul]
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, ← Complex.ofReal_natCast n, ← Complex.ofReal_mul,
    Complex.ofReal_re]
  ring

/-- `∑ᵢ |pᵢ − ⟦i=0⟧| = 2(1 − p₀)` for nonnegative weights summing to `1` with `p₀ ≤ 1`. -/
theorem sum_abs_eb_coeff {p : Fin (M + 1) → ℝ} (h0 : ∀ i, 0 ≤ p i) (h1 : p 0 ≤ 1)
    (hsum : ∑ i, p i = 1) :
    ∑ i, |p i - if i = 0 then 1 else 0| = 2 * (1 - p 0) := by
  have hcongr : ∀ i, |p i - if i = 0 then (1 : ℝ) else 0|
      = p i + if i = 0 then (1 - 2 * p 0) else 0 := by
    intro i; split_ifs with h
    · subst h; rw [abs_of_nonpos (by linarith)]; ring
    · rw [sub_zero, abs_of_nonneg (h0 i)]; ring
  rw [Finset.sum_congr rfl fun i _ => hcongr i, Finset.sum_add_distrib, hsum,
    Finset.sum_ite_eq' Finset.univ (0 : Fin (M + 1)) (fun _ => 1 - 2 * p 0)]
  simp only [Finset.mem_univ, if_true]; ring

/-- **Trace norm of the Choi difference** `‖J(Φ_p) − J(id)‖₁ = 2n(1 − p₀)`. -/
theorem traceNorm_eb_choi_diff (E : UnitaryErrorBasis n M) {p : Fin (M + 1) → ℝ}
    (h0 : ∀ i, 0 ≤ p i) (h1 : p 0 ≤ 1) (hsum : ∑ i, p i = 1) :
    traceNorm (choiMatrix (krausMap (errorBasisKraus E p))
        - choiMatrix (krausMap (idKrausPad M n)))
      = 2 * (n : ℝ) * (1 - p 0) := by
  rw [eb_choi_diff E h0, traceNorm_ebCombo, sum_abs_eb_coeff h0 h1 hsum]; ring

/-- **Lower bound** `diamondDist (errorBasisKraus E p) (id) ≥ 1 − p₀`. -/
theorem diamondDist_errorBasisKraus_ge (E : UnitaryErrorBasis n M) [NeZero n]
    {p : Fin (M + 1) → ℝ} (h0 : ∀ i, 0 ≤ p i) (h1 : p 0 ≤ 1) (hsum : ∑ i, p i = 1) :
    1 - p 0 ≤ diamondDist (errorBasisKraus E p) (idKrausPad M n) := by
  have hbound := diamondDist_ge_choi_traceNorm (isKrausChannel_errorBasisKraus E h0 hsum)
    (isKrausChannel_idKrausPad M n)
  rw [traceNorm_eb_choi_diff E h0 h1 hsum] at hbound
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  calc 1 - p 0 = (1 : ℝ) / (2 * (n : ℕ)) * (2 * (n : ℝ) * (1 - p 0)) := by
        field_simp
    _ ≤ _ := hbound

/-! ## Optimal dual witness and the exact diamond distance -/

/-- The **optimal dual witness** `W = ∑_{i≥1} pᵢ Bᵢ`. -/
noncomputable def ebWitness (E : UnitaryErrorBasis n M) (p : Fin (M + 1) → ℝ) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  ∑ i, ((if i = 0 then 0 else p i : ℝ) : ℂ) • ebBlock E i

theorem ebWitness_posSemidef (E : UnitaryErrorBasis n M) {p : Fin (M + 1) → ℝ} (h0 : ∀ i, 0 ≤ p i) :
    (ebWitness E p).PosSemidef := by
  refine Matrix.posSemidef_sum _ fun i _ => (ebBlock_posSemidef E i).smul ?_
  rw [Complex.le_def]; refine ⟨?_, ?_⟩ <;> simp only [Complex.ofReal_re, Complex.ofReal_im,
    Complex.zero_re, Complex.zero_im] <;> split_ifs <;> simp [h0]

/-- `Tr₂ W = (1 − p₀)·1`. -/
theorem ptrace2_ebWitness (E : UnitaryErrorBasis n M) {p : Fin (M + 1) → ℝ} (hsum : ∑ i, p i = 1) :
    ptrace2 (ebWitness E p) = ((1 - p 0 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have hlin : ptrace2 (ebWitness E p)
      = ∑ i, ((if i = 0 then 0 else p i : ℝ) : ℂ) • ptrace2 (ebBlock E i) := by
    ext a b
    simp only [ptrace2, ebWitness, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hlin]; simp_rw [ptrace2_ebBlock]; rw [← Finset.sum_smul]
  have hw : ∑ i, ((if i = 0 then 0 else p i : ℝ) : ℂ) = ((1 - p 0 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sum]; congr 1
    have hsub : ∀ i, (if i = 0 then (0 : ℝ) else p i) = p i - if i = 0 then p 0 else 0 := by
      intro i; split_ifs with h
      · subst h; ring
      · ring
    rw [Finset.sum_congr rfl fun i _ => hsub i, Finset.sum_sub_distrib, hsum,
      Finset.sum_ite_eq' Finset.univ (0 : Fin (M + 1)) (fun _ => p 0)]
    simp
  rw [hw]

/-- `W ⪰ Δ` in the Loewner order: `W − (J(Φ_p) − J(id)) = (1 − p₀)·B₀ ⪰ 0`. -/
theorem ebWitness_sub_choi_posSemidef (E : UnitaryErrorBasis n M) {p : Fin (M + 1) → ℝ}
    (h0 : ∀ i, 0 ≤ p i) (h1 : p 0 ≤ 1) :
    (ebWitness E p - (choiMatrix (krausMap (errorBasisKraus E p))
      - choiMatrix (krausMap (idKrausPad M n)))).PosSemidef := by
  rw [eb_choi_diff E h0, ebWitness, ← Finset.sum_sub_distrib]
  rw [show (∑ i, (((if i = 0 then 0 else p i : ℝ) : ℂ) • ebBlock E i
            - ((p i - if i = 0 then 1 else 0 : ℝ) : ℂ) • ebBlock E i))
        = ((1 - p 0 : ℝ) : ℂ) • ebBlock E 0 by
      rw [Finset.sum_eq_single (0 : Fin (M + 1))]
      · rw [← sub_smul]; norm_num
      · intro b _ hb; rw [← sub_smul, if_neg hb, if_neg hb]; norm_num
      · simp]
  exact (ebBlock_posSemidef E 0).smul (by rw [Complex.le_def]; exact ⟨by simp; linarith, by simp⟩)

/-- **Exact diamond distance of a unitary-error-basis channel:**
`diamondDist (errorBasisKraus E p) (id) = 1 − p₀` (total error probability), for nonnegative weights
summing to `1`. Lower bound from the Choi trace-norm; upper bound from the positive-part dual witness
with `Tr₂ W = (1−p₀)·1`. Two-sided exact, dimension-general, no twirl machinery. -/
theorem diamondDist_errorBasisKraus_eq (E : UnitaryErrorBasis n M) [NeZero n]
    {p : Fin (M + 1) → ℝ} (h0 : ∀ i, 0 ≤ p i) (h1 : p 0 ≤ 1) (hsum : ∑ i, p i = 1) :
    diamondDist (errorBasisKraus E p) (idKrausPad M n) = 1 - p 0 := by
  refine le_antisymm ?_ (diamondDist_errorBasisKraus_ge E h0 h1 hsum)
  have hub := diamondDist_le_dual_witness (isKrausChannel_errorBasisKraus E h0 hsum)
    (isKrausChannel_idKrausPad M n) (ebWitness_posSemidef E h0)
    (ebWitness_sub_choi_posSemidef E h0 h1)
  rwa [ptrace2_ebWitness E hsum, norm_smul, norm_one, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (by linarith)] at hub

/-! ## Instance: the single-qubit Pauli basis (`n = 2`) -/

/-- Hilbert–Schmidt orthonormality of the single-qubit Pauli basis: `tr(σᵢᴴ σⱼ) = 2δᵢⱼ`. -/
theorem pauliOp_trace_orthonormal (i j : Fin 4) :
    ((pauliOp i)ᴴ * pauliOp j).trace = if i = j then (2 : ℂ) else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [pauliOp, pauliX, pauliY, pauliZ, Matrix.trace, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_two, Matrix.one_apply] <;> norm_num

/-- The single-qubit Pauli operators as a unitary error basis on `ℂ²`. -/
noncomputable def pauliUEB : UnitaryErrorBasis 2 3 where
  op := pauliOp
  op_zero := rfl
  op_unitary i := by rw [pauliOp_conjTranspose, pauliOp_mul_self]
  op_orthonormal := pauliOp_trace_orthonormal

/-- **Single-qubit Pauli diamond distance re-derived from the error-basis theorem** (`n = 2`):
`diamondDist (pauliKraus p) (id) = 1 − p₀`. Confirms `diamondDist_pauliKraus_eq` (6AH.2) is the
`n = 2` instance of the dimension-general formula. -/
theorem diamondDist_pauliKraus_eq_of_errorBasis {p : Fin 4 → ℝ} (h0 : ∀ i, 0 ≤ p i)
    (h1 : p 0 ≤ 1) (hsum : ∑ i, p i = 1) :
    diamondDist (pauliKraus p) (idKrausPad 3 2) = 1 - p 0 :=
  diamondDist_errorBasisKraus_eq pauliUEB h0 h1 hsum

/-! ## Instance: the two-qubit Pauli basis (`n = 4`) -/

open scoped Kronecker

section Reindex

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (e : α ≃ β)

omit [Fintype α] [Fintype β] in
theorem reindex_one_eq : Matrix.reindex e e (1 : Matrix α α ℂ) = 1 := by
  rw [Matrix.reindex_apply, Matrix.submatrix_one_equiv]

omit [DecidableEq α] [DecidableEq β] in
theorem reindex_mul_eq (Mx Nx : Matrix α α ℂ) :
    Matrix.reindex e e Mx * Matrix.reindex e e Nx = Matrix.reindex e e (Mx * Nx) := by
  simp only [Matrix.reindex_apply]; rw [Matrix.submatrix_mul_equiv]

omit [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] in
theorem reindex_conjTranspose_eq (Mx : Matrix α α ℂ) :
    (Matrix.reindex e e Mx)ᴴ = Matrix.reindex e e Mxᴴ := by
  simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix]

omit [DecidableEq α] [DecidableEq β] in
theorem trace_reindex_eq (Mx : Matrix α α ℂ) : (Matrix.reindex e e Mx).trace = Mx.trace := by
  rw [Matrix.reindex_apply, Matrix.trace, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp e.symm (fun j => Mx j j)

end Reindex

/-- The 16 two-qubit Pauli operators `σᵢ ⊗ σⱼ` on `ℂ⁴`, indexed by `Fin 16 ≃ Fin 4 × Fin 4`
(reindexing the `Fin 2 × Fin 2` tensor carrier to `Fin 4`). -/
noncomputable def twoQubitPauliOp (k : Fin 16) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.reindex (finProdFinEquiv (m := 2) (n := 2)) (finProdFinEquiv (m := 2) (n := 2))
    (pauliOp ((finProdFinEquiv (m := 4) (n := 4)).symm k).1
      ⊗ₖ pauliOp ((finProdFinEquiv (m := 4) (n := 4)).symm k).2)

/-- The two-qubit Pauli operators as a unitary error basis on `ℂ⁴`. -/
noncomputable def pauli2UEB : UnitaryErrorBasis 4 15 where
  op := twoQubitPauliOp
  op_zero := by
    show Matrix.reindex _ _ (pauliOp _ ⊗ₖ pauliOp _) = 1
    rw [show ((finProdFinEquiv (m := 4) (n := 4)).symm 0).1 = 0 from rfl,
      show ((finProdFinEquiv (m := 4) (n := 4)).symm 0).2 = 0 from rfl,
      show pauliOp 0 = 1 from rfl, Matrix.one_kronecker_one, reindex_one_eq]
  op_unitary i := by
    show (Matrix.reindex _ _ (pauliOp _ ⊗ₖ pauliOp _))ᴴ
        * Matrix.reindex _ _ (pauliOp _ ⊗ₖ pauliOp _) = 1
    rw [reindex_conjTranspose_eq, reindex_mul_eq, Matrix.conjTranspose_kronecker,
      ← Matrix.mul_kronecker_mul, pauliOp_conjTranspose, pauliOp_conjTranspose,
      pauliOp_mul_self, pauliOp_mul_self, Matrix.one_kronecker_one, reindex_one_eq]
  op_orthonormal i j := by
    show Matrix.trace ((Matrix.reindex _ _ (pauliOp _ ⊗ₖ pauliOp _))ᴴ
        * Matrix.reindex _ _ (pauliOp _ ⊗ₖ pauliOp _)) = _
    rw [reindex_conjTranspose_eq, reindex_mul_eq, trace_reindex_eq,
      Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker,
      pauliOp_trace_orthonormal, pauliOp_trace_orthonormal]
    set f := finProdFinEquiv (m := 4) (n := 4) with hf
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, if_pos rfl, if_pos rfl]; norm_num
    · rw [if_neg hij]
      by_cases ha : (f.symm i).1 = (f.symm j).1
      · by_cases hb : (f.symm i).2 = (f.symm j).2
        · exact absurd (f.symm.injective (Prod.ext ha hb)) hij
        · rw [if_neg hb, mul_zero]
      · rw [if_neg ha, zero_mul]

/-- **Two-qubit Pauli channel** Kraus operators `√(p_{ij})·(σᵢ ⊗ σⱼ)` (16 weights). -/
noncomputable def twoQubitPauliKraus (p : Fin 16 → ℝ) : Fin 16 → Matrix (Fin 4) (Fin 4) ℂ :=
  errorBasisKraus pauli2UEB p

/-- **Exact diamond distance of a general two-qubit Pauli channel:**
`diamondDist (twoQubitPauliKraus p) (id) = 1 − p₀₀` (the total error probability), for nonnegative
weights summing to `1`. The `n = 4` instance of the dimension-general error-basis theorem; covers the
dominant two-qubit-gate / crosstalk error model. -/
theorem diamondDist_twoQubitPauliKraus_eq {p : Fin 16 → ℝ} (h0 : ∀ i, 0 ≤ p i) (h1 : p 0 ≤ 1)
    (hsum : ∑ i, p i = 1) :
    diamondDist (twoQubitPauliKraus p) (idKrausPad 15 4) = 1 - p 0 :=
  diamondDist_errorBasisKraus_eq pauli2UEB h0 h1 hsum

end SKEFTHawking.QuantumNetwork
