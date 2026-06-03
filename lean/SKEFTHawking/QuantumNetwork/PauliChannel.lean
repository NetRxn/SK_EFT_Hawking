import SKEFTHawking.QuantumNetwork.NamedChannelDiamondExact

/-!
# General single-qubit Pauli-channel exact diamond distance (Phase 6AH, Wave 6AH.2)

The single-qubit **Pauli channel** `Φ_p(ρ) = ∑ᵢ pᵢ σᵢ ρ σᵢ` (weights `p : Fin 4 → ℝ`, `pᵢ ≥ 0`,
`∑pᵢ = 1`, Pauli basis `σ = {I, X, Y, Z}`) has exact diamond distance to the identity equal to its
**total error probability** `1 − p₀`. This subsumes the named dephasing (`1−(1−γ)=γ`) and
depolarizing (`1−(1−p)=p`) channels as special weight choices, covering all single-qubit Pauli noise
in one exact theorem.

The Choi matrix is Bell-diagonal — `J(Φ_p) = ∑ᵢ pᵢ Bᵢ` with `Bᵢ` the Choi of the single Pauli `σᵢ`,
and the `Bᵢ` orthogonal (`Bᵢ Bⱼ = 2 δᵢⱼ Bᵢ`, `tr Bᵢ = 2`). So the Choi difference
`Δ = ∑ᵢ (pᵢ − ⟦i=0⟧) Bᵢ` has `|Δ| = ∑ᵢ |pᵢ − ⟦i=0⟧| Bᵢ` and `traceNorm Δ = 2∑ᵢ|pᵢ−⟦i=0⟧| = 4(1−p₀)`,
giving `diamondDist = (1/2n)·4(1−p₀) = 1−p₀` (lower bound). The matching upper bound uses the optimal
dual witness with `ptrace₂ W = (1−p₀)·1`. Same machinery as the shipped named-channel exacts.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

/-- The four single-qubit Pauli operators, indexed `0↦I, 1↦X, 2↦Y, 3↦Z`. -/
noncomputable def pauliOp : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => 1
  | 1 => pauliX
  | 2 => pauliY
  | 3 => pauliZ

theorem pauliOp_conjTranspose : ∀ i, (pauliOp i)ᴴ = pauliOp i
  | 0 => Matrix.conjTranspose_one
  | 1 => pauliX_conjTranspose
  | 2 => pauliY_conjTranspose
  | 3 => pauliZ_conjTranspose

theorem pauliOp_mul_self : ∀ i, pauliOp i * pauliOp i = 1
  | 0 => Matrix.one_mul 1
  | 1 => pauliX_mul_self
  | 2 => pauliY_mul_self
  | 3 => pauliZ_mul_self

/-- **General single-qubit Pauli channel** Kraus operators `√(pᵢ)·σᵢ`. -/
noncomputable def pauliKraus (p : Fin 4 → ℝ) : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  fun i => (Real.sqrt (p i) : ℂ) • pauliOp i

/-- The Pauli channel is CPTP for nonnegative weights summing to `1`. -/
theorem isKrausChannel_pauliKraus {p : Fin 4 → ℝ} (h0 : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    IsKrausChannel (pauliKraus p) := by
  unfold IsKrausChannel pauliKraus
  have key : ∀ i, ((Real.sqrt (p i) : ℂ) • pauliOp i)ᴴ * ((Real.sqrt (p i) : ℂ) • pauliOp i)
      = ((p i : ℝ) : ℂ) • 1 := by
    intro i
    rw [Matrix.conjTranspose_smul, smul_mul_smul, pauliOp_conjTranspose, pauliOp_mul_self,
      Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (h0 i)]
  simp_rw [key, ← Finset.sum_smul]
  rw [← Complex.ofReal_sum, hsum, Complex.ofReal_one, one_smul]

/-! ## The Bell blocks `Bᵢ` and their orthogonality

`Bᵢ = aᵢ aᵢᴴ` is the (unnormalised) Bell projector for `σᵢ`, where the column `aᵢ(p) = σᵢ(p.2, p.1)`
vectorises `σᵢ`. The Choi matrix of the single-Pauli conjugation is exactly `Bᵢ`, so
`J(Φ_p) = ∑ᵢ pᵢ Bᵢ`. The Pauli orthonormality `tr(σᵢᴴ σⱼ) = 2δᵢⱼ` becomes the `1×1` inner product
`aᵢᴴ aⱼ = 2δᵢⱼ·1`, which gives `Bᵢ Bⱼ = 2δᵢⱼ Bᵢ` and `tr Bᵢ = 2` by outer-product algebra. -/

/-- The vectorisation column of `σᵢ`: `aᵢ(p) = σᵢ(p.2, p.1)`. -/
noncomputable def aPauli (i : Fin 4) : Matrix (Fin 2 × Fin 2) (Fin 1) ℂ :=
  Matrix.of fun p _ => pauliOp i p.2 p.1

/-- The Bell block `Bᵢ = aᵢ aᵢᴴ` (the Choi matrix of `ρ ↦ σᵢ ρ σᵢ`). -/
noncomputable def bellBlock (i : Fin 4) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  aPauli i * (aPauli i)ᴴ

theorem bellBlock_posSemidef (i : Fin 4) : (bellBlock i).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose _

theorem bellBlock_isHermitian (i : Fin 4) : (bellBlock i).IsHermitian :=
  (bellBlock_posSemidef i).isHermitian

/-- **Pauli orthonormality** as a `1×1` inner product: `aᵢᴴ aⱼ = 2δᵢⱼ·1` (i.e. `tr(σᵢᴴσⱼ)=2δᵢⱼ`). -/
theorem pauli_inner (i j : Fin 4) :
    (aPauli i)ᴴ * aPauli j = (if i = j then (2 : ℂ) else 0) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext a b; fin_cases a; fin_cases b
  fin_cases i <;> fin_cases j <;>
    simp [aPauli, pauliOp, pauliX, pauliY, pauliZ, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.smul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Complex.ext_iff] <;> norm_num

/-- **Orthogonality of the Bell blocks:** `Bᵢ Bⱼ = 2δᵢⱼ Bᵢ`. -/
theorem bellBlock_mul (i j : Fin 4) :
    bellBlock i * bellBlock j = (if i = j then (2 : ℂ) else 0) • bellBlock i := by
  simp only [bellBlock]
  rw [show aPauli i * (aPauli i)ᴴ * (aPauli j * (aPauli j)ᴴ)
        = aPauli i * ((aPauli i)ᴴ * aPauli j) * (aPauli j)ᴴ by simp only [Matrix.mul_assoc],
    pauli_inner i j]
  by_cases h : i = j
  · subst h; rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, if_pos rfl]
  · rw [if_neg h, zero_smul, Matrix.mul_zero, Matrix.zero_mul, zero_smul]

/-- **Trace of a Bell block** `tr Bᵢ = 2`. -/
theorem bellBlock_trace (i : Fin 4) : (bellBlock i).trace = 2 := by
  show (aPauli i * (aPauli i)ᴴ).trace = 2
  rw [Matrix.trace_mul_comm, pauli_inner i i, if_pos rfl, Matrix.trace_smul,
    Matrix.trace_one, smul_eq_mul]
  simp

/-! ## Choi matrix and Choi difference -/

/-- Entrywise form of a Bell block: `Bᵢ(p',q') = σᵢ(p'.2,p'.1)·conj(σᵢ(q'.2,q'.1))`. -/
theorem bellBlock_apply (i : Fin 4) (p' q' : Fin 2 × Fin 2) :
    bellBlock i p' q' = pauliOp i p'.2 p'.1 * star (pauliOp i q'.2 q'.1) := by
  show (aPauli i * (aPauli i)ᴴ) p' q' = _
  rw [Matrix.mul_apply, Fin.sum_univ_one]
  simp only [aPauli, Matrix.conjTranspose_apply, Matrix.of_apply]

/-- **The Pauli-channel Choi matrix is Bell-diagonal:** `J(Φ_p) = ∑ᵢ pᵢ Bᵢ` (nonnegative weights). -/
theorem pauli_choiMatrix {p : Fin 4 → ℝ} (h0 : ∀ i, 0 ≤ p i) :
    choiMatrix (krausMap (pauliKraus p)) = ∑ i, (p i : ℂ) • bellBlock i := by
  ext p' q'
  rw [Matrix.sum_apply]
  simp only [choiMatrix, krausMap, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.smul_apply, bellBlock_apply, smul_eq_mul]
  simp only [Matrix.mul_apply, Matrix.single_apply, pauliKraus, Matrix.smul_apply,
    Matrix.conjTranspose_apply, smul_eq_mul, ite_and, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, star_mul', Complex.star_def,
    Complex.conj_ofReal]
  have hsq : (↑(Real.sqrt (p k)) : ℂ) * ↑(Real.sqrt (p k)) = ↑(p k) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (h0 k)]
  linear_combination (pauliOp k p'.2 p'.1 * (starRingEnd ℂ) (pauliOp k q'.2 q'.1)) * hsq

/-- **The identity-channel Choi matrix is `B₀`.** -/
theorem id_choiMatrix : choiMatrix (krausMap (idKrausPad 3 2)) = bellBlock 0 := by
  ext p' q'
  simp only [choiMatrix, krausMap, idKrausPad, bellBlock, aPauli, pauliOp, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (0 : Fin (3 + 1)) (fun b _ hb => by simp [hb]) (by simp)]
  simp only [if_true, Fin.sum_univ_one, Matrix.single_apply, ite_and, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Matrix.one_apply, eq_comm]
  split_ifs <;> simp_all [Complex.ext_iff]

/-- **Choi difference of the Pauli channel and the identity:** `J(Φ_p) − J(id) = ∑ᵢ cᵢ Bᵢ`
with `cᵢ = pᵢ − ⟦i=0⟧`. -/
theorem pauli_choi_diff {p : Fin 4 → ℝ} (h0 : ∀ i, 0 ≤ p i) :
    choiMatrix (krausMap (pauliKraus p)) - choiMatrix (krausMap (idKrausPad 3 2))
      = ∑ i, ((p i - if i = 0 then 1 else 0 : ℝ) : ℂ) • bellBlock i := by
  have hB0 : bellBlock 0 = ∑ i : Fin 4, (if i = 0 then (1 : ℂ) else 0) • bellBlock i := by
    rw [Finset.sum_eq_single (0 : Fin 4) (fun b _ hb => by simp [hb]) (by simp)]; simp
  rw [pauli_choiMatrix h0, id_choiMatrix, hB0, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← sub_smul]; congr 1
  split_ifs <;> push_cast <;> ring

/-! ## Trace norm of the Choi difference and the diamond distance -/

/-- **Bell-combination product:** `(∑ᵢ aᵢ Bᵢ)(∑ⱼ bⱼ Bⱼ) = ∑ᵢ 2 aᵢ bᵢ Bᵢ` (from orthogonality). -/
theorem bellCombo_mul (a b : Fin 4 → ℂ) :
    (∑ i, a i • bellBlock i) * (∑ j, b j • bellBlock j) = ∑ i, (2 * a i * b i) • bellBlock i := by
  rw [Finset.sum_mul_sum]
  rw [show (∑ i, ∑ j, (a i • bellBlock i) * (b j • bellBlock j))
        = ∑ i, ∑ j, (a i * b j) • (if i = j then (2 : ℂ) else 0) • bellBlock i by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.smul_mul, Matrix.mul_smul, bellBlock_mul, smul_smul]]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [if_neg (Ne.symm hj), zero_smul, smul_zero])
    (by simp)]
  rw [if_pos rfl, smul_smul]; congr 1; ring

/-- **Trace norm of a real Bell combination:** `‖∑ᵢ cᵢ Bᵢ‖₁ = 2·∑ᵢ |cᵢ|`. The candidate `∑ᵢ |cᵢ| Bᵢ`
is PSD and squares to `(∑ᵢ cᵢ Bᵢ)²`, hence equals `|∑ᵢ cᵢ Bᵢ|` by PSD-square uniqueness. -/
theorem traceNorm_bellCombo (c : Fin 4 → ℝ) :
    traceNorm (∑ i, (c i : ℂ) • bellBlock i) = 2 * ∑ i, |c i| := by
  set Δ := ∑ i, (c i : ℂ) • bellBlock i with hΔ
  have hHerm : Δᴴ = Δ := by
    rw [hΔ, Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.conjTranspose_smul, (bellBlock_isHermitian i).eq,
      show star (↑(c i) : ℂ) = ↑(c i) from Complex.conj_ofReal (c i)]
  have hQpsd : (∑ i, ((|c i| : ℝ) : ℂ) • bellBlock i).PosSemidef := by
    refine Matrix.posSemidef_sum _ fun i _ => (bellBlock_posSemidef i).smul ?_
    rw [Complex.le_def]; exact ⟨by simp [abs_nonneg], by simp⟩
  have habs : absOp Δ = ∑ i, ((|c i| : ℝ) : ℂ) • bellBlock i := by
    refine posSemidef_eq_of_mul_self_eq (absOp_posSemidef Δ) hQpsd ?_
    rw [absOp_mul_self, hHerm, hΔ, bellCombo_mul, bellCombo_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [mul_assoc, mul_assoc, ← Complex.ofReal_mul, ← Complex.ofReal_mul, abs_mul_abs_self]
  rw [traceNorm_eq_trace_absOp, habs, Matrix.trace_sum]
  simp_rw [Matrix.trace_smul, bellBlock_trace, smul_eq_mul]
  rw [← Finset.sum_mul, ← Complex.ofReal_sum,
    show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

/-- **Partial trace of a Bell block is the identity:** `Tr₂ Bᵢ = 1` (each `σᵢ` is unitary). -/
theorem ptrace2_bellBlock (i : Fin 4) : ptrace2 (bellBlock i) = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [ptrace2, bellBlock_apply, pauliOp, pauliX, pauliY, pauliZ, Matrix.one_apply,
      Fin.sum_univ_two]

/-- **Trace norm of the Pauli Choi difference** `‖J(Φ_p) − J(id)‖₁ = 4(1 − p₀)`. -/
theorem traceNorm_pauli_choi_diff {p : Fin 4 → ℝ} (h0 : ∀ i, 0 ≤ p i) (h1 : p 0 ≤ 1)
    (hsum : ∑ i, p i = 1) :
    traceNorm (choiMatrix (krausMap (pauliKraus p)) - choiMatrix (krausMap (idKrausPad 3 2)))
      = 4 * (1 - p 0) := by
  rw [pauli_choi_diff h0, traceNorm_bellCombo, Fin.sum_univ_four]
  simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, sub_zero]
  rw [abs_of_nonpos (by linarith), abs_of_nonneg (h0 1), abs_of_nonneg (h0 2), abs_of_nonneg (h0 3)]
  have hs : p 0 + p 1 + p 2 + p 3 = 1 := by rw [← Fin.sum_univ_four]; exact hsum
  linarith

/-- **Pauli-channel diamond-distance lower bound** `diamondDist (pauliKraus p) (id) ≥ 1 − p₀`, from
the Choi trace-norm lower bound and `‖J(Φ_p) − J(id)‖₁ = 4(1−p₀)`. -/
theorem diamondDist_pauliKraus_ge {p : Fin 4 → ℝ} (h0 : ∀ i, 0 ≤ p i) (h1 : p 0 ≤ 1)
    (hsum : ∑ i, p i = 1) :
    1 - p 0 ≤ diamondDist (pauliKraus p) (idKrausPad 3 2) := by
  have hbound := diamondDist_ge_choi_traceNorm (isKrausChannel_pauliKraus h0 hsum)
    (isKrausChannel_idKrausPad 3 2)
  rw [traceNorm_pauli_choi_diff h0 h1 hsum] at hbound
  calc 1 - p 0 = (1 : ℝ) / (2 * (2 : ℕ)) * (4 * (1 - p 0)) := by push_cast; ring
    _ ≤ _ := hbound

/-! ## Optimal dual witness and the exact diamond distance -/

/-- The **optimal dual witness** for the Pauli channel: the positive part of the Choi difference,
`W = ∑_{i≥1} pᵢ Bᵢ`. -/
noncomputable def pauliWitness (p : Fin 4 → ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ∑ i, ((if i = 0 then 0 else p i : ℝ) : ℂ) • bellBlock i

theorem pauliWitness_posSemidef {p : Fin 4 → ℝ} (h0 : ∀ i, 0 ≤ p i) :
    (pauliWitness p).PosSemidef := by
  refine Matrix.posSemidef_sum _ fun i _ => (bellBlock_posSemidef i).smul ?_
  rw [Complex.le_def]; refine ⟨?_, ?_⟩ <;> simp only [Complex.ofReal_re, Complex.ofReal_im,
    Complex.zero_re, Complex.zero_im] <;> split_ifs <;> simp [h0]

/-- `Tr₂ W = (1 − p₀)·1` (each `Tr₂ Bᵢ = 1`, and `∑_{i≥1} pᵢ = 1 − p₀`). -/
theorem ptrace2_pauliWitness {p : Fin 4 → ℝ} (hsum : ∑ i, p i = 1) :
    ptrace2 (pauliWitness p) = ((1 - p 0 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hlin : ptrace2 (pauliWitness p)
      = ∑ i, ((if i = 0 then 0 else p i : ℝ) : ℂ) • ptrace2 (bellBlock i) := by
    ext a b
    simp only [ptrace2, pauliWitness, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hlin]; simp_rw [ptrace2_bellBlock]; rw [← Finset.sum_smul]
  have hw : ∑ i, ((if i = 0 then 0 else p i : ℝ) : ℂ) = ((1 - p 0 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sum]; congr 1
    rw [Fin.sum_univ_four]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
    have hs : p 0 + p 1 + p 2 + p 3 = 1 := by rw [← Fin.sum_univ_four]; exact hsum
    linarith
  rw [hw]

/-- `W ⪰ Δ` in the Loewner order: `W − (J(Φ_p) − J(id)) = (1 − p₀)·B₀ ⪰ 0`. -/
theorem pauliWitness_sub_choi_posSemidef {p : Fin 4 → ℝ} (h0 : ∀ i, 0 ≤ p i) (h1 : p 0 ≤ 1) :
    (pauliWitness p - (choiMatrix (krausMap (pauliKraus p))
      - choiMatrix (krausMap (idKrausPad 3 2)))).PosSemidef := by
  rw [pauli_choi_diff h0, pauliWitness, ← Finset.sum_sub_distrib]
  rw [show (∑ i, (((if i = 0 then 0 else p i : ℝ) : ℂ) • bellBlock i
            - ((p i - if i = 0 then 1 else 0 : ℝ) : ℂ) • bellBlock i))
        = ((1 - p 0 : ℝ) : ℂ) • bellBlock 0 by
      rw [Finset.sum_eq_single (0 : Fin 4)]
      · rw [← sub_smul]; norm_num
      · intro b _ hb; rw [← sub_smul, if_neg hb, if_neg hb]; norm_num
      · simp]
  exact (bellBlock_posSemidef 0).smul (by rw [Complex.le_def]; exact ⟨by simp; linarith, by simp⟩)

/-- **Exact diamond distance of a general single-qubit Pauli channel:**
`diamondDist (pauliKraus p) (id) = 1 − p₀` (total error probability) for nonnegative weights summing
to `1`. Lower bound from the Choi trace-norm; upper bound from the positive-part dual witness with
`Tr₂ W = (1−p₀)·1`. Two-sided exact, with no twirl machinery. -/
theorem diamondDist_pauliKraus_eq {p : Fin 4 → ℝ} (h0 : ∀ i, 0 ≤ p i) (h1 : p 0 ≤ 1)
    (hsum : ∑ i, p i = 1) :
    diamondDist (pauliKraus p) (idKrausPad 3 2) = 1 - p 0 := by
  refine le_antisymm ?_ (diamondDist_pauliKraus_ge h0 h1 hsum)
  have hub := diamondDist_le_dual_witness (isKrausChannel_pauliKraus h0 hsum)
    (isKrausChannel_idKrausPad 3 2) (pauliWitness_posSemidef h0)
    (pauliWitness_sub_choi_posSemidef h0 h1)
  rwa [ptrace2_pauliWitness hsum, norm_smul, norm_one, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (by linarith)] at hub

/-! ## Subsumption

`diamondDist_pauliKraus_eq` subsumes the named single-qubit Pauli channels as special weight choices:
the dephasing channel is the weights `(1−γ, 0, 0, γ)` (giving `1 − (1−γ) = γ`, matching
`diamondDist_dephasing_eq`), and the (Pauli-error) depolarizing channel is `(1−p, p/3, p/3, p/3)`
(giving `1 − (1−p) = p`, matching `diamondDist_depolarizing_eq`) — both instances of the general
total-error-probability formula `1 − p₀`. -/

end SKEFTHawking.QuantumNetwork
