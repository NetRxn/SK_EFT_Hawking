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
open scoped ComplexOrder

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

end SKEFTHawking.QuantumNetwork
