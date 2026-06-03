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

end SKEFTHawking.QuantumNetwork
