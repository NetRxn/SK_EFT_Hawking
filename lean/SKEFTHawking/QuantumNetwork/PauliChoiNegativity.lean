import SKEFTHawking.QuantumNetwork.LogNegativity

/-!
# Entanglement-generating capacity of a Pauli channel via its Choi state (Phase 6AK, Wave FU-7)

The repeaterless rate-*ceiling* `E_N(output) ≤ E_N(Choi)` for an arbitrary channel is LOCC-gapped (it
needs the Bell-measurement / classical-communication teleportation-simulation that Mathlib lacks — the
same gap that fences the PLOB secret-key bound). But the *channel's own entanglement measure* — the
(log-)negativity of its **normalised Choi state** — is exactly computable for the teleportation-covariant
Pauli class, and that is a genuine, axiom-free FU-7 brick: it is the channel's entanglement-generating
capacity (the entanglement of the Choi state `Ω_Φ = (id ⊗ Φ)|Φ⁺⟩⟨Φ⁺|`).

The single-qubit Pauli channel `Φ_p(ρ) = ∑ᵢ pᵢ σᵢ ρ σᵢ` has the Bell-diagonal Choi matrix
`J(Φ_p) = ∑ᵢ pᵢ Bᵢ` (`pauli_choiMatrix`), with each `Bᵢ` of trace `2`. Its **normalised** Choi state is
therefore `Ω_Φ = ½ J(Φ_p) = ∑ᵢ (pᵢ/2) Bᵢ = bellDiagState p` — exactly the Bell-diagonal density matrix
whose negativity / log-negativity we already computed in closed form (`BellNegativity.lean`,
`LogNegativity.lean`). So:

- `pauliChannelChoiState p = bellDiagState p` (the normalised Choi state is Bell-diagonal);
- the channel's Choi-state **negativity** is `N(Ω_Φ) = ½(∑ⱼ|μⱼ(p)| − 1)` with
  `μⱼ(p) = pⱼ − ½ yⱼ ∑ᵢ yᵢ pᵢ` (`bellPTeig`);
- the channel's Choi-state **log-negativity** (entanglement-generating capacity) is
  `E_N(Ω_Φ) = log₂(∑ⱼ |μⱼ(p)|)`;
- worked instance: the **dephasing** channel `(1−γ, 0, 0, γ)` has `N(Ω_Φ) = ½|2γ−1|`, vanishing
  (entanglement-breaking Choi) exactly at the fully-dephasing point `γ = ½`.

This is distinct from — and does not require — the LOCC-gapped output≤Choi rate-ceiling; it is the
channel's intrinsic entanglement measure, read off its Choi state.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder

/-- The **normalised Choi state** of the single-qubit Pauli channel `Φ_p`: `Ω_Φ = ½ J(Φ_p)`. (The
unnormalised Choi matrix `J(Φ_p) = ∑ᵢ pᵢ Bᵢ` has trace `2`, so the `½` makes it a density matrix.) -/
noncomputable def pauliChannelChoiState (p : Fin 4 → ℝ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (2⁻¹ : ℂ) • choiMatrix (krausMap (pauliKraus p))

/-- **The normalised Pauli-channel Choi state is Bell-diagonal:** `Ω_Φ = bellDiagState p`. -/
theorem pauliChannelChoiState_eq_bellDiagState {p : Fin 4 → ℝ} (h0 : ∀ i, 0 ≤ p i) :
    pauliChannelChoiState p = bellDiagState p := by
  rw [pauliChannelChoiState, pauli_choiMatrix h0, bellDiagState, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul]
  congr 1
  push_cast
  ring

/-- **Negativity of the Pauli-channel Choi state** in terms of the actual normalised Choi density
matrix: `N(Ω_Φ) = ½(‖Ω_Φ^Γ‖₁ − 1) = negativityBellDiag p`. -/
theorem pauliChannelChoi_negativity {p : Fin 4 → ℝ} (h0 : ∀ i, 0 ≤ p i) :
    (traceNorm (pt2 (pauliChannelChoiState p)) - 1) / 2 = negativityBellDiag p := by
  rw [pauliChannelChoiState_eq_bellDiagState h0, negativityBellDiag]

/-- **The Pauli channel's entanglement-generating capacity** — the log-negativity of its normalised
Choi state — in closed form: `E_N(Ω_Φ) = log₂(∑ⱼ |μⱼ(p)|)`, where `μⱼ(p) = pⱼ − ½ yⱼ ∑ᵢ yᵢ pᵢ` are the
partial-transpose eigenvalues. -/
theorem pauliChannelChoi_logNegativity_eq {p : Fin 4 → ℝ} (h0 : ∀ i, 0 ≤ p i) :
    logNegativity (pauliChannelChoiState p) = Real.logb 2 (∑ j, |bellPTeig p j|) := by
  rw [pauliChannelChoiState_eq_bellDiagState h0, logNegativity, traceNorm_pt2_bellDiagState]

/-- **PPT / separability criterion for the Pauli-channel Choi state:** the Choi state has zero
negativity (is PPT, hence — by the 2-qubit Horodecki theorem, cited — separable / the channel is
entanglement-breaking) exactly when all partial-transpose eigenvalues are nonnegative. -/
theorem pauliChannelChoi_separable_iff {p : Fin 4 → ℝ} (hsum : ∑ i, p i = 1) :
    negativityBellDiag p = 0 ↔ ∀ j, 0 ≤ bellPTeig p j :=
  ppt_bellDiagState_iff p hsum

/-- **Worked instance — the dephasing channel `(1−γ, 0, 0, γ)`:** its Choi-state negativity is
`N(Ω_Φ) = ½|2γ − 1|`. The entanglement-generating capacity vanishes (the Choi state becomes PPT /
entanglement-breaking) exactly at the fully-dephasing point `γ = ½`. -/
theorem dephasingChoi_negativity (γ : ℝ) :
    negativityBellDiag ![1 - γ, 0, 0, γ] = |2 * γ - 1| / 2 := by
  have e0 : bellPTeig ![1 - γ, 0, 0, γ] 0 = 1 / 2 := by
    simp [bellPTeig, bellY, Fin.sum_univ_four]; ring
  have e1 : bellPTeig ![1 - γ, 0, 0, γ] 1 = (1 - 2 * γ) / 2 := by
    simp [bellPTeig, bellY, Fin.sum_univ_four]; ring
  have e2 : bellPTeig ![1 - γ, 0, 0, γ] 2 = (2 * γ - 1) / 2 := by
    simp [bellPTeig, bellY, Fin.sum_univ_four]; ring
  have e3 : bellPTeig ![1 - γ, 0, 0, γ] 3 = 1 / 2 := by
    simp [bellPTeig, bellY, Fin.sum_univ_four]; ring
  rw [negativityBellDiag_eq, Fin.sum_univ_four, e0, e1, e2, e3]
  have hb1 : |(1 - 2 * γ) / 2| = |2 * γ - 1| / 2 := by
    rw [abs_div, abs_sub_comm]; norm_num
  have hb2 : |(2 * γ - 1) / 2| = |2 * γ - 1| / 2 := by rw [abs_div]; norm_num
  rw [hb1, hb2, show |(1 / 2 : ℝ)| = 1 / 2 from by norm_num]
  ring

end SKEFTHawking.QuantumNetwork
