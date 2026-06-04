import SKEFTHawking.QuantumNetwork.ErrorBasisDiamond
import SKEFTHawking.QuantumNetwork.GateFidelity

/-!
# SPAM (measurement) error and process fidelity (Phase 6AK, Wave 6AK.6)

This wave rounds out the device-characterisation substrate.

* **SPAM / measurement bit-flip channel.** A symmetric readout (state-preparation-and-measurement)
  error is the bit-flip channel `Φ_q(ρ) = (1−q)ρ + q·XρX` (a measurement that returns the wrong
  classical bit with probability `q`). As a Pauli channel with weights `(1−q, q, 0, 0)` its diamond
  distance to the identity is exactly `q` (a special case of 6AH.2 / `diamondDist_pauliKraus_eq`).

* **Process fidelity.** The process (entanglement) fidelity `F_pro(Φ) = (1/d²)∑ₖ|tr Kₖ|²` is exposed
  as a named quantity, and the 6AG identity `avgGateFidelity_eq` is restated for it:
  `F_avg(Φ) = (d·F_pro(Φ) + 1)/(d+1)`. For the SPAM bit-flip channel `F_pro = 1 − q`.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix

/-! ## SPAM / measurement bit-flip channel -/

/-- The **SPAM (readout) bit-flip channel** with error probability `q`: the Pauli channel with
weights `(1−q, q, 0, 0)` (identity with probability `1−q`, bit flip `X` with probability `q`). -/
noncomputable def spamBitFlipKraus (q : ℝ) : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  pauliKraus (fun i => if i = 0 then 1 - q else if i = 1 then q else 0)

/-- **Exact diamond distance of the SPAM bit-flip channel:** `diamondDist (spamBitFlipKraus q) (id)
= q` for `0 ≤ q ≤ 1` — the readout error probability. Direct instance of the single-qubit Pauli
exact diamond distance. -/
theorem diamondDist_spamBitFlip_eq {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    diamondDist (spamBitFlipKraus q) (idKrausPad 3 2) = q := by
  have hw0 : ∀ i, 0 ≤ (fun i : Fin 4 => if i = 0 then 1 - q else if i = 1 then q else 0) i := by
    intro i; fin_cases i <;> simp <;> linarith
  have hsum : (∑ i, (fun i : Fin 4 => if i = 0 then 1 - q else if i = 1 then q else 0) i) = 1 := by
    simp only [Fin.sum_univ_four, Fin.reduceEq, if_true, if_false]; ring
  have hp1 : (fun i : Fin 4 => if i = 0 then 1 - q else if i = 1 then q else 0) 0 ≤ 1 := by
    simp; linarith
  rw [spamBitFlipKraus, diamondDist_pauliKraus_eq hw0 hp1 hsum]
  simp

/-! ## Process (entanglement) fidelity -/

variable {d : ℕ}

/-- **Process fidelity** of a Kraus channel — definitionally the entanglement fidelity
`F_pro(Φ) = (1/d²)∑ₖ|tr Kₖ|²`. Named separately because process-fidelity benchmarks (e.g. from
gate-set tomography) report this quantity directly. -/
noncomputable def processFidelity {m : ℕ} (K : Fin m → Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  entanglementFidelity K

/-- **Average-gate-fidelity ↔ process-fidelity bridge:** `F_avg(Φ) = (d·F_pro(Φ) + 1)/(d+1)` — the
6AG identity `avgGateFidelity_eq` restated for the process fidelity. -/
theorem avgGateFidelity_eq_processFidelity {m : ℕ} [NeZero d]
    (K : Fin m → Matrix (Fin d) (Fin d) ℂ) (hK : IsKrausChannel K) :
    avgGateFidelity K = ((d : ℝ) * processFidelity K + 1) / ((d : ℝ) + 1) :=
  avgGateFidelity_eq K hK

/-- Trace of a single-qubit Pauli operator: `tr σᵢ = 2·⟦i=0⟧`. -/
theorem pauliOp_trace_eq (i : Fin 4) : (pauliOp i).trace = if i = 0 then (2 : ℂ) else 0 := by
  fin_cases i <;> simp [pauliOp, pauliX, pauliY, pauliZ, Matrix.trace_fin_two]

/-- **Process fidelity of a Pauli channel** equals its identity weight: `F_pro(Φ_w) = w₀`. -/
theorem processFidelity_pauliKraus {w : Fin 4 → ℝ} (h0 : 0 ≤ w 0) :
    processFidelity (pauliKraus w) = w 0 := by
  unfold processFidelity entanglementFidelity
  rw [Fin.sum_univ_four]
  simp only [pauliKraus, Matrix.trace_smul, smul_eq_mul, pauliOp_trace_eq, Fin.reduceEq, if_true,
    if_false, mul_zero, map_zero, add_zero, Complex.normSq_mul, Complex.normSq_ofReal]
  have h2 : Complex.normSq 2 = 4 := by simp [Complex.normSq]; norm_num
  rw [Real.mul_self_sqrt h0, h2]; ring

/-- **Process fidelity of the SPAM bit-flip channel:** `F_pro = 1 − q` (the readout success
probability). -/
theorem processFidelity_spamBitFlip {q : ℝ} (h1 : q ≤ 1) :
    processFidelity (spamBitFlipKraus q) = 1 - q := by
  rw [spamBitFlipKraus, processFidelity_pauliKraus (by simp; linarith)]
  simp

end SKEFTHawking.QuantumNetwork
