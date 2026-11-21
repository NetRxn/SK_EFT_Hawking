import SKEFTHawking.QuantumNetwork.OneRecordMemoryGapMargin
import SKEFTHawking.QuantumNetwork.FiniteBinaryOptimumStability
import SKEFTHawking.QuantumNetwork.CPTPChannel

/-!
# A trace-norm error budget for the selected timing advantage

The physical memory marginal is positive and trace-preserving. Its trace
norm contracts on Hermitian differences, so one error budget in the
weighted joint states controls both optimized decisions.
-/

set_option autoImplicit false

open Matrix
open scoped ComplexOrder

namespace SKEFTHawking.QuantumNetwork.OneRecordCoherentSchedule

/-- Tracing out the system preserves positivity of the selected density. -/
theorem memoryMarginal_posSemidef {X : Matrix (Fin 4) (Fin 4) ℂ}
    (hX : X.PosSemidef) : (memoryMarginal X).PosSemidef := by
  let emb (s : Fin 2) : Fin 2 → Fin 4 := fun i => finProdFinEquiv (s, i)
  have he : memoryMarginal X = ∑ s : Fin 2, X.submatrix (emb s) (emb s) := by
    ext i j
    simp [memoryMarginal, emb, Matrix.sum_apply]
  rw [he]
  exact Matrix.posSemidef_sum _ (fun s _ => hX.submatrix (emb s))

/-- The system-major memory marginal preserves the full trace. -/
theorem trace_memoryMarginal (X : Matrix (Fin 4) (Fin 4) ℂ) :
    (memoryMarginal X).trace = X.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, memoryMarginal, Matrix.of_apply]
  rw [Finset.sum_comm]
  calc
    _ = ∑ ij : Fin 2 × Fin 2, X (finProdFinEquiv ij) (finProdFinEquiv ij) :=
      (Fintype.sum_prod_type _).symm
    _ = _ := (finProdFinEquiv : (Fin 2 × Fin 2) ≃ Fin (2 * 2)).sum_comp (fun i : Fin 4 => X i i)

private theorem memoryMarginal_sub (X Y : Matrix (Fin 4) (Fin 4) ℂ) :
    memoryMarginal (X - Y) = memoryMarginal X - memoryMarginal Y := by
  ext i j
  simp [memoryMarginal, Finset.sum_sub_distrib]

/-- In the physical system-major coordinates, tracing out the system
contracts trace norm on Hermitian errors. -/
theorem traceNorm_memoryMarginal_le {X : Matrix (Fin 4) (Fin 4) ℂ} (hX : X.IsHermitian) :
    traceNorm (memoryMarginal X) ≤ traceNorm X := by
  conv_lhs => rw [self_eq_posPart_sub_negPart hX]
  rw [memoryMarginal_sub, traceNorm_hermitian_eq_pos_add_neg hX]
  have h := traceNorm_triangle (memoryMarginal (posPart hX)) (-(memoryMarginal (negPart hX)))
  rwa [← sub_eq_add_neg, traceNorm_neg, traceNorm_posSemidef
    (memoryMarginal_posSemidef (posPart_posSemidef hX)), traceNorm_posSemidef
    (memoryMarginal_posSemidef (negPart_posSemidef hX)), trace_memoryMarginal, trace_memoryMarginal] at h


private theorem binary_effect_optimum_traceNorm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P Q : Matrix ι ι ℂ) (hP : P.PosSemidef) (hQ : Q.PosSemidef)
    (ht : P.trace.re + Q.trace.re = 1) :
    IsGreatest {x | ∃ E : Matrix ι ι ℂ, E.PosSemidef ∧ (1 - E).PosSemidef ∧
      (P * E).trace.re + (Q * (1 - E)).trace.re = x} ((1 + traceNorm (P - Q)) / 2) := by
  obtain ⟨hu, ha⟩ := finite_binary_success_optimal (fun _ : Unit => P) (fun _ : Unit => Q)
    (fun _ => hP) (fun _ => hQ) (by simpa only [Fintype.sum_unique] using ht)
  constructor
  · obtain ⟨E, hE, hI, hs⟩ := ha
    exact ⟨E (), hE (), hI (), by simpa only [finite_binary_success, Fintype.sum_unique] using hs⟩
  · rintro x ⟨E, hE, hI, rfl⟩
    simpa only [finite_binary_success, Fintype.sum_unique] using
      hu (fun _ => E) (fun _ => hE) (fun _ => hI)

/-- A single trace-norm budget on the two perturbed weighted joint states
preserves a selected circuit's strict advantage over all memory effects. -/
theorem selected_joint_beats_memory_under_traceNorm_error (a b c d p : ℝ)
    (train : a^2 + b^2 = 1) (offset : c^2 + d^2 = 1) (hd : d ≠ 0)
    (hp : 0 ≤ p) (hp1 : p < 1) (hd1 : d^2 < 1)
    (hJ : (1 - p) * (d^2 / 2) < p)
    (P' Q' : Matrix (Fin 4) (Fin 4) ℂ)
    (hP' : P'.PosSemidef) (hQ' : Q'.PosSemidef) (ht' : P'.trace.re + Q'.trace.re = 1) :
    let q := 1 - p
    let P := (((p / (d^2 / 2) : ℝ) : ℂ)) • coherentSelected a b c d
    let Q := (((2 * q : ℝ) : ℂ)) • dephasedSelected a b c d
    let margin := q * (1 - d^2) * (p - q * (d^2 / 2)) / (2 * (p + q * (1 - d^2)))
    traceNorm (P - P') + traceNorm (Q - Q') < margin →
    ∃ E : Matrix (Fin 4) (Fin 4) ℂ, E.PosSemidef ∧ (1 - E).PosSemidef ∧
      ∀ F : Matrix (Fin 2) (Fin 2) ℂ, F.PosSemidef → (1 - F).PosSemidef →
        (memoryMarginal P' * F).trace.re + (memoryMarginal Q' * (1 - F)).trace.re <
          (P' * E).trace.re + (Q' * (1 - E)).trace.re := by
  intro q P Q margin hErr
  have hInput := one_record_conditional_optimum_with_prior a b c d p train offset hd hp hp1.le
  have hP : P.PosSemidef := (hInput.1 ()).1
  have hQ : Q.PosSemidef := (hInput.1 ()).2
  have htP : P.trace.re = p := (hInput.2.1 ()).1
  have htQ : Q.trace.re = q := (hInput.2.1 ()).2
  have ht : P.trace.re + Q.trace.re = 1 := by rw [htP, htQ]; dsimp [q]; ring
  have hIdeal := selected_memory_and_joint_optima a b c d p train offset hd hp hp1.le
  let memory := q + max 0
    ((p - q + Real.sqrt (p^2 + (q * (1 - 2 * (((a * c - b * d)^2 + a^2) / 2)))^2)) / 2)
  let joint := q + max 0 (p - q * (d^2 / 2))
  have hpM : (memoryMarginal P).PosSemidef := memoryMarginal_posSemidef hP
  have hqM : (memoryMarginal Q).PosSemidef := memoryMarginal_posSemidef hQ
  have htpM : (memoryMarginal P).trace.re + (memoryMarginal Q).trace.re = 1 := by
    simpa only [trace_memoryMarginal] using ht
  have hM0 : (1 + traceNorm (memoryMarginal P - memoryMarginal Q)) / 2 = memory :=
    (binary_effect_optimum_traceNorm _ _ hpM hqM htpM).unique hIdeal.1
  have hJ0 : (1 + traceNorm (P - Q)) / 2 = joint :=
    (binary_effect_optimum_traceNorm P Q hP hQ ht).unique hIdeal.2.1
  have hmargin : margin ≤ joint - memory :=
    (selected_memory_joint_gap_lower a b c d p train offset hp hp1 hd1 hJ).2
  have hPerr : traceNorm (memoryMarginal P - memoryMarginal P') ≤ traceNorm (P - P') := by
    rw [← memoryMarginal_sub]
    exact traceNorm_memoryMarginal_le (hP.isHermitian.sub hP'.isHermitian)
  have hQerr : traceNorm (memoryMarginal Q - memoryMarginal Q') ≤ traceNorm (Q - Q') := by
    rw [← memoryMarginal_sub]
    exact traceNorm_memoryMarginal_le (hQ.isHermitian.sub hQ'.isHermitian)
  have hstrict : (1 + traceNorm (memoryMarginal P' - memoryMarginal Q')) / 2 <
      (1 + traceNorm (P' - Q')) / 2 := by
    have hlt := finite_binary_optimum_lt_of_traceNorm_budget
      (fun _ : Unit => memoryMarginal P) (fun _ : Unit => memoryMarginal Q)
      (fun _ : Unit => memoryMarginal P') (fun _ : Unit => memoryMarginal Q')
      (fun _ : Unit => P) (fun _ : Unit => Q) (fun _ : Unit => P') (fun _ : Unit => Q')
    simp only [Fintype.sum_unique] at hlt
    apply hlt
    linarith only [hPerr, hQerr, hErr, hmargin, hM0, hJ0]
  have htM' : (memoryMarginal P').trace.re + (memoryMarginal Q').trace.re = 1 := by
    simpa only [trace_memoryMarginal] using ht'
  have hM' := binary_effect_optimum_traceNorm _ _
    (memoryMarginal_posSemidef hP') (memoryMarginal_posSemidef hQ') htM'
  obtain ⟨E, hE, hIE, hs⟩ := (binary_effect_optimum_traceNorm P' Q' hP' hQ' ht').1
  refine ⟨E, hE, hIE, fun F hF hIF => ?_⟩
  rw [hs]
  exact (hM'.2 ⟨F, hF, hIF, rfl⟩).trans_lt hstrict

end SKEFTHawking.QuantumNetwork.OneRecordCoherentSchedule
