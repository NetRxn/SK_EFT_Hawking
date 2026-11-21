import SKEFTHawking.QuantumNetwork.OneRecordCoherentSchedule
import SKEFTHawking.StoppingRetainedClockRecordSufficiency

/-!
# Conditional decision for one-record coherent timing

Conditioning both hypotheses on the antisymmetric schedule outcome gives one
fixed record. Equal conditional priors then permit an exact comparison of
record-only rules, the existing memory-X measurement, and the best joint effect.
-/

noncomputable section
open Matrix
open scoped ComplexOrder

namespace SKEFTHawking.QuantumNetwork.OneRecordCoherentSchedule

/-- The equally weighted coherent hypothesis conditioned on successful timing selection. -/
noncomputable def coherentPriorState (a b c d : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (((d^2)⁻¹ : ℝ) : ℂ) • coherentSelected a b c d

/-- The projection onto the normalized antisymmetric timing branch. -/
noncomputable def antisymmetricEffect (a b c d : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (((d^2 / 2)⁻¹ : ℝ) : ℂ) • coherentSelected a b c d

/-- Give the hypotheses equal priors after conditioning each on the same
selected record. The record-only success is one half. The best joint effect
has success `1 - d²/4`, attained by the antisymmetric projection. -/
theorem one_record_conditional_binary_optimum (a b c d : ℝ)
    (train : a^2 + b^2 = 1) (offset : c^2 + d^2 = 1) (hd : d ≠ 0) :
    let P (_ : Unit) := coherentPriorState a b c d
    let Q (_ : Unit) := dephasedSelected a b c d
    let E (_ : Unit) := antisymmetricEffect a b c d
    (∀ r, (P r).PosSemidef ∧ (Q r).PosSemidef) ∧
    ((∑ r, (P r).trace.re) + ∑ r, (Q r).trace.re) = 1 ∧
    (∀ r, (E r).PosSemidef ∧ (1 - E r).PosSemidef) ∧
    (∀ rule : Unit → Bool, finite_binary_record_success P Q rule = 1/2) ∧
    (∀ F : Unit → Matrix (Fin 4) (Fin 4) ℂ, (∀ r, (F r).PosSemidef) →
      (∀ r, (1 - F r).PosSemidef) → finite_binary_success P Q F ≤ 1 - d^2 / 4) ∧
    finite_binary_success P Q E = 1 - d^2/4 := by
  intro P Q E
  let C := coherentSelected a b c d
  let D := dephasedSelected a b c d
  let A := symmetricSelected a b c d
  let mass : ℝ := d^2/2
  let scale : ℝ := (d^2)⁻¹
  have hm : 0 < mass := div_pos (sq_pos_of_ne_zero hd) (by norm_num)
  have hd2 : (d^2 : ℝ) ≠ 0 := pow_ne_zero _ hd
  have hscale : 0 ≤ scale := inv_nonneg.mpr (sq_nonneg _)
  have hbudget : 0 ≤ scale - 1/2 := by
    have hsmall : d^2 ≤ 1 := by nlinarith [sq_nonneg c]
    have hinv : (1 : ℝ) ≤ (d^2)⁻¹ := by
      rw [← one_div]
      exact (le_div_iff₀ (sq_pos_of_ne_zero hd)).2 (by simpa using hsmall)
    change 0 ≤ (d^2)⁻¹ - 1/2
    linarith
  obtain ⟨hC, hD, _, hc, _, hdt, _⟩ := selected_density_contrast a b c d train offset hd
  change C.PosSemidef at hC
  change D.PosSemidef at hD
  change C.trace.re = mass at hc
  change D.trace.re = 1/2 at hdt
  obtain ⟨hA, hAB, hDsplit⟩ := dephasedSelected_split a b c d
  change A.PosSemidef at hA
  change A * C = 0 at hAB
  change D = (1/2 : ℂ) • (C + A) at hDsplit
  have hP (r : Unit) : (P r).PosSemidef := hC.smul (Complex.zero_le_real.mpr hscale)
  have hE (r : Unit) : (E r).PosSemidef := hC.smul (Complex.zero_le_real.mpr (inv_nonneg.mpr hm.le))
  have hCE (r : Unit) : C * E r = C := by
    change C * (((mass⁻¹ : ℝ) : ℂ) • C) = C
    rw [Matrix.mul_smul, coherentSelected_sq a b c d train offset hd, smul_smul]
    change (((mass⁻¹ : ℝ) : ℂ) * (mass : ℂ)) • C = C
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ hm.ne', Complex.ofReal_one, one_smul]
  have hAE (r : Unit) : A * E r = 0 := by
    change A * (((mass⁻¹ : ℝ) : ℂ) • C) = 0
    rw [Matrix.mul_smul, hAB, smul_zero]
  have hI (r : Unit) : (1 - E r).PosSemidef := by
    apply one_sub_posSemidef_of_projection (hE r).isHermitian
    change (((mass⁻¹ : ℝ) : ℂ) • C) * E r = ((mass⁻¹ : ℝ) : ℂ) • C
    rw [Matrix.smul_mul, hCE r]
  have scaled_mass : scale * mass = 1/2 := by
    change (d^2)⁻¹ * (d^2 / 2) = 1/2
    rw [← mul_div_assoc, inv_mul_cancel₀ hd2]
  have hPt (r : Unit) : (P r).trace.re = 1/2 := by
    change ((scale : ℂ) • C).trace.re = 1/2
    rw [Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul, hc, scaled_mass]
  have score (F : Unit → Matrix (Fin 4) (Fin 4) ℂ) :
      finite_binary_success P Q F = 1/2 + (scale - 1/2)*(C * F ()).trace.re -
        (1/2)*(A * F ()).trace.re := by
    simp only [finite_binary_success, Fintype.sum_unique]
    change (((scale : ℂ) • C) * F ()).trace.re + (D * (1 - F ())).trace.re = _
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul,
      Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, Complex.sub_re, hdt]
    have hhalf : (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) := by norm_num
    rw [hDsplit, Matrix.smul_mul, Matrix.add_mul, Matrix.trace_smul,
      Matrix.trace_add, smul_eq_mul, hhalf, Complex.re_ofReal_mul, Complex.add_re]
    ring
  have limit : (1/2 : ℝ) + (scale - 1/2)*mass = 1 - d^2/4 := by
    calc
      _ = 1/2 + scale*mass - (1/2)*mass := by ring
      _ = _ := by rw [scaled_mass]; dsimp [mass]; ring
  refine ⟨fun r => ⟨hP r, hD⟩, ?_, fun r => ⟨hE r,hI r⟩, ?_, ?_, ?_⟩
  · rw [Fintype.sum_unique, Fintype.sum_unique, hPt ()]
    change (1/2 : ℝ) + D.trace.re = 1
    rw [hdt]
    norm_num
  · intro rule
    simp only [finite_binary_record_success, Fintype.sum_unique, hPt]
    change (if rule () then (1/2 : ℝ) else D.trace.re) = 1/2
    rw [hdt]
    simp
  · intro F hF hIF
    have hbound : (C * F ()).trace.re ≤ mass := hc ▸ re_trace_mul_le_of_one_sub_posSemidef hC (hIF ())
    have hnonneg : 0 ≤ (A * F ()).trace.re := (Complex.le_def.mp (trace_mul_nonneg hA (hF ()))).1
    rw [score, ← limit]
    linarith [mul_le_mul_of_nonneg_left hbound hbudget]
  · rw [score, hCE (), hAE (), hc, Matrix.trace_zero, Complex.zero_re, mul_zero, sub_zero, limit]

/-- Guessing the coherent hypothesis on memory X minus has success three quarters
in the same equal-prior conditional experiment. -/
theorem one_record_memoryX_binary_success (a b c d : ℝ)
    (train : a^2 + b^2 = 1) (offset : c^2 + d^2 = 1) (hd : d ≠ 0) :
    let P (_ : Unit) := coherentPriorState a b c d
    let Q (_ : Unit) := dephasedSelected a b c d
    let E (_ : Unit) := memoryXReadout.operators 1 ⟨0, by decide⟩
    (∀ r, (E r).PosSemidef ∧ (1 - E r).PosSemidef) ∧
    finite_binary_success P Q E = 3/4 := by
  intro P Q E
  let C := coherentSelected a b c d
  let D := dephasedSelected a b c d
  obtain ⟨hE,hI,_,hCT⟩ := memoryXReadout_effects C
  obtain ⟨_,_,hDT,_⟩ := memoryXReadout_effects D
  refine ⟨fun _ => ⟨hE,hI⟩, ?_⟩
  obtain ⟨_,hminus,hplus,_⟩ := one_record_readout_weights a b c d train offset hd
  rw [finite_binary_success, Fintype.sum_unique, Fintype.sum_unique]
  change ((((d^2)⁻¹ : ℝ) : ℂ) • C * E ()).trace.re +
    (D * (1 - E ())).trace.re = 3/4
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul,
    ← hCT, ← hDT, hminus, hplus, ← mul_div_assoc, inv_mul_cancel₀ (pow_ne_zero _ hd)]
  norm_num

/-- The fixed selected record is insufficient by the positive-semidefinite
comparability criterion for binary readout. -/
theorem one_record_conditional_incomparable (a b c d : ℝ)
    (train : a^2 + b^2 = 1) (offset : c^2 + d^2 = 1) (hd : d ≠ 0) :
    let P := coherentPriorState a b c d
    let Q := dephasedSelected a b c d
    ¬ ((P - Q).PosSemidef ∨ (Q - P).PosSemidef) := by
  intro P Q hsign
  let E (_ : Unit) := antisymmetricEffect a b c d
  obtain ⟨hPQ, htrace, hE, hrec, _, hscore⟩ :=
    one_record_conditional_binary_optimum a b c d train offset hd
  obtain ⟨rule, hRule⟩ := (finite_binary_record_sufficient_iff (fun _ : Unit => P)
    (fun _ => Q) (fun r => (hPQ r).1) (fun r => (hPQ r).2) htrace).2 (fun _ => hsign)
  have hle := hRule E (fun r => (hE r).1) (fun r => (hE r).2)
  rw [hrec rule, hscore] at hle
  nlinarith [sq_nonneg c]

end SKEFTHawking.QuantumNetwork.OneRecordCoherentSchedule
