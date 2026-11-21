import SKEFTHawking.QuantumNetwork.OneRecordMemoryErrorBudget
import SKEFTHawking.QuantumNetwork.NegativityGeneral

/-!
# Conditioning errors for the selected timing circuit

The trace norm of the difference of normalized positive branches is
controlled by the unnormalized difference and the nominal selection mass.
The actual coherent and dephased masses give the two amplification factors
in the circuit certificate. Conditional priors may differ between the
nominal and perturbed experiments.
-/

set_option autoImplicit false

open Matrix
open scoped ComplexOrder

namespace SKEFTHawking.QuantumNetwork

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Scale a selected matrix by the reciprocal of its real trace. -/
noncomputable def traceNormalized (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (((X.trace.re)⁻¹ : ℝ) : ℂ) • X

theorem traceNormalized_posSemidef {X : Matrix ι ι ℂ} (hX : X.PosSemidef) :
    (traceNormalized X).PosSemidef :=
  hX.smul (Complex.zero_le_real.mpr (inv_nonneg.mpr (traceNorm_posSemidef hX ▸ traceNorm_nonneg X)))

omit [DecidableEq ι] in
theorem trace_traceNormalized_re {X : Matrix ι ι ℂ} (hX : 0 < X.trace.re) :
    (traceNormalized X).trace.re = 1 := by
  rw [traceNormalized, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul, inv_mul_cancel₀ hX.ne']

private theorem traceNorm_real_smul (p : ℝ) (X : Matrix ι ι ℂ) :
    traceNorm ((p : ℂ) • X) = |p| * traceNorm X := by
  simp only [traceNorm_eq_physlib, Matrix.traceNorm_smul, Complex.norm_real, Real.norm_eq_abs]

/-- Postselection amplifies the branch error by at most twice the inverse
nominal selection mass. The observed mass may differ from the nominal one. -/
theorem traceNorm_traceNormalized_sub_le {X Y : Matrix ι ι ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (hx : 0 < X.trace.re) (hy : 0 < Y.trace.re) :
    traceNorm (traceNormalized X - traceNormalized Y) ≤
      2 / X.trace.re * traceNorm (X - Y) := by
  let x := X.trace.re
  let y := Y.trace.re
  have hx' : 0 < x := hx
  have hy' : 0 < y := hy
  have heq : traceNormalized X - traceNormalized Y =
      ((x⁻¹ : ℝ) : ℂ) • (X - Y) + ((x⁻¹ - y⁻¹ : ℝ) : ℂ) • Y := by
    dsimp only [traceNormalized, x, y]
    push_cast
    rw [smul_sub, sub_smul]
    abel
  have hmass : |x - y| ≤ traceNorm (X - Y) := by
    simpa only [x, y, Matrix.trace_sub, Complex.sub_re] using
      traceNorm_ge_abs_re_trace (hX.isHermitian.sub hY.isHermitian)
  have hinv : |x⁻¹ - y⁻¹| * y = |x - y| / x := by
    have hid : x⁻¹ - y⁻¹ = (y - x) / (x * y) := by field_simp [hx'.ne', hy'.ne']
    rw [hid, abs_div, abs_sub_comm y x, abs_of_pos (mul_pos hx' hy')]
    field_simp [hx'.ne', hy'.ne']
  rw [heq]
  calc
    _ ≤ traceNorm (((x⁻¹ : ℝ) : ℂ) • (X - Y)) +
        traceNorm (((x⁻¹ - y⁻¹ : ℝ) : ℂ) • Y) := traceNorm_triangle _ _
    _ = x⁻¹ * traceNorm (X - Y) + |x - y| / x := by
      rw [traceNorm_real_smul, traceNorm_real_smul, abs_of_nonneg (inv_nonneg.mpr hx'.le),
        traceNorm_posSemidef hY]
      change _ + |x⁻¹ - y⁻¹| * y = _
      rw [hinv]
    _ ≤ _ := by
      calc
        _ ≤ x⁻¹ * traceNorm (X - Y) + traceNorm (X - Y) / x :=
          add_le_add le_rfl (div_le_div_of_nonneg_right hmass hx'.le)
        _ = _ := by change _ = 2 / x * traceNorm (X - Y); ring

/-- The branch bound includes the absolute change in the conditional prior.
The normalization estimate uses the nominal weight. -/
theorem traceNorm_conditioned_prior_sub_le {X Y : Matrix ι ι ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (hx : 0 < X.trace.re) (hy : 0 < Y.trace.re) (p p' : ℝ) (hp : 0 ≤ p) :
    traceNorm ((p : ℂ) • traceNormalized X - (p' : ℂ) • traceNormalized Y) ≤
      p * (2 / X.trace.re * traceNorm (X - Y)) + |p - p'| := by
  have hY1 : traceNorm (traceNormalized Y) = 1 := by
    rw [traceNorm_posSemidef (traceNormalized_posSemidef hY), trace_traceNormalized_re hy]
  have he : (p : ℂ) • traceNormalized X - (p' : ℂ) • traceNormalized Y =
      (p : ℂ) • (traceNormalized X - traceNormalized Y) +
        ((p - p' : ℝ) : ℂ) • traceNormalized Y := by
    push_cast
    rw [smul_sub, sub_smul]
    abel
  rw [he]
  refine (traceNorm_triangle _ _).trans ?_
  rw [traceNorm_real_smul, traceNorm_real_smul, abs_of_nonneg hp, hY1, mul_one]
  exact add_le_add (mul_le_mul_of_nonneg_left
    (traceNorm_traceNormalized_sub_le hX hY hx hy) hp) le_rfl

end SKEFTHawking.QuantumNetwork

namespace SKEFTHawking.QuantumNetwork.OneRecordCoherentSchedule

open SKEFTHawking.QuantumNetwork

/-- Error in the two raw selected branches and in the posterior prior
preserves a joint advantage when the amplified error is below the margin. -/
theorem selected_joint_beats_memory_under_raw_branch_error (a b c d p p' : ℝ)
    (train : a^2 + b^2 = 1) (offset : c^2 + d^2 = 1) (hd : d ≠ 0)
    (hp : 0 ≤ p) (hp1 : p < 1) (hd1 : d^2 < 1)
    (hJ : (1 - p) * (d^2 / 2) < p)
    (hp' : 0 ≤ p') (hp'1 : p' ≤ 1)
    (C' D' : Matrix (Fin 4) (Fin 4) ℂ)
    (hC' : C'.PosSemidef) (hD' : D'.PosSemidef)
    (hmC' : 0 < C'.trace.re) (hmD' : 0 < D'.trace.re) :
    let q := 1 - p
    let q' := 1 - p'
    let C := coherentSelected a b c d
    let D := dephasedSelected a b c d
    let P' := (p' : ℂ) • traceNormalized C'
    let Q' := (q' : ℂ) • traceNormalized D'
    let margin := q * (1 - d^2) * (p - q * (d^2 / 2)) / (2 * (p + q * (1 - d^2)))
    p * (2 / (d^2 / 2) * traceNorm (C - C')) +
      q * (2 / (1 / 2) * traceNorm (D - D')) + 2 * |p - p'| < margin →
    ∃ E : Matrix (Fin 4) (Fin 4) ℂ, E.PosSemidef ∧ (1 - E).PosSemidef ∧
      ∀ F : Matrix (Fin 2) (Fin 2) ℂ, F.PosSemidef → (1 - F).PosSemidef →
        (memoryMarginal P' * F).trace.re + (memoryMarginal Q' * (1 - F)).trace.re <
          (P' * E).trace.re + (Q' * (1 - E)).trace.re := by
  intro q q' C D P' Q' margin hbudget
  have hq : 0 ≤ q := sub_nonneg.mpr hp1.le
  have hq' : 0 ≤ q' := sub_nonneg.mpr hp'1
  have hP' : P'.PosSemidef := (traceNormalized_posSemidef hC').smul (Complex.zero_le_real.mpr hp')
  have hQ' : Q'.PosSemidef := (traceNormalized_posSemidef hD').smul (Complex.zero_le_real.mpr hq')
  have hs' : P'.trace.re + Q'.trace.re = 1 := by
    dsimp only [P', Q']
    rw [Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul,
      Complex.re_ofReal_mul, Complex.re_ofReal_mul, trace_traceNormalized_re hmC',
      trace_traceNormalized_re hmD', mul_one, mul_one]
    dsimp only [q']
    ring
  obtain ⟨hC, hD, hmCpos, hmC, _, hmD, _⟩ := selected_density_contrast a b c d train offset hd
  change C.trace.re = d^2 / 2 at hmC
  change D.trace.re = 1 / 2 at hmD
  have hmDpos : 0 < D.trace.re := by rw [hmD]; norm_num
  have hP := traceNorm_conditioned_prior_sub_le hC hC' hmCpos hmC' p p' hp
  have hQ := traceNorm_conditioned_prior_sub_le hD hD' hmDpos hmD' q q' hq
  change traceNorm ((p : ℂ) • traceNormalized C - P') ≤
    p * (2 / C.trace.re * traceNorm (C - C')) + |p - p'| at hP
  change traceNorm ((q : ℂ) • traceNormalized D - Q') ≤
    q * (2 / D.trace.re * traceNorm (D - D')) + |q - q'| at hQ
  have hprior : |q - q'| = |p - p'| := by
    rw [show q - q' = -(p - p') by dsimp only [q, q']; ring, abs_neg]
  rw [traceNormalized, smul_smul, ← Complex.ofReal_mul, hmC, ← div_eq_mul_inv] at hP
  rw [traceNormalized, smul_smul, ← Complex.ofReal_mul, hmD, hprior] at hQ
  rw [show (1 / 2 : ℝ)⁻¹ = 2 by norm_num, mul_comm q 2] at hQ
  apply selected_joint_beats_memory_under_traceNorm_error a b c d p train offset hd hp hp1 hd1 hJ
    P' Q' hP' hQ' hs'
  change traceNorm (((p / (d^2 / 2) : ℝ) : ℂ) • C - P') +
    traceNorm (((2 * q : ℝ) : ℂ) • D - Q') < margin
  apply (add_le_add hP hQ).trans_lt
  linarith only [hbudget]

end SKEFTHawking.QuantumNetwork.OneRecordCoherentSchedule
