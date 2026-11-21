import SKEFTHawking.QuantumNetwork.OneRecordCoherentPrior
import SKEFTHawking.QuantumNetwork.DiamondNorm

/-!
# Memory-only discrimination in the one-record timing circuit

The fixed memory-X instrument and an arbitrary memory-only binary effect
can have different success probabilities after timing selection.
-/

open Matrix
open scoped ComplexOrder

namespace SKEFTHawking.QuantumNetwork.OneRecordCoherentSchedule

/-- The system-major entry formula agrees with the library partial trace,
with memory as the retained factor. -/
theorem memoryMarginal_eq_partialTrace (ρ : Matrix (Fin 4) (Fin 4) ℂ) :
    memoryMarginal ρ =
      partialTrace (Matrix.of fun (i j : Fin 2 × Fin 2) =>
        ρ (finProdFinEquiv (i.2, i.1)) (finProdFinEquiv (j.2, j.1))) := by
  ext i j
  rfl

private theorem memoryMarginal_smul (z : ℂ) (ρ : Matrix (Fin 4) (Fin 4) ℂ) :
    memoryMarginal (z • ρ) = z • memoryMarginal ρ := by
  ext i j
  simp [memoryMarginal, Matrix.smul_apply, mul_add]

/-- The projection onto the unit vector (3,-4)/5 supplies the explicit
memory-only score for equal priors after selection. -/
private theorem selected_memory_effect_score (c d : ℝ)
    (hc : c^2 = 1 / 2) (hd : d^2 = 1 / 2) :
    let P := memoryMarginal (coherentPriorState 1 0 c d)
    let Q := memoryMarginal (dephasedSelected 1 0 c d)
    ∃ E : Matrix (Fin 2) (Fin 2) ℂ, E.PosSemidef ∧ (1 - E).PosSemidef ∧
      (P * E).trace.re + (Q * (1 - E)).trace.re = 31 / 40 := by
  intro P Q
  let v : Fin 2 → ℂ := ![3, -4]
  let w : Fin 2 → ℂ := ![4, 3]
  let E := ((1 / 25 : ℝ) : ℂ) • vecMulVec v (star v)
  let F := ((1 / 25 : ℝ) : ℂ) • vecMulVec w (star w)
  have hE : E.PosSemidef :=
    (posSemidef_vecMulVec_self_star v).smul (Complex.zero_le_real.mpr (by norm_num))
  have hF : F.PosSemidef :=
    (posSemidef_vecMulVec_self_star w).smul (Complex.zero_le_real.mpr (by norm_num))
  have complement : (1 : Matrix (Fin 2) (Fin 2) ℂ) - E = F := by
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      norm_num [E, F, v, w, Matrix.vecMulVec_apply, Matrix.smul_apply,
        Matrix.one_apply, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
        Complex.div_ofNat_re, Complex.div_ofNat_im]
  obtain ⟨hC, hD⟩ := selected_memory_marginals 1 0 c d (by norm_num) (by rw [hc, hd]; norm_num)
  have hP : P = (1 / 4 : ℂ) • (!![1, -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℂ) := by
    dsimp only [P, coherentPriorState]
    rw [memoryMarginal_smul, hC, hd, smul_smul, ← Complex.ofReal_mul]
    norm_num
  have hQ : Q = Matrix.diagonal ![(3 / 8 : ℂ), (1 / 8 : ℂ)] := by
    dsimp only [Q]
    rw [hD]
    norm_num [hc, hd]
  refine ⟨E, hE, complement.symm ▸ hF, ?_⟩
  rw [hP, hQ, complement]
  norm_num [E, F, v, w, Matrix.trace, Matrix.mul_apply, Matrix.diag,
    Matrix.vecMulVec_apply, Matrix.smul_apply, Fin.sum_univ_two,
    Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.div_ofNat_re, Complex.div_ofNat_im]

/-- For the half-offset circuit and equal priors after selection, a memory
effect scores 31/40 and beats every decision rule applied to memory X. -/
theorem selected_memory_effect_beats_X (c d : ℝ)
    (hc : c^2 = 1 / 2) (hd : d^2 = 1 / 2) :
    let P := coherentPriorState 1 0 c d
    let Q := dephasedSelected 1 0 c d
    let XP := fun r => memoryXReadout.branch r P
    let XQ := fun r => memoryXReadout.branch r Q
    ∃ E : Matrix (Fin 2) (Fin 2) ℂ, E.PosSemidef ∧ (1 - E).PosSemidef ∧
      ((memoryMarginal P * E).trace.re + (memoryMarginal Q * (1 - E)).trace.re = 31 / 40) ∧
      (∀ rule : Fin 2 → Bool, finite_binary_record_success XP XQ rule < 31 / 40) := by
  intro P Q XP XQ
  obtain ⟨E, hE, hEF, hScore⟩ := selected_memory_effect_score c d hc hd
  refine ⟨E, hE, hEF, hScore, ?_⟩
  have hdn : d ≠ 0 := by
    intro h
    norm_num [h] at hd
  obtain ⟨_, hMax, _⟩ :=
    one_record_memoryX_optimal_with_prior 1 0 c d (1/2)
      (by norm_num) (by rw [hc, hd]; norm_num) hdn (by norm_num) (by norm_num)
  intro rule
  have hr := hMax rule
  have hfactor : (1 / 2 : ℝ) / (d^2 / 2) = (d^2)⁻¹ := by rw [hd]; norm_num
  have hother : (2 * (1 - 1 / 2) : ℝ) = 1 := by norm_num
  simp only [hfactor, hother, Complex.ofReal_one, one_smul] at hr
  apply lt_of_le_of_lt hr
  norm_num

/-- Exact optimum for a minus-state hypothesis with prior `p` against a
diagonal memory state with population `u` in the first basis vector. -/
theorem minus_vs_diagonal_memory_optimum (p u : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    let q := 1 - p
    let P := ((p / 2 : ℝ) : ℂ) • (!![1, -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℂ)
    let Q := Matrix.diagonal ![((q * u : ℝ) : ℂ), ((q * (1 - u) : ℝ) : ℂ)]
    let score := fun E : Matrix (Fin 2) (Fin 2) ℂ =>
      (P * E).trace.re + (Q * (1 - E)).trace.re
    IsGreatest {x | ∃ E, E.PosSemidef ∧ (1 - E).PosSemidef ∧ score E = x}
      (q + max 0 ((p - q + Real.sqrt (p^2 + (q * (1 - 2 * u))^2)) / 2)) := by
  intro q P Q score
  let delta := q * (1 - 2 * u)
  let s := Real.sqrt (p^2 + delta^2)
  let upper := (p - q + s) / 2
  let lower := (p - q - s) / 2
  change IsGreatest _ (q + max 0 upper)
  have hq : 0 ≤ q := sub_nonneg.mpr hp1
  have hTraceQ : Q.trace.re = q := by
    simp [Q, Matrix.trace, Matrix.diag, Fin.sum_univ_two,
      Complex.add_re, Complex.mul_re, Complex.sub_re]
    ring
  by_cases hp : p = 0
  · have hpz : P = 0 := by simp [P, hp]
    have hq1 : q = 1 := by simp [q, hp]
    have hs : s ≤ 1 := by
      have hi : |1 - 2 * u| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      simpa [s, delta, q, hp, Real.sqrt_sq_eq_abs] using hi
    have huv : upper ≤ 0 := by
      dsimp only [upper]
      rw [hp, hq1]
      linarith
    have hQ : Q.PosSemidef := by
      apply Matrix.PosSemidef.diagonal
      intro i
      fin_cases i
      · exact Complex.zero_le_real.mpr (mul_nonneg hq hu0)
      · exact Complex.zero_le_real.mpr (mul_nonneg hq (sub_nonneg.mpr hu1))
    rw [max_eq_left huv, add_zero]
    refine ⟨⟨0, Matrix.PosSemidef.zero, by simpa using Matrix.PosSemidef.one, ?_⟩, ?_⟩
    · simp [score, hTraceQ]
    · rintro x ⟨E,hE,hEF,rfl⟩
      have h := re_trace_mul_le_of_one_sub_posSemidef hQ
        (show (1 - (1 - E)).PosSemidef by rwa [sub_sub_cancel])
      simpa [score, hpz, hTraceQ] using h
  · have hpPos : 0 < p := lt_of_le_of_ne hp0 (fun he => hp he.symm)
    have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
    have hs2 : s^2 = p^2 + delta^2 := Real.sq_sqrt (by positivity)
    have hpS : p ≤ s := Real.le_sqrt_of_sq_le (by linarith [sq_nonneg delta])
    have hLower : lower ≤ 0 := by dsimp [lower]; linarith only [hpS, hq]
    let H : Matrix (Fin 2) (Fin 2) ℂ :=
      !![(((1 + delta / s) / 2 : ℝ) : ℂ), ((-p / (2 * s) : ℝ) : ℂ);
         ((-p / (2 * s) : ℝ) : ℂ), (((1 - delta / s) / 2 : ℝ) : ℂ)]
    have hHer : H.IsHermitian := by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [H, Matrix.conjTranspose_apply]
    have hIdem : H * H = H := by
      ext i j
      fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
        simp [H, Matrix.mul_apply, Fin.sum_univ_two, Complex.div_ofNat_re, Complex.div_ofNat_im,
          Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
          Complex.sub_im, Complex.div_re, Complex.div_im]
      all_goals field_simp [hs.ne']
      all_goals nlinarith only [hs2]
    have hH : H.PosSemidef := by
      have he : Hᴴ * H = H := by rw [hHer.eq, hIdem]
      exact he ▸ posSemidef_conjTranspose_mul_self H
    have hComp := one_sub_posSemidef_of_projection hHer hIdem
    have hTraceH : H.trace.re = 1 := by
      simp [H, Matrix.trace, Matrix.diag, Fin.sum_univ_two, Complex.add_re,
        Complex.div_ofNat_re, Complex.sub_re, Complex.div_re]
      ring
    have hShift : P - Q = (upper : ℂ) • H + (lower : ℂ) • (1 - H) := by
      ext i j
      fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
        simp [P, Q, H, upper, lower, Matrix.smul_apply, Complex.ofReal_div,
          Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.mul_re, Complex.mul_im,
          Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.div_re, Complex.div_im]
      all_goals field_simp [hs.ne']
      all_goals try dsimp only [delta]
      all_goals ring
    have hScore (E : Matrix (Fin 2) (Fin 2) ℂ) :
        score E = q + upper * (H * E).trace.re + lower * ((1 - H) * E).trace.re := by
      dsimp only [score]
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, Complex.sub_re, hTraceQ]
      have hh := congrArg (fun D => (D * E).trace.re) hShift
      simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_add,
        Matrix.trace_sub, Complex.add_re, Complex.sub_re, Matrix.trace_smul,
        smul_eq_mul, Complex.re_ofReal_mul] at hh
      simp only [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
      linarith only [hh]
    by_cases hv : 0 ≤ upper
    · rw [max_eq_right hv]
      have hZero : (1 - H) * H = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hIdem, sub_self]
      refine ⟨⟨H,hH,hComp,?_⟩,?_⟩
      · rw [hScore, hIdem, hZero, hTraceH, Matrix.trace_zero, Complex.zero_re, mul_one, mul_zero, add_zero]
      · rintro x ⟨E,hE,hEF,rfl⟩
        have hu := (re_trace_mul_le_of_one_sub_posSemidef hH hEF).trans_eq hTraceH
        have hl := (Complex.le_def.mp (trace_mul_nonneg hComp hE)).1
        rw [hScore]
        linarith only [mul_le_mul_of_nonneg_left hu hv,
          mul_nonpos_of_nonpos_of_nonneg hLower (show 0 ≤ ((1 - H) * E).trace.re by simpa using hl)]
    · rw [max_eq_left (le_of_not_ge hv), add_zero]
      refine ⟨⟨0, Matrix.PosSemidef.zero, by simpa using Matrix.PosSemidef.one, ?_⟩, ?_⟩
      · simp [hScore]
      · rintro x ⟨E,hE,_,rfl⟩
        have hu := (Complex.le_def.mp (trace_mul_nonneg hH hE)).1
        have hl := (Complex.le_def.mp (trace_mul_nonneg hComp hE)).1
        rw [hScore]
        linarith only [
          mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hv) (show 0 ≤ (H * E).trace.re by simpa using hu),
          mul_nonpos_of_nonpos_of_nonneg hLower (show 0 ≤ ((1 - H) * E).trace.re by simpa using hl)]


/-- Exact optimal memory-only decision for the actual circuit and an
arbitrary prior assigned after timing selection. -/
theorem selected_memory_effect_optimum_with_prior (a b c d p : ℝ)
    (train : a^2 + b^2 = 1) (offset : c^2 + d^2 = 1) (hd : d ≠ 0)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    let q := 1 - p
    let u := ((a * c - b * d)^2 + a^2) / 2
    let P := memoryMarginal (((p / (d^2 / 2) : ℝ) : ℂ) • coherentSelected a b c d)
    let Q := memoryMarginal (((2 * q : ℝ) : ℂ) • dephasedSelected a b c d)
    let score := fun E : Matrix (Fin 2) (Fin 2) ℂ =>
      (P * E).trace.re + (Q * (1 - E)).trace.re
    IsGreatest {x | ∃ E, E.PosSemidef ∧ (1 - E).PosSemidef ∧ score E = x}
      (q + max 0 ((p - q + Real.sqrt (p^2 + (q * (1 - 2 * u))^2)) / 2)) := by
  intro q u P Q score
  obtain ⟨hC,hD⟩ := selected_memory_marginals a b c d train offset
  have hsum : (a * c - b * d)^2 + (a * d + b * c)^2 = 1 := by
    calc
      _ = (a^2 + b^2) * (c^2 + d^2) := by ring
      _ = 1 := by simp [train,offset]
  have hv : ((a * d + b * c)^2 + b^2) / 2 = 1 - u := by
    dsimp only [u]
    linarith only [hsum,train]
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := sub_nonneg.mp (hv ▸ (by positivity :
    0 ≤ ((a * d + b * c)^2 + b^2) / 2))
  have hU : ((a * c - b * d)^2 + a^2) / 4 = u / 2 := by dsimp [u]; ring
  have hV : ((a * d + b * c)^2 + b^2) / 4 = (1 - u) / 2 := by linarith only [hv]
  have hP : P = ((p / 2 : ℝ) : ℂ) • (!![1, -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℂ) := by
    dsimp only [P]
    rw [memoryMarginal_smul, hC, smul_smul, ← Complex.ofReal_mul]
    have h : p / (d^2 / 2) * (d^2 / 4) = p / 2 := by
      field_simp [pow_ne_zero _ hd]
      ring
    rw [h]
  have hQ : Q = Matrix.diagonal ![((q * u : ℝ) : ℂ), ((q * (1 - u) : ℝ) : ℂ)] := by
    dsimp only [Q]
    rw [memoryMarginal_smul, hD, hU, hV]
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      norm_num [Matrix.smul_apply, Complex.mul_re, Complex.mul_im, Complex.div_ofNat_re,
        Complex.div_ofNat_im, Complex.sub_re, Complex.sub_im]
    all_goals ring
  dsimp only [score]
  rw [hP,hQ]
  exact minus_vs_diagonal_memory_optimum p u hp0 hp1 hu0 hu1


/-- In the half-offset circuit with equal priors after selection, the optimum
over all binary effects on memory is `1/2 + sqrt(5)/8`. -/
theorem selected_memory_effect_optimum (c d : ℝ)
    (hc : c^2 = 1 / 2) (hd : d^2 = 1 / 2) :
    let P := memoryMarginal (coherentPriorState 1 0 c d)
    let Q := memoryMarginal (dephasedSelected 1 0 c d)
    let score := fun E : Matrix (Fin 2) (Fin 2) ℂ =>
      (P * E).trace.re + (Q * (1 - E)).trace.re
    IsGreatest {x | ∃ E, E.PosSemidef ∧ (1 - E).PosSemidef ∧ score E = x}
      (1 / 2 + Real.sqrt 5 / 8) := by
  have hdn : d ≠ 0 := by
    intro h
    norm_num [h] at hd
  have h := selected_memory_effect_optimum_with_prior 1 0 c d (1 / 2)
    (by norm_num) (by rw [hc,hd]; norm_num) hdn (by norm_num) (by norm_num)
  dsimp only at h
  have hScale : (1 / 2 : ℝ) / (d^2 / 2) = (d^2)⁻¹ := by rw [hd]; norm_num
  have hQ : (2 * (1 - 1 / 2) : ℝ) = 1 := by norm_num
  have hU : (((1 : ℝ) * c - (0 : ℝ) * d)^2 + (1 : ℝ)^2) / 2 = 3 / 4 := by
    norm_num [hc]
  have hScore :
      (1 - 1 / 2 : ℝ) + max 0
          ((1 / 2 - (1 - 1 / 2) + Real.sqrt ((1 / 2)^2 + ((1 - 1 / 2) * (1 - 2 * (3 / 4)))^2)) / 2) =
        1 / 2 + Real.sqrt 5 / 8 := by
    have hRadicand : ((1 / 2 : ℝ)^2 + ((1 - 1 / 2) * (1 - 2 * (3 / 4)))^2) =
        (1 / 16 : ℝ) * 5 := by norm_num
    rw [hRadicand, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1 / 16)]
    rw [show Real.sqrt ((1 : ℝ) / 16) = 1 / 4 by
      exact (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)]
    simp only [show (1 / 2 - (1 - 1 / 2) : ℝ) = 0 by norm_num, zero_add,
      max_eq_right (by positivity : 0 ≤ (1 / 4 : ℝ) * Real.sqrt 5 / 2)]
    ring
  rw [hU, hScore] at h
  simpa only [coherentPriorState, hScale, hQ, Complex.ofReal_one, one_smul] using h

end SKEFTHawking.QuantumNetwork.OneRecordCoherentSchedule
