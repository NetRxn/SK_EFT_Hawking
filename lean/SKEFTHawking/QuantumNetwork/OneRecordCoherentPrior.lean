import SKEFTHawking.QuantumNetwork.OneRecordCoherentDecision

/-!
# Conditional decisions for coherent timing with arbitrary priors

The selected coherent and dephased selection masses are `d²/2` and `1/2`, respectively.
The formulas below account for this mass before comparing the record,
the measured memory X sign, and an unrestricted joint effect.
-/

open Matrix
open scoped ComplexOrder

namespace SKEFTHawking.QuantumNetwork.OneRecordCoherentSchedule

/-- Exact optimal decision for an arbitrary conditional prior on the coherent
hypothesis. The dephased hypothesis uses the complementary prior. -/
theorem one_record_conditional_optimum_with_prior (a b c d prior : ℝ)
    (train : a^2 + b^2 = 1) (offset : c^2 + d^2 = 1) (hd : d ≠ 0)
    (hlo : 0 ≤ prior) (hhi : prior ≤ 1) :
    let mass := d^2 / 2
    let other := 1 - prior
    let P (_ : Unit) := ((prior / mass : ℝ) : ℂ) • coherentSelected a b c d
    let Q (_ : Unit) := ((2 * other : ℝ) : ℂ) • dephasedSelected a b c d
    (∀ r, (P r).PosSemidef ∧ (Q r).PosSemidef) ∧
    (∀ r, (P r).trace.re = prior ∧ (Q r).trace.re = other) ∧
    (∀ F : Unit → Matrix (Fin 4) (Fin 4) ℂ, (∀ r, (F r).PosSemidef) →
      (∀ r, (1-F r).PosSemidef) →
      finite_binary_success P Q F ≤ other + max 0 (prior - other * mass)) ∧
    (∃ F : Unit → Matrix (Fin 4) (Fin 4) ℂ, (∀ r, (F r).PosSemidef) ∧
      (∀ r, (1-F r).PosSemidef) ∧
      finite_binary_success P Q F = other + max 0 (prior - other * mass)) := by
  intro mass other P Q
  let C := coherentSelected a b c d
  let D := dephasedSelected a b c d
  let A := symmetricSelected a b c d
  let E (_ : Unit) := antisymmetricEffect a b c d
  let scale := prior / mass-other
  have hm : 0 < mass := div_pos (sq_pos_of_ne_zero hd) (by norm_num)
  have ho : 0 ≤ other := sub_nonneg.mpr hhi
  obtain ⟨hC,_,_,htC,_,htD,_⟩ := selected_density_contrast a b c d train offset hd
  obtain ⟨hA,hAC,hsplit⟩ := dephasedSelected_split a b c d
  change C.PosSemidef at hC
  change A.PosSemidef at hA
  change C.trace.re = mass at htC
  change D.trace.re = 1/2 at htD
  change A * C = 0 at hAC
  change D = (1/2 : ℂ) • (C+A) at hsplit
  obtain ⟨_,_,hE,_,_,_⟩ := one_record_conditional_binary_optimum a b c d train offset hd
  have hQ (r : Unit) : Q r = (other : ℂ) • (C+A) := by
    change (((2 * other : ℝ) : ℂ) • D) = _
    rw [hsplit, smul_smul]
    have h : ((2 * other : ℝ) : ℂ) * (1/2 : ℂ) = (other : ℂ) := by push_cast; ring
    rw [h]
  have hQt (r : Unit) : (Q r).trace.re = other := by
    change (((2 * other : ℝ) : ℂ) • D).trace.re = _
    rw [Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul, htD]
    ring
  have score (F : Unit → Matrix (Fin 4) (Fin 4) ℂ) :
      finite_binary_success P Q F = other + scale*(C*F ()).trace.re - other*(A*F ()).trace.re := by
    rw [finite_binary_success, Fintype.sum_unique, Fintype.sum_unique, Matrix.mul_sub,
      Matrix.mul_one, Matrix.trace_sub, Complex.sub_re, hQt (), hQ ()]
    change ((((prior / mass : ℝ) : ℂ) • C) * F ()).trace.re +
      (other - (((other : ℂ) • (C+A)) * F ()).trace.re) = _
    simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul,
      Matrix.add_mul, Matrix.trace_add, Complex.add_re]
    dsimp [scale]
    ring
  have hscale : scale * mass = prior-other * mass := by
    dsimp [scale]
    rw [sub_mul, div_mul_cancel₀ _ hm.ne']
  have hCE : C*E () = C := by
    change C * (((mass⁻¹ : ℝ) : ℂ) • C) = C
    rw [Matrix.mul_smul, coherentSelected_sq a b c d train offset hd, smul_smul]
    change (((mass⁻¹ : ℝ) : ℂ) * (mass : ℂ)) • C = C
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ hm.ne', Complex.ofReal_one, one_smul]
  have hAE : A*E () = 0 := by
    change A * (((mass⁻¹ : ℝ) : ℂ) • C) = 0
    rw [Matrix.mul_smul, hAC, smul_zero]
  have hP (r : Unit) : (P r).PosSemidef :=
    hC.smul (Complex.zero_le_real.mpr (div_nonneg hlo hm.le))
  have hQpos (r : Unit) : (Q r).PosSemidef := by
    rw [hQ r]
    exact (hC.add hA).smul (Complex.zero_le_real.mpr ho)
  have hPt (r : Unit) : (P r).trace.re = prior := by
    change (((prior / mass : ℝ) : ℂ) • C).trace.re = _
    rw [Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul, htC, div_mul_cancel₀ _ hm.ne']
  refine ⟨fun r => ⟨hP r,hQpos r⟩, fun r => ⟨hPt r,hQt r⟩, ?_⟩
  by_cases hsign : 0 ≤ scale
  · have hv : 0 ≤ prior-other * mass := hscale ▸ mul_nonneg hsign hm.le
    rw [max_eq_right hv]
    constructor
    · intro F hF hI
      have hCf := re_trace_mul_le_of_one_sub_posSemidef hC (hI ())
      rw [htC] at hCf
      have hAf := (Complex.le_def.mp (trace_mul_nonneg hA (hF ()))).1
      rw [score, ← hscale]
      linarith [mul_le_mul_of_nonneg_left hCf hsign,
        mul_nonneg ho (show 0 ≤ (A*F ()).trace.re by simpa using hAf)]
    · refine ⟨E, fun r => (hE r).1, fun r => (hE r).2, ?_⟩
      rw [score, hCE, hAE, htC, Matrix.trace_zero, Complex.zero_re, mul_zero, sub_zero, hscale]
  · have hneg : scale ≤ 0 := le_of_not_ge hsign
    have hv : prior-other * mass ≤ 0 := hscale ▸ mul_nonpos_of_nonpos_of_nonneg hneg hm.le
    rw [max_eq_left hv, add_zero]
    constructor
    · intro F hF _
      have hCf : 0 ≤ (C*F ()).trace.re := (Complex.le_def.mp (trace_mul_nonneg hC (hF ()))).1
      have hAf : 0 ≤ (A*F ()).trace.re := (Complex.le_def.mp (trace_mul_nonneg hA (hF ()))).1
      rw [score]
      linarith [mul_nonpos_of_nonpos_of_nonneg hneg hCf, mul_nonneg ho hAf]
    · refine ⟨fun _ => 0, fun _ => Matrix.PosSemidef.zero, fun _ => by simpa using
          (Matrix.PosSemidef.one : (1 : Matrix (Fin 4) (Fin 4) ℂ).PosSemidef), ?_⟩
      rw [score]
      simp

private theorem memoryX_weight_real_smul (label : Fin 2) (scale : ℝ) (ρ : Matrix (Fin 4) (Fin 4) ℂ) :
    memoryXReadout.weight label ((scale : ℂ) • ρ) = scale * memoryXReadout.weight label ρ := by
  simp only [FiniteInstrument.weight, FiniteInstrument.branch_smul, Matrix.trace_smul,
    smul_eq_mul, Complex.re_ofReal_mul]

/-- With an arbitrary conditional prior, an optimal rule on the measured
memory-X sign reaches the sum of the maxima for the two signs. -/
theorem one_record_memoryX_optimal_with_prior (a b c d prior : ℝ)
    (train : a^2 + b^2 = 1) (offset : c^2 + d^2 = 1) (hd : d ≠ 0)
    (hlo : 0 ≤ prior) (hhi : prior ≤ 1) :
    let mass := d^2 / 2
    let other := 1 - prior
    let P (label : Fin 2) := memoryXReadout.branch label
      (((prior / mass : ℝ) : ℂ) • coherentSelected a b c d)
    let Q (label : Fin 2) := memoryXReadout.branch label
      (((2 * other : ℝ) : ℂ) • dephasedSelected a b c d)
    (∀ label, (P label).PosSemidef ∧ (Q label).PosSemidef) ∧
    (∀ rule : Fin 2 → Bool, finite_binary_record_success P Q rule ≤ other / 2 + max prior (other / 2)) ∧
    (∃ rule : Fin 2 → Bool, finite_binary_record_success P Q rule = other / 2 + max prior (other / 2)) := by
  intro mass other P Q
  obtain ⟨hzero,hfull,hqzero,hqone⟩ := one_record_readout_weights a b c d train offset hd
  have hm : mass ≠ 0 := (div_pos (sq_pos_of_ne_zero hd) (by norm_num)).ne'
  have ho : 0 ≤ other / 2 := div_nonneg (sub_nonneg.mpr hhi) (by norm_num)
  have hp0 : (P 0).trace.re = 0 := by
    change memoryXReadout.weight 0 (((prior / mass : ℝ) : ℂ) • _) = _
    rw [memoryX_weight_real_smul,hzero,mul_zero]
  have hp1 : (P 1).trace.re = prior := by
    change memoryXReadout.weight 1 (((prior / mass : ℝ) : ℂ) • _) = _
    rw [memoryX_weight_real_smul,hfull]
    change prior / mass * mass = _
    exact div_mul_cancel₀ _ hm
  have hq0 : (Q 0).trace.re = other / 2 := by
    change memoryXReadout.weight 0 (((2 * other : ℝ) : ℂ) • _) = _
    rw [memoryX_weight_real_smul,hqzero]
    ring
  have hq1 : (Q 1).trace.re = other / 2 := by
    change memoryXReadout.weight 1 (((2 * other : ℝ) : ℂ) • _) = _
    rw [memoryX_weight_real_smul,hqone]
    ring
  have total : (∑ r, (P r).trace.re) + ∑ r, (Q r).trace.re = 1 := by
    rw [Fin.sum_univ_two,Fin.sum_univ_two,hp0,hp1,hq0,hq1]
    dsimp only [other]
    ring
  have value : (1 + ∑ r, |(P r).trace.re - (Q r).trace.re|)/2 = other / 2 + max prior (other / 2) := by
    rw [Fin.sum_univ_two,hp0,hp1,hq0,hq1,zero_sub,abs_neg,abs_of_nonneg ho]
    rcases le_total prior (other / 2) with h | h
    · rw [max_eq_right h,abs_of_nonpos (sub_nonpos.mpr h)]
      dsimp only [other]
      ring
    · rw [max_eq_left h,abs_of_nonneg (sub_nonneg.mpr h)]
      dsimp only [other]
      ring
  obtain ⟨hC,hD,_,_,_,_,_⟩ := selected_density_contrast a b c d train offset hd
  have hPm : 0 ≤ prior / mass := div_nonneg hlo (le_of_lt (div_pos (sq_pos_of_ne_zero hd) (by norm_num)))
  have hQm : 0 ≤ 2 * other := mul_nonneg (by norm_num) (sub_nonneg.mpr hhi)
  refine ⟨fun label => ⟨memoryXReadout.branch_posSemidef label
    (hC.smul (Complex.zero_le_real.mpr hPm)),
    memoryXReadout.branch_posSemidef label (hD.smul (Complex.zero_le_real.mpr hQm))⟩, ?_⟩
  rw [← value]
  exact finite_binary_record_success_optimal P Q total

/-- Equal priors before selection give a posterior proportional to selection
mass. The record, memory-X and joint optima then have explicit scores. -/
private theorem one_record_equal_preselection_scores (d : ℝ) (hd : d ≠ 0) (hd1 : d^2 ≤ 1) :
    let p := d^2 / (1 + d^2)
    let q := 1 / (1 + d^2)
    (d^2 / 2)/(d^2 / 2+1/2) = p ∧ p + q=1 ∧ max p q=q ∧
      q + max 0 (p - q*(d^2 / 2)) = 1-d^2/(2*(1 + d^2)) ∧
      q / 2 + max p (q / 2) = if d^2 ≤ 1/2 then q else 1-1/(2*(1 + d^2)) := by
  intro p q
  let s := d^2
  have hs : 0 < s := sq_pos_of_ne_zero hd
  have hden : 0 < 1 + s := by linarith
  have hp : p = s/(1 + s) := rfl
  have hq : q = 1/(1 + s) := rfl
  have hsum : p + q=1 := by rw [hp,hq]; field_simp [hden.ne']; ring
  have hqHalf : q / 2 = (1/2)/(1 + s) := by rw [hq]; ring
  have hgap : p - q*(s/2) = s/(2*(1 + s)) := by
    rw [hp,hq]
    field_simp [hden.ne']
    ring
  have hsmall : p ≤ q := by rw [hp,hq]; exact div_le_div_of_nonneg_right hd1 hden.le
  refine ⟨?_,hsum,max_eq_right hsmall,?_,?_⟩
  · change (s/2)/(s/2+1/2)=p
    rw [hp]
    field_simp [show s/2+1/2≠0 by linarith]
    ring
  · change q + max 0 (p - q*(s/2)) = 1-s/(2*(1 + s))
    rw [hgap,max_eq_right (div_nonneg hs.le (by positivity))]
    rw [hq]
    field_simp [hden.ne']
    ring
  · change q / 2+max p (q / 2) = if s≤1/2 then q else 1-1/(2*(1 + s))
    by_cases h : s≤1/2
    · have hc : p≤q / 2 := by rw [hp,hqHalf]; exact div_le_div_of_nonneg_right h hden.le
      rw [if_pos h,max_eq_right hc]
      ring
    · have hc : q / 2≤p := by rw [hp,hqHalf]; exact div_le_div_of_nonneg_right (le_of_not_ge h) hden.le
      rw [if_neg h,max_eq_left hc,hp,hq]
      field_simp [hden.ne']
      ring

/-- For equal priors before selection, normalize both actual selected branches
by their common total selection probability. The three scores are the maximal
success probabilities conditional on observing the selected timing record. -/
theorem one_record_equal_preselection_optima (a b c d : ℝ)
    (train : a^2 + b^2 = 1) (offset : c^2 + d^2 = 1) (hd : d ≠ 0) :
    let C := coherentSelected a b c d
    let D := dephasedSelected a b c d
    let selectedProbability := C.trace.re / 2 + D.trace.re / 2
    let P (_ : Unit) := (((1 / 2 : ℝ) / selectedProbability : ℝ) : ℂ) • C
    let Q (_ : Unit) := (((1 / 2 : ℝ) / selectedProbability : ℝ) : ℂ) • D
    let MP (r : Fin 2) := memoryXReadout.branch r (P ())
    let MQ (r : Fin 2) := memoryXReadout.branch r (Q ())
    0 < selectedProbability ∧
      IsGreatest (Set.range (finite_binary_record_success P Q)) (1 / (1 + d^2)) ∧
      IsGreatest (Set.range (finite_binary_record_success MP MQ))
        (if d^2 ≤ 1 / 2 then 1 / (1 + d^2) else 1 - 1 / (2 * (1 + d^2))) ∧
      IsGreatest
        {score | ∃ F : Unit → Matrix (Fin 4) (Fin 4) ℂ,
          (∀ r, (F r).PosSemidef) ∧ (∀ r, (1 - F r).PosSemidef) ∧
          finite_binary_success P Q F = score}
        (1 - d^2 / (2 * (1 + d^2))) := by
  intro C D selectedProbability P Q MP MQ
  let p := d^2 / (1 + d^2)
  let q := 1 / (1 + d^2)
  have hd1 : d^2 ≤ 1 := by nlinarith [sq_nonneg c]
  have hm : 0 < d^2 / 2 := div_pos (sq_pos_of_ne_zero hd) (by norm_num)
  have hden : 0 < 1 + d^2 := by positivity
  have hp0 : 0 ≤ p := div_nonneg (sq_nonneg d) hden.le
  have hp1 : p ≤ 1 := (div_le_one hden).2 (by linarith)
  obtain ⟨_, _, _, htc, _, htd, _⟩ := selected_density_contrast a b c d train offset hd
  change C.trace.re = d^2 / 2 at htc
  change D.trace.re = 1 / 2 at htd
  have hselected : selectedProbability = (1 + d^2) / 4 := by
    dsimp only [selectedProbability]
    rw [htc, htd]
    ring
  have hpos : 0 < selectedProbability := hselected ▸ div_pos hden (by norm_num)
  obtain ⟨_, hpq, hmax, hjval, hmval⟩ := one_record_equal_preselection_scores d hd hd1
  change p + q = 1 at hpq
  change max p q = q at hmax
  change q + max 0 (p - q * (d^2 / 2)) = _ at hjval
  change q / 2 + max p (q / 2) = _ at hmval
  have hq : 1 - p = q := by linarith
  have hPscale : (1 / 2 : ℝ) / selectedProbability = p / (d^2 / 2) := by
    rw [hselected]
    dsimp only [p]
    field_simp [hden.ne', hm.ne', pow_ne_zero 2 hd]
    ring
  have hQscale : (1 / 2 : ℝ) / selectedProbability = 2 * (1 - p) := by
    rw [hselected, hq]
    dsimp only [q]
    field_simp [hden.ne']
    ring
  have hP : P = fun _ => ((p / (d^2 / 2) : ℝ) : ℂ) • C := by
    funext r
    dsimp only [P]
    rw [hPscale]
  have hQ : Q = fun _ => ((2 * (1 - p) : ℝ) : ℂ) • D := by
    funext r
    dsimp only [Q]
    rw [hQscale]
  obtain ⟨_, htrace, hjupper, hjreach⟩ :=
    one_record_conditional_optimum_with_prior a b c d p train offset hd hp0 hp1
  obtain ⟨_, hmemupper, hmemreach⟩ :=
    one_record_memoryX_optimal_with_prior a b c d p train offset hd hp0 hp1
  have htraceP : (P ()).trace.re = p := hP ▸ (htrace ()).1
  have htraceQ : (Q ()).trace.re = q := by
    rw [hQ, ← hq]
    exact (htrace ()).2
  have hrec (rule : Unit → Bool) :
      finite_binary_record_success P Q rule = if rule () then p else q := by
    simp only [finite_binary_record_success, Fintype.sum_unique, htraceP, htraceQ]
  refine ⟨hpos, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact ⟨fun _ => false, by simp [hrec, q]⟩
  · rintro score ⟨rule, rfl⟩
    change finite_binary_record_success P Q rule ≤ q
    rw [hrec]
    split
    · simpa only [hmax] using le_max_left p q
    · exact le_rfl
  · obtain ⟨rule, hscore⟩ := hmemreach
    refine ⟨rule, ?_⟩
    dsimp only [MP, MQ]
    rw [hP, hQ, hscore, hq, hmval]
  · rintro score ⟨rule, rfl⟩
    dsimp only [MP, MQ]
    rw [hP, hQ, ← hmval, ← hq]
    exact hmemupper rule
  · obtain ⟨F, hF, hIF, hscore⟩ := hjreach
    refine ⟨F, hF, hIF, ?_⟩
    rw [hP, hQ, hscore, hq, hjval]
  · rintro score ⟨F, hF, hIF, rfl⟩
    rw [hP, hQ, ← hjval, ← hq]
    exact hjupper F hF hIF

/-- With equal priors before selection, the joint advantage over memory X
is largest when the squared sine coefficient is one half. -/
theorem one_record_equal_preselection_joint_memory_gap (d : ℝ)
    (hd : d ≠ 0) (hd1 : d^2 ≤ 1) :
    let joint := 1 - d^2 / (2 * (1 + d^2))
    let memory := if d^2 ≤ 1 / 2 then 1 / (1 + d^2) else 1 - 1 / (2 * (1 + d^2))
    joint - memory = min (d^2) (1 - d^2) / (2 * (1 + d^2)) ∧
      joint - memory ≤ 1 / 6 ∧
      (joint - memory = 1 / 6 ↔ d^2 = 1 / 2) ∧
      (joint = memory ↔ d^2 = 1) := by
  intro joint memory
  let s := d^2
  have hs : 0 < s := sq_pos_of_ne_zero hd
  have hden : 0 < 2 * (1 + s) := by positivity
  have hplus : 0 < 1 + s := by positivity
  have hgap : joint - memory = min s (1 - s) / (2 * (1 + s)) := by
    by_cases h : s ≤ 1 / 2
    · have hm : s ≤ 1 - s := by linarith
      dsimp only [joint, memory]
      change 1 - s / (2 * (1 + s)) -
        (if s ≤ 1 / 2 then 1 / (1 + s) else 1 - 1 / (2 * (1 + s))) = _
      rw [if_pos h, min_eq_left hm]
      field_simp [hplus.ne']
      ring
    · have hm : 1 - s ≤ s := by linarith
      dsimp only [joint, memory]
      change 1 - s / (2 * (1 + s)) -
        (if s ≤ 1 / 2 then 1 / (1 + s) else 1 - 1 / (2 * (1 + s))) = _
      rw [if_neg h, min_eq_right hm]
      ring
  refine ⟨hgap, ?_, ?_, ?_⟩
  · rw [hgap, div_le_iff₀ hden]
    rcases le_total s (1 / 2) with h | h
    · linarith [min_le_left s (1 - s)]
    · linarith [min_le_right s (1 - s)]
  · rw [hgap, div_eq_iff hden.ne']
    change min s (1 - s) = 1 / 6 * (2 * (1 + s)) ↔ s = 1 / 2
    constructor
    · intro h
      linarith [min_le_left s (1 - s), min_le_right s (1 - s)]
    · rintro h
      norm_num [h]
  · rw [← sub_eq_zero, hgap, div_eq_zero_iff]
    simp only [hden.ne', or_false]
    change min s (1 - s) = 0 ↔ s = 1
    constructor
    · intro hzero
      rcases le_total s (1 - s) with h | h
      · rw [min_eq_left h] at hzero
        linarith
      · rw [min_eq_right h] at hzero
        linarith
    · rintro h
      norm_num [h]

end SKEFTHawking.QuantumNetwork.OneRecordCoherentSchedule
