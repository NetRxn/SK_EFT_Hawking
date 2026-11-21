import SKEFTHawking.QuantumNetwork.OneRecordMemoryReadout

/-!
# Joint versus memory-only discrimination after one-record selection

Both optima use the same two weighted, selected branches. The timing
coefficients and the conditional priors determine exactly when observing
the system as well as the memory gives a higher binary success score.
-/

open Matrix
open scoped ComplexOrder

namespace SKEFTHawking.QuantumNetwork.OneRecordCoherentSchedule

/-- Compare the two score formulas under the imbalance bound. Strict inequality
holds exactly when the complementary prior and joint gain are positive and
the selection coefficient is below one. -/
theorem memory_joint_prior_score_comparison (p q t x : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (ht1 : t ≤ 1)
    (hx : x^2 ≤ 1 - t) :
    let jointGain := p - q * t / 2
    let memoryGain := (p - q + Real.sqrt (p^2 + (q * x)^2)) / 2
    q + max 0 memoryGain ≤ q + max 0 jointGain ∧
      (q + max 0 memoryGain < q + max 0 jointGain ↔
        0 < q ∧ t < 1 ∧ 0 < jointGain) := by
  intro jointGain memoryGain
  let rad := p^2 + (q * x)^2
  have hrad : 0 ≤ rad := by dsimp [rad]; positivity
  have hdiff : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hs0 : 0 ≤ 1 - t - x^2 := sub_nonneg.mpr hx
  by_cases hj : 0 < jointGain
  · let b := p + q * (1 - t)
    have hb : 0 ≤ b := add_nonneg hp (mul_nonneg hq hdiff)
    have hgain : 0 < 2 * p - q * t := by dsimp [jointGain] at hj; linarith only [hj]
    have hfactor : b^2 - rad =
        q * (1 - t) * (2 * p - q * t) + q^2 * (1 - t - x^2) := by
      dsimp [b, rad]
      ring
    have hradBound : rad ≤ b^2 := by
      linarith only [hfactor, mul_nonneg (mul_nonneg hq hdiff) hgain.le,
        mul_nonneg (sq_nonneg q) hs0]
    have hroot : Real.sqrt rad ≤ b := (Real.sqrt_le_iff).2 ⟨hb, hradBound⟩
    have hmem : memoryGain ≤ jointGain := by
      change (p - q + Real.sqrt rad) / 2 ≤ p - q * t/2
      dsimp only [b] at hroot
      linarith only [hroot]
    refine ⟨add_le_add le_rfl (max_le_max_left 0 hmem), ?_⟩
    by_cases hactive : 0 < q ∧ t < 1
    · have hstrict : rad < b^2 := by
        linarith only [hfactor, mul_pos (mul_pos hactive.1 (sub_pos.mpr hactive.2)) hgain,
          mul_nonneg (sq_nonneg q) hs0]
      have hs : Real.sqrt rad < b := (Real.sqrt_lt hrad hb).2 hstrict
      have hm : memoryGain < jointGain := by
        change (p - q + Real.sqrt rad) / 2 < p - q * t/2
        dsimp only [b] at hs
        linarith only [hs]
      have hMax : max 0 memoryGain < jointGain := max_lt_iff.2 ⟨hj,hm⟩
      rw [max_eq_right hj.le]
      exact iff_of_true (by linarith only [hMax]) ⟨hactive.1,hactive.2,hj⟩
    · have he : memoryGain = jointGain := by
        by_cases hq0 : q = 0
        · dsimp [memoryGain,jointGain]
          rw [hq0]
          simp [Real.sqrt_sq_eq_abs, abs_of_nonneg hp]
        · have ht : t = 1 := by
            have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
            rcases lt_or_eq_of_le ht1 with hlt | heq
            · exact (hactive ⟨hqp,hlt⟩).elim
            · exact heq
          have hx0 : x = 0 := by
            rw [ht, sub_self] at hx
            exact sq_eq_zero_iff.mp (le_antisymm hx (sq_nonneg _))
          dsimp [memoryGain,jointGain]
          rw [ht,hx0]
          simp [Real.sqrt_sq_eq_abs, abs_of_nonneg hp]
          ring
      rw [he]
      exact iff_of_false (lt_irrefl _) (fun h => hactive ⟨h.1,h.2.1⟩)
  · have hj0 : jointGain ≤ 0 := le_of_not_gt hj
    have htwo : 0 ≤ q * t - 2 * p := by dsimp [jointGain] at hj0; linarith only [hj0]
    have hb : 0 ≤ q - p := by
      linarith only [htwo, hp, mul_le_mul_of_nonneg_left ht1 hq]
    have he : (q - p)^2 - rad = q*(q * t - 2 * p) + q^2*(1 - t - x^2) := by
      dsimp [rad]
      ring
    have hs : Real.sqrt rad ≤ q - p := (Real.sqrt_le_iff).2 ⟨hb, by
      linarith only [he, mul_nonneg hq htwo, mul_nonneg (sq_nonneg q) hs0]⟩
    have hmem : memoryGain ≤ 0 := by
      change (p - q + Real.sqrt rad) / 2 ≤ 0
      linarith only [hs]
    rw [max_eq_left hj0, max_eq_left hmem]
    exact ⟨le_rfl, iff_of_false (lt_irrefl _) (fun h => hj h.2.2)⟩

/-- The squared memory population imbalance is at most the squared cosine of the offset. -/
theorem selected_memory_imbalance_sq_le (a b c d : ℝ)
    (train : a^2 + b^2 = 1) (offset : c^2 + d^2 = 1) :
    let u := ((a * c - b * d)^2 + a^2) / 2
    (1 - 2*u)^2 ≤ 1 - d^2 := by
  intro u
  let x := c*(a^2 - b^2) - 2*d * a * b
  let y := d*(a^2 - b^2) + 2*c * a * b
  have hrot : x^2 + y^2 = 1 := by
    calc
      _ = (c^2 + d^2)*(a^2 + b^2)^2 := by dsimp [x,y]; ring
      _ = 1 := by simp [offset,train]
  have hx : x^2 ≤ 1 := by linarith only [hrot,sq_nonneg y]
  have himbalance : 1 - 2*u = -c*x := by
    dsimp [u,x]
    have hb : b^2*(c^2 + d^2) = b^2 := by rw [offset,mul_one]
    nlinarith only [train,hb]
  calc
    _ = c^2*x^2 := by rw [himbalance]; ring
    _ ≤ c^2*1 := mul_le_mul_of_nonneg_left hx (sq_nonneg c)
    _ = 1 - d^2 := by linarith only [offset]

/-- Exact memory-only and joint optima for the same selected branches. The
joint improvement is strict precisely when the dephased prior is positive,
the squared sine of the offset is below one, and the joint effect improves
on always choosing the dephased hypothesis. -/
theorem selected_memory_and_joint_optima (a b c d p : ℝ)
    (train : a^2 + b^2 = 1) (offset : c^2 + d^2 = 1) (hd : d ≠ 0)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    let q := 1 - p
    let u := ((a * c - b * d)^2 + a^2) / 2
    let P := (((p / (d^2 / 2) : ℝ) : ℂ)) • coherentSelected a b c d
    let Q := (((2 * q : ℝ) : ℂ)) • dephasedSelected a b c d
    let memory := q + max 0 ((p - q + Real.sqrt (p^2 + (q*(1 - 2 * u))^2)) / 2)
    let joint := q + max 0 (p - q*(d^2 / 2))
    IsGreatest {x | ∃ E : Matrix (Fin 2) (Fin 2) ℂ,
      E.PosSemidef ∧ (1 - E).PosSemidef ∧
      ((memoryMarginal P * E).trace.re + (memoryMarginal Q * (1 - E)).trace.re = x)} memory ∧
    IsGreatest {x | ∃ E : Matrix (Fin 4) (Fin 4) ℂ,
      E.PosSemidef ∧ (1 - E).PosSemidef ∧ ((P * E).trace.re + (Q * (1 - E)).trace.re = x)} joint ∧
    memory ≤ joint ∧ (memory < joint ↔ p < 1 ∧ d^2 < 1 ∧ q * (d^2 / 2) < p) := by
  intro q u P Q memory joint
  have hm := selected_memory_effect_optimum_with_prior a b c d p train offset hd hp0 hp1
  obtain ⟨_,_,hUpper,hAttain⟩ :=
    one_record_conditional_optimum_with_prior a b c d p train offset hd hp0 hp1
  have hJoint : IsGreatest {x | ∃ E : Matrix (Fin 4) (Fin 4) ℂ,
      E.PosSemidef ∧ (1 - E).PosSemidef ∧ ((P * E).trace.re + (Q * (1 - E)).trace.re = x)} joint := by
    constructor
    · obtain ⟨F,hF,hIF,hscore⟩ := hAttain
      refine ⟨F (),hF (),hIF (),?_⟩
      simpa only [finite_binary_success, Fintype.sum_unique] using hscore
    · rintro x ⟨E,hE,hIE,rfl⟩
      simpa only [finite_binary_success, Fintype.sum_unique] using
        hUpper (fun _ => E) (fun _ => hE) (fun _ => hIE)
  have hd1 : d^2 ≤ 1 := by nlinarith only [offset,sq_nonneg c]
  have hCompare := memory_joint_prior_score_comparison p q (d^2) (1 - 2 * u)
    hp0 (sub_nonneg.mpr hp1) hd1 (selected_memory_imbalance_sq_le a b c d train offset)
  have hGain : p - q * d^2 / 2 = p - q * (d^2 / 2) := by ring
  rw [hGain] at hCompare
  refine ⟨hm, hJoint, hCompare.1, ?_⟩
  simpa only [sub_pos, q] using hCompare.2

end SKEFTHawking.QuantumNetwork.OneRecordCoherentSchedule
