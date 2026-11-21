import SKEFTHawking.QuantumNetwork.OneRecordMemoryJointGap

/-!
# A quantitative advantage margin for the selected timing circuit

Comparing the squares of the two nonnegative terms in the scores
gives a positive margin throughout the strict-advantage region. The bound
is independent of the training coefficients.
-/

namespace SKEFTHawking.QuantumNetwork.OneRecordCoherentSchedule

/-- In the strict-advantage region the improvement has a uniform lower
bound over all admissible memory imbalances. -/
theorem memory_joint_score_gap_lower (p q t x : ℝ) (hp : 0 ≤ p) (hq : 0 < q)
    (ht : t < 1) (hx : x^2 ≤ 1 - t) (hj : 0 < p - q * t / 2) :
    let jointGain := p - q * t / 2
    let memoryGain := (p - q + Real.sqrt (p^2 + (q*x)^2)) / 2
    q * (1 - t) * jointGain / (2 * (p + q * (1 - t))) ≤
      (q + max 0 jointGain) - (q + max 0 memoryGain) := by
  intro jointGain memoryGain
  let b := p + q * (1 - t)
  let rad := p^2 + (q*x)^2
  let r := Real.sqrt rad
  have ht' : 0 < 1 - t := sub_pos.mpr ht
  have hqt : 0 < q * (1 - t) := mul_pos hq ht'
  have hb : 0 < b := add_pos_of_nonneg_of_pos hp hqt
  have h2b : 0 < 2*b := by positivity
  have hJ : 0 < jointGain := hj
  have hrad : 0 ≤ rad := by dsimp [rad]; positivity
  have hr : r^2 = rad := Real.sq_sqrt hrad
  have hfactor : b^2 - rad =
      2 * q * (1 - t) * jointGain + q^2 * (1 - t - x^2) := by
    dsimp [b, rad, jointGain]
    ring
  have hfirst : 0 ≤ 2 * q * (1 - t) * jointGain := by positivity
  have hsecond := mul_nonneg (sq_nonneg q) (sub_nonneg.mpr hx)
  have hrad_le : rad ≤ b^2 := by linarith only [hfactor, hfirst, hsecond]
  have hr_le : r ≤ b := Real.sqrt_le_iff.2 ⟨hb.le, hrad_le⟩
  have hmul := mul_le_mul_of_nonneg_left (show b + r ≤ 2*b by linarith only [hr_le])
    (sub_nonneg.mpr hr_le)
  have hprod : 2 * q * (1 - t) * jointGain ≤ (b-r) * (2*b) := by
    calc
      _ ≤ b^2 - rad := by linarith only [hfactor, hsecond]
      _ = (b-r) * (b+r) := by rw [← hr]; ring
      _ ≤ _ := hmul
  have hdecomp : b-r = 2 * (jointGain - memoryGain) := by
    dsimp [b, r, rad, jointGain, memoryGain]
    ring
  have hmem :
      q * (1 - t) * jointGain / (2*b) ≤ jointGain - memoryGain := by
    apply (div_le_iff₀ h2b).2
    rw [hdecomp] at hprod
    nlinarith only [hprod]
  have hbase :
      q * (1 - t) * jointGain / (2*b) ≤ jointGain := by
    apply (div_le_iff₀ h2b).2
    have hqb : q * (1 - t) ≤ 2*b := by
      dsimp [b]
      linarith only [hp, hqt]
    simpa only [mul_comm jointGain] using mul_le_mul_of_nonneg_right hqb hJ.le
  have hbudget : q * (1 - t) * jointGain / (2*b) ≤ jointGain - max 0 memoryGain := by
    rcases le_total memoryGain 0 with hm | hm
    · simpa only [max_eq_left hm, sub_zero] using hbase
    · simpa only [max_eq_right hm] using hmem
  rwa [max_eq_right hJ.le, add_sub_add_left_eq_sub]

/-- The score formulas have a positive, training-independent margin.
For nonzero coherent selection these are the circuit optima. -/
theorem selected_memory_joint_gap_lower (a b c d p : ℝ)
    (train : a^2 + b^2 = 1) (offset : c^2 + d^2 = 1)
    (hp : 0 ≤ p) (hp1 : p < 1) (hd : d^2 < 1)
    (hJ : (1-p) * (d^2 / 2) < p) :
    let q := 1-p
    let u := ((a*c - b*d)^2 + a^2) / 2
    let memory := q + max 0 ((p - q + Real.sqrt (p^2 + (q * (1 - 2*u))^2)) / 2)
    let joint := q + max 0 (p - q * (d^2 / 2))
    0 < q * (1 - d^2) * (p - q * (d^2 / 2)) / (2 * (p + q * (1 - d^2))) ∧
      q * (1 - d^2) * (p - q * (d^2 / 2)) / (2 * (p + q * (1 - d^2))) ≤ joint - memory := by
  intro q u memory joint
  have hq : 0 < q := sub_pos.mpr hp1
  have hd' : 0 < 1-d^2 := sub_pos.mpr hd
  have hj : 0 < p - q * (d^2/2) := sub_pos.mpr hJ
  have hden : 0 < p + q * (1 - d^2) := add_pos_of_nonneg_of_pos hp (mul_pos hq hd')
  refine ⟨by positivity, ?_⟩
  have he : p - q * d^2 / 2 = p - q * (d^2 / 2) := by ring
  have hd0 : 0 < p - q * d^2 / 2 := he.symm ▸ hj
  have h := memory_joint_score_gap_lower p q (d^2) (1 - 2*u) hp hq hd
    (selected_memory_imbalance_sq_le a b c d train offset) hd0
  simpa only [he] using h

end SKEFTHawking.QuantumNetwork.OneRecordCoherentSchedule
