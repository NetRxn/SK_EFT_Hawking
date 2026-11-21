import SKEFTHawking.QuantumNetwork.OneRecordMemoryErrorBudget
import SKEFTHawking.QuantumNetwork.NegativityGeneral

/-!
# Conditioning errors for the selected timing circuit

The trace norm of the difference of normalized positive branches is
controlled by the unnormalized difference and the nominal selection mass.
The actual coherent and dephased masses give the two amplification factors
in the circuit certificate. Conditional priors may differ between the
nominal and perturbed experiments.

For a fixed input prior, common normalization instead uses the total
postselection mass. The circuit's raw error budget itself guarantees a
positive observed total, so the perturbed weights follow from the
measured branches.
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

private theorem traceNorm_scaled_branch_sub_le {X X' : Matrix ι ι ℂ}
    (hX' : X'.PosSemidef) {s s' : ℝ} (hs : 0 ≤ s) :
    traceNorm ((s : ℂ) • X - (s' : ℂ) • X') ≤
      s * traceNorm (X - X') + |s - s'| * X'.trace.re := by
  have he : (s : ℂ) • X - (s' : ℂ) • X' =
      (s : ℂ) • (X - X') + ((s - s' : ℝ) : ℂ) • X' := by
    push_cast
    rw [smul_sub, sub_smul]
    abel
  rw [he]
  refine (traceNorm_triangle _ _).trans ?_
  rw [traceNorm_real_smul, traceNorm_real_smul, abs_of_nonneg hs, traceNorm_posSemidef hX']

private theorem abs_trace_pair_sub_le {X Y X' Y' : Matrix ι ι ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) (hX' : X'.IsHermitian) (hY' : Y'.IsHermitian) :
    |(X.trace.re + Y.trace.re) - (X'.trace.re + Y'.trace.re)| ≤
      traceNorm (X - X') + traceNorm (Y - Y') := by
  have hx : |X.trace.re - X'.trace.re| ≤ traceNorm (X - X') := by
    simpa only [Matrix.trace_sub, Complex.sub_re] using traceNorm_ge_abs_re_trace (hX.sub hX')
  have hy : |Y.trace.re - Y'.trace.re| ≤ traceNorm (Y - Y') := by
    simpa only [Matrix.trace_sub, Complex.sub_re] using traceNorm_ge_abs_re_trace (hY.sub hY')
  rw [show (X.trace.re + Y.trace.re) - (X'.trace.re + Y'.trace.re) =
    X.trace.re - X'.trace.re + (Y.trace.re - Y'.trace.re) by ring]
  exact (abs_add_le _ _).trans (add_le_add hx hy)

/-- Normalizing both weighted raw branches by the same success mass
costs at most twice the combined raw trace-norm error divided by the
nominal total success mass. -/
theorem traceNorm_joint_selection_sub_le {X Y X' Y' : Matrix ι ι ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (hX' : X'.PosSemidef) (hY' : Y'.PosSemidef)
    (h : 0 < X.trace.re + Y.trace.re) (h' : 0 < X'.trace.re + Y'.trace.re) :
    let m := X.trace.re + Y.trace.re
    let m' := X'.trace.re + Y'.trace.re
    traceNorm (((m⁻¹ : ℝ) : ℂ) • X - ((m'⁻¹ : ℝ) : ℂ) • X') +
      traceNorm (((m⁻¹ : ℝ) : ℂ) • Y - ((m'⁻¹ : ℝ) : ℂ) • Y') ≤
      2 / m * (traceNorm (X - X') + traceNorm (Y - Y')) := by
  intro m m'
  have h0 : 0 < m := h
  have h0' : 0 < m' := h'
  have hMass : |m - m'| ≤ traceNorm (X - X') + traceNorm (Y - Y') :=
    abs_trace_pair_sub_le hX.isHermitian hY.isHermitian hX'.isHermitian hY'.isHermitian
  have hInv : |m⁻¹ - m'⁻¹| * m' = |m - m'| / m := by
    have he : m⁻¹ - m'⁻¹ = (m' - m) / (m * m') := by field_simp [h0.ne', h0'.ne']
    rw [he, abs_div, abs_sub_comm m' m, abs_of_pos (mul_pos h0 h0')]
    field_simp [h0.ne', h0'.ne']
  have hΔX := traceNorm_scaled_branch_sub_le hX' (inv_nonneg.mpr h0.le) (s' := m'⁻¹)
    (X := X)
  have hΔY := traceNorm_scaled_branch_sub_le hY' (inv_nonneg.mpr h0.le) (s' := m'⁻¹)
    (X := Y)
  refine (add_le_add hΔX hΔY).trans ?_
  calc
    _ = m⁻¹ * (traceNorm (X - X') + traceNorm (Y - Y')) + |m⁻¹ - m'⁻¹| * m' := by
      dsimp only [m']
      ring
    _ ≤ _ := by
      rw [hInv]
      have hb := div_le_div_of_nonneg_right hMass h0.le
      rw [div_eq_mul_inv, div_eq_mul_inv] at hb
      rw [div_eq_mul_inv, div_eq_mul_inv]
      linarith only [hb]

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

/-- With a fixed input prior above one third, the observed selection mass
determines the perturbed conditional ensemble directly. A raw-branch
error budget ensures positive total observed mass and preserves the
selected circuit's joint readout advantage. -/
theorem selected_joint_beats_memory_under_input_prior_error (a b c d r : ℝ)
    (train : a^2 + b^2 = 1) (offset : c^2 + d^2 = 1) (hd : d ≠ 0)
    (hr : 1 / 3 < r) (hr1 : r < 1) (hd1 : d^2 < 1)
    (C' D' : Matrix (Fin 4) (Fin 4) ℂ) (hC' : C'.PosSemidef) (hD' : D'.PosSemidef) :
    let C := coherentSelected a b c d
    let D := dephasedSelected a b c d
    let m := r * (d^2 / 2) + (1 - r) / 2
    let m' := r * C'.trace.re + (1 - r) * D'.trace.re
    let p := r * (d^2 / 2) / m
    let q := 1 - p
    let P' := (((r / m' : ℝ) : ℂ)) • C'
    let Q' := ((((1 - r) / m' : ℝ) : ℂ)) • D'
    let margin := q * (1 - d^2) * (p - q * (d^2 / 2)) / (2 * (p + q * (1 - d^2)))
    2 / m * (r * traceNorm (C - C') + (1 - r) * traceNorm (D - D')) < margin →
    0 < m' ∧ ∃ E : Matrix (Fin 4) (Fin 4) ℂ, E.PosSemidef ∧ (1 - E).PosSemidef ∧
      ∀ F : Matrix (Fin 2) (Fin 2) ℂ, F.PosSemidef → (1 - F).PosSemidef →
        (memoryMarginal P' * F).trace.re + (memoryMarginal Q' * (1 - F)).trace.re <
          (P' * E).trace.re + (Q' * (1 - E)).trace.re := by
  intro C D m m' p q P' Q' margin hbudget
  have hr0 : 0 < r := by linarith
  have hOther : 0 < 1 - r := sub_pos.mpr hr1
  have hd0 : 0 < d^2 / 2 := div_pos (sq_pos_of_ne_zero hd) (by norm_num)
  have hm : 0 < m := add_pos (mul_pos hr0 hd0) (div_pos hOther (by norm_num))
  have hp : 0 ≤ p := div_nonneg (mul_nonneg hr0.le hd0.le) hm.le
  have hp1 : p < 1 := by
    apply (div_lt_one hm).mpr
    dsimp only [m]
    linarith [div_pos hOther (by norm_num : (0 : ℝ) < 2)]
  have hq : q = ((1 - r) / 2) / m := by
    dsimp only [q, p]
    calc
      _ = m / m - r * (d^2 / 2) / m := by rw [div_self hm.ne']
      _ = (m - r * (d^2 / 2)) / m := (sub_div _ _ _).symm
      _ = _ := by
        congr 1
        dsimp only [m]
        ring
  have hJ : q * (d^2 / 2) < p := by
    rw [hq, div_mul_eq_mul_div]
    apply div_lt_div_of_pos_right _ hm
    exact mul_lt_mul_of_pos_right (by linarith) hd0
  obtain ⟨hC, hD, _, hmassC, _, hmassD, _⟩ := selected_density_contrast a b c d train offset hd
  let X := (r : ℂ) • C
  let Y := (((1 - r : ℝ) : ℂ)) • D
  let X' := (r : ℂ) • C'
  let Y' := (((1 - r : ℝ) : ℂ)) • D'
  have hX : X.PosSemidef := hC.smul (Complex.zero_le_real.mpr hr0.le)
  have hY : Y.PosSemidef := hD.smul (Complex.zero_le_real.mpr hOther.le)
  have hX' : X'.PosSemidef := hC'.smul (Complex.zero_le_real.mpr hr0.le)
  have hY' : Y'.PosSemidef := hD'.smul (Complex.zero_le_real.mpr hOther.le)
  have hN : X.trace.re + Y.trace.re = m := by
    change C.trace.re = d^2 / 2 at hmassC
    change D.trace.re = 1 / 2 at hmassD
    simp only [X, Y, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul, hmassC, hmassD, m]
    ring
  have hN' : X'.trace.re + Y'.trace.re = m' := by
    simp only [X', Y', Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul, m']
  have hRawC : X - X' = (r : ℂ) • (C - C') := (smul_sub _ _ _).symm
  have hRawD : Y - Y' = ((1 - r : ℝ) : ℂ) • (D - D') := (smul_sub _ _ _).symm
  let e := r * traceNorm (C - C') + (1 - r) * traceNorm (D - D')
  have hMass : |m - m'| ≤ e := by
    have h := abs_trace_pair_sub_le hX.isHermitian hY.isHermitian hX'.isHermitian hY'.isHermitian
    rw [hN, hN', hRawC, hRawD, traceNorm_real_smul, traceNorm_real_smul,
      abs_of_nonneg hr0.le, abs_of_nonneg hOther.le] at h
    exact h
  have hMargin : margin ≤ 1 / 2 := by
    let K := q * (1 - d^2)
    have hq0 : 0 < q := sub_pos.mpr hp1
    have hK : 0 < K := mul_pos hq0 (sub_pos.mpr hd1)
    have hsmall : p - q * (d^2 / 2) ≤ 1 := by
      linarith [mul_nonneg hq0.le hd0.le]
    change K * (p - q * (d^2 / 2)) / (2 * (p + K)) ≤ 1 / 2
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) (add_pos_of_nonneg_of_pos hp hK))).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsmall hK.le]
  have hErr' : 2 * e < m / 2 := by
    have hb : (2 / m) * e < 1 / 2 := hbudget.trans_le hMargin
    rw [div_mul_eq_mul_div] at hb
    have ht := (div_lt_iff₀ hm).mp hb
    nlinarith only [ht]
  have hm' : 0 < m' := by
    linarith [hErr', (le_abs_self (m - m')).trans hMass]
  refine ⟨hm', ?_⟩
  have hP' : P'.PosSemidef := hC'.smul (Complex.zero_le_real.mpr (div_nonneg hr0.le hm'.le))
  have hQ' : Q'.PosSemidef := hD'.smul (Complex.zero_le_real.mpr (div_nonneg hOther.le hm'.le))
  have hNorm' : P'.trace.re + Q'.trace.re = 1 := by
    dsimp only [P', Q']
    simp only [Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul, div_mul_eq_mul_div, ← add_div]
    exact div_self hm'.ne'
  have hErr := traceNorm_joint_selection_sub_le hX hY hX' hY' (hN.symm ▸ hm) (hN'.symm ▸ hm')
  dsimp only at hErr
  rw [hN, hN'] at hErr
  have hNomC : ((m⁻¹ : ℝ) : ℂ) • X = (((p / (d^2 / 2) : ℝ) : ℂ)) • C := by
    dsimp only [X]
    rw [smul_smul, ← Complex.ofReal_mul]
    congr 2
    dsimp only [p]
    field_simp [hm.ne', hd0.ne']
  have hNomD : ((m⁻¹ : ℝ) : ℂ) • Y = (((2 * q : ℝ) : ℂ)) • D := by
    dsimp only [Y]
    rw [smul_smul, ← Complex.ofReal_mul, hq]
    congr 2
    ring
  have hObsC : ((m'⁻¹ : ℝ) : ℂ) • X' = P' := by
    dsimp only [X', P']
    rw [smul_smul, ← Complex.ofReal_mul]
    congr 2
    ring
  have hObsD : ((m'⁻¹ : ℝ) : ℂ) • Y' = Q' := by
    dsimp only [Y', Q']
    rw [smul_smul, ← Complex.ofReal_mul]
    congr 2
    ring
  rw [hNomC, hNomD, hObsC, hObsD, hRawC, hRawD, traceNorm_real_smul, traceNorm_real_smul,
    abs_of_nonneg hr0.le, abs_of_nonneg hOther.le] at hErr
  exact selected_joint_beats_memory_under_traceNorm_error a b c d p train offset hd hp hp1 hd1 hJ
    P' Q' hP' hQ' hNorm' (hErr.trans_lt hbudget)

end SKEFTHawking.QuantumNetwork.OneRecordCoherentSchedule
