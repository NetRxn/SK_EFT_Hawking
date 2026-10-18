import SKEFTHawking.QuantumNetwork.FiniteThreeLevelCompressedStrategyMemoryExamples

/-!
# Ordinary events of the actual binary history experiment

The table below is obtained from the normalized inserted Kraus tree.  The
weighted norm uses the existing sandwich feature and a local Hilbert–Schmidt
instance.  The equal-label event is classical postprocessing of recorded labels.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteThreeLevelCompressedMemoryObservability
open Matrix FiniteInterventionProcess FiniteThreeLevelStationaryStrategyReflection
open FiniteThreeLevelStationaryStrategyTransfer FiniteThreeLevelStationaryStrategyTransferExamples
open FiniteThreeLevelCompressedStrategyMemory FiniteThreeLevelCompressedStrategyMemoryExamples
open FiniteThreeLevelPositiveHistory (Q MatQ form Psi rhoN feature featureLinear)
open FiniteThreeLevelHistoryTransfer (mean rotate)
open FinitePositiveKernel.GibbsObservable
open scoped BigOperators ComplexOrder InnerProductSpace

local instance : NormedAddCommGroup MatQ := Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one
local instance : InnerProductSpace ℂ MatQ := Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

abbrev Table := Fin 2 → Fin 2 → ℝ
def labelMass : Fin 2 → ℝ := ![1/12, 11/12]
def labelSign : Fin 2 → ℝ := ![1, -1]
def baseline : Table := fun i j => labelMass i * labelMass j
def equalLabels (k : Table) : ℝ := k 0 0 + k 1 1
def finiteTV (k l : Table) : ℝ := (1/2) * ∑ i, ∑ j, |k i j - l i j|
def ProbabilityTable (k : Table) : Prop := (∀ i j, 0 ≤ k i j) ∧ ∑ i, ∑ j, k i j = 1
def weightedNorm (A : MatQ) : ℝ := ‖feature A‖
def beta {m : ℕ} (L : Fin m → MatQ) : ℝ :=
  (form centeredF (Channel.heisenberg L centeredF)).re
def correlation {m : ℕ} (p : ℝ) (L : Fin m → MatQ) : ℝ := p^2 * beta L

/-- Actual encoded weights, rather than a table defined by its closed formula. -/
def channelTable {m : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (L : Fin m → MatQ) (hL : IsKrausChannel L) : Table := fun i j =>
  (insertedKernel binaryTree p (by decide) binary_stationary hp hp1 L hL (i,()) (j,())).re

theorem centeredF_adjoint : centeredFᴴ = centeredF := by
  simp [centeredF, ← binary_effect_zero, effect_adjoint]

theorem mean_heisenberg {m : ℕ} (L : Fin m → MatQ)
    (hstat : krausMap L rhoN = rhoN) (A : MatQ) :
    mean (Channel.heisenberg L A) = mean A := by
  change (rhoN * Channel.heisenberg L A).trace = (rhoN * A).trace
  rw [Channel.trace_duality, hstat]

theorem centered_response_real {m : ℕ} (L : Fin m → MatQ) :
    (beta L : ℂ) = form centeredF (Channel.heisenberg L centeredF) := by
  have ho : (Channel.heisenberg L centeredF)ᴴ = Channel.heisenberg L centeredF := by
    rw [← Channel.heisenberg_star, centeredF_adjoint]
  have hs : (FiniteThreeLevelPositiveHistory.R * centeredF * FiniteThreeLevelPositiveHistory.R)ᴴ =
      FiniteThreeLevelPositiveHistory.R * centeredF * FiniteThreeLevelPositiveHistory.R := by
    simp only [Matrix.conjTranspose_mul, FiniteThreeLevelPositiveHistory.R_adjoint,
      centeredF_adjoint]
    noncomm_ring
  simpa only [beta, form, centeredF_adjoint, Matrix.mul_assoc] using
    FiniteThreeLevelPositiveHistory.hermitian_product_real
      (Channel.heisenberg L centeredF)
      (FiniteThreeLevelPositiveHistory.R * centeredF * FiniteThreeLevelPositiveHistory.R) ho hs

theorem binary_column (p : ℝ) (i : Fin 2) :
    Psi p (effect binaryTree (i,())) =
      (labelMass i : ℂ) • 1 + ((labelSign i * p : ℝ) : ℂ) • centeredF := by
  fin_cases i
  · simpa [labelMass, labelSign, binary_effect_zero] using binary_column_zero p
  · simpa [labelMass, labelSign, binary_effect_one, sub_eq_add_neg] using binary_column_one p

theorem centered_form_expansion {m : ℕ} (L : Fin m → MatQ) (hL : IsKrausChannel L)
    (hstat : krausMap L rhoN = rhoN) (x y u v : ℝ) :
    form ((x : ℂ) • 1 + (u : ℂ) • centeredF)
      (Channel.heisenberg L ((y : ℂ) • 1 + (v : ℂ) • centeredF)) =
        ((x*y + u*v*beta L : ℝ) : ℂ) := by
  have hm : form 1 (Channel.heisenberg L centeredF) = 0 := by
    rw [form_one_left, mean_heisenberg L hstat, mean_F]
  rw [Channel.heisenberg_add, Channel.heisenberg_smul, Channel.heisenberg_smul,
    Channel.heisenberg_one L hL]
  simp only [form_add_left, FiniteThreeLevelHistoryTransfer.form_add_right,
    form_smul_left, FiniteThreeLevelHistoryTransfer.form_smul_right, hm, form_FI,
    form_one_left, FiniteThreeLevelHistoryTransfer.mean_one, mul_zero, add_zero,
    zero_add, Complex.star_def, Complex.conj_ofReal, ← centered_response_real L]
  push_cast
  ring

/-- Full complex law; normalization, stationarity and commutation have separate roles. -/
theorem inserted_binary_law {m : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (L : Fin m → MatQ) (hL : IsKrausChannel L) (hstat : krausMap L rhoN = rhoN)
    (hcomm : ∀ A, Channel.heisenberg L (Psi p A) = Psi p (Channel.heisenberg L A))
    (i j : Fin 2) :
    insertedKernel binaryTree p (by decide) binary_stationary hp hp1 L hL (i,()) (j,()) =
      ((labelMass i * labelMass j + labelSign i * labelSign j * correlation p L : ℝ) : ℂ) := by
  rw [insertedKernel_form _ _ _ _ _ _ _ _ hcomm, binary_column, binary_column]
  rw [centered_form_expansion L hL hstat]
  congr 1
  dsimp [correlation]
  ring


/-- A derived four-entry law, used only after connecting the actual tree. -/
def BinaryLaw (k : Table) (q : ℝ) : Prop := ∀ i j,
  k i j = labelMass i * labelMass j + labelSign i * labelSign j * q

theorem channelTable_law {m : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (L : Fin m → MatQ) (hL : IsKrausChannel L) (hstat : krausMap L rhoN = rhoN)
    (hcomm : ∀ A, Channel.heisenberg L (Psi p A) = Psi p (Channel.heisenberg L A)) :
    BinaryLaw (channelTable p hp hp1 L hL) (correlation p L) := by
  intro i j
  exact congrArg Complex.re (inserted_binary_law p hp hp1 L hL hstat hcomm i j)

theorem channelTable_probability {m : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (L : Fin m → MatQ) (hL : IsKrausChannel L) :
    ProbabilityTable (channelTable p hp hp1 L hL) := by
  constructor
  · intro i j
    exact insertedKernel_nonnegative binaryTree p (by decide) binary_stationary hp hp1 L hL _ _
  · have hn := congrArg Complex.re
      (insertedKernel_normalized binaryTree p (by decide) binary_stationary hp hp1 L hL)
    change (∑ i : Fin 2 × Unit, ∑ j : Fin 2 × Unit,
      insertedKernel binaryTree p (by decide) binary_stationary hp hp1 L hL i j).re = 1 at hn
    convert hn using 1
    simp [channelTable, Fintype.sum_prod_type]
    rfl

theorem binary_mass (i : Fin 2) : mass binaryTree (i,()) = labelMass i := by
  rcases i with ⟨i, hi⟩
  interval_cases i
  · apply Complex.ofReal_injective
    erw [mass_complex, binary_effect_zero]
    simpa [mean, labelMass] using binary_mean
  · apply Complex.ofReal_injective
    erw [mass_complex, binary_effect_one]
    have hb : (rhoN * binaryEffect).trace = (1/12 : ℂ) := by
      simpa [mean] using binary_mean
    norm_num [mul_sub, Matrix.trace_sub, hb, FiniteThreeLevelPositiveHistory.rhoN_trace, labelMass]

theorem channelTable_row {m : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (L : Fin m → MatQ) (hL : IsKrausChannel L) (i : Fin 2) :
    ∑ j, channelTable p hp hp1 L hL i j = labelMass i := by
  have hr := congrArg Complex.re
    (insertedKernel_row_sum binaryTree p (by decide) binary_stationary hp hp1 L hL (i,()))
  change (∑ j : Fin 2 × Unit,
    insertedKernel binaryTree p (by decide) binary_stationary hp hp1 L hL (i,()) j).re = _ at hr
  convert hr using 1
  · simp [channelTable, Fintype.sum_prod_type]
    rfl
  · simpa using (binary_mass _).symm

theorem channelTable_column {m : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (L : Fin m → MatQ) (hL : IsKrausChannel L) (hstat : krausMap L rhoN = rhoN)
    (j : Fin 2) : ∑ i, channelTable p hp hp1 L hL i j = labelMass j := by
  have hc := congrArg Complex.re
    (insertedKernel_column_sum binaryTree p (by decide) binary_stationary hp hp1 L hL hstat (j,()))
  change (∑ i : Fin 2 × Unit,
    insertedKernel binaryTree p (by decide) binary_stationary hp hp1 L hL i (j,())).re = _ at hc
  convert hc using 1
  · simp [channelTable, Fintype.sum_prod_type]
    rfl
  · simpa using (binary_mass _).symm

theorem channel_correlation_interval {m : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (L : Fin m → MatQ) (hL : IsKrausChannel L) (hstat : krausMap L rhoN = rhoN)
    (hcomm : ∀ A, Channel.heisenberg L (Psi p A) = Psi p (Channel.heisenberg L A)) :
    -(1/12:ℝ)^2 ≤ correlation p L ∧ correlation p L ≤ (1/12:ℝ)*(11/12) := by
  have hn := (channelTable_probability p hp hp1 L hL).1
  have hk := channelTable_law p hp hp1 L hL hstat hcomm
  have h00 := hn 0 0
  have h01 := hn 0 1
  rw [hk 0 0] at h00
  rw [hk 0 1] at h01
  norm_num [labelMass, labelSign] at h00 h01 ⊢
  constructor <;> linarith

theorem baseline_probability : ProbabilityTable baseline := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [baseline, labelMass]
  · norm_num [baseline, labelMass, Fin.sum_univ_two]

theorem baseline_equalLabels : equalLabels baseline = 61/72 := by
  norm_num [equalLabels, baseline, labelMass]

theorem baseline_law : BinaryLaw baseline 0 := by
  intro i j
  simp [baseline]

theorem law_equalLabels {k : Table} {q : ℝ} (hk : BinaryLaw k q) :
    equalLabels k - 61/72 = 2*q := by
  dsimp [equalLabels]
  rw [hk 0 0, hk 1 1]
  norm_num [labelMass, labelSign]
  ring

theorem law_difference {k l : Table} {q r : ℝ}
    (hk : BinaryLaw k q) (hl : BinaryLaw l r) (i j : Fin 2) :
    k i j - l i j = labelSign i * labelSign j * (q-r) := by
  rw [hk i j, hl i j]
  ring

theorem law_finiteTV {k l : Table} {q r : ℝ}
    (hk : BinaryLaw k q) (hl : BinaryLaw l r) : finiteTV k l = 2*|q-r| := by
  simp only [finiteTV, law_difference hk hl, Fin.sum_univ_two]
  norm_num [labelSign, abs_neg]
  simp only [abs_sub_comm]
  ring

theorem law_event_attains {k l : Table} {q r : ℝ}
    (hk : BinaryLaw k q) (hl : BinaryLaw l r) :
    |equalLabels k - equalLabels l| = finiteTV k l := by
  rw [law_finiteTV hk hl]
  have hq := law_equalLabels hk
  have hr := law_equalLabels hl
  have he : equalLabels k - equalLabels l = 2*(q-r) := by linarith
  rw [he, abs_mul]
  norm_num



def eventProbability (k : Table) (A : Finset (Fin 2 × Fin 2)) : ℝ :=
  ∑ i, ∑ j, if (i,j) ∈ A then k i j else 0

theorem eventProbability_sum (k : Table) (A : Finset (Fin 2 × Fin 2)) :
    eventProbability k A = ∑ x ∈ A, k x.1 x.2 := by
  classical
  unfold eventProbability
  calc
    _ = ∑ x : Fin 2 × Fin 2, if x ∈ A then k x.1 x.2 else 0 :=
      (Fintype.sum_prod_type (fun x : Fin 2 × Fin 2 => if x ∈ A then k x.1 x.2 else 0)).symm
    _ = _ := by simp

/-- Normalization suffices; the observed table need not have the model's marginals. -/
theorem event_contraction {k l : Table}
    (hk : ∑ i, ∑ j, k i j = 1) (hl : ∑ i, ∑ j, l i j = 1)
    (A : Finset (Fin 2 × Fin 2)) :
    |eventProbability k A - eventProbability l A| ≤ finiteTV k l := by
  classical
  have hn : (k 0 0-l 0 0)+(k 0 1-l 0 1)+(k 1 0-l 1 0)+(k 1 1-l 1 1) = 0 := by
    simp only [Fin.sum_univ_two] at hk hl
    linarith
  have h00 := le_abs_self (k 0 0-l 0 0)
  have h01 := le_abs_self (k 0 1-l 0 1)
  have h10 := le_abs_self (k 1 0-l 1 0)
  have h11 := le_abs_self (k 1 1-l 1 1)
  have g00 := neg_abs_le (k 0 0-l 0 0)
  have g01 := neg_abs_le (k 0 1-l 0 1)
  have g10 := neg_abs_le (k 1 0-l 1 0)
  have g11 := neg_abs_le (k 1 1-l 1 1)
  by_cases a00 : (0,0) ∈ A <;> by_cases a01 : (0,1) ∈ A <;>
    by_cases a10 : (1,0) ∈ A <;> by_cases a11 : (1,1) ∈ A <;>
    simp only [eventProbability, finiteTV, Fin.sum_univ_two, a00, a01, a10, a11,
      if_true, if_false] <;> apply abs_le.mpr <;> constructor <;> linarith

theorem equalLabels_contraction {k l : Table}
    (hk : ∑ i, ∑ j, k i j = 1) (hl : ∑ i, ∑ j, l i j = 1) :
    |equalLabels k - equalLabels l| ≤ finiteTV k l := by
  have he := event_contraction hk hl {(0,0),(1,1)}
  simpa [eventProbability, equalLabels, Fin.sum_univ_two] using he

theorem finiteTV_symm (k l : Table) : finiteTV k l = finiteTV l k := by
  simp only [finiteTV, abs_sub_comm]

theorem weightedNorm_F : weightedNorm centeredF = Real.sqrt N := by
  have hs : weightedNorm centeredF ^ 2 = N := by
    rw [weightedNorm, norm_sq_eq_re_inner (𝕜 := ℂ), feature_inner, form_FF]
    rfl
  have hn : 0 ≤ weightedNorm centeredF := norm_nonneg _
  nlinarith [hn, Real.sqrt_nonneg N, Real.sq_sqrt N_pos.le]

theorem centered_Psi (a : ℝ) : Psi a centeredF = (a : ℂ) • centeredF := by
  have hm : (rhoN * centeredF).trace = 0 := mean_F
  simp [Psi, hm]

def phaseResponse (t : ℝ) : ℝ := d + h * Real.cos (Real.pi*t/2)

theorem phaseResponse_multiplier (t : ℝ) : phaseResponse t = N * multiplier t := by
  unfold phaseResponse multiplier alpha N
  have hn := ne_of_gt N_pos
  dsimp [N] at hn
  field_simp
  ring

theorem pulse_centered (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (t : ℝ) :
    Channel.heisenberg (FiniteThreeLevelHistoryTransfer.pulseResetKraus a leakingFrequencies t)
      centeredF = (a : ℂ) • rotate leakingFrequencies t centeredF := by
  rw [FiniteThreeLevelHistoryTransfer.pulseReset_observable a ha ha1, centered_Psi, map_smul]

theorem pulse_beta (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (t : ℝ) :
    beta (FiniteThreeLevelHistoryTransfer.pulseResetKraus a leakingFrequencies t) =
      a * phaseResponse t := by
  rw [beta, pulse_centered a ha ha1, FiniteThreeLevelHistoryTransfer.form_smul_right,
    form_F_rotate, ← phaseResponse_multiplier]
  simp

/-- The real part of the existing actual pulse/reset kernel. -/
def pulseTable (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (t : ℝ) : Table := fun i j =>
  (pulseKernel binaryTree p (by decide) binary_stationary hp hp1
    a ha ha1 leakingFrequencies t (i,()) (j,())).re

theorem pulseTable_law (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (t : ℝ) :
    BinaryLaw (pulseTable p hp hp1 a ha ha1 t) (p^2*a*phaseResponse t) := by
  have hk := channelTable_law p hp hp1 _
    (FiniteThreeLevelHistoryTransfer.pulseReset_normalized a ha ha1 leakingFrequencies t)
    (pulse_stationary a ha ha1 leakingFrequencies t)
    (FiniteThreeLevelHistoryTransfer.pulseReset_commutes a ha ha1 leakingFrequencies t p)
  rw [correlation, pulse_beta a ha ha1] at hk
  simpa only [BinaryLaw, channelTable, pulseTable, pulseKernel, mul_assoc] using hk

theorem pulseTable_probability (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (t : ℝ) :
    ProbabilityTable (pulseTable p hp hp1 a ha ha1 t) :=
  channelTable_probability p hp hp1 _
    (FiniteThreeLevelHistoryTransfer.pulseReset_normalized a ha ha1 leakingFrequencies t)

theorem pulseTable_central_reset (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (t : ℝ) :
    pulseTable 0 (by norm_num) (by norm_num) a ha ha1 t = baseline := by
  funext i j
  rw [pulseTable_law 0 (by norm_num) (by norm_num) a ha ha1 t i j]
  simp [baseline]

theorem pulseTable_complete_reset (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) :
    pulseTable p hp hp1 0 (by norm_num) (by norm_num) t = baseline := by
  have hz := pulseKernel_zero binaryTree p (by decide) binary_stationary hp hp1 leakingFrequencies t
  funext i j
  change (pulseKernel binaryTree p (by decide) binary_stationary hp hp1
    0 (by norm_num) (by norm_num) leakingFrequencies t (i,()) (j,())).re = _
  rw [hz]
  simp [massKernel, baseline, binary_mass]

theorem pulseTable_original (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) (i j : Fin 2) :
    pulseTable p hp hp1 1 (by norm_num) (by norm_num) t i j =
      (actualKernel p hp hp1 t (i,()) (j,())).re := by
  unfold pulseTable actualKernel
  rw [pulseKernel_form, FiniteThreeLevelPositiveHistory.Psi_one,
    insertedKernel_form _ _ _ _ _ _ _ _ (by
      intro A
      simp only [FiniteThreeLevelHistoryTransfer.pulse_observable,
        FiniteThreeLevelHistoryTransfer.rotate_Psi]), FiniteThreeLevelHistoryTransfer.pulse_observable]

theorem pulseTable_event (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (t : ℝ) :
    equalLabels (pulseTable p hp hp1 a ha ha1 t)-61/72 = 2*p^2*a*phaseResponse t := by
  have he := law_equalLabels (pulseTable_law p hp hp1 a ha ha1 t)
  linarith

theorem pulseTable_TV_baseline (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (t : ℝ) :
    finiteTV (pulseTable p hp hp1 a ha ha1 t) baseline = 2*p^2*a*|phaseResponse t| := by
  rw [law_finiteTV (pulseTable_law p hp hp1 a ha ha1 t) baseline_law, sub_zero,
    abs_mul, abs_mul, abs_of_nonneg (sq_nonneg p), abs_of_nonneg ha]
  ring

/-- Cauchy–Schwarz acts on the actual weighted feature residual. -/
theorem correlation_residual_bound {m n : ℕ} (p : ℝ) (L : Fin m → MatQ) (M : Fin n → MatQ)
    (eta : ℝ) (hres : weightedNorm (Channel.heisenberg L centeredF -
      Channel.heisenberg M centeredF) ≤ eta * Real.sqrt N) :
    |correlation p L - correlation p M| ≤ p^2*N*eta := by
  have he : beta L-beta M = (form centeredF
      (Channel.heisenberg L centeredF - Channel.heisenberg M centeredF)).re := by
    simp [beta, form, sub_mul, Matrix.trace_sub]
  have hi := norm_inner_le_norm (𝕜 := ℂ) (feature centeredF)
    (feature (Channel.heisenberg L centeredF - Channel.heisenberg M centeredF))
  rw [feature_inner] at hi
  have hb : |beta L-beta M| ≤ N*eta := by
    calc
      |beta L-beta M| = |(form centeredF
        (Channel.heisenberg L centeredF - Channel.heisenberg M centeredF)).re| := congrArg abs he
      _ ≤ ‖form centeredF (Channel.heisenberg L centeredF - Channel.heisenberg M centeredF)‖ :=
        Complex.abs_re_le_norm _
      _ ≤ weightedNorm centeredF * weightedNorm
        (Channel.heisenberg L centeredF - Channel.heisenberg M centeredF) := hi
      _ ≤ Real.sqrt N * (eta * Real.sqrt N) := by
        rw [weightedNorm_F]
        exact mul_le_mul_of_nonneg_left hres (Real.sqrt_nonneg N)
      _ = N*eta := by
        calc
          _ = eta * (Real.sqrt N)^2 := by ring
          _ = _ := by rw [Real.sq_sqrt N_pos.le]; ring
  rw [correlation, correlation, ← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg p)]
  nlinarith [sq_nonneg p]

theorem pulse_retention_residual (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (t : ℝ) :
    weightedNorm (Channel.heisenberg (FiniteThreeLevelHistoryTransfer.pulseResetKraus a leakingFrequencies t) centeredF -
      Channel.heisenberg (FiniteThreeLevelHistoryTransfer.pulseResetKraus b leakingFrequencies t) centeredF) =
        |a-b| * Real.sqrt N := by
  rw [pulse_centered a ha ha1, pulse_centered b hb hb1, ← sub_smul, ← Complex.ofReal_sub]
  change ‖featureLinear (((a-b : ℝ) : ℂ) • rotate leakingFrequencies t centeredF)‖ = _
  rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  change |a-b| * ‖feature (rotate leakingFrequencies t centeredF)‖ = _
  rw [feature_rotate_norm]
  exact congrArg (|a-b| * ·) weightedNorm_F



theorem channel_finiteTV_bound {m n : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (L : Fin m → MatQ) (hL : IsKrausChannel L) (hstatL : krausMap L rhoN = rhoN)
    (hcL : ∀ A, Channel.heisenberg L (Psi p A) = Psi p (Channel.heisenberg L A))
    (M : Fin n → MatQ) (hM : IsKrausChannel M) (hstatM : krausMap M rhoN = rhoN)
    (hcM : ∀ A, Channel.heisenberg M (Psi p A) = Psi p (Channel.heisenberg M A))
    (eta : ℝ) (hres : weightedNorm (Channel.heisenberg L centeredF -
      Channel.heisenberg M centeredF) ≤ eta * Real.sqrt N) :
    finiteTV (channelTable p hp hp1 L hL) (channelTable p hp hp1 M hM) ≤ 2*p^2*N*eta := by
  rw [law_finiteTV (channelTable_law p hp hp1 L hL hstatL hcL)
    (channelTable_law p hp hp1 M hM hstatM hcM)]
  linarith [correlation_residual_bound p L M eta hres]

theorem channel_event_bound {m n : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (L : Fin m → MatQ) (hL : IsKrausChannel L) (hstatL : krausMap L rhoN = rhoN)
    (hcL : ∀ A, Channel.heisenberg L (Psi p A) = Psi p (Channel.heisenberg L A))
    (M : Fin n → MatQ) (hM : IsKrausChannel M) (hstatM : krausMap M rhoN = rhoN)
    (hcM : ∀ A, Channel.heisenberg M (Psi p A) = Psi p (Channel.heisenberg M A))
    (eta : ℝ) (hres : weightedNorm (Channel.heisenberg L centeredF -
      Channel.heisenberg M centeredF) ≤ eta * Real.sqrt N) :
    |equalLabels (channelTable p hp hp1 L hL)-equalLabels (channelTable p hp hp1 M hM)| ≤
      2*p^2*N*eta := by
  rw [law_event_attains (channelTable_law p hp hp1 L hL hstatL hcL)
    (channelTable_law p hp hp1 M hM hstatM hcM)]
  exact channel_finiteTV_bound p hp hp1 L hL hstatL hcL M hM hstatM hcM eta hres

theorem pulse_retention_TV (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) (t : ℝ) :
    finiteTV (pulseTable p hp hp1 a ha ha1 t) (pulseTable p hp hp1 b hb hb1 t) =
      2*p^2 * |a-b| * |phaseResponse t| := by
  rw [law_finiteTV (pulseTable_law p hp hp1 a ha ha1 t)
    (pulseTable_law p hp hp1 b hb hb1 t)]
  rw [show p^2*a*phaseResponse t-p^2*b*phaseResponse t = p^2*(a-b)*phaseResponse t by ring,
    abs_mul, abs_mul, abs_of_nonneg (sq_nonneg p)]
  ring


end SKEFTHawking.QuantumNetwork.FiniteThreeLevelCompressedMemoryObservability
