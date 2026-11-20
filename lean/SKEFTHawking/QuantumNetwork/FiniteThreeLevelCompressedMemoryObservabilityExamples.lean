import SKEFTHawking.QuantumNetwork.FiniteThreeLevelCompressedMemoryObservability

/-!
# Actual sampled events and retained error margins

These are separate normalized phase experiments with one central reset and one
inserted pulse/reset.  They retain the predecessor's distinction between
uninterrupted evolution and repeated mathematical compression.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteThreeLevelCompressedMemoryObservabilityExamples
open Matrix FiniteInterventionProcess FiniteThreeLevelStationaryStrategyReflection
open FiniteThreeLevelStationaryStrategyTransfer FiniteThreeLevelStationaryStrategyTransferExamples
open FiniteThreeLevelCompressedStrategyMemory FiniteThreeLevelCompressedStrategyMemoryExamples
open FiniteThreeLevelCompressedMemoryObservability
open FiniteThreeLevelPositiveHistory (Q MatQ form Psi Phi rhoN feature)
open FiniteThreeLevelHistoryTransfer (mean rotate)
open FinitePositiveKernel.GibbsObservable
open scoped BigOperators ComplexOrder InnerProductSpace

local instance : NormedAddCommGroup MatQ := Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one
local instance : InnerProductSpace ℂ MatQ := Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

def pulseTree (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (t : ℝ) :=
  insertedTree binaryTree p (by decide) binary_stationary hp hp1
    (FiniteThreeLevelHistoryTransfer.pulseResetKraus a leakingFrequencies t)
    (FiniteThreeLevelHistoryTransfer.pulseReset_normalized a ha ha1 leakingFrequencies t)

/-- The full complex carrier fixes the order and the opposite state phase. -/
theorem pulse_run (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (t : ℝ)
    (u v : History 2 1) (X : MatQ) :
    FiniteAdaptiveKrausRealization.unJoint (run Q Unit _ (pulseTree p hp hp1 a ha ha1 t)
      (pairedHistory u v) (FiniteAdaptiveKrausRealization.joint X)) =
      branch binaryTree v (rotate leakingFrequencies (-t)
        (Phi a (Phi (p*p) (reverseBranch binaryTree u X)))) := by
  rw [pulseTree, inserted_run, FiniteThreeLevelHistoryTransfer.pulseReset_state a ha ha1]

theorem pulse_invalid_zero (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (t : ℝ)
    (v : History (pairedArity 2 1) (1+2))
    (hv : v ∉ Set.range (fun uv : History 2 1 × History 2 1 => pairedHistory uv.1 uv.2))
    (X : Matrix (Q × Unit) (Q × Unit) ℂ) :
    run Q Unit _ (pulseTree p hp hp1 a ha ha1 t) v X = 0 :=
  inserted_invalid_zero binaryTree p (by decide) binary_stationary hp hp1 _ _ v hv X

theorem pulse_encoded_sum (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (t : ℝ)
    (X : Matrix (Q × Unit) (Q × Unit) ℂ) :
    (∑ uv : History 2 1 × History 2 1,
      run Q Unit _ (pulseTree p hp hp1 a ha ha1 t) (pairedHistory uv.1 uv.2) X) =
      ∑ v, run Q Unit _ (pulseTree p hp hp1 a ha ha1 t) v X :=
  inserted_encoded_sum binaryTree p (by decide) binary_stationary hp hp1 _ _ X

theorem phaseResponse_zero : phaseResponse 0 = N := by norm_num [phaseResponse, N]
theorem phaseResponse_one : phaseResponse 1 = d := by norm_num [phaseResponse]
theorem phaseResponse_two : phaseResponse 2 = d-h := by
  rw [phaseResponse, show Real.pi*2/2 = Real.pi by ring, Real.cos_pi]
  ring
theorem phaseResponse_four : phaseResponse 4 = N := by
  rw [phaseResponse, show Real.pi*4/2 = 2*Real.pi by ring, Real.cos_two_pi]
  simp [N]

theorem h_gt_twice_d : 2*d < h := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 6 by norm_num)
  have hp := Real.sqrt_nonneg (6:ℝ)
  dsimp [d, h]
  nlinarith

theorem pairing_single_entry (K : Matrix (History 2 1) (History 2 1) ℂ) (u v : History 2 1) :
    FinitePositiveKernel.pairing K (Pi.single u 1) (Pi.single v 1) = K u v := by
  classical
  simp [FinitePositiveKernel.pairing]

/-- Actual predecessor recurrence consumed on coefficient basis vectors. -/
theorem original_entry_order_three (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p)
    (i j : Fin 2) (k : ℕ) :
    (actualKernel p hp hp1 ((k+3 : ℕ) : ℝ) (i,()) (j,())).re -
      (actualKernel p hp hp1 ((k+2 : ℕ) : ℝ) (i,()) (j,())).re +
      (actualKernel p hp hp1 ((k+1 : ℕ) : ℝ) (i,()) (j,())).re -
      (actualKernel p hp hp1 k (i,()) (j,())).re = 0 := by
  have he := actual_history_order_three p hp hp1 hpos
    (Pi.single (i,()) 1) (Pi.single (j,()) 1) k
  simp only [pairing_single_entry] at he
  simpa only [Complex.sub_re, Complex.add_re, Complex.zero_re] using congrArg Complex.re he

theorem original_entry_four_return (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p)
    (i j : Fin 2) (k : ℕ) :
    (actualKernel p hp hp1 ((k+4 : ℕ) : ℝ) (i,()) (j,())).re =
      (actualKernel p hp hp1 k (i,()) (j,())).re := by
  have he := actual_history_four_return p hp hp1 hpos
    (Pi.single (i,()) 1) (Pi.single (j,()) 1) k
  simp only [pairing_single_entry] at he
  exact congrArg Complex.re he

theorem pulseTable_affine (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (t : ℝ) (i j : Fin 2) :
    pulseTable p hp hp1 a ha ha1 t i j =
      a*(actualKernel p hp hp1 t (i,()) (j,())).re + (1-a)*baseline i j := by
  have h1 := pulseTable_law p hp hp1 1 (by norm_num) (by norm_num) t i j
  rw [pulseTable_original] at h1
  rw [pulseTable_law p hp hp1 a ha ha1 t i j, h1]
  dsimp [baseline]
  ring

theorem pulse_entry_order_three (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (i j : Fin 2) (k : ℕ) :
    pulseTable p hp hp1 a ha ha1 ((k+3 : ℕ) : ℝ) i j - pulseTable p hp hp1 a ha ha1 ((k+2 : ℕ) : ℝ) i j +
      pulseTable p hp hp1 a ha ha1 ((k+1 : ℕ) : ℝ) i j - pulseTable p hp hp1 a ha ha1 k i j = 0 := by
  by_cases hpos : 0 < p
  · simp only [pulseTable_affine]
    have he := original_entry_order_three p hp hp1 hpos i j k
    linear_combination a * he
  · have hz : p = 0 := by linarith
    subst p
    simp only [pulseTable_central_reset]
    ring

theorem pulse_entry_four_return (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (i j : Fin 2) (k : ℕ) :
    pulseTable p hp hp1 a ha ha1 ((k+4 : ℕ) : ℝ) i j = pulseTable p hp hp1 a ha ha1 k i j := by
  by_cases hpos : 0 < p
  · simp only [pulseTable_affine, original_entry_four_return p hp hp1 hpos i j k]
  · have hz : p = 0 := by linarith
    subst p
    simp only [pulseTable_central_reset]

theorem pulse_initial_laws (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    BinaryLaw (pulseTable p hp hp1 a ha ha1 0) (p^2*a*N) ∧
      BinaryLaw (pulseTable p hp hp1 a ha ha1 1) (p^2*a*d) ∧
      BinaryLaw (pulseTable p hp hp1 a ha ha1 2) (p^2*a*(d-h)) := by
  simpa only [phaseResponse_zero, phaseResponse_one, phaseResponse_two] using
    And.intro (pulseTable_law p hp hp1 a ha ha1 0)
      (And.intro (pulseTable_law p hp hp1 a ha ha1 1) (pulseTable_law p hp hp1 a ha ha1 2))



/-- Exactly the two equal-label encoded histories, with ordinary 0/1 membership. -/
def recordedEqualEvent : Finset (History (pairedArity 2 1) (1+2)) :=
  {@pairedHistory 2 1 (0,()) (0,()), @pairedHistory 2 1 (1,()) (1,())}

theorem recordedEqualEvent_probability (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (t : ℝ) :
    (∑ v ∈ recordedEqualEvent, weight Q Unit _ (pulseTree p hp hp1 a ha ha1 t) v
      (FiniteAdaptiveKrausRealization.joint rhoN)) = equalLabels (pulseTable p hp hp1 a ha ha1 t) := by
  have hn : @pairedHistory 2 1 (0,()) (0,()) ≠ @pairedHistory 2 1 (1,()) (1,())
      := by
    intro he
    have he' : (((0,()),(0,())) : History 2 1 × History 2 1) = ((1,()),(1,())) :=
      @pairedHistory_injective 2 1 _ _ he
    have hf := congrArg (fun uv : History 2 1 × History 2 1 => uv.1.1) he'
    norm_num at hf
  simp [recordedEqualEvent, hn, equalLabels, pulseTable, pulseKernel, insertedKernel, pulseTree]

theorem arbitrary_event_sum_bound (khat lhat : Table)
    (hk : ProbabilityTable khat) (hl : ProbabilityTable lhat) (A : Finset (Fin 2 × Fin 2)) :
    |∑ x ∈ A, (khat x.1 x.2-lhat x.1 x.2)| ≤ finiteTV khat lhat := by
  have he := event_contraction hk.2 hl.2 A
  rw [eventProbability_sum, eventProbability_sum, ← Finset.sum_sub_distrib] at he
  exact he

/-- Phase isometry gives the same exact directional estimate at every frequency. -/
theorem pulse_retention_residual_any (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (omega : Q → ℝ) (t : ℝ) :
    weightedNorm (Channel.heisenberg (FiniteThreeLevelHistoryTransfer.pulseResetKraus a omega t) centeredF -
      Channel.heisenberg (FiniteThreeLevelHistoryTransfer.pulseResetKraus b omega t) centeredF) =
      |a-b| * Real.sqrt N := by
  rw [FiniteThreeLevelHistoryTransfer.pulseReset_observable a ha ha1,
    FiniteThreeLevelHistoryTransfer.pulseReset_observable b hb hb1,
    centered_Psi, centered_Psi, map_smul, map_smul, ← sub_smul, ← Complex.ofReal_sub]
  change ‖FiniteThreeLevelPositiveHistory.featureLinear (((a-b : ℝ) : ℂ) • rotate omega t centeredF)‖ = _
  rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  change |a-b| * ‖feature (rotate omega t centeredF)‖ = _
  rw [feature_rotate_norm]
  exact congrArg (|a-b| * ·) weightedNorm_F


def errorBudget (p eta epsilon : ℝ) : ℝ := 2*p^2*N*eta+epsilon

theorem errorBudget_nonnegative (p eta epsilon : ℝ) (heta : 0 ≤ eta) (hepsilon : 0 ≤ epsilon) :
    0 ≤ errorBudget p eta epsilon := by
  unfold errorBudget
  have hn := N_pos.le
  positivity

/-- Channel-action error and normalized-table error are independent inputs. -/
theorem observed_budget {m : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (t : ℝ)
    (L : Fin m → MatQ) (hL : IsKrausChannel L) (hstat : krausMap L rhoN = rhoN)
    (hcomm : ∀ A, Channel.heisenberg L (Psi p A) = Psi p (Channel.heisenberg L A))
    (eta : ℝ) (hres : weightedNorm (Channel.heisenberg L centeredF -
      Channel.heisenberg (FiniteThreeLevelHistoryTransfer.pulseResetKraus a leakingFrequencies t)
        centeredF) ≤ eta*Real.sqrt N)
    (khat : Table) (hhat : ProbabilityTable khat) (epsilon : ℝ)
    (hdata : finiteTV khat (channelTable p hp hp1 L hL) ≤ epsilon) :
    |(equalLabels khat-61/72)-2*p^2*a*phaseResponse t| ≤ errorBudget p eta epsilon := by
  have hd := (equalLabels_contraction hhat.2 (channelTable_probability p hp hp1 L hL).2).trans hdata
  have hc := channel_event_bound p hp hp1 L hL hstat hcomm _
    (FiniteThreeLevelHistoryTransfer.pulseReset_normalized a ha ha1 leakingFrequencies t)
    (pulse_stationary a ha ha1 leakingFrequencies t)
    (FiniteThreeLevelHistoryTransfer.pulseReset_commutes a ha ha1 leakingFrequencies t p) eta hres
  have ht := pulseTable_event p hp hp1 a ha ha1 t
  change |equalLabels (channelTable p hp hp1 L hL)-equalLabels (pulseTable p hp hp1 a ha ha1 t)| ≤
    2*p^2*N*eta at hc
  calc
    _ = |(equalLabels khat-equalLabels (channelTable p hp hp1 L hL))+
      (equalLabels (channelTable p hp hp1 L hL)-equalLabels (pulseTable p hp hp1 a ha ha1 t))| := by
      congr 1
      linarith
    _ ≤ |equalLabels khat-equalLabels (channelTable p hp hp1 L hL)|+
      |equalLabels (channelTable p hp hp1 L hL)-equalLabels (pulseTable p hp hp1 a ha ha1 t)| :=
      abs_add_le _ _
    _ ≤ errorBudget p eta epsilon := by dsimp [errorBudget]; linarith

/-- A separately estimated baseline contributes its own TV budget. -/
theorem estimated_baseline_budget (khat bhat : Table) (hbase : ProbabilityTable bhat)
    (epsilon0 target B : ℝ) (hb : finiteTV bhat baseline ≤ epsilon0)
    (hk : |(equalLabels khat-61/72)-target| ≤ B) :
    |(equalLabels khat-equalLabels bhat)-target| ≤ B+epsilon0 := by
  have he := (equalLabels_contraction hbase.2 baseline_probability.2).trans hb
  rw [baseline_equalLabels] at he
  calc
    _ = |((equalLabels khat-61/72)-target)-(equalLabels bhat-61/72)| := by congr 1; ring
    _ ≤ |(equalLabels khat-61/72)-target|+|equalLabels bhat-61/72| := by simpa only [abs_neg, sub_eq_add_neg] using (abs_add_le ((equalLabels khat-61/72)-target) (-(equalLabels bhat-61/72)))
    _ ≤ _ := add_le_add hk he

theorem phase_two_margin (khat : Table) (p a B : ℝ)
    (hb : |(equalLabels khat-61/72)-2*p^2*a*(d-h)| ≤ B)
    (hmargin : B < 2*p^2*a*(h-d)) : equalLabels khat < 61/72 := by
  have hu := (abs_le.mp hb).2
  nlinarith

theorem phase_four_margin (khat : Table) (p a B : ℝ)
    (hb : |(equalLabels khat-61/72)-2*p^2*a*N| ≤ B)
    (hmargin : B < 2*p^2*a*N) : 61/72 < equalLabels khat := by
  have hl := (abs_le.mp hb).1
  linarith

theorem two_phase_revival_margin (khat2 khat4 : Table) (p a B2 B4 : ℝ)
    (h2 : |(equalLabels khat2-61/72)-2*p^2*a*(d-h)| ≤ B2)
    (h4 : |(equalLabels khat4-61/72)-2*p^2*a*N| ≤ B4)
    (hmargin : B2+B4 < 4*p^2*a*h) : equalLabels khat2 < equalLabels khat4 := by
  have hu := (abs_le.mp h2).2
  have hl := (abs_le.mp h4).1
  dsimp [N] at hl
  nlinarith


theorem observed_phase_two {m : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (L : Fin m → MatQ) (hL : IsKrausChannel L) (hstat : krausMap L rhoN = rhoN)
    (hcomm : ∀ A, Channel.heisenberg L (Psi p A) = Psi p (Channel.heisenberg L A))
    (eta : ℝ) (hres : weightedNorm (Channel.heisenberg L centeredF -
      Channel.heisenberg (FiniteThreeLevelHistoryTransfer.pulseResetKraus a leakingFrequencies 2)
        centeredF) ≤ eta*Real.sqrt N)
    (khat : Table) (hhat : ProbabilityTable khat) (epsilon : ℝ)
    (hdata : finiteTV khat (channelTable p hp hp1 L hL) ≤ epsilon)
    (hmargin : errorBudget p eta epsilon < 2*p^2*a*(h-d)) : equalLabels khat < 61/72 := by
  have he := observed_budget p hp hp1 a ha ha1 2 L hL hstat hcomm eta hres khat hhat epsilon hdata
  rw [phaseResponse_two] at he
  exact phase_two_margin khat p a _ he hmargin

theorem observed_phase_four {m : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (L : Fin m → MatQ) (hL : IsKrausChannel L) (hstat : krausMap L rhoN = rhoN)
    (hcomm : ∀ A, Channel.heisenberg L (Psi p A) = Psi p (Channel.heisenberg L A))
    (eta : ℝ) (hres : weightedNorm (Channel.heisenberg L centeredF -
      Channel.heisenberg (FiniteThreeLevelHistoryTransfer.pulseResetKraus a leakingFrequencies 4)
        centeredF) ≤ eta*Real.sqrt N)
    (khat : Table) (hhat : ProbabilityTable khat) (epsilon : ℝ)
    (hdata : finiteTV khat (channelTable p hp hp1 L hL) ≤ epsilon)
    (hmargin : errorBudget p eta epsilon < 2*p^2*a*N) : 61/72 < equalLabels khat := by
  have he := observed_budget p hp hp1 a ha ha1 4 L hL hstat hcomm eta hres khat hhat epsilon hdata
  rw [phaseResponse_four] at he
  exact phase_four_margin khat p a _ he hmargin

theorem observed_two_phase_revival {m n : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (L : Fin m → MatQ) (hL : IsKrausChannel L) (hstatL : krausMap L rhoN = rhoN)
    (hcL : ∀ A, Channel.heisenberg L (Psi p A) = Psi p (Channel.heisenberg L A))
    (M : Fin n → MatQ) (hM : IsKrausChannel M) (hstatM : krausMap M rhoN = rhoN)
    (hcM : ∀ A, Channel.heisenberg M (Psi p A) = Psi p (Channel.heisenberg M A))
    (eta2 eta4 : ℝ)
    (hres2 : weightedNorm (Channel.heisenberg L centeredF -
      Channel.heisenberg (FiniteThreeLevelHistoryTransfer.pulseResetKraus a leakingFrequencies 2)
        centeredF) ≤ eta2*Real.sqrt N)
    (hres4 : weightedNorm (Channel.heisenberg M centeredF -
      Channel.heisenberg (FiniteThreeLevelHistoryTransfer.pulseResetKraus a leakingFrequencies 4)
        centeredF) ≤ eta4*Real.sqrt N)
    (khat2 khat4 : Table) (hhat2 : ProbabilityTable khat2) (hhat4 : ProbabilityTable khat4)
    (epsilon2 epsilon4 : ℝ)
    (hdata2 : finiteTV khat2 (channelTable p hp hp1 L hL) ≤ epsilon2)
    (hdata4 : finiteTV khat4 (channelTable p hp hp1 M hM) ≤ epsilon4)
    (hmargin : errorBudget p eta2 epsilon2+errorBudget p eta4 epsilon4 < 4*p^2*a*h) :
    equalLabels khat2 < equalLabels khat4 := by
  have h2 := observed_budget p hp hp1 a ha ha1 2 L hL hstatL hcL eta2 hres2 khat2 hhat2 epsilon2 hdata2
  have h4 := observed_budget p hp hp1 a ha ha1 4 M hM hstatM hcM eta4 hres4 khat4 hhat4 epsilon4 hdata4
  rw [phaseResponse_two] at h2
  rw [phaseResponse_four] at h4
  exact two_phase_revival_margin khat2 khat4 p a _ _ h2 h4 hmargin


/-- The same two-estimate comparison, allowing an independently estimated baseline. -/
theorem estimated_baseline_signs (khat bhat : Table) (hbase : ProbabilityTable bhat)
    (epsilon0 deficit B : ℝ) (hb : finiteTV bhat baseline ≤ epsilon0)
    (hnegative : |(equalLabels khat-61/72)+deficit| ≤ B)
    (hmargin : B+epsilon0 < deficit) : equalLabels khat < equalLabels bhat := by
  have he := estimated_baseline_budget khat bhat hbase epsilon0 (-deficit) B hb (by simpa using hnegative)
  have hu := (abs_le.mp he).2
  linarith

theorem estimated_baseline_positive (khat bhat : Table) (hbase : ProbabilityTable bhat)
    (epsilon0 excess B : ℝ) (hb : finiteTV bhat baseline ≤ epsilon0)
    (hpositive : |(equalLabels khat-61/72)-excess| ≤ B)
    (hmargin : B+epsilon0 < excess) : equalLabels bhat < equalLabels khat := by
  have he := estimated_baseline_budget khat bhat hbase epsilon0 excess B hb hpositive
  have hl := (abs_le.mp he).1
  linarith

theorem exact_phase_two_signal (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    equalLabels (pulseTable p hp.le hp1 a ha.le ha1 2)-61/72 = -2*p^2*a*(h-d) ∧
      equalLabels (pulseTable p hp.le hp1 a ha.le ha1 2) < 61/72 := by
  have he := pulseTable_event p hp.le hp1 a ha.le ha1 2
  rw [phaseResponse_two] at he
  have hm : 0 < 2*p^2*a*(h-d) := mul_pos (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hp)) ha)
    (sub_pos.mpr d_lt_h)
  constructor <;> nlinarith

theorem exact_phase_four_signal (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    equalLabels (pulseTable p hp.le hp1 a ha.le ha1 4)-61/72 = 2*p^2*a*N ∧
      61/72 < equalLabels (pulseTable p hp.le hp1 a ha.le ha1 4) := by
  have he := pulseTable_event p hp.le hp1 a ha.le ha1 4
  rw [phaseResponse_four] at he
  have hm : 0 < 2*p^2*a*N := mul_pos (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hp)) ha) N_pos
  exact ⟨he, by linarith⟩

theorem exact_revival_signal (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    equalLabels (pulseTable p hp.le hp1 a ha.le ha1 4)-
      equalLabels (pulseTable p hp.le hp1 a ha.le ha1 2) = 4*p^2*a*h ∧
      equalLabels (pulseTable p hp.le hp1 a ha.le ha1 2) <
        equalLabels (pulseTable p hp.le hp1 a ha.le ha1 4) := by
  have h2 := (exact_phase_two_signal p hp hp1 a ha ha1).1
  have h4 := (exact_phase_four_signal p hp hp1 a ha ha1).1
  have hm : 0 < 4*p^2*a*h := mul_pos (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hp)) ha) h_pos
  dsimp [N] at h4
  constructor <;> nlinarith

def dataEpsilon : ℝ := (h-d)/8

theorem dataEpsilon_positive : 0 < dataEpsilon := div_pos (sub_pos.mpr d_lt_h) (by norm_num)

theorem actual_nonzero_residual (t : ℝ) :
    weightedNorm (Channel.heisenberg
      (FiniteThreeLevelHistoryTransfer.pulseResetKraus (3/4) leakingFrequencies t) centeredF -
      Channel.heisenberg (FiniteThreeLevelHistoryTransfer.pulseResetKraus 1 leakingFrequencies t)
        centeredF) = (1/4)*Real.sqrt N := by
  rw [pulse_retention_residual (3/4) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

theorem actual_residual_positive (t : ℝ) :
    0 < weightedNorm (Channel.heisenberg
      (FiniteThreeLevelHistoryTransfer.pulseResetKraus (3/4) leakingFrequencies t) centeredF -
      Channel.heisenberg (FiniteThreeLevelHistoryTransfer.pulseResetKraus 1 leakingFrequencies t)
        centeredF) := by
  rw [actual_nonzero_residual]
  exact mul_pos (by norm_num) (Real.sqrt_pos.mpr N_pos)

theorem fixed_budget_value : errorBudget (1/2) (1/4) dataEpsilon = h/4 := by
  dsimp [errorBudget, dataEpsilon, N]
  ring


theorem fixed_negative_margin_value :
    (h-d)/2-errorBudget (1/2) (1/4) dataEpsilon = (h-2*d)/4 := by
  rw [fixed_budget_value]
  ring

theorem fixed_positive_margin_value :
    N/2-errorBudget (1/2) (1/4) dataEpsilon = d/2+h/4 := by
  rw [fixed_budget_value]
  dsimp [N]
  ring


/-- Nonzero physical retention perturbation and a positive allowed data error. -/
theorem fixed_observed_budget (t : ℝ) (khat : Table) (hhat : ProbabilityTable khat)
    (hdata : finiteTV khat
      (pulseTable (1/2) (by norm_num) (by norm_num) (3/4) (by norm_num) (by norm_num) t) ≤ dataEpsilon) :
    |(equalLabels khat-61/72)-(1/2)*phaseResponse t| ≤ h/4 := by
  have he := observed_budget (1/2) (by norm_num) (by norm_num) 1 (by norm_num) (by norm_num) t
    (FiniteThreeLevelHistoryTransfer.pulseResetKraus (3/4) leakingFrequencies t)
    (FiniteThreeLevelHistoryTransfer.pulseReset_normalized (3/4) (by norm_num) (by norm_num) leakingFrequencies t)
    (pulse_stationary (3/4) (by norm_num) (by norm_num) leakingFrequencies t)
    (FiniteThreeLevelHistoryTransfer.pulseReset_commutes (3/4) (by norm_num) (by norm_num) leakingFrequencies t (1/2))
    (1/4) (le_of_eq (actual_nonzero_residual t)) khat hhat dataEpsilon hdata
  rw [fixed_budget_value] at he
  norm_num at he
  exact he

theorem fixed_negative_consumer (khat : Table) (hhat : ProbabilityTable khat)
    (hdata : finiteTV khat
      (pulseTable (1/2) (by norm_num) (by norm_num) (3/4) (by norm_num) (by norm_num) 2) ≤ dataEpsilon) :
    equalLabels khat < 61/72 := by
  have he := fixed_observed_budget 2 khat hhat hdata
  rw [phaseResponse_two] at he
  have hu := (abs_le.mp he).2
  nlinarith [h_gt_twice_d]

theorem fixed_positive_consumer (khat : Table) (hhat : ProbabilityTable khat)
    (hdata : finiteTV khat
      (pulseTable (1/2) (by norm_num) (by norm_num) (3/4) (by norm_num) (by norm_num) 4) ≤ dataEpsilon) :
    61/72 < equalLabels khat := by
  have he := fixed_observed_budget 4 khat hhat hdata
  rw [phaseResponse_four] at he
  have hl := (abs_le.mp he).1
  dsimp [N] at hl
  nlinarith [d_pos, h_pos]

theorem fixed_revival_consumer (khat2 khat4 : Table)
    (hhat2 : ProbabilityTable khat2) (hhat4 : ProbabilityTable khat4)
    (hdata2 : finiteTV khat2
      (pulseTable (1/2) (by norm_num) (by norm_num) (3/4) (by norm_num) (by norm_num) 2) ≤ dataEpsilon)
    (hdata4 : finiteTV khat4
      (pulseTable (1/2) (by norm_num) (by norm_num) (3/4) (by norm_num) (by norm_num) 4) ≤ dataEpsilon) :
    equalLabels khat2 < equalLabels khat4 := by
  exact (fixed_negative_consumer khat2 hhat2 hdata2).trans
    (fixed_positive_consumer khat4 hhat4 hdata4)


/-- A concrete changed data table: the same actual pulse with retention one half. -/
def noisyPhaseTwo : Table :=
  pulseTable (1/2) (by norm_num) (by norm_num) (1/2) (by norm_num) (by norm_num) 2

theorem noisyPhaseTwo_probability : ProbabilityTable noisyPhaseTwo :=
  pulseTable_probability (1/2) (by norm_num) (by norm_num) (1/2) (by norm_num) (by norm_num) 2

theorem noisyPhaseTwo_error : finiteTV noisyPhaseTwo
    (pulseTable (1/2) (by norm_num) (by norm_num) (3/4) (by norm_num) (by norm_num) 2) = dataEpsilon := by
  unfold noisyPhaseTwo
  rw [pulse_retention_TV, phaseResponse_two, abs_of_neg (sub_neg.mpr d_lt_h)]
  norm_num [dataEpsilon]
  ring

def observedRetention4 : ℝ := 3/4-(h-d)/(4*N)

theorem observedRetention4_bounds : 1/2 < observedRetention4 ∧ observedRetention4 < 3/4 := by
  have h4N : 0 < 4*N := mul_pos (by norm_num) N_pos
  have hr : 0 < (h-d)/(4*N) := div_pos (sub_pos.mpr d_lt_h) h4N
  have hl : (h-d)/(4*N) < 1/4 := (div_lt_iff₀ h4N).2 (by dsimp [N]; linarith [d_pos])
  dsimp [observedRetention4]
  constructor <;> linarith

/-- A second changed normalized physical table exhausts the same positive data budget. -/
def noisyPhaseFour : Table := pulseTable (1/2) (by norm_num) (by norm_num)
  observedRetention4 (by linarith [observedRetention4_bounds.1])
    (by linarith [observedRetention4_bounds.2]) 4

theorem noisyPhaseFour_probability : ProbabilityTable noisyPhaseFour :=
  pulseTable_probability (1/2) (by norm_num) (by norm_num) observedRetention4
    (by linarith [observedRetention4_bounds.1]) (by linarith [observedRetention4_bounds.2]) 4

theorem noisyPhaseFour_error : finiteTV noisyPhaseFour
    (pulseTable (1/2) (by norm_num) (by norm_num) (3/4) (by norm_num) (by norm_num) 4) = dataEpsilon := by
  unfold noisyPhaseFour
  rw [pulse_retention_TV, phaseResponse_four, abs_of_nonneg N_pos.le,
    abs_of_neg (sub_neg.mpr observedRetention4_bounds.2)]
  norm_num
  dsimp [observedRetention4, dataEpsilon]
  field_simp [ne_of_gt N_pos]
  ring

theorem noisyPhaseTwo_nonzero_error : 0 < finiteTV noisyPhaseTwo
    (pulseTable (1/2) (by norm_num) (by norm_num) (3/4) (by norm_num) (by norm_num) 2) := by
  rw [noisyPhaseTwo_error]
  exact dataEpsilon_positive

theorem noisyPhaseFour_nonzero_error : 0 < finiteTV noisyPhaseFour
    (pulseTable (1/2) (by norm_num) (by norm_num) (3/4) (by norm_num) (by norm_num) 4) := by
  rw [noisyPhaseFour_error]
  exact dataEpsilon_positive

theorem noisyPhaseTwo_below_baseline : equalLabels noisyPhaseTwo < 61/72 :=
  fixed_negative_consumer noisyPhaseTwo noisyPhaseTwo_probability noisyPhaseTwo_error.le

theorem noisyPhaseFour_above_baseline : 61/72 < equalLabels noisyPhaseFour :=
  fixed_positive_consumer noisyPhaseFour noisyPhaseFour_probability noisyPhaseFour_error.le

theorem noisyPhase_revival : equalLabels noisyPhaseTwo < equalLabels noisyPhaseFour :=
  fixed_revival_consumer noisyPhaseTwo noisyPhaseFour noisyPhaseTwo_probability noisyPhaseFour_probability
    noisyPhaseTwo_error.le noisyPhaseFour_error.le

theorem complete_reset_event_zero (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) :
    equalLabels (pulseTable p hp hp1 0 (by norm_num) (by norm_num) t)-61/72 = 0 := by
  rw [pulseTable_complete_reset, baseline_equalLabels, sub_self]

theorem central_reset_event_zero (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (t : ℝ) :
    equalLabels (pulseTable 0 (by norm_num) (by norm_num) a ha ha1 t)-61/72 = 0 := by
  rw [pulseTable_central_reset, baseline_equalLabels, sub_self]

theorem pulse_four_zero_table (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    pulseTable p hp hp1 a ha ha1 4 = pulseTable p hp hp1 a ha ha1 0 := by
  funext i j
  simpa only [Nat.zero_add, Nat.cast_ofNat, Nat.cast_zero] using
    pulse_entry_four_return p hp hp1 a ha ha1 i j 0



theorem original_central_reset (t : ℝ) (i j : Fin 2) :
    (actualKernel 0 (by norm_num) (by norm_num) t (i,()) (j,())).re = baseline i j := by
  rw [← pulseTable_original 0 (by norm_num) (by norm_num) t i j, pulseTable_central_reset]

theorem constant_frequency_rotate (w t : ℝ) (A : MatQ) : rotate (fun _ => w) t A = A := by
  ext i j
  simp [FiniteThreeLevelHistoryTransfer.rotate_entry]

theorem constant_frequency_no_contrast (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (w t s : ℝ) :
    pulseKernel binaryTree p (by decide) binary_stationary hp hp1 a ha ha1 (fun _ => w) t =
      pulseKernel binaryTree p (by decide) binary_stationary hp hp1 a ha ha1 (fun _ => w) s := by
  funext u v
  rw [pulseKernel_form, pulseKernel_form, constant_frequency_rotate, constant_frequency_rotate]

theorem constant_frequency_entry (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (w t : ℝ) (i j : Fin 2) :
    (pulseKernel binaryTree p (by decide) binary_stationary hp hp1 a ha ha1 (fun _ => w) t
      (i,()) (j,())).re = pulseTable p hp hp1 a ha ha1 0 i j := by
  unfold pulseTable
  rw [pulseKernel_form, pulseKernel_form, constant_frequency_rotate, FiniteThreeLevelHistoryTransfer.rotate_zero]

theorem constant_frequency_event (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (w t : ℝ) :
    (pulseKernel binaryTree p (by decide) binary_stationary hp hp1 a ha ha1 (fun _ => w) t
      (0,()) (0,())).re +
    (pulseKernel binaryTree p (by decide) binary_stationary hp hp1 a ha ha1 (fun _ => w) t
      (1,()) (1,())).re -61/72 = 2*p^2*a*N := by
  rw [constant_frequency_entry, constant_frequency_entry]
  have he := pulseTable_event p hp hp1 a ha ha1 0
  rwa [phaseResponse_zero] at he


/-- The baseline is itself the actual normalized additional complete-reset experiment. -/
theorem noise_ball_erasure (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (t epsilon : ℝ)
    (hnoise : 2*|p^2*a*phaseResponse t| ≤ epsilon) :
    ∃ khat : Table,
      khat = pulseTable p hp hp1 0 (by norm_num) (by norm_num) t ∧
      ProbabilityTable khat ∧ finiteTV khat (pulseTable p hp hp1 a ha ha1 t) ≤ epsilon ∧
      equalLabels khat = 61/72 := by
  refine ⟨pulseTable p hp hp1 0 (by norm_num) (by norm_num) t, rfl,
    pulseTable_probability p hp hp1 0 (by norm_num) (by norm_num) t, ?_, ?_⟩
  · rw [pulseTable_complete_reset, law_finiteTV baseline_law (pulseTable_law p hp hp1 a ha ha1 t)]
    simpa only [zero_sub, abs_neg] using hnoise
  · rw [pulseTable_complete_reset, baseline_equalLabels]

theorem baseline_ball_refutes_uniform_sign (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (t epsilon : ℝ)
    (hnoise : 2*|p^2*a*phaseResponse t| ≤ epsilon) :
    ¬(∀ khat : Table, ProbabilityTable khat →
      finiteTV khat (pulseTable p hp hp1 a ha ha1 t) ≤ epsilon → equalLabels khat ≠ 61/72) := by
  intro hall
  obtain ⟨khat, _, hk, hd, hz⟩ := noise_ball_erasure p hp hp1 a ha ha1 t epsilon hnoise
  exact hall khat hk hd hz

theorem ordinary_event_probability (khat : Table) (hk : ProbabilityTable khat) :
    0 ≤ equalLabels khat ∧ equalLabels khat ≤ 1 := by
  have hn := hk.2
  simp only [Fin.sum_univ_two] at hn
  constructor
  · exact add_nonneg (hk.1 0 0) (hk.1 1 1)
  · dsimp [equalLabels]
    linarith [hk.1 0 1, hk.1 1 0]

/-- The ordinary event remains a probability while the old signed diagnostic is negative. -/
theorem ordinary_and_signed_distinct (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    (0 ≤ equalLabels (pulseTable p hp.le hp1 1 (by norm_num) (by norm_num) 2) ∧
      equalLabels (pulseTable p hp.le hp1 1 (by norm_num) (by norm_num) 2) ≤ 1) ∧
      (signedCoefficients p (1,())).re < 0 ∧
      (FinitePositiveKernel.pairing (actualKernel p hp.le hp1 2)
        (signedCoefficients p) (signedCoefficients p)).re < 0 := by
  exact ⟨ordinary_event_probability _ (pulseTable_probability p hp.le hp1 1 (by norm_num) (by norm_num) 2),
    signed_coefficient_negative p hp, actual_signed_two_negative p hp.le hp1 hp⟩

/-- Retain both independent obstructions; the event does not realize the projection. -/
theorem projection_and_compression_guards (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    ¬PosSemidef (projection binaryTree p (FiniteThreeLevelPositiveHistory.D 2)) ∧
      compression binaryTree p (by decide) binary_stationary hp.le hp1 (rotate leakingFrequencies 2) ≠
        (compression binaryTree p (by decide) binary_stationary hp.le hp1 (rotate leakingFrequencies 1)).comp
          (compression binaryTree p (by decide) binary_stationary hp.le hp1 (rotate leakingFrequencies 1)) := by
  exact ⟨(projection_not_positive p hp).2, quotient_not_semigroup p hp.le hp1 hp⟩


end SKEFTHawking.QuantumNetwork.FiniteThreeLevelCompressedMemoryObservabilityExamples
