import SKEFTHawking.QuantumNetwork.FiniteThreeLevelStationaryStrategyTransfer
import SKEFTHawking.QuantumNetwork.FiniteThreeLevelStationaryStrategyExamples

/-! Actual strategy consumers for exact observable transfer. -/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteThreeLevelStationaryStrategyTransferExamples
open FiniteInterventionProcess FiniteThreeLevelStationaryStrategyReflection
open FiniteThreeLevelStationaryStrategyTransfer FiniteThreeLevelStationaryStrategyExamples
open FiniteThreeLevelPositiveHistory (Q MatQ rhoN)
open Matrix
open scoped BigOperators ComplexOrder

/-- Every normalized prefix-dependent continuation and every finite depth are
included; positive retention makes the actual effect span full. -/
theorem adaptiveFamily_invariant {k : ℕ} (U : Fin 15 → Tree Q Unit 15 k)
    (p : ℝ) (hp : 0 < p) (O : MatQ →ₗ[ℂ] MatQ) :
    Invariant (adaptiveFamily U) p O := by
  intro A _
  rw [range_positive_eq_effect_span _ _ hp, adaptiveFamily_full_span]
  exact Submodule.mem_top

theorem computational_phase_fixed (p : ℝ) (hp : 0 < p) (ω : Q → ℝ) (t : ℝ)
    (A : MatQ) (hA : A ∈ accessible computationalTree p) :
    FiniteThreeLevelHistoryTransfer.rotate ω t A = A := by
  rw [computational_range p hp] at hA
  obtain ⟨d, rfl⟩ := hA
  exact FiniteThreeLevelHistoryTransfer.rotate_diagonal ω t d

/-- Label three versus all other labels, with every original Kraus operator retained. -/
def binaryLabel (j : Fin 15) : Fin 2 := if j = 3 then 0 else 1

def maskedKraus (a : Fin 2) (j : Fin 15) : MatQ :=
  if binaryLabel j = a then FiniteThreeLevelPositiveHistory.L j else 0

theorem masked_complete :
    (∑ a, ∑ j, (maskedKraus a j)ᴴ * maskedKraus a j) = 1 := by
  rw [Finset.sum_comm]
  simp only [maskedKraus, apply_ite Matrix.conjTranspose, Matrix.conjTranspose_zero,
    ite_mul, mul_ite, zero_mul, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true,
    FiniteThreeLevelPositiveHistory.L_effect]
  exact FiniteThreeLevelPositiveHistory.effect_sum

def binaryInstrument : FiniteInstrument Q 2 where
  count := 15
  operators := maskedKraus
  normalized := masked_complete

theorem binaryInstrument_branch (a : Fin 2) (X : MatQ) :
    binaryInstrument.branch a X =
      ∑ j, if binaryLabel j = a then FiniteThreeLevelPositiveHistory.instrument.branch j X else 0 := by
  simp_rw [FiniteThreeLevelPositiveHistory.instrument_branch]
  simp only [FiniteInstrument.branch, binaryInstrument, krausMap, maskedKraus]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

theorem binary_aggregate (X : MatQ) :
    (∑ a, binaryInstrument.branch a X) =
      ∑ j, FiniteThreeLevelPositiveHistory.instrument.branch j X := by
  simp_rw [binaryInstrument_branch]
  rw [Finset.sum_comm]
  simp

def binaryTree : Tree Q Unit 2 1 :=
  .node (localStep Q Unit 2 binaryInstrument) (fun _ => .done)

theorem binary_branch (a : Fin 2) (X : MatQ) :
    branch binaryTree (a,()) X = binaryInstrument.branch a X := by
  unfold branch binaryTree
  rw [run, run, localStep_joint, FiniteAdaptiveKrausRealization.unJoint_joint]

theorem binary_stationary : Stationary binaryTree := by
  change (∑ h : Fin 2 × Unit, branch binaryTree h rhoN) = rhoN
  simp only [Fintype.sum_prod_type, Fintype.sum_unique]
  change (∑ a, branch binaryTree (a,()) rhoN) = rhoN
  simp_rw [binary_branch]
  rw [binary_aggregate, FiniteThreeLevelPositiveHistory.instrument_stationary]

def binaryEffect : MatQ := FiniteThreeLevelPositiveHistory.effect 3

theorem binaryEffect_formula : binaryEffect = (1/10 : ℂ) •
    (FiniteThreeLevelPositiveHistory.D 0 + FiniteThreeLevelPositiveHistory.D 1 +
      FiniteThreeLevelPositiveHistory.X 0 1) := by
  change (1/5 : ℂ) • !![1/2,1/2,0;1/2,1/2,0;0,0,0] = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [FiniteThreeLevelPositiveHistory.D,
      FiniteThreeLevelPositiveHistory.E, FiniteThreeLevelPositiveHistory.X, Matrix.single]

theorem binary_effect_zero : effect binaryTree (0,()) = binaryEffect := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  rw [← branch_trace, binary_branch, binaryInstrument_branch]
  simp only [binaryLabel]
  have hh (j : Fin 15) : (if j = 3 then (0 : Fin 2) else 1) = 0 ↔ j = 3 := by
    by_cases hj : j = 3 <;> simp [hj]
  simp_rw [hh]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact FiniteThreeLevelPositiveHistory.branch_trace 3 X

theorem binary_effect_one : effect binaryTree (1,()) = 1 - binaryEffect := by
  have hs := effect_sum binaryTree
  change (∑ h : Fin 2 × Unit, effect binaryTree h) = 1 at hs
  simp only [Fintype.sum_prod_type, Fintype.sum_unique, Fin.sum_univ_two] at hs
  change effect binaryTree (0,()) + effect binaryTree (1,()) = 1 at hs
  rw [binary_effect_zero] at hs
  exact eq_sub_of_add_eq' hs

def binarySpan : Submodule ℂ MatQ := Submodule.span ℂ {(1 : MatQ), binaryEffect}

theorem binary_effectSpan : effectSpan binaryTree = binarySpan := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro A ⟨⟨a,u⟩, rfl⟩
    cases u
    fin_cases a
    · change effect binaryTree (0,()) ∈ binarySpan
      rw [binary_effect_zero]
      exact Submodule.subset_span (by simp)
    · change effect binaryTree (1,()) ∈ binarySpan
      rw [binary_effect_one]
      exact Submodule.sub_mem _ (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
  · apply Submodule.span_le.mpr
    intro A hA
    rcases Set.mem_insert_iff.mp hA with h | h
    · subst A
      rw [← accessible_one]
      exact one_mem_accessible binaryTree 1
    · have he : A = binaryEffect := Set.mem_singleton_iff.mp h
      subst A
      rw [← binary_effect_zero]
      exact Submodule.subset_span ⟨(0,()),rfl⟩

theorem binary_accessible (p : ℝ) (hp : 0 < p) : accessible binaryTree p = binarySpan := by
  rw [range_positive_eq_effect_span _ _ hp, binary_effectSpan]

theorem binarySpan_rank : Module.finrank ℂ binarySpan = 2 := by
  have hi : LinearIndependent ℂ (![1, binaryEffect] : Fin 2 → MatQ) := by
    rw [linearIndependent_fin2]
    constructor
    · intro he
      have h := congrArg (fun A : MatQ => A 0 1) he
      change binaryEffect 0 1 = 0 at h
      rw [binaryEffect_formula] at h
      norm_num [FiniteThreeLevelPositiveHistory.D, FiniteThreeLevelPositiveHistory.E,
        FiniteThreeLevelPositiveHistory.X, Matrix.single] at h
    · intro c he
      have h := congrArg (fun A : MatQ => A 2 2) he
      change (c • binaryEffect) 2 2 = 1 at h
      have h22 : binaryEffect 2 2 = 0 := by
        change (1/5 : ℂ) * 0 = 0
        exact mul_zero _
      change c * binaryEffect 2 2 = 1 at h
      rw [h22, mul_zero] at h
      exact zero_ne_one h
  have hr := finrank_span_eq_card hi
  have he : Set.range (![1, binaryEffect] : Fin 2 → MatQ) = {(1 : MatQ), binaryEffect} := by
    ext A
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro h
      rcases Set.mem_insert_iff.mp h with h | h
      · exact ⟨0, h.symm⟩
      · exact ⟨1, (Set.mem_singleton_iff.mp h).symm⟩
  rw [he] at hr
  exact hr

theorem binary_rank (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p) :
    Module.finrank ℂ (Reconstructed binaryTree (by norm_num) binary_stationary p hp hp1) = 2 := by
  rw [reconstructed_finrank, binary_accessible p hpos, binarySpan_rank]

theorem binary_equal_entries (A : MatQ) (hA : A ∈ binarySpan) : A 0 1 = A 1 0 := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    rcases Set.mem_insert_iff.mp hA with h | h
    · subst A; norm_num
    · rw [Set.mem_singleton_iff.mp h, binaryEffect_formula]
      norm_num [FiniteThreeLevelPositiveHistory.D, FiniteThreeLevelPositiveHistory.E,
        FiniteThreeLevelPositiveHistory.X, Matrix.single]
  | zero => rfl
  | add A B _ _ hA hB => exact congrArg₂ (· + ·) hA hB
  | smul c A _ hA => exact congrArg (c * ·) hA

def leakingFrequencies : Q → ℝ := ![0, Real.pi/2, 0]

theorem binary_rotated_zero_one :
    FiniteThreeLevelHistoryTransfer.rotate leakingFrequencies 1 binaryEffect 0 1 = -Complex.I/10 := by
  rw [FiniteThreeLevelHistoryTransfer.rotate_entry, binaryEffect_formula]
  simp only [Complex.ofReal_one]
  have he : Complex.I * (1 : ℂ) *
      ((leakingFrequencies 0 : ℂ) - leakingFrequencies 1) =
      ((-(Real.pi/2) : ℝ) : ℂ) * Complex.I := by
    simp [leakingFrequencies]; ring
  rw [he, Complex.exp_ofReal_mul_I]
  norm_num [Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two,
    FiniteThreeLevelPositiveHistory.D, FiniteThreeLevelPositiveHistory.E,
    FiniteThreeLevelPositiveHistory.X, Matrix.single]
  ring

theorem binary_rotated_one_zero :
    FiniteThreeLevelHistoryTransfer.rotate leakingFrequencies 1 binaryEffect 1 0 = Complex.I/10 := by
  rw [FiniteThreeLevelHistoryTransfer.rotate_entry, binaryEffect_formula]
  simp only [Complex.ofReal_one]
  have he : Complex.I * (1 : ℂ) *
      ((leakingFrequencies 1 : ℂ) - leakingFrequencies 0) =
      ((Real.pi/2 : ℝ) : ℂ) * Complex.I := by
    simp [leakingFrequencies]; ring
  rw [he, Complex.exp_ofReal_mul_I]
  norm_num [Real.cos_pi_div_two, Real.sin_pi_div_two, FiniteThreeLevelPositiveHistory.D,
    FiniteThreeLevelPositiveHistory.E, FiniteThreeLevelPositiveHistory.X, Matrix.single]
  ring

theorem binary_not_invariant (p : ℝ) (hp : 0 < p) :
    ¬ Invariant binaryTree p (FiniteThreeLevelHistoryTransfer.rotate leakingFrequencies 1) := by
  intro h
  have hm : binaryEffect ∈ accessible binaryTree p := by
    rw [binary_accessible p hp]
    exact Submodule.subset_span (by simp)
  have he := h binaryEffect hm
  rw [binary_accessible p hp] at he
  have hc := binary_equal_entries _ he
  rw [binary_rotated_zero_one, binary_rotated_one_zero] at hc
  have hi := congrArg Complex.im hc
  norm_num at hi

theorem binary_no_exact_lift (p : ℝ) (hp : 0 < p) :
    ¬ ∃ C, ExactLift binaryTree p (FiniteThreeLevelHistoryTransfer.rotate leakingFrequencies 1) C := by
  rw [← invariant_iff_exists_exactLift]
  exact binary_not_invariant p hp

theorem binary_no_coordinate_intertwiner (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hpos : 0 < p) :
    ¬ ∃ F : Reconstructed binaryTree (by norm_num) binary_stationary p hp hp1 →ₗ[ℂ]
        Reconstructed binaryTree (by norm_num) binary_stationary p hp hp1,
      ∀ z, coordinates binaryTree (by norm_num) binary_stationary p hp hp1 (F z) =
        FiniteThreeLevelHistoryTransfer.rotate leakingFrequencies 1
          (coordinates binaryTree (by norm_num) binary_stationary p hp hp1 z) := by
  rintro ⟨F,hF⟩
  exact binary_not_invariant p hpos
    (invariant_of_coordinates binaryTree p (by norm_num) binary_stationary hp hp1 F hF)

theorem binary_reset_phase_invariant (ω : Q → ℝ) (t : ℝ) :
    Invariant binaryTree 0 (FiniteThreeLevelHistoryTransfer.rotate ω t) :=
  reset_range_invariant binaryTree _ (FiniteThreeLevelHistoryTransfer.rotate_one ω t)

theorem binary_inserted_normalized (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (∑ h, weight Q Unit _ (insertedTree binaryTree p (by norm_num) binary_stationary hp hp1
      (FiniteThreeLevelHistoryTransfer.pulseKraus leakingFrequencies 1)
      (FiniteThreeLevelHistoryTransfer.pulse_normalized leakingFrequencies 1)) h
        (FiniteAdaptiveKrausRealization.joint rhoN)) = 1 :=
  (inserted_probabilities binaryTree p (by norm_num) binary_stationary hp hp1 _ _).2

theorem binary_inserted_form (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (u v : History 2 1) :
    insertedKernel binaryTree p (by norm_num) binary_stationary hp hp1
      (FiniteThreeLevelHistoryTransfer.pulseKraus leakingFrequencies 1)
      (FiniteThreeLevelHistoryTransfer.pulse_normalized leakingFrequencies 1) u v =
    FiniteThreeLevelPositiveHistory.form (FiniteThreeLevelPositiveHistory.Psi p (effect binaryTree u))
      (FiniteThreeLevelHistoryTransfer.rotate leakingFrequencies 1
        (FiniteThreeLevelPositiveHistory.Psi p (effect binaryTree v))) := by
  rw [insertedKernel_form binaryTree p (by norm_num) binary_stationary hp hp1 _ _ (by
    intro A
    simp only [FiniteThreeLevelHistoryTransfer.pulse_observable,
      FiniteThreeLevelHistoryTransfer.rotate_Psi]), FiniteThreeLevelHistoryTransfer.pulse_observable]

theorem computational_phase_invariant (p : ℝ) (hp : 0 < p) (ω : Q → ℝ) (t : ℝ) :
    Invariant computationalTree p (FiniteThreeLevelHistoryTransfer.rotate ω t) := by
  intro A hA
  rw [computational_phase_fixed p hp ω t A hA]
  exact hA

theorem computational_pulse_positive (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ω : Q → ℝ) (t : ℝ) :
    (pulseKernel computationalTree p (by norm_num) computational_stationary hp hp1
      a ha ha1 ω t).PosSemidef :=
  pulseKernel_positive_of_fixed computationalTree p (by norm_num) computational_stationary hp hp1
    a ha ha1 ω t (computational_phase_fixed p hpos ω t)

theorem computational_thermal_positive (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p)
    (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) :
    (thermalKernel computationalTree p (by norm_num) computational_stationary hp hp1
      b ℏ γ t hγ ht).PosSemidef := by
  rw [thermalKernel_eq_pulse]
  exact computational_pulse_positive p hp hp1 hpos _ _ _ _ _

theorem done_no_center (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (z : Reconstructed (Tree.done : Tree Q Unit 1 0) (Nat.zero_lt_succ 0) done_stationary p hp hp1) :
    z - resetTransfer (Tree.done : Tree Q Unit 1 0) p (Nat.zero_lt_succ 0) done_stationary hp hp1 0 z = 0 := by
  apply rank_one_no_center
  rw [← reconstructed_finrank _ (by decide) done_stationary p hp hp1]
  exact done_rank p hp hp1

open scoped InnerProductSpace in
theorem familyCoeff_pulse_pairing {k : ℕ} (U : Fin 15 → Tree Q Unit 15 k)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ω : Q → ℝ) (t : ℝ) (A B : MatQ) :
    FinitePositiveKernel.pairing (pulseKernel (adaptiveFamily U) p (by norm_num)
      (adaptiveFamily_stationary U) hp hp1 a ha ha1 ω t) (familyCoeff U p A) (familyCoeff U p B) =
    FiniteThreeLevelPositiveHistory.form A
      (FiniteThreeLevelHistoryTransfer.rotate ω t (FiniteThreeLevelPositiveHistory.Psi a B)) := by
  rw [pulseKernel_pairing]
  rw [show synthesis (adaptiveFamily U) p (familyCoeff U p A) = A from
    adaptiveFamily_synthesis U p hpos A,
    show synthesis (adaptiveFamily U) p (familyCoeff U p B) = B from
    adaptiveFamily_synthesis U p hpos B]

theorem familyCoeff_pulse_coordinates {k : ℕ} (U : Fin 15 → Tree Q Unit 15 k)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p)
    (a : ℝ) (ω : Q → ℝ) (t : ℝ) (A : MatQ) :
    coordinates (adaptiveFamily U) (by norm_num) (adaptiveFamily_stationary U) p hp hp1
      (pulseTransfer (adaptiveFamily U) p (by norm_num) (adaptiveFamily_stationary U) hp hp1 ω
        (fun s => adaptiveFamily_invariant U p hpos (FiniteThreeLevelHistoryTransfer.rotate ω s)) a t
        (FinitePositiveKernel.mk _ _ (familyCoeff U p A))) =
    FiniteThreeLevelHistoryTransfer.rotate ω t (FiniteThreeLevelPositiveHistory.Psi a A) := by
  rw [pulse_coordinates, coordinates_mk]
  rw [show synthesis (adaptiveFamily U) p (familyCoeff U p A) = A from
    adaptiveFamily_synthesis U p hpos A]

def fixtureHistoryEquiv : History 15 2 ≃ FiniteThreeLevelPositiveHistory.HalfHistory where
  toFun h := (h.1,h.2.1)
  invFun h := (h.1,h.2,())
  left_inv h := by rcases h with ⟨a,b,u⟩; cases u; rfl
  right_inv h := by rcases h with ⟨a,b⟩; rfl

def fixtureRecode : (FiniteThreeLevelPositiveHistory.HalfHistory → ℂ) →ₗ[ℂ] (History 15 2 → ℂ) where
  toFun f h := f (fixtureHistoryEquiv h)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem fixture_synthesis_relabel (p r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (f : FiniteThreeLevelPositiveHistory.HalfHistory → ℂ) :
    synthesis (FiniteThreeLevelPositiveHistory.negativeTree r hr hr1) p (fixtureRecode f) =
      FiniteThreeLevelPositiveHistory.synthesis p r f := by
  unfold synthesis
  change (∑ h : Fin 15 × Fin 15 × Unit,
    f (h.1,h.2.1) • FiniteThreeLevelPositiveHistory.Psi p
      (effect (FiniteThreeLevelPositiveHistory.negativeTree r hr hr1) h)) = _
  simp only [Fintype.sum_prod_type, Fintype.sum_unique]
  simp only [show (default : Unit) = () from rfl]
  simp only [FiniteThreeLevelPositiveHistory.synthesis, Fintype.sum_prod_type,
    FiniteThreeLevelPositiveHistory.midpoint]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  exact congrArg (fun A => f (a,b) • FiniteThreeLevelPositiveHistory.Psi p A)
    (fixture_effect r hr hr1 a b)

theorem fixture_inserted_kernel {m : ℕ} (L : Fin m → MatQ) (hL : IsKrausChannel L)
    (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (u v : History 15 2) :
    insertedKernel (FiniteThreeLevelPositiveHistory.negativeTree r hr hr1) p (by norm_num)
      (fixture_stationary r hr hr1) hp hp1 L hL u v =
    FiniteThreeLevelHistoryTransfer.evolutionKernel L hL p r hp hp1 hr hr1
      (fixtureHistoryEquiv u) (fixtureHistoryEquiv v) := by
  rcases u with ⟨a,b,x⟩
  rcases v with ⟨c,d,y⟩
  cases x; cases y
  rw [insertedKernel_trace, fixture_effect, fixture_effect,
    FiniteThreeLevelHistoryTransfer.evolutionKernel_trace]
  rfl

section FixtureQuotient
open FinitePositiveKernel
open scoped InnerProductSpace
variable (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
local notation "TF" => FiniteThreeLevelPositiveHistory.negativeTree r hr hr1
local notation "KF" => kernel TF (Nat.zero_lt_succ 14) (fixture_stationary r hr hr1) p hp hp1
local notation "hKF" => kernel_posSemidef TF (Nat.zero_lt_succ 14) (fixture_stationary r hr hr1) p hp hp1
local notation "KO" => FiniteThreeLevelPositiveHistory.kernel p r hp hp1 hr hr1
local notation "hKO" => FiniteThreeLevelPositiveHistory.kernel_posSemidef p r hp hp1 hr hr1

def fixtureCoefficientMap : Coefficients hKO →ₗ[ℂ] Coefficients hKF := fixtureRecode

theorem fixture_null_relabel (f : Coefficients hKO) (hf : f ∈ nullSpace KO hKO) :
    fixtureCoefficientMap p r hp hp1 hr hr1 f ∈ nullSpace KF hKF := by
  apply (mem_nullSpace_iff _ _ _).mpr
  rw [pairing_synthesis]
  change FiniteThreeLevelPositiveHistory.form (synthesis TF p (fixtureRecode f))
    (synthesis TF p (fixtureRecode f)) = 0
  rw [fixture_synthesis_relabel,
    ← FiniteThreeLevelPositiveHistory.pairing_synthesis p r hp hp1 hr hr1]
  exact (mem_nullSpace_iff _ _ _).mp hf

def fixtureQuotientMap : FiniteThreeLevelPositiveHistory.Reconstructed p r hp hp1 hr hr1 →ₗ[ℂ]
    Reconstructed TF (by norm_num) (fixture_stationary r hr hr1) p hp hp1 :=
  (quotientEquiv KF hKF).toLinearMap.comp
    (((nullSpace KO hKO).mapQ (nullSpace KF hKF) (fixtureCoefficientMap p r hp hp1 hr hr1)
      (fixture_null_relabel p r hp hp1 hr hr1)).comp (quotientEquiv KO hKO).symm.toLinearMap)

theorem fixtureQuotientMap_mk (f : FiniteThreeLevelPositiveHistory.HalfHistory → ℂ) :
    fixtureQuotientMap p r hp hp1 hr hr1 (mk KO hKO f) = mk KF hKF (fixtureRecode f) := by
  rw [← quotientEquiv_mk hKO f]
  simp only [fixtureQuotientMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, Submodule.mapQ_apply]
  exact quotientEquiv_mk hKF _

theorem fixtureQuotientMap_coordinates (z : FiniteThreeLevelPositiveHistory.Reconstructed p r hp hp1 hr hr1) :
    coordinates TF (by norm_num) (fixture_stationary r hr hr1) p hp hp1
      (fixtureQuotientMap p r hp hp1 hr hr1 z) =
      FiniteThreeLevelPositiveHistory.coordinates p r hp hp1 hr hr1 z := by
  obtain ⟨f,rfl⟩ := mk_surjective KO hKO z
  rw [fixtureQuotientMap_mk, coordinates_mk, fixture_synthesis_relabel,
    FiniteThreeLevelPositiveHistory.coordinates_mk]

theorem fixtureQuotientMap_inner
    (z w : FiniteThreeLevelPositiveHistory.Reconstructed p r hp hp1 hr hr1) :
    ⟪fixtureQuotientMap p r hp hp1 hr hr1 z,fixtureQuotientMap p r hp hp1 hr hr1 w⟫_ℂ = ⟪z,w⟫_ℂ := by
  obtain ⟨f,rfl⟩ := mk_surjective KO hKO z
  obtain ⟨g,rfl⟩ := mk_surjective KO hKO w
  rw [fixtureQuotientMap_mk, fixtureQuotientMap_mk, inner_mk, inner_mk,
    pairing_synthesis, fixture_synthesis_relabel, fixture_synthesis_relabel,
    FiniteThreeLevelPositiveHistory.pairing_synthesis]

theorem fixtureQuotientMap_surjective : Function.Surjective (fixtureQuotientMap p r hp hp1 hr hr1) := by
  intro z
  obtain ⟨f,rfl⟩ := mk_surjective KF hKF z
  refine ⟨mk KO hKO (fun h => f (fixtureHistoryEquiv.symm h)), ?_⟩
  rw [fixtureQuotientMap_mk]
  congr 1

/-- The relabeling identifies the old and strategy quotients with their actual metrics. -/
def fixtureQuotientEquiv : FiniteThreeLevelPositiveHistory.Reconstructed p r hp hp1 hr hr1 ≃ₗᵢ[ℂ]
    Reconstructed TF (Nat.zero_lt_succ 14) (fixture_stationary r hr hr1) p hp hp1 :=
  LinearIsometryEquiv.ofSurjective
    ((fixtureQuotientMap p r hp hp1 hr hr1).isometryOfInner
      (fixtureQuotientMap_inner p r hp hp1 hr hr1))
    (fixtureQuotientMap_surjective p r hp hp1 hr hr1)

include hp hp1 in
theorem fixture_invariant (O : MatQ →ₗ[ℂ] MatQ)
    (hO : ∀ A, O (FiniteThreeLevelPositiveHistory.Psi p A) =
      FiniteThreeLevelPositiveHistory.Psi p (O A)) : Invariant TF p O := by
  intro A hA
  rw [← coordinates_range TF (Nat.zero_lt_succ 14) (fixture_stationary r hr hr1) p hp hp1] at hA ⊢
  obtain ⟨z,rfl⟩ := hA
  obtain ⟨w,rfl⟩ := fixtureQuotientMap_surjective p r hp hp1 hr hr1 z
  refine ⟨fixtureQuotientMap p r hp hp1 hr hr1
    (FiniteThreeLevelHistoryTransfer.induced p r hp hp1 hr hr1 O hO w), ?_⟩
  rw [fixtureQuotientMap_coordinates, fixtureQuotientMap_coordinates,
    FiniteThreeLevelHistoryTransfer.induced_coordinates]

theorem fixture_transfer_intertwines (O : MatQ →ₗ[ℂ] MatQ)
    (hO : ∀ A, O (FiniteThreeLevelPositiveHistory.Psi p A) =
      FiniteThreeLevelPositiveHistory.Psi p (O A))
    (z : FiniteThreeLevelPositiveHistory.Reconstructed p r hp hp1 hr hr1) :
    transfer TF p (Nat.zero_lt_succ 14) (fixture_stationary r hr hr1) hp hp1 O
      (fixture_invariant p r hp hp1 hr hr1 O hO) (fixtureQuotientMap p r hp hp1 hr hr1 z) =
    fixtureQuotientMap p r hp hp1 hr hr1
      (FiniteThreeLevelHistoryTransfer.induced p r hp hp1 hr hr1 O hO z) := by
  apply coordinates_injective TF (Nat.zero_lt_succ 14) (fixture_stationary r hr hr1) p hp hp1
  rw [coordinates_transfer, fixtureQuotientMap_coordinates, fixtureQuotientMap_coordinates,
    FiniteThreeLevelHistoryTransfer.induced_coordinates]

/-- Arbitrary exact lifts agree with the old explicit lift only modulo the synthesis nullspace. -/
theorem fixture_lift_mod_null (O : MatQ →ₗ[ℂ] MatQ)
    (hO : ∀ A, O (FiniteThreeLevelPositiveHistory.Psi p A) =
      FiniteThreeLevelPositiveHistory.Psi p (O A))
    (C : (History 15 2 → ℂ) →ₗ[ℂ] (History 15 2 → ℂ)) (hC : ExactLift TF p O C)
    (f : FiniteThreeLevelPositiveHistory.HalfHistory → ℂ) :
    mk KF hKF (C (fixtureRecode f)) =
      mk KF hKF (fixtureRecode (FiniteThreeLevelHistoryTransfer.raw r O f)) := by
  apply coordinates_injective TF (Nat.zero_lt_succ 14) (fixture_stationary r hr hr1) p hp hp1
  rw [coordinates_mk, coordinates_mk, exactLift_apply TF p hC,
    fixture_synthesis_relabel, fixture_synthesis_relabel,
    FiniteThreeLevelHistoryTransfer.raw_synthesis p r O hO]

theorem fixture_pulse_pairing (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ω : Q → ℝ) (t : ℝ)
    (f g : FiniteThreeLevelPositiveHistory.HalfHistory → ℂ) :
    pairing (pulseKernel TF p (Nat.zero_lt_succ 14) (fixture_stationary r hr hr1) hp hp1
      a ha ha1 ω t) (fixtureRecode f) (fixtureRecode g) =
    pairing (FiniteThreeLevelHistoryTransfer.phaseKernel p r a hp hp1 hr hr1 ha ha1 ω t) f g := by
  rw [pulseKernel_pairing, fixture_synthesis_relabel, fixture_synthesis_relabel,
    FiniteThreeLevelHistoryTransfer.phaseKernel_pairing]

theorem fixture_frame_transfer (hpos : 0 < p) (O : MatQ →ₗ[ℂ] MatQ)
    (hO : ∀ A, O (FiniteThreeLevelPositiveHistory.Psi p A) =
      FiniteThreeLevelPositiveHistory.Psi p (O A)) (A : MatQ) :
    coordinates TF (Nat.zero_lt_succ 14) (fixture_stationary r hr hr1) p hp hp1
      (transfer TF p (Nat.zero_lt_succ 14) (fixture_stationary r hr hr1) hp hp1 O
        (fixture_invariant p r hp hp1 hr hr1 O hO)
        (mk KF hKF (fixtureRecode (FiniteThreeLevelPositiveHistory.coefficients p A)))) = O A := by
  rw [coordinates_transfer, coordinates_mk]
  exact congrArg O (fixture_coefficients p r hpos hr hr1 A)

include hp hp1 in
theorem fixture_phase_invariant (ω : Q → ℝ) (t : ℝ) :
    Invariant TF p (FiniteThreeLevelHistoryTransfer.rotate ω t) :=
  fixture_invariant p r hp hp1 hr hr1 _ (FiniteThreeLevelHistoryTransfer.rotate_Psi ω t p)

/-- The actual old pulse transfer is intertwined for every physical side retention,
including both side-reset endpoints and central reset. -/
theorem fixture_pulse_intertwines (a : ℝ) (ω : Q → ℝ) (t : ℝ)
    (z : FiniteThreeLevelPositiveHistory.Reconstructed p r hp hp1 hr hr1) :
    pulseTransfer TF p (Nat.zero_lt_succ 14) (fixture_stationary r hr hr1) hp hp1
      ω (fixture_phase_invariant p r hp hp1 hr hr1 ω) a t
      (fixtureQuotientMap p r hp hp1 hr hr1 z) =
    fixtureQuotientMap p r hp hp1 hr hr1
      (FiniteThreeLevelHistoryTransfer.transfer p r hp hp1 hr hr1 a ω t z) := by
  apply coordinates_injective TF (Nat.zero_lt_succ 14) (fixture_stationary r hr hr1) p hp hp1
  rw [pulse_coordinates, fixtureQuotientMap_coordinates, fixtureQuotientMap_coordinates,
    FiniteThreeLevelHistoryTransfer.transfer_coordinates]

end FixtureQuotient

section AdaptiveControls
open FinitePositiveKernel
open FiniteThreeLevelHistoryTransfer (rotate freeLevels)
variable {k : ℕ} (U : Fin 15 → Tree Q Unit 15 k)
variable (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p)

include hpos in
/-- Complex leaf readout after the actual pulse insertion, for every adaptive continuation. -/
theorem family_complex_readout (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (ω : Q → ℝ) (t : ℝ) (X : MatQ) (h : History 15 (1+k+1)) :
    pairing (pulseKernel (adaptiveFamily U) p (Nat.zero_lt_succ 14)
      (adaptiveFamily_stationary U) hp hp1 a ha ha1 ω t)
      (familyCoeff U p (FiniteThreeLevelHistoryReadout.dualState X)) (Pi.single h 1) =
    (rotate ω t (FiniteThreeLevelPositiveHistory.Psi a
      (FiniteThreeLevelPositiveHistory.Psi p (effect (adaptiveFamily U) h))) * X).trace := by
  rw [pulseKernel_pairing, synthesis_single]
  rw [show synthesis (adaptiveFamily U) p
    (familyCoeff U p (FiniteThreeLevelHistoryReadout.dualState X)) =
      FiniteThreeLevelHistoryReadout.dualState X from adaptiveFamily_synthesis U p hpos _]
  exact FiniteThreeLevelHistoryReadout.dualState_form _ _

/-- The existing genuinely adaptive complex leaf remains a physical coefficient probe. -/
theorem adaptive_complex_leaf_reset_entry (a : ℝ) :
    FiniteThreeLevelPositiveHistory.Psi a
      (FiniteThreeLevelPositiveHistory.Psi p (effect adaptiveExample (5,0,0,()))) 0 1 =
      -3 * (a : ℂ) * (p : ℂ) * Complex.I / 250 := by
  simp only [FiniteThreeLevelPositiveHistory.Psi, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.one_apply_ne (by decide : (0 : Q) ≠ 1), mul_zero, add_zero]
  rw [imaginary_leaf_entry]
  ring

include hpos in
/-- Old fixture probes can be realized with the explicit arbitrary-depth family coefficients. -/
theorem family_fixture_pulse_pairing (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (ω : Q → ℝ) (t : ℝ) (f g : FiniteThreeLevelPositiveHistory.HalfHistory → ℂ) :
    pairing (pulseKernel (adaptiveFamily U) p (Nat.zero_lt_succ 14)
      (adaptiveFamily_stationary U) hp hp1 a ha ha1 ω t)
      (familyCoeff U p (FiniteThreeLevelPositiveHistory.synthesis p 0 f))
      (familyCoeff U p (FiniteThreeLevelPositiveHistory.synthesis p 0 g)) =
    pairing (FiniteThreeLevelHistoryTransfer.phaseKernel p 0 a hp hp1
      (by norm_num) (by norm_num) ha ha1 ω t) f g := by
  rw [familyCoeff_pulse_pairing U p hp hp1 hpos,
    FiniteThreeLevelHistoryTransfer.phaseKernel_pairing]

include hpos in
theorem family_quarter_nonhermitian (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    ¬ (pulseKernel (adaptiveFamily U) p (Nat.zero_lt_succ 14) (adaptiveFamily_stationary U)
      hp hp1 a ha.le ha1 (freeLevels (Real.pi/2) (Real.pi/2)) 1).IsHermitian := by
  intro hh
  have hf : accessible (adaptiveFamily U) p = ⊤ := by
    rw [range_positive_eq_effect_span _ _ hpos, adaptiveFamily_full_span]
  have hi := full_hermitian_necessary (adaptiveFamily U) p (Nat.zero_lt_succ 14)
    (adaptiveFamily_stationary U) hp hp1 hf a ha ha1 _ _ hh 0 1
  rw [FiniteThreeLevelHistoryTransfer.multiplier_euler,
    (FiniteThreeLevelHistoryTransfer.free_angles _ _).1] at hi
  norm_num at hi

theorem family_free_half_hermitian (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (pulseKernel (adaptiveFamily U) p (Nat.zero_lt_succ 14) (adaptiveFamily_stationary U)
      hp hp1 a ha ha1 (freeLevels Real.pi Real.pi) 1).IsHermitian := by
  apply ambient_hermitian_sufficient
  intro i j
  rw [FiniteThreeLevelHistoryTransfer.multiplier_euler]
  fin_cases i <;> fin_cases j <;> simp [FiniteThreeLevelHistoryTransfer.angle, freeLevels]

include hpos in
theorem family_free_half_negative (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    (pairing (pulseKernel (adaptiveFamily U) p (Nat.zero_lt_succ 14) (adaptiveFamily_stationary U)
      hp hp1 a ha.le ha1 (freeLevels Real.pi Real.pi) 1)
      (familyCoeff U p (FiniteThreeLevelPositiveHistory.synthesis p 0
        (FiniteThreeLevelPositiveHistory.innerMode 2)))
      (familyCoeff U p (FiniteThreeLevelPositiveHistory.synthesis p 0
        (FiniteThreeLevelPositiveHistory.innerMode 2)))).re < 0 := by
  rw [family_fixture_pulse_pairing U p hp hp1 hpos]
  exact (FiniteThreeLevelHistoryTransfer.free_half_negative p 0 a hp hp1
    (by norm_num) (by norm_num) ha.le ha1 hpos ha).2

include hpos in
/-- Only the selected thermal half-time quadratic value is asserted negative. -/
theorem family_thermal_half_negative {b ℏ : ℝ} (hb : 0 < b) (hℏ : 0 < ℏ)
    (γ : ℝ) (hγ : 0 ≤ γ) :
    (pairing (thermalKernel (adaptiveFamily U) p (Nat.zero_lt_succ 14) (adaptiveFamily_stationary U)
      hp hp1 b ℏ γ (FiniteThreeLevelHistoryTransfer.halfTime b ℏ) hγ
        (FiniteThreeLevelHistoryTransfer.halfTime_positive hb hℏ).le)
      (familyCoeff U p (FiniteThreeLevelPositiveHistory.synthesis p 0
        (FiniteThreeLevelPositiveHistory.innerMode 2)))
      (familyCoeff U p (FiniteThreeLevelPositiveHistory.synthesis p 0
        (FiniteThreeLevelPositiveHistory.innerMode 2)))).re < 0 := by
  rw [thermalKernel_eq_pulse, family_fixture_pulse_pairing U p hp hp1 hpos,
    ← FiniteThreeLevelHistoryTransfer.thermalKernel_eq_phase]
  exact (FiniteThreeLevelHistoryTransfer.timed_half_negative p 0 hp hp1
    (by norm_num) (by norm_num) hpos hb hℏ γ hγ).2

end AdaptiveControls

section RankDeficientControls
open FiniteThreeLevelHistoryTransfer (rotate)

theorem computational_phase_fixed_all (p : ℝ) (hp : 0 ≤ p) (ω : Q → ℝ) (t : ℝ)
    (A : MatQ) (hA : A ∈ accessible computationalTree p) : rotate ω t A = A := by
  rcases eq_or_lt_of_le hp with h | h
  · subst p
    exact phase_fixed_of_scalar computationalTree 0 (reset_range computationalTree) ω t A hA
  · exact computational_phase_fixed p h ω t A hA

theorem computational_pulse_positive_all (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ω : Q → ℝ) (t : ℝ) :
    (pulseKernel computationalTree p (Nat.zero_lt_succ 2) computational_stationary hp hp1
      a ha ha1 ω t).PosSemidef :=
  pulseKernel_positive_of_fixed computationalTree p (Nat.zero_lt_succ 2) computational_stationary
    hp hp1 a ha ha1 ω t (computational_phase_fixed_all p hp ω t)

/-- All ambient phases remain allowed on the actual rank-three diagonal range. -/
theorem computational_rank_phase (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p)
    (ω : Q → ℝ) (t : ℝ) :
    Module.finrank ℂ (Reconstructed computationalTree (Nat.zero_lt_succ 2)
      computational_stationary p hp hp1) = 3 ∧
    (pulseKernel computationalTree p (Nat.zero_lt_succ 2) computational_stationary hp hp1
      1 (by norm_num) (by norm_num) ω t).PosSemidef :=
  ⟨computational_rank p hp hp1 hpos,
    computational_pulse_positive_all p hp hp1 1 (by norm_num) (by norm_num) ω t⟩

theorem done_scalar_range (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    accessible (Tree.done : Tree Q Unit 1 0) p = Submodule.span ℂ {(1 : MatQ)} := by
  apply scalar_of_rank_one
  rw [← reconstructed_finrank _ (Nat.zero_lt_succ 0) done_stationary p hp hp1]
  exact done_rank p hp hp1

theorem done_phase_invariant (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (ω : Q → ℝ) (t : ℝ) :
    Invariant (Tree.done : Tree Q Unit 1 0) p (rotate ω t) :=
  scalar_phase_invariant _ p (done_scalar_range p hp hp1) ω t

theorem done_pulse_identity (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (ω : Q → ℝ) (a t : ℝ)
    (z : Reconstructed (Tree.done : Tree Q Unit 1 0) (Nat.zero_lt_succ 0) done_stationary p hp hp1) :
    pulseTransfer (Tree.done : Tree Q Unit 1 0) p (Nat.zero_lt_succ 0) done_stationary hp hp1
      ω (done_phase_invariant p hp hp1 ω) a t z = z :=
  pulse_identity_of_scalar _ p (Nat.zero_lt_succ 0) done_stationary hp hp1
    (done_scalar_range p hp hp1) ω _ a t z

theorem binary_central_reset_identity (ω : Q → ℝ) (a t : ℝ)
    (z : Reconstructed binaryTree (Nat.zero_lt_succ 1) binary_stationary 0
      (by norm_num) (by norm_num)) :
    pulseTransfer binaryTree 0 (Nat.zero_lt_succ 1) binary_stationary (by norm_num) (by norm_num)
      ω (binary_reset_phase_invariant ω) a t z = z :=
  pulse_identity_of_scalar binaryTree 0 (Nat.zero_lt_succ 1) binary_stationary
    (by norm_num) (by norm_num) (reset_range binaryTree) ω _ a t z

theorem family_central_reset_identity {k : ℕ} (U : Fin 15 → Tree Q Unit 15 k)
    (ω : Q → ℝ) (a t : ℝ)
    (z : Reconstructed (adaptiveFamily U) (Nat.zero_lt_succ 14) (adaptiveFamily_stationary U)
      0 (by norm_num) (by norm_num)) :
    pulseTransfer (adaptiveFamily U) 0 (Nat.zero_lt_succ 14) (adaptiveFamily_stationary U)
      (by norm_num) (by norm_num) ω
      (fun s => scalar_phase_invariant _ 0 (reset_range _) ω s) a t z = z :=
  reset_endpoint_pulse_identity _ (Nat.zero_lt_succ 14) (adaptiveFamily_stationary U) ω a t z

end RankDeficientControls

section PhysicalAdaptiveConsumer
open FiniteThreeLevelHistoryTransfer (rotate)
open FinitePositiveKernel.GibbsObservable
variable {k : ℕ} (U : Fin 15 → Tree Q Unit 15 k)
variable (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p)

include hpos in
theorem family_thermal_physical_coordinates (b ℏ γ t : ℝ) (hb : 0 < b) (hℏ : 0 < ℏ)
    (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (z : Reconstructed (adaptiveFamily U) (Nat.zero_lt_succ 14) (adaptiveFamily_stationary U)
      p hp hp1) :
    FiniteGibbsClock.gibbs (FiniteThreeLevelThermalPhase.thermalH b) b = rhoN ∧
    coordinates (adaptiveFamily U) (Nat.zero_lt_succ 14) (adaptiveFamily_stationary U) p hp hp1
      (pulseTransfer (adaptiveFamily U) p (Nat.zero_lt_succ 14) (adaptiveFamily_stationary U)
        hp hp1 (FiniteThreeLevelThermalPhase.frequencies b ℏ)
        (fun s => adaptiveFamily_invariant U p hpos (rotate _ s)) (Real.exp (-γ*t)) t z) =
      FiniteGibbsClock.heisenberg (FiniteThreeLevelThermalPhase.thermalH b) ℏ t
        (Channel.heisenberg (FiniteThreeLevelPositiveHistory.channel (Real.exp (-γ*t)))
          (coordinates (adaptiveFamily U) (Nat.zero_lt_succ 14) (adaptiveFamily_stationary U)
            p hp hp1 z)) :=
  ⟨FiniteThreeLevelThermalPhase.gibbs_thermal hb,
    thermal_physical_coordinates _ p (Nat.zero_lt_succ 14) (adaptiveFamily_stationary U)
      hp hp1 b ℏ γ t hℏ hγ ht _ z⟩

include hpos in
theorem family_actual_right_derivative (b ℏ γ : ℝ) (hγ : 0 ≤ γ)
    (z : Reconstructed (adaptiveFamily U) (Nat.zero_lt_succ 14) (adaptiveFamily_stationary U)
      p hp hp1) :
    HasDerivWithinAt
      (fun t : ℝ => coordinateRecovery (adaptiveFamily U) p (Nat.zero_lt_succ 14)
        (adaptiveFamily_stationary U) hp hp1
        (Channel.heisenberg (FiniteThreeLevelThermalPhase.channelKraus b ℏ γ t)
          (coordinates (adaptiveFamily U) (Nat.zero_lt_succ 14) (adaptiveFamily_stationary U)
            p hp hp1 z)))
      (generator (adaptiveFamily U) p (Nat.zero_lt_succ 14) (adaptiveFamily_stationary U)
        hp hp1 (FiniteThreeLevelThermalPhase.frequencies b ℏ) γ z) (Set.Ici 0) 0 :=
  actual_thermal_right_derivative _ p (Nat.zero_lt_succ 14) (adaptiveFamily_stationary U)
    hp hp1 b ℏ γ hγ (fun s => adaptiveFamily_invariant U p hpos (rotate _ s)) z

include hpos in
theorem family_generator_duality (b ℏ γ : ℝ) (hγ : 0 ≤ γ)
    (z : Reconstructed (adaptiveFamily U) (Nat.zero_lt_succ 14) (adaptiveFamily_stationary U)
      p hp hp1) (X : MatQ) :
    (coordinates (adaptiveFamily U) (Nat.zero_lt_succ 14) (adaptiveFamily_stationary U) p hp hp1
      (generator (adaptiveFamily U) p (Nat.zero_lt_succ 14) (adaptiveFamily_stationary U)
        hp hp1 (FiniteThreeLevelThermalPhase.frequencies b ℏ) γ z) * X).trace =
    (coordinates (adaptiveFamily U) (Nat.zero_lt_succ 14) (adaptiveFamily_stationary U) p hp hp1 z *
      OpenSystems.lindbladGenerator (FiniteThreeLevelThermalPhase.scaledH b ℏ)
        (FiniteThreeLevelThermalPhase.jumps γ) X).trace :=
  thermal_generator_duality _ p (Nat.zero_lt_succ 14) (adaptiveFamily_stationary U)
    hp hp1 b ℏ γ hγ (fun s => adaptiveFamily_invariant U p hpos (rotate _ s)) z X

include hpos in
theorem family_modular_coordinates (b ℏ s : ℝ) (hℏ : 0 < ℏ)
    (z : Reconstructed (adaptiveFamily U) (Nat.zero_lt_succ 14) (adaptiveFamily_stationary U)
      p hp hp1) :
    coordinates (adaptiveFamily U) (Nat.zero_lt_succ 14) (adaptiveFamily_stationary U) p hp hp1
      (transfer (adaptiveFamily U) p (Nat.zero_lt_succ 14) (adaptiveFamily_stationary U) hp hp1
        (modularLinear b s) (modular_invariant _ p b ℏ s hℏ
          (fun t => adaptiveFamily_invariant U p hpos (rotate _ t))) z) =
    rotate (FiniteThreeLevelThermalPhase.frequencies b ℏ) (-b*ℏ*s)
      (coordinates (adaptiveFamily U) (Nat.zero_lt_succ 14) (adaptiveFamily_stationary U) p hp hp1 z) :=
  modular_strategy_coordinates _ p (Nat.zero_lt_succ 14) (adaptiveFamily_stationary U)
    hp hp1 b ℏ s hℏ (fun t => adaptiveFamily_invariant U p hpos (rotate _ t)) z

end PhysicalAdaptiveConsumer


/-- The actual leaking binary strategy satisfies single-time invariance at zero,
without satisfying the all-real hypothesis at positive central retention. -/
theorem binary_zero_invariant (p : ℝ) :
    Invariant binaryTree p (FiniteThreeLevelHistoryTransfer.rotate leakingFrequencies 0) := by
  intro A hA
  rwa [FiniteThreeLevelHistoryTransfer.rotate_zero]

theorem binary_not_all_real_invariant (p : ℝ) (hp : 0 < p) :
    ¬ ∀ t : ℝ, Invariant binaryTree p
      (FiniteThreeLevelHistoryTransfer.rotate leakingFrequencies t) := by
  intro h
  exact binary_not_invariant p hp (h 1)

/-- The sharp selected-time criterion applies to this actual kernel even though
its positive-retention strategy has no all-real phase action. -/
theorem binary_zero_pulse_positive (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    (pulseKernel binaryTree p (Nat.zero_lt_succ 1) binary_stationary hp hp1
      a ha.le ha1 leakingFrequencies 0).PosSemidef := by
  apply (Pointwise.pulseKernel_positive_iff_on_range binaryTree p (Nat.zero_lt_succ 1)
    binary_stationary hp hp1 leakingFrequencies 0 (binary_zero_invariant p) a ha ha1).mpr
  intro A _
  exact FiniteThreeLevelHistoryTransfer.rotate_zero leakingFrequencies A

end SKEFTHawking.QuantumNetwork.FiniteThreeLevelStationaryStrategyTransferExamples

#check Nat
