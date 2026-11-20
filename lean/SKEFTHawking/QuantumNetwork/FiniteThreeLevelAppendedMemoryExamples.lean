import SKEFTHawking.QuantumNetwork.FiniteThreeLevelAppendedMemory

/-!
# Repeated physical endpoints, minimal linear realization and retained memory

Each count selects a fresh normalized experiment, with that many unread pulses.
Baseline subtraction concerns its ordinary equal-label event. The real linear
minimum follows from five such endpoints. Deterministic errors retain a concrete
nonzero channel/data/baseline consumer. Actual hidden-block elimination retains
arbitrary initial forcing and has no eventual finite lag at positive retention.
These are finite centered linear-model statements, with no physical hidden-state
uniqueness, tomography, clock calibration or continuum interpretation.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteThreeLevelAppendedMemoryExamples
open Matrix FiniteInterventionProcess FiniteAdaptiveKrausRealization
open FiniteThreeLevelStationaryStrategyTransferExamples
open FiniteThreeLevelCompressedStrategyMemoryExamples
open FiniteThreeLevelCompressedMemoryObservability FiniteThreeLevelCompressedMemoryObservabilityExamples
open FiniteThreeLevelAppendedMemory
open scoped BigOperators ComplexOrder

def repeated (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) : List Pulse :=
  List.replicate n ⟨a,ha,ha1,1⟩

theorem repeated_retention (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
    retention (repeated a ha ha1 n) = a^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change a * retention (repeated a ha ha1 n) = a^(n+1)
    rw [ih, pow_succ']

theorem repeated_phase (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
    totalPhase (repeated a ha ha1 n) = n := by
  induction n with
  | zero => simp [repeated, totalPhase]
  | succ n ih =>
    change 1 + totalPhase (repeated a ha ha1 n) = ((n+1 : ℕ) : ℝ)
    rw [ih]
    push_cast
    ring

def endpoint (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) : Table :=
  appendedTable p hp hp1 leakingFrequencies (repeated a ha ha1 n)

def response (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) : ℝ :=
  equalLabels (endpoint p hp hp1 a ha ha1 n) - 61/72

theorem endpoint_eq_pulseTable (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
    endpoint p hp hp1 a ha ha1 n =
      pulseTable p hp hp1 (a^n) (pow_nonneg ha _) (pow_le_one₀ ha ha1) n := by
  rw [endpoint, appendedTable_eq_pulseTable]
  funext i j
  rw [pulseTable_law, pulseTable_law, repeated_retention, repeated_phase]

theorem response_formula (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
    response p hp hp1 a ha ha1 n = 2*p^2*a^n*phaseResponse n := by
  rw [response, endpoint_eq_pulseTable, pulseTable_event]

theorem endpoint_law (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) (i j : Fin 2) :
    endpoint p hp hp1 a ha ha1 n i j =
      baseline i j + labelSign i * labelSign j * response p hp hp1 a ha ha1 n / 2 := by
  rw [endpoint_eq_pulseTable, pulseTable_law, response_formula]
  dsimp [baseline]
  ring

theorem endpoint_probability (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
    ProbabilityTable (endpoint p hp hp1 a ha ha1 n) :=
  appendedTable_probability p hp hp1 _

theorem phaseResponse_three : phaseResponse 3 = d := by
  rw [phaseResponse, show Real.pi*3/2 = Real.pi+Real.pi/2 by ring, Real.cos_add]
  norm_num

theorem phaseResponse_recurrence (n : ℕ) :
    phaseResponse (n+3) - phaseResponse (n+2) + phaseResponse (n+1) - phaseResponse n = 0 := by
  have he := pulse_entry_order_three 1 (by norm_num) (by norm_num)
    1 (by norm_num) (by norm_num) 0 0 n
  simp only [show ∀ t : ℝ, pulseTable 1 (by norm_num) (by norm_num) 1
      (by norm_num) (by norm_num) t 0 0 = (1/12)*(1/12)+phaseResponse t from
      fun t => by simpa [labelMass, labelSign] using
        pulseTable_law 1 (by norm_num) (by norm_num) 1 (by norm_num) (by norm_num) t 0 0, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] at he
  linarith

theorem phaseResponse_four_periodic (n : ℕ) : phaseResponse (n+4) = phaseResponse n := by
  have he := pulse_entry_four_return 1 (by norm_num) (by norm_num)
    1 (by norm_num) (by norm_num) 0 0 n
  simp only [show ∀ t : ℝ, pulseTable 1 (by norm_num) (by norm_num) 1
      (by norm_num) (by norm_num) t 0 0 = (1/12)*(1/12)+phaseResponse t from
      fun t => by simpa [labelMass, labelSign] using
        pulseTable_law 1 (by norm_num) (by norm_num) 1 (by norm_num) (by norm_num) t 0 0, Nat.cast_add, Nat.cast_ofNat] at he
  linarith

theorem response_recurrence (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
    response p hp hp1 a ha ha1 (n+3) - a * response p hp hp1 a ha ha1 (n+2) +
      a^2 * response p hp hp1 a ha ha1 (n+1) - a^3 * response p hp hp1 a ha ha1 n = 0 := by
  simp only [response_formula, pow_add, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  linear_combination 2*p^2*a^n*a^3 * phaseResponse_recurrence n

theorem response_four_step (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
    response p hp hp1 a ha ha1 (n+4) = a^4 * response p hp hp1 a ha ha1 n := by
  simp only [response_formula, pow_add, Nat.cast_add, Nat.cast_ofNat]
  rw [phaseResponse_four_periodic]
  ring

theorem response_zero (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) : response p hp hp1 a ha ha1 0 = 2*p^2*N := by
  rw [response_formula, Nat.cast_zero, phaseResponse_zero, pow_zero, mul_one]

theorem response_one (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) : response p hp hp1 a ha ha1 1 = 2*p^2*a*d := by
  rw [response_formula, Nat.cast_one, phaseResponse_one, pow_one]

theorem response_two (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) : response p hp hp1 a ha ha1 2 = 2*p^2*a^2*(d-h) := by
  rw [response_formula, Nat.cast_ofNat, phaseResponse_two]

def hankel (g : ℕ → ℝ) : Matrix (Fin 3) (Fin 3) ℝ := fun i j => g (i.val+j.val)

theorem response_hankel_det (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (hankel (response p hp hp1 a ha ha1)).det = -32*p^6*a^6*d*h^2 := by
  rw [Matrix.det_fin_three]
  simp only [hankel, response_formula]
  norm_num only [Fin.val_zero, Fin.val_one, Fin.val_two, zero_add, add_zero,
    Nat.reduceAdd, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, phaseResponse_zero,
    phaseResponse_one, phaseResponse_two, phaseResponse_three, phaseResponse_four, pow_zero,
    pow_one]
  dsimp [N]
  ring

theorem response_hankel_det_neg (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hapos : 0 < a) :
    (hankel (response p hp hp1 a ha ha1)).det < 0 := by
  rw [response_hankel_det]
  have hd : 0 < d := by norm_num [d]
  have hh : 0 < h := lt_trans hd (lt_trans (by linarith : d < 2*d) h_gt_twice_d)
  have ht : 0 < 32*p^6*a^6*d*h^2 := by positivity
  linarith

/-- Five outputs suffice, for every finite-dimensional homogeneous real linear model. -/
theorem finrank_ge_three_of_hankel {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (U : V →ₗ[ℝ] V) (x : V) (ell : V →ₗ[ℝ] ℝ)
    (g : ℕ → ℝ) (hdet : (hankel g).det ≠ 0)
    (hmatch : ∀ n ≤ 4, ell ((U^n) x) = g n) : 3 ≤ Module.finrank ℝ V := by
  let O : V →ₗ[ℝ] (Fin 3 → ℝ) := LinearMap.pi (fun i => ell.comp (U^i.val))
  have hcol : (fun j : Fin 3 => O ((U^j.val) x)) = (hankel g).col := by
    funext j i
    change ell ((U^i.val) ((U^j.val) x)) = g (i.val+j.val)
    rw [← Module.End.mul_apply, ← pow_add]
    exact hmatch _ (by have := i.isLt; have := j.isLt; omega)
  have hi : LinearIndependent ℝ (fun j : Fin 3 => (U^j.val) x) := by
    apply LinearIndependent.of_comp O
    change LinearIndependent ℝ (fun j : Fin 3 => O ((U^j.val) x))
    rw [hcol]
    exact Matrix.linearIndependent_cols_of_det_ne_zero hdet
  simpa using hi.fintype_card_le_finrank

theorem response_minimum_dimension (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hapos : 0 < a)
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (U : V →ₗ[ℝ] V) (x : V) (ell : V →ₗ[ℝ] ℝ)
    (hmatch : ∀ n ≤ 4, ell ((U^n) x) = response p hp hp1 a ha ha1 n) :
    3 ≤ Module.finrank ℝ V :=
  finrank_ge_three_of_hankel U x ell _ (ne_of_lt (response_hankel_det_neg p hp hp1 hpos a ha ha1 hapos)) hmatch

theorem hankel_det_zero_of_order_two (g : ℕ → ℝ) (b c : ℝ)
    (hr : ∀ n, g (n+2) = b*g (n+1)+c*g n) : (hankel g).det = 0 := by
  rw [Matrix.det_fin_three]
  norm_num only [hankel, Fin.val_zero, Fin.val_one, Fin.val_two, zero_add, add_zero, Nat.reduceAdd]
  have h0 := hr 0
  have h1 := hr 1
  have h2 := hr 2
  norm_num only [Nat.reduceAdd, zero_add] at h0 h1 h2
  rw [h2, h1, h0]
  ring

theorem response_no_order_two (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hapos : 0 < a) :
    ¬ ∃ b c : ℝ, ∀ n, response p hp hp1 a ha ha1 (n+2) =
      b*response p hp hp1 a ha ha1 (n+1) + c*response p hp hp1 a ha ha1 n := by
  rintro ⟨b,c,hr⟩
  exact (ne_of_lt (response_hankel_det_neg p hp hp1 hpos a ha ha1 hapos))
    (hankel_det_zero_of_order_two _ b c hr)

def modelUpdate (a : ℝ) : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun x := ![a*x 0, -a*x 2, a*x 1]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c x := by ext i; fin_cases i <;> simp <;> ring

def modelInitial : Fin 3 → ℝ := ![1,1,0]

def modelReadout (p : ℝ) : (Fin 3 → ℝ) →ₗ[ℝ] ℝ where
  toFun x := 2*p^2*(d*x 0+h*x 1)
  map_add' x y := by simp; ring
  map_smul' c x := by simp; ring

theorem model_characteristic (a : ℝ) (x : Fin 3 → ℝ) :
    modelUpdate a (modelUpdate a (modelUpdate a x)) -
      a • modelUpdate a (modelUpdate a x) + a^2 • modelUpdate a x - a^3 • x = 0 := by
  ext i
  fin_cases i <;> simp [modelUpdate] <;> ring

def modelOrbit (a : ℝ) : ℕ → (Fin 3 → ℝ)
  | 0 => modelInitial
  | n+1 => modelUpdate a (modelOrbit a n)

theorem modelOrbit_eq_power (a : ℝ) (n : ℕ) :
    modelOrbit a n = (modelUpdate a ^ n) modelInitial := by
  induction n with
  | zero => rfl
  | succ n ih => rw [modelOrbit, ih, pow_succ', Module.End.mul_apply]

theorem model_output_recurrence (p a : ℝ) (n : ℕ) :
    modelReadout p (modelOrbit a (n+3)) - a*modelReadout p (modelOrbit a (n+2)) +
      a^2*modelReadout p (modelOrbit a (n+1)) - a^3*modelReadout p (modelOrbit a n) = 0 := by
  have he := congrArg (modelReadout p) (model_characteristic a (modelOrbit a n))
  simpa only [map_sub, map_add, map_smul, map_zero, smul_eq_mul, modelOrbit] using he

theorem model_attains (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
    modelReadout p (modelOrbit a n) = response p hp hp1 a ha ha1 n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => rw [response_zero]; simp [modelOrbit, modelInitial, modelReadout, N]
    | 1 => rw [response_one]; simp [modelOrbit, modelInitial, modelUpdate, modelReadout]; ring
    | 2 => rw [response_two]; simp [modelOrbit, modelInitial, modelUpdate, modelReadout]; ring
    | k+3 =>
      have hm := model_output_recurrence p a k
      rw [ih k (by omega), ih (k+1) (by omega), ih (k+2) (by omega)] at hm
      have hr := response_recurrence p hp hp1 a ha ha1 k
      linarith

theorem model_attains_power (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
    modelReadout p ((modelUpdate a ^ n) modelInitial) = response p hp hp1 a ha ha1 n := by
  rw [← modelOrbit_eq_power, model_attains]

open FiniteThreeLevelCompressedStrategyMemory
open FiniteThreeLevelStationaryStrategyReflection
open FiniteThreeLevelPositiveHistory (Q MatQ Psi)
open FiniteThreeLevelHistoryTransfer (mean)
open FinitePositiveKernel.GibbsObservable

def actualUpdate (a : ℝ) : MatQ →ₗ[ℂ] MatQ :=
  Channel.heisenbergLinear (FiniteThreeLevelHistoryTransfer.pulseResetKraus a leakingFrequencies 1)

theorem actualUpdate_one (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) : actualUpdate a 1 = 1 :=
  Channel.heisenberg_one _ (FiniteThreeLevelHistoryTransfer.pulseReset_normalized a ha ha1 _ _)

theorem actualUpdate_centered (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (X : MatQ) (hX : mean X = 0) : actualUpdate a X = (a : ℂ) • sampled X := by
  change Channel.heisenberg _ X = _
  rw [FiniteThreeLevelHistoryTransfer.pulseReset_observable _ ha ha1]
  have he : Psi a X = (a : ℂ) • X := by
    change (a : ℂ) • X + (1-(a : ℂ)) • mean X • 1 = (a : ℂ) • X
    rw [hX, zero_smul, smul_zero, add_zero]
  rw [he, map_smul]
  rfl

theorem mean_G : mean hiddenG = 0 := by
  change FiniteThreeLevelHistoryTransfer.meanLinear
    (centeredD - (alpha : ℂ) • centeredF) = 0
  rw [map_sub, map_smul]
  change mean centeredD - (alpha : ℂ)*mean centeredF = 0
  rw [mean_D, mean_F, mul_zero, sub_self]

theorem actual_blockA (p : ℝ) (hp : 0 < p) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    projection binaryTree p (actualUpdate a centeredF) = (a*alpha : ℂ) • centeredF := by
  rw [actualUpdate_centered _ ha ha1 _ mean_F, map_smul, actual_A_F p hp, smul_smul]


theorem actual_blockB (p : ℝ) (hp : 0 < p) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (c e : ℂ) :
    blockB binaryTree p (actualUpdate a) (hiddenVector p hp c e) =
      visibleVector p hp 0 ((a : ℂ)*(alpha*(1-alpha)*c-(1-alpha)*e)) := by
  apply Subtype.ext
  change projection binaryTree p (actualUpdate a (c • hiddenG + e • centeredY)) = _
  rw [map_add, map_smul, map_smul, actualUpdate_centered _ ha ha1 _ mean_G,
    actualUpdate_centered _ ha ha1 _ mean_Y, map_add, map_smul, map_smul, map_smul,
    map_smul, actual_B_G p hp, actual_B_Y p hp]
  change _ = (0 : ℂ) • (1 : MatQ) + _ • centeredF
  module

theorem actual_blockC (p : ℝ) (hp : 0 < p) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (b : ℂ) :
    blockC binaryTree p (actualUpdate a) (visibleVector p hp 0 b) =
      hiddenVector p hp ((a : ℂ)*b) ((a : ℂ)*b) := by
  apply Subtype.ext
  change hiddenProjection binaryTree p (actualUpdate a ((0 : ℂ) • 1 + b • centeredF)) = _
  simp only [zero_smul, zero_add, map_smul]
  rw [actualUpdate_centered _ ha ha1 _ mean_F, map_smul, actual_C_F p hp]
  change _ = ((a : ℂ)*b) • hiddenG + ((a : ℂ)*b) • centeredY
  module

theorem actual_blockD (p : ℝ) (hp : 0 < p) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (c e : ℂ) :
    blockD binaryTree p (actualUpdate a) (hiddenVector p hp c e) =
      hiddenVector p hp ((a : ℂ)*((1-alpha)*c+e)) (-(a : ℂ)*alpha*c) := by
  apply Subtype.ext
  change hiddenProjection binaryTree p (actualUpdate a (c • hiddenG + e • centeredY)) = _
  rw [map_add, map_smul, map_smul, actualUpdate_centered _ ha ha1 _ mean_G,
    actualUpdate_centered _ ha ha1 _ mean_Y, map_add, map_smul, map_smul,
    map_smul, map_smul, actual_D_G p hp, actual_D_Y p hp]
  change _ = ((a : ℂ)*((1-alpha)*c+e)) • hiddenG + (-(a : ℂ)*alpha*c) • centeredY
  module

def hiddenUpdate (a : ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun x := ![a*((1-alpha)*x 0+x 1), -a*alpha*x 0]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c x := by ext i; fin_cases i <;> simp <;> ring

def hiddenReadout (a : ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] ℝ where
  toFun x := a*(alpha*(1-alpha)*x 0-(1-alpha)*x 1)
  map_add' x y := by simp; ring
  map_smul' c x := by simp; ring

def hiddenSequence (a : ℝ) : ℕ → (Fin 2 → ℝ)
  | 0 => ![a,a]
  | n+1 => hiddenUpdate a (hiddenSequence a n)

/-- Coordinates of B D^m C for the actual pulse channel, identified below. -/
def kappa (a : ℝ) (m : ℕ) : ℝ := hiddenReadout a (hiddenSequence a m)

theorem actual_hidden_power (p : ℝ) (hp : 0 < p) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (m : ℕ) :
    (blockD binaryTree p (actualUpdate a)^m) (hiddenVector p hp a a) =
      hiddenVector p hp ((hiddenSequence a m 0 : ℝ) : ℂ) ((hiddenSequence a m 1 : ℝ) : ℂ) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, ih, actual_blockD p hp a ha ha1]
    simp only [hiddenSequence, hiddenUpdate, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    push_cast
    rfl

theorem actual_kernel_F (p : ℝ) (hp : 0 < p) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (m : ℕ) :
    (memoryKernel binaryTree p (actualUpdate a) m (visibleVector p hp 0 1) : MatQ) =
      (kappa a m : ℂ) • centeredF := by
  simp only [memoryKernel, LinearMap.comp_apply]
  rw [actual_blockC p hp a ha ha1, mul_one, actual_hidden_power p hp a ha ha1,
    actual_blockB p hp a ha ha1]
  change (0 : ℂ) • (1 : MatQ) + _ • centeredF = _
  simp only [zero_smul, zero_add, kappa, hiddenReadout, LinearMap.coe_mk, AddHom.coe_mk]
  push_cast
  rfl

theorem actual_kernel_I (p : ℝ) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (m : ℕ) :
    memoryKernel binaryTree p (actualUpdate a) m ⟨1,one_mem_accessible binaryTree p⟩ = 0 := by
  have hc : blockC binaryTree p (actualUpdate a) ⟨1,one_mem_accessible binaryTree p⟩ = 0 := by
    apply Subtype.ext
    change hiddenProjection binaryTree p (actualUpdate a 1) = 0
    rw [actualUpdate_one _ ha ha1, hidden_fixed_zero _ _ (one_mem_accessible binaryTree p)]
  simp only [memoryKernel, LinearMap.comp_apply, hc, map_zero]

theorem hidden_characteristic (a : ℝ) (x : Fin 2 → ℝ) :
    hiddenUpdate a (hiddenUpdate a x) - (a*(1-alpha)) • hiddenUpdate a x +
      (a^2*alpha) • x = 0 := by
  ext i
  fin_cases i <;> simp [hiddenUpdate] <;> ring

theorem kappa_zero (a : ℝ) : kappa a 0 = -a^2*(1-alpha)^2 := by
  simp [kappa, hiddenReadout, hiddenSequence]
  ring

theorem kappa_one (a : ℝ) : kappa a 1 = a^3*alpha*(1-alpha)*(3-alpha) := by
  simp [kappa, hiddenReadout, hiddenSequence, hiddenUpdate]
  ring

theorem kappa_recurrence (a : ℝ) (m : ℕ) :
    kappa a (m+2) = a*(1-alpha)*kappa a (m+1) - a^2*alpha*kappa a m := by
  have he := congrArg (hiddenReadout a) (hidden_characteristic a (hiddenSequence a m))
  simp only [map_sub, map_add, map_smul, map_zero, smul_eq_mul] at he
  change kappa a (m+2) - a*(1-alpha)*kappa a (m+1) + a^2*alpha*kappa a m = 0 at he
  linarith

theorem kappa_not_eventually_zero (a : ℝ) (ha : 0 < a) (L : ℕ) :
    ∃ m ≥ L, kappa a m ≠ 0 := by
  have hc : a^2*alpha ≠ 0 := ne_of_gt (mul_pos (sq_pos_of_pos ha) alpha_pos)
  have hb : ∀ n, kappa a (n+1) = 0 → kappa a (n+2) = 0 → kappa a n = 0 := by
    intro n h1 h2
    have he := kappa_recurrence a n
    rw [h1,h2, mul_zero, zero_sub] at he
    exact (mul_eq_zero.mp (neg_eq_zero.mp he.symm)).resolve_left hc
  have hback : ∀ k, (∀ m ≥ k, kappa a m = 0) → kappa a 0 = 0 := by
    intro k
    induction k with
    | zero => intro hz; exact hz 0 le_rfl
    | succ k ih =>
      intro hz
      apply ih
      intro m hm
      by_cases he : m = k
      · subst m
        exact hb k (hz (k+1) (by omega)) (hz (k+2) (by omega))
      · exact hz m (by omega)
  by_contra hn
  push Not at hn
  have hz := hback L hn
  rw [kappa_zero] at hz
  have ht : 0 < a^2*(1-alpha)^2 := by
    have hal : 0 < 1-alpha := by linarith [alpha_lt_half]
    positivity
  linarith

/-- The real model coordinates embed the actual centered D,H,Y orbit. -/
def realize (x : Fin 3 → ℝ) : MatQ :=
  (x 0 : ℂ) • centeredD + (x 1 : ℂ) • centeredH + (x 2 : ℂ) • centeredY

theorem realize_initial : realize modelInitial = centeredF := by
  simp [realize, modelInitial, centered_decomposition]

theorem actualUpdate_realize (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (x : Fin 3 → ℝ) :
    actualUpdate a (realize x) = realize (modelUpdate a x) := by
  simp only [realize, map_add, map_smul, actualUpdate_centered _ ha ha1 _ mean_D,
    actualUpdate_centered _ ha ha1 _ mean_H, actualUpdate_centered _ ha ha1 _ mean_Y,
    sampled_D, sampled_H, sampled_Y]
  change _ = ((a*x 0 : ℝ) : ℂ) • centeredD + ((-a*x 2 : ℝ) : ℂ) • centeredH +
    ((a*x 1 : ℝ) : ℂ) • centeredY
  push_cast
  module

theorem actual_centered_orbit (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
    (actualUpdate a ^ n) centeredF = realize (modelOrbit a n) := by
  induction n with
  | zero => exact realize_initial.symm
  | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, actualUpdate_realize _ ha ha1, modelOrbit]

theorem actualUpdate_preserves_closure (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    {X : MatQ} (hX : X ∈ invariantClosure) : actualUpdate a X ∈ invariantClosure := by
  induction hX using Submodule.span_induction with
  | mem X hX =>
    obtain ⟨i,rfl⟩ := hX
    fin_cases i
    · change actualUpdate a 1 ∈ invariantClosure
      rw [actualUpdate_one _ ha ha1]
      exact closure_I
    · change actualUpdate a centeredD ∈ invariantClosure
      rw [actualUpdate_centered _ ha ha1 _ mean_D, sampled_D]
      exact invariantClosure.smul_mem (a : ℂ) closure_D
    · change actualUpdate a centeredH ∈ invariantClosure
      rw [actualUpdate_centered _ ha ha1 _ mean_H, sampled_H]
      exact invariantClosure.smul_mem (a : ℂ) closure_Y
    · change actualUpdate a centeredY ∈ invariantClosure
      rw [actualUpdate_centered _ ha ha1 _ mean_Y, sampled_Y]
      exact invariantClosure.smul_mem (a : ℂ) (invariantClosure.neg_mem closure_H)
  | zero => simp
  | add X Y _ _ hX hY => simpa only [map_add] using invariantClosure.add_mem hX hY
  | smul c X _ hX => simpa only [map_smul] using invariantClosure.smul_mem c hX

def actualRestrictedD (p : ℝ) (hp : 0 < p) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    restrictedHidden p →ₗ[ℂ] restrictedHidden p :=
  ((hiddenProjection binaryTree p).comp ((actualUpdate a).comp (restrictedHidden p).subtype)).codRestrict _
    (fun x => ⟨closure_preserved_Q p hp (actualUpdate_preserves_closure a ha ha1 x.property.1),
      projection_hidden binaryTree p _⟩)

theorem actual_restricted_D_matrix (p : ℝ) (hp : 0 < p) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (c e : ℂ) : actualRestrictedD p hp a ha ha1 (restrictedHiddenVector p hp c e) =
      restrictedHiddenVector p hp ((a : ℂ)*((1-alpha)*c+e)) (-(a : ℂ)*alpha*c) := by
  apply Subtype.ext
  exact congrArg (fun x : (projection binaryTree p).ker => (x : MatQ))
    (actual_blockD p hp a ha ha1 c e)

/-- Ambient elimination retains arbitrary initial hidden forcing, even at count zero. -/
theorem actual_visible_memory (p a : ℝ) (x : MatQ) (n : ℕ) :
    visibleOrbit binaryTree p (actualUpdate a) x (n+1) =
      blockA binaryTree p (actualUpdate a) (visibleOrbit binaryTree p (actualUpdate a) x n) +
      blockB binaryTree p (actualUpdate a)
        ((blockD binaryTree p (actualUpdate a)^n) (hidden binaryTree p x)) +
      ∑ j ∈ Finset.range n, memoryKernel binaryTree p (actualUpdate a) (n-1-j)
        (visibleOrbit binaryTree p (actualUpdate a) x j) :=
  visible_memory binaryTree p (actualUpdate a) x n

theorem actual_centered_memory (p : ℝ) (hp : 0 < p) (a : ℝ) (n : ℕ) :
    visibleOrbit binaryTree p (actualUpdate a) centeredF (n+1) =
      blockA binaryTree p (actualUpdate a) (visibleOrbit binaryTree p (actualUpdate a) centeredF n) +
      ∑ j ∈ Finset.range n, memoryKernel binaryTree p (actualUpdate a) (n-1-j)
        (visibleOrbit binaryTree p (actualUpdate a) centeredF j) := by
  rw [actual_visible_memory, hidden_initial_accessible _ _ _ (centeredF_mem p hp),
    map_zero, map_zero, add_zero]

theorem raw_event_recurrence (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
    equalLabels (endpoint p hp hp1 a ha ha1 (n+3)) -
      a*equalLabels (endpoint p hp hp1 a ha ha1 (n+2)) +
      a^2*equalLabels (endpoint p hp hp1 a ha ha1 (n+1)) -
      a^3*equalLabels (endpoint p hp hp1 a ha ha1 n) = (61/72)*(1-a+a^2-a^3) := by
  have hr := response_recurrence p hp hp1 a ha ha1 n
  dsimp [response] at hr
  linear_combination hr

theorem triple_error (x y z u v w L delta : ℝ) (hL : 0 ≤ L) (hd : 0 ≤ delta)
    (hy : |y| ≤ L) (hz : |z| ≤ L) (hu : |u| ≤ L) (hv : |v| ≤ L)
    (hx : |x-u| ≤ delta) (hyy : |y-v| ≤ delta) (hzz : |z-w| ≤ delta) :
    |x*y*z-u*v*w| ≤ 3*delta*L^2 := by
  calc
    _ = |(x-u)*y*z+u*(y-v)*z+u*v*(z-w)| := by congr 1; ring
    _ ≤ |(x-u)*y*z+u*(y-v)*z|+|u*v*(z-w)| := abs_add_le _ _
    _ ≤ (|(x-u)*y*z|+|u*(y-v)*z|)+|u*v*(z-w)| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ ≤ (delta*L*L+L*delta*L)+L*L*delta := by
      simp only [abs_mul]
      gcongr
    _ = _ := by ring

theorem abs_sub_bound (x y : ℝ) : |x-y| ≤ |x|+|y| := by
  simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le x 0 y

theorem abs_six_terms (a b c d e f : ℝ) :
    |a-b-c+d+e-f| ≤ |a|+|b|+|c|+|d|+|e|+|f| := by
  calc
    _ ≤ |a-b-c+d+e|+|f| := abs_sub_bound _ _
    _ ≤ (|a-b-c+d|+|e|)+|f| := add_le_add (abs_add_le _ _) le_rfl
    _ ≤ ((|a-b-c|+|d|)+|e|)+|f| := by gcongr; exact abs_add_le _ _
    _ ≤ (((|a-b|+|c|)+|d|)+|e|)+|f| := by gcongr; exact abs_sub_bound _ _
    _ ≤ _ := by gcongr; exact abs_sub_bound _ _

theorem hankel_error (g f : ℕ → ℝ) (M delta : ℝ) (hM : 0 ≤ M) (hd : 0 ≤ delta)
    (hg : ∀ n ≤ 4, |g n| ≤ M) (he : ∀ n ≤ 4, |f n-g n| ≤ delta) :
    |(hankel f).det-(hankel g).det| ≤ 18*delta*(M+delta)^2 := by
  have hf : ∀ n ≤ 4, |f n| ≤ M+delta := by
    intro n hn
    calc
      _ = |(f n-g n)+g n| := by congr 1; ring
      _ ≤ |f n-g n|+|g n| := abs_add_le _ _
      _ ≤ delta+M := add_le_add (he n hn) (hg n hn)
      _ = _ := add_comm _ _
  have hg' : ∀ n ≤ 4, |g n| ≤ M+delta := fun n hn => (hg n hn).trans (by linarith)
  have ht (i j k : ℕ) (hi : i ≤ 4) (hj : j ≤ 4) (hk : k ≤ 4) :
      |f i*f j*f k-g i*g j*g k| ≤ 3*delta*(M+delta)^2 :=
    triple_error _ _ _ _ _ _ _ _ (by linarith) hd (hf j hj) (hf k hk)
      (hg' i hi) (hg' j hj) (he i hi) (he j hj) (he k hk)
  have hdet : (hankel f).det-(hankel g).det =
      (f 0*f 2*f 4-g 0*g 2*g 4) - (f 0*f 3*f 3-g 0*g 3*g 3) -
      (f 1*f 1*f 4-g 1*g 1*g 4) + (f 1*f 3*f 2-g 1*g 3*g 2) +
      (f 2*f 1*f 3-g 2*g 1*g 3) - (f 2*f 2*f 2-g 2*g 2*g 2) := by
    simp only [Matrix.det_fin_three, hankel]
    norm_num
    ring
  rw [hdet]
  have hs := abs_six_terms (f 0*f 2*f 4-g 0*g 2*g 4) (f 0*f 3*f 3-g 0*g 3*g 3)
    (f 1*f 1*f 4-g 1*g 1*g 4) (f 1*f 3*f 2-g 1*g 3*g 2)
    (f 2*f 1*f 3-g 2*g 1*g 3) (f 2*f 2*f 2-g 2*g 2*g 2)
  linarith [ht 0 2 4 (by omega) (by omega) (by omega),
    ht 0 3 3 (by omega) (by omega) (by omega), ht 1 1 4 (by omega) (by omega) (by omega),
    ht 1 3 2 (by omega) (by omega) (by omega), ht 2 1 3 (by omega) (by omega) (by omega),
    ht 2 2 2 (by omega) (by omega) (by omega)]

def amplitude (p : ℝ) : ℝ := 2*p^2*N
def determinantMargin (p a : ℝ) : ℝ := 32*p^6*a^6*d*h^2
def deltaStar (p a : ℝ) : ℝ := p^2*a^6*d*h^2/(18*N^2)

theorem amplitude_pos (p : ℝ) (hp : 0 < p) : 0 < amplitude p := by
  dsimp [amplitude]
  have := N_pos
  positivity

theorem deltaStar_pos (p a : ℝ) (hp : 0 < p) (ha : 0 < a) : 0 < deltaStar p a := by
  dsimp [deltaStar]
  have := d_pos
  have := h_pos
  have := N_pos
  positivity

theorem deltaStar_le (p a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    deltaStar p a ≤ amplitude p / 36 := by
  have hdpos := d_pos
  have hhpos := h_pos
  have hnpos := N_pos
  have hn : 0 < 18*N^2 := by positivity
  have hdh : d*h^2 ≤ N^3 := by
    have hd : d ≤ N := by dsimp [N]; linarith [h_pos]
    have hh : h ≤ N := by dsimp [N]; linarith [d_pos]
    calc
      d*h^2 ≤ N*N^2 := by gcongr
      _ = N^3 := by ring
  have ha6 : a^6 ≤ 1 := pow_le_one₀ ha ha1
  rw [deltaStar, div_le_iff₀ hn, amplitude]
  nlinarith [mul_le_mul_of_nonneg_left hdh (sq_nonneg p),
    mul_le_mul_of_nonneg_left ha6 (show 0 ≤ p^2*d*h^2 by positivity)]

theorem deltaStar_identity (p a : ℝ) :
    72*(amplitude p)^2*deltaStar p a = determinantMargin p a / 2 := by
  have hn : N ≠ 0 := ne_of_gt N_pos
  dsimp [amplitude, deltaStar, determinantMargin]
  field_simp
  ring

theorem response_abs_le (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
    |response p hp hp1 a ha ha1 n| ≤ amplitude p := by
  have hhpos := h_pos
  have hnpos := N_pos
  have hf : |phaseResponse (n : ℝ)| ≤ N := by
    dsimp [phaseResponse]
    calc
      _ ≤ |d|+|h*Real.cos (Real.pi*(n : ℝ)/2)| := abs_add_le _ _
      _ = d+h*|Real.cos (Real.pi*(n : ℝ)/2)| := by rw [abs_mul, abs_of_pos d_pos, abs_of_pos h_pos]
      _ ≤ d+h*1 := by gcongr; exact Real.abs_cos_le_one _
      _ = N := by rw [mul_one]; rfl
  rw [response_formula]
  simp only [abs_mul, abs_pow, abs_of_nonneg hp, abs_of_nonneg ha,
    abs_of_pos (by norm_num : (0:ℝ)<2)]
  calc
    2*p^2*a^n*|phaseResponse n| ≤ 2*p^2*1*N := by gcongr; exact pow_le_one₀ ha ha1
    _ = amplitude p := by rw [mul_one]; rfl

theorem robust_hankel_negative (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hapos : 0 < a) (f : ℕ → ℝ)
    (he : ∀ n ≤ 4, |f n-response p hp hp1 a ha ha1 n| ≤ deltaStar p a) :
    (hankel f).det ≤ -determinantMargin p a/2 ∧ (hankel f).det < 0 := by
  have hM := amplitude_pos p hpos
  have hd := deltaStar_pos p a hpos hapos
  have hdelta := deltaStar_le p a ha ha1
  have herr := hankel_error (response p hp hp1 a ha ha1) f (amplitude p) (deltaStar p a)
    hM.le hd.le (fun n _ => response_abs_le p hp hp1 a ha ha1 n) he
  have hb : 18*deltaStar p a*(amplitude p+deltaStar p a)^2 ≤
      72*(amplitude p)^2*deltaStar p a := by
    have hsum : 0 ≤ amplitude p+deltaStar p a := by positivity
    have hle : amplitude p+deltaStar p a ≤ 2*amplitude p := by linarith
    nlinarith [sq_le_sq₀ hsum (by positivity : 0 ≤ 2*amplitude p) |>.mpr hle]
  rw [deltaStar_identity] at hb
  rw [response_hankel_det] at herr
  have heq : -32*p^6*a^6*d*h^2 = -determinantMargin p a := by dsimp [determinantMargin]; ring
  rw [heq] at herr
  have hD : 0 < determinantMargin p a := by
    dsimp [determinantMargin]
    have := d_pos
    have := h_pos
    positivity
  have hu := (abs_le.mp herr).2
  constructor <;> linarith

def fiveError (f g : ℕ → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin 5)).sup' Finset.univ_nonempty (fun i => |f i.val-g i.val|)

theorem low_model_separation (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hapos : 0 < a)
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (U : V →ₗ[ℝ] V) (x : V) (ell : V →ₗ[ℝ] ℝ) (hdim : Module.finrank ℝ V ≤ 2) :
    deltaStar p a < fiveError (fun n => ell ((U^n) x)) (response p hp hp1 a ha ha1) := by
  by_contra hn
  have he : ∀ n ≤ 4, |ell ((U^n) x)-response p hp hp1 a ha ha1 n| ≤ deltaStar p a := by
    intro n hn'
    exact (Finset.le_sup' (fun i : Fin 5 => |ell ((U^i.val) x)-response p hp hp1 a ha ha1 i.val|)
      (Finset.mem_univ ⟨n,by omega⟩)).trans (le_of_not_gt hn)
  have hneg := (robust_hankel_negative p hp hp1 hpos a ha ha1 hapos _ he).2
  have hge := finrank_ge_three_of_hankel U x ell _ (ne_of_lt hneg) (fun _ _ => rfl)
  omega

theorem endpoint_budget {m : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) (L : Fin m → MatQ)
    (hL : IsKrausChannel L) (hstat : krausMap L FiniteThreeLevelPositiveHistory.rhoN =
      FiniteThreeLevelPositiveHistory.rhoN)
    (hcomm : ∀ X, Channel.heisenberg L (Psi p X) = Psi p (Channel.heisenberg L X))
    (eta : ℝ) (hres : weightedNorm (Channel.heisenberg L centeredF -
      Channel.heisenberg (FiniteThreeLevelHistoryTransfer.pulseResetKraus (a^n)
        leakingFrequencies n) centeredF) ≤ eta*Real.sqrt N)
    (khat bhat : Table) (hhat : ProbabilityTable khat) (hbase : ProbabilityTable bhat)
    (epsilon epsilon0 : ℝ) (hdata : finiteTV khat (channelTable p hp hp1 L hL) ≤ epsilon)
    (hb : finiteTV bhat baseline ≤ epsilon0) :
    |equalLabels khat-equalLabels bhat-response p hp hp1 a ha ha1 n| ≤
      amplitude p*eta+epsilon+epsilon0 := by
  have he := observed_budget p hp hp1 (a^n) (pow_nonneg ha _) (pow_le_one₀ ha ha1) n
    L hL hstat hcomm eta hres khat hhat epsilon hdata
  rw [← response_formula p hp hp1 a ha ha1 n] at he
  simpa only [errorBudget, amplitude] using
    estimated_baseline_budget khat bhat hbase epsilon0 _ _ hb he

theorem power_difference_bound (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (n : ℕ) : |b^n-a^n| ≤ n*|b-a| := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = |b*(b^n-a^n)+(b-a)*a^n| := by congr 1; rw [pow_succ, pow_succ]; ring
      _ ≤ |b*(b^n-a^n)|+|(b-a)*a^n| := abs_add_le _ _
      _ = b*|b^n-a^n|+|b-a| *a^n := by simp only [abs_mul, abs_of_nonneg hb,
          abs_pow, abs_of_nonneg ha]
      _ ≤ 1*(n*|b-a|)+|b-a| *1 := by gcongr; exact pow_le_one₀ ha ha1
      _ = (↑(n+1) : ℝ)*|b-a| := by push_cast; ring

def zeta (p a : ℝ) : ℝ := deltaStar p a/(16*amplitude p)
def theta (p a : ℝ) : ℝ := deltaStar p a/(4*amplitude p)
def xi (p a : ℝ) : ℝ := deltaStar p a/(8*amplitude p)
def changedRetention (p a : ℝ) : ℝ := a*(1-zeta p a)

theorem perturbation_parameters (p a : ℝ) (hp : 0 < p) (ha : 0 < a) (ha1 : a ≤ 1) :
    0 < zeta p a ∧ zeta p a ≤ 1/576 ∧
    0 < theta p a ∧ theta p a ≤ 1/144 ∧ 0 < xi p a ∧ xi p a ≤ 1/288 := by
  have hM := amplitude_pos p hp
  have hd := deltaStar_pos p a hp ha
  have hu := deltaStar_le p a ha.le ha1
  have hz : 0 < zeta p a := div_pos hd (by positivity)
  have ht : 0 < theta p a := div_pos hd (by positivity)
  have hx : 0 < xi p a := div_pos hd (by positivity)
  refine ⟨hz, ?_, ht, ?_, hx, ?_⟩
  · rw [zeta, div_le_iff₀ (by positivity : 0 < 16*amplitude p)]
    linarith
  · rw [theta, div_le_iff₀ (by positivity : 0 < 4*amplitude p)]
    linarith
  · rw [xi, div_le_iff₀ (by positivity : 0 < 8*amplitude p)]
    linarith

theorem changedRetention_domain (p a : ℝ) (hp : 0 < p) (ha : 0 < a) (ha1 : a ≤ 1) :
    0 < changedRetention p a ∧ changedRetention p a < a ∧ changedRetention p a ≤ 1 := by
  obtain ⟨hz,hz1,_,_,_,_⟩ := perturbation_parameters p a hp ha ha1
  have hb : 0 < changedRetention p a := mul_pos ha (by linarith)
  have hba : changedRetention p a < a := by dsimp [changedRetention]; nlinarith
  exact ⟨hb,hba,hba.le.trans ha1⟩

theorem aggregate_residual_bound (p a : ℝ) (hp : 0 < p) (ha : 0 < a) (ha1 : a ≤ 1)
    (n : ℕ) (hn : n ≤ 4) :
    |(changedRetention p a)^n-a^n| ≤ 4*zeta p a := by
  obtain ⟨hb,hba,hb1⟩ := changedRetention_domain p a hp ha ha1
  obtain ⟨hz,hz1,_,_,_,_⟩ := perturbation_parameters p a hp ha ha1
  have hd : |changedRetention p a-a| ≤ zeta p a := by
    rw [abs_of_neg (sub_neg.mpr hba)]
    dsimp [changedRetention]
    nlinarith
  calc
    _ ≤ n*|changedRetention p a-a| := power_difference_bound a _ ha.le ha1 hb.le hb1 n
    _ ≤ (4:ℝ)*zeta p a := by gcongr; exact_mod_cast hn

theorem channel_budget_small (p a : ℝ) (hp : 0 < p) (ha : 0 < a) (ha1 : a ≤ 1)
    (n : ℕ) (hn : n ≤ 4) :
    amplitude p*|(changedRetention p a)^n-a^n| ≤ deltaStar p a/4 := by
  have hM := amplitude_pos p hp
  calc
    _ ≤ amplitude p*(4*zeta p a) := mul_le_mul_of_nonneg_left
      (aggregate_residual_bound p a hp ha ha1 n hn) hM.le
    _ = deltaStar p a/4 := by dsimp [zeta]; field_simp; ring

theorem half_margin_value : deltaStar (1/2) (1/2) = d*h^2/(4608*N^2) := by
  dsimp [deltaStar]
  ring

theorem phaseResponse_ne_zero_five (n : ℕ) (hn : n ≤ 4) : phaseResponse (n : ℝ) ≠ 0 := by
  interval_cases n
  · simpa only [Nat.cast_zero, phaseResponse_zero] using ne_of_gt N_pos
  · simpa only [Nat.cast_one, phaseResponse_one] using ne_of_gt d_pos
  · simpa only [Nat.cast_ofNat, phaseResponse_two] using sub_ne_zero.mpr (ne_of_lt d_lt_h)
  · simpa only [Nat.cast_ofNat, phaseResponse_three] using ne_of_gt d_pos
  · simpa only [Nat.cast_ofNat, phaseResponse_four] using ne_of_gt N_pos

section PhysicalWitness
variable (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)

def changedEndpoint (n : ℕ) : Table :=
  endpoint p hp.le hp1 (changedRetention p a)
    (changedRetention_domain p a hp ha ha1).1.le
    (changedRetention_domain p a hp ha ha1).2.2 n

def changedData (n : ℕ) : Table := fun i j =>
  (1-theta p a)*changedEndpoint p hp hp1 a ha ha1 n i j + theta p a*baseline i j

def changedBaseline : Table := fun i j =>
  (1-xi p a)*baseline i j + xi p a*endpoint p hp.le hp1 a ha.le ha1 0 i j

include hp ha ha1

theorem dataRetention_domain (n : ℕ) :
    0 ≤ (1-theta p a)*(changedRetention p a)^n ∧
    (1-theta p a)*(changedRetention p a)^n ≤ 1 := by
  obtain ⟨_,_,ht,ht1,_,_⟩ := perturbation_parameters p a hp ha ha1
  obtain ⟨hb,_,hb1⟩ := changedRetention_domain p a hp ha ha1
  constructor
  · exact mul_nonneg (by linarith) (pow_nonneg hb.le _)
  · calc
      _ ≤ 1*1 := mul_le_mul (by linarith : 1-theta p a ≤ 1)
        (pow_le_one₀ hb.le hb1) (pow_nonneg hb.le _) (by norm_num)
      _ = 1 := one_mul _

theorem changedData_actual (n : ℕ) :
    changedData p hp hp1 a ha ha1 n =
      pulseTable p hp.le hp1 ((1-theta p a)*(changedRetention p a)^n)
        (dataRetention_domain p hp a ha ha1 n).1 (dataRetention_domain p hp a ha ha1 n).2 n := by
  funext i j
  dsimp only [changedData, changedEndpoint]
  rw [endpoint_eq_pulseTable, pulseTable_law, pulseTable_law]
  dsimp [baseline]
  ring

theorem changedBaseline_actual :
    changedBaseline p hp hp1 a ha ha1 =
      pulseTable p hp.le hp1 (xi p a) (perturbation_parameters p a hp ha ha1).2.2.2.2.1.le
        (by have ht := (perturbation_parameters p a hp ha ha1).2.2.2.2.2; linarith) 0 := by
  funext i j
  dsimp only [changedBaseline]
  rw [endpoint_law, response_zero, pulseTable_law, phaseResponse_zero]
  dsimp [baseline]
  ring

theorem changedData_probability (n : ℕ) : ProbabilityTable (changedData p hp hp1 a ha ha1 n) := by
  rw [changedData_actual]
  exact pulseTable_probability _ _ _ _ _ _ _

theorem changedBaseline_probability : ProbabilityTable (changedBaseline p hp hp1 a ha ha1) := by
  rw [changedBaseline_actual]
  exact pulseTable_probability _ _ _ _ _ _ _

theorem changedData_TV (n : ℕ) :
    finiteTV (changedData p hp hp1 a ha ha1 n) (changedEndpoint p hp hp1 a ha ha1 n) =
      theta p a * |response p hp.le hp1 (changedRetention p a)
        (changedRetention_domain p a hp ha ha1).1.le
        (changedRetention_domain p a hp ha ha1).2.2 n| := by
  have ht := (perturbation_parameters p a hp ha ha1).2.2.1
  rw [changedData_actual]
  dsimp only [changedEndpoint]
  rw [endpoint_eq_pulseTable, law_finiteTV (pulseTable_law _ _ _ _ _ _ _) (pulseTable_law _ _ _ _ _ _ _),
    response_formula]
  have he : p^2*((1-theta p a)*(changedRetention p a)^n)*phaseResponse n -
      p^2*(changedRetention p a)^n*phaseResponse n =
      -(theta p a)*(p^2*(changedRetention p a)^n*phaseResponse n) := by ring
  rw [he, abs_mul, abs_neg, abs_of_pos ht]
  rw [show 2*p^2*(changedRetention p a)^n*phaseResponse n =
    2*(p^2*(changedRetention p a)^n*phaseResponse n) by ring, abs_mul]
  norm_num
  ring

theorem changedData_error_small (n : ℕ) :
    finiteTV (changedData p hp hp1 a ha ha1 n) (changedEndpoint p hp hp1 a ha ha1 n) ≤ deltaStar p a/4 := by
  have hM := amplitude_pos p hp
  have ht := (perturbation_parameters p a hp ha ha1).2.2.1
  rw [changedData_TV]
  calc
    _ ≤ theta p a*amplitude p := mul_le_mul_of_nonneg_left
      (response_abs_le p hp.le hp1 (changedRetention p a)
        (changedRetention_domain p a hp ha ha1).1.le
        (changedRetention_domain p a hp ha ha1).2.2 n) ht.le
    _ = deltaStar p a/4 := by dsimp [theta]; field_simp

theorem changedData_error_positive (n : ℕ) (hn : n ≤ 4) :
    0 < finiteTV (changedData p hp hp1 a ha ha1 n) (changedEndpoint p hp hp1 a ha ha1 n) := by
  rw [changedData_TV, response_formula]
  have hb := (changedRetention_domain p a hp ha ha1).1
  have ht := (perturbation_parameters p a hp ha ha1).2.2.1
  apply mul_pos ht
  apply abs_pos.mpr
  exact mul_ne_zero (by positivity) (phaseResponse_ne_zero_five n hn)

theorem changedBaseline_error : finiteTV (changedBaseline p hp hp1 a ha ha1) baseline = deltaStar p a/8 := by
  have hM := amplitude_pos p hp
  have hx := (perturbation_parameters p a hp ha ha1).2.2.2.2.1
  rw [changedBaseline_actual, pulseTable_TV_baseline, phaseResponse_zero, abs_of_pos N_pos]
  change 2*p^2*xi p a*N = deltaStar p a/8
  have he : 2*p^2*xi p a*N = xi p a*amplitude p := by dsimp [amplitude]; ring
  rw [he]
  dsimp [xi]
  field_simp

theorem changedBaseline_error_positive : 0 < finiteTV (changedBaseline p hp hp1 a ha ha1) baseline := by
  rw [changedBaseline_error]
  exact div_pos (deltaStar_pos p a hp ha) (by norm_num)

theorem actual_aggregate_residual (n : ℕ) :
    weightedNorm (Channel.heisenberg (FiniteThreeLevelHistoryTransfer.pulseResetKraus
      ((changedRetention p a)^n) leakingFrequencies n) centeredF -
      Channel.heisenberg (FiniteThreeLevelHistoryTransfer.pulseResetKraus (a^n)
        leakingFrequencies n) centeredF) = |(changedRetention p a)^n-a^n| * Real.sqrt N :=
  pulse_retention_residual _ _ (pow_nonneg (changedRetention_domain p a hp ha ha1).1.le _)
    (pow_le_one₀ (changedRetention_domain p a hp ha ha1).1.le
      (changedRetention_domain p a hp ha ha1).2.2) (pow_nonneg ha.le _) (pow_le_one₀ ha.le ha1) _

theorem actual_aggregate_residual_positive (n : ℕ) (hn : n ≠ 0) :
    0 < weightedNorm (Channel.heisenberg (FiniteThreeLevelHistoryTransfer.pulseResetKraus
      ((changedRetention p a)^n) leakingFrequencies n) centeredF -
      Channel.heisenberg (FiniteThreeLevelHistoryTransfer.pulseResetKraus (a^n)
        leakingFrequencies n) centeredF) := by
  rw [actual_aggregate_residual p hp a ha ha1]
  apply mul_pos (abs_pos.mpr _) (Real.sqrt_pos.mpr N_pos)
  exact sub_ne_zero.mpr (ne_of_lt (pow_lt_pow_left₀
    (changedRetention_domain p a hp ha ha1).2.1 (changedRetention_domain p a hp ha ha1).1.le hn))

theorem actual_aggregate_residual_zero :
    weightedNorm (Channel.heisenberg (FiniteThreeLevelHistoryTransfer.pulseResetKraus
      ((changedRetention p a)^0) leakingFrequencies 0) centeredF -
      Channel.heisenberg (FiniteThreeLevelHistoryTransfer.pulseResetKraus (a^0)
        leakingFrequencies 0) centeredF) = 0 := by
  simpa only [Nat.cast_zero, pow_zero, sub_self, abs_zero, zero_mul] using
    actual_aggregate_residual p hp a ha ha1 0

theorem total_consumer_budget (n : ℕ) (hn : n ≤ 4) :
    amplitude p*|(changedRetention p a)^n-a^n| +
      finiteTV (changedData p hp hp1 a ha ha1 n) (changedEndpoint p hp hp1 a ha ha1 n) +
      finiteTV (changedBaseline p hp hp1 a ha ha1) baseline ≤ (5/8)*deltaStar p a := by
  rw [changedBaseline_error]
  linarith [channel_budget_small p a hp ha ha1 n hn, changedData_error_small p hp hp1 a ha ha1 n]

theorem changed_channel_stationary (n : ℕ) :
    krausMap (FiniteThreeLevelHistoryTransfer.pulseResetKraus ((changedRetention p a)^n)
      leakingFrequencies n) FiniteThreeLevelPositiveHistory.rhoN = FiniteThreeLevelPositiveHistory.rhoN := by
  have he := stateAction_stationary leakingFrequencies
    [⟨(changedRetention p a)^n, pow_nonneg (changedRetention_domain p a hp ha ha1).1.le _,
      pow_le_one₀ (changedRetention_domain p a hp ha ha1).1.le
        (changedRetention_domain p a hp ha ha1).2.2, n⟩]
  rw [FiniteThreeLevelHistoryTransfer.pulseReset_state _
    (pow_nonneg (changedRetention_domain p a hp ha ha1).1.le _)
    (pow_le_one₀ (changedRetention_domain p a hp ha ha1).1.le
      (changedRetention_domain p a hp ha ha1).2.2)]
  exact he

theorem changed_consumer_errors (n : ℕ) (hn : n ≤ 4) :
    |equalLabels (changedData p hp hp1 a ha ha1 n)-equalLabels (changedBaseline p hp hp1 a ha ha1)-
      response p hp.le hp1 a ha.le ha1 n| ≤ (5/8)*deltaStar p a := by
  have hb := changedRetention_domain p a hp ha ha1
  have hbn : 0 ≤ (changedRetention p a)^n := pow_nonneg hb.1.le _
  have hbn1 : (changedRetention p a)^n ≤ 1 := pow_le_one₀ hb.1.le hb.2.2
  have he := endpoint_budget p hp.le hp1 a ha.le ha1 n
    (FiniteThreeLevelHistoryTransfer.pulseResetKraus ((changedRetention p a)^n) leakingFrequencies n)
    (FiniteThreeLevelHistoryTransfer.pulseReset_normalized _ hbn hbn1 _ _)
    (changed_channel_stationary p hp a ha ha1 n)
    (FiniteThreeLevelHistoryTransfer.pulseReset_commutes _ hbn hbn1 _ _ p)
    |(changedRetention p a)^n-a^n| (le_of_eq (actual_aggregate_residual p hp a ha ha1 n))
    (changedData p hp hp1 a ha ha1 n) (changedBaseline p hp hp1 a ha ha1)
    (changedData_probability p hp hp1 a ha ha1 n) (changedBaseline_probability p hp hp1 a ha ha1)
    (finiteTV (changedData p hp hp1 a ha ha1 n) (changedEndpoint p hp hp1 a ha ha1 n))
    (finiteTV (changedBaseline p hp hp1 a ha ha1) baseline)
    (by dsimp only [changedEndpoint]; rw [endpoint_eq_pulseTable]; exact le_rfl) le_rfl
  exact he.trans (total_consumer_budget p hp hp1 a ha ha1 n hn)

theorem changed_consumer_hankel :
    (hankel (fun n => equalLabels (changedData p hp hp1 a ha ha1 n)-
      equalLabels (changedBaseline p hp hp1 a ha ha1))).det < 0 := by
  apply (robust_hankel_negative p hp.le hp1 hp a ha.le ha1 ha _ _).2
  intro n hn
  have he := changed_consumer_errors p hp hp1 a ha ha1 n hn
  have hd := deltaStar_pos p a hp ha
  linarith

end PhysicalWitness

theorem matrix_rank_zero_iff (A : Matrix (Fin 3) (Fin 3) ℝ) : A.rank = 0 ↔ A = 0 := by
  constructor
  · intro hr
    have hs : Submodule.span ℝ (Set.range A.col) = ⊥ :=
      Submodule.finrank_eq_zero.mp (by rw [← Matrix.rank_eq_finrank_span_cols]; exact hr)
    ext i j
    have hc : A.col j ∈ Submodule.span ℝ (Set.range A.col) := Submodule.subset_span ⟨j,rfl⟩
    rw [hs] at hc
    exact congrFun (show A.col j = 0 from hc) i
  · rintro rfl
    exact Matrix.rank_zero

def phaseIdentityEndpoint (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) : Table :=
  appendedTable p hp hp1 leakingFrequencies (List.replicate n ⟨a,ha,ha1,0⟩)

theorem phaseIdentity_response (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
    equalLabels (phaseIdentityEndpoint p hp hp1 a ha ha1 n)-61/72 = amplitude p*a^n := by
  have he := law_equalLabels (appendedTable_law p hp hp1 (List.replicate n ⟨a,ha,ha1,0⟩))
  rw [retention_eq_prod, totalPhase_eq_sum] at he
  simp only [List.map_replicate, List.prod_replicate, List.sum_replicate, nsmul_zero,
    phaseResponse_zero] at he
  simpa only [phaseIdentityEndpoint, amplitude, mul_assoc, mul_comm, mul_left_comm] using he

theorem geometric_hankel_factorization (M a : ℝ) :
    hankel (fun n => M*a^n) = Matrix.vecMulVec (fun i : Fin 3 => M*a^i.val) (fun j : Fin 3 => a^j.val) := by
  ext i j
  change M*a^(i.val+j.val) = (M*a^i.val)*a^j.val
  rw [pow_add]
  ring

theorem geometric_hankel_rank_le_one (M a : ℝ) : (hankel (fun n => M*a^n)).rank ≤ 1 := by
  rw [geometric_hankel_factorization]
  exact Matrix.rank_vecMulVec_le _ _

theorem geometric_hankel_rank_one (M a : ℝ) (hM : M ≠ 0) :
    (hankel (fun n => M*a^n)).rank = 1 := by
  have hu := geometric_hankel_rank_le_one M a
  have hn : (hankel (fun n => M*a^n)).rank ≠ 0 := by
    intro hz
    have he := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A 0 0) ((matrix_rank_zero_iff _).mp hz)
    simp only [hankel, Fin.val_zero, zero_add, pow_zero, mul_one, Matrix.zero_apply] at he
    exact hM he
  omega

theorem phaseIdentity_rank_controls (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (hankel (fun n => equalLabels (phaseIdentityEndpoint p hp hp1 a ha ha1 n)-61/72)).rank ≤ 1 ∧
    ((hankel (fun n => equalLabels (phaseIdentityEndpoint p hp hp1 a ha ha1 n)-61/72)).rank = 1 ↔ 0 < p) := by
  simp only [phaseIdentity_response]
  refine ⟨geometric_hankel_rank_le_one _ _, ?_⟩
  constructor
  · intro hr
    by_contra hn
    have hz : p = 0 := by linarith
    subst p
    have he : hankel (fun n => amplitude 0*a^n) = 0 := by ext i j; simp [hankel, amplitude]
    rw [he, Matrix.rank_zero] at hr
    omega
  · intro hpos
    exact geometric_hankel_rank_one _ _ (ne_of_gt (amplitude_pos p hpos))

theorem central_zero_endpoint (hp1 : (0:ℝ) ≤ 1) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
    endpoint 0 le_rfl hp1 a ha ha1 n = baseline := by
  ext i j
  rw [endpoint_law, response_formula]
  simp

theorem central_zero_hankel (hp1 : (0:ℝ) ≤ 1) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    hankel (response 0 le_rfl hp1 a ha ha1) = 0 := by
  ext i j
  simp [hankel, response_formula]

theorem zero_retention_response (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) (hn : n ≠ 0) :
    response p hp hp1 0 le_rfl (by norm_num) n = 0 := by
  rw [response_formula, zero_pow hn, mul_zero, zero_mul]

theorem zero_retention_hankel (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    hankel (response p hp hp1 0 le_rfl (by norm_num)) = hankel (fun n => amplitude p*0^n) := by
  congr 1
  funext n
  by_cases hn : n = 0
  · subst n
    simp only [response_zero, amplitude, pow_zero, mul_one]
  · simp only [zero_retention_response p hp hp1 n hn, zero_pow hn, mul_zero]

theorem zero_retention_rank_one (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p) :
    (hankel (response p hp hp1 0 le_rfl (by norm_num))).rank = 1 := by
  rw [zero_retention_hankel]
  exact geometric_hankel_rank_one _ _ (ne_of_gt (amplitude_pos p hpos))

theorem zero_retention_kernel (m : ℕ) : kappa 0 m = 0 := by
  simp [kappa, hiddenReadout]

theorem zero_retention_endpoint (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) (hn : n ≠ 0) :
    endpoint p hp hp1 0 le_rfl (by norm_num) n = baseline := by
  ext i j
  rw [endpoint_law, zero_retention_response p hp hp1 n hn]
  simp

theorem response_two_negative (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hapos : 0 < a) : response p hp hp1 a ha ha1 2 < 0 := by
  rw [response_two]
  exact mul_neg_of_pos_of_neg (by positivity) (sub_neg.mpr d_lt_h)

theorem response_four_positive (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hapos : 0 < a) : response p hp hp1 a ha ha1 4 > 0 := by
  rw [show 4 = 0+4 from rfl, response_four_step, response_zero]
  have := N_pos
  positivity

theorem damped_four_strict (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    response p hp hp1 a ha ha1.le 4 < response p hp hp1 a ha ha1.le 0 := by
  rw [show 4 = 0+4 from rfl, response_four_step, response_zero]
  have hpow : a^4 < 1 := by simpa using pow_lt_pow_left₀ ha1 ha (by norm_num : (4:ℕ) ≠ 0)
  have hM := amplitude_pos p hpos
  change a^4*amplitude p < amplitude p
  nlinarith

theorem repeated_actual_compression (p : ℝ) (hp : 0 < p) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (n : ℕ) : (((projection binaryTree p).comp (actualUpdate a))^n) centeredF =
      ((a*alpha)^n : ℂ) • centeredF := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul]
    change _ • projection binaryTree p (actualUpdate a centeredF) = _
    rw [actual_blockA p hp a ha ha1, smul_smul]
    rw [pow_succ]

theorem compressed_two_opposite_sign (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    0 < amplitude p*(a*alpha)^2 ∧ response p hp.le hp1 a ha.le ha1 2 < 0 := by
  constructor
  · have hM := amplitude_pos p hp
    have hal := alpha_pos
    positivity
  · exact response_two_negative p hp.le hp1 hp a ha.le ha1 ha

theorem compression_zero_controls (p a : ℝ) (hz : p = 0 ∨ a = 0) :
    amplitude p*(a*alpha)^2 = 0 ∧ 2*p^2*a^2*(d-h) = 0 ∧ 2*p^2*a^4*N = 0 := by
  rcases hz with rfl | rfl <;> simp [amplitude]

theorem erasure_distance (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
    finiteTV baseline (endpoint p hp hp1 a ha ha1 n) = |response p hp hp1 a ha ha1 n| := by
  rw [finiteTV_symm, endpoint_eq_pulseTable, pulseTable_TV_baseline, response_formula]
  simp only [abs_mul, abs_pow, abs_of_nonneg hp, abs_of_nonneg ha,
    abs_of_pos (by norm_num : (0:ℝ)<2)]

theorem baseline_erases_hankel : hankel (fun _ => equalLabels baseline-equalLabels baseline) = 0 := by
  ext i j
  simp [hankel]

theorem response_hankel_factorization (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    hankel (response p hp hp1 a ha ha1) = (2*p^2) •
      (Matrix.diagonal ![1,a,a^2] * !![N,d,d-h; d,d-h,d; d-h,d,N] * Matrix.diagonal ![1,a,a^2]) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hankel, response_formula, Matrix.diagonal_mul, Matrix.mul_diagonal,
      phaseResponse_zero, phaseResponse_one, phaseResponse_two, phaseResponse_three, phaseResponse_four] <;> ring

theorem attained_dimension_three : Module.finrank ℝ (Fin 3 → ℝ) = 3 := by
  simp

theorem actual_blockA_full (p : ℝ) (hp : 0 < p) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (c b : ℂ) : blockA binaryTree p (actualUpdate a) (visibleVector p hp c b) =
      visibleVector p hp c ((a*alpha : ℂ)*b) := by
  apply Subtype.ext
  change projection binaryTree p (actualUpdate a (c • 1 + b • centeredF)) = _
  rw [map_add, map_smul, map_smul, actualUpdate_one _ ha ha1, map_add, map_smul,
    map_smul, projection_one, actual_blockA p hp a ha ha1]
  change _ = c • (1 : MatQ) + _ • centeredF
  module

def actualRestrictedB (p : ℝ) (a : ℝ) : restrictedHidden p →ₗ[ℂ] accessible binaryTree p :=
  (retained binaryTree p).comp ((actualUpdate a).comp (restrictedHidden p).subtype)

def actualRestrictedC (p : ℝ) (hp : 0 < p) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    accessible binaryTree p →ₗ[ℂ] restrictedHidden p :=
  ((hiddenProjection binaryTree p).comp ((actualUpdate a).comp (accessible binaryTree p).subtype)).codRestrict _
    (fun x => ⟨closure_preserved_Q p hp
      (actualUpdate_preserves_closure a ha ha1 (accessible_le_closure p hp x.property)),
      projection_hidden binaryTree p _⟩)

theorem actual_restricted_B_matrix (p : ℝ) (hp : 0 < p) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (c e : ℂ) : actualRestrictedB p a (restrictedHiddenVector p hp c e) =
      visibleVector p hp 0 ((a : ℂ)*(alpha*(1-alpha)*c-(1-alpha)*e)) :=
  actual_blockB p hp a ha ha1 c e

theorem actual_restricted_C_matrix (p : ℝ) (hp : 0 < p) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (b : ℂ) : actualRestrictedC p hp a ha ha1 (visibleVector p hp 0 b) =
      restrictedHiddenVector p hp ((a : ℂ)*b) ((a : ℂ)*b) := by
  apply Subtype.ext
  exact congrArg (fun x : (projection binaryTree p).ker => (x : MatQ)) (actual_blockC p hp a ha ha1 b)

theorem actual_kernel_visible (p : ℝ) (hp : 0 < p) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (m : ℕ) (c b : ℂ) :
    memoryKernel binaryTree p (actualUpdate a) m (visibleVector p hp c b) =
      visibleVector p hp 0 ((kappa a m : ℂ)*b) := by
  have hv : visibleVector p hp c b = c • (⟨1,one_mem_accessible binaryTree p⟩ : accessible binaryTree p) +
      b • visibleVector p hp 0 1 := by apply Subtype.ext; simp [visibleVector]
  rw [hv, map_add, map_smul, map_smul, actual_kernel_I p a ha ha1, smul_zero, zero_add]
  apply Subtype.ext
  change b • (memoryKernel binaryTree p (actualUpdate a) m (visibleVector p hp 0 1) : MatQ) = _
  rw [actual_kernel_F p hp a ha ha1]
  change _ = (0 : ℂ) • (1 : MatQ) + _ • centeredF
  module

theorem actual_zero_kernel_operator (p : ℝ) (hp : 0 < p) (m : ℕ) :
    memoryKernel binaryTree p (actualUpdate 0) m = 0 := by
  apply LinearMap.ext
  intro x
  obtain ⟨c,b,he⟩ := binary_span_coordinates (show (x : MatQ) ∈ binarySpan by
    rw [← binary_accessible p hp]; exact x.property)
  have hx : x = visibleVector p hp c b := Subtype.ext he
  rw [hx, actual_kernel_visible p hp 0 le_rfl (by norm_num), zero_retention_kernel]
  apply Subtype.ext
  simp [visibleVector]

theorem hankel_error_linear (g f : ℕ → ℝ) (M delta : ℝ) (hM : 0 ≤ M) (hd : 0 ≤ delta)
    (hdelta : delta ≤ M) (hg : ∀ n ≤ 4, |g n| ≤ M) (he : ∀ n ≤ 4, |f n-g n| ≤ delta) :
    |(hankel f).det-(hankel g).det| ≤ 72*M^2*delta := by
  have herr := hankel_error g f M delta hM hd hg he
  have hs : (M+delta)^2 ≤ (2*M)^2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr (by linarith)
  nlinarith

theorem robust_model_dimension (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hapos : 0 < a) (f : ℕ → ℝ)
    (he : ∀ n ≤ 4, |f n-response p hp hp1 a ha ha1 n| ≤ deltaStar p a)
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (U : V →ₗ[ℝ] V) (x : V) (ell : V →ₗ[ℝ] ℝ) (hmatch : ∀ n ≤ 4, ell ((U^n) x) = f n) :
    3 ≤ Module.finrank ℝ V :=
  finrank_ge_three_of_hankel U x ell f
    (ne_of_lt (robust_hankel_negative p hp hp1 hpos a ha ha1 hapos f he).2) hmatch

theorem heterogeneous_zero_erases (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (qs : List Pulse)
    (hz : ∃ q ∈ qs, q.retention = 0) : appendedTable p hp hp1 leakingFrequencies qs = baseline := by
  have hr : retention qs = 0 := by
    rw [retention_eq_prod]
    apply List.prod_eq_zero
    obtain ⟨q,hq,hzero⟩ := hz
    exact List.mem_map.mpr ⟨q,hq,hzero⟩
  funext i j
  rw [appendedTable_law p hp hp1 qs i j, hr]
  simp [baseline]

theorem phaseIdentity_rank_zero (hp1 : (0:ℝ) ≤ 1) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (hankel (fun n => equalLabels (phaseIdentityEndpoint 0 le_rfl hp1 a ha ha1 n)-61/72)).rank = 0 := by
  apply (matrix_rank_zero_iff _).mpr
  ext i j
  simp [hankel, phaseIdentity_response, amplitude]

def phaseIdentityUpdate (a : ℝ) : MatQ →ₗ[ℂ] MatQ :=
  Channel.heisenbergLinear (FiniteThreeLevelHistoryTransfer.pulseResetKraus a leakingFrequencies 0)

theorem phaseIdentity_visible_action (p : ℝ) (hp : 0 < p) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (c b : ℂ) : phaseIdentityUpdate a (visibleVector p hp c b) =
      (visibleVector p hp c ((a : ℂ)*b) : MatQ) := by
  change Channel.heisenberg _ (c • 1 + b • centeredF) = _
  rw [Channel.heisenberg_add, Channel.heisenberg_smul, Channel.heisenberg_smul,
    Channel.heisenberg_one _ (FiniteThreeLevelHistoryTransfer.pulseReset_normalized _ ha ha1 _ _),
    pulse_centered _ ha ha1, FiniteThreeLevelHistoryTransfer.rotate_zero]
  change _ = c • (1 : MatQ) + _ • centeredF
  module

theorem phaseIdentity_visible_invariant (p : ℝ) (hp : 0 < p) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    Module.finrank ℂ (accessible binaryTree p) = 2 ∧
    ∀ x ∈ accessible binaryTree p, phaseIdentityUpdate a x ∈ accessible binaryTree p := by
  constructor
  · rw [binary_accessible p hp]
    exact binarySpan_rank
  · intro x hx
    obtain ⟨c,b,he⟩ := binary_span_coordinates (by rw [← binary_accessible p hp]; exact hx)
    rw [he]
    have hv := phaseIdentity_visible_action p hp a ha ha1 c b
    exact hv ▸ (visibleVector p hp c ((a : ℂ)*b)).property

theorem central_reset_scalar_quotient : Module.finrank ℂ
    (Reconstructed binaryTree (by decide) binary_stationary 0 (by norm_num) (by norm_num)) = 1 :=
  reset_finrank binaryTree (by decide) binary_stationary

theorem compressed_response_formula (p : ℝ) (hp : 0 < p) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (n : ℕ) : 2*p^2*(FiniteThreeLevelPositiveHistory.form centeredF
      ((((projection binaryTree p).comp (actualUpdate a))^n) centeredF)).re = amplitude p*(a*alpha)^n := by
  rw [repeated_actual_compression p hp a ha ha1,
    FiniteThreeLevelHistoryTransfer.form_smul_right, form_FF]
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_pow, Complex.ofReal_re, amplitude]
  ring

theorem actual_memory_not_eventually_zero (p : ℝ) (hp : 0 < p)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hapos : 0 < a) (L : ℕ) :
    ∃ m ≥ L, memoryKernel binaryTree p (actualUpdate a) m ≠ 0 := by
  obtain ⟨m,hm,hk⟩ := kappa_not_eventually_zero a hapos L
  refine ⟨m,hm,?_⟩
  intro hz
  have he := actual_kernel_F p hp a ha ha1 m
  rw [hz, LinearMap.zero_apply] at he
  have hsmul : (kappa a m : ℂ) • centeredF = 0 := he.symm
  have hscalar : (kappa a m : ℂ) = 0 := (smul_eq_zero.mp hsmul).resolve_right centeredF_ne_zero
  exact hk (Complex.ofReal_eq_zero.mp hscalar)

theorem arbitrary_initial_forcing_zero_count (p a : ℝ) (x : MatQ) :
    visibleOrbit binaryTree p (actualUpdate a) x 1 =
      blockA binaryTree p (actualUpdate a) (retained binaryTree p x) +
      blockB binaryTree p (actualUpdate a) (hidden binaryTree p x) := by
  simpa only [Nat.zero_add, visibleOrbit, pow_zero, Module.End.one_apply,
    Finset.range_zero, Finset.sum_empty, add_zero] using actual_visible_memory p a x 0

theorem phase_four_formula (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) : response p hp hp1 a ha ha1 4 = 2*p^2*a^4*N := by
  rw [response_formula, Nat.cast_ofNat, phaseResponse_four]

theorem no_damping_four_return (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    response p hp hp1 1 (by norm_num) (by norm_num) (n+4) =
      response p hp hp1 1 (by norm_num) (by norm_num) n := by
  rw [response_four_step, one_pow, one_mul]

theorem zero_central_rank (hp1 : (0:ℝ) ≤ 1) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (hankel (response 0 le_rfl hp1 a ha ha1)).rank = 0 := by
  rw [central_zero_hankel, Matrix.rank_zero]

theorem actual_blockC_full (p : ℝ) (hp : 0 < p) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (c b : ℂ) : blockC binaryTree p (actualUpdate a) (visibleVector p hp c b) =
      hiddenVector p hp ((a : ℂ)*b) ((a : ℂ)*b) := by
  apply Subtype.ext
  change hiddenProjection binaryTree p (actualUpdate a (c • 1 + b • centeredF)) = _
  rw [map_add, map_smul, map_smul, actualUpdate_one _ ha ha1, map_add, map_smul, map_smul,
    hidden_fixed_zero _ _ (one_mem_accessible binaryTree p), smul_zero, zero_add,
    actualUpdate_centered _ ha ha1 _ mean_F, map_smul, actual_C_F p hp]
  change _ = ((a : ℂ)*b) • hiddenG + ((a : ℂ)*b) • centeredY
  module

theorem actual_restricted_C_full_matrix (p : ℝ) (hp : 0 < p) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (c b : ℂ) : actualRestrictedC p hp a ha ha1 (visibleVector p hp c b) =
      restrictedHiddenVector p hp ((a : ℂ)*b) ((a : ℂ)*b) := by
  apply Subtype.ext
  exact congrArg (fun x : (projection binaryTree p).ker => (x : MatQ))
    (actual_blockC_full p hp a ha ha1 c b)

/-- Existing positive-p projection and compression obstructions remain in force. -/
theorem retained_projection_guard (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    ¬ (projection binaryTree p (FiniteThreeLevelPositiveHistory.D 2)).PosSemidef :=
  (projection_and_compression_guards p hp hp1).1

/-- The kernel tail is independent of the three-dimensional scalar realization bound. -/
theorem positive_domain_capstone (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    (hankel (response p hp.le hp1 a ha.le ha1)).det = -32*p^6*a^6*d*h^2 ∧
    (∀ n, modelReadout p ((modelUpdate a^n) modelInitial) = response p hp.le hp1 a ha.le ha1 n) ∧
    (∀ L, ∃ m ≥ L, memoryKernel binaryTree p (actualUpdate a) m ≠ 0) ∧
    (hankel (fun n => equalLabels (changedData p hp hp1 a ha ha1 n)-
      equalLabels (changedBaseline p hp hp1 a ha ha1))).det < 0 :=
  ⟨response_hankel_det p hp.le hp1 a ha.le ha1,
    model_attains_power p hp.le hp1 a ha.le ha1,
    actual_memory_not_eventually_zero p hp a ha.le ha1 ha,
    changed_consumer_hankel p hp hp1 a ha ha1⟩

/-- The general append law gives precisely the unread first-pulse chronology. -/
theorem first_pulse_append_run (ω : Q → ℝ) (q : Pulse) (qs : List Pulse)
    (v : History 2 1) (X : Matrix (Q × Unit) (Q × Unit) ℂ) :
    run Q Unit B (continuation ω (q::qs)) (suffixHistory (q::qs) v) X =
      run Q Unit B (continuation ω qs) (suffixHistory qs v)
        ((pulseStep ω q).branch Q Unit B (resetLabel 2 1 0) X) :=
  append_run (.node (pulseStep ω q) (fun _ => .done)) (fun _ => continuation ω qs)
    (resetLabel 2 1 0,()) (suffixHistory qs v) X

end SKEFTHawking.QuantumNetwork.FiniteThreeLevelAppendedMemoryExamples
