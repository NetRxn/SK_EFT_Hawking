import SKEFTHawking.QuantumNetwork.FiniteThreeLevelHistoryTransfer
import SKEFTHawking.QuantumNetwork.FiniteThreeLevelMemoryReadout

/-!
# Qutrit history evaluation and retained readout

The actual history coefficients encode matrix observables. An inverse-reference
sandwich represents all-complex trace evaluation in the conjugate-first inner
product. The physical retained experiment and the reflection quotient have
distinct carriers and norms.

The encoding requires positive central retention, including at either side-reset
endpoint. It does not extend arbitrary matrix coordinates to the rank-one central
reset quotient. Physical probability statements require preparation in [0,1]
and nonnegative rate and time. Physical energy-scale interpretations additionally
require positive inverse temperature and Planck scale; the algebraic definitions
at zero scale do not supply such an interpretation.

The imported positive-history and transfer controls remain in force: replacement
and Luders selected states differ; entrywise positive probabilities do not imply
positive chronology; real negative phase modes also fail positivity. Free phase
pulses are distinct from a single thermal elapsed time. Operational zero retention
is distinct from every finite positive exponential. Stationarity and the Gibbs
state do not determine a clock scale. The sandwiched metric is neither the old
one-sided metric nor physical trace distance.

This finite representation bridge makes no arbitrary-prefix adaptive reflection,
continuum reconstruction, mass-gap, calibrated-clock, entanglement advantage,
diamond-norm or universal non-Markovian claim. The optional adaptive pullback
retains control-adjoint/read-projection/observable-channel order; it is not used
to replace the physical optimization results below.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteThreeLevelHistoryReadout
open Matrix FinitePositiveKernel GibbsObservable FiniteThreeLevelPositiveHistory
open scoped BigOperators ComplexOrder Kronecker InnerProductSpace

/-- The inverse of the faithful reference square root is self-adjoint. -/
theorem Rinv_adjoint : Rinvᴴ = Rinv := by simp [Rinv]

/-- Conjugate-linear state coordinate; no positivity or faithfulness of X is needed. -/
def dualState (X : MatQ) : MatQ := Rinv * Xᴴ * Rinv

theorem dualState_adjoint (X : MatQ) : (dualState X)ᴴ = Rinv * X * Rinv := by
  simp [dualState, Matrix.conjTranspose_mul, Rinv_adjoint, Matrix.mul_assoc]

theorem dualState_add (X Y : MatQ) : dualState (X+Y) = dualState X + dualState Y := by
  simp [dualState, mul_add, add_mul]

theorem dualState_smul (z : ℂ) (X : MatQ) : dualState (z • X) = star z • dualState X := by
  simp [dualState]

theorem dualState_form (X A : MatQ) : form (dualState X) A = (A*X).trace := by
  rw [form, dualState_adjoint]
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc R Rinv, R_mul_inv, one_mul,
    Rinv_mul, mul_one]

section Encoding
variable (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
local notation "H" => Reconstructed p r hp hp1 hr hr1
local notation "coord" => coordinates p r hp hp1 hr hr1

/-- Literal coefficients of the actual reflected process, not its feature embedding. -/
def enc (A : MatQ) : H := mk _ _ (coefficients p A)

theorem enc_coordinates (hpos : 0 < p) (A : MatQ) :
    coord (enc p r hp hp1 hr hr1 A) = A := by
  rw [enc, coordinates_mk, synthesis_coefficients hpos]

theorem enc_add (hpos : 0 < p) (A B : MatQ) :
    enc p r hp hp1 hr hr1 (A+B) = enc p r hp hp1 hr hr1 A + enc p r hp hp1 hr hr1 B := by
  apply coordinates_injective p r hp hp1 hr hr1
  simp only [map_add, enc_coordinates p r hp hp1 hr hr1 hpos]

theorem enc_smul (hpos : 0 < p) (z : ℂ) (A : MatQ) :
    enc p r hp hp1 hr hr1 (z • A) = z • enc p r hp hp1 hr hr1 A := by
  apply coordinates_injective p r hp hp1 hr hr1
  simp only [map_smul, enc_coordinates p r hp hp1 hr hr1 hpos]

theorem enc_coordinate_inverse (hpos : 0 < p) (z : H) :
    enc p r hp hp1 hr hr1 (coord z) = z := by
  apply coordinates_injective p r hp hp1 hr hr1
  exact enc_coordinates p r hp hp1 hr hr1 hpos _

def eval (X A : MatQ) : ℂ :=
  ⟪enc p r hp hp1 hr hr1 (dualState X), enc p r hp hp1 hr hr1 A⟫_ℂ

/-- Both arguments are arbitrary complex matrices, including imaginary matrix units. -/
theorem eval_trace (hpos : 0 < p) (X A : MatQ) :
    eval p r hp hp1 hr hr1 X A = (A*X).trace := by
  rw [eval, FiniteThreeLevelHistoryTransfer.coordinates_inner,
    enc_coordinates p r hp hp1 hr hr1 hpos, enc_coordinates p r hp hp1 hr hr1 hpos,
    dualState_form]

def thermalEval (b ℏ γ t : ℝ) (X A : MatQ) : ℂ :=
  ⟪enc p r hp hp1 hr hr1 (dualState X),
    FiniteThreeLevelHistoryTransfer.transfer p r hp hp1 hr hr1 (Real.exp (-γ*t))
      (FiniteThreeLevelThermalPhase.frequencies b ℏ) t (enc p r hp hp1 hr hr1 A)⟫_ℂ

theorem thermal_enc (hpos : 0 < p) (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (A : MatQ) :
    FiniteThreeLevelHistoryTransfer.transfer p r hp hp1 hr hr1 (Real.exp (-γ*t))
      (FiniteThreeLevelThermalPhase.frequencies b ℏ) t (enc p r hp hp1 hr hr1 A) =
    enc p r hp hp1 hr hr1 (Channel.heisenberg
      (FiniteThreeLevelThermalPhase.channelKraus b ℏ γ t) A) := by
  apply coordinates_injective p r hp hp1 hr hr1
  rw [FiniteThreeLevelHistoryTransfer.thermal_coordinates p r hp hp1 hr hr1 b ℏ γ t hγ ht,
    enc_coordinates p r hp hp1 hr hr1 hpos, enc_coordinates p r hp hp1 hr hr1 hpos]

theorem thermalEval_propagator (hpos : 0 < p) (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (X A : MatQ) :
    thermalEval p r hp hp1 hr hr1 b ℏ γ t X A =
      (A * OpenSystems.lindbladPropagatorAction (FiniteThreeLevelThermalPhase.scaledH b ℏ)
        (FiniteThreeLevelThermalPhase.jumps γ) t X).trace := by
  rw [thermalEval, thermal_enc p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
  change eval p r hp hp1 hr hr1 X _ = _
  rw [eval_trace p r hp hp1 hr hr1 hpos, Matrix.trace_mul_comm,
    FiniteThreeLevelThermalPhase.channel_duality b ℏ γ t hγ ht, Matrix.trace_mul_comm]

theorem thermalEval_channel (hpos : 0 < p) (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (X A : MatQ) :
    thermalEval p r hp hp1 hr hr1 b ℏ γ t X A =
      (A * krausMap (FiniteThreeLevelThermalPhase.channelKraus b ℏ γ t) X).trace := by
  rw [thermalEval_propagator p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht,
    FiniteThreeLevelThermalPhase.channel_propagator b ℏ γ t hγ ht]

end Encoding
open FiniteThreeLevelMemoryReadout hiding Q MatQ R D
open FiniteAdaptiveReadoutDiscrimination FiniteAdaptiveReadoutRobustness
open FiniteThreeLevelThermalPhase hiding Q MatQ MatJoint
section Retained
variable (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
variable (hpos : 0 < p) (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
include hpos hγ ht
local notation "ev" => thermalEval p r hp hp1 hr hr1 b ℏ γ t

/-- Entry reconstruction uses the transposed matrix unit as the effect. -/
def stateFromEval (X : MatQ) : MatQ := fun i j => ev X (E j i)

theorem stateFromEval_channel (X : MatQ) :
    stateFromEval p r hp hp1 hr hr1 b ℏ γ t X = krausMap (channelKraus b ℏ γ t) X := by
  ext i j
  simp only [stateFromEval, thermalEval_channel p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht,
    E, Matrix.trace_single_mul, one_smul]

omit hγ ht in
theorem imaginary_unit_eval (i j k l : Q) :
    eval p r hp hp1 hr hr1 (Complex.I • E i j) (E k l) =
      if l=i ∧ k=j then Complex.I else 0 := by
  rw [eval_trace p r hp hp1 hr hr1 hpos]
  simp [E, Matrix.trace_single_mul, Matrix.single_apply, eq_comm]

def bornEval (rPrep φ₁ φ₂ : ℝ) (flip : Bool) (a j : Q) : ℂ :=
  ev (sigma rPrep (signalLabel flip a)) (FiniteThreeLevelMemoryReadout.R φ₁ φ₂ j)

theorem bornEval_probability (rPrep φ₁ φ₂ : ℝ) (flip : Bool) (a j : Q) :
    bornEval p r hp hp1 hr hr1 b ℏ γ t rPrep φ₁ φ₂ flip a j =
    (probability (retention rPrep γ t) (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂)
      (signalLabel flip a) j : ℂ) := by
  rw [bornEval, thermalEval_channel p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
  exact evolved_probability b ℏ γ t rPrep φ₁ φ₂ hγ ht _ _

/-- The scalar is defined by quotient evaluation before its probability formula. -/
def branchEval (rPrep φ₁ φ₂ : ℝ) (flip : Bool) (a c j : Q) : ℂ :=
  if c=0 then bornEval p r hp hp1 hr hr1 b ℏ γ t rPrep φ₁ φ₂ flip a j / 3 else 0

theorem branchEval_mass (rPrep φ₁ φ₂ : ℝ) (flip : Bool) (a c j : Q) :
    branchEval p r hp hp1 hr hr1 b ℏ γ t rPrep φ₁ φ₂ flip a c j =
    (mass (retention rPrep γ t) (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂) flip a c j : ℂ) := by
  rw [branchEval, bornEval_probability p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
  unfold mass
  split_ifs <;> simp

/-- All nine unnormalized memory matrices, including every impossible c. -/
theorem memory_matrices_eval (rPrep : ℝ) (flip : Bool) (a c : Q) :
    memoryFamily b ℏ γ t rPrep hγ ht flip (a,c,()) =
      if c=0 then (1/3:ℂ) • (GibbsMultilevelReflection.projector (0:Q) ⊗ₖ
        stateFromEval p r hp hp1 hr hr1 b ℏ γ t (sigma rPrep (signalLabel flip a))) else 0 := by
  rw [stateFromEval_channel p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
  exact memory_run b ℏ γ t rPrep hγ ht flip a c

/-- All twenty-seven unnormalized measured matrices; no conditioning is applied. -/
theorem measured_matrices_eval (rPrep φ₁ φ₂ : ℝ) (flip : Bool) (a c j : Q) :
    measuredFamily b ℏ γ t rPrep φ₁ φ₂ hγ ht flip (a,c,j,()) =
      branchEval p r hp hp1 hr hr1 b ℏ γ t rPrep φ₁ φ₂ flip a c j •
        (FiniteThreeLevelMemoryReadout.R φ₁ φ₂ j ⊗ₖ GibbsMultilevelReflection.projector (0:Q)) := by
  rw [measured_run, branchEval, bornEval,
    thermalEval_channel p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
  unfold evolved
  split_ifs <;> simp

theorem measured_traces_eval (rPrep φ₁ φ₂ : ℝ) (flip : Bool) (a c j : Q) :
    (measuredFamily b ℏ γ t rPrep φ₁ φ₂ hγ ht flip (a,c,j,())).trace =
      branchEval p r hp hp1 hr hr1 b ℏ γ t rPrep φ₁ φ₂ flip a c j := by
  rw [measured_traces, branchEval_mass p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]

theorem fixed_columns_eval (rPrep φ₁ φ₂ : ℝ) (flip rev : Bool) (h : MeasuredHist) (d : Fin 2) :
    readoutTable (decisionReadout rev) (measuredFamily b ℏ γ t rPrep φ₁ φ₂ hγ ht flip) h d =
      (if d=0 then score rev h else 1-score rev h) *
        (branchEval p r hp hp1 hr hr1 b ℏ γ t rPrep φ₁ φ₂ flip h.1 h.2.1 h.2.2.1).re := by
  rw [decision_table, branchEval_mass p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
  rfl

theorem optimized_columns_eval (rPrep φ₁ φ₂ : ℝ) (flip : Bool) (h : MeasuredHist) (d : Fin 2) :
    readoutTable (optimalDecisionReadout (retention rPrep γ t)
      (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂))
      (measuredFamily b ℏ γ t rPrep φ₁ φ₂ hγ ht flip) h d =
      (if d=0 then optimalScore (retention rPrep γ t)
        (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂) h else
        1-optimalScore (retention rPrep γ t) (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂) h) *
        (branchEval p r hp hp1 hr hr1 b ℏ γ t rPrep φ₁ φ₂ flip h.1 h.2.1 h.2.2.1).re := by
  rw [optimal_decision_table, branchEval_mass p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
  rfl

omit hpos hγ ht in
/-- Both nonzero signal arms are derived from the actual P0-P1. -/
theorem signal_decomposition :
    FiniteThreeLevelMemoryReadout.D = (3/5:ℂ) • X 0 1 + (4/5:ℂ) • X 0 2 := by
  rw [D_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [X,E,Matrix.single_apply,Fin.ext_iff]

def dualD : MatQ := dualState FiniteThreeLevelMemoryReadout.D

omit hpos hγ ht in
theorem signal_adjoint : (FiniteThreeLevelMemoryReadout.D)ᴴ =
    FiniteThreeLevelMemoryReadout.D := by
  simp [FiniteThreeLevelMemoryReadout.D, (P_hermitian 0).eq, (P_hermitian 1).eq]

/-- J is the actual quotient pairing, not a definition by its closed scalar value. -/
def Jcomplex (φ₁ φ₂ : ℝ) : ℂ :=
  ev FiniteThreeLevelMemoryReadout.D (rotate φ₁ φ₂ FiniteThreeLevelMemoryReadout.D)

def Jreal (φ₁ φ₂ : ℝ) : ℝ := (Jcomplex p r hp hp1 hr hr1 b ℏ γ t φ₁ φ₂).re

omit hpos hγ ht in
theorem Jcomplex_pairing (φ₁ φ₂ : ℝ) :
    Jcomplex p r hp hp1 hr hr1 b ℏ γ t φ₁ φ₂ =
      ⟪enc p r hp hp1 hr hr1 dualD,
        FiniteThreeLevelHistoryTransfer.transfer p r hp hp1 hr hr1 (Real.exp (-γ*t))
          (frequencies b ℏ) t (enc p r hp hp1 hr hr1
            (rotate φ₁ φ₂ FiniteThreeLevelMemoryReadout.D))⟫_ℂ := rfl

theorem Jcomplex_trace (φ₁ φ₂ : ℝ) :
    Jcomplex p r hp hp1 hr hr1 b ℏ γ t φ₁ φ₂ =
      (rotate φ₁ φ₂ FiniteThreeLevelMemoryReadout.D *
        krausMap (channelKraus b ℏ γ t) FiniteThreeLevelMemoryReadout.D).trace :=
  thermalEval_channel p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht _ _

theorem Jcomplex_formula (φ₁ φ₂ : ℝ) :
    Jcomplex p r hp hp1 hr hr1 b ℏ γ t φ₁ φ₂ =
      ((2*Real.exp (-γ*t)*contrast (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂):ℝ):ℂ) := by
  have hd : krausMap (channelKraus b ℏ γ t) FiniteThreeLevelMemoryReadout.D =
      evolved b ℏ γ t 1 0 - evolved b ℏ γ t 1 1 := by
    simp [evolved, sigma, mixture, FiniteThreeLevelMemoryReadout.D, krausMap,
      mul_sub, sub_mul, Finset.sum_sub_distrib]
  have hf : rotate φ₁ φ₂ FiniteThreeLevelMemoryReadout.D =
      FiniteThreeLevelMemoryReadout.R φ₁ φ₂ 0 - FiniteThreeLevelMemoryReadout.R φ₁ φ₂ 1 := by
    ext i j
    simp [rotate_entry, FiniteThreeLevelMemoryReadout.R, FiniteThreeLevelMemoryReadout.D, mul_sub]
  rw [Jcomplex_trace p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht, hd, hf]
  simp only [sub_mul, mul_sub, Matrix.trace_sub,
    evolved_probability b ℏ γ t 1 φ₁ φ₂ hγ ht]
  norm_num [probability, signalOverlap, gibbsProbability, retention]
  ring

theorem Jreal_formula (φ₁ φ₂ : ℝ) :
    Jreal p r hp hp1 hr hr1 b ℏ γ t φ₁ φ₂ =
      2*Real.exp (-γ*t)*contrast (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂) := by
  rw [Jreal, Jcomplex_formula p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
  rfl

theorem Jcomplex_real (φ₁ φ₂ : ℝ) :
    (Jcomplex p r hp hp1 hr hr1 b ℏ γ t φ₁ φ₂).im = 0 := by
  rw [Jcomplex_formula p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
  rfl

theorem Jmatched :
    Jreal p r hp hp1 hr hr1 b ℏ γ t (theta₁ b ℏ t) (theta₂ b ℏ t) =
      2*Real.exp (-γ*t) := by
  rw [Jreal_formula p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
  norm_num [contrast]

theorem measured_distance_eval (rPrep φ₁ φ₂ : ℝ) (hPrep : 0 ≤ rPrep) :
    branchDistance (measuredFamily b ℏ γ t rPrep φ₁ φ₂ hγ ht false)
      (measuredFamily b ℏ γ t rPrep φ₁ φ₂ hγ ht true) =
      rPrep * |Jreal p r hp hp1 hr hr1 b ℏ γ t φ₁ φ₂| / 3 := by
  rw [measured_distance b ℏ γ t φ₁ φ₂ hγ ht hPrep,
    Jreal_formula p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht,
    abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  norm_num [retention]
  ring

theorem memory_distance_eval (rPrep : ℝ) (hPrep : 0 ≤ rPrep) :
    branchDistance (memoryFamily b ℏ γ t rPrep hγ ht false)
      (memoryFamily b ℏ γ t rPrep hγ ht true) =
      rPrep * Jreal p r hp hp1 hr hr1 b ℏ γ t (theta₁ b ℏ t) (theta₂ b ℏ t) / 3 := by
  rw [memory_distance b ℏ γ t hγ ht hPrep, Jmatched p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
  unfold retention
  ring

theorem measured_minimum_value (rPrep φ₁ φ₂ : ℝ) :
    1/2-rPrep*|Jreal p r hp hp1 hr hr1 b ℏ γ t φ₁ φ₂|/6 =
      1/2-retention rPrep γ t*|contrast (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂)|/3 := by
  rw [Jreal_formula p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht,
    abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  norm_num [retention]
  ring

theorem memory_minimum_value (rPrep : ℝ) :
    1/2-rPrep*Jreal p r hp hp1 hr hr1 b ℏ γ t (theta₁ b ℏ t) (theta₂ b ℏ t)/6 =
      1/2-retention rPrep γ t/3 := by
  rw [Jmatched p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
  unfold retention
  ring

/-- The domain contains every history-dependent normalized binary physical instrument. -/
theorem measured_physical_minimum_eval (rPrep φ₁ φ₂ : ℝ) (hPrep : 0 ≤ rPrep) (hPrep1 : rPrep ≤ 1) :
    IsLeast (FiniteThreeLevelEnvironmentLift.PhysicalErrors
      (measuredFamily b ℏ γ t rPrep φ₁ φ₂ hγ ht false)
      (measuredFamily b ℏ γ t rPrep φ₁ φ₂ hγ ht true))
      (1/2-rPrep*|Jreal p r hp hp1 hr hr1 b ℏ γ t φ₁ φ₂|/6) := by
  rw [measured_minimum_value p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
  exact measured_physical_isLeast b ℏ γ t φ₁ φ₂ hγ ht hPrep hPrep1

theorem memory_physical_minimum_eval (rPrep : ℝ) (hPrep : 0 ≤ rPrep) (hPrep1 : rPrep ≤ 1) :
    IsLeast (FiniteThreeLevelEnvironmentLift.PhysicalErrors
      (memoryFamily b ℏ γ t rPrep hγ ht false) (memoryFamily b ℏ γ t rPrep hγ ht true))
      (1/2-rPrep*Jreal p r hp hp1 hr hr1 b ℏ γ t (theta₁ b ℏ t) (theta₂ b ℏ t)/6) := by
  rw [memory_minimum_value p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
  exact memory_physical_isLeast b ℏ γ t hγ ht hPrep hPrep1

theorem measured_universal_lower_bound (rPrep φ₁ φ₂ : ℝ) (hPrep : 0 ≤ rPrep) (hPrep1 : rPrep ≤ 1)
    (I : MeasuredHist → FiniteInstrument Joint 2) :
    1/2-rPrep*|Jreal p r hp hp1 hr hr1 b ℏ γ t φ₁ φ₂|/6 ≤
      instrumentError (measuredFamily b ℏ γ t rPrep φ₁ φ₂ hγ ht false)
        (measuredFamily b ℏ γ t rPrep φ₁ φ₂ hγ ht true) I :=
  (measured_physical_minimum_eval p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht rPrep φ₁ φ₂ hPrep hPrep1).2
    ⟨I,rfl⟩

theorem memory_universal_lower_bound (rPrep : ℝ) (hPrep : 0 ≤ rPrep) (hPrep1 : rPrep ≤ 1)
    (I : MemoryHist → FiniteInstrument Joint 2) :
    1/2-rPrep*Jreal p r hp hp1 hr hr1 b ℏ γ t (theta₁ b ℏ t) (theta₂ b ℏ t)/6 ≤
      instrumentError (memoryFamily b ℏ γ t rPrep hγ ht false)
        (memoryFamily b ℏ γ t rPrep hγ ht true) I :=
  (memory_physical_minimum_eval p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht rPrep hPrep hPrep1).2
    ⟨I,rfl⟩

theorem measured_attainer_eval (rPrep φ₁ φ₂ : ℝ) (hPrep : 0 ≤ rPrep) (hPrep1 : rPrep ≤ 1) :
    instrumentError (measuredFamily b ℏ γ t rPrep φ₁ φ₂ hγ ht false)
      (measuredFamily b ℏ γ t rPrep φ₁ φ₂ hγ ht true)
      (optimalDecisionReadout (retention rPrep γ t) (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂)) =
      1/2-rPrep*|Jreal p r hp hp1 hr hr1 b ℏ γ t φ₁ φ₂|/6 := by
  rw [measured_minimum_value p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
  exact measured_attainer b ℏ γ t rPrep φ₁ φ₂ hγ ht hPrep hPrep1

theorem memory_grouped_attainer_eval (rPrep : ℝ) (hPrep : 0 ≤ rPrep) (hPrep1 : rPrep ≤ 1) :
    instrumentError (memoryFamily b ℏ γ t rPrep hγ ht false) (memoryFamily b ℏ γ t rPrep hγ ht true)
      (groupedReadout (theta₁ b ℏ t) (theta₂ b ℏ t) false) =
      1/2-rPrep*Jreal p r hp hp1 hr hr1 b ℏ γ t (theta₁ b ℏ t) (theta₂ b ℏ t)/6 := by
  rw [memory_minimum_value p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
  exact memory_named_attainer b ℏ γ t rPrep hγ ht hPrep hPrep1

theorem memory_sequential_attainer_eval (rPrep : ℝ) (hPrep : 0 ≤ rPrep) (hPrep1 : rPrep ≤ 1) :
    instrumentError (memoryFamily b ℏ γ t rPrep hγ ht false) (memoryFamily b ℏ γ t rPrep hγ ht true)
      (sequentialReadout (theta₁ b ℏ t) (theta₂ b ℏ t) false) =
      1/2-rPrep*Jreal p r hp hp1 hr hr1 b ℏ γ t (theta₁ b ℏ t) (theta₂ b ℏ t)/6 := by
  rw [memory_minimum_value p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
  exact memory_sequential_attainer b ℏ γ t rPrep hγ ht hPrep hPrep1
end Retained
theorem reference_sandwich_entry (A : MatQ) (i j : Q) :
    (FiniteThreeLevelPositiveHistory.R * A * FiniteThreeLevelPositiveHistory.R) i j =
      (metricWeight i j : ℂ)*A i j := by
  simp only [FiniteThreeLevelPositiveHistory.R, Matrix.mul_diagonal, Matrix.diagonal_mul,
    ← rdiag_product, Complex.ofReal_mul]
  ring

theorem dualD_decomposition :
    dualD = ((3*Real.sqrt 6/5:ℝ):ℂ) • X 0 1 +
      ((8*Real.sqrt 3/5:ℝ):ℂ) • X 0 2 := by
  let T : MatQ := ((3*Real.sqrt 6/5:ℝ):ℂ) • X 0 1 +
      ((8*Real.sqrt 3/5:ℝ):ℂ) • X 0 2
  have hs : FiniteThreeLevelPositiveHistory.R*T*FiniteThreeLevelPositiveHistory.R =
      FiniteThreeLevelMemoryReadout.D := by
    rw [D_entries]
    ext i j
    rw [reference_sandwich_entry]
    fin_cases i <;> fin_cases j <;>
      norm_num [T, metricWeight, X, E, Matrix.single_apply, Fin.ext_iff]
    all_goals ring_nf
    all_goals norm_num [← Complex.ofReal_pow, Real.sq_sqrt]
  change Rinv * (FiniteThreeLevelMemoryReadout.D)ᴴ * Rinv = T
  rw [signal_adjoint, ← hs]
  simp only [← Matrix.mul_assoc, Rinv_mul, one_mul]
  simp only [Matrix.mul_assoc, R_mul_inv, mul_one]

theorem signal_metric :
    form FiniteThreeLevelMemoryReadout.D FiniteThreeLevelMemoryReadout.D =
      ((3*Real.sqrt 6/25+16*Real.sqrt 3/75:ℝ):ℂ) := by
  rw [form_entries, D_entries]
  norm_num [metricWeight, Fin.sum_univ_three]
  push_cast
  norm_num [map_ofNat, map_inv₀]
  ring

theorem dualD_metric :
    form dualD dualD = ((18*Real.sqrt 6/25+64*Real.sqrt 3/25:ℝ):ℂ) := by
  rw [form_entries, dualD_decomposition]
  norm_num [metricWeight, X, E, Matrix.single_apply, Fin.ext_iff, Fin.sum_univ_three]
  push_cast
  ring_nf
  have h6 : (Real.sqrt 6 : ℂ)^3 = 6*(Real.sqrt 6 : ℂ) := by
    norm_cast
    rw [pow_succ, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 6)]
  have h3 : (Real.sqrt 3 : ℂ)^3 = 3*(Real.sqrt 3 : ℂ) := by
    norm_cast
    rw [pow_succ, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  rw [h6,h3]
  norm_num [map_ofNat, map_inv₀]
  ring

theorem dualD_signal_metric : form dualD FiniteThreeLevelMemoryReadout.D = 2 := by
  rw [dualD, dualState_form, D_entries]
  norm_num [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ]
/-- Complete three-by-three table, including the Gibbs dark row and 12-gap overlap. -/
def Wtable (q d₁ d₂ : ℝ) : Matrix Q Q ℝ :=
  !![(1-q)*109/300+q*Complex.normSq (1+W d₁ d₂)/4,
      (1-q)*109/300+q*Complex.normSq (1-W d₁ d₂)/4,
      (1-q)*41/150+q*(1-Complex.normSq (W d₁ d₂))/2;
     (1-q)*109/300+q*Complex.normSq (1-W d₁ d₂)/4,
      (1-q)*109/300+q*Complex.normSq (1+W d₁ d₂)/4,
      (1-q)*41/150+q*(1-Complex.normSq (W d₁ d₂))/2;
     109/300,109/300,41/150]

theorem probability_Wtable (q d₁ d₂ : ℝ) (a j : Q) :
    probability q d₁ d₂ a j = Wtable q d₁ d₂ a j := by
  have hw := full_W_probabilities d₁ d₂
  fin_cases a <;> fin_cases j <;>
    norm_num [probability, gibbsProbability, Wtable, hw.1, hw.2.1, hw.2.2] <;> ring

theorem theta_gap01 (b ℏ t : ℝ) :
    theta₁ b ℏ t = FiniteThreeLevelHistoryTransfer.gap01 b ℏ t := by
  simp only [theta₁, FiniteThreeLevelHistoryTransfer.gap01, delta, div_eq_mul_inv, _root_.mul_inv_rev]
  ring

theorem theta_gap02 (b ℏ t : ℝ) :
    theta₂ b ℏ t = FiniteThreeLevelHistoryTransfer.gap02 b ℏ t := by
  simp only [theta₂, FiniteThreeLevelHistoryTransfer.gap02, div_eq_mul_inv, _root_.mul_inv_rev]
  ring

theorem relative_gap12 (b ℏ t φ₁ φ₂ : ℝ) :
    (theta₁ b ℏ t-φ₁)-(theta₂ b ℏ t-φ₂) =
      -FiniteThreeLevelHistoryTransfer.gap12 b ℏ t+(φ₂-φ₁) := by
  rw [theta_gap01, theta_gap02, FiniteThreeLevelHistoryTransfer.gaps_tied]
  ring

/-- The literal negative-exponent convention is retained alongside its real invariants. -/
theorem W_physical_gap (b ℏ t φ₁ φ₂ : ℝ) :
    W (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂) =
      (9/25:ℂ)*Complex.exp (-(Complex.I*(theta₁ b ℏ t-φ₁))) +
      (16/25:ℂ)*Complex.exp (-(Complex.I*(theta₂ b ℏ t-φ₂))) ∧
    Complex.normSq (W (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂)) =
      337/625+288/625*Real.cos (-FiniteThreeLevelHistoryTransfer.gap12 b ℏ t+(φ₂-φ₁)) ∧
    darkOverlap (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂) =
      144/625*(1-Real.cos (-FiniteThreeLevelHistoryTransfer.gap12 b ℏ t+(φ₂-φ₁))) := by
  refine ⟨by simp only [W, Complex.ofReal_sub], ?_, ?_⟩
  · rw [W_normSq, relative_gap12]
  · rw [darkOverlap, relative_gap12]

section Tables
variable (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
variable (hpos : 0 < p) (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
include hpos hγ ht
local notation "ev" => thermalEval p r hp hp1 hr hr1 b ℏ γ t
local notation "be" => branchEval p r hp hp1 hr hr1 b ℏ γ t

theorem all_branch_Wtable (rPrep φ₁ φ₂ : ℝ) (flip : Bool) (a c j : Q) :
    be rPrep φ₁ φ₂ flip a c j =
      if c=0 then ((Wtable (retention rPrep γ t) (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂)
        (signalLabel flip a) j / 3 : ℝ):ℂ) else 0 := by
  rw [branchEval_mass p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
  unfold mass
  rw [probability_Wtable]
  split_ifs <;> simp

def binaryEffect (φ₁ φ₂ : ℝ) (rev : Bool) (a : Q) (d : Fin 2) : MatQ :=
  if d=0 then groupProjection φ₁ φ₂ rev a else 1-groupProjection φ₁ φ₂ rev a

theorem grouped_eval_scalar (rPrep φ₁ φ₂ : ℝ) (flip rev : Bool) (a : Q) (d : Fin 2) :
    (ev (sigma rPrep (signalLabel flip a)) (binaryEffect φ₁ φ₂ rev a d)).re =
      if d=0 then (if a.val=2 then 1 else 1-probability (retention rPrep γ t)
        (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂) (signalLabel flip a) (rejected rev a))
      else (if a.val=2 then 0 else probability (retention rPrep γ t)
        (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂) (signalLabel flip a) (rejected rev a)) := by
  rw [thermalEval_channel p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
  change (binaryEffect φ₁ φ₂ rev a d * evolved b ℏ γ t rPrep (signalLabel flip a)).trace.re = _
  unfold binaryEffect groupProjection
  split_ifs <;>
    simp [sub_mul, Matrix.trace_sub, evolved_trace b ℏ γ t rPrep hγ ht,
      evolved_probability b ℏ γ t rPrep φ₁ φ₂ hγ ht]

theorem grouped_columns_eval (rPrep φ₁ φ₂ : ℝ) (flip rev : Bool) (a c : Q) (d : Fin 2) :
    readoutTable (groupedReadout φ₁ φ₂ rev) (memoryFamily b ℏ γ t rPrep hγ ht flip) (a,c,()) d =
      if c=0 then (ev (sigma rPrep (signalLabel flip a)) (binaryEffect φ₁ φ₂ rev a d)).re/3 else 0 := by
  rw [grouped_table, grouped_eval_scalar p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
  unfold groupedMass
  split_ifs <;> simp_all
  ring

theorem sequential_columns_eval (rPrep φ₁ φ₂ : ℝ) (flip rev : Bool) (a c : Q) (d : Fin 2) :
    readoutTable (sequentialReadout φ₁ φ₂ rev) (memoryFamily b ℏ γ t rPrep hγ ht flip) (a,c,()) d =
      if c=0 then (ev (sigma rPrep (signalLabel flip a)) (binaryEffect φ₁ φ₂ rev a d)).re/3 else 0 := by
  change (sequentialReadout φ₁ φ₂ rev (a,c,())).weight d _ = _
  rw [sequential_grouped_weights]
  exact grouped_columns_eval p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht rPrep φ₁ φ₂ flip rev a c d

theorem sequential_measured_eval (rPrep φ₁ φ₂ : ℝ) (flip rev : Bool) (a c : Q) (d : Fin 2) :
    readoutTable (sequentialReadout φ₁ φ₂ rev) (memoryFamily b ℏ γ t rPrep hγ ht flip) (a,c,()) d =
      ∑ j, (if d=0 then score rev (a,c,j,()) else 1-score rev (a,c,j,())) *
        (be rPrep φ₁ φ₂ flip a c j).re := by
  rw [sequential_measured_decision_table]
  apply Finset.sum_congr rfl
  intro j _
  exact fixed_columns_eval p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht rPrep φ₁ φ₂ flip rev _ d

theorem optimal_equal_eval_ties (rPrep φ₁ φ₂ : ℝ) (a c j : Q)
    (heq : (be rPrep φ₁ φ₂ false a c j).re = (be rPrep φ₁ φ₂ true a c j).re) (flip : Bool) :
    readoutTable (optimalDecisionReadout (retention rPrep γ t)
      (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂))
      (measuredFamily b ℏ γ t rPrep φ₁ φ₂ hγ ht flip) (a,c,j,()) 0 =
        (be rPrep φ₁ φ₂ flip a c j).re ∧
    readoutTable (optimalDecisionReadout (retention rPrep γ t)
      (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂))
      (measuredFamily b ℏ γ t rPrep φ₁ φ₂ hγ ht flip) (a,c,j,()) 1 = 0 := by
  have he : (measuredFamily b ℏ γ t rPrep φ₁ φ₂ hγ ht false (a,c,j,())).trace.re =
      (measuredFamily b ℏ γ t rPrep φ₁ φ₂ hγ ht true (a,c,j,())).trace.re := by
    simpa only [measured_traces_eval p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht] using heq
  have hh := optimal_actual_tie_columns b ℏ γ t rPrep φ₁ φ₂ hγ ht (a,c,j,()) he flip
  simpa only [measured_traces_eval p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht] using hh

theorem optimal_degenerate_eval (rPrep φ₁ φ₂ : ℝ)
    (hzero : retention rPrep γ t*contrast (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂)=0)
    (flip : Bool) (a c j : Q) (d : Fin 2) :
    readoutTable (optimalDecisionReadout (retention rPrep γ t)
      (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂))
      (measuredFamily b ℏ γ t rPrep φ₁ φ₂ hγ ht flip) (a,c,j,()) d =
      if d=0 then (be rPrep φ₁ φ₂ flip a c j).re else 0 := by
  rw [optimal_degenerate_table b ℏ γ t rPrep φ₁ φ₂ hγ ht hzero,
    branchEval_mass p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
  rfl

end Tables
open FiniteInterventionProcess
section Controls
variable (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
variable (hpos : 0 < p) (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
include hpos hγ ht
local notation "be" => branchEval p r hp hp1 hr hr1 b ℏ γ t

/-- Both hypotheses run through the same Keep tree on their respective initial states. -/
def initialState (rPrep : ℝ) (flip : Bool) : MatJoint := if flip then rhoF rPrep else input rPrep

theorem common_memory_eval (rPrep : ℝ) (flip : Bool) (a c : Q) :
    run Q Q 3 (memoryTree b ℏ γ t hγ ht false) (a,c,()) (initialState rPrep flip) =
      if c=0 then (1/3:ℂ) • (GibbsMultilevelReflection.projector (0:Q) ⊗ₖ
        stateFromEval p r hp hp1 hr hr1 b ℏ γ t (sigma rPrep (signalLabel flip a))) else 0 := by
  have hc : run Q Q 3 (memoryTree b ℏ γ t hγ ht false) (a,c,()) (initialState rPrep flip) =
      memoryFamily b ℏ γ t rPrep hγ ht flip (a,c,()) := by
    cases flip
    · rfl
    · exact memory_common_input b ℏ γ t rPrep hγ ht _
  rw [hc, memory_matrices_eval p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]

theorem common_measured_eval (rPrep φ₁ φ₂ : ℝ) (flip : Bool) (a c j : Q) :
    run Q Q 3 (measuredTree b ℏ γ t φ₁ φ₂ hγ ht false) (a,c,j,()) (initialState rPrep flip) =
      be rPrep φ₁ φ₂ flip a c j •
        (FiniteThreeLevelMemoryReadout.R φ₁ φ₂ j ⊗ₖ GibbsMultilevelReflection.projector (0:Q)) := by
  have hc : run Q Q 3 (measuredTree b ℏ γ t φ₁ φ₂ hγ ht false) (a,c,j,()) (initialState rPrep flip) =
      measuredFamily b ℏ γ t rPrep φ₁ φ₂ hγ ht flip (a,c,j,()) := by
    cases flip
    · rfl
    · exact measured_common_input b ℏ γ t rPrep φ₁ φ₂ hγ ht _
  rw [hc, measured_matrices_eval p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]

omit hpos hγ ht in
theorem initialState_marginals (rPrep : ℝ) (flip : Bool) :
    FiniteThreeLevelEnvironmentLift.ptrace2 (initialState rPrep flip) = (1/3:ℂ) • (1:MatQ) ∧
    FiniteThreeLevelEnvironmentLift.ptrace2 (FiniteThreeLevelEnvironmentLift.swap (initialState rPrep flip)) =
      (1/3:ℂ) • ∑ a : Q, sigma rPrep a := by
  cases flip
  · exact ⟨input_initial_S_marginal _,input_initial_E_marginal _⟩
  · exact ⟨rhoF_initial_S_marginal _,rhoF_initial_E_marginal _⟩

omit hγ ht in
theorem commutator_evaluation (rPrep : ℝ) :
    eval p r hp hp1 hr hr1 (sigma rPrep 0*sigma rPrep 1-sigma rPrep 1*sigma rPrep 0) (E 1 0) =
      ((-rPrep*(1-rPrep)/10:ℝ):ℂ) ∧
    eval p r hp hp1 hr hr1 (sigma rPrep 0*sigma rPrep 1-sigma rPrep 1*sigma rPrep 0) (E 2 0) =
      ((-4*rPrep*(1-rPrep)/15:ℝ):ℂ) ∧
    (initialState rPrep false*initialState rPrep true-initialState rPrep true*initialState rPrep false)
      (0,0) (0,1) = ((-rPrep*(1-rPrep)/90:ℝ):ℂ) ∧
    (initialState rPrep false*initialState rPrep true-initialState rPrep true*initialState rPrep false)
      (0,0) (0,2) = ((-4*rPrep*(1-rPrep)/135:ℝ):ℂ) := by
  simp only [eval_trace p r hp hp1 hr hr1 hpos, E, Matrix.trace_single_mul, one_smul]
  exact ⟨signal_commutator_01 _,signal_commutator_02 _,initial_commutator_01 _,initial_commutator_02 _⟩

omit hγ ht in
theorem common_coherence_evaluation (rPrep : ℝ) :
    eval p r hp hp1 hr hr1 (sigma rPrep 0) (E 2 1) = ((6*rPrep/25:ℝ):ℂ) ∧
    eval p r hp hp1 hr hr1 (sigma rPrep 1) (E 2 1) = ((6*rPrep/25:ℝ):ℂ) := by
  simp only [eval_trace p r hp hp1 hr hr1 hpos, E, Matrix.trace_single_mul, one_smul]
  exact common_twelve_coherence _

omit hpos in
theorem impossible_branch_eval (rPrep φ₁ φ₂ : ℝ) (flip : Bool) (a c j : Q) (hc : c ≠ 0) :
    be rPrep φ₁ φ₂ flip a c j = 0 ∧
    memoryFamily b ℏ γ t rPrep hγ ht flip (a,c,()) = 0 ∧
    measuredFamily b ℏ γ t rPrep φ₁ φ₂ hγ ht flip (a,c,j,()) = 0 := by
  refine ⟨by simp [branchEval,hc], ?_, ?_⟩
  · exact impossible_memory_zero b ℏ γ t rPrep hγ ht flip (a,c,()) hc
  · exact impossible_measured_zero b ℏ γ t rPrep φ₁ φ₂ hγ ht flip (a,c,j,()) hc

theorem zero_J_erases_measured (rPrep φ₁ φ₂ : ℝ)
    (hJ : Jreal p r hp hp1 hr hr1 b ℏ γ t φ₁ φ₂ = 0) :
    measuredFamily b ℏ γ t rPrep φ₁ φ₂ hγ ht false =
      measuredFamily b ℏ γ t rPrep φ₁ φ₂ hγ ht true := by
  apply destructive_erasure b ℏ γ t rPrep φ₁ φ₂ hγ ht
  rw [Jreal_formula p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht] at hJ
  exact (mul_eq_zero.mp hJ).resolve_left (mul_ne_zero (by norm_num) (ne_of_gt (Real.exp_pos _)))

theorem positive_memory_after_zero_J (rPrep φ₁ φ₂ : ℝ) (hPrep : 0 < rPrep)
    (hJ : Jreal p r hp hp1 hr hr1 b ℏ γ t φ₁ φ₂ = 0) :
    measuredFamily b ℏ γ t rPrep φ₁ φ₂ hγ ht false =
      measuredFamily b ℏ γ t rPrep φ₁ φ₂ hγ ht true ∧
    0 < branchDistance (memoryFamily b ℏ γ t rPrep hγ ht false)
      (memoryFamily b ℏ γ t rPrep hγ ht true) := by
  refine ⟨zero_J_erases_measured p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht rPrep φ₁ φ₂ hJ, ?_⟩
  rw [memory_distance_eval p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht rPrep hPrep.le,
    Jmatched p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
  positivity

theorem pure_evaluation_faithfulness (hγpos : 0 < γ) (htpos : 0 < t) (a : Q) :
    (stateFromEval p r hp hp1 hr hr1 b ℏ γ t (sigma 1 a)).PosDef ∧
      ¬(P a).PosDef := by
  rw [stateFromEval_channel p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
  exact ⟨pure_signal_restored_faithful b ℏ γ t hγpos htpos a, P_not_faithful a⟩

theorem represented_branches_singular (rPrep φ₁ φ₂ : ℝ) (flip : Bool) (a c j : Q) :
    ¬(if c=0 then (1/3:ℂ) • (GibbsMultilevelReflection.projector (0:Q) ⊗ₖ
      stateFromEval p r hp hp1 hr hr1 b ℏ γ t (sigma rPrep (signalLabel flip a))) else 0).PosDef ∧
    ¬(be rPrep φ₁ φ₂ flip a c j •
      (FiniteThreeLevelMemoryReadout.R φ₁ φ₂ j ⊗ₖ GibbsMultilevelReflection.projector (0:Q))).PosDef := by
  rw [← memory_matrices_eval p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht,
    ← measured_matrices_eval p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
  exact ⟨memory_joint_not_faithful b ℏ γ t rPrep hγ ht flip a c,
    measured_joint_not_faithful b ℏ γ t rPrep φ₁ φ₂ hγ ht flip a c j⟩

theorem represented_environment_reset (rPrep : ℝ) (flip : Bool) (a c : Q) :
    FiniteThreeLevelEnvironmentLift.gibbsReset
      (if c=0 then (1/3:ℂ) • (GibbsMultilevelReflection.projector (0:Q) ⊗ₖ
        stateFromEval p r hp hp1 hr hr1 b ℏ γ t (sigma rPrep (signalLabel flip a))) else 0) =
      if c=0 then (1/3:ℂ) • (GibbsMultilevelReflection.projector (0:Q) ⊗ₖ equilibrium) else 0 := by
  rw [← memory_matrices_eval p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
  exact actual_E_reset_memory b ℏ γ t rPrep hγ ht flip a c

end Controls

section CompleteFamilies
variable (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
variable (hpos : 0 < p) (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
include hpos hγ ht
local notation "be" => branchEval p r hp hp1 hr hr1 b ℏ γ t

def memoryFromEval (rPrep : ℝ) (flip : Bool) (h : MemoryHist) : MatJoint :=
  if h.2.1=0 then (1/3:ℂ) • (GibbsMultilevelReflection.projector (0:Q) ⊗ₖ
    stateFromEval p r hp hp1 hr hr1 b ℏ γ t (sigma rPrep (signalLabel flip h.1))) else 0

def measuredFromEval (rPrep φ₁ φ₂ : ℝ) (flip : Bool) (h : MeasuredHist) : MatJoint :=
  be rPrep φ₁ φ₂ flip h.1 h.2.1 h.2.2.1 •
    (FiniteThreeLevelMemoryReadout.R φ₁ φ₂ h.2.2.1 ⊗ₖ GibbsMultilevelReflection.projector (0:Q))

theorem memoryFromEval_actual (rPrep : ℝ) (flip : Bool) :
    memoryFromEval p r hp hp1 hr hr1 b ℏ γ t rPrep flip =
      memoryFamily b ℏ γ t rPrep hγ ht flip := by
  funext ⟨a,c,⟨⟩⟩
  exact (memory_matrices_eval p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht rPrep flip a c).symm

theorem measuredFromEval_actual (rPrep φ₁ φ₂ : ℝ) (flip : Bool) :
    measuredFromEval p r hp hp1 hr hr1 b ℏ γ t rPrep φ₁ φ₂ flip =
      measuredFamily b ℏ γ t rPrep φ₁ φ₂ hγ ht flip := by
  funext ⟨a,c,j,⟨⟩⟩
  exact (measured_matrices_eval p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht rPrep φ₁ φ₂ flip a c j).symm

/-- Positivity and total normalization are preserved without removing zero branches. -/
theorem evaluated_families_valid (rPrep φ₁ φ₂ : ℝ) (hPrep : 0 ≤ rPrep) (hPrep1 : rPrep ≤ 1)
    (flip : Bool) :
    IsBranchFamily (memoryFromEval p r hp hp1 hr hr1 b ℏ γ t rPrep flip) ∧
    IsBranchFamily (measuredFromEval p r hp hp1 hr hr1 b ℏ γ t rPrep φ₁ φ₂ flip) := by
  rw [memoryFromEval_actual p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht,
    measuredFromEval_actual p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
  exact ⟨memory_valid b ℏ γ t hγ ht hPrep hPrep1 flip,
    measured_valid b ℏ γ t φ₁ φ₂ hγ ht hPrep hPrep1 flip⟩

theorem evaluated_mass_laws (rPrep φ₁ φ₂ : ℝ) (hPrep : 0 ≤ rPrep) (hPrep1 : rPrep ≤ 1)
    (flip : Bool) :
    (∀ a c j, 0 ≤ (be rPrep φ₁ φ₂ flip a c j).re ∧ (be rPrep φ₁ φ₂ flip a c j).im=0) ∧
    (∑ h : MeasuredHist, (be rPrep φ₁ φ₂ flip h.1 h.2.1 h.2.2.1).re)=1 := by
  have hv := measured_valid b ℏ γ t φ₁ φ₂ hγ ht hPrep hPrep1 flip
  constructor
  · intro a c j
    constructor
    · rw [← measured_traces_eval p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
      exact (Complex.le_def.mp (hv.1 (a,c,j,())).trace_nonneg).1
    · rw [branchEval_mass p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
      rfl
  · calc
      _ = ∑ h : MeasuredHist, (measuredFamily b ℏ γ t rPrep φ₁ φ₂ hγ ht flip h).trace.re := by
        apply Finset.sum_congr rfl
        intro ⟨a,c,j,⟨⟩⟩ _
        exact congrArg Complex.re (measured_traces_eval p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht rPrep φ₁ φ₂ flip a c j).symm
      _ = 1 := hv.2

theorem evaluated_memory_same_history (rPrep : ℝ) (h : MemoryHist) :
    (memoryFromEval p r hp hp1 hr hr1 b ℏ γ t rPrep false h).trace.re =
      (memoryFromEval p r hp hp1 hr hr1 b ℏ γ t rPrep true h).trace.re := by
  simp only [memoryFromEval_actual p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
  exact memory_same_history b ℏ γ t rPrep hγ ht h

theorem evaluated_structural_ties (rPrep φ₁ φ₂ : ℝ) (flip : Bool) (a c j : Q) (d : Fin 2)
    (hs : c≠0 ∨ a.val=2 ∨ j.val=2) :
    readoutTable (optimalDecisionReadout (retention rPrep γ t)
      (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂))
      (measuredFamily b ℏ γ t rPrep φ₁ φ₂ hγ ht flip) (a,c,j,()) d =
      if d=0 then (be rPrep φ₁ φ₂ flip a c j).re else 0 := by
  rw [optimized_columns_eval p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
  rw [(optimal_structural_ties_A _ _ _ (a,c,j,()) hs).2]
  split_ifs <;> simp

theorem evaluated_zero_preparation_ties (φ₁ φ₂ : ℝ) (flip : Bool) (a c j : Q) (d : Fin 2) :
    readoutTable (optimalDecisionReadout (retention 0 γ t)
      (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂))
      (measuredFamily b ℏ γ t 0 φ₁ φ₂ hγ ht flip) (a,c,j,()) d =
      if d=0 then (be 0 φ₁ φ₂ flip a c j).re else 0 := by
  rw [optimized_columns_eval p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht,
    (optimal_zero_preparation_ties_A b ℏ γ t φ₁ φ₂ (a,c,j,())).2]
  split_ifs <;> simp

theorem evaluated_nontie_rule (rPrep φ₁ φ₂ : ℝ) (a c j : Q)
    (hne : (be rPrep φ₁ φ₂ false a c j).re ≠ (be rPrep φ₁ φ₂ true a c j).re) :
    optimalDecisionProjection (retention rPrep γ t) (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂) (a,c,j,()) =
      decisionProjection (optimalReversal (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂)) (a,c,j,()) ∧
    optimalScore (retention rPrep γ t) (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂) (a,c,j,()) =
      score (optimalReversal (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂)) (a,c,j,()) := by
  apply optimal_decision_non_tie
  simpa only [branchEval_mass p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht,Complex.ofReal_re] using hne

include hp hp1 hr hr1 in
/-- Equal nonzero masses need not have the same columns under the fixed and optimal rules. -/
theorem fixed_optimal_tie_distinction (φ₁ φ₂ : ℝ) :
    readoutTable (decisionReadout false)
      (measuredFamily b ℏ γ t 0 φ₁ φ₂ hγ ht false) (0,0,1,()) 0 = 0 ∧
    readoutTable (optimalDecisionReadout (retention 0 γ t)
      (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂))
      (measuredFamily b ℏ γ t 0 φ₁ φ₂ hγ ht false) (0,0,1,()) 0 = 109/900 := by
  rw [fixed_columns_eval p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht,
    evaluated_zero_preparation_ties p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
  rw [branchEval_mass p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
  norm_num [score,choosesA,mass,retention,probability,gibbsProbability,signalLabel]

theorem evaluated_reset_before_readout (rPrep : ℝ) (hPrep : 0 ≤ rPrep) (hPrep1 : rPrep ≤ 1)
    (I : MemoryHist → FiniteInstrument Joint 2) :
    branchDistance (fun h => FiniteThreeLevelEnvironmentLift.gibbsReset
      (memoryFromEval p r hp hp1 hr hr1 b ℏ γ t rPrep false h))
      (fun h => FiniteThreeLevelEnvironmentLift.gibbsReset
      (memoryFromEval p r hp hp1 hr hr1 b ℏ γ t rPrep true h)) = 0 ∧
    instrumentError (fun h => FiniteThreeLevelEnvironmentLift.gibbsReset
      (memoryFromEval p r hp hp1 hr hr1 b ℏ γ t rPrep false h))
      (fun h => FiniteThreeLevelEnvironmentLift.gibbsReset
      (memoryFromEval p r hp hp1 hr hr1 b ℏ γ t rPrep true h)) I = 1/2 := by
  simp only [memoryFromEval_actual p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
  exact E_reset_all_physical_errors b ℏ γ t hγ ht hPrep hPrep1 I

theorem evaluated_reset_after_readout (rPrep φ₁ φ₂ : ℝ) (f : MeasuredHist → ℝ) :
    historyError (fun h => FiniteThreeLevelEnvironmentLift.gibbsReset
      (measuredFromEval p r hp hp1 hr hr1 b ℏ γ t rPrep φ₁ φ₂ false h))
      (fun h => FiniteThreeLevelEnvironmentLift.gibbsReset
      (measuredFromEval p r hp hp1 hr hr1 b ℏ γ t rPrep φ₁ φ₂ true h)) f =
    historyError (measuredFamily b ℏ γ t rPrep φ₁ φ₂ hγ ht false)
      (measuredFamily b ℏ γ t rPrep φ₁ φ₂ hγ ht true) f := by
  simp only [measuredFromEval_actual p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
  exact E_reset_preserves_recorded_error _ _ _

theorem evaluated_system_reset_after_swap (rPrep : ℝ) (flip : Bool) (a c : Q) :
    resetS (FiniteThreeLevelEnvironmentLift.swap
      (memoryFromEval p r hp hp1 hr hr1 b ℏ γ t rPrep flip (a,c,()))) =
      if c=0 then (1/3:ℂ) • (GibbsMultilevelReflection.projector (0:Q) ⊗ₖ
        GibbsMultilevelReflection.projector (0:Q)) else 0 := by
  rw [memoryFromEval_actual p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
  exact S_reset_after_swap b ℏ γ t rPrep hγ ht flip a c

theorem evaluated_terminal_equal (rPrep φ₁ φ₂ : ℝ) :
    (∑ h, memoryFromEval p r hp hp1 hr hr1 b ℏ γ t rPrep false h) =
      (∑ h, memoryFromEval p r hp hp1 hr hr1 b ℏ γ t rPrep true h) ∧
    (∑ h, measuredFromEval p r hp hp1 hr hr1 b ℏ γ t rPrep φ₁ φ₂ false h) =
      (∑ h, measuredFromEval p r hp hp1 hr hr1 b ℏ γ t rPrep φ₁ φ₂ true h) := by
  simp only [memoryFromEval_actual p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht,
    measuredFromEval_actual p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
  exact ⟨memory_terminal_equal b ℏ γ t rPrep hγ ht,
    measured_terminal_equal b ℏ γ t rPrep φ₁ φ₂ hγ ht⟩

theorem evaluated_marginals (rPrep φ₁ φ₂ : ℝ) (a j : Q) :
    (∑ c, ∑ j, (be rPrep φ₁ φ₂ false a c j).re)=1/3 ∧
    (∑ c, ∑ j, (be rPrep φ₁ φ₂ true a c j).re)=1/3 ∧
    (∑ a, ∑ c, (be rPrep φ₁ φ₂ false a c j).re)=
      (∑ a, ∑ c, (be rPrep φ₁ φ₂ true a c j).re) := by
  simp only [branchEval_mass p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht, Complex.ofReal_re]
  exact marginal_mass_laws _ _ _ a j

end CompleteFamilies

section ThermalControls
variable (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1) (hpos : 0 < p)
include hpos

theorem evaluated_zero_time (b ℏ γ : ℝ) (hγ : 0 ≤ γ) (X : MatQ) :
    stateFromEval p r hp hp1 hr hr1 b ℏ γ 0 X = X := by
  rw [stateFromEval_channel p r hp hp1 hr hr1 hpos b ℏ γ 0 hγ le_rfl,channel_zero_time b ℏ γ hγ]

theorem evaluated_zero_rate (b ℏ t : ℝ) (ht : 0 ≤ t) (X : MatQ) :
    stateFromEval p r hp hp1 hr hr1 b ℏ 0 t X = phase b ℏ t X := by
  rw [stateFromEval_channel p r hp hp1 hr hr1 hpos b ℏ 0 t le_rfl ht,channel_zero_rate b ℏ t ht]

theorem evaluated_zero_rate_nonidentity :
    stateFromEval p r hp hp1 hr hr1 1 1 0 secondGapHalfTurn (E 0 2) = -E 0 2 ∧
    stateFromEval p r hp hp1 hr hr1 1 1 0 secondGapHalfTurn (E 0 2) ≠ E 0 2 := by
  rw [stateFromEval_channel p r hp hp1 hr hr1 hpos 1 1 0 secondGapHalfTurn
    le_rfl secondGapHalfTurn_positive.le]
  exact zero_rate_still_nonidentity

theorem evaluated_observable_identity (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (X : MatQ) :
    thermalEval p r hp hp1 hr hr1 b ℏ γ t X 1 = X.trace := by
  rw [thermalEval,thermal_enc p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht,
    FiniteThreeLevelHistoryTransfer.actual_observable_unital b ℏ γ t hγ ht]
  change eval p r hp hp1 hr hr1 X 1 = _
  rw [eval_trace p r hp hp1 hr hr1 hpos,one_mul]

theorem evaluated_state_identity (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) :
    stateFromEval p r hp hp1 hr hr1 b ℏ γ t 1 =
      (Real.exp (-γ*t):ℂ) • (1:MatQ)+(3*(1-(Real.exp (-γ*t):ℂ))) • rhoN := by
  rw [stateFromEval_channel p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
  exact FiniteThreeLevelHistoryTransfer.actual_state_identity b ℏ γ t hγ ht

theorem evaluated_state_not_unital (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (hdose : 0 < γ*t) :
    stateFromEval p r hp hp1 hr hr1 b ℏ γ t 1 ≠ 1 := by
  rw [stateFromEval_channel p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
  exact FiniteThreeLevelHistoryTransfer.actual_state_not_unital b ℏ γ t hγ ht hdose

theorem evaluated_mixture_faithful (b ℏ γ t rPrep : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (hPrep : 0 ≤ rPrep) (hq : retention rPrep γ t < 1) (a : Q) :
    (stateFromEval p r hp hp1 hr hr1 b ℏ γ t (sigma rPrep a)).PosDef := by
  rw [stateFromEval_channel p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
  exact evolved_faithful b ℏ γ t hγ ht hPrep hq a

theorem evaluated_recorded_reset_fixture :
    historyError (fun h => FiniteThreeLevelEnvironmentLift.gibbsReset
      (measuredFromEval p r hp hp1 hr hr1 1 1 1 fixtureTime (1/2)
        (theta₁ 1 1 fixtureTime) (theta₂ 1 1 fixtureTime) false h))
      (fun h => FiniteThreeLevelEnvironmentLift.gibbsReset
      (measuredFromEval p r hp hp1 hr hr1 1 1 1 fixtureTime (1/2)
        (theta₁ 1 1 fixtureTime) (theta₂ 1 1 fixtureTime) true h)) (score false) = 5/12 := by
  simp only [measuredFromEval_actual p r hp hp1 hr hr1 hpos 1 1 1 fixtureTime
    (by norm_num) fixtureTime_positive.le]
  simpa only [fixtureShifted,add_zero] using E_reset_after_readout_fixture

theorem evaluated_quarter_table (sign : Bool) (flip : Bool) (a c j : Q) :
    let x := if sign then Real.pi/2 else -Real.pi/2
    (branchEval p r hp hp1 hr hr1 1 1 1 fixtureTime (1/2)
      (theta₁ 1 1 fixtureTime+x) (theta₂ 1 1 fixtureTime+x) flip a c j).re =
      if c=0 then quarterTable a j else 0 := by
  dsimp
  rw [← measured_traces_eval p r hp hp1 hr hr1 hpos 1 1 1 fixtureTime
    (by norm_num) fixtureTime_positive.le]
  exact quarter_tables sign flip a c j

theorem evaluated_single_arm_negative (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) :
    Jreal p r hp hp1 hr hr1 b ℏ γ t (theta₁ b ℏ t) (theta₂ b ℏ t-Real.pi) =
      -14*Real.exp (-γ*t)/25 ∧
    optimalReversal (theta₁ b ℏ t-theta₁ b ℏ t)
      (theta₂ b ℏ t-(theta₂ b ℏ t-Real.pi)) = true := by
  rw [Jreal_formula p r hp hp1 hr hr1 hpos b ℏ γ t hγ ht]
  norm_num [sub_sub_cancel,contrast,optimalReversal]
  ring

end ThermalControls

/-- These inherited position controls concern the actual system reset, not a second
environment contraction after SWAP. -/
theorem system_reset_positions (b ℏ γ t rPrep : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (a c : Q) :
    run Q Q 3 (memoryTree b ℏ γ t hγ ht false) (a,c,()) (resetS (input rPrep)) =
      run Q Q 3 (memoryTree b ℏ γ t hγ ht true) (a,c,()) (resetS (input rPrep)) ∧
    recordStep.branch Q Q 3 a (resetS (input rPrep)) =
      (if a=0 then resetS (input rPrep) else 0) ∧
    resetS (recordStep.branch Q Q 3 a (input rPrep)) =
      (1/3:ℂ) • (GibbsMultilevelReflection.projector (0:Q) ⊗ₖ sigma rPrep a) := by
  refine ⟨S_reset_before_record_erases b ℏ γ t rPrep hγ ht a c,
    record_after_S_reset rPrep a, ?_⟩
  rw [recordStep_branch,resetS_smul,resetS_tensor,GibbsMultilevelReflection.projector_trace,one_smul]

theorem noncommutation_domain {rPrep : ℝ} (hPrep : 0 < rPrep) (hPrep1 : rPrep < 1) :
    sigma rPrep 0*sigma rPrep 1 ≠ sigma rPrep 1*sigma rPrep 0 ∧
    initialState rPrep false*initialState rPrep true ≠ initialState rPrep true*initialState rPrep false :=
  ⟨signal_noncommuting hPrep hPrep1,initial_pair_noncommuting hPrep hPrep1⟩

theorem signal_endpoints_commute (rPrep : ℝ) (he : rPrep=0 ∨ rPrep=1) (a : Q) :
    sigma rPrep a*sigma rPrep (exchange a) = sigma rPrep (exchange a)*sigma rPrep a := by
  rcases he with rfl | rfl
  · simp only [sigma_zero]
  · have s0 : sigma 1 0=P 0 := by simp [sigma,mixture]
    have s1 : sigma 1 1=P 1 := by simp [sigma,mixture]
    have casesQ : ∀ a : Q, a=0 ∨ a=1 ∨ a=2 := by decide
    rcases casesQ a with rfl | rfl | rfl
    · rw [show exchange 0=1 by decide,s0,s1,P_orthogonal _ _ (by decide),P_orthogonal _ _ (by decide)]
    · rw [show exchange 1=0 by decide,s0,s1,P_orthogonal _ _ (by decide),P_orthogonal _ _ (by decide)]
    · rw [show exchange 2=2 by decide]

theorem initial_endpoints_commute (rPrep : ℝ) (he : rPrep=0 ∨ rPrep=1) :
    initialState rPrep false*initialState rPrep true = initialState rPrep true*initialState rPrep false := by
  ext ⟨a,e⟩ ⟨k,f⟩
  change (input rPrep*rhoF rPrep) (a,e) (k,f) = (rhoF rPrep*input rPrep) (a,e) (k,f)
  by_cases hak : a=k
  · subst k
    have h := initial_commutator_block rPrep a e f
    rw [signal_endpoints_commute rPrep he a,sub_self] at h
    simpa only [Matrix.sub_apply,Matrix.zero_apply,zero_div,sub_eq_zero] using h
  · simp [Matrix.mul_apply,Fintype.sum_prod_type,input_entry,rhoF_entry,ite_mul,mul_ite,hak]

theorem carrier_and_history_counts :
    Fintype.card (Q × Unit)=3 ∧ Fintype.card Joint=9 ∧
    Fintype.card (Fin 15)=15 ∧ Fintype.card Q=3 ∧
    Fintype.card MemoryHist=9 ∧ Fintype.card MeasuredHist=27 ∧
    Fintype.card {h : MemoryHist // h.2.1≠0}=6 ∧
    Fintype.card {h : MeasuredHist // h.2.1≠0}=18 := by
  refine ⟨by decide,by decide,by decide,by decide,by decide,by decide,impossible_history_counts⟩

/-- Side reset does not obstruct arbitrary matrix encoding at positive central retention. -/
theorem side_endpoint_encodings (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p) (A : MatQ) :
    coordinates p 0 hp hp1 le_rfl (by norm_num) (enc p 0 hp hp1 le_rfl (by norm_num) A)=A ∧
    coordinates p 1 hp hp1 (by norm_num) le_rfl (enc p 1 hp hp1 (by norm_num) le_rfl A)=A :=
  ⟨enc_coordinates p 0 hp hp1 le_rfl (by norm_num) hpos A,
    enc_coordinates p 1 hp hp1 (by norm_num) le_rfl hpos A⟩

/-- The central reset quotient can be trivial on centered modes while the separately
prepared retained experiment still has positive physical distance. -/
theorem central_reset_independent_memory (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (z : Reconstructed 0 r le_rfl (by norm_num) hr hr1) (a : ℝ) (ω : Q → ℝ)
    (b ℏ γ t rPrep : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (hPrep : 0 < rPrep) :
    Module.finrank ℂ (Reconstructed 0 r le_rfl (by norm_num) hr hr1)=1 ∧
    FiniteThreeLevelHistoryTransfer.transfer 0 r le_rfl (by norm_num) hr hr1 a ω t z=z ∧
    FiniteThreeLevelHistoryTransfer.generator 0 r le_rfl (by norm_num) hr hr1 ω γ z=0 ∧
    0 < branchDistance (memoryFamily b ℏ γ t rPrep hγ ht false)
      (memoryFamily b ℏ γ t rPrep hγ ht true) := by
  refine ⟨reset_finrank r hr hr1,
    FiniteThreeLevelHistoryTransfer.central_reset_transfer 0 r le_rfl (by norm_num) hr hr1 rfl a ω t z,
    FiniteThreeLevelHistoryTransfer.central_reset_generator 0 r le_rfl (by norm_num) hr hr1 rfl ω γ z, ?_⟩
  rw [memory_distance b ℏ γ t hγ ht hPrep.le]
  unfold retention
  positivity

theorem physical_gap_domain (b ℏ t : ℝ) (hb : 0 < b) (hℏ : 0 < ℏ) (ht : 0 < t) :
    0 < FiniteThreeLevelHistoryTransfer.gap01 b ℏ t ∧
    FiniteThreeLevelHistoryTransfer.gap01 b ℏ t < FiniteThreeLevelHistoryTransfer.gap02 b ℏ t ∧
    FiniteThreeLevelHistoryTransfer.gap02 b ℏ t =
      FiniteThreeLevelHistoryTransfer.gap01 b ℏ t+FiniteThreeLevelHistoryTransfer.gap12 b ℏ t := by
  have hh := physical_two_gap_domain hb hℏ ht
  exact ⟨by simpa only [theta_gap01] using hh.1,
    by simpa only [theta_gap01,theta_gap02] using hh.2.1,
    by rw [FiniteThreeLevelHistoryTransfer.gaps_tied]; ring⟩

theorem finite_retention_and_zero_dose (γ t : ℝ) :
    0 < Real.exp (-γ*t) ∧ (γ=0 ∨ t=0 → Real.exp (-γ*t)=1) :=
  ⟨Real.exp_pos _,FiniteThreeLevelHistoryTransfer.zero_dose_retention γ t⟩

/-- Equality of weights does not identify the selected states, even after undoing SWAP. -/
theorem same_weights_distinct_updates :
    ∃ X : MatJoint, IsDensityOperator X ∧
      (sequentialReadout 0 0 false (2,0,())).weight 0 X =
        (groupedReadout 0 0 false (2,0,())).weight 0 X ∧
      (sequentialReadout 0 0 false (2,0,())).branch 0 X ≠
        (groupedReadout 0 0 false (2,0,())).branch 0 X ∧
      FiniteThreeLevelEnvironmentLift.swap ((sequentialReadout 0 0 false (2,0,())).branch 0 X) ≠
        (groupedReadout 0 0 false (2,0,())).branch 0 X := by
  have hh := sequential_grouped_state_distinction
  exact ⟨_,hh.1,hh.2.1.trans hh.2.2.1.symm,hh.2.2.2⟩
end SKEFTHawking.QuantumNetwork.FiniteThreeLevelHistoryReadout
