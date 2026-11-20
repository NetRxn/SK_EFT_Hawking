import SKEFTHawking.FiniteNontracialReflectionDynamics
import SKEFTHawking.QuantumNetwork.NamedChannels

/-! Finite chronological schedules of the actual nontracial reset/dephasing channel.
The head acts first. Dose parameters describe finite compositions; they are not a clock.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteNontracialSchedule
open Matrix NontracialPauliReflection
open FinitePositiveKernel GibbsObservable BlockConditionalExpectation
open scoped BigOperators ComplexOrder Matrix.Norms.Elementwise

abbrev Q := Fin 2
abbrev MatQ := Matrix Q Q ℂ

structure Slice where
  gamma : ℝ
  eta : ℝ
  duration : ℝ
  gamma_nonneg : 0 ≤ gamma
  eta_nonneg : 0 ≤ eta
  duration_nonneg : 0 ≤ duration

abbrev Schedule := List Slice

/-- Preserve the actual quotient-dependent index of the primitive family. -/
def primitiveCount : ℕ := Fintype.card
  (Sum (Fin (Fintype.card (Q × Q)))
    (Sum (Fin (Fintype.card (Blocks NontracialReflectionDynamics.signature))) (Fin 1)))

def count : Schedule → ℕ
  | [] => 1
  | _ :: tail => count tail * primitiveCount

def scheduleKraus : (s : Schedule) → Fin (count s) → MatQ
  | [] => idKrausPad 0 2
  | head :: tail => composeKraus (scheduleKraus tail)
      (NontracialReflectionDynamics.timeKraus head.gamma head.eta head.duration)

def state (s : Schedule) (X : MatQ) : MatQ := krausMap (scheduleKraus s) X
def observable (s : Schedule) (A : MatQ) : MatQ :=
  Channel.heisenberg (scheduleKraus s) A

theorem normalized (s : Schedule) : IsKrausChannel (scheduleKraus s) := by
  induction s with
  | nil => exact isKrausChannel_idKrausPad 0 2
  | cons h t ih =>
    exact isKrausChannel_composeKraus ih
      (NontracialReflectionDynamics.normalized h.gamma h.eta h.duration
        h.gamma_nonneg h.eta_nonneg h.duration_nonneg)

@[simp] theorem state_nil (X : MatQ) : state [] X = X := krausMap_idKrausPad 0 2 X

/-- Literal head-first forward evolution, before any sector simplification. -/
theorem state_cons (h : Slice) (t : Schedule) (X : MatQ) :
    state (h :: t) X = state t
      (NontracialReflectionDynamics.state h.gamma h.eta h.duration X) :=
  krausMap_composeKraus _ _ X

theorem state_append (s t : Schedule) (X : MatQ) :
    state (s ++ t) X = state t (state s X) := by
  induction s generalizing X with
  | nil => simp
  | cons h s ih =>
    simpa only [List.cons_append, state_cons] using ih
      (NontracialReflectionDynamics.state h.gamma h.eta h.duration X)

theorem state_trace (s : Schedule) (X : MatQ) : (state s X).trace = X.trace :=
  trace_krausMap (normalized s) X
theorem state_posSemidef (s : Schedule) {X : MatQ} (hX : X.PosSemidef) :
    (state s X).PosSemidef := krausMap_posSemidef _ hX
theorem state_density (s : Schedule) {X : MatQ} (hX : IsDensityOperator X) :
    IsDensityOperator (state s X) := krausMap_isDensityOperator (normalized s) hX
theorem state_stationary (s : Schedule) : state s rhoN = rhoN := by
  induction s with
  | nil => exact state_nil _
  | cons h t ih => rw [state_cons, NontracialReflectionDynamics.stationary
      h.gamma h.eta h.duration h.gamma_nonneg h.eta_nonneg h.duration_nonneg, ih]

theorem heisenberg_compose {a b : ℕ} (L : Fin b → MatQ) (K : Fin a → MatQ)
    (A : MatQ) : Channel.heisenberg (composeKraus L K) A =
      Channel.heisenberg K (Channel.heisenberg L A) := by
  unfold Channel.heisenberg composeKraus
  rw [finProdFinEquiv.symm.sum_comp
    (fun p : Fin b × Fin a => (L p.1 * K p.2)ᴴ * A * (L p.1 * K p.2)),
    Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.conjTranspose_mul]
  noncomm_ring

@[simp] theorem observable_nil (A : MatQ) : observable [] A = A := by
  change Channel.heisenberg (idKrausPad 0 2) A = A
  unfold Channel.heisenberg
  change (∑ k : Fin 1, (idKrausPad 0 2 k)ᴴ * A * idKrausPad 0 2 k) = A
  rw [Fin.sum_univ_one]
  simp [idKrausPad]

/-- The dual of head-first evolution pulls observables back in reverse order. -/
theorem observable_cons (h : Slice) (t : Schedule) (A : MatQ) :
    observable (h :: t) A =
      NontracialReflectionDynamics.observable h.gamma h.eta h.duration (observable t A) :=
  heisenberg_compose _ _ A

theorem observable_append (s t : Schedule) (A : MatQ) :
    observable (s ++ t) A = observable s (observable t A) := by
  induction s with
  | nil => simp
  | cons h s ih => rw [List.cons_append, observable_cons, ih, observable_cons]

theorem trace_dual (s : Schedule) (A X : MatQ) :
    (A * state s X).trace = (observable s A * X).trace := by
  rw [Matrix.trace_mul_comm, state, observable, ← Channel.trace_duality,
    Matrix.trace_mul_comm]

def G : Schedule → ℝ
  | [] => 0
  | h :: t => h.gamma * h.duration + G t
def D : Schedule → ℝ
  | [] => 0
  | h :: t => h.eta * h.duration + D t
def alpha (s : Schedule) : ℝ := Real.exp (-G s)
def beta (s : Schedule) : ℝ := Real.exp (-(G s + D s))

theorem G_nonneg (s : Schedule) : 0 ≤ G s := by
  induction s with
  | nil => exact le_rfl
  | cons h t ih => exact add_nonneg (mul_nonneg h.gamma_nonneg h.duration_nonneg) ih
theorem D_nonneg (s : Schedule) : 0 ≤ D s := by
  induction s with
  | nil => exact le_rfl
  | cons h t ih => exact add_nonneg (mul_nonneg h.eta_nonneg h.duration_nonneg) ih
theorem G_append (s t : Schedule) : G (s ++ t) = G s + G t := by
  induction s with
  | nil => simp [G]
  | cons h s ih => simp [G, ih, add_assoc]
theorem D_append (s t : Schedule) : D (s ++ t) = D s + D t := by
  induction s with
  | nil => simp [D]
  | cons h s ih => simp [D, ih, add_assoc]

@[simp] theorem alpha_nil : alpha [] = 1 := by simp [alpha, G]
@[simp] theorem beta_nil : beta [] = 1 := by simp [beta, G, D]
theorem alpha_cons (h : Slice) (t : Schedule) :
    alpha (h :: t) = alpha t * Real.exp (-h.gamma * h.duration) := by
  rw [alpha, G, neg_add, Real.exp_add]
  simp [alpha, mul_comm]
theorem beta_cons (h : Slice) (t : Schedule) :
    beta (h :: t) = beta t * Real.exp (-(h.gamma + h.eta) * h.duration) := by
  have e : -(G (h :: t) + D (h :: t)) =
      -(G t + D t) + (-(h.gamma + h.eta) * h.duration) := by simp only [G,D]; ring
  rw [beta, e, Real.exp_add]
  rfl
theorem alpha_append (s t : Schedule) : alpha (s ++ t) = alpha s * alpha t := by
  simp only [alpha, G_append, neg_add, Real.exp_add]
theorem beta_append (s t : Schedule) : beta (s ++ t) = beta s * beta t := by
  unfold beta
  rw [G_append, D_append, show -(G s + G t + (D s + D t)) =
    -(G s + D s) + -(G t + D t) by ring, Real.exp_add]
theorem alpha_product (s : Schedule) :
    alpha s = (s.map (fun h => Real.exp (-h.gamma * h.duration))).prod := by
  induction s with
  | nil => simp
  | cons h t ih => simp [alpha_cons, ih, mul_comm]
theorem beta_product (s : Schedule) :
    beta s = (s.map (fun h => Real.exp (-(h.gamma + h.eta) * h.duration))).prod := by
  induction s with
  | nil => simp
  | cons h t ih => simp [beta_cons, ih, mul_comm]
theorem coefficients (s : Schedule) : 0 < beta s ∧ beta s ≤ alpha s ∧ alpha s ≤ 1 := by
  refine ⟨Real.exp_pos _, Real.exp_le_exp.mpr ?_, Real.exp_le_one_iff.mpr ?_⟩
  · have := D_nonneg s; change -(G s + D s) ≤ -G s; linarith
  · exact neg_nonpos.mpr (G_nonneg s)

def stateForm (a b : ℂ) (X : MatQ) : MatQ := X.trace • rhoN +
  a • (NontracialReflectionDynamics.diagonalPart X - X.trace • rhoN) +
  b • (X - NontracialReflectionDynamics.diagonalPart X)
def observableForm (a b : ℂ) (A : MatQ) : MatQ := (rhoN*A).trace • (1 : MatQ) +
  a • (NontracialReflectionDynamics.diagonalPart A - (rhoN*A).trace • 1) +
  b • (A - NontracialReflectionDynamics.diagonalPart A)

theorem stateForm_compose (a b c d : ℂ) (X : MatQ) :
    stateForm a b (stateForm c d X) = stateForm (a*c) (b*d) X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [stateForm, NontracialReflectionDynamics.diagonalPart, rhoN, Matrix.trace,
      Fin.sum_univ_two, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] <;> ring
/-- Full complex trace pairing determines a matrix, using literal matrix units. -/
theorem trace_ext (A B : MatQ) (h : ∀ X : MatQ, (A*X).trace = (B*X).trace) : A=B := by
  ext i j
  have hh := h (Matrix.single j i 1)
  simpa only [Matrix.trace_mul_single, MulOpposite.op_one, one_smul] using hh

theorem forms_trace_dual (a b : ℂ) (A X : MatQ) :
    (A * stateForm a b X).trace = (observableForm a b A * X).trace := by
  norm_num [stateForm, observableForm, NontracialReflectionDynamics.diagonalPart, rhoN,
    Matrix.trace, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

theorem state_formula (s : Schedule) (X : MatQ) :
    state s X = stateForm (alpha s) (beta s) X := by
  induction s generalizing X with
  | nil => simp [stateForm]
  | cons h t ih =>
    rw [state_cons, ih, NontracialReflectionDynamics.state_formula h.gamma h.eta
      h.duration h.gamma_nonneg h.eta_nonneg h.duration_nonneg]
    change stateForm _ _ (stateForm _ _ X) = _
    rw [stateForm_compose, alpha_cons, beta_cons, Complex.ofReal_mul, Complex.ofReal_mul]

theorem observable_formula (s : Schedule) (A : MatQ) :
    observable s A = observableForm (alpha s) (beta s) A := by
  apply trace_ext
  intro X
  rw [← trace_dual, state_formula, forms_trace_dual]

theorem G_sum (s : Schedule) : G s = (s.map (fun h => h.gamma*h.duration)).sum := by
  induction s with
  | nil => rfl
  | cons h t ih => simp [G, ih]
theorem D_sum (s : Schedule) : D s = (s.map (fun h => h.eta*h.duration)).sum := by
  induction s with
  | nil => rfl
  | cons h t ih => simp [D, ih]

/-- Equality of actions, without identifying distinct finite Kraus indices. -/
theorem state_effective (s : Schedule) (X : MatQ) :
    state s X = NontracialReflectionDynamics.state (G s) (D s) 1 X := by
  rw [state_formula, NontracialReflectionDynamics.state_formula (G s) (D s) 1
    (G_nonneg s) (D_nonneg s) zero_le_one]
  simp only [stateForm, alpha, beta, mul_one]
theorem observable_effective (s : Schedule) (A : MatQ) :
    observable s A = NontracialReflectionDynamics.observable (G s) (D s) 1 A := by
  rw [observable_formula, NontracialReflectionDynamics.observable_formula (G s) (D s) 1
    (G_nonneg s) (D_nonneg s) zero_le_one]
  simp only [observableForm, alpha, beta, mul_one]

theorem state_convex_formula (s : Schedule) (X : MatQ) :
    state s X = (1-(alpha s:ℂ)) • (X.trace • rhoN) +
      ((alpha s:ℂ)-(beta s:ℂ)) • NontracialReflectionDynamics.diagonalPart X +
      (beta s:ℂ) • X := by rw [state_formula]; unfold stateForm; module

theorem observable_convex_formula (s : Schedule) (A : MatQ) :
    observable s A = (1-(alpha s:ℂ)) • ((rhoN*A).trace • (1:MatQ)) +
      ((alpha s:ℂ)-(beta s:ℂ)) • NontracialReflectionDynamics.diagonalPart A +
      (beta s:ℂ) • A := by rw [observable_formula]; unfold observableForm; module

theorem state_append_commute (s t : Schedule) (X : MatQ) :
    state s (state t X) = state t (state s X) := by
  rw [← state_append, ← state_append, state_effective, state_effective,
    G_append, G_append, D_append, D_append]
  simp only [add_comm]
theorem observable_append_commute (s t : Schedule) (A : MatQ) :
    observable s (observable t A) = observable t (observable s A) := by
  rw [← observable_append, ← observable_append, observable_effective, observable_effective,
    G_append, G_append, D_append, D_append]
  simp only [add_comm]

@[simp] theorem state_singleton (h : Slice) (X : MatQ) :
    state [h] X = NontracialReflectionDynamics.state h.gamma h.eta h.duration X := by
  rw [state_cons, state_nil]
@[simp] theorem observable_singleton (h : Slice) (A : MatQ) :
    observable [h] A = NontracialReflectionDynamics.observable h.gamma h.eta h.duration A := by
  rw [observable_cons, observable_nil]

/-- The primitive is the actual GKSL propagator on its nonnegative physical domain. -/
theorem primitive_propagator (γ η t : ℝ) (hγ : 0≤γ) (hη : 0≤η) (ht : 0≤t) (X : MatQ) :
    NontracialReflectionDynamics.state γ η t X =
      OpenSystems.lindbladPropagatorAction 0
        (GibbsBlockRelaxation.jumps NontracialReflectionDynamics.signature weights γ η) t X :=
  GibbsBlockRelaxation.time_state_eq_propagator NontracialReflectionDynamics.signature weights
    weights_nonnegative weights_normalized γ η t hγ hη ht X

theorem singleton_propagator (h : Slice) (X : MatQ) :
    state [h] X = OpenSystems.lindbladPropagatorAction 0
      (GibbsBlockRelaxation.jumps NontracialReflectionDynamics.signature weights h.gamma h.eta)
      h.duration X := by
  rw [state_singleton]
  exact primitive_propagator _ _ _ h.gamma_nonneg h.eta_nonneg h.duration_nonneg X

def generator (γ η : ℝ) := OpenSystems.lindbladGenerator 0
  (GibbsBlockRelaxation.jumps NontracialReflectionDynamics.signature weights γ η)

theorem generator_formula (γ η : ℝ) (hγ : 0≤γ) (hη : 0≤η) (X : MatQ) :
    generator γ η X = (γ:ℂ) • (X.trace • rhoN-X) +
      (η:ℂ) • (NontracialReflectionDynamics.diagonalPart X-X) := by
  rw [generator, GibbsBlockRelaxation.generator_state NontracialReflectionDynamics.signature
    weights weights_nonnegative weights_normalized γ η hγ hη,
    weights_density, NontracialReflectionDynamics.singleton_expectation]

/-- All-real exponential extension. Equality to the square-root Kraus action is only
proved at nonnegative time; differentiation below preserves this boundary. -/
def analyticState (γ η t : ℝ) (X : MatQ) : MatQ :=
  stateForm (Real.exp (-γ*t)) (Real.exp (-(γ+η)*t)) X

theorem analyticState_eq (γ η t : ℝ) (hγ : 0≤γ) (hη : 0≤η) (ht : 0≤t) (X : MatQ) :
    NontracialReflectionDynamics.state γ η t X = analyticState γ η t X :=
  NontracialReflectionDynamics.state_formula γ η t hγ hη ht X

theorem analyticState_propagator (γ η t : ℝ) (hγ : 0≤γ) (hη : 0≤η) (X : MatQ) :
    analyticState γ η t X = OpenSystems.lindbladPropagatorAction 0
      (GibbsBlockRelaxation.jumps NontracialReflectionDynamics.signature weights γ η) t X := by
  rw [GibbsBlockRelaxation.propagator_state NontracialReflectionDynamics.signature weights
    weights_nonnegative weights_normalized γ η t hγ hη,
    weights_density, NontracialReflectionDynamics.singleton_expectation]
  rfl

theorem stateForm_trace (a b : ℂ) (X : MatQ) : (stateForm a b X).trace = X.trace := by
  norm_num [stateForm, NontracialReflectionDynamics.diagonalPart, rhoN, Matrix.trace,
    Fin.sum_univ_two, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem stateForm_diagonal (a b : ℂ) (X : MatQ) :
    NontracialReflectionDynamics.diagonalPart (stateForm a b X) = X.trace • rhoN +
      a • (NontracialReflectionDynamics.diagonalPart X-X.trace • rhoN) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [stateForm, NontracialReflectionDynamics.diagonalPart, rhoN, Matrix.trace,
      Fin.sum_univ_two, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]

theorem generator_analyticState (γ η t : ℝ) (hγ : 0≤γ) (hη : 0≤η) (X : MatQ) :
    generator γ η (analyticState γ η t X) =
      ((Real.exp (-γ*t)*(-γ):ℝ):ℂ) •
        (NontracialReflectionDynamics.diagonalPart X-X.trace • rhoN) +
      ((Real.exp (-(γ+η)*t)*(-(γ+η)):ℝ):ℂ) •
        (X-NontracialReflectionDynamics.diagonalPart X) := by
  rw [generator_formula γ η hγ hη]
  unfold analyticState
  rw [stateForm_trace, stateForm_diagonal]
  simp only [stateForm, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_add]
  module

theorem analyticState_hasDerivAt (γ η t : ℝ) (hγ : 0≤γ) (hη : 0≤η) (X : MatQ) :
    HasDerivAt (fun u : ℝ => analyticState γ η u X)
      (generator γ η (analyticState γ η t X)) t := by
  have hs : HasDerivAt (fun u : ℝ => Real.exp (-γ*u)) (Real.exp (-γ*t)*(-γ)) t := by
    simpa using ((hasDerivAt_id t).const_mul (-γ)).exp
  have hf : HasDerivAt (fun u : ℝ => Real.exp (-(γ+η)*u))
      (Real.exp (-(γ+η)*t)*(-(γ+η))) t := by
    simpa using ((hasDerivAt_id t).const_mul (-(γ+η))).exp
  have hd := ((hasDerivAt_const t (X.trace • rhoN)).add
    (hs.ofReal_comp.smul_const (NontracialReflectionDynamics.diagonalPart X-X.trace • rhoN))).add
    (hf.ofReal_comp.smul_const (X-NontracialReflectionDynamics.diagonalPart X))
  rw [generator_analyticState γ η t hγ hη]
  convert hd using 1 <;> first | rfl | simp

/-- Includes the physical zero endpoint, with a one-sided derivative only. -/
theorem primitive_hasDerivWithinAt (γ η t : ℝ) (hγ : 0≤γ) (hη : 0≤η) (ht : 0≤t)
    (X : MatQ) : HasDerivWithinAt (fun u : ℝ => NontracialReflectionDynamics.state γ η u X)
      (generator γ η (NontracialReflectionDynamics.state γ η t X)) (Set.Ici 0) t := by
  rw [analyticState_eq γ η t hγ hη ht]
  exact (analyticState_hasDerivAt γ η t hγ hη X).hasDerivWithinAt.congr
    (fun u hu => analyticState_eq γ η u hγ hη hu X)
    (analyticState_eq γ η t hγ hη ht X)

/-- At positive time a neighborhood lies in the physical domain. -/
theorem primitive_hasDerivAt (γ η t : ℝ) (hγ : 0≤γ) (hη : 0≤η) (ht : 0<t)
    (X : MatQ) : HasDerivAt (fun u : ℝ => NontracialReflectionDynamics.state γ η u X)
      (generator γ η (NontracialReflectionDynamics.state γ η t X)) t := by
  rw [analyticState_eq γ η t hγ hη ht.le]
  apply (analyticState_hasDerivAt γ η t hγ hη X).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds ht] with u hu
  exact analyticState_eq γ η u hγ hη hu.le X

/-- Vanishing doses give the identity action of the same composed family. -/
theorem zero_dose_actions (s : Schedule) (hG : G s=0) (hD : D s=0) (X : MatQ) :
    state s X=X ∧ observable s X=X := by
  rw [state_formula, observable_formula]
  simp only [alpha, beta, hG, hD, add_zero, neg_zero, Real.exp_zero, Complex.ofReal_one,
    stateForm, observableForm, one_smul]
  constructor <;> module

theorem zero_duration_doses (s : Schedule) (hz : ∀ h∈s, h.duration=0) : G s=0 ∧ D s=0 := by
  induction s with
  | nil => exact ⟨rfl,rfl⟩
  | cons h t ih =>
    have hd := hz h (List.mem_cons_self)
    have ht := ih (fun a ha => hz a (List.mem_cons_of_mem h ha))
    simp [G,D,hd,ht.1,ht.2]

theorem zero_duration_actions (s : Schedule) (hz : ∀ h∈s, h.duration=0) (X : MatQ) :
    state s X=X ∧ observable s X=X :=
  zero_dose_actions s (zero_duration_doses s hz).1 (zero_duration_doses s hz).2 X

theorem zero_rate_doses (s : Schedule) (hz : ∀ h∈s, h.gamma=0 ∧ h.eta=0) : G s=0 ∧ D s=0 := by
  induction s with
  | nil => exact ⟨rfl,rfl⟩
  | cons h t ih =>
    have hd := hz h (List.mem_cons_self)
    have ht := ih (fun a ha => hz a (List.mem_cons_of_mem h ha))
    simp [G,D,hd.1,hd.2,ht.1,ht.2]

theorem zero_rate_actions (s : Schedule) (hz : ∀ h∈s, h.gamma=0 ∧ h.eta=0) (X : MatQ) :
    state s X=X ∧ observable s X=X :=
  zero_dose_actions s (zero_rate_doses s hz).1 (zero_rate_doses s hz).2 X

theorem zero_dephasing_actions (s : Schedule) (hD : D s=0) (X : MatQ) :
    state s X=Phi (alpha s) X ∧ observable s X=Psi (alpha s) X := by
  rw [state_effective, observable_effective, hD]
  simpa only [alpha,mul_one] using
    NontracialReflectionDynamics.zero_dephasing_actions (G s) 1 (G_nonneg s) zero_le_one X

def logTwoSlice : Slice := ⟨1,1,Real.log 2,zero_le_one,zero_le_one,
  Real.log_nonneg (by norm_num)⟩

theorem logTwo_coefficients : alpha [logTwoSlice]=1/2 ∧ beta [logTwoSlice]=1/4 := by
  have hl : Real.exp (-Real.log 2) = (1:ℝ)/2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<2)]
    norm_num
  have hb : Real.exp (-(Real.log 2+Real.log 2)) = (1:ℝ)/4 := by
    rw [neg_add,Real.exp_add,hl]
    norm_num
  constructor
  · simpa [alpha,G,logTwoSlice] using hl
  · simpa [beta,G,D,logTwoSlice] using hb

/-- Non-Hermitian guard uses the all-complex channel formula without density assumptions. -/
theorem imaginary_offDiagonal (s : Schedule) :
    state s (Matrix.single 0 1 Complex.I) =
      (beta s:ℂ) • Matrix.single 0 1 Complex.I := by
  rw [state_formula]
  have ht : (Matrix.single 0 1 Complex.I : MatQ).trace=0 := by
    norm_num [Matrix.trace,Fin.sum_univ_two,Matrix.single]
  have hd : NontracialReflectionDynamics.diagonalPart
      (Matrix.single 0 1 Complex.I) = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [NontracialReflectionDynamics.diagonalPart,Matrix.single]
  simp only [stateForm,ht,hd,zero_smul,sub_zero,smul_zero,zero_add]

end SKEFTHawking.QuantumNetwork.FiniteNontracialSchedule
