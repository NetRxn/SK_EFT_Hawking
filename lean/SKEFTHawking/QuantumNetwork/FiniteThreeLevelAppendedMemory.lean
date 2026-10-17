import SKEFTHawking.QuantumNetwork.FiniteThreeLevelCompressedMemoryObservabilityExamples

/-!
# Actual finite lists of unread pulse/reset interventions

The reverse and original binary instruments occur once, with exactly one central
reset. Each intervening channel is followed by a singleton identity instrument.
All branch identities below hold on arbitrary complex inputs.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteThreeLevelAppendedMemory
open Matrix FiniteInterventionProcess FiniteAdaptiveKrausRealization
open FiniteThreeLevelStationaryStrategyReflection
open FiniteThreeLevelStationaryStrategyTransferExamples
open FiniteThreeLevelCompressedMemoryObservability
open FiniteThreeLevelPositiveHistory (Q MatQ Phi Psi rhoN)
open FiniteThreeLevelHistoryTransfer (rotate pulseResetKraus pulseReset_normalized pulseReset_state)
open scoped BigOperators

/-- Physical retention and free dimensionless phase of one actual channel. -/
structure Pulse where
  retention : ℝ
  nonneg : 0 ≤ retention
  le_one : retention ≤ 1
  phase : ℝ

abbrev B := pairedArity 2 1

def pulseStep (ω : Q → ℝ) (q : Pulse) : Step Q Unit B :=
  recodeStep (channelStep Q Unit
    (fun k => GibbsMultilevelReflection.joint (pulseResetKraus q.retention ω q.phase k))
    (GibbsMultilevelReflection.joint_normalized _
      (pulseReset_normalized q.retention q.nonneg q.le_one ω q.phase))) (resetLabel 2 1)

theorem pulseStep_branch (ω : Q → ℝ) (q : Pulse) (X : MatQ) :
    (pulseStep ω q).branch Q Unit B (resetLabel 2 1 0) (joint X) =
      joint (rotate ω (-q.phase) (Phi q.retention X)) := by
  rw [pulseStep, recodeStep_branch, channelStep_branch]
  change krausMap (fun k => GibbsMultilevelReflection.joint
    (pulseResetKraus q.retention ω q.phase k)) (GibbsMultilevelReflection.joint X) = _
  rw [GibbsMultilevelReflection.joint_kraus, pulseReset_state _ q.nonneg q.le_one]
  rfl

theorem pulseStep_invalid (ω : Q → ℝ) (q : Pulse) (b : Fin B)
    (hb : b ≠ resetLabel 2 1 0) (X : Matrix (Q × Unit) (Q × Unit) ℂ) :
    (pulseStep ω q).branch Q Unit B b X = 0 := by
  apply recodeStep_invalid
  rintro ⟨a, rfl⟩
  exact hb (congrArg (resetLabel 2 1) (Subsingleton.elim a 0))

/-- Append each actual pulse to the remaining unread evolution and final instrument. -/
def continuation (ω : Q → ℝ) : (qs : List Pulse) → Tree Q Unit B (qs.length+1)
  | [] => recodeTree (originalLabel 2 1) 0 binaryTree
  | q::qs => appendTree (.node (pulseStep ω q) (fun _ => .done))
      (fun _ => continuation ω qs)

def suffixHistory : (qs : List Pulse) → History 2 1 → History B (qs.length+1)
  | [], v => recodeHistory (originalLabel 2 1) v
  | _::qs, v => (resetLabel 2 1 0, suffixHistory qs v)

/-- Chronological state order: the first list entry acts first. -/
def stateAction (ω : Q → ℝ) : List Pulse → MatQ → MatQ
  | [], X => X
  | q::qs, X => stateAction ω qs (rotate ω (-q.phase) (Phi q.retention X))

theorem continuation_run (ω : Q → ℝ) (qs : List Pulse) (v : History 2 1) (X : MatQ) :
    unJoint (run Q Unit B (continuation ω qs) (suffixHistory qs v) (joint X)) =
      branch binaryTree v (stateAction ω qs X) := by
  induction qs generalizing X with
  | nil => rw [continuation, suffixHistory, recode_run]; rfl
  | cons q qs ih =>
    change unJoint (run Q Unit B (continuation ω qs) (suffixHistory qs v)
      ((pulseStep ω q).branch Q Unit B (resetLabel 2 1 0) (joint X))) = _
    rw [pulseStep_branch, ih]
    rfl

theorem suffixHistory_injective (qs : List Pulse) : Function.Injective (suffixHistory qs) := by
  induction qs with
  | nil => exact recodeHistory_injective (originalLabel 2 1) 1
  | cons q qs ih => intro v w he; exact ih (Prod.mk.inj he).2

theorem continuation_invalid (ω : Q → ℝ) (qs : List Pulse)
    (v : History B (qs.length+1)) (hv : v ∉ Set.range (suffixHistory qs))
    (X : Matrix (Q × Unit) (Q × Unit) ℂ) :
    run Q Unit B (continuation ω qs) v X = 0 := by
  induction qs generalizing X with
  | nil => exact recode_invalid_zero _ _ _ v hv X
  | cons q qs ih =>
    rcases v with ⟨b,v⟩
    by_cases hb : b = resetLabel 2 1 0
    · subst b
      have ht : v ∉ Set.range (suffixHistory qs) := by
        rintro ⟨w, rfl⟩
        exact hv ⟨w, rfl⟩
      exact ih v ht _
    · change run Q Unit B (continuation ω qs) v ((pulseStep ω q).branch Q Unit B b X) = 0
      rw [pulseStep_invalid ω q b hb, run_zero]

def appendedTree (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (ω : Q → ℝ) (qs : List Pulse) :
    Tree Q Unit B (qs.length+3) :=
  .node (recodeStep (localStep Q Unit _ (reverseInstrument binaryTree binary_stationary))
    (reverseLabel 2 1)) (fun _ =>
      .node (resetStep 2 1 (p*p) (mul_nonneg hp hp) (by nlinarith))
        (fun _ => continuation ω qs))

def encodedHistory (qs : List Pulse) (u v : History 2 1) : History B (qs.length+3) :=
  (reverseLabel 2 1 ((historyEquiv 2 1).symm u), resetLabel 2 1 0, suffixHistory qs v)

theorem encodedHistory_injective (qs : List Pulse) : Function.Injective
    (fun uv : History 2 1 × History 2 1 => encodedHistory qs uv.1 uv.2) := by
  intro ⟨u,v⟩ ⟨w,z⟩ he
  have h := Prod.mk.inj he
  exact Prod.ext ((historyEquiv 2 1).symm.injective ((reverseLabel 2 1).injective h.1))
    (suffixHistory_injective qs (Prod.mk.inj h.2).2)

theorem appended_run (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (ω : Q → ℝ)
    (qs : List Pulse) (u v : History 2 1) (X : MatQ) :
    unJoint (run Q Unit B (appendedTree p hp hp1 ω qs) (encodedHistory qs u v) (joint X)) =
      branch binaryTree v (stateAction ω qs (Phi (p*p) (reverseBranch binaryTree u X))) := by
  simp only [appendedTree, encodedHistory, run, recodeStep_branch, localStep_joint,
    reverseInstrument_branch, Equiv.apply_symm_apply, resetStep_branch]
  exact continuation_run ω qs v _

theorem appended_invalid_zero (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (ω : Q → ℝ)
    (qs : List Pulse) (v : History B (qs.length+3))
    (hv : v ∉ Set.range (fun uv : History 2 1 × History 2 1 => encodedHistory qs uv.1 uv.2))
    (X : Matrix (Q × Unit) (Q × Unit) ℂ) :
    run Q Unit B (appendedTree p hp hp1 ω qs) v X = 0 := by
  rcases v with ⟨a,b,v⟩
  by_cases ha : a ∈ Set.range (reverseLabel 2 1)
  · obtain ⟨a,rfl⟩ := ha
    by_cases hb : b = resetLabel 2 1 0
    · subst b
      have ht : v ∉ Set.range (suffixHistory qs) := by
        rintro ⟨w,rfl⟩
        apply hv
        refine ⟨(historyEquiv 2 1 a,w), ?_⟩
        simp only [encodedHistory, Equiv.symm_apply_apply]
      exact continuation_invalid ω qs v ht _
    · change run Q Unit B (continuation ω qs) v
        ((resetStep 2 1 (p*p) _ _).branch Q Unit B b _) = 0
      rw [resetStep_invalid _ _ _ _ _ b hb, run_zero]
  · simp only [appendedTree, run]
    rw [recodeStep_invalid _ _ a ha, Step.branch_zero, run_zero]

theorem appended_encoded_sum (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (ω : Q → ℝ)
    (qs : List Pulse) (X : Matrix (Q × Unit) (Q × Unit) ℂ) :
    (∑ uv : History 2 1 × History 2 1,
      run Q Unit B (appendedTree p hp hp1 ω qs) (encodedHistory qs uv.1 uv.2) X) =
      ∑ v, run Q Unit B (appendedTree p hp hp1 ω qs) v X :=
  Fintype.sum_of_injective _ (encodedHistory_injective qs) _ _
    (fun v hv => appended_invalid_zero p hp hp1 ω qs v hv X) (fun _ => rfl)

theorem appended_probabilities (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (ω : Q → ℝ)
    (qs : List Pulse) :
    (∀ v, 0 ≤ weight Q Unit B (appendedTree p hp hp1 ω qs) v (joint rhoN)) ∧
    (∑ v, weight Q Unit B (appendedTree p hp hp1 ω qs) v (joint rhoN)) = 1 :=
  normalized_weights Q Unit B _ FiniteThreeLevelPositiveHistory.joint_density

theorem empty_tree (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (ω : Q → ℝ) :
    appendedTree p hp hp1 ω [] = pairedTree binaryTree (by decide) binary_stationary p hp hp1 := rfl

def retention : List Pulse → ℝ
  | [] => 1
  | q::qs => q.retention * retention qs

def totalPhase : List Pulse → ℝ
  | [] => 0
  | q::qs => q.phase + totalPhase qs

theorem retention_nonneg (qs : List Pulse) : 0 ≤ retention qs := by
  induction qs with
  | nil => norm_num [retention]
  | cons q qs ih => exact mul_nonneg q.nonneg ih

theorem retention_le_one (qs : List Pulse) : retention qs ≤ 1 := by
  induction qs with
  | nil => exact le_rfl
  | cons q qs ih =>
    exact (mul_le_mul_of_nonneg_left ih q.nonneg).trans (by simpa using q.le_one)

theorem retention_eq_prod (qs : List Pulse) : retention qs = (qs.map Pulse.retention).prod := by
  induction qs <;> simp_all [retention]

theorem totalPhase_eq_sum (qs : List Pulse) : totalPhase qs = (qs.map Pulse.phase).sum := by
  induction qs <;> simp_all [totalPhase]

theorem Phi_trace (q : ℝ) (X : MatQ) : (Phi q X).trace = X.trace := by
  simp only [Phi, Matrix.trace_add, Matrix.trace_smul, FiniteThreeLevelPositiveHistory.rhoN_trace,
    smul_eq_mul]
  ring

theorem Phi_comp (p q : ℝ) (X : MatQ) : Phi p (Phi q X) = Phi (p*q) X := by
  simp only [Phi, Matrix.trace_add, Matrix.trace_smul, FiniteThreeLevelPositiveHistory.rhoN_trace,
    smul_eq_mul]
  push_cast
  module

theorem rotate_Phi (ω : Q → ℝ) (t q : ℝ) (X : MatQ) :
    rotate ω t (Phi q X) = Phi q (rotate ω t X) := by
  simp only [Phi, map_add, map_smul, FiniteThreeLevelHistoryTransfer.rotate_equilibrium,
    FiniteThreeLevelHistoryTransfer.rotate_trace]

theorem stateAction_formula (ω : Q → ℝ) (qs : List Pulse) (X : MatQ) :
    stateAction ω qs X = rotate ω (-totalPhase qs) (Phi (retention qs) X) := by
  induction qs generalizing X with
  | nil => simp [stateAction, totalPhase, retention, FiniteThreeLevelPositiveHistory.Phi_one,
      FiniteThreeLevelHistoryTransfer.rotate_zero]
  | cons q qs ih =>
    rw [stateAction, ih, ← rotate_Phi, Phi_comp, FiniteThreeLevelHistoryTransfer.rotate_group]
    simp only [totalPhase, retention]
    congr 1 <;> congr 1 <;> ring

/-- The observable order reverses the chronological state order before simplification. -/
def observableAction (ω : Q → ℝ) : List Pulse → MatQ → MatQ
  | [], X => X
  | q::qs, X => FinitePositiveKernel.GibbsObservable.Channel.heisenberg
      (pulseResetKraus q.retention ω q.phase) (observableAction ω qs X)

theorem observableAction_formula (ω : Q → ℝ) (qs : List Pulse) (X : MatQ) :
    observableAction ω qs X = rotate ω (totalPhase qs) (Psi (retention qs) X) := by
  induction qs generalizing X with
  | nil => simp [observableAction, totalPhase, retention, FiniteThreeLevelPositiveHistory.Psi_one,
      FiniteThreeLevelHistoryTransfer.rotate_zero]
  | cons q qs ih =>
    rw [observableAction, FiniteThreeLevelHistoryTransfer.pulseReset_observable _ q.nonneg q.le_one,
      ih, ← FiniteThreeLevelHistoryTransfer.rotate_Psi, FiniteThreeLevelPositiveHistory.Psi_comp,
      FiniteThreeLevelHistoryTransfer.rotate_group]
    rfl

/-- Stationarity is inherited from each actual pulse, separately from normalization. -/
theorem stateAction_stationary (ω : Q → ℝ) (qs : List Pulse) : stateAction ω qs rhoN = rhoN := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    have hr : Phi q.retention rhoN = rhoN := by
      simp only [Phi, FiniteThreeLevelPositiveHistory.rhoN_trace, one_smul]
      module
    simpa only [stateAction, hr, FiniteThreeLevelHistoryTransfer.rotate_equilibrium] using ih

theorem observableAction_commutes (ω : Q → ℝ) (qs : List Pulse) (p : ℝ) (X : MatQ) :
    observableAction ω qs (Psi p X) = Psi p (observableAction ω qs X) := by
  induction qs generalizing X with
  | nil => rfl
  | cons q qs ih =>
    rw [observableAction, ih,
      FiniteThreeLevelHistoryTransfer.pulseReset_commutes _ q.nonneg q.le_one]
    rfl

def appendedTable (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (ω : Q → ℝ) (qs : List Pulse) : Table :=
  fun i j => weight Q Unit B (appendedTree p hp hp1 ω qs)
    (encodedHistory qs (i,()) (j,())) (joint rhoN)

theorem appendedTable_eq_inserted (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (ω : Q → ℝ) (qs : List Pulse) (i j : Fin 2) :
    appendedTable p hp hp1 ω qs i j =
      (FiniteThreeLevelStationaryStrategyTransfer.insertedKernel binaryTree p (by decide)
        binary_stationary hp hp1 (pulseResetKraus (retention qs) ω (totalPhase qs))
        (pulseReset_normalized _ (retention_nonneg qs) (retention_le_one qs) _ _)
        (i,()) (j,())).re := by
  have he := appended_run p hp hp1 ω qs (i,()) (j,()) rhoN
  rw [stateAction_formula] at he
  have hi := FiniteThreeLevelStationaryStrategyTransfer.inserted_run binaryTree p (by decide)
    binary_stationary hp hp1 (pulseResetKraus (retention qs) ω (totalPhase qs))
    (pulseReset_normalized _ (retention_nonneg qs) (retention_le_one qs) _ _)
    (i,()) (j,()) rhoN
  rw [pulseReset_state _ (retention_nonneg qs) (retention_le_one qs)] at hi
  have ht := congrArg (fun X : MatQ => X.trace.re) (he.trans hi.symm)
  simpa only [appendedTable, FiniteThreeLevelStationaryStrategyTransfer.insertedKernel, weight,
    unJoint_trace, Complex.ofReal_re] using ht

theorem appendedTable_eq_pulseTable (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (qs : List Pulse) :
    appendedTable p hp hp1 leakingFrequencies qs =
      pulseTable p hp hp1 (retention qs) (retention_nonneg qs) (retention_le_one qs) (totalPhase qs) := by
  funext i j
  exact appendedTable_eq_inserted p hp hp1 leakingFrequencies qs i j

theorem appendedTable_probability (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (qs : List Pulse) :
    ProbabilityTable (appendedTable p hp hp1 leakingFrequencies qs) := by
  rw [appendedTable_eq_pulseTable]
  exact pulseTable_probability p hp hp1 _ (retention_nonneg qs) (retention_le_one qs) _

theorem appendedTable_law (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (qs : List Pulse) :
    BinaryLaw (appendedTable p hp hp1 leakingFrequencies qs)
      (p^2 * retention qs * phaseResponse (totalPhase qs)) := by
  rw [appendedTable_eq_pulseTable]
  exact pulseTable_law p hp hp1 _ (retention_nonneg qs) (retention_le_one qs) _

theorem appendedTable_row (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (qs : List Pulse) (i : Fin 2) :
    ∑ j, appendedTable p hp hp1 leakingFrequencies qs i j = labelMass i := by
  have hl := appendedTable_law p hp hp1 qs
  dsimp only [BinaryLaw] at hl
  simp only [hl, Fin.sum_univ_two]
  fin_cases i <;> norm_num [labelMass, labelSign] <;> ring

theorem appendedTable_column (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (qs : List Pulse) (j : Fin 2) :
    ∑ i, appendedTable p hp hp1 leakingFrequencies qs i j = labelMass j := by
  have hl := appendedTable_law p hp hp1 qs
  dsimp only [BinaryLaw] at hl
  simp only [hl, Fin.sum_univ_two]
  fin_cases j <;> norm_num [labelMass, labelSign] <;> ring

end SKEFTHawking.QuantumNetwork.FiniteThreeLevelAppendedMemory
