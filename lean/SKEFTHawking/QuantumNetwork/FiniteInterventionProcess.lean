import SKEFTHawking.QuantumNetwork.FiniteInstrument

/-! Finite realized intervention trees with retained finite environments and classical feedback.
Every branch stays unnormalized. Marginalization sums every future outcome, without postselection. -/
namespace SKEFTHawking.QuantumNetwork
open Matrix
open scoped BigOperators ComplexOrder

namespace FiniteInterventionProcess
variable (S E : Type*) [Fintype S] [DecidableEq S] [Fintype E] [DecidableEq E] (o : ℕ)

/-- Joint evolution precedes a local instrument; later nodes may depend on its outcome. -/
structure Step where
  count : ℕ
  evolution : Fin count → Matrix (S × E) (S × E) ℂ
  normalized : IsKrausChannel evolution
  instrument : FiniteInstrument S o

noncomputable def Step.branch (D : Step S E o) (a : Fin o)
    (X : Matrix (S × E) (S × E) ℂ) : Matrix (S × E) (S × E) ℂ :=
  (D.instrument.lift E).branch a (krausMap D.evolution X)

theorem Step.branch_posSemidef (D : Step S E o) (a : Fin o)
    {X : Matrix (S × E) (S × E) ℂ} (hX : X.PosSemidef) : (D.branch S E o a X).PosSemidef :=
  (D.instrument.lift E).branch_posSemidef a (krausMap_posSemidef _ hX)

theorem Step.sum_trace (D : Step S E o) (X : Matrix (S × E) (S × E) ℂ) :
    ∑ a, (D.branch S E o a X).trace = X.trace := by
  change (∑ a, ((D.instrument.lift E).branch a (krausMap D.evolution X)).trace) = _
  rw [FiniteInstrument.sum_trace, trace_krausMap D.normalized]

/-- Fixed depth, with a distinct continuation for each earlier outcome. -/
inductive Tree : ℕ → Type _
  | done : Tree 0
  | node {n : ℕ} (step : Step S E o) (next : Fin o → Tree n) : Tree (n+1)

def History : ℕ → Type
  | 0 => Unit
  | n+1 => Fin o × History n

instance historyFintype : (n : ℕ) → Fintype (History o n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => @instFintypeProd _ _ inferInstance (historyFintype n)

noncomputable def run : {n : ℕ} → Tree S E o n → History o n →
    Matrix (S × E) (S × E) ℂ → Matrix (S × E) (S × E) ℂ
  | 0, .done, _, X => X
  | _+1, .node D F, (a,h), X => run (F a) h (D.branch S E o a X)

noncomputable def weight {n : ℕ} (T : Tree S E o n) (h : History o n)
    (X : Matrix (S × E) (S × E) ℂ) : ℝ := (run S E o T h X).trace.re

theorem run_posSemidef {n : ℕ} (T : Tree S E o n) (h : History o n)
    {X : Matrix (S × E) (S × E) ℂ} (hX : X.PosSemidef) :
    (run S E o T h X).PosSemidef := by
  induction T generalizing X with
  | done => exact hX
  | node D F ih => exact ih h.1 h.2 (D.branch_posSemidef S E o h.1 hX)

theorem weight_nonneg {n : ℕ} (T : Tree S E o n) (h : History o n)
    {X : Matrix (S × E) (S × E) ℂ} (hX : X.PosSemidef) : 0 ≤ weight S E o T h X :=
  (Complex.le_def.mp (run_posSemidef S E o T h hX).trace_nonneg).1

/-- Normalization follows from the realized node maps at every depth. -/
theorem sum_trace {n : ℕ} (T : Tree S E o n) (X : Matrix (S × E) (S × E) ℂ) :
    ∑ h, (run S E o T h X).trace = X.trace := by
  induction T generalizing X with
  | done => simp [History, run]
  | node D F ih =>
    change (∑ h : Fin o × History o _, (run S E o (F h.1) h.2 (D.branch S E o h.1 X)).trace) = _
    rw [Fintype.sum_prod_type]
    simp_rw [ih]
    exact D.sum_trace S E o X

theorem sum_weight {n : ℕ} (T : Tree S E o n) (X : Matrix (S × E) (S × E) ℂ) :
    ∑ h, weight S E o T h X = X.trace.re := by
  simpa [weight] using congrArg Complex.re (sum_trace S E o T X)

theorem normalized_weights {n : ℕ} (T : Tree S E o n)
    {X : Matrix (S × E) (S × E) ℂ} (hX : IsDensityOperator X) :
    (∀ h, 0 ≤ weight S E o T h X) ∧ (∑ h, weight S E o T h X) = 1 := by
  exact ⟨fun h => weight_nonneg S E o T h hX.1, by rw [sum_weight, hX.2]; norm_num⟩

/-- Fix the initial state and the full prefix. Sum all leaves of any normalized future tree. -/
theorem prefix_marginal {n m : ℕ} (T : Tree S E o n) (h : History o n)
    (F : Tree S E o m) (X : Matrix (S × E) (S × E) ℂ) :
    (∑ f, weight S E o F f (run S E o T h X)) = weight S E o T h X :=
  sum_weight S E o F _

/-- Later choices cannot alter the earlier unpostselected marginal. -/
theorem no_future_signaling {n m l : ℕ} (T : Tree S E o n) (h : History o n)
    (F : Tree S E o m) (G : Tree S E o l) (X : Matrix (S × E) (S × E) ℂ) :
    (∑ f, weight S E o F f (run S E o T h X)) =
      ∑ g, weight S E o G g (run S E o T h X) := by
  rw [prefix_marginal, prefix_marginal]

theorem Step.branch_add (D : Step S E o) (a : Fin o)
    (X Y : Matrix (S × E) (S × E) ℂ) :
    D.branch S E o a (X+Y) = D.branch S E o a X+D.branch S E o a Y := by
  unfold Step.branch
  rw [krausMap_add, FiniteInstrument.branch_add]

theorem Step.branch_smul (D : Step S E o) (a : Fin o) (c : ℂ)
    (X : Matrix (S × E) (S × E) ℂ) :
    D.branch S E o a (c • X) = c • D.branch S E o a X := by
  unfold Step.branch
  rw [krausMap_smul, FiniteInstrument.branch_smul]

theorem run_add {n : ℕ} (T : Tree S E o n) (h : History o n)
    (X Y : Matrix (S × E) (S × E) ℂ) :
    run S E o T h (X+Y) = run S E o T h X+run S E o T h Y := by
  induction T generalizing X Y with
  | done => rfl
  | node D F ih =>
    change run S E o (F h.1) h.2 (D.branch S E o h.1 (X+Y)) = _
    rw [Step.branch_add, ih]
    cases h; rfl

theorem run_smul {n : ℕ} (T : Tree S E o n) (h : History o n) (c : ℂ)
    (X : Matrix (S × E) (S × E) ℂ) :
    run S E o T h (c • X) = c • run S E o T h X := by
  induction T generalizing X with
  | done => rfl
  | node D F ih =>
    change run S E o (F h.1) h.2 (D.branch S E o h.1 (c • X)) = _
    rw [Step.branch_smul, ih]
    cases h; rfl

theorem weight_le_one {n : ℕ} (T : Tree S E o n) (h : History o n)
    {X : Matrix (S × E) (S × E) ℂ} (hX : IsDensityOperator X) :
    weight S E o T h X ≤ 1 := by
  classical
  rw [← (normalized_weights S E o T hX).2]
  exact Finset.single_le_sum (fun a _ => weight_nonneg S E o T a hX.1) (Finset.mem_univ h)

/-- Full enumeration has exponentially many leaves in the fixed-arity representation. -/
theorem history_card (n : ℕ) : Fintype.card (History o n) = o^n := by
  induction n with
  | zero => simp [History]
  | succ n ih =>
    change Fintype.card (Fin o × History o n) = _
    simp [ih, pow_succ, Nat.mul_comm]

theorem Step.branch_zero (D : Step S E o) (a : Fin o) :
    D.branch S E o a 0 = 0 := by simp [Step.branch, FiniteInstrument.branch, krausMap]

theorem run_zero {n : ℕ} (T : Tree S E o n) (h : History o n) :
    run S E o T h 0 = 0 := by
  induction T with
  | done => rfl
  | node D F ih =>
    change run S E o (F h.1) h.2 (D.branch S E o h.1 0) = _
    rw [Step.branch_zero, ih]

/-- A channel followed by a singleton instrument embeds the ordinary one-step channel. -/
noncomputable def channelStep {k : ℕ} (K : Fin k → Matrix (S × E) (S × E) ℂ)
    (hK : IsKrausChannel K) : Step S E 1 where
  count := k
  evolution := K
  normalized := hK
  instrument := FiniteInstrument.identity

theorem channelStep_branch {k : ℕ} (K : Fin k → Matrix (S × E) (S × E) ℂ)
    (hK : IsKrausChannel K) (X : Matrix (S × E) (S × E) ℂ) :
    (channelStep S E K hK).branch S E 1 0 X = krausMap K X := by
  simp [channelStep, Step.branch, FiniteInstrument.identity, FiniteInstrument.singleton,
    FiniteInstrument.lift, FiniteInstrument.branch, krausMap]
  rfl

/-- An intervention with no preceding joint dynamics. -/
noncomputable def localStep (I : FiniteInstrument S o) : Step S E o where
  count := 1
  evolution _ := 1
  normalized := by simp [IsKrausChannel]
  instrument := I

theorem localStep_branch (I : FiniteInstrument S o) (a : Fin o)
    (X : Matrix (S × E) (S × E) ℂ) :
    (localStep S E o I).branch S E o a X = (I.lift E).branch a X := by
  simp [localStep, Step.branch, krausMap]

/-- Measurement followed by a preparation selected from its actual outcome. -/
noncomputable def feedback (D : Step (Fin 2) E 2) : Tree (Fin 2) E 2 2 :=
  .node D (fun a => .node (localStep (Fin 2) E 2 (FiniteInstrument.prepare a)) (fun _ => .done))

/-- The feedback tree has diagonal outcome support, with the earlier branch probability unchanged. -/
theorem feedback_weights (D : Step (Fin 2) E 2) (a b : Fin 2)
    (X : Matrix (Fin 2 × E) (Fin 2 × E) ℂ) :
    weight (Fin 2) E 2 (feedback E D) (a,b,()) X =
      if b=a then (D.branch (Fin 2) E 2 a X).trace.re else 0 := by
  change ((localStep (Fin 2) E 2 (FiniteInstrument.prepare a)).branch (Fin 2) E 2 b
    (D.branch (Fin 2) E 2 a X)).trace.re = _
  rw [localStep_branch]
  by_cases h : b=a
  · subst b
    rw [FiniteInstrument.lift_prepare_trace]
    simp
  · rw [FiniteInstrument.lift_prepare_other E a b h]
    simp [h]

/-- A physical input with both projective outcomes reachable. -/
noncomputable def feedbackInput : Matrix (Fin 2 × Unit) (Fin 2 × Unit) ℂ :=
  Matrix.kronecker (binaryDiagonalState (1/2)) (1 : Matrix Unit Unit ℂ)

noncomputable def feedbackExample : Tree (Fin 2) Unit 2 2 :=
  feedback Unit (localStep (Fin 2) Unit 2 FiniteInstrument.computational)

theorem feedbackInput_density : IsDensityOperator feedbackInput := by
  constructor
  · exact (binaryDiagonalState_density (r := 1/2) (by norm_num)).1.kronecker (Matrix.PosSemidef.one)
  · norm_num [feedbackInput, Matrix.trace, Matrix.diag, Matrix.kronecker_apply,
      binaryDiagonalState, Fin.sum_univ_two, Fintype.sum_prod_type, Matrix.one_apply]

private theorem feedback_first_trace (a : Fin 2) :
    ((localStep (Fin 2) Unit 2 FiniteInstrument.computational).branch (Fin 2) Unit 2 a feedbackInput).trace.re = 1/2 := by
  rw [localStep_branch]
  simp only [FiniteInstrument.branch, FiniteInstrument.lift, FiniteInstrument.computational]
  fin_cases a <;>
    norm_num [krausMap, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.kronecker_apply, FiniteMemoryProcess.basisState, feedbackInput,
      binaryDiagonalState, Fin.sum_univ_two, Fintype.sum_prod_type, Matrix.one_apply]

/-- Actual evaluator table: both feedback paths have probability one half; cross paths are zero. -/
theorem feedback_example_weights (a b : Fin 2) :
    weight (Fin 2) Unit 2 feedbackExample (a,b,()) feedbackInput = if b=a then 1/2 else 0 := by
  rw [feedbackExample, feedback_weights, feedback_first_trace]

end FiniteInterventionProcess
end SKEFTHawking.QuantumNetwork
