import SKEFTHawking.QuantumNetwork.FiniteAdaptiveReadoutDiscrimination
import SKEFTHawking.QuantumNetwork.FiniteAdaptiveKrausRealization
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Five binary projective settings on a retained qutrit

`wordTree` uses the existing finite intervention process. Both continuations are
retained at every node, including impossible histories. `wordProduct` records
chronological Kraus multiplication, and is proved equal to the actual tree run
on every complex joint input, including correlated spectator inputs.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteQutritPhysicalMemory
open Matrix FiniteInterventionProcess FiniteAdaptiveKrausRealization
open FiniteAdaptiveReadoutDiscrimination
open scoped BigOperators ComplexOrder Kronecker

abbrev Q := Fin 3
abbrev Setting := Fin 5
abbrev Mat := Matrix Q Q ℂ

def projector : Setting → Mat := ![
  !![1,0,0; 0,0,0; 0,0,0],
  !![0,0,0; 0,1,0; 0,0,0],
  !![0,0,0; 0,0,0; 0,0,1],
  !![1/2,1/2,0; 1/2,1/2,0; 0,0,0],
  !![1/2,0,1/2; 0,0,0; 1/2,0,1/2]]

theorem projector_hermitian (j : Setting) : (projector j).IsHermitian := by
  fin_cases j <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [projector, Matrix.conjTranspose_apply]

theorem projector_idempotent (j : Setting) : projector j * projector j = projector j := by
  fin_cases j <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [projector, Matrix.mul_apply, Fin.sum_univ_succ]

theorem projector_trace (j : Setting) : (projector j).trace = 1 := by
  fin_cases j <;> norm_num [projector, Matrix.trace, Fin.sum_univ_succ]

def readout (j : Setting) : FiniteInstrument Q 2 :=
  projectiveReadout (projector j) (projector_hermitian j) (projector_idempotent j)

def outcomeOperator (j : Setting) (a : Fin 2) : Mat :=
  if a = 0 then projector j else 1 - projector j

theorem outcomeOperator_hermitian (j : Setting) (a : Fin 2) :
    (outcomeOperator j a)ᴴ = outcomeOperator j a := by
  unfold outcomeOperator
  split_ifs
  · exact (projector_hermitian j).eq
  · exact (Matrix.isHermitian_one.sub (projector_hermitian j)).eq

variable (E : Type*) [Fintype E] [DecidableEq E]

def liftedOperator (j : Setting) (a : Fin 2) : Matrix (Q × E) (Q × E) ℂ :=
  outcomeOperator j a ⊗ₖ (1 : Matrix E E ℂ)

theorem local_branch (j : Setting) (a : Fin 2) (X : Matrix (Q × E) (Q × E) ℂ) :
    (localStep Q E 2 (readout j)).branch Q E 2 a X =
      liftedOperator E j a * X * (liftedOperator E j a)ᴴ := by
  rw [localStep_branch]
  simp [FiniteInstrument.branch, FiniteInstrument.lift, readout,
    projectiveReadout, krausMap, liftedOperator, outcomeOperator]

def wordTree : (w : List Setting) → Tree Q E 2 w.length
  | [] => .done
  | j :: w => .node (localStep Q E 2 (readout j)) (fun _ => wordTree w)

def wordProduct : (w : List Setting) → History 2 w.length → Matrix (Q × E) (Q × E) ℂ
  | [], _ => 1
  | j :: w, (a,h) => wordProduct w h * liftedOperator E j a

/-- Later operators act on the left, for all inputs, without terminal normalization. -/
theorem word_run (w : List Setting) (h : History 2 w.length)
    (X : Matrix (Q × E) (Q × E) ℂ) :
    run Q E 2 (wordTree E w) h X = wordProduct E w h * X * (wordProduct E w h)ᴴ := by
  induction w generalizing X with
  | nil => simp [wordTree, wordProduct, run]
  | cons j w ih =>
    rcases h with ⟨a,h⟩
    change run Q E 2 (wordTree E w) h ((localStep Q E 2 (readout j)).branch Q E 2 a X) = _
    rw [ih, local_branch, wordProduct, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]

/-- Positivity holds on arbitrary correlated system-spectator states. -/
theorem word_positive (w : List Setting) (h : History 2 w.length)
    {X : Matrix (Q × E) (Q × E) ℂ} (hX : X.PosSemidef) :
    (run Q E 2 (wordTree E w) h X).PosSemidef :=
  run_posSemidef Q E 2 _ _ hX

theorem word_normalized (w : List Setting) {X : Matrix (Q × E) (Q × E) ℂ}
    (hX : IsDensityOperator X) :
    (∀ h, 0 ≤ weight Q E 2 (wordTree E w) h X) ∧
      (∑ h, weight Q E 2 (wordTree E w) h X) = 1 :=
  normalized_weights Q E 2 _ hX

theorem word_zero (w : List Setting) (h : History 2 w.length) :
    run Q E 2 (wordTree E w) h 0 = 0 := run_zero Q E 2 _ _

/-- No leaf is filtered, even when its probability vanishes. -/
theorem word_history_card (w : List Setting) :
    Fintype.card (History 2 w.length) = 2 ^ w.length := history_card 2 _

theorem word_prefix_marginal (u v : List Setting) (h : History 2 u.length)
    (X : Matrix (Q × E) (Q × E) ℂ) :
    (∑ g, weight Q E 2 (wordTree E v) g (run Q E 2 (wordTree E u) h X)) =
      weight Q E 2 (wordTree E u) h X := prefix_marginal Q E 2 _ _ _ _

theorem word_no_future_signaling (u v w : List Setting) (h : History 2 u.length)
    (X : Matrix (Q × E) (Q × E) ℂ) :
    (∑ g, weight Q E 2 (wordTree E v) g (run Q E 2 (wordTree E u) h X)) =
    (∑ g, weight Q E 2 (wordTree E w) g (run Q E 2 (wordTree E u) h X)) :=
  no_future_signaling Q E 2 _ _ _ _ _

def systemProduct : (w : List Setting) → History 2 w.length → Mat
  | [], _ => 1
  | j :: w, (a,h) => systemProduct w h * outcomeOperator j a

theorem wordProduct_lift (w : List Setting) (h : History 2 w.length) :
    wordProduct E w h = systemProduct w h ⊗ₖ (1 : Matrix E E ℂ) := by
  induction w with
  | nil => simp [wordProduct, systemProduct]
  | cons j w ih =>
    rcases h with ⟨a,h⟩
    simp only [wordProduct, systemProduct, ih, liftedOperator,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul]

/-- Product inputs preserve their spectator, while correlated-input positivity
is already covered independently by `word_positive`. -/
theorem word_product_input (w : List Setting) (h : History 2 w.length)
    (X : Mat) (σ : Matrix E E ℂ) :
    run Q E 2 (wordTree E w) h (X ⊗ₖ σ) =
      (systemProduct w h * X * (systemProduct w h)ᴴ) ⊗ₖ σ := by
  rw [word_run, wordProduct_lift]
  simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]

theorem word_product_weight (w : List Setting) (h : History 2 w.length)
    (X : Mat) {σ : Matrix E E ℂ} (hσ : σ.trace = 1) :
    weight Q E 2 (wordTree E w) h (X ⊗ₖ σ) =
      (systemProduct w h * X * (systemProduct w h)ᴴ).trace.re := by
  unfold weight
  rw [word_product_input, Matrix.trace_kronecker, hσ, mul_one]

def rho : Mat := (1 / 3 : ℝ) • 1

theorem rho_density : IsDensityOperator rho := by
  constructor
  · have h : (1 : Mat).PosSemidef := by
      simpa using Matrix.posSemidef_conjTranspose_mul_self (1 : Mat)
    exact h.smul (by norm_num : (0 : ℝ) ≤ 1 / 3)
  · norm_num [rho, Matrix.trace, Fin.sum_univ_succ]

/-- Every entry is a separate controlled two-step experiment. -/
def selected : Matrix Setting Setting ℝ := fun i j =>
  weight Q Unit 2 (wordTree Unit [j,i]) (0,0,())
    (rho ⊗ₖ (1 : Matrix Unit Unit ℂ))

theorem selected_trace (i j : Setting) :
    selected i j = (projector i * projector j).trace.re / 3 := by
  unfold selected
  rw [word_product_weight Unit _ _ _ (by simp [Matrix.trace])]
  simp only [systemProduct, outcomeOperator, ite_true, Matrix.one_mul,
    Matrix.conjTranspose_mul, (projector_hermitian i).eq, (projector_hermitian j).eq]
  have hm : (projector i * projector j) * rho * (projector j * projector i) =
      (1 / 3 : ℝ) • (projector i * projector j * projector i) := by
    simp only [rho, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    congr 1
    calc
      (projector i * projector j) * (projector j * projector i) =
          projector i * (projector j * projector j) * projector i := by
            simp only [Matrix.mul_assoc]
      _ = _ := by rw [projector_idempotent]
  rw [hm, Matrix.trace_smul, Matrix.trace_mul_cycle, projector_idempotent]
  simp [div_eq_mul_inv, mul_comm]

/-- Twelve times the actual selected probability table. -/
def integerTable : Matrix Setting Setting ℝ :=
  !![4,0,0,2,2; 0,4,0,2,0; 0,0,4,0,2; 2,2,0,4,1; 2,0,2,1,4]

theorem selected_table : (12 : ℝ) • selected = integerTable := by
  ext i j
  rw [Matrix.smul_apply, selected_trace]
  fin_cases i <;> fin_cases j <;>
    norm_num [projector, integerTable, Matrix.mul_apply, Matrix.trace,
      Fin.sum_univ_succ, smul_eq_mul]

theorem integerTable_det : integerTable.det = 256 := by
  simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  norm_num [integerTable, Matrix.submatrix, Fin.succAbove, Fin.succ, Fin.castSucc,
    Fin.castAdd, Fin.castLE, Fin.lt_def, Fin.le_def, Fin.reduceFinMk]

theorem selected_eq : selected = (1 / 12 : ℝ) • integerTable := by
  rw [← selected_table, smul_smul]
  norm_num

theorem selected_det : selected.det = 1 / 972 := by
  rw [selected_eq, Matrix.det_smul, integerTable_det]
  norm_num

theorem selected_rank : selected.rank = 5 := by
  have h : IsUnit selected := (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr (by rw [selected_det]; norm_num))
  simpa using Matrix.rank_of_isUnit selected h

theorem outcomeOperator_idempotent (j : Setting) (a : Fin 2) :
    outcomeOperator j a * outcomeOperator j a = outcomeOperator j a := by
  unfold outcomeOperator
  split_ifs
  · exact projector_idempotent j
  · rw [sub_mul, one_mul, mul_sub, mul_one, projector_idempotent, sub_self, sub_zero]

/-- All four histories use the same chronological tree; none is conditioned. -/
theorem pair_trace (i j : Setting) (a b : Fin 2) :
    weight Q Unit 2 (wordTree Unit [j,i]) (a,b,()) (joint rho) =
      (outcomeOperator i b * outcomeOperator j a).trace.re / 3 := by
  rw [joint, word_product_weight Unit _ _ _ (by simp [Matrix.trace])]
  simp only [systemProduct, Matrix.one_mul, Matrix.conjTranspose_mul,
    outcomeOperator_hermitian]
  have hm : (outcomeOperator i b * outcomeOperator j a) * rho *
      (outcomeOperator j a * outcomeOperator i b) =
      (1 / 3 : ℝ) • (outcomeOperator i b * outcomeOperator j a * outcomeOperator i b) := by
    simp only [rho, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    congr 1
    calc
      (outcomeOperator i b * outcomeOperator j a) *
          (outcomeOperator j a * outcomeOperator i b) =
          outcomeOperator i b * (outcomeOperator j a * outcomeOperator j a) *
            outcomeOperator i b := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [outcomeOperator_idempotent]
  rw [hm, Matrix.trace_smul, Matrix.trace_mul_cycle, outcomeOperator_idempotent]
  simp [div_eq_mul_inv, mul_comm]

theorem pair_all_outcomes (i j : Setting) (a b : Fin 2) :
    weight Q Unit 2 (wordTree Unit [j,i]) (a,b,()) (joint rho) =
      if a = 0 then (if b = 0 then selected i j else 1 / 3 - selected i j)
      else (if b = 0 then 1 / 3 - selected i j else 1 / 3 + selected i j) := by
  rw [pair_trace, selected_trace]
  fin_cases a <;> fin_cases b <;>
    simp [outcomeOperator, Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub,
      projector_trace] <;> ring

theorem selected_nonneg (i j : Setting) : 0 ≤ selected i j :=
  weight_nonneg Q Unit 2 _ _ (rho_density.1.kronecker
    (by simpa using Matrix.posSemidef_conjTranspose_mul_self (1 : Matrix Unit Unit ℂ)))

theorem selected_le_third (i j : Setting) : selected i j ≤ 1 / 3 := by
  have h := congrArg (fun M : Matrix Setting Setting ℝ => M i j) selected_eq
  simp only [Matrix.smul_apply] at h
  rw [h]
  fin_cases i <;> fin_cases j <;> norm_num [integerTable]

theorem first_zero_mass (j : Setting) :
    weight Q Unit 2 (wordTree Unit [j]) (0,()) (joint rho) = 1 / 3 := by
  rw [joint, word_product_weight Unit _ _ _ (by simp [Matrix.trace])]
  simp only [systemProduct, outcomeOperator, ite_true, Matrix.one_mul,
    (projector_hermitian j).eq, rho, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, projector_idempotent, Matrix.trace_smul, projector_trace]
  norm_num

/-- The conditional mass differs from the unnormalized joint mass. -/
theorem conditional_selected (i j : Setting) :
    selected i j / weight Q Unit 2 (wordTree Unit [j]) (0,()) (joint rho) =
      3 * selected i j := by
  rw [first_zero_mass]
  ring

theorem chronology_forward_state :
    run Q Unit 2 (wordTree Unit [0,3]) (0,0,()) (joint rho) =
      joint ((1 / 6 : ℝ) • projector 3) := by
  have hp0 : projector 0 = !![1,0,0; 0,0,0; 0,0,0] := rfl
  have hp3 : projector 3 = !![1/2,1/2,0; 1/2,1/2,0; 0,0,0] := rfl
  rw [joint, word_product_input]
  congr 1
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [systemProduct, outcomeOperator, hp0, hp3, rho, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.conjTranspose_apply, Fin.reduceFinMk, Matrix.vecMul, dotProduct, Complex.star_def, map_ofNat]

theorem chronology_reverse_state :
    run Q Unit 2 (wordTree Unit [3,0]) (0,0,()) (joint rho) =
      joint ((1 / 6 : ℝ) • projector 0) := by
  have hp0 : projector 0 = !![1,0,0; 0,0,0; 0,0,0] := rfl
  have hp3 : projector 3 = !![1/2,1/2,0; 1/2,1/2,0; 0,0,0] := rfl
  rw [joint, word_product_input]
  congr 1
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [systemProduct, outcomeOperator, hp0, hp3, rho, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.conjTranspose_apply, Fin.reduceFinMk, Matrix.vecMul, dotProduct, Complex.star_def, map_ofNat]

/-- A third event distinguishes chronology even though the selected two-step
table is symmetric. This statement uses the actual appended-tree semantics. -/
theorem chronology_third_event :
    weight Q Unit 2
      (appendTree (wordTree Unit [0,3]) (fun _ => wordTree Unit [1]))
      (appendHistory (0,0,()) (0,())) (joint rho) = 1 / 12 ∧
    weight Q Unit 2
      (appendTree (wordTree Unit [3,0]) (fun _ => wordTree Unit [1]))
      (appendHistory (0,0,()) (0,())) (joint rho) = 0 := by
  have hp0 : projector 0 = !![1,0,0; 0,0,0; 0,0,0] := rfl
  have hp1 : projector 1 = !![0,0,0; 0,1,0; 0,0,0] := rfl
  have hp3 : projector 3 = !![1/2,1/2,0; 1/2,1/2,0; 0,0,0] := rfl
  unfold weight
  rw [append_run, append_run, chronology_forward_state, chronology_reverse_state]
  simp only [joint, word_product_input, Matrix.trace_kronecker]
  constructor <;>
    norm_num [systemProduct, outcomeOperator, hp0, hp1, hp3, Matrix.mul_apply,
      Matrix.trace, Fin.sum_univ_succ, Matrix.conjTranspose_apply, Fin.reduceFinMk, Matrix.vecMul, dotProduct, Complex.star_def, map_ofNat]

end SKEFTHawking.QuantumNetwork.FiniteQutritPhysicalMemory
