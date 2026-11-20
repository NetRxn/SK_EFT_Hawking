import SKEFTHawking.QuantumNetwork.FiniteQutritPhysicalMemoryExamples
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# The symmetric carrier of the original qutrit experiment

The initial state and the original binary instruments determine this carrier.
The sixth operator is an effect obtained from an actual two-command branch.
Feature operators and unnormalized branch states have different scaling.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteQutritInvariantCarrier
open Matrix FiniteInterventionProcess FiniteAdaptiveKrausRealization
open FiniteQutritPhysicalMemory FiniteQutritPhysicalMemoryExamples
open scoped BigOperators ComplexOrder Kronecker

private theorem vec6_last {α : Type*} (a b c d e f : α) :
    ![a,b,c,d,e,f] (5 : Fin 6) = f := rfl

abbrev Index := Fin 6

def complement : Mat := 1 - projector 3
def escape : Mat := complement * projector 4 * complement

theorem escape_matrix : escape =
    !![1/8,-1/8,1/4; -1/8,1/8,-1/4; 1/4,-1/4,1/2] := by
  have hb : complement = !![1/2,-1/2,0; -1/2,1/2,0; 0,0,1] := by
    have hp3 : projector 3 = !![1/2,1/2,0; 1/2,1/2,0; 0,0,0] := rfl
    unfold complement
    rw [hp3]
    ext a b
    fin_cases a <;> fin_cases b <;> norm_num [Matrix.one_apply, Fin.ext_iff, Matrix.cons_val_two]
  have hp4 : projector 4 = !![1/2,0,1/2; 0,0,0; 1/2,0,1/2] := rfl
  unfold escape
  rw [hb, hp4]
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.cons_val_two]

theorem escape_hermitian : escape.IsHermitian := by
  rw [escape_matrix]
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [Matrix.conjTranspose_apply, Matrix.one_apply, map_ofNat, Fin.ext_iff, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec6_last]

theorem escape_positive : escape.PosSemidef := by
  have hp : (projector 4).PosSemidef := by
    simpa only [(projector_hermitian 4).eq, projector_idempotent] using
      Matrix.posSemidef_conjTranspose_mul_self (projector 4)
  have hc : complementᴴ = complement :=
    (Matrix.isHermitian_one.sub (projector_hermitian 3)).eq
  simpa only [escape, hc] using hp.mul_mul_conjTranspose_same complement

theorem escape_trace : escape.trace = 3/4 := by
  rw [escape_matrix]
  norm_num [Matrix.trace, Fin.sum_univ_succ, Matrix.one_apply, map_ofNat, Fin.ext_iff, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec6_last]

theorem escape_square : escape * escape = (3/4 : ℂ) • escape := by
  rw [escape_matrix]
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.smul_apply, smul_eq_mul]

theorem escape_prefix_state :
    run Q Unit 2 (wordTree Unit [4,3]) (0,1,()) (joint rho) =
      joint ((1/3 : ℂ) • escape) := by
  have hr : rho = (1/3 : ℂ) • (1 : Mat) := by ext a b; simp [rho]
  rw [joint, word_product_input]
  congr 1
  simp only [systemProduct, outcomeOperator, ite_true, Matrix.one_mul,
    show (1 : Fin 2) ≠ 0 by decide, ite_false, Matrix.conjTranspose_mul,
    (projector_hermitian 4).eq, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    (projector_hermitian 3).eq, hr, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  change (1/3 : ℂ) • ((complement * projector 4) * (projector 4 * complement)) = _
  rw [show (complement * projector 4) * (projector 4 * complement) =
    complement * (projector 4 * projector 4) * complement by simp only [Matrix.mul_assoc],
    projector_idempotent]
  rfl

theorem escape_prefix_mass :
    weight Q Unit 2 (wordTree Unit [4,3]) (0,1,()) (joint rho) = 1/4 := by
  unfold weight
  rw [escape_prefix_state, joint_trace, Matrix.trace_smul, escape_trace]
  norm_num

theorem old_projector_missing_entry (j : Setting) : projector j 1 2 = 0 := by
  fin_cases j <;> norm_num [projector, Fin.ext_iff, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec6_last]

theorem old_span_missing_entry {X : Mat}
    (hX : X ∈ Submodule.span ℂ (Set.range projector)) : X 1 2 = 0 := by
  induction hX using Submodule.span_induction with
  | mem X h => obtain ⟨j,rfl⟩ := h; exact old_projector_missing_entry j
  | zero => rfl
  | add X Y _ _ hX hY => simp only [Matrix.add_apply, hX, hY, add_zero]
  | smul c X _ hX => simp only [Matrix.smul_apply, hX, smul_zero]

theorem actual_branch_escapes_old_span :
    (1/3 : ℂ) • escape ∉ Submodule.span ℂ (Set.range projector) := by
  intro h
  have he := old_span_missing_entry h
  norm_num [escape_matrix, Matrix.smul_apply, smul_eq_mul, Fin.ext_iff, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec6_last] at he

def effect : Index → Mat := ![projector 0, projector 1, projector 2,
  projector 3, projector 4, escape]

theorem effect_old (j : Setting) : effect j.castSucc = projector j := by
  fin_cases j <;> rfl

theorem effect_sixth : effect 5 = escape := rfl

theorem effect_symmetric (i : Index) : (effect i).IsSymm := by
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [effect, projector, escape_matrix, Matrix.transpose_apply, Fin.ext_iff, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec6_last]

theorem effect_hermitian (i : Index) : (effect i).IsHermitian := by
  fin_cases i
  · exact projector_hermitian 0
  · exact projector_hermitian 1
  · exact projector_hermitian 2
  · exact projector_hermitian 3
  · exact projector_hermitian 4
  · exact escape_hermitian

def symmetricCarrier : Submodule ℂ Mat where
  carrier := {X | X.IsSymm}
  zero_mem' := Matrix.isSymm_zero
  add_mem' := fun hX hY => hX.add hY
  smul_mem' := fun c _ hX => hX.smul c

@[simp] theorem mem_symmetricCarrier (X : Mat) :
    X ∈ symmetricCarrier ↔ X.IsSymm := Iff.rfl

def coordinates : Mat →ₗ[ℂ] (Index → ℂ) where
  toFun X := ![X 0 0, X 1 1, X 2 2, X 0 1, X 0 2, X 1 2]
  map_add' X Y := by ext i; fin_cases i <;> rfl
  map_smul' c X := by ext i; fin_cases i <;> rfl

def symmetricMatrix (c : Index → ℂ) : Mat :=
  !![c 0,c 3,c 4; c 3,c 1,c 5; c 4,c 5,c 2]

theorem symmetricMatrix_mem (c : Index → ℂ) : symmetricMatrix c ∈ symmetricCarrier := by
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

def coordinateEquiv : symmetricCarrier ≃ₗ[ℂ] (Index → ℂ) where
  toFun X := coordinates X
  invFun c := ⟨symmetricMatrix c, symmetricMatrix_mem c⟩
  left_inv X := by
    apply Subtype.ext
    ext a b
    have h := X.property
    fin_cases a <;> fin_cases b <;>
      first | rfl | exact h.apply _ _
  right_inv c := by ext i; fin_cases i <;> rfl
  map_add' X Y := coordinates.map_add X Y
  map_smul' c X := coordinates.map_smul c X

theorem symmetric_dimension : Module.finrank ℂ symmetricCarrier = 6 := by
  rw [coordinateEquiv.finrank_eq, Module.finrank_pi]
  rfl

theorem rho_mem : rho ∈ symmetricCarrier := Matrix.isSymm_one.smul _

theorem outcome_symmetric (j : Setting) (a : Fin 2) : (outcomeOperator j a).IsSymm := by
  have hp : (projector j).IsSymm := by
    rw [← effect_old j]
    exact effect_symmetric _
  unfold outcomeOperator
  split_ifs
  · exact hp
  · exact Matrix.isSymm_one.sub hp

def systemBranch (j : Setting) (a : Fin 2) : Mat →ₗ[ℂ] Mat where
  toFun X := outcomeOperator j a * X * outcomeOperator j a
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp

theorem branch_invariant (j : Setting) (a : Fin 2) {X : Mat}
    (hX : X ∈ symmetricCarrier) : systemBranch j a X ∈ symmetricCarrier := by
  change (outcomeOperator j a * X * outcomeOperator j a).transpose = _
  rw [Matrix.transpose_mul, Matrix.transpose_mul, (outcome_symmetric j a).eq,
    hX.eq]
  simp only [systemBranch, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_assoc]


def systemRun : (w : List Setting) → History 2 w.length → Mat → Mat
  | [], _, X => X
  | j :: w, (a,h), X => systemRun w h (systemBranch j a X)

theorem systemRun_invariant (w : List Setting) (h : History 2 w.length) {X : Mat}
    (hX : X ∈ symmetricCarrier) : systemRun w h X ∈ symmetricCarrier := by
  induction w generalizing X with
  | nil => exact hX
  | cons j w ih => exact ih h.2 (branch_invariant j h.1 hX)

theorem systemRun_product (w : List Setting) (h : History 2 w.length) (X : Mat) :
    systemRun w h X = systemProduct w h * X * (systemProduct w h)ᴴ := by
  induction w generalizing X with
  | nil => simp [systemRun, systemProduct]
  | cons j w ih =>
    rcases h with ⟨a,h⟩
    simp only [systemRun, ih, systemProduct, Matrix.conjTranspose_mul,
      outcomeOperator_hermitian, systemBranch, LinearMap.coe_mk, AddHom.coe_mk]
    simp only [Matrix.mul_assoc]

theorem actual_run_joint (w : List Setting) (h : History 2 w.length) (X : Mat) :
    run Q Unit 2 (wordTree Unit w) h (joint X) = joint (systemRun w h X) := by
  rw [joint, word_product_input, systemRun_product]
  rfl

theorem every_reachable_state_symmetric (w : List Setting) (h : History 2 w.length) :
    systemRun w h rho ∈ symmetricCarrier := systemRun_invariant w h rho_mem


def combination : (Index → ℂ) →ₗ[ℂ] Mat where
  toFun c := ∑ i, c i • effect i
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.smul_sum, smul_smul]

theorem combination_mem (c : Index → ℂ) : combination c ∈ symmetricCarrier :=
  by
    change (∑ i, c i • effect i) ∈ symmetricCarrier
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (effect_symmetric i))

def effectCoefficients (X : Mat) : Index → ℂ :=
  ![X 0 0 - X 0 1 - X 0 2, X 1 1 - X 0 1 + X 1 2,
    X 2 2 - X 0 2 + X 1 2, 2 * X 0 1 - X 1 2,
    2 * X 0 2 + 2 * X 1 2, -4 * X 1 2]

theorem combination_inverse (X : symmetricCarrier) :
    combination (effectCoefficients X) = X := by
  have hs := X.property
  have h10 := hs.apply 0 1
  have h20 := hs.apply 0 2
  have h21 := hs.apply 1 2
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [combination, effectCoefficients, effect, projector, escape_matrix,
      Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, vec6_last, smul_eq_mul,
      h10, h20, h21] <;> ring

theorem coefficients_inverse (c : Index → ℂ) : effectCoefficients (combination c) = c := by
  ext i
  fin_cases i <;>
    simp [combination, effectCoefficients, effect, projector, escape_matrix,
      Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, vec6_last, smul_eq_mul] <;> ring

def effectEquiv : (Index → ℂ) ≃ₗ[ℂ] symmetricCarrier where
  toFun c := ⟨combination c, combination_mem c⟩
  invFun X := effectCoefficients X
  left_inv := coefficients_inverse
  right_inv X := Subtype.ext (combination_inverse X)
  map_add' c d := Subtype.ext (combination.map_add c d)
  map_smul' a c := Subtype.ext (combination.map_smul a c)

def effectBasis : Module.Basis Index ℂ symmetricCarrier :=
  (Pi.basisFun ℂ Index).map effectEquiv

theorem effectBasis_apply (i : Index) : (effectBasis i : Mat) = effect i := by
  simp [effectBasis, Module.Basis.map_apply, Pi.basisFun_apply, effectEquiv, combination]

theorem effect_span : Submodule.span ℂ (Set.range effect) = symmetricCarrier := by
  apply le_antisymm
  · exact Submodule.span_le.mpr (by rintro X ⟨i,rfl⟩; exact effect_symmetric i)
  · intro X hX
    have he : combination (effectCoefficients X) = X := combination_inverse ⟨X,hX⟩
    rw [← he]
    change (∑ i, effectCoefficients X i • effect i) ∈ _
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i,rfl⟩))

def prefixFirst : Index → Setting := ![0,1,2,3,4,4]
def prefixSecond : Index → Setting := ![0,1,2,3,4,3]
def prefixWord (i : Index) : List Setting := [prefixFirst i, prefixSecond i]
def prefixHistory (i : Index) : History 2 (prefixWord i).length :=
  if i = 5 then (0,1,()) else (0,0,())
def suffixFirst : Index → Setting := ![0,1,2,3,4,3]
def suffixSecond : Index → Setting := ![0,1,2,3,4,4]
def suffixWord (i : Index) : List Setting := [suffixFirst i, suffixSecond i]
def suffixHistory (i : Index) : History 2 (suffixWord i).length :=
  if i = 5 then (1,0,()) else (0,0,())

theorem prefix_length (i : Index) : (prefixWord i).length = 2 := by
  rfl

theorem suffix_length (i : Index) : (suffixWord i).length = 2 := by
  rfl

theorem prefix_systemState (i : Index) :
    systemRun (prefixWord i) (prefixHistory i) rho = (1/3 : ℂ) • effect i := by
  have hr : rho = (1/3 : ℂ) • (1 : Mat) := by ext a b; simp [rho]
  fin_cases i
  all_goals try {
    simp [prefixWord, prefixFirst, prefixSecond, prefixHistory, effect,
      systemRun, systemBranch, outcomeOperator, hr, projector_idempotent, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, vec6_last, Fin.ext_iff]
  }
  change systemRun [4,3] (0,1,()) rho = (1/3 : ℂ) • escape
  have h := escape_prefix_state
  rw [actual_run_joint] at h
  ext a b
  have he := congrArg (fun X : Matrix (Q × Unit) (Q × Unit) ℂ => X (a,()) (b,())) h
  simpa [joint, Matrix.kroneckerMap_apply] using he

def reachableStates : Set Mat := {X | ∃ w h, X = systemRun w h rho}

theorem reachable_span : Submodule.span ℂ reachableStates = symmetricCarrier := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro X ⟨w,h,rfl⟩
    exact every_reachable_state_symmetric w h
  · rw [← effect_span]
    apply Submodule.span_le.mpr
    rintro X ⟨i,rfl⟩
    have h : (1/3 : ℂ) • effect i ∈ Submodule.span ℂ reachableStates := by
      rw [← prefix_systemState i]
      exact Submodule.subset_span ⟨prefixWord i,prefixHistory i,rfl⟩
    have hh := Submodule.smul_mem (Submodule.span ℂ reachableStates) (3 : ℂ) h
    have hm : (3 : ℂ) • ((1/3 : ℂ) • effect i) = effect i := by
      rw [smul_smul]; norm_num
    rw [hm] at hh
    exact hh

theorem least_invariant (T : Submodule ℂ Mat) (hρ : rho ∈ T)
    (hinv : ∀ j a X, X ∈ T → systemBranch j a X ∈ T) : symmetricCarrier ≤ T := by
  rw [← reachable_span]
  apply Submodule.span_le.mpr
  rintro X ⟨w,h,rfl⟩
  have hm : ∀ w (h : History 2 w.length) X, X ∈ T → systemRun w h X ∈ T := by
    intro w
    induction w with
    | nil => intro h X hX; exact hX
    | cons j w ih => intro h X hX; exact ih h.2 _ (hinv j h.1 X hX)
  exact hm w h rho hρ


def commonCut : FinitePhysicalMemoryDimension.CommonCut Q Unit Index Index 2 where
  initial := joint rho
  density := FiniteQutritPhysicalMemoryExamples.attainer.density
  prefixLength i := (prefixWord i).length
  prefixTree i := wordTree Unit (prefixWord i)
  prefixHistory := prefixHistory
  suffixLength i := (suffixWord i).length
  suffixTree i := wordTree Unit (suffixWord i)
  suffixHistory := suffixHistory

theorem commonCut_prefix (j : Index) :
    commonCut.prefixState j = joint ((1/3 : ℂ) • effect j) := by
  change run Q Unit 2 (wordTree Unit (prefixWord j)) (prefixHistory j) (joint rho) = _
  rw [actual_run_joint, prefix_systemState]

theorem suffix_effect (i : Index) :
    (systemProduct (suffixWord i) (suffixHistory i))ᴴ *
      systemProduct (suffixWord i) (suffixHistory i) = effect i := by
  have hp (j : Setting) : systemProduct [j,j] (0,0,()) = projector j := by
    simp [systemProduct, outcomeOperator, projector_idempotent]
  fin_cases i
  · change (systemProduct [0,0] (0,0,()))ᴴ * systemProduct [0,0] (0,0,()) = projector 0
    rw [hp, (projector_hermitian 0).eq, projector_idempotent]
  · change (systemProduct [1,1] (0,0,()))ᴴ * systemProduct [1,1] (0,0,()) = projector 1
    rw [hp, (projector_hermitian 1).eq, projector_idempotent]
  · change (systemProduct [2,2] (0,0,()))ᴴ * systemProduct [2,2] (0,0,()) = projector 2
    rw [hp, (projector_hermitian 2).eq, projector_idempotent]
  · change (systemProduct [3,3] (0,0,()))ᴴ * systemProduct [3,3] (0,0,()) = projector 3
    rw [hp, (projector_hermitian 3).eq, projector_idempotent]
  · change (systemProduct [4,4] (0,0,()))ᴴ * systemProduct [4,4] (0,0,()) = projector 4
    rw [hp, (projector_hermitian 4).eq, projector_idempotent]
  · change (systemProduct [3,4] (1,0,()))ᴴ * systemProduct [3,4] (1,0,()) = escape
    simp only [systemProduct, Matrix.one_mul, outcomeOperator, ite_true,
      show (1 : Fin 2) ≠ 0 by decide, ite_false]
    change (projector 4 * complement)ᴴ * (projector 4 * complement) = escape
    rw [Matrix.conjTranspose_mul, (projector_hermitian 4).eq,
      show complementᴴ = complement from
        (Matrix.isHermitian_one.sub (projector_hermitian 3)).eq]
    change (complement * projector 4) * (projector 4 * complement) = _
    rw [show (complement * projector 4) * (projector 4 * complement) =
      complement * (projector 4 * projector 4) * complement by simp only [Matrix.mul_assoc],
      projector_idempotent]
    rfl

theorem suffix_trace (i : Index) (X : Mat) :
    (systemRun (suffixWord i) (suffixHistory i) X).trace = (effect i * X).trace := by
  rw [systemRun_product, Matrix.trace_mul_cycle, suffix_effect]

theorem commonCut_suffix (i : Index) (X : Mat) :
    commonCut.suffixFunctional i (joint X) = (effect i * X).trace := by
  change (run Q Unit 2 (wordTree Unit (suffixWord i)) (suffixHistory i) (joint X)).trace = _
  rw [actual_run_joint, joint_trace, suffix_trace]

/-- Derived from the actual appended experiment at the common two-command cut. -/
theorem commonCut_probability (i j : Index) :
    (commonCut.probability i j : ℂ) = (effect i * effect j).trace / 3 := by
  rw [commonCut.complex_probability, commonCut_prefix, commonCut_suffix,
    Matrix.mul_smul, Matrix.trace_smul]
  simp [smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- Forty-eight times the actual joint probability table. -/
def integerKernel : Matrix Index Index ℝ :=
  !![16,0,0,8,8,2; 0,16,0,8,0,2; 0,0,16,0,8,8;
    8,8,0,16,4,0; 8,0,8,4,16,9; 2,2,8,0,9,9]

theorem commonCut_table : (48 : ℝ) • commonCut.probability = integerKernel := by
  ext i j
  have h := congrArg Complex.re (commonCut_probability i j)
  simp only [Complex.ofReal_re] at h
  rw [Matrix.smul_apply, h]
  fin_cases i <;> fin_cases j <;>
    norm_num [effect, projector, escape_matrix, integerKernel, Matrix.mul_apply,
      Matrix.trace, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, vec6_last, smul_eq_mul, map_ofNat]

theorem commonCut_table_eq : commonCut.probability = (1/48 : ℝ) • integerKernel := by
  rw [← commonCut_table, smul_smul]
  norm_num

private theorem integerKernel_minor0 : (integerKernel.submatrix Fin.succ (0 : Index).succAbove).det = 65536 := by
  simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  norm_num [integerKernel, Matrix.submatrix, Fin.succAbove, Fin.succ, Fin.castSucc,
    Fin.castAdd, Fin.castLE, Fin.lt_def, Fin.le_def, Fin.reduceFinMk,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec6_last]

private theorem integerKernel_minor3 : (integerKernel.submatrix Fin.succ (3 : Index).succAbove).det = 32768 := by
  simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  norm_num [integerKernel, Matrix.submatrix, Fin.succAbove, Fin.succ, Fin.castSucc,
    Fin.castAdd, Fin.castLE, Fin.lt_def, Fin.le_def, Fin.reduceFinMk,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec6_last]

private theorem integerKernel_minor4 : (integerKernel.submatrix Fin.succ (4 : Index).succAbove).det = -32768 := by
  simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  norm_num [integerKernel, Matrix.submatrix, Fin.succAbove, Fin.succ, Fin.castSucc,
    Fin.castAdd, Fin.castLE, Fin.lt_def, Fin.le_def, Fin.reduceFinMk,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec6_last]

private theorem integerKernel_minor5 : (integerKernel.submatrix Fin.succ (5 : Index).succAbove).det = 0 := by
  simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  norm_num [integerKernel, Matrix.submatrix, Fin.succAbove, Fin.succ, Fin.castSucc,
    Fin.castAdd, Fin.castLE, Fin.lt_def, Fin.le_def, Fin.reduceFinMk,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec6_last]

theorem integerKernel_det : integerKernel.det = 524288 := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ]
  erw [integerKernel_minor0, integerKernel_minor3, integerKernel_minor4, integerKernel_minor5]
  norm_num [integerKernel, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, vec6_last]

theorem commonCut_det : commonCut.probability.det = 1/23328 := by
  rw [commonCut_table_eq, Matrix.det_smul, integerKernel_det]
  norm_num

theorem commonCut_rank_complex : (commonCut.probability.map Complex.ofReal).rank = 6 := by
  have hd : (commonCut.probability.map Complex.ofReal).det = 1/23328 := by
    change (Complex.ofRealHom.mapMatrix commonCut.probability).det = _
    rw [← Complex.ofRealHom.map_det, commonCut_det]
    norm_num
  have hu : IsUnit (commonCut.probability.map Complex.ofReal) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (by rw [hd]; norm_num))
  simpa using Matrix.rank_of_isUnit _ hu

theorem experiment_all_outcomes (i j : Index) :
    (∀ h, 0 ≤ weight Q Unit 2
      (appendTree (wordTree Unit (prefixWord j)) (fun _ => wordTree Unit (suffixWord i)))
      h (joint rho)) ∧
    (∑ h, weight Q Unit 2
      (appendTree (wordTree Unit (prefixWord j)) (fun _ => wordTree Unit (suffixWord i)))
      h (joint rho)) = 1 :=
  normalized_weights Q Unit 2 _ commonCut.density

theorem experiment_history_card (i j : Index) :
    Fintype.card (History 2 ((prefixWord j).length + (suffixWord i).length)) = 16 := by
  rw [prefix_length, suffix_length, history_card]
  norm_num

end SKEFTHawking.QuantumNetwork.FiniteQutritInvariantCarrier
