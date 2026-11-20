import SKEFTHawking.QuantumNetwork.FiniteQutritInvariantReconstruction

/-!
# Physical resources, spectator quantifiers and invariant-carrier controls

Physical dimension three, the selected old feature dimension five and the least
reachable operator dimension six concern different carriers. Amplified Kraus
positivity applies to every positive correlated input. The matrix-level
restriction applies only to inputs in its explicitly inherited carrier.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteQutritInvariantExamples
open Matrix FiniteInterventionProcess FiniteAdaptiveKrausRealization
open FiniteQutritPhysicalMemory FiniteQutritInvariantCarrier
open FiniteQutritInvariantReconstruction FinitePhysicalMemoryDimension
open scoped BigOperators ComplexOrder Kronecker InnerProductSpace

private theorem vec6_last {α : Type*} (a b c d e f : α) :
    ![a,b,c,d,e,f] (5 : Fin 6) = f := rfl

def coordinateMatrix : Matrix Index Index ℂ := fun r j => coordinates (effect j) r

theorem coordinate_matrix : coordinateMatrix =
    !![1,0,0,1/2,1/2,1/8; 0,1,0,1/2,0,1/8; 0,0,1,0,1/2,1/2;
      0,0,0,1/2,0,-1/8; 0,0,0,0,1/2,1/4; 0,0,0,0,0,-1/4] := by
  ext r j
  fin_cases r <;> fin_cases j <;>
    norm_num [coordinateMatrix, coordinates, effect, projector, escape_matrix,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec6_last]

theorem coordinate_det : coordinateMatrix.det = -1/16 := by
  have hu : coordinateMatrix.BlockTriangular id := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      norm_num [coordinate_matrix, id_eq, Fin.lt_def,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec6_last] at *
  rw [Matrix.det_of_upperTriangular hu, coordinate_matrix]
  norm_num [Fin.prod_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, vec6_last]

theorem old_principal_minor (i j : Setting) :
    commonCut.probability i.castSucc j.castSucc = selected i j := by
  have h := commonCut_probability i.castSucc j.castSucc
  rw [effect_old, effect_old] at h
  have hr := congrArg Complex.re h
  rw [selected_trace]
  simpa using hr

theorem old_principal_det :
    (commonCut.probability.submatrix Fin.castSucc Fin.castSucc).det = 1/972 := by
  have he : commonCut.probability.submatrix Fin.castSucc Fin.castSucc = selected := by
    ext i j; exact old_principal_minor i j
  rw [he, selected_det]

theorem sixth_joint_not_prefix : commonCut.probability 5 5 = 3/16 ∧
    weight Q Unit 2 (wordTree Unit [4,3]) (0,1,()) (joint rho) = 1/4 := by
  constructor
  · rw [commonCut_table_eq]
    change (1/48 : ℝ) * 9 = 3/16
    norm_num
  · exact escape_prefix_mass

theorem original_complement_escapes :
    ¬ ∀ X ∈ Submodule.span ℂ (Set.range projector),
      systemBranch 3 1 X ∈ Submodule.span ℂ (Set.range projector) := by
  intro h
  have hm : (1/3 : ℂ) • projector 4 ∈ Submodule.span ℂ (Set.range projector) :=
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨4,rfl⟩)
  have he := h _ hm
  have hb : systemBranch 3 1 ((1/3 : ℂ) • projector 4) = (1/3 : ℂ) • escape := by
    change (1-projector 3) * ((1/3 : ℂ) • projector 4) * (1-projector 3) = _
    rw [Matrix.mul_smul, Matrix.smul_mul]
    rfl
  rw [hb] at he
  exact actual_branch_escapes_old_span he

theorem outcome_positive (j : Setting) (a : Fin 2) : (outcomeOperator j a).PosSemidef := by
  simpa only [outcomeOperator_hermitian, outcomeOperator_idempotent] using
    Matrix.posSemidef_conjTranspose_mul_self (outcomeOperator j a)

theorem escape_effect : escape.PosSemidef ∧ (1 - escape).PosSemidef := by
  have hc : complementᴴ = complement :=
    (Matrix.isHermitian_one.sub (projector_hermitian 3)).eq
  have hb : complement * complement = complement := outcomeOperator_idempotent 3 1
  have hp := (outcome_positive 4 1).mul_mul_conjTranspose_same complement
  rw [hc] at hp
  have he : (1 : Mat) - escape = projector 3 + complement * (1-projector 4) * complement := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hb]
    unfold escape complement
    abel
  exact ⟨escape_positive, he ▸ (outcome_positive 3 0).add hp⟩

theorem escape_not_projector : escape * escape ≠ escape := by
  intro h
  rw [escape_square] at h
  have he := congrArg (fun X : Mat => X 0 0) h
  norm_num [escape_matrix, Matrix.smul_apply] at he

theorem escape_not_density : ¬ IsDensityOperator escape := by
  intro h
  have he := h.2
  rw [escape_trace] at he
  norm_num at he

/-- All suffix-accessible quantum systems, records, seeds and controllers
belong to the complete carrier `S × E` in this quantified competitor. -/
theorem complete_carrier_bound {S E : Type*} [Fintype S] [DecidableEq S]
    [Fintype E] [DecidableEq E] {o : ℕ} (C : CommonCut S E Index Index o)
    (hC : C.probability = commonCut.probability) :
    6 ≤ (Fintype.card (S × E)) ^ 2 := by
  have hd := C.dimension_bound_of_det_ne_zero (by rw [hC, commonCut_det]; norm_num)
  simpa using hd

theorem physical_lower_bound {S E : Type*} [Fintype S] [DecidableEq S]
    [Fintype E] [DecidableEq E] {o : ℕ} (C : CommonCut S E Index Index o)
    (hC : C.probability = commonCut.probability) : 3 ≤ Fintype.card (S × E) := by
  have hd := complete_carrier_bound C hC
  by_contra hn
  have hl : Fintype.card (S × E) ≤ 2 := by omega
  interval_cases hc : Fintype.card (S × E) <;> norm_num [hc] at hd

theorem exact_physical_minimum :
    IsLeast {d : ℕ | ∃ C : CommonCut (Fin d) Unit Index Index 2,
      C.probability = commonCut.probability} 3 := by
  constructor
  · exact ⟨commonCut,rfl⟩
  · rintro d ⟨C,hC⟩
    simpa using physical_lower_bound C hC

theorem three_five_six :
    Fintype.card (Q × Unit) = 3 ∧
    Module.finrank ℂ FiniteQutritPhysicalMemoryExamples.FeatureSpace = 5 ∧
    Module.finrank ℂ FeatureSpace = 6 ∧ Module.finrank ℂ symmetricCarrier = 6 := by
  exact ⟨by decide, FiniteQutritPhysicalMemoryExamples.feature_dimension,
    feature_dimension, symmetric_dimension⟩

variable (E : Type*) [Fintype E] [DecidableEq E]

/-- A system block for fixed spectator row and column, complex-linear on all inputs. -/
def block (e f : E) : Matrix (Q × E) (Q × E) ℂ →ₗ[ℂ] Mat where
  toFun X := fun a b => X (a,e) (b,f)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def matrixCarrier : Submodule ℂ (Matrix (Q × E) (Q × E) ℂ) where
  carrier := {X | ∀ e f, block E e f X ∈ symmetricCarrier}
  zero_mem' := by intro e f; simp
  add_mem' := by intro _ _ hX hY e f; simpa using (hX e f).add (hY e f)
  smul_mem' := by intro _ _ hX e f; simpa using (hX e f).smul _

def matrixCone : Set (Matrix (Q × E) (Q × E) ℂ) :=
  {X | X ∈ matrixCarrier E ∧ X.PosSemidef}

theorem amplified_sandwich_block (A : Mat) (X : Matrix (Q × E) (Q × E) ℂ)
    (e f : E) :
    block E e f ((A ⊗ₖ (1 : Matrix E E ℂ)) * X *
      (A ⊗ₖ (1 : Matrix E E ℂ))ᴴ) = A * block E e f X * Aᴴ := by
  ext i j
  simp [block, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.conjTranspose_kronecker, Matrix.one_apply]

theorem amplified_kraus_block {k : ℕ} (K : Fin k → Mat)
    (X : Matrix (Q × E) (Q × E) ℂ) (e f : E) :
    block E e f (krausMap (fun k => K k ⊗ₖ (1 : Matrix E E ℂ)) X) =
      krausMap K (block E e f X) := by
  simp only [krausMap, map_sum, amplified_sandwich_block]

theorem lifted_branch_block (I : FiniteInstrument Q 2) (a : Fin 2)
    (X : Matrix (Q × E) (Q × E) ℂ) (e f : E) :
    block E e f ((I.lift E).branch a X) = I.branch a (block E e f X) :=
  amplified_kraus_block E (I.operators a) X e f

theorem original_step_matrix_invariant (j : Setting) (a : Fin 2)
    {X : Matrix (Q × E) (Q × E) ℂ} (hX : X ∈ matrixCarrier E) :
    (localStep Q E 2 (readout j)).branch Q E 2 a X ∈ matrixCarrier E := by
  intro e f
  rw [local_branch]
  change block E e f ((outcomeOperator j a ⊗ₖ (1 : Matrix E E ℂ)) * X *
    (outcomeOperator j a ⊗ₖ (1 : Matrix E E ℂ))ᴴ) ∈ symmetricCarrier
  rw [amplified_sandwich_block, outcomeOperator_hermitian]
  exact branch_invariant j a (hX e f)

theorem original_word_matrix_invariant (w : List Setting) (h : History 2 w.length)
    {X : Matrix (Q × E) (Q × E) ℂ} (hX : X ∈ matrixCarrier E) :
    run Q E 2 (wordTree E w) h X ∈ matrixCarrier E := by
  induction w generalizing X with
  | nil => exact hX
  | cons j w ih => exact ih h.2 (original_step_matrix_invariant E j h.1 hX)

/-- Ambient CP positivity holds without a carrier or product-input premise. -/
theorem original_correlated_positive (w : List Setting) (h : History 2 w.length)
    {X : Matrix (Q × E) (Q × E) ℂ} (hX : X.PosSemidef) :
    (run Q E 2 (wordTree E w) h X).PosSemidef := word_positive E w h hX

theorem original_matrix_cone (w : List Setting) (h : History 2 w.length)
    {X : Matrix (Q × E) (Q × E) ℂ} (hX : X ∈ matrixCone E) :
    run Q E 2 (wordTree E w) h X ∈ matrixCone E :=
  ⟨original_word_matrix_invariant E w h hX.1, original_correlated_positive E w h hX.2⟩

def amplifiedNoisyStep (N : Noise) (j : Setting) : Step Q E 2 where
  count := 10
  evolution k := FiniteQutritPhysicalMemoryExamples.depolarizingKraus N.e k ⊗ₖ
    (1 : Matrix E E ℂ)
  normalized := by
    unfold IsKrausChannel
    simp_rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul, sum_kronOne_general]
    rw [FiniteQutritPhysicalMemoryExamples.depolarizingKraus_normalized
      N.e_nonneg N.e_le_one, Matrix.one_kronecker_one]
  instrument := FiniteQutritPhysicalMemoryExamples.noisyReadout j N.t N.t_nonneg N.t_le_one

theorem amplified_noisy_block (N : Noise) (j : Setting) (a : Fin 2)
    (X : Matrix (Q × E) (Q × E) ℂ) (e f : E) :
    block E e f ((amplifiedNoisyStep E N j).branch Q E 2 a X) =
      noisySystemBranch N j a (block E e f X) := by
  change block E e f (((FiniteQutritPhysicalMemoryExamples.noisyReadout j N.t
    N.t_nonneg N.t_le_one).lift E).branch a
      (krausMap (fun k => FiniteQutritPhysicalMemoryExamples.depolarizingKraus N.e k ⊗ₖ
        (1 : Matrix E E ℂ)) X)) = _
  rw [lifted_branch_block, amplified_kraus_block,
    FiniteQutritPhysicalMemoryExamples.depolarizingKraus_action N.e_nonneg N.e_le_one,
    FiniteQutritPhysicalMemoryExamples.noisyReadout_branch, original_readout_branch]
  rfl

theorem noisy_step_matrix_invariant (N : Noise) (j : Setting) (a : Fin 2)
    {X : Matrix (Q × E) (Q × E) ℂ} (hX : X ∈ matrixCarrier E) :
    (amplifiedNoisyStep E N j).branch Q E 2 a X ∈ matrixCarrier E := by
  intro e f
  rw [amplified_noisy_block]
  exact noisy_invariant N j a (hX e f)

def amplifiedNoisyTree (N : Noise) : (w : List Setting) → Tree Q E 2 w.length
  | [] => .done
  | j :: w => .node (amplifiedNoisyStep E N j) (fun _ => amplifiedNoisyTree N w)

theorem noisy_word_matrix_invariant (N : Noise) (w : List Setting) (h : History 2 w.length)
    {X : Matrix (Q × E) (Q × E) ℂ} (hX : X ∈ matrixCarrier E) :
    run Q E 2 (amplifiedNoisyTree E N w) h X ∈ matrixCarrier E := by
  induction w generalizing X with
  | nil => exact hX
  | cons j w ih => exact ih h.2 (noisy_step_matrix_invariant E N j h.1 hX)

theorem noisy_correlated_positive (N : Noise) (w : List Setting) (h : History 2 w.length)
    {X : Matrix (Q × E) (Q × E) ℂ} (hX : X.PosSemidef) :
    (run Q E 2 (amplifiedNoisyTree E N w) h X).PosSemidef :=
  run_posSemidef Q E 2 _ _ hX

theorem noisy_matrix_cone (N : Noise) (w : List Setting) (h : History 2 w.length)
    {X : Matrix (Q × E) (Q × E) ℂ} (hX : X ∈ matrixCone E) :
    run Q E 2 (amplifiedNoisyTree E N w) h X ∈ matrixCone E :=
  ⟨noisy_word_matrix_invariant E N w h hX.1, noisy_correlated_positive E N w h hX.2⟩

theorem amplified_noisy_normalized (N : Noise) (w : List Setting)
    {X : Matrix (Q × E) (Q × E) ℂ} (hX : IsDensityOperator X) :
    (∀ h, 0 ≤ weight Q E 2 (amplifiedNoisyTree E N w) h X) ∧
      (∑ h, weight Q E 2 (amplifiedNoisyTree E N w) h X) = 1 :=
  FiniteInterventionProcess.normalized_weights Q E 2 _ hX

theorem spectator_word_probability (w : List Setting) (h : History 2 w.length)
    {σ : Matrix E E ℂ} (hσ : σ.trace = 1) :
    weight Q E 2 (wordTree E w) h (rho ⊗ₖ σ) =
      weight Q Unit 2 (wordTree Unit w) h (joint rho) := by
  rw [word_product_weight E _ _ _ hσ, joint,
    word_product_weight Unit _ _ _ (by simp [Matrix.trace])]


theorem amplified_channel_product {k : ℕ} (K : Fin k → Mat) (X : Mat)
    (σ : Matrix E E ℂ) :
    krausMap (fun k => K k ⊗ₖ (1 : Matrix E E ℂ)) (X ⊗ₖ σ) = krausMap K X ⊗ₖ σ := by
  simp only [krausMap, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  ext ⟨i,e⟩ ⟨j,f⟩
  simp only [Matrix.sum_apply, Matrix.kronecker_apply, Finset.sum_mul]

theorem amplified_noisy_product (N : Noise) (j : Setting) (a : Fin 2)
    (X : Mat) (σ : Matrix E E ℂ) :
    (amplifiedNoisyStep E N j).branch Q E 2 a (X ⊗ₖ σ) =
      noisySystemBranch N j a X ⊗ₖ σ := by
  change ((FiniteQutritPhysicalMemoryExamples.noisyReadout j N.t
    N.t_nonneg N.t_le_one).lift E).branch a
      (krausMap (fun k => FiniteQutritPhysicalMemoryExamples.depolarizingKraus N.e k ⊗ₖ
        (1 : Matrix E E ℂ)) (X ⊗ₖ σ)) = _
  rw [amplified_channel_product, FiniteAdaptiveMapPerturbation.lift_branch_tensor,
    FiniteQutritPhysicalMemoryExamples.depolarizingKraus_action N.e_nonneg N.e_le_one,
    FiniteQutritPhysicalMemoryExamples.noisyReadout_branch, original_readout_branch]
  rfl

theorem amplified_noisy_word_product (N : Noise) (w : List Setting) (h : History 2 w.length)
    (q : FeatureSpace) (σ : Matrix E E ℂ) :
    run Q E 2 (amplifiedNoisyTree E N w) h ((U q : Mat) ⊗ₖ σ) =
      (U (noisyWord N w h q) : Mat) ⊗ₖ σ := by
  induction w generalizing q with
  | nil => rfl
  | cons j w ih =>
    change run Q E 2 (amplifiedNoisyTree E N w) h.2
      ((amplifiedNoisyStep E N j).branch Q E 2 h.1 ((U q : Mat) ⊗ₖ σ)) = _
    rw [amplified_noisy_product, ← U_noisyBranch, ih]
    rfl

theorem spectator_noisy_probability (N : Noise) (w : List Setting) (h : History 2 w.length)
    (q : FeatureSpace) {σ : Matrix E E ℂ} (hσ : σ.trace = 1) :
    weight Q E 2 (amplifiedNoisyTree E N w) h ((U q : Mat) ⊗ₖ σ) =
      (FiniteQutritInvariantReconstruction.trace (noisyWord N w h q)).re := by
  unfold FiniteInterventionProcess.weight
  rw [amplified_noisy_word_product, Matrix.trace_kronecker, hσ, mul_one]
  rfl

theorem spectator_noisy_initial_probability (N : Noise) (w : List Setting)
    (h : History 2 w.length) {σ : Matrix E E ℂ} (hσ : σ.trace = 1) :
    weight Q E 2 (amplifiedNoisyTree E N w) h (rho ⊗ₖ σ) =
      weight Q Unit 2 (FiniteQutritInvariantReconstruction.noisyTree N w) h (joint rho) := by
  rw [← U_initial, spectator_noisy_probability E N w h initial hσ]
  unfold FiniteInterventionProcess.weight
  rw [actual_noisyWord, joint_trace]
  rfl

theorem amplified_noisy_prefix_marginal (N : Noise) (u v : List Setting)
    (h : History 2 u.length) (X : Matrix (Q × E) (Q × E) ℂ) :
    (∑ g, weight Q E 2 (amplifiedNoisyTree E N v) g
      (run Q E 2 (amplifiedNoisyTree E N u) h X)) =
      weight Q E 2 (amplifiedNoisyTree E N u) h X :=
  FiniteInterventionProcess.prefix_marginal Q E 2 _ _ _ _

theorem amplified_noisy_append (N : Noise) (u v : List Setting)
    (h : History 2 u.length) (g : History 2 v.length)
    (X : Matrix (Q × E) (Q × E) ℂ) :
    run Q E 2 (appendTree (amplifiedNoisyTree E N u)
      (fun _ => amplifiedNoisyTree E N v)) (appendHistory h g) X =
      run Q E 2 (amplifiedNoisyTree E N v) g
        (run Q E 2 (amplifiedNoisyTree E N u) h X) := append_run _ _ _ _ _


theorem original_spectator_append_probability (u v : List Setting)
    (h : History 2 u.length) (g : History 2 v.length)
    {σ : Matrix E E ℂ} (hσ : σ.trace = 1) :
    weight Q E 2 (appendTree (wordTree E u) (fun _ => wordTree E v))
      (appendHistory h g) (rho ⊗ₖ σ) =
    weight Q Unit 2 (appendTree (wordTree Unit u) (fun _ => wordTree Unit v))
      (appendHistory h g) (joint rho) := by
  unfold FiniteInterventionProcess.weight
  rw [← FiniteQutritPhysicalMemoryExamples.word_append_coherence,
    ← FiniteQutritPhysicalMemoryExamples.word_append_coherence]
  exact spectator_word_probability E (u ++ v)
    (FiniteQutritPhysicalMemoryExamples.wordAppendHistory u v h g) hσ

omit [Fintype E] [DecidableEq E] in
/-- A readable classical record is part of the complete retained dimension. -/
theorem retained_records {C R : Type*} [Fintype C] [Fintype R] :
    Fintype.card (C × R) = Fintype.card C * Fintype.card R := Fintype.card_prod _ _

omit [Fintype E] [DecidableEq E] in
theorem retained_blocks {C : Type*} [Fintype C] (R : C → Type*) [∀ c, Fintype (R c)] :
    Fintype.card (Sigma R) = ∑ c, Fintype.card (R c) := Fintype.card_sigma

end SKEFTHawking.QuantumNetwork.FiniteQutritInvariantExamples

namespace SKEFTHawking.QuantumNetwork.FiniteQutritInvariantExamples
open Matrix FiniteInterventionProcess FiniteAdaptiveKrausRealization
open FiniteQutritPhysicalMemory FiniteQutritInvariantCarrier
open FiniteQutritInvariantReconstruction
open scoped BigOperators ComplexOrder Kronecker InnerProductSpace

theorem initial_density : initial ∈ density := by
  constructor
  · change (U initial : Mat).PosSemidef
    rw [U_initial]
    exact rho_density.1
  · change (U initial : Mat).trace = 1
    rw [U_initial]
    exact rho_density.2

theorem escape_state_entry : ((1/3 : ℂ) • escape) 1 2 = -1/12 := by
  norm_num [escape_matrix, Matrix.smul_apply, Matrix.cons_val_two]

theorem prefix_states_span :
    Submodule.span ℂ (Set.range (fun i : Index => (1/3 : ℂ) • effect i)) = symmetricCarrier := by
  apply le_antisymm
  · exact Submodule.span_le.mpr (by rintro X ⟨i,rfl⟩; exact (effect_symmetric i).smul _)
  · rw [← effect_span]
    apply Submodule.span_le.mpr
    rintro X ⟨i,rfl⟩
    have h := Submodule.smul_mem (Submodule.span ℂ
      (Set.range (fun i : Index => (1/3 : ℂ) • effect i))) (3 : ℂ)
      (Submodule.subset_span (Set.mem_range_self i))
    have he : (3 : ℂ) • ((1/3 : ℂ) • effect i) = effect i := by rw [smul_smul]; norm_num
    rw [he] at h
    exact h

theorem reconstructed_empty (q : FeatureSpace) : word [] () q = q := rfl

theorem reconstructed_word_add (w : List Setting) (h : History 2 w.length)
    (q r : FeatureSpace) : word w h (q+r) = word w h q + word w h r := by
  induction w generalizing q r with
  | nil => rfl
  | cons j w ih =>
    change word w h.2 (branch j h.1 (q+r)) = _
    rw [map_add, ih]
    rfl

theorem reconstructed_word_smul (w : List Setting) (h : History 2 w.length)
    (c : ℂ) (q : FeatureSpace) : word w h (c • q) = c • word w h q := by
  induction w generalizing q with
  | nil => rfl
  | cons j w ih =>
    change word w h.2 (branch j h.1 (c • q)) = _
    rw [map_smul, ih]
    rfl

def reconstructedWordLinear (w : List Setting) (h : History 2 w.length) :
    FeatureSpace →ₗ[ℂ] FeatureSpace where
  toFun := word w h
  map_add' := reconstructed_word_add w h
  map_smul' := reconstructed_word_smul w h

theorem reconstructed_word_cone (w : List Setting) (h : History 2 w.length)
    {q : FeatureSpace} (hq : q ∈ cone) : word w h q ∈ cone := by
  induction w generalizing q with
  | nil => exact hq
  | cons j w ih => exact ih h.2 (branch_cone j h.1 hq)

theorem reconstructed_noisy_word_cone (N : Noise) (w : List Setting)
    (h : History 2 w.length) {q : FeatureSpace} (hq : q ∈ cone) :
    noisyWord N w h q ∈ cone := by
  induction w generalizing q with
  | nil => exact hq
  | cons j w ih => exact ih h.2 (noisyBranch_cone N j h.1 hq)

end SKEFTHawking.QuantumNetwork.FiniteQutritInvariantExamples
