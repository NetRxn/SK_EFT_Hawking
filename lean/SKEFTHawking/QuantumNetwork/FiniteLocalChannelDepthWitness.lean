import SKEFTHawking.QuantumNetwork.FiniteLocalChannelDepthObstruction
import Mathlib.LinearAlgebra.Matrix.Permutation

/-! Exact finite local depth attainment and assumption-removal channels. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace SKEFTHawking.QuantumNetwork.FiniteLocalChannelDepthWitness
open FiniteLocalChannelLayer FiniteLocalChannelDepthObstruction

section Permutation
variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Forward permutation orientation: the column y is sent to row g y. -/
def forward (g : A ≃ A) : Matrix A A ℂ := fun x y => if x = g y then 1 else 0

omit [Fintype A] in
theorem forward_eq_permMatrix (g : A ≃ A) :
    forward g = Equiv.Perm.permMatrix ℂ g.symm := by
  ext x y
  simp [forward, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv,
    g.eq_symm_apply, eq_comm]

theorem forward_mul (g : A ≃ A) (X : Matrix A A ℂ) (x y : A) :
    (forward g * X) x y = X (g.symm x) y := by
  simp [Matrix.mul_apply, forward, ← g.symm_apply_eq, ite_mul]

theorem mul_forward_adjoint (g : A ≃ A) (X : Matrix A A ℂ) (x y : A) :
    (X * (forward g).conjTranspose) x y = X x (g.symm y) := by
  simp [Matrix.mul_apply, forward, Matrix.conjTranspose_apply,
    ← g.symm_apply_eq, mul_ite]

theorem forward_conjugation (g : A ≃ A) (X : Matrix A A ℂ) :
    forward g * X * (forward g).conjTranspose = pull g.symm X := by
  ext x y
  rw [mul_forward_adjoint, forward_mul]
  rfl

omit [Fintype A] in
theorem forward_adjoint (g : A ≃ A) : (forward g).conjTranspose = forward g.symm := by
  ext x y
  simp [forward, Matrix.conjTranspose_apply, g.eq_symm_apply, eq_comm]

theorem forward_unitary (g : A ≃ A) :
    (forward g).conjTranspose * forward g = 1 := by
  rw [forward_adjoint]
  ext x y
  rw [forward_mul]
  simp [forward, Matrix.one_apply, g.injective.eq_iff]

theorem forward_projector (g : A ≃ A) (s : A) :
    forward g * Matrix.single s s 1 * (forward g).conjTranspose =
      Matrix.single (g s) (g s) 1 := by
  rw [forward_conjugation]
  ext x y
  simp [pull, Matrix.single_apply, g.eq_symm_apply]

theorem forward_normalized (g : A ≃ A) :
    IsKrausChannel (fun _ : Fin 1 => forward g) := by
  simpa [IsKrausChannel] using forward_unitary g

end Permutation

/-- Only the named target changes, by xor with the named control.
The local channel requires unitarity; no special-unitary membership is asserted. -/
def cnotMap {W : Type*} [DecidableEq W] (control target : W) (x : W → Bool) : W → Bool :=
  Function.update x target (xor (x target) (x control))

theorem cnotMap_involutive {W : Type*} [DecidableEq W]
    (control target : W) (h : control ≠ target) :
    Function.Involutive (cnotMap control target) := by
  intro x
  funext w
  by_cases hw : w = target
  · subst w
    simp [cnotMap, h]
  · simp [cnotMap, hw]

def cnot {W : Type*} [DecidableEq W] (control target : W) (h : control ≠ target) :
    (W → Bool) ≃ (W → Bool) :=
  (cnotMap_involutive control target h).toPerm (cnotMap control target)

theorem cnot_control {W : Type*} [DecidableEq W]
    (c t : W) (h : c ≠ t) (x : W → Bool) : cnot c t h x c = x c := by
  simp [cnot, cnotMap, h]

theorem cnot_target {W : Type*} [DecidableEq W]
    (c t : W) (h : c ≠ t) (x : W → Bool) :
    cnot c t h x t = xor (x t) (x c) := by
  simp [cnot, cnotMap]

/-- The independent layer formed from one local permutation on each block. -/
def permutationLayer (P : Partition) (g : ∀ j, P.LocalBasis j ≃ P.LocalBasis j) : Layer where
  partition := P
  count := fun _ => 1
  operator := fun j _ => forward (g j)
  normalized := fun j => forward_normalized (g j)

def physicalPermutation (P : Partition) (g : ∀ j, P.LocalBasis j ≃ P.LocalBasis j) :
    Basis ≃ Basis := P.split.trans ((Equiv.piCongrRight g).trans P.split.symm)

theorem physicalPermutation_split (P : Partition)
    (g : ∀ j, P.LocalBasis j ≃ P.LocalBasis j) (y : Basis) (j : Fin P.blocks) :
    P.split (physicalPermutation P g y) j = g j (P.split y j) := by
  simp [physicalPermutation]

theorem permutationLayer_physical (P : Partition)
    (g : ∀ j, P.LocalBasis j ≃ P.LocalBasis j)
    (a : (permutationLayer P g).Selector) :
    (permutationLayer P g).physicalKraus a = forward (physicalPermutation P g) := by
  ext x y
  change (∏ j, if P.split x j = g j (P.split y j) then (1 : ℂ) else 0) =
    if x = physicalPermutation P g y then 1 else 0
  by_cases h : x = physicalPermutation P g y
  · subst x
    simp [physicalPermutation_split]
  · rw [if_neg h]
    have hn : ∃ j, P.split x j ≠ g j (P.split y j) := by
      by_contra hn
      apply h
      apply P.split.injective
      funext j
      rw [physicalPermutation_split]
      simpa using not_exists.mp hn j
    obtain ⟨j, hj⟩ := hn
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

theorem permutationLayer_action (P : Partition)
    (g : ∀ j, P.LocalBasis j ≃ P.LocalBasis j) (X : PhysicalMatrix) :
    (permutationLayer P g).action X =
      forward (physicalPermutation P g) * X * (forward (physicalPermutation P g)).conjTranspose := by
  rw [Layer.action_eq_sum]
  simp_rw [permutationLayer_physical]
  have hc : Fintype.card (permutationLayer P g).Selector = 1 := by
    simp [Layer.Selector, permutationLayer]
  simp [hc]

theorem permutationLayer_projector (P : Partition)
    (g : ∀ j, P.LocalBasis j ≃ P.LocalBasis j) (s : Basis) :
    (permutationLayer P g).action (basisProjector s) =
      basisProjector (physicalPermutation P g s) := by
  rw [permutationLayer_action]
  exact forward_projector _ s

abbrev firstPartition : Partition where
  blocks := 3
  blockOf := ![0, 0, 1, 2]
  onto := by decide
  small := by decide

abbrev secondPartition : Partition where
  blocks := 2
  blockOf := ![0, 1, 0, 1]
  onto := by decide
  small := by decide

theorem firstPartition_cards :
    (fun j => Fintype.card (firstPartition.Fiber j)) = ![2, 1, 1] := by decide

theorem secondPartition_cards :
    (fun j => Fintype.card (secondPartition.Fiber j)) = ![2, 2] := by decide

def firstLocal (j : Fin firstPartition.blocks) :
    firstPartition.LocalBasis j ≃ firstPartition.LocalBasis j :=
  if h : j = 0 then h.symm ▸ cnot
    (⟨0, rfl⟩ : firstPartition.Fiber 0) ⟨1, rfl⟩ (by decide)
  else Equiv.refl _

def secondControl (j : Fin secondPartition.blocks) : secondPartition.Fiber j :=
  ⟨⟨j.val, by have := j.isLt; change j.val < 2 at this; omega⟩, by fin_cases j <;> rfl⟩

def secondTarget (j : Fin secondPartition.blocks) : secondPartition.Fiber j :=
  ⟨⟨j.val + 2, by have := j.isLt; change j.val < 2 at this; omega⟩, by fin_cases j <;> rfl⟩

def secondLocal (j : Fin secondPartition.blocks) :
    secondPartition.LocalBasis j ≃ secondPartition.LocalBasis j :=
  cnot (secondControl j) (secondTarget j) (by
    intro h
    have hv := congrArg (fun w : secondPartition.Fiber j => w.val.val) h
    simp [secondControl, secondTarget] at hv)

def firstLayer : Layer := permutationLayer firstPartition firstLocal
def secondLayer : Layer := permutationLayer secondPartition secondLocal

theorem first_physical (x : Basis) :
    physicalPermutation firstPartition firstLocal x =
      ![x 0, xor (x 1) (x 0), x 2, x 3] := by
  funext w
  fin_cases w <;>
    simp [physicalPermutation, Partition.split, firstLocal, firstPartition, cnot, cnotMap] <;> rfl

theorem second_physical (x : Basis) :
    physicalPermutation secondPartition secondLocal x =
      ![x 0, x 1, xor (x 2) (x 0), xor (x 3) (x 1)] := by
  funext w
  fin_cases w <;>
    simp [physicalPermutation, Partition.split, secondLocal, secondPartition,
      secondControl, secondTarget, cnot, cnotMap] <;> rfl


def qubitZero : Matrix Bool Bool ℂ := Matrix.single false false 1
def qubitMixed : Matrix Bool Bool ℂ := (1 / 2 : ℂ) • 1

theorem qubitZero_density : IsDensityOperator qubitZero := by
  have he : qubitZero = Matrix.diagonal (fun b : Bool => if b then 0 else 1) := by
    ext x y
    cases x <;> cases y <;> simp [qubitZero, Matrix.diagonal]
  rw [he]
  refine ⟨Matrix.PosSemidef.diagonal (fun b => ?_), ?_⟩
  · cases b <;> simp
  · norm_num [Matrix.trace, Fintype.sum_bool]

theorem qubitMixed_density : IsDensityOperator qubitMixed := by
  have h1 : (1 : Matrix Bool Bool ℂ).PosSemidef := by
    simpa using Matrix.posSemidef_conjTranspose_mul_self (1 : Matrix Bool Bool ℂ)
  refine ⟨h1.smul (by norm_num [Complex.le_def] : (0 : ℂ) ≤ 1 / 2), ?_⟩
  norm_num [qubitMixed, Matrix.trace, Fintype.sum_bool]

/-- The only mixed input is wire zero; the remaining wires are pure zero. -/
def witnessInput : ProductInput where
  localState := fun w => if w = 0 then qubitMixed else qubitZero
  density := fun w => by split <;> first | exact qubitMixed_density | exact qubitZero_density

def seed : Basis := ![true, false, false, false]
def intermediate : Basis := ![true, true, false, false]



theorem bit_mixture_entry (a0 a1 a2 a3 b0 b1 b2 b3 : Bool) :
    (if a3 = false ∧ b3 = false then
      if a2 = false ∧ b2 = false then
        if a1 = false ∧ b1 = false then if a0 = b0 then (2 : ℂ)⁻¹ else 0 else 0 else 0 else 0) =
    (if (a0 = false ∧ a1 = false ∧ a2 = false ∧ a3 = false) ∧
      b0 = false ∧ b1 = false ∧ b2 = false ∧ b3 = false then (2 : ℂ)⁻¹ else 0) +
    (if (a0 = true ∧ a1 = false ∧ a2 = false ∧ a3 = false) ∧
      b0 = true ∧ b1 = false ∧ b2 = false ∧ b3 = false then (2 : ℂ)⁻¹ else 0) := by
  cases a0 <;> cases b0 <;> simp only [Bool.false_eq_true, Bool.true_eq_false,
    and_false, true_and, false_and, ↓reduceIte, add_zero, zero_add]
    <;> split_ifs <;> first | rfl | tauto

theorem witnessInput_matrix :
    witnessInput.state =
      (1 / 2 : ℂ) • basisProjector (fun _ => false) +
      (1 / 2 : ℂ) • basisProjector seed := by
  ext x y
  simp [ProductInput.state, tensor, witnessInput, qubitMixed, qubitZero,
    Fin.prod_univ_succ, basisProjector, Matrix.single_apply, Matrix.one_apply,
    funext_iff, Fin.forall_fin_succ, seed]
  exact bit_mixture_entry (x 0) (x 1) (x 2) (x 3) (y 0) (y 1) (y 2) (y 3)

theorem permutationLayer_mixture (P : Partition)
    (g : ∀ j, P.LocalBasis j ≃ P.LocalBasis j) (s t : Basis) (a b : ℂ) :
    (permutationLayer P g).action (a • basisProjector s + b • basisProjector t) =
      a • basisProjector (physicalPermutation P g s) +
      b • basisProjector (physicalPermutation P g t) := by
  simp only [permutationLayer_action, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, basisProjector, forward_projector]

theorem first_zero :
    physicalPermutation firstPartition firstLocal (fun _ => false) = (fun _ => false) := by
  rw [first_physical]
  funext w
  fin_cases w <;> rfl

theorem first_seed : physicalPermutation firstPartition firstLocal seed = intermediate := by
  rw [first_physical]
  rfl

theorem second_zero :
    physicalPermutation secondPartition secondLocal (fun _ => false) = (fun _ => false) := by
  rw [second_physical]
  funext w
  fin_cases w <;> rfl

theorem second_intermediate :
    physicalPermutation secondPartition secondLocal intermediate = (fun _ => true) := by
  rw [second_physical]
  funext w
  fin_cases w <;> rfl

theorem firstLayer_output :
    firstLayer.action witnessInput.state =
      (1 / 2 : ℂ) • basisProjector (fun _ => false) +
      (1 / 2 : ℂ) • basisProjector intermediate := by
  rw [witnessInput_matrix, firstLayer, permutationLayer_mixture, first_zero, first_seed]

theorem witness_output : run [firstLayer, secondLayer] witnessInput.state = B4 := by
  simp only [run_cons, run_nil]
  rw [firstLayer_output, secondLayer, permutationLayer_mixture, second_zero, second_intermediate]
  rfl

theorem witness_depth : depth [firstLayer, secondLayer] = 2 := rfl

/-- Feasible depths quantify over all admitted inputs and schedules. -/
def feasibleDepths : Set ℕ :=
  {d | ∃ (ρ : ProductInput) (Ls : List Layer), depth Ls = d ∧ run Ls ρ.state = B4}

/-- Exact B4 is attained at depth two, and the universal shallow theorem excludes every smaller depth. -/
theorem minimum_depth_two : IsLeast feasibleDepths 2 := by
  refine ⟨⟨witnessInput, [firstLayer, secondLayer], witness_depth, witness_output⟩, ?_⟩
  intro d hd
  obtain ⟨ρ, Ls, hdepth, hout⟩ := hd
  by_contra hn
  have hs : depth Ls ≤ 1 := by omega
  have hc := shallow_traceDist_gt ρ Ls hs
  rw [hout, traceDist_self] at hc
  norm_num at hc

theorem B4_covariance (u v : Wire) :
    binaryOutcomeProb (pairEffect u v) B4 -
      binaryOutcomeProb (singleEffect u) B4 * binaryOutcomeProb (singleEffect v) B4 = 1 / 4 := by
  rw [B4_pair_probability, B4_single_probability, B4_single_probability]
  norm_num

theorem B4_not_product : ¬ ∃ ρ : ProductInput, ρ.state = B4 := by
  rintro ⟨ρ, hρ⟩
  have hz := product_event_factorization ρ (u := 0) (v := 1) (by decide)
  rw [hρ, B4_pair_probability, B4_single_probability, B4_single_probability] at hz
  norm_num at hz

/-- Correlated initialization is outside ProductInput and needs no layer to retain B4. -/
theorem correlated_empty_guard :
    IsDensityOperator B4 ∧ run [] B4 = B4 ∧ traceDist (run [] B4) B4 = 0 := by
  exact ⟨B4_density, rfl, traceDist_self B4⟩

theorem correlated_identity_guard :
    IsKrausChannel identityKraus ∧ krausMap identityKraus B4 = B4 ∧
      traceDist (krausMap identityKraus B4) B4 = 0 := by
  exact ⟨identityKraus_normalized, identityKraus_action B4,
    by rw [identityKraus_action, traceDist_self]⟩

/-- The unrestricted replacement family has two output bits and every input basis column. -/
abbrev PreparationIndex := Bool × Basis

def preparationScalar : ℂ := (Real.sqrt (1 / 2) : ℝ)

theorem preparationScalar_sq :
    preparationScalar * star preparationScalar = (1 / 2 : ℂ) := by
  simp only [preparationScalar, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
  rw [← pow_two, Real.sq_sqrt (by norm_num)]
  norm_num

def preparationOperator (i : PreparationIndex) : PhysicalMatrix :=
  preparationScalar • Matrix.single (fun _ => i.1) i.2 1

theorem preparationIndex_card : Fintype.card PreparationIndex = 32 := by decide

def preparationEnumeration : Fin 32 ≃ PreparationIndex :=
  (Fintype.equivFinOfCardEq preparationIndex_card).symm

def preparationKraus : Fin 32 → PhysicalMatrix :=
  fun i => preparationOperator (preparationEnumeration i)

section MatrixUnits
variable {A : Type*} [Fintype A] [DecidableEq A]

theorem matrixUnit_sandwich (a s : A) (X : Matrix A A ℂ) :
    Matrix.single a s 1 * X * (Matrix.single a s 1).conjTranspose =
      X s s • Matrix.single a a 1 := by
  ext x y
  by_cases hx : x = a
  · subst x
    by_cases hy : y = a
    · subst y
      simp [Matrix.mul_apply, Matrix.single_apply, ite_mul, mul_ite]
    · simp [Matrix.mul_apply, Matrix.single_apply, Ne.symm hy, ite_mul]
  · simp [Matrix.mul_apply, Matrix.single_apply, Ne.symm hx, mul_ite]

theorem matrixUnit_normalization (a s : A) :
    (Matrix.single a s (1 : ℂ)).conjTranspose * Matrix.single a s 1 =
      Matrix.single s s 1 := by
  ext x y
  by_cases hx : x = s
  · subst x
    by_cases hy : y = s
    · subst y
      simp [Matrix.mul_apply, Matrix.single_apply, mul_ite]
    · simp [Matrix.mul_apply, Matrix.single_apply, Ne.symm hy]
  · simp [Matrix.mul_apply, Matrix.single_apply, Ne.symm hx, mul_ite]

end MatrixUnits

theorem preparationOperator_normalization (i : PreparationIndex) :
    (preparationOperator i).conjTranspose * preparationOperator i =
      (1 / 2 : ℂ) • basisProjector i.2 := by
  simp only [preparationOperator, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, matrixUnit_normalization]
  rw [preparationScalar_sq]
  rfl

theorem preparationOperator_action (i : PreparationIndex) (X : PhysicalMatrix) :
    preparationOperator i * X * (preparationOperator i).conjTranspose =
      ((1 / 2 : ℂ) * X i.2 i.2) • basisProjector (fun _ => i.1) := by
  simp only [preparationOperator, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, matrixUnit_sandwich]
  rw [← mul_assoc, mul_comm (star preparationScalar), preparationScalar_sq]
  rfl

theorem sum_basisProjector : (∑ s : Basis, basisProjector s) = 1 := by
  ext x y
  simp only [Matrix.sum_apply, basisProjector]
  by_cases h : x = y
  · subst y
    simp [Matrix.single_apply]
  · rw [Matrix.one_apply_ne h]
    apply Finset.sum_eq_zero
    intro s _
    have hs : ¬(s = x ∧ s = y) := fun hh => h (hh.1.symm.trans hh.2)
    simp [hs]

theorem preparation_normalized : IsKrausChannel preparationKraus := by
  unfold IsKrausChannel preparationKraus
  rw [preparationEnumeration.sum_comp (fun i => (preparationOperator i).conjTranspose * preparationOperator i)]
  simp_rw [preparationOperator_normalization]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, ← Finset.smul_sum, sum_basisProjector]
  module

/-- The replacement law holds for every complex matrix, with its full complex trace. -/
theorem preparation_action (X : PhysicalMatrix) :
    krausMap preparationKraus X = X.trace • B4 := by
  unfold krausMap preparationKraus
  rw [preparationEnumeration.sum_comp (fun i => preparationOperator i * X * (preparationOperator i).conjTranspose)]
  simp_rw [preparationOperator_action]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, ← Finset.sum_smul, ← Finset.mul_sum]
  unfold B4 Matrix.trace Matrix.diag
  module

theorem preparation_density_action (X : PhysicalMatrix) (hX : IsDensityOperator X) :
    krausMap preparationKraus X = B4 := by
  rw [preparation_action, hX.2, one_smul]

/-- A single general Layer cannot realize this unrestricted channel. -/
theorem preparation_not_layer : ¬ ∃ L : Layer, ∀ X : PhysicalMatrix,
    L.action X = krausMap preparationKraus X := by
  rintro ⟨L, hL⟩
  have hc := layer_traceDist_gt L witnessInput
  rw [hL, preparation_density_action _ witnessInput.state_density, traceDist_self] at hc
  norm_num at hc

/-- Renaming either witness's block labels preserves its physical channel. -/
theorem witness_block_labels
    (e₁ : Fin firstLayer.partition.blocks ≃ Fin firstLayer.partition.blocks)
    (e₂ : Fin secondLayer.partition.blocks ≃ Fin secondLayer.partition.blocks)
    (X : PhysicalMatrix) :
    (firstLayer.relabel e₁).action X = firstLayer.action X ∧
      (secondLayer.relabel e₂).action X = secondLayer.action X :=
  ⟨firstLayer.block_label_invariant e₁ X, secondLayer.block_label_invariant e₂ X⟩

theorem witness_local_enumerations
    (e₁ : ∀ j, Fin (firstLayer.count j) ≃ Fin (firstLayer.count j))
    (e₂ : ∀ j, Fin (secondLayer.count j) ≃ Fin (secondLayer.count j))
    (X : PhysicalMatrix) :
    (firstLayer.reindexLocal e₁).action X = firstLayer.action X ∧
      (secondLayer.reindexLocal e₂).action X = secondLayer.action X :=
  ⟨firstLayer.local_enumeration_invariant e₁ X, secondLayer.local_enumeration_invariant e₂ X⟩

theorem witness_global_enumerations
    (e₁ : Fin (Fintype.card firstLayer.Selector) ≃ firstLayer.Selector)
    (e₂ : Fin (Fintype.card secondLayer.Selector) ≃ secondLayer.Selector)
    (X : PhysicalMatrix) :
    firstLayer.enumeratedAction e₁ X = firstLayer.action X ∧
      secondLayer.enumeratedAction e₂ X = secondLayer.action X :=
  ⟨firstLayer.enumeratedAction_eq e₁ X, secondLayer.enumeratedAction_eq e₂ X⟩

/-- All three allowed representation changes can be combined in the actual witness. -/
theorem witness_representation_output
    (e₁ : Fin firstLayer.partition.blocks ≃ Fin firstLayer.partition.blocks)
    (e₂ : Fin secondLayer.partition.blocks ≃ Fin secondLayer.partition.blocks)
    (f₁ : ∀ j, Fin ((firstLayer.relabel e₁).count j) ≃ Fin ((firstLayer.relabel e₁).count j))
    (f₂ : ∀ j, Fin ((secondLayer.relabel e₂).count j) ≃ Fin ((secondLayer.relabel e₂).count j))
    (g₁ : Fin (Fintype.card ((firstLayer.relabel e₁).reindexLocal f₁).Selector) ≃
      ((firstLayer.relabel e₁).reindexLocal f₁).Selector)
    (g₂ : Fin (Fintype.card ((secondLayer.relabel e₂).reindexLocal f₂).Selector) ≃
      ((secondLayer.relabel e₂).reindexLocal f₂).Selector) :
    ((secondLayer.relabel e₂).reindexLocal f₂).enumeratedAction g₂
      (((firstLayer.relabel e₁).reindexLocal f₁).enumeratedAction g₁ witnessInput.state) = B4 := by
  simp only [Layer.enumeratedAction_eq, Layer.local_enumeration_invariant,
    Layer.block_label_invariant]
  exact witness_output

/-- The canonical gluing is exactly identity on every physical wire of both schedules. -/
theorem witness_physical_wires (x : Basis) (w : Wire) :
    firstLayer.partition.split.symm (firstLayer.partition.split x) w = x w ∧
      secondLayer.partition.split.symm (secondLayer.partition.split x) w = x w :=
  ⟨firstLayer.partition.glue_split_wire x w, secondLayer.partition.glue_split_wire x w⟩

/-- Relabeled local coordinates still refer to the original physical controls and targets. -/
theorem witness_relabel_coordinates
    (e₁ : Fin firstLayer.partition.blocks ≃ Fin firstLayer.partition.blocks)
    (e₂ : Fin secondLayer.partition.blocks ≃ Fin secondLayer.partition.blocks)
    (x : Basis) :
    (∀ j, firstLayer.partition.relabelBasis e₁ j
      ((firstLayer.partition.relabel e₁).split x j) =
        firstLayer.partition.split x (e₁.symm j)) ∧
    (∀ j, secondLayer.partition.relabelBasis e₂ j
      ((secondLayer.partition.relabel e₂).split x j) =
        secondLayer.partition.split x (e₂.symm j)) :=
  ⟨firstLayer.partition.relabelBasis_split e₁ x, secondLayer.partition.relabelBasis_split e₂ x⟩

theorem preparation_enumeration_normalized (e : Fin 32 ≃ PreparationIndex) :
    IsKrausChannel (fun i => preparationOperator (e i)) := by
  unfold IsKrausChannel
  rw [e.sum_comp (fun i => (preparationOperator i).conjTranspose * preparationOperator i),
    ← preparationEnumeration.sum_comp
      (fun i => (preparationOperator i).conjTranspose * preparationOperator i)]
  exact preparation_normalized

theorem preparation_enumeration_action (e : Fin 32 ≃ PreparationIndex) (X : PhysicalMatrix) :
    krausMap (fun i => preparationOperator (e i)) X = X.trace • B4 := by
  unfold krausMap
  rw [e.sum_comp (fun i => preparationOperator i * X * (preparationOperator i).conjTranspose),
    ← preparationEnumeration.sum_comp
      (fun i => preparationOperator i * X * (preparationOperator i).conjTranspose)]
  exact preparation_action X

/-- Enumeration cannot move the preparation guard into the local Layer model. -/
theorem preparation_enumeration_not_layer (e : Fin 32 ≃ PreparationIndex) :
    ¬ ∃ L : Layer, ∀ X : PhysicalMatrix,
      L.action X = krausMap (fun i => preparationOperator (e i)) X := by
  intro h
  apply preparation_not_layer
  obtain ⟨L, hL⟩ := h
  refine ⟨L, fun X => ?_⟩
  rw [hL, preparation_enumeration_action, preparation_action]


theorem first_pair_exhausts (w : firstPartition.Fiber 0) :
    w = ⟨0, rfl⟩ ∨ w = ⟨1, rfl⟩ := by
  revert w
  decide

theorem second_pair_exhausts (j : Fin secondPartition.blocks) (w : secondPartition.Fiber j) :
    w = secondControl j ∨ w = secondTarget j := by
  revert w j
  decide

theorem first_idle (j : Fin firstLayer.partition.blocks) (hj : j ≠ (0 : Fin 3))
    (a : Fin (firstLayer.count j)) : firstLayer.operator j a = 1 := by
  fin_cases j
  · exact (hj rfl).elim
  all_goals
    ext x y
    simp [firstLayer, permutationLayer, firstLocal, forward, Matrix.one_apply]


end SKEFTHawking.QuantumNetwork.FiniteLocalChannelDepthWitness
