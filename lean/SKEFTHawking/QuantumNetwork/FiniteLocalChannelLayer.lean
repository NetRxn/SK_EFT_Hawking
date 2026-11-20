import SKEFTHawking.QuantumNetwork.CPTPChannel
import Mathlib.Analysis.Matrix.Order
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! Independent finite local channels on four labeled Boolean wires. -/

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

namespace SKEFTHawking.QuantumNetwork.FiniteLocalChannelLayer

section Tensor

variable {I : Type*} [Fintype I] [DecidableEq I] {α : I → Type*}
  [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]

/-- The dependent tensor is a product of complex matrix entries. -/
def tensor (A : ∀ i, Matrix (α i) (α i) ℂ) :
    Matrix (∀ i, α i) (∀ i, α i) ℂ :=
  fun x y => ∏ i, A i (x i) (y i)

omit [DecidableEq I] [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)] in
theorem tensor_conjTranspose (A : ∀ i, Matrix (α i) (α i) ℂ) :
    (tensor A).conjTranspose = tensor (fun i => (A i).conjTranspose) := by
  ext x y
  simp [tensor, Matrix.conjTranspose_apply]

omit [∀ i, DecidableEq (α i)] in
theorem tensor_mul (A B : ∀ i, Matrix (α i) (α i) ℂ) :
    tensor A * tensor B = tensor (fun i => A i * B i) := by
  classical
  ext x y
  simp only [Matrix.mul_apply, tensor]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i z => A i (x i) z * B i z (y i))).symm

omit [∀ i, DecidableEq (α i)] in
theorem tensor_trace (A : ∀ i, Matrix (α i) (α i) ℂ) :
    (tensor A).trace = ∏ i, (A i).trace := by
  classical
  exact (Fintype.prod_sum (fun i z => A i z z)).symm

omit [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)] in
theorem tensor_sum {κ : I → Type*} [∀ i, Fintype (κ i)]
    (A : ∀ i, κ i → Matrix (α i) (α i) ℂ) :
    (∑ a : ∀ i, κ i, tensor (fun i => A i (a i))) =
      tensor (fun i => ∑ a, A i a) := by
  classical
  ext x y
  simp only [Matrix.sum_apply, tensor]
  exact (Fintype.prod_sum (fun i a => A i a (x i) (y i))).symm

omit [DecidableEq I] [∀ i, Fintype (α i)] in
theorem tensor_one : tensor (fun i => (1 : Matrix (α i) (α i) ℂ)) = 1 := by
  classical
  ext x y
  by_cases h : x = y
  · subst y
    simp [tensor]
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra hn
      exact h (funext (fun i => by simpa using not_exists.mp hn i))
    rw [Matrix.one_apply_ne h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.one_apply_ne hi)

theorem tensor_posSemidef (A : ∀ i, Matrix (α i) (α i) ℂ)
    (hA : ∀ i, (A i).PosSemidef) : (tensor A).PosSemidef := by
  classical
  have hfactor : ∀ i, ∃ B : Matrix (α i) (α i) ℂ, A i = B.conjTranspose * B := by
    intro i
    exact (CStarAlgebra.nonneg_iff_eq_star_mul_self (a := A i)).mp (hA i).nonneg
  choose B hB using hfactor
  have heq : A = fun i => (B i).conjTranspose * B i := funext hB
  rw [heq, ← tensor_mul, ← tensor_conjTranspose]
  exact Matrix.posSemidef_conjTranspose_mul_self (tensor B)

theorem tensor_density (A : ∀ i, Matrix (α i) (α i) ℂ)
    (hA : ∀ i, IsDensityOperator (A i)) : IsDensityOperator (tensor A) := by
  refine ⟨tensor_posSemidef A (fun i => (hA i).1), ?_⟩
  rw [tensor_trace]
  simp [fun i => (hA i).2]

end Tensor

section Transport

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Pulling both matrix coordinates along an equivalence preserves physical action. -/
def pull (e : A ≃ B) (M : Matrix B B ℂ) : Matrix A A ℂ := M.submatrix e e

omit [DecidableEq A] [DecidableEq B] in
theorem pull_mul (e : A ≃ B) (M N : Matrix B B ℂ) :
    pull e (M * N) = pull e M * pull e N :=
  (Matrix.submatrix_mul_equiv M N e e e).symm

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
theorem pull_adjoint (e : A ≃ B) (M : Matrix B B ℂ) :
    pull e M.conjTranspose = (pull e M).conjTranspose :=
  (Matrix.conjTranspose_submatrix M e e).symm

omit [Fintype A] [Fintype B] in
theorem pull_one (e : A ≃ B) : pull e (1 : Matrix B B ℂ) = 1 :=
  Matrix.submatrix_one_equiv e

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
theorem pull_sum {J : Type*} [Fintype J] (e : A ≃ B) (M : J → Matrix B B ℂ) :
    pull e (∑ j, M j) = ∑ j, pull e (M j) := by
  ext x y
  simp only [pull, Matrix.submatrix_apply, Matrix.sum_apply]

omit [DecidableEq A] [DecidableEq B] in
theorem pull_trace (e : A ≃ B) (M : Matrix B B ℂ) :
    (pull e M).trace = M.trace := e.sum_comp (fun x => M x x)

omit [DecidableEq A] [DecidableEq B] in
theorem pull_density (e : A ≃ B) (M : Matrix B B ℂ) (hM : IsDensityOperator M) :
    IsDensityOperator (pull e M) :=
  ⟨hM.1.submatrix e, (pull_trace e M).trans hM.2⟩

end Transport

abbrev Wire := Fin 4
abbrev Basis := Wire → Bool
abbrev PhysicalMatrix := Matrix Basis Basis ℂ

/-- A surjective assignment of physical wires to nonempty blocks of size at most two. -/
structure Partition where
  blocks : ℕ
  blockOf : Wire → Fin blocks
  onto : Function.Surjective blockOf
  small : ∀ j, Fintype.card {w : Wire // blockOf w = j} ≤ 2

abbrev Partition.Fiber (P : Partition) (j : Fin P.blocks) :=
  {w : Wire // P.blockOf w = j}

abbrev Partition.LocalBasis (P : Partition) (j : Fin P.blocks) := P.Fiber j → Bool

/-- Restriction to fibers, with gluing along the original physical wire labels. -/
def Partition.split (P : Partition) : Basis ≃ (∀ j, P.LocalBasis j) :=
  Equiv.piCongrFiberwise (f := P.blockOf) (fun _ => Equiv.refl _)

theorem Partition.split_apply (P : Partition) (x : Basis) (j : Fin P.blocks)
    (w : P.Fiber j) : P.split x j w = x w.val := rfl

theorem Partition.glue_apply (P : Partition) (x : ∀ j, P.LocalBasis j) (w : Wire) :
    P.split.symm x w = x (P.blockOf w) ⟨w, rfl⟩ := rfl

theorem Partition.glue_split_wire (P : Partition) (x : Basis) (w : Wire) :
    P.split.symm (P.split x) w = x w := congrFun (P.split.symm_apply_apply x) w

theorem Partition.split_glue_wire (P : Partition) (x : ∀ j, P.LocalBasis j)
    (j : Fin P.blocks) (w : P.Fiber j) : P.split (P.split.symm x) j w = x j w := by
  rw [P.split.apply_symm_apply]

theorem Partition.fiber_nonempty (P : Partition) (j : Fin P.blocks) :
    Nonempty (P.Fiber j) := by
  obtain ⟨w, hw⟩ := P.onto j
  exact ⟨⟨w, hw⟩⟩

/-- Any finite labeling of a genuine singleton/pair partition can be encoded. -/
def encodePartition {J : Type*} [Fintype J] [DecidableEq J]
    (f : Wire → J) (hf : Function.Surjective f)
    (hs : ∀ j, Fintype.card {w : Wire // f w = j} ≤ 2) : Partition where
  blocks := Fintype.card J
  blockOf := fun w => Fintype.equivFin J (f w)
  onto := (Fintype.equivFin J).surjective.comp hf
  small := by
    intro j
    let e : {w : Wire // Fintype.equivFin J (f w) = j} ≃
        {w : Wire // f w = (Fintype.equivFin J).symm j} :=
      { toFun := fun w => ⟨w.val, (Fintype.equivFin J).injective (by simpa using w.property)⟩
        invFun := fun w => ⟨w.val, by simp [w.property]⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact (Fintype.card_congr e).trans_le (hs _)

theorem encodePartition_physical {J : Type*} [Fintype J] [DecidableEq J]
    (f : Wire → J) (hf : Function.Surjective f)
    (hs : ∀ j, Fintype.card {w : Wire // f w = j} ≤ 2) (w : Wire) :
    (Fintype.equivFin J).symm ((encodePartition f hf hs).blockOf w) = f w :=
  (Fintype.equivFin J).symm_apply_apply (f w)

/-- Each block has its own finite normalized complex Kraus family. -/
structure Layer where
  partition : Partition
  count : Fin partition.blocks → ℕ
  operator : ∀ j, Fin (count j) → Matrix (partition.LocalBasis j) (partition.LocalBasis j) ℂ
  normalized : ∀ j, IsKrausChannel (operator j)

/-- Every independent local choice occurs in the global sum. -/
abbrev Layer.Selector (L : Layer) := ∀ j, Fin (L.count j)

def Layer.blockKraus (L : Layer) (a : L.Selector) := tensor (fun j => L.operator j (a j))

def Layer.physicalKraus (L : Layer) (a : L.Selector) : PhysicalMatrix :=
  pull L.partition.split (L.blockKraus a)

/-- Flattening is enumeration only; the selector remains a dependent product. -/
def Layer.kraus (L : Layer) (a : Fin (Fintype.card L.Selector)) : PhysicalMatrix :=
  L.physicalKraus ((Fintype.equivFin L.Selector).symm a)

theorem Layer.block_normalized (L : Layer) :
    ∑ a, (L.blockKraus a).conjTranspose * L.blockKraus a = 1 := by
  simp_rw [blockKraus, tensor_conjTranspose, tensor_mul]
  rw [tensor_sum (fun j a => (L.operator j a).conjTranspose * L.operator j a)]
  have h : (fun j => ∑ a, (L.operator j a).conjTranspose * L.operator j a) =
      (fun j => (1 : Matrix (L.partition.LocalBasis j) (L.partition.LocalBasis j) ℂ)) :=
    funext L.normalized
  rw [h, tensor_one]

theorem Layer.physical_normalized (L : Layer) :
    ∑ a, (L.physicalKraus a).conjTranspose * L.physicalKraus a = 1 := by
  simp_rw [physicalKraus, ← pull_adjoint, ← pull_mul]
  rw [← pull_sum, L.block_normalized, pull_one]

theorem Layer.kraus_normalized (L : Layer) : IsKrausChannel L.kraus := by
  unfold IsKrausChannel kraus
  exact ((Fintype.equivFin L.Selector).symm.sum_comp
    (fun a => (L.physicalKraus a).conjTranspose * L.physicalKraus a)).trans
    L.physical_normalized

def Layer.action (L : Layer) (X : PhysicalMatrix) : PhysicalMatrix := krausMap L.kraus X

theorem Layer.action_density (L : Layer) {X : PhysicalMatrix} (hX : IsDensityOperator X) :
    IsDensityOperator (L.action X) := krausMap_isDensityOperator L.kraus_normalized hX


theorem Layer.action_eq_sum (L : Layer) (X : PhysicalMatrix) :
    L.action X = ∑ a : L.Selector,
      L.physicalKraus a * X * (L.physicalKraus a).conjTranspose := by
  unfold action krausMap kraus
  exact (Fintype.equivFin L.Selector).symm.sum_comp
    (fun a => L.physicalKraus a * X * (L.physicalKraus a).conjTranspose)

/-- Independence factors the actual channel action for arbitrary complex local matrices. -/
theorem Layer.block_action_product (L : Layer)
    (R : ∀ j, Matrix (L.partition.LocalBasis j) (L.partition.LocalBasis j) ℂ) :
    (∑ a : L.Selector, L.blockKraus a * tensor R * (L.blockKraus a).conjTranspose) =
      tensor (fun j => krausMap (L.operator j) (R j)) := by
  simp_rw [blockKraus, tensor_conjTranspose, tensor_mul]
  exact tensor_sum (fun j a => L.operator j a * R j * (L.operator j a).conjTranspose)

theorem Layer.action_product (L : Layer)
    (R : ∀ j, Matrix (L.partition.LocalBasis j) (L.partition.LocalBasis j) ℂ) :
    L.action (pull L.partition.split (tensor R)) =
      pull L.partition.split (tensor (fun j => krausMap (L.operator j) (R j))) := by
  rw [L.action_eq_sum]
  simp_rw [physicalKraus, ← pull_adjoint, ← pull_mul]
  rw [← pull_sum, L.block_action_product]

/-- Initialization allows an arbitrary complex density matrix at every wire. -/
structure ProductInput where
  localState : Wire → Matrix Bool Bool ℂ
  density : ∀ w, IsDensityOperator (localState w)

def ProductInput.state (ρ : ProductInput) : PhysicalMatrix := tensor ρ.localState

theorem ProductInput.state_density (ρ : ProductInput) : IsDensityOperator ρ.state :=
  tensor_density ρ.localState ρ.density

def ProductInput.blockState (ρ : ProductInput) (P : Partition) (j : Fin P.blocks) :
    Matrix (P.LocalBasis j) (P.LocalBasis j) ℂ := tensor (fun w : P.Fiber j => ρ.localState w.val)

theorem ProductInput.blockState_density (ρ : ProductInput) (P : Partition) (j : Fin P.blocks) :
    IsDensityOperator (ρ.blockState P j) :=
  tensor_density _ (fun w => ρ.density w.val)

theorem ProductInput.regroup (ρ : ProductInput) (P : Partition) :
    ρ.state = pull P.split (tensor (ρ.blockState P)) := by
  ext x y
  exact (Fintype.prod_fiberwise P.blockOf (fun w => ρ.localState w (x w) (y w))).symm

def Layer.blockOutput (L : Layer) (ρ : ProductInput) (j : Fin L.partition.blocks) :=
  krausMap (L.operator j) (ρ.blockState L.partition j)

theorem Layer.blockOutput_density (L : Layer) (ρ : ProductInput) (j : Fin L.partition.blocks) :
    IsDensityOperator (L.blockOutput ρ j) :=
  krausMap_isDensityOperator (L.normalized j) (ρ.blockState_density L.partition j)

theorem Layer.action_productInput (L : Layer) (ρ : ProductInput) :
    L.action ρ.state = pull L.partition.split (tensor (L.blockOutput ρ)) := by
  rw [ρ.regroup L.partition, L.action_product]
  rfl

/-- A coherent qubit density with nonzero imaginary off-diagonal entries. -/
def coherentDensity : Matrix Bool Bool ℂ :=
  (1 / 2 : ℝ) • Matrix.vecMulVec (fun b : Bool => if b then Complex.I else 1)
    (star (fun b : Bool => if b then Complex.I else 1))

theorem coherentDensity_density : IsDensityOperator coherentDensity := by
  refine ⟨(Matrix.posSemidef_vecMulVec_self_star _).smul (by norm_num : (0 : ℝ) ≤ 1 / 2), ?_⟩
  norm_num [coherentDensity, Matrix.trace, Fintype.sum_bool, Matrix.vecMulVec, Complex.real_smul]

theorem coherentDensity_offDiagonal : coherentDensity false true = -Complex.I / 2 := by
  norm_num [coherentDensity, Matrix.vecMulVec, Complex.real_smul]
  ring

def coherentInput : ProductInput := ⟨fun _ => coherentDensity, fun _ => coherentDensity_density⟩

theorem coherentInput_admitted : IsDensityOperator coherentInput.state :=
  coherentInput.state_density

/-- Lists are chronological: the head acts first. -/
def run (Ls : List Layer) (X : PhysicalMatrix) : PhysicalMatrix :=
  Ls.foldl (fun state L => L.action state) X

@[simp] theorem run_nil (X : PhysicalMatrix) : run [] X = X := rfl

@[simp] theorem run_cons (L : Layer) (Ls : List Layer) (X : PhysicalMatrix) :
    run (L :: Ls) X = run Ls (L.action X) := rfl

@[simp] theorem run_singleton (L : Layer) (X : PhysicalMatrix) : run [L] X = L.action X := rfl

theorem run_append (Ls Ms : List Layer) (X : PhysicalMatrix) :
    run (Ls ++ Ms) X = run Ms (run Ls X) := by
  induction Ls generalizing X with
  | nil => rfl
  | cons L Ls ih => exact ih (L.action X)

theorem run_density (Ls : List Layer) {X : PhysicalMatrix} (hX : IsDensityOperator X) :
    IsDensityOperator (run Ls X) := by
  induction Ls generalizing X with
  | nil => exact hX
  | cons L Ls ih => exact ih (L.action_density hX)

def depth (Ls : List Layer) : ℕ := Ls.length


theorem Partition.blocks_le_four (P : Partition) : P.blocks ≤ 4 := by
  simpa using Fintype.card_le_of_surjective P.blockOf P.onto

theorem Partition.two_le_blocks (P : Partition) : 2 ≤ P.blocks := by
  have hcard : (∑ j, Fintype.card (P.Fiber j)) = 4 := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv P.blockOf)
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => P.small j)
  have hbound : 4 ≤ P.blocks * 2 := by simpa [hcard] using hsum
  omega

/-- An arbitrary enumeration of the full independent selector gives the same action. -/
def Layer.enumeratedAction (L : Layer)
    (e : Fin (Fintype.card L.Selector) ≃ L.Selector) (X : PhysicalMatrix) : PhysicalMatrix :=
  krausMap (fun a => L.physicalKraus (e a)) X

theorem Layer.enumeratedAction_eq (L : Layer)
    (e : Fin (Fintype.card L.Selector) ≃ L.Selector) (X : PhysicalMatrix) :
    L.enumeratedAction e X = L.action X := by
  rw [L.action_eq_sum]
  exact e.sum_comp (fun a => L.physicalKraus a * X * (L.physicalKraus a).conjTranspose)

theorem Layer.global_enumeration_invariant (L : Layer)
    (e f : Fin (Fintype.card L.Selector) ≃ L.Selector) (X : PhysicalMatrix) :
    L.enumeratedAction e X = L.enumeratedAction f X := by
  rw [L.enumeratedAction_eq, L.enumeratedAction_eq]

/-- Local enumerations change independently at each block. -/
def Layer.reindexLocal (L : Layer) (e : ∀ j, Fin (L.count j) ≃ Fin (L.count j)) : Layer where
  partition := L.partition
  count := L.count
  operator := fun j a => L.operator j (e j a)
  normalized := by
    intro j
    exact ((e j).sum_comp (fun a => (L.operator j a).conjTranspose * L.operator j a)).trans
      (L.normalized j)

theorem Layer.reindexLocal_physicalKraus (L : Layer)
    (e : ∀ j, Fin (L.count j) ≃ Fin (L.count j)) (a : L.Selector) :
    (L.reindexLocal e).physicalKraus a = L.physicalKraus (Equiv.piCongrRight e a) := rfl

theorem Layer.local_enumeration_invariant (L : Layer)
    (e : ∀ j, Fin (L.count j) ≃ Fin (L.count j)) (X : PhysicalMatrix) :
    (L.reindexLocal e).action X = L.action X := by
  rw [Layer.action_eq_sum, L.action_eq_sum]
  simp_rw [L.reindexLocal_physicalKraus]
  exact (Equiv.piCongrRight e).sum_comp
    (fun a => L.physicalKraus a * X * (L.physicalKraus a).conjTranspose)

/-- Block renaming preserves the underlying physical wire of each fiber element. -/
def Partition.relabel (P : Partition) (e : Fin P.blocks ≃ Fin P.blocks) : Partition where
  blocks := P.blocks
  blockOf := fun w => e (P.blockOf w)
  onto := e.surjective.comp P.onto
  small := by
    intro j
    let f : {w : Wire // e (P.blockOf w) = j} ≃ P.Fiber (e.symm j) :=
      { toFun := fun w => ⟨w.val, e.injective (by simpa using w.property)⟩
        invFun := fun w => ⟨w.val, by simp [w.property]⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact (Fintype.card_congr f).trans_le (P.small _)

def Partition.relabelFiber (P : Partition) (e : Fin P.blocks ≃ Fin P.blocks)
    (j : Fin P.blocks) : (P.relabel e).Fiber j ≃ P.Fiber (e.symm j) where
  toFun w := ⟨w.val, e.injective (by simpa [Partition.relabel] using w.property)⟩
  invFun w := ⟨w.val, by simp [relabel, w.property]⟩
  left_inv _ := rfl
  right_inv _ := rfl

def Partition.relabelBasis (P : Partition) (e : Fin P.blocks ≃ Fin P.blocks)
    (j : Fin P.blocks) : (P.relabel e).LocalBasis j ≃ P.LocalBasis (e.symm j) :=
  Equiv.arrowCongr (P.relabelFiber e j) (Equiv.refl Bool)

theorem Partition.relabelBasis_split (P : Partition) (e : Fin P.blocks ≃ Fin P.blocks)
    (x : Basis) (j : Fin P.blocks) :
    P.relabelBasis e j ((P.relabel e).split x j) = P.split x (e.symm j) := rfl

/-- Relabeling transports local bases without performing a physical permutation. -/
def Layer.relabel (L : Layer) (e : Fin L.partition.blocks ≃ Fin L.partition.blocks) : Layer where
  partition := L.partition.relabel e
  count := fun j => L.count (e.symm j)
  operator := fun j a => pull (L.partition.relabelBasis e j) (L.operator (e.symm j) a)
  normalized := by
    intro j
    unfold IsKrausChannel
    simp_rw [← pull_adjoint, ← pull_mul]
    rw [← pull_sum, L.normalized (e.symm j), pull_one]

def Layer.relabelSelector (L : Layer) (e : Fin L.partition.blocks ≃ Fin L.partition.blocks) :
    L.Selector ≃ (L.relabel e).Selector := Equiv.piCongrLeft' (fun j => Fin (L.count j)) e

theorem Layer.relabel_physicalKraus (L : Layer)
    (e : Fin L.partition.blocks ≃ Fin L.partition.blocks) (a : L.Selector) :
    (L.relabel e).physicalKraus (L.relabelSelector e a) = L.physicalKraus a := by
  ext x y
  change (∏ j, L.operator (e.symm j) (a (e.symm j))
      (L.partition.split x (e.symm j)) (L.partition.split y (e.symm j))) =
    ∏ j, L.operator j (a j) (L.partition.split x j) (L.partition.split y j)
  exact e.symm.prod_comp (fun j =>
    L.operator j (a j) (L.partition.split x j) (L.partition.split y j))

theorem Layer.block_label_invariant (L : Layer)
    (e : Fin L.partition.blocks ≃ Fin L.partition.blocks) (X : PhysicalMatrix) :
    (L.relabel e).action X = L.action X := by
  rw [Layer.action_eq_sum, L.action_eq_sum]
  rw [← (L.relabelSelector e).sum_comp
    (fun a => (L.relabel e).physicalKraus a * X * ((L.relabel e).physicalKraus a).conjTranspose)]
  simp_rw [L.relabel_physicalKraus]


/-- Encoding a partition preserves exactly which physical wires share a block. -/
theorem encodePartition_same_block {J : Type*} [Fintype J] [DecidableEq J]
    (f : Wire → J) (hf : Function.Surjective f)
    (hs : ∀ j, Fintype.card {w : Wire // f w = j} ≤ 2) (u v : Wire) :
    (encodePartition f hf hs).blockOf u = (encodePartition f hf hs).blockOf v ↔ f u = f v :=
  (Fintype.equivFin J).injective.eq_iff

theorem Layer.enumerated_normalized (L : Layer)
    (e : Fin (Fintype.card L.Selector) ≃ L.Selector) :
    IsKrausChannel (fun a => L.physicalKraus (e a)) :=
  (e.sum_comp (fun a => (L.physicalKraus a).conjTranspose * L.physicalKraus a)).trans
    L.physical_normalized

theorem coherentDensity_offDiagonal_ne_zero : coherentDensity false true ≠ 0 := by
  rw [coherentDensity_offDiagonal]
  exact div_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (by norm_num)

theorem run_productInput_density (Ls : List Layer) (ρ : ProductInput) :
    IsDensityOperator (run Ls ρ.state) := run_density Ls ρ.state_density

theorem depth_append (Ls Ms : List Layer) : depth (Ls ++ Ms) = depth Ls + depth Ms :=
  List.length_append

end SKEFTHawking.QuantumNetwork.FiniteLocalChannelLayer
