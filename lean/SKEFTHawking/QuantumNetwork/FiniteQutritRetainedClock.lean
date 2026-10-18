import SKEFTHawking.QuantumNetwork.FiniteQutritAmbientRootObstruction
import SKEFTHawking.QuantumNetwork.DiamondNorm

/-!
# An actual retained two-sector clock

The physical system is a qutrit; the joint Hilbert carrier has dimension six.
The Kraus index records eleven alternatives, rather than a singleton readout.
All matrix identities are complex-linear ambient identities. The discrete
register records parity and supplies no physical elapsed-time calibration.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteQutritRetainedClock
open Matrix FiniteInterventionProcess
open FiniteQutritPhysicalMemory
open scoped BigOperators ComplexOrder Kronecker
abbrev C := Fin 2
abbrev Joint := Q × C
abbrev JointMat := Matrix Joint Joint ℂ
abbrev ClockMat := Matrix C C ℂ

def e (a b : C) : ClockMat := Matrix.single a b 1
def P (a : C) : ClockMat := e a a
def block (X : JointMat) (a b : C) : Mat := fun s t => X (s,a) (t,b)

theorem e_adjoint (a b : C) : (e a b)ᴴ = e b a := by
  simp [e, Matrix.conjTranspose_single]

theorem e_mul (a b c d : C) : e a b * e c d = if b = c then e a d else 0 := by
  ext s t
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    fin_cases s <;> fin_cases t <;> norm_num [e, Matrix.single, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem P_sum : P 0 + P 1 = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [P, e, Matrix.single, Matrix.one_apply]

theorem P_trace (a : C) : (P a).trace = 1 := by
  fin_cases a <;> norm_num [P, e, Matrix.single, Matrix.trace, Fin.sum_univ_two]

theorem corner_sandwich (A : Mat) (a b : C) (X : JointMat) :
    (A ⊗ₖ e a b) * X * (A ⊗ₖ e a b)ᴴ =
      (A * block X b b * Aᴴ) ⊗ₖ P a := by
  ext ⟨s,c⟩ ⟨t,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [e, P, Matrix.single, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, block]

/-- The explicit recoding retains every Option-labelled alternative. -/
def labelEquiv : Option (Fin 10) ≃ Fin 11 := (finSuccEquiv 10).symm

def optionKraus : Option (Fin 10) → JointMat
  | none => (1 : Mat) ⊗ₖ e 1 0
  | some i => FiniteQutritAveragedTransfer.krausOperator i ⊗ₖ e 0 1

def K (i : Fin 11) : JointMat := optionKraus (labelEquiv.symm i)

theorem K_label (i : Option (Fin 10)) : K (labelEquiv i) = optionKraus i := by
  simp [K]

theorem sum_labels {M : Type*} [AddCommMonoid M] (f : Fin 11 → M) :
    (∑ i, f i) = f (labelEquiv none) + ∑ i : Fin 10, f (labelEquiv (some i)) := by
  rw [← labelEquiv.sum_comp f, Fintype.sum_option]

private theorem sum_tensor {α : Type*} [Fintype α] (A : α → Mat) (B : ClockMat) :
    (∑ i, A i ⊗ₖ B) = (∑ i, A i) ⊗ₖ B := by
  ext ⟨s,a⟩ ⟨t,b⟩
  simp [Matrix.sum_apply, Finset.sum_mul]

theorem K_normalized : IsKrausChannel K := by
  unfold IsKrausChannel
  rw [sum_labels]
  simp only [K_label, optionKraus, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, e_adjoint, ← Matrix.mul_kronecker_mul, one_mul,
    e_mul, ite_true]
  rw [sum_tensor, FiniteQutritAveragedTransfer.kraus_normalized]
  change (1 : Mat) ⊗ₖ P 0 + (1 : Mat) ⊗ₖ P 1 = 1
  rw [← Matrix.kronecker_add, P_sum, Matrix.one_kronecker_one]

def J : JointMat →ₗ[ℂ] JointMat where
  toFun := krausMap K
  map_add' := krausMap_add K
  map_smul' := krausMap_smul K

theorem J_action (X : JointMat) :
    J X = block X 0 0 ⊗ₖ P 1 +
      FiniteQutritAveragedTransfer.transfer (block X 1 1) ⊗ₖ P 0 := by
  change (∑ i, K i * X * (K i)ᴴ) = _
  rw [sum_labels]
  simp only [K_label, optionKraus, corner_sandwich, Matrix.one_mul, Matrix.mul_one,
    Matrix.conjTranspose_one]
  rw [sum_tensor]
  exact congrArg (fun Y => block X 0 0 ⊗ₖ P 1 + Y ⊗ₖ P 0)
    (FiniteQutritAveragedTransfer.kraus_action (block X 1 1))

theorem block_tensor (X : Mat) (a b c : C) :
    block (X ⊗ₖ P a) b c = if b = a ∧ c = a then X else 0 := by
  ext s t
  by_cases hb : b = a <;> by_cases hc : c = a <;>
    simp [block, P, e, Matrix.single, hb, hc, Ne.symm]

theorem block_one (a : C) : block (1 : JointMat) a a = 1 := by
  ext s t
  simp [block, Matrix.one_apply]

theorem J_one : J 1 = 1 := by
  rw [J_action, block_one, block_one, FiniteQutritAveragedTransfer.transfer_one,
    ← Matrix.kronecker_add, add_comm, P_sum, Matrix.one_kronecker_one]

theorem K_unital : (∑ i, K i * (K i)ᴴ) = 1 := by
  simpa [J, krausMap] using J_one

theorem J_positive {X : JointMat} (hX : X.PosSemidef) : (J X).PosSemidef :=
  krausMap_posSemidef K hX

theorem J_trace (X : JointMat) : (J X).trace = X.trace := trace_krausMap K_normalized X

theorem J_density {X : JointMat} (hX : IsDensityOperator X) : IsDensityOperator (J X) :=
  krausMap_isDensityOperator K_normalized hX

def embedClock (a : C) : Mat →ₗ[ℂ] JointMat where
  toFun X := X ⊗ₖ P a
  map_add' X Y := Matrix.add_kronecker X Y (P a)
  map_smul' c X := by ext ⟨s,b⟩ ⟨t,d⟩; simp [mul_assoc]

def E0 : Mat →ₗ[ℂ] JointMat := embedClock 0

/-- Actual second-factor trace, with no dimension divisor. -/
def D : JointMat →ₗ[ℂ] Mat where
  toFun := SKEFTHawking.QuantumNetwork.partialTrace
  map_add' := partialTrace_add
  map_smul' c X := by ext s t; simp [partialTrace, mul_add]

theorem D_blocks (X : JointMat) : D X = block X 0 0 + block X 1 1 := by
  ext s t
  simp [D, partialTrace, Fin.sum_univ_two, block]

theorem D_embed (a : C) (X : Mat) : D (embedClock a X) = X := by
  rw [D_blocks]
  change block (X ⊗ₖ P a) 0 0 + block (X ⊗ₖ P a) 1 1 = X
  rw [block_tensor, block_tensor]
  fin_cases a <;> simp

theorem J_embed_zero (X : Mat) : J (E0 X) = embedClock 1 X := by
  rw [J_action]
  simp [E0, embedClock, block_tensor]

theorem J_embed_one (X : Mat) :
    J (embedClock 1 X) = E0 (FiniteQutritAveragedTransfer.transfer X) := by
  rw [J_action]
  simp [embedClock, E0, block_tensor]

/-- Rectangular preparation isometry from the qutrit into clock sector a. -/
def V (a : C) : Matrix Joint Q ℂ := fun p t =>
  (1 : Mat) p.1 t * if p.2 = a then 1 else 0

theorem V_isometry (a : C) : (V a)ᴴ * V a = 1 := by
  ext s t
  fin_cases a <;> simp [V, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.one_apply, eq_comm]

theorem V_range (a : C) : V a * (V a)ᴴ = (1 : Mat) ⊗ₖ P a := by
  ext ⟨s,b⟩ ⟨t,c⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [V, P, e, Matrix.single, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply]

theorem V_complete : (∑ a : C, V a * (V a)ᴴ) = 1 := by
  simp only [V_range, Fin.sum_univ_two]
  rw [← Matrix.kronecker_add, P_sum, Matrix.one_kronecker_one]

theorem V_prepare (a : C) (X : Mat) : V a * X * (V a)ᴴ = embedClock a X := by
  ext ⟨s,b⟩ ⟨t,c⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [V, embedClock, P, e, Matrix.single, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply]

theorem V_compress (a : C) (X : JointMat) : (V a)ᴴ * X * V a = block X a a := by
  ext s t
  fin_cases a <;> simp [V, block, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply]

theorem D_rectangular (X : JointMat) : D X = ∑ a : C, (V a)ᴴ * X * V a := by
  simp only [V_compress, Fin.sum_univ_two, D_blocks]

theorem embed_positive (a : C) {X : Mat} (hX : X.PosSemidef) :
    (embedClock a X).PosSemidef := by
  rw [← V_prepare]
  simpa using hX.conjTranspose_mul_mul_same ((V a)ᴴ)

theorem embed_trace (a : C) (X : Mat) : (embedClock a X).trace = X.trace := by
  change (X ⊗ₖ P a).trace = _
  rw [Matrix.trace_kronecker, P_trace, mul_one]

theorem embed_density (a : C) {X : Mat} (hX : IsDensityOperator X) :
    IsDensityOperator (embedClock a X) :=
  ⟨embed_positive a hX.1, (embed_trace a X).trans hX.2⟩

theorem D_positive {X : JointMat} (hX : X.PosSemidef) : (D X).PosSemidef := by
  rw [D_rectangular]
  exact Matrix.posSemidef_sum _ (fun a _ => hX.conjTranspose_mul_mul_same (V a))

theorem D_trace (X : JointMat) : (D X).trace = X.trace := trace_partialTrace X

theorem D_density {X : JointMat} (hX : IsDensityOperator X) : IsDensityOperator (D X) :=
  ⟨D_positive hX.1, (D_trace X).trans hX.2⟩

/-- Literal repeated actual joint channel. -/
def jointIterate : ℕ → JointMat →ₗ[ℂ] JointMat
  | 0 => LinearMap.id
  | n+1 => (jointIterate n).comp J

theorem jointIterate_left (n : ℕ) (X : JointMat) :
    jointIterate (n+1) X = J (jointIterate n X) := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih => exact ih (J X)

theorem transferIterate_left (n : ℕ) (X : Mat) :
    FiniteQutritAveragedTransfer.iterate (n+1) X =
      FiniteQutritAveragedTransfer.transfer (FiniteQutritAveragedTransfer.iterate n X) := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih => exact ih (FiniteQutritAveragedTransfer.transfer X)

theorem encoded_even (n : ℕ) (X : Mat) :
    jointIterate (2*n) (E0 X) = E0 (FiniteQutritAveragedTransfer.iterate n X) := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1) = (2*n+1)+1 by omega, jointIterate_left,
      jointIterate_left, ih, J_embed_zero, J_embed_one, ← transferIterate_left]

theorem encoded_odd (n : ℕ) (X : Mat) :
    jointIterate (2*n+1) (E0 X) = embedClock 1 (FiniteQutritAveragedTransfer.iterate n X) := by
  rw [jointIterate_left, encoded_even, J_embed_zero]

theorem reduced_even (n : ℕ) (X : Mat) :
    D (jointIterate (2*n) (E0 X)) = FiniteQutritAveragedTransfer.iterate n X := by
  rw [encoded_even, E0, D_embed]

theorem reduced_odd (n : ℕ) (X : Mat) :
    D (jointIterate (2*n+1) (E0 X)) = FiniteQutritAveragedTransfer.iterate n X := by
  rw [encoded_odd, D_embed]

theorem arbitrary_odd (n : ℕ) (X : JointMat) :
    jointIterate (2*n+1) X =
      embedClock 1 (FiniteQutritAveragedTransfer.iterate n (block X 0 0)) +
      E0 (FiniteQutritAveragedTransfer.iterate (n+1) (block X 1 1)) := by
  induction n with
  | zero => exact J_action X
  | succ n ih =>
    rw [show 2*(n+1)+1 = ((2*n+1)+1)+1 by omega,
      jointIterate_left, jointIterate_left, ih]
    simp only [map_add, J_embed_one, J_embed_zero, ← transferIterate_left]

theorem arbitrary_even (n : ℕ) (hn : 1 ≤ n) (X : JointMat) :
    jointIterate (2*n) X =
      E0 (FiniteQutritAveragedTransfer.iterate n (block X 0 0)) +
      embedClock 1 (FiniteQutritAveragedTransfer.iterate n (block X 1 1)) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [show 2*(k+1) = (2*k+1)+1 by omega, jointIterate_left, arbitrary_odd]
  simp only [map_add, J_embed_one, J_embed_zero, ← transferIterate_left]

theorem quotient_even (n : ℕ) (q : FiniteQutritInvariantReconstruction.FeatureSpace) :
    D (jointIterate (2*n) (E0 (FiniteQutritInvariantReconstruction.U q))) =
      FiniteQutritInvariantReconstruction.U (FiniteQutritAveragedTransfer.quotientIterate n q) := by
  rw [reduced_even, FiniteQutritAveragedTransfer.U_iterate]

theorem quotient_odd (n : ℕ) (q : FiniteQutritInvariantReconstruction.FeatureSpace) :
    D (jointIterate (2*n+1) (E0 (FiniteQutritInvariantReconstruction.U q))) =
      FiniteQutritInvariantReconstruction.U (FiniteQutritAveragedTransfer.quotientIterate n q) := by
  rw [reduced_odd, FiniteQutritAveragedTransfer.U_iterate]

variable (F : Type*) [Fintype F] [DecidableEq F]
abbrev SpectatorMat := Matrix (Joint × F) (Joint × F) ℂ

def amplified : SpectatorMat F →ₗ[ℂ] SpectatorMat F where
  toFun := krausMap (fun i => K i ⊗ₖ (1 : Matrix F F ℂ))
  map_add' := krausMap_add _
  map_smul' := krausMap_smul _

theorem amplified_normalized : IsKrausChannel (fun i => K i ⊗ₖ (1 : Matrix F F ℂ)) := by
  unfold IsKrausChannel
  simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  rw [sum_kronOne_general, K_normalized, Matrix.one_kronecker_one]

/-- Complete positivity on arbitrary correlated joint/clock/spectator inputs. -/
theorem amplified_positive {X : SpectatorMat F} (hX : X.PosSemidef) :
    (amplified F X).PosSemidef := krausMap_posSemidef _ hX

theorem amplified_trace (X : SpectatorMat F) : (amplified F X).trace = X.trace :=
  trace_krausMap (amplified_normalized F) X

theorem amplified_density {X : SpectatorMat F} (hX : IsDensityOperator X) :
    IsDensityOperator (amplified F X) := krausMap_isDensityOperator (amplified_normalized F) hX

def amplifiedPreparation (a : C)
    (X : Matrix (Q × F) (Q × F) ℂ) : SpectatorMat F :=
  (V a ⊗ₖ (1 : Matrix F F ℂ)) * X * (V a ⊗ₖ (1 : Matrix F F ℂ))ᴴ

def amplifiedReduction (X : SpectatorMat F) : Matrix (Q × F) (Q × F) ℂ :=
  ∑ a : C, (V a ⊗ₖ (1 : Matrix F F ℂ))ᴴ * X * (V a ⊗ₖ (1 : Matrix F F ℂ))

theorem preparation_CP (a : C) {X : Matrix (Q × F) (Q × F) ℂ} (hX : X.PosSemidef) :
    (amplifiedPreparation F a X).PosSemidef := by
  simpa [amplifiedPreparation] using
    hX.conjTranspose_mul_mul_same ((V a ⊗ₖ (1 : Matrix F F ℂ))ᴴ)

theorem reduction_CP {X : SpectatorMat F} (hX : X.PosSemidef) :
    (amplifiedReduction F X).PosSemidef :=
  Matrix.posSemidef_sum _ (fun _ _ => hX.conjTranspose_mul_mul_same _)

/-- The clock is inserted between system and spectator by this actual permutation. -/
def clockSpectatorEquiv : ((Q × F) × C) ≃ ((Q × C) × F) where
  toFun p := ((p.1.1,p.2),p.1.2)
  invFun p := ((p.1.1,p.2),p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem preparation_entry (a : C) (Y : Matrix (Q × F) (Q × F) ℂ)
    (s t : Q) (c d : C) (f g : F) :
    amplifiedPreparation F a Y ((s,c),f) ((t,d),g) = Y (s,f) (t,g) * P a c d := by
  fin_cases a <;> fin_cases c <;> fin_cases d <;>
    simp [amplifiedPreparation, V, P, e, Matrix.single, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.one_apply, apply_ite]

theorem preparation_reindex (a : C) (Y : Matrix (Q × F) (Q × F) ℂ) :
    amplifiedPreparation F a Y =
      (Y ⊗ₖ P a).submatrix (clockSpectatorEquiv F).symm (clockSpectatorEquiv F).symm := by
  ext ⟨⟨s,c⟩,f⟩ ⟨⟨t,d⟩,g⟩
  exact preparation_entry F a Y s t c d f g

theorem reduction_entry (X : SpectatorMat F) (s t : Q) (f g : F) :
    amplifiedReduction F X (s,f) (t,g) = ∑ a : C, X ((s,a),f) ((t,a),g) := by
  simp [amplifiedReduction, V, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.one_apply, Matrix.sum_apply, apply_ite]

def spectatorBlock (X : SpectatorMat F) (f g : F) : JointMat :=
  fun s t => X (s,f) (t,g)

theorem preparation_block (a : C) (Y : Matrix (Q × F) (Q × F) ℂ) (f g : F) :
    spectatorBlock F (amplifiedPreparation F a Y) f g =
      embedClock a (FiniteQutritInvariantExamples.block F f g Y) := by
  ext ⟨s,c⟩ ⟨t,d⟩
  exact preparation_entry F a Y s t c d f g

theorem amplified_block (X : SpectatorMat F) (f g : F) :
    spectatorBlock F (amplified F X) f g = J (spectatorBlock F X f g) := by
  ext s t
  simp [amplified, J, spectatorBlock, krausMap, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.one_apply, apply_ite]

def amplifiedJointIterate : ℕ → SpectatorMat F →ₗ[ℂ] SpectatorMat F
  | 0 => LinearMap.id
  | n+1 => (amplifiedJointIterate n).comp (amplified F)

theorem amplifiedJointIterate_block (n : ℕ) (X : SpectatorMat F) (f g : F) :
    spectatorBlock F (amplifiedJointIterate F n X) f g =
      jointIterate n (spectatorBlock F X f g) := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih =>
    change spectatorBlock F (amplifiedJointIterate F n (amplified F X)) f g = _
    rw [ih, amplified_block]
    rfl

theorem reduction_block (X : SpectatorMat F) (f g : F) :
    FiniteQutritInvariantExamples.block F f g (amplifiedReduction F X) =
      D (spectatorBlock F X f g) := by
  ext s t
  exact reduction_entry F X s t f g

theorem systemIterate_block (n : ℕ) (Y : Matrix (Q × F) (Q × F) ℂ) (f g : F) :
    FiniteQutritInvariantExamples.block F f g (FiniteQutritAveragedTransfer.amplifiedIterate F n Y) =
      FiniteQutritAveragedTransfer.iterate n (FiniteQutritInvariantExamples.block F f g Y) := by
  induction n generalizing Y with
  | zero => rfl
  | succ n ih =>
    change FiniteQutritInvariantExamples.block F f g
      (FiniteQutritAveragedTransfer.amplifiedIterate F n
        (FiniteQutritAveragedTransfer.amplified F Y)) = _
    rw [ih, FiniteQutritAveragedTransfer.amplified_block]
    rfl

/-- Both reductions hold for every correlated complex input, including empty F. -/
theorem spectator_reduced_even (n : ℕ) (Y : Matrix (Q × F) (Q × F) ℂ) :
    amplifiedReduction F (amplifiedJointIterate F (2*n) (amplifiedPreparation F 0 Y)) =
      FiniteQutritAveragedTransfer.amplifiedIterate F n Y := by
  ext ⟨s,f⟩ ⟨t,g⟩
  have h := reduction_block F (amplifiedJointIterate F (2*n) (amplifiedPreparation F 0 Y)) f g
  rw [amplifiedJointIterate_block, preparation_block, ← E0, reduced_even,
    ← systemIterate_block] at h
  exact congrFun (congrFun h s) t

theorem spectator_reduced_odd (n : ℕ) (Y : Matrix (Q × F) (Q × F) ℂ) :
    amplifiedReduction F (amplifiedJointIterate F (2*n+1) (amplifiedPreparation F 0 Y)) =
      FiniteQutritAveragedTransfer.amplifiedIterate F n Y := by
  ext ⟨s,f⟩ ⟨t,g⟩
  have h := reduction_block F (amplifiedJointIterate F (2*n+1) (amplifiedPreparation F 0 Y)) f g
  rw [amplifiedJointIterate_block, preparation_block, ← E0, reduced_odd,
    ← systemIterate_block] at h
  exact congrFun (congrFun h s) t

theorem preparation_trace (a : C) (Y : Matrix (Q × F) (Q × F) ℂ) :
    (amplifiedPreparation F a Y).trace = Y.trace := by
  unfold amplifiedPreparation
  rw [Matrix.trace_mul_cycle, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, V_isometry, Matrix.conjTranspose_one, Matrix.one_mul,
    Matrix.one_kronecker_one, Matrix.one_mul]

theorem reduction_trace (X : SpectatorMat F) : (amplifiedReduction F X).trace = X.trace := by
  simp only [amplifiedReduction, Matrix.trace_sum]
  have hc : ∀ a : C, (((V a ⊗ₖ (1 : Matrix F F ℂ))ᴴ * X *
      (V a ⊗ₖ (1 : Matrix F F ℂ))).trace) =
      ((V a ⊗ₖ (1 : Matrix F F ℂ)) * (V a ⊗ₖ (1 : Matrix F F ℂ))ᴴ * X).trace :=
    fun _ => Matrix.trace_mul_cycle _ _ _
  simp only [hc]
  rw [← Matrix.trace_sum, ← Finset.sum_mul]
  have hn : (∑ a : C, (V a ⊗ₖ (1 : Matrix F F ℂ)) *
      (V a ⊗ₖ (1 : Matrix F F ℂ))ᴴ) = 1 := by
    simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul]
    rw [sum_kronOne_general, V_complete, Matrix.one_kronecker_one]
  rw [hn, Matrix.one_mul]

/-- Eleven actual outcomes, each with one actual Kraus operator. -/
def instrument : FiniteInstrument Joint 11 where
  count := 1
  operators a _ := K a
  normalized := by simpa [IsKrausChannel] using K_normalized

def recordTree : (n : ℕ) → Tree Joint F 11 n
  | 0 => .done
  | n+1 => .node (localStep Joint F 11 instrument) (fun _ => recordTree n)

theorem record_branch (a : Fin 11) (X : SpectatorMat F) :
    (localStep Joint F 11 instrument).branch Joint F 11 a X =
      (K a ⊗ₖ (1 : Matrix F F ℂ)) * X * (K a ⊗ₖ (1 : Matrix F F ℂ))ᴴ := by
  simp [localStep_branch, instrument, FiniteInstrument.branch, FiniteInstrument.lift, krausMap]

theorem record_branch_sum (X : SpectatorMat F) :
    (∑ a, (localStep Joint F 11 instrument).branch Joint F 11 a X) = amplified F X := by
  simp only [record_branch]
  rfl

theorem all_records_sum (n : ℕ) (X : SpectatorMat F) :
    (∑ h, run Joint F 11 (recordTree F n) h X) = amplifiedJointIterate F n X := by
  induction n generalizing X with
  | zero => change (∑ _ : Unit, X) = X; simp
  | succ n ih =>
    change (∑ h : Fin 11 × History 11 n, run Joint F 11 (recordTree F n) h.2
      ((localStep Joint F 11 instrument).branch Joint F 11 h.1 X)) = _
    rw [Fintype.sum_prod_type]
    simp_rw [ih]
    rw [← map_sum, record_branch_sum]
    rfl

theorem all_records_positive (n : ℕ) (h : History 11 n)
    {X : SpectatorMat F} (hX : X.PosSemidef) :
    (run Joint F 11 (recordTree F n) h X).PosSemidef :=
  run_posSemidef Joint F 11 _ h hX

theorem all_records_normalized (n : ℕ) {X : SpectatorMat F} (hX : IsDensityOperator X) :
    (∀ h, 0 ≤ weight Joint F 11 (recordTree F n) h X) ∧
      (∑ h, weight Joint F 11 (recordTree F n) h X) = 1 :=
  normalized_weights Joint F 11 _ hX

theorem all_records_card (n : ℕ) : Fintype.card (History 11 n) = 11^n := history_card 11 n

theorem empty_record (X : SpectatorMat F) : run Joint F 11 (recordTree F 0) () X = X := rfl

/-- Discard the clock and prepare its pure zero sector again. -/
def resetClock : JointMat →ₗ[ℂ] JointMat := E0.comp D

def L (a : C) : JointMat := (1 : Mat) ⊗ₖ e 0 a

theorem L_normalized : IsKrausChannel L := by
  unfold IsKrausChannel
  simp only [L, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    e_adjoint, ← Matrix.mul_kronecker_mul, Matrix.one_mul, e_mul, ite_true,
    Fin.sum_univ_two]
  change (1 : Mat) ⊗ₖ P 0 + (1 : Mat) ⊗ₖ P 1 = 1
  rw [← Matrix.kronecker_add, P_sum, Matrix.one_kronecker_one]

theorem reset_kraus_action (X : JointMat) : krausMap L X = resetClock X := by
  simp only [krausMap, L, corner_sandwich, Matrix.one_mul, Matrix.conjTranspose_one,
    Matrix.mul_one, Fin.sum_univ_two]
  change block X 0 0 ⊗ₖ P 0 + block X 1 1 ⊗ₖ P 0 = (D X) ⊗ₖ P 0
  rw [D_blocks, Matrix.add_kronecker]

theorem reset_positive {X : JointMat} (hX : X.PosSemidef) :
    (resetClock X).PosSemidef := by
  rw [← reset_kraus_action]
  exact krausMap_posSemidef L hX

theorem reset_trace (X : JointMat) : (resetClock X).trace = X.trace := by
  rw [← reset_kraus_action]
  exact trace_krausMap L_normalized X

theorem reset_density {X : JointMat} (hX : IsDensityOperator X) :
    IsDensityOperator (resetClock X) := ⟨reset_positive hX.1, (reset_trace X).trans hX.2⟩

theorem reset_CP {X : SpectatorMat F} (hX : X.PosSemidef) :
    (krausMap (fun a => L a ⊗ₖ (1 : Matrix F F ℂ)) X).PosSemidef :=
  krausMap_posSemidef _ hX

theorem reset_idempotent (X : JointMat) : resetClock (resetClock X) = resetClock X := by
  change E0 (D (E0 (D X))) = E0 (D X)
  rw [E0, D_embed]

theorem reset_one : resetClock 1 = (2 : ℂ) • ((1 : Mat) ⊗ₖ P 0) := by
  change (D 1) ⊗ₖ P 0 = _
  rw [D_blocks, block_one, block_one, Matrix.add_kronecker]
  module

theorem reset_not_unital : resetClock 1 ≠ 1 := by
  intro h
  have he := congrFun (congrFun h (0,1)) (0,1)
  rw [reset_one] at he
  norm_num [P, e, Matrix.single, Matrix.one_apply] at he

/-- The clock marginal, tracing the physical qutrit rather than the clock. -/
def clockMarginal (X : JointMat) : ClockMat := fun a b => (block X a b).trace

theorem clockMarginal_embed (a : C) (X : Mat) (hX : X.trace = 1) :
    clockMarginal (embedClock a X) = P a := by
  ext b c
  change (block (X ⊗ₖ P a) b c).trace = P a b c
  rw [block_tensor]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [P, e, Matrix.single, hX]

theorem jointIterate_density (n : ℕ) {X : JointMat} (hX : IsDensityOperator X) :
    IsDensityOperator (jointIterate n X) := by
  induction n generalizing X with
  | zero => exact hX
  | succ n ih => exact ih (J_density hX)

theorem encoded_density_even (n : ℕ) {X : Mat} (hX : IsDensityOperator X) :
    IsDensityOperator (jointIterate (2*n) (E0 X)) ∧
      clockMarginal (jointIterate (2*n) (E0 X)) = P 0 := by
  constructor
  · exact jointIterate_density _ (embed_density 0 hX)
  · rw [encoded_even]
    exact clockMarginal_embed 0 _ ((FiniteQutritAveragedTransfer.iterate_trace n X).trans hX.2)

theorem encoded_density_odd (n : ℕ) {X : Mat} (hX : IsDensityOperator X) :
    IsDensityOperator (jointIterate (2*n+1) (E0 X)) ∧
      clockMarginal (jointIterate (2*n+1) (E0 X)) = P 1 := by
  constructor
  · exact jointIterate_density _ (embed_density 0 hX)
  · rw [encoded_odd]
    exact clockMarginal_embed 1 _ ((FiniteQutritAveragedTransfer.iterate_trace n X).trans hX.2)

def rho0 : Mat := projector 0

theorem rho0_density : IsDensityOperator rho0 :=
  FiniteQutritAmbientRootObstruction.coordinate_projector_density 0

theorem encoded_rho0_density : IsDensityOperator (E0 rho0) := embed_density 0 rho0_density

theorem reset_defect (X : Mat) : resetClock (J (E0 X)) - J (E0 X) = X ⊗ₖ (P 0 - P 1) := by
  rw [J_embed_zero]
  change E0 (D (embedClock 1 X)) - embedClock 1 X = _
  rw [D_embed]
  ext ⟨s,a⟩ ⟨t,b⟩
  simp [E0, embedClock, mul_sub]

theorem reset_defect_rho0_entry :
    (resetClock (J (E0 rho0)) - J (E0 rho0)) (0,0) (0,0) = 1 := by
  rw [reset_defect]
  norm_num [rho0, projector, P, e, Matrix.single]

theorem reset_defect_nonzero (X : Mat) (hX : X.trace = 1) :
    resetClock (J (E0 X)) - J (E0 X) ≠ 0 := by
  rw [reset_defect]
  intro h
  have hx : X = 0 := by
    ext s t
    have he := congrFun (congrFun h (s,0)) (t,0)
    simpa [P, e, Matrix.single] using he
  rw [hx, Matrix.trace_zero] at hX
  exact zero_ne_one hX

theorem transfer_rho0 : FiniteQutritAveragedTransfer.transfer rho0 =
    Matrix.diagonal ![(4/5 : ℂ),1/10,1/10] := by
  rw [FiniteQutritAveragedTransfer.transfer_apply]
  ext s t
  fin_cases s <;> fin_cases t <;>
    norm_num [FiniteQutritAveragedTransfer.pinching_apply, rho0, projector,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, Matrix.diagonal]

theorem retained_two_ticks : D (J (J (E0 rho0))) = FiniteQutritAveragedTransfer.transfer rho0 := by
  rw [J_embed_zero, J_embed_one, E0, D_embed]

theorem reset_two_ticks (X : Mat) : D (J (resetClock (J (E0 X)))) = X := by
  rw [J_embed_zero]
  change D (J (E0 (D (embedClock 1 X)))) = X
  rw [D_embed, J_embed_zero, D_embed]

def event0 (X : Mat) : ℝ := ((projector 0 * X).trace).re

theorem event0_effect : (projector 0).PosSemidef ∧ (1-projector 0).PosSemidef := by
  constructor
  · exact rho0_density.1
  · have h := Matrix.posSemidef_conjTranspose_mul_self (1-projector 0)
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, (projector_hermitian 0).eq] at h
    have hc := outcomeOperator_idempotent 0 1
    change (1-projector 0) * (1-projector 0) = 1-projector 0 at hc
    rwa [hc] at h

theorem retained_event : event0 (D (J (J (E0 rho0)))) = 4/5 := by
  rw [retained_two_ticks, transfer_rho0]
  norm_num [event0, projector, Matrix.mul_apply, Matrix.trace, Matrix.diagonal, Fin.sum_univ_succ, Matrix.vecHead]

theorem reset_event : event0 (D (J (resetClock (J (E0 rho0))))) = 1 := by
  rw [reset_two_ticks]
  norm_num [event0, rho0, projector, Matrix.mul_apply, Matrix.trace, Fin.sum_univ_succ]

theorem attained_gap :
    |event0 (D (J (J (E0 rho0)))) - event0 (D (J (resetClock (J (E0 rho0)))))| = 1/5 := by
  rw [retained_event, reset_event]
  norm_num

/-- The generic algebra uses no retraction, trace, unitality or invariant-feature premise. -/
theorem generic_positive_root
    (Jg : JointMat →ₗ[ℂ] JointMat) (Eg : Mat →ₗ[ℂ] JointMat) (Dg : JointMat →ₗ[ℂ] Mat)
    (hJ : ∀ X, X.PosSemidef → (Jg X).PosSemidef)
    (hE : ∀ X, X.PosSemidef → (Eg X).PosSemidef)
    (hD : ∀ X, X.PosSemidef → (Dg X).PosSemidef)
    (h2 : Dg.comp (Jg.comp (Jg.comp Eg)) = FiniteQutritAveragedTransfer.transfer)
    (hc : Eg.comp (Dg.comp (Jg.comp Eg)) = Jg.comp Eg) :
    let R := Dg.comp (Jg.comp Eg)
    R.comp R = FiniteQutritAveragedTransfer.transfer ∧
      ∀ X, X.PosSemidef → (R X).PosSemidef := by
  constructor
  · ext X s t
    have h := LinearMap.congr_fun hc X
    have hh := congrArg (fun Y => Dg (Jg Y)) h
    have htwo := LinearMap.congr_fun h2 X
    change Dg (Jg (Eg (Dg (Jg (Eg X))))) = Dg (Jg (Jg (Eg X))) at hh
    exact congrFun (congrFun (hh.trans htwo) s) t
  · intro X hX
    exact hD _ (hJ _ (hE _ hX))

theorem generic_closure_impossible
    (Jg : JointMat →ₗ[ℂ] JointMat) (Eg : Mat →ₗ[ℂ] JointMat) (Dg : JointMat →ₗ[ℂ] Mat)
    (hJ : ∀ X, X.PosSemidef → (Jg X).PosSemidef)
    (hE : ∀ X, X.PosSemidef → (Eg X).PosSemidef)
    (hD : ∀ X, X.PosSemidef → (Dg X).PosSemidef)
    (h2 : Dg.comp (Jg.comp (Jg.comp Eg)) = FiniteQutritAveragedTransfer.transfer) :
    Eg.comp (Dg.comp (Jg.comp Eg)) ≠ Jg.comp Eg := by
  intro hc
  obtain ⟨hr,hp⟩ := generic_positive_root Jg Eg Dg hJ hE hD h2 hc
  exact FiniteQutritAmbientRootObstruction.ambient_positive_root_impossible _ hr hp

/-- Coordinate matrix units, on the full complex physical operator algebra. -/
def unit (i j : Q) : Mat := Matrix.single i j 1

def Pi (i : Q) : Mat := unit i i

def rhoPlus (i j : Q) : Mat :=
  (1/2 : ℂ) • (Pi i + Pi j + unit i j + unit j i)

/-- Sign convention: the state vector is e_i + i e_j. -/
def rhoI (i j : Q) : Mat :=
  (1/2 : ℂ) • (Pi i + Pi j - Complex.I • unit i j + Complex.I • unit j i)

def delta (i k : Q) : ℂ := if k = i then 1 else 0

theorem star_delta (i k : Q) : star (delta i k) = delta i k := by
  unfold delta
  split_ifs <;> simp

def probeVector (i j : Q) (z : ℂ) : Q → ℂ :=
  fun k => delta i k + z * delta j k

theorem Pi_density (i : Q) : IsDensityOperator (Pi i) := by
  have hp : Pi i = projector i.castSucc.castSucc := by
    fin_cases i <;> ext s t <;> fin_cases s <;> fin_cases t <;>
      norm_num [Pi, unit, Matrix.single, projector]
  rw [hp]
  exact FiniteQutritAmbientRootObstruction.coordinate_projector_density i

theorem unit_entry (i j s t : Q) : unit i j s t = delta i s * delta j t := by
  by_cases hs : s = i <;> by_cases ht : t = j <;>
    simp [unit, Matrix.single, delta, hs, ht, Ne.symm]

theorem rhoPlus_outer (i j : Q) :
    rhoPlus i j = (1/2 : ℂ) • Matrix.vecMulVec (probeVector i j 1) (star (probeVector i j 1)) := by
  ext s t
  change (1/2 : ℂ) * (unit i i s t + unit j j s t + unit i j s t + unit j i s t) =
    (1/2 : ℂ) * ((delta i s + 1 * delta j s) * star (delta i t + 1 * delta j t))
  simp only [unit_entry, star_add, star_mul, star_delta, star_one]
  ring

theorem rhoI_outer (i j : Q) :
    rhoI i j = (1/2 : ℂ) • Matrix.vecMulVec (probeVector i j Complex.I) (star (probeVector i j Complex.I)) := by
  ext s t
  change (1/2 : ℂ) * (unit i i s t + unit j j s t - Complex.I * unit i j s t + Complex.I * unit j i s t) =
    (1/2 : ℂ) * ((delta i s + Complex.I * delta j s) * star (delta i t + Complex.I * delta j t))
  simp only [unit_entry, star_add, star_mul, star_delta, Complex.star_def, Complex.conj_I]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem unit_trace (i j : Q) : (unit i j).trace = if i = j then 1 else 0 := by
  change (∑ k : Q, if i = k ∧ j = k then (1 : ℂ) else 0) = _
  rw [Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> norm_num <;> decide

theorem rhoPlus_density (i j : Q) (hij : i < j) : IsDensityOperator (rhoPlus i j) := by
  constructor
  · rw [rhoPlus_outer]
    exact (Matrix.posSemidef_vecMulVec_self_star _).smul (by norm_num [Complex.le_def] : (0 : ℂ) ≤ 1/2)
  · have hne := ne_of_lt hij
    simp [rhoPlus, Pi, Matrix.trace_smul, Matrix.trace_add, unit_trace, hne, Ne.symm hne]; norm_num

theorem rhoI_density (i j : Q) (hij : i < j) : IsDensityOperator (rhoI i j) := by
  constructor
  · rw [rhoI_outer]
    exact (Matrix.posSemidef_vecMulVec_self_star _).smul (by norm_num [Complex.le_def] : (0 : ℂ) ≤ 1/2)
  · have hne := ne_of_lt hij
    simp [rhoI, Pi, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_sub, unit_trace,
      hne, Ne.symm hne]; norm_num

theorem span_forward (i j : Q) : unit i j = rhoPlus i j + Complex.I • rhoI i j -
    ((1+Complex.I)/2) • (Pi i + Pi j) := by
  ext s t
  simp only [rhoPlus, rhoI, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem span_backward (i j : Q) : unit j i = rhoPlus i j - Complex.I • rhoI i j -
    ((1-Complex.I)/2) • (Pi i + Pi j) := by
  ext s t
  simp only [rhoPlus, rhoI, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring_nf
  simp [Complex.I_sq]
  ring

abbrev PairLabel := {p : Q × Q // p.1 < p.2}
abbrev ProbeLabel := Q ⊕ (PairLabel × C)

/-- Three coordinate states and two states for each of the three ordered pairs. -/
def densityProbe : ProbeLabel → Mat
  | .inl i => Pi i
  | .inr (p,a) => if a = 0 then rhoPlus p.val.1 p.val.2 else rhoI p.val.1 p.val.2

theorem nine_probes : Fintype.card ProbeLabel = 9 := by decide

theorem densityProbe_density (k : ProbeLabel) : IsDensityOperator (densityProbe k) := by
  rcases k with i | ⟨p,a⟩
  · exact Pi_density i
  · by_cases ha : a = 0
    · simpa [densityProbe, ha] using rhoPlus_density p.val.1 p.val.2 p.property
    · simpa [densityProbe, ha] using rhoI_density p.val.1 p.val.2 p.property

theorem matrix_unit_expansion (X : Mat) : X = ∑ i : Q, ∑ j : Q, X i j • unit i j := by
  ext s t
  fin_cases s <;> fin_cases t <;> simp [unit, Matrix.single, Matrix.sum_apply, Fin.sum_univ_succ]

/-- Vanishing on the nine physical probes forces vanishing on the full complex algebra. -/
theorem probes_span {M : Type*} [AddCommGroup M] [Module ℂ M] (H : Mat →ₗ[ℂ] M)
    (hz : ∀ k, H (densityProbe k) = 0) : H = 0 := by
  have hp : ∀ i, H (Pi i) = 0 := fun i => hz (.inl i)
  have hplus : ∀ i j, i < j → H (rhoPlus i j) = 0 := by
    intro i j hij
    exact hz (.inr (⟨(i,j),hij⟩,0))
  have him : ∀ i j, i < j → H (rhoI i j) = 0 := by
    intro i j hij
    simpa [densityProbe] using hz (.inr (⟨(i,j),hij⟩,1))
  have hu : ∀ i j, H (unit i j) = 0 := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · rw [span_forward, map_sub, map_add, map_smul, map_smul, map_add,
        hp, hp, hplus i j h, him i j h]
      simp
    · subst j; exact hp i
    · rw [span_backward j i, map_sub, map_sub, map_smul, map_smul, map_add,
        hp, hp, hplus j i h, him j i h]
      simp
  ext X
  conv_lhs => rw [matrix_unit_expansion X]
  simp [map_sum, hu]

theorem physical_probe_witness {M : Type*} [AddCommGroup M] [Module ℂ M]
    (H : Mat →ₗ[ℂ] M) (hH : H ≠ 0) :
    ∃ k : ProbeLabel, IsDensityOperator (densityProbe k) ∧ H (densityProbe k) ≠ 0 := by
  by_contra hn
  apply hH
  apply probes_span H
  intro k
  by_contra hk
  exact hn ⟨k,densityProbe_density k,hk⟩

theorem generic_density_defect
    (Jg : JointMat →ₗ[ℂ] JointMat) (Eg : Mat →ₗ[ℂ] JointMat) (Dg : JointMat →ₗ[ℂ] Mat)
    (hJ : ∀ X, X.PosSemidef → (Jg X).PosSemidef)
    (hE : ∀ X, X.PosSemidef → (Eg X).PosSemidef)
    (hD : ∀ X, X.PosSemidef → (Dg X).PosSemidef)
    (h2 : Dg.comp (Jg.comp (Jg.comp Eg)) = FiniteQutritAveragedTransfer.transfer) :
    ∃ k : ProbeLabel, IsDensityOperator (densityProbe k) ∧
      Eg (Dg (Jg (Eg (densityProbe k)))) ≠ Jg (Eg (densityProbe k)) := by
  have hn := generic_closure_impossible Jg Eg Dg hJ hE hD h2
  obtain ⟨k,hk,hne⟩ := physical_probe_witness
    (Eg.comp (Dg.comp (Jg.comp Eg)) - Jg.comp Eg) (sub_ne_zero.mpr hn)
  refine ⟨k,hk,?_⟩
  exact sub_ne_zero.mp hne

def noneLabel : Fin 11 := labelEquiv none

def someLabel (i : Fin 10) : Fin 11 := labelEquiv (some i)

theorem label_cases (a : Fin 11) : a = noneLabel ∨ ∃ i, a = someLabel i := by
  have h := labelEquiv.apply_symm_apply a
  cases he : labelEquiv.symm a with
  | none => left; simpa [he, noneLabel] using h.symm
  | some i => right; exact ⟨i, by simpa [he, someLabel] using h.symm⟩

theorem none_ne_some (i : Fin 10) : noneLabel ≠ someLabel i := by
  intro h
  have := labelEquiv.injective h
  contradiction

theorem someLabel_injective : Function.Injective someLabel := by
  intro i j h
  exact Option.some.inj (labelEquiv.injective h)

theorem record_branch_block (a : Fin 11) (X : SpectatorMat F) (f g : F) :
    spectatorBlock F ((localStep Joint F 11 instrument).branch Joint F 11 a X) f g =
      K a * spectatorBlock F X f g * (K a)ᴴ := by
  ext s t
  simp [record_branch, spectatorBlock, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.one_apply, apply_ite]

theorem ten_branch_block (i : Fin 10) (Y : Matrix (Q × F) (Q × F) ℂ) (f g : F) :
    FiniteQutritInvariantExamples.block F f g
      ((localStep Q F 10 FiniteQutritAveragedTransfer.instrument).branch Q F 10 i Y) =
      FiniteQutritAveragedTransfer.krausOperator i *
        FiniteQutritInvariantExamples.block F f g Y *
        (FiniteQutritAveragedTransfer.krausOperator i)ᴴ := by
  ext s t
  simp [localStep_branch, FiniteQutritAveragedTransfer.instrument,
    FiniteInstrument.branch, FiniteInstrument.lift, krausMap, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.one_apply, apply_ite,
    FiniteQutritInvariantExamples.block]

theorem none_zero_branch (Y : Matrix (Q × F) (Q × F) ℂ) :
    (localStep Joint F 11 instrument).branch Joint F 11 noneLabel
      (amplifiedPreparation F 0 Y) = amplifiedPreparation F 1 Y := by
  ext ⟨s,f⟩ ⟨t,g⟩
  have h := record_branch_block F noneLabel (amplifiedPreparation F 0 Y) f g
  rw [preparation_block] at h
  change _ = optionKraus none * embedClock 0 _ * (optionKraus none)ᴴ at h
  simp [optionKraus, embedClock, corner_sandwich, block_tensor] at h
  have hp := preparation_block F 1 Y f g
  exact congrFun (congrFun (h.trans hp.symm) s) t

theorem none_one_branch (Y : Matrix (Q × F) (Q × F) ℂ) :
    (localStep Joint F 11 instrument).branch Joint F 11 noneLabel
      (amplifiedPreparation F 1 Y) = 0 := by
  ext ⟨s,f⟩ ⟨t,g⟩
  have h := record_branch_block F noneLabel (amplifiedPreparation F 1 Y) f g
  rw [preparation_block] at h
  change _ = optionKraus none * embedClock 1 _ * (optionKraus none)ᴴ at h
  simp [optionKraus, embedClock, corner_sandwich, block_tensor] at h
  exact congrFun (congrFun h s) t

theorem some_zero_branch (i : Fin 10) (Y : Matrix (Q × F) (Q × F) ℂ) :
    (localStep Joint F 11 instrument).branch Joint F 11 (someLabel i)
      (amplifiedPreparation F 0 Y) = 0 := by
  ext ⟨s,f⟩ ⟨t,g⟩
  have h := record_branch_block F (someLabel i) (amplifiedPreparation F 0 Y) f g
  rw [preparation_block] at h
  change _ = optionKraus (some i) * embedClock 0 _ * (optionKraus (some i))ᴴ at h
  simp [optionKraus, embedClock, corner_sandwich, block_tensor] at h
  exact congrFun (congrFun h s) t

theorem some_one_branch (i : Fin 10) (Y : Matrix (Q × F) (Q × F) ℂ) :
    (localStep Joint F 11 instrument).branch Joint F 11 (someLabel i)
      (amplifiedPreparation F 1 Y) = amplifiedPreparation F 0
        ((localStep Q F 10 FiniteQutritAveragedTransfer.instrument).branch Q F 10 i Y) := by
  ext ⟨s,f⟩ ⟨t,g⟩
  have h := record_branch_block F (someLabel i) (amplifiedPreparation F 1 Y) f g
  rw [preparation_block] at h
  change _ = optionKraus (some i) * embedClock 1 _ * (optionKraus (some i))ᴴ at h
  simp [optionKraus, embedClock, corner_sandwich, block_tensor] at h
  have hp := preparation_block F 0
    ((localStep Q F 10 FiniteQutritAveragedTransfer.instrument).branch Q F 10 i Y) f g
  rw [ten_branch_block] at hp
  exact congrFun (congrFun (h.trans hp.symm) s) t

/-- Chronology: the fresh none tick precedes the next original ten-label outcome. -/
def evenRecord : (n : ℕ) → History 10 n → History 11 (2*n)
  | 0, _ => ()
  | n+1, (i,h) => (noneLabel, someLabel i, evenRecord n h)

def oddRecord : (n : ℕ) → History 10 n → History 11 (2*n+1)
  | 0, _ => (noneLabel,())
  | n+1, (i,h) => (noneLabel, someLabel i, oddRecord n h)

theorem evenRecord_injective (n : ℕ) : Function.Injective (evenRecord n) := by
  induction n with
  | zero => intro a b _; cases a; cases b; rfl
  | succ n ih =>
    rintro ⟨i,h⟩ ⟨j,k⟩ he
    have hi := someLabel_injective (congrArg (fun z => z.2.1) he)
    have ht := ih (congrArg (fun z => z.2.2) he)
    cases hi; cases ht; rfl

theorem oddRecord_injective (n : ℕ) : Function.Injective (oddRecord n) := by
  induction n with
  | zero => intro a b _; cases a; cases b; rfl
  | succ n ih =>
    rintro ⟨i,h⟩ ⟨j,k⟩ he
    have hi := someLabel_injective (congrArg (fun z => z.2.1) he)
    have ht := ih (congrArg (fun z => z.2.2) he)
    cases hi; cases ht; rfl

/-- Allowed patterns include dynamically zero leaves. -/
def evenPatternEquiv (n : ℕ) : History 10 n ≃ Set.range (evenRecord n) :=
  Equiv.ofInjective _ (evenRecord_injective n)

def oddPatternEquiv (n : ℕ) : History 10 n ≃ Set.range (oddRecord n) :=
  Equiv.ofInjective _ (oddRecord_injective n)

instance evenPatternFintype (n : ℕ) : Fintype (Set.range (evenRecord n)) :=
  Fintype.ofEquiv _ (evenPatternEquiv n)

instance oddPatternFintype (n : ℕ) : Fintype (Set.range (oddRecord n)) :=
  Fintype.ofEquiv _ (oddPatternEquiv n)

theorem even_pattern_card (n : ℕ) : Fintype.card (Set.range (evenRecord n)) = 10^n := by
  rw [← Fintype.card_congr (evenPatternEquiv n)]
  exact history_card 10 n

theorem odd_pattern_card (n : ℕ) : Fintype.card (Set.range (oddRecord n)) = 10^n := by
  rw [← Fintype.card_congr (oddPatternEquiv n)]
  exact history_card 10 n

/-- Actual chronological ten-record histories, without division or removal of zero leaves. -/
theorem permitted_even_branch (n : ℕ) (h : History 10 n) (Y : Matrix (Q × F) (Q × F) ℂ) :
    run Joint F 11 (recordTree F (2*n)) (evenRecord n h) (amplifiedPreparation F 0 Y) =
      amplifiedPreparation F 0
        (run Q F 10 (FiniteQutritAveragedTransfer.recordTree F n) h Y) := by
  induction n generalizing Y with
  | zero => rfl
  | succ n ih =>
    rcases h with ⟨i,h⟩
    change run Joint F 11 (recordTree F (2*n)) (evenRecord n h)
      ((localStep Joint F 11 instrument).branch Joint F 11 (someLabel i)
        ((localStep Joint F 11 instrument).branch Joint F 11 noneLabel
          (amplifiedPreparation F 0 Y))) = _
    rw [none_zero_branch, some_one_branch, ih]
    rfl

theorem permitted_odd_branch (n : ℕ) (h : History 10 n) (Y : Matrix (Q × F) (Q × F) ℂ) :
    run Joint F 11 (recordTree F (2*n+1)) (oddRecord n h) (amplifiedPreparation F 0 Y) =
      amplifiedPreparation F 1
        (run Q F 10 (FiniteQutritAveragedTransfer.recordTree F n) h Y) := by
  induction n generalizing Y with
  | zero => exact none_zero_branch F Y
  | succ n ih =>
    rcases h with ⟨i,h⟩
    change run Joint F 11 (recordTree F (2*n+1)) (oddRecord n h)
      ((localStep Joint F 11 instrument).branch Joint F 11 (someLabel i)
        ((localStep Joint F 11 instrument).branch Joint F 11 noneLabel
          (amplifiedPreparation F 0 Y))) = _
    rw [none_zero_branch, some_one_branch, ih]
    rfl

/-- Chronological n-tuples, with the first original label at tuple index zero. -/
def tenTupleEquiv : (n : ℕ) → History 10 n ≃ (Fin n → Fin 10)
  | 0 => {
      toFun _ := Fin.elim0
      invFun _ := ()
      left_inv h := by cases h; rfl
      right_inv f := by funext i; exact Fin.elim0 i }
  | n+1 => (Equiv.prodCongr (Equiv.refl _) (tenTupleEquiv n)).trans
      (Fin.consEquiv (fun _ => Fin 10))

def evenTuplePatternEquiv (n : ℕ) : (Fin n → Fin 10) ≃ Set.range (evenRecord n) :=
  (tenTupleEquiv n).symm.trans (evenPatternEquiv n)

def oddTuplePatternEquiv (n : ℕ) : (Fin n → Fin 10) ≃ Set.range (oddRecord n) :=
  (tenTupleEquiv n).symm.trans (oddPatternEquiv n)

/-- Outside the allowed pattern the actual unnormalized branch is zero. -/
theorem forbidden_even_branch (n : ℕ) (h : History 11 (2*n))
    (hn : h ∉ Set.range (evenRecord n)) (Y : Matrix (Q × F) (Q × F) ℂ) :
    run Joint F 11 (recordTree F (2*n)) h (amplifiedPreparation F 0 Y) = 0 := by
  induction n generalizing Y with
  | zero => exact False.elim (hn ⟨(),by cases h; rfl⟩)
  | succ n ih =>
    rcases h with ⟨a,b,h⟩
    rcases label_cases a with rfl | ⟨i,rfl⟩
    · change run Joint F 11 (recordTree F (2*n)) h
        ((localStep Joint F 11 instrument).branch Joint F 11 b
          ((localStep Joint F 11 instrument).branch Joint F 11 noneLabel
            (amplifiedPreparation F 0 Y))) = 0
      rw [none_zero_branch]
      rcases label_cases b with rfl | ⟨i,rfl⟩
      · rw [none_one_branch, run_zero]
      · rw [some_one_branch]
        apply ih
        rintro ⟨w,hw⟩
        apply hn
        exact ⟨(i,w),by simp only [evenRecord, hw]⟩
    · change run Joint F 11 (recordTree F (2*n+1)) (b,h)
        ((localStep Joint F 11 instrument).branch Joint F 11 (someLabel i)
          (amplifiedPreparation F 0 Y)) = 0
      rw [some_zero_branch, run_zero]

theorem forbidden_odd_branch (n : ℕ) (h : History 11 (2*n+1))
    (hn : h ∉ Set.range (oddRecord n)) (Y : Matrix (Q × F) (Q × F) ℂ) :
    run Joint F 11 (recordTree F (2*n+1)) h (amplifiedPreparation F 0 Y) = 0 := by
  induction n generalizing Y with
  | zero =>
    rcases h with ⟨a,h⟩
    cases h
    rcases label_cases a with rfl | ⟨i,rfl⟩
    · exact False.elim (hn ⟨(),rfl⟩)
    · exact some_zero_branch F i Y
  | succ n ih =>
    rcases h with ⟨a,b,h⟩
    rcases label_cases a with rfl | ⟨i,rfl⟩
    · change run Joint F 11 (recordTree F (2*n+1)) h
        ((localStep Joint F 11 instrument).branch Joint F 11 b
          ((localStep Joint F 11 instrument).branch Joint F 11 noneLabel
            (amplifiedPreparation F 0 Y))) = 0
      rw [none_zero_branch]
      rcases label_cases b with rfl | ⟨i,rfl⟩
      · rw [none_one_branch, run_zero]
      · rw [some_one_branch]
        apply ih
        rintro ⟨w,hw⟩
        apply hn
        exact ⟨(i,w),by simp only [oddRecord, hw]⟩
    · change run Joint F 11 (recordTree F (2*n+2)) (b,h)
        ((localStep Joint F 11 instrument).branch Joint F 11 (someLabel i)
          (amplifiedPreparation F 0 Y)) = 0
      rw [some_zero_branch, run_zero]

/-- Later operators multiply on the left of the earlier operators. -/
def tenWord : (n : ℕ) → History 10 n → Mat
  | 0, _ => 1
  | n+1, (i,h) => tenWord n h * FiniteQutritAveragedTransfer.krausOperator i

theorem ten_history_word (n : ℕ) (h : History 10 n) (Y : Matrix (Q × F) (Q × F) ℂ) :
    run Q F 10 (FiniteQutritAveragedTransfer.recordTree F n) h Y =
      (tenWord n h ⊗ₖ (1 : Matrix F F ℂ)) * Y * (tenWord n h ⊗ₖ (1 : Matrix F F ℂ))ᴴ := by
  induction n generalizing Y with
  | zero => simp [FiniteQutritAveragedTransfer.recordTree, run, tenWord]
  | succ n ih =>
    rcases h with ⟨i,h⟩
    change run Q F 10 (FiniteQutritAveragedTransfer.recordTree F n) h
      ((localStep Q F 10 FiniteQutritAveragedTransfer.instrument).branch Q F 10 i Y) = _
    rw [ih]
    have hb : (localStep Q F 10 FiniteQutritAveragedTransfer.instrument).branch Q F 10 i Y =
        (FiniteQutritAveragedTransfer.krausOperator i ⊗ₖ (1 : Matrix F F ℂ)) * Y *
          (FiniteQutritAveragedTransfer.krausOperator i ⊗ₖ (1 : Matrix F F ℂ))ᴴ := by
      simp [localStep_branch, FiniteQutritAveragedTransfer.instrument,
        FiniteInstrument.branch, FiniteInstrument.lift, krausMap]
    rw [hb]
    simp only [tenWord]
    have hk : (tenWord n h * FiniteQutritAveragedTransfer.krausOperator i) ⊗ₖ (1 : Matrix F F ℂ) =
        (tenWord n h ⊗ₖ (1 : Matrix F F ℂ)) *
          (FiniteQutritAveragedTransfer.krausOperator i ⊗ₖ (1 : Matrix F F ℂ)) := by
      simpa using Matrix.mul_kronecker_mul (tenWord n h)
        (FiniteQutritAveragedTransfer.krausOperator i) (1 : Matrix F F ℂ) (1 : Matrix F F ℂ)
    rw [hk, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]

theorem permitted_even_word (n : ℕ) (h : History 10 n) (Y : Matrix (Q × F) (Q × F) ℂ) :
    run Joint F 11 (recordTree F (2*n)) (evenRecord n h) (amplifiedPreparation F 0 Y) =
      amplifiedPreparation F 0
        ((tenWord n h ⊗ₖ (1 : Matrix F F ℂ)) * Y * (tenWord n h ⊗ₖ (1 : Matrix F F ℂ))ᴴ) := by
  rw [permitted_even_branch, ten_history_word]

theorem permitted_odd_word (n : ℕ) (h : History 10 n) (Y : Matrix (Q × F) (Q × F) ℂ) :
    run Joint F 11 (recordTree F (2*n+1)) (oddRecord n h) (amplifiedPreparation F 0 Y) =
      amplifiedPreparation F 1
        ((tenWord n h ⊗ₖ (1 : Matrix F F ℂ)) * Y * (tenWord n h ⊗ₖ (1 : Matrix F F ℂ))ᴴ) := by
  rw [permitted_odd_branch, ten_history_word]

theorem label_none_value : labelEquiv none = 0 := finSuccEquiv_symm_none

theorem label_some_value (i : Fin 10) : labelEquiv (some i) = i.succ :=
  finSuccEquiv_symm_some i

theorem J_offdiagonal (X : JointMat) (a b : C) (hab : a ≠ b) : block (J X) a b = 0 := by
  rw [J_action]
  have hblock : ∀ Y Z : JointMat, block (Y+Z) a b = block Y a b + block Z a b := by
    intro Y Z; rfl
  rw [hblock, block_tensor, block_tensor]
  fin_cases a <;> fin_cases b <;> simp_all

theorem zero_depth (X : JointMat) : jointIterate 0 X = X := rfl

theorem DE0 : D.comp E0 = LinearMap.id := by
  ext X s t
  exact congrFun (congrFun (D_embed 0 X) s) t

theorem quotient_physical_even (n : ℕ)
    {q : FiniteQutritInvariantReconstruction.FeatureSpace}
    (hq : q ∈ FiniteQutritInvariantReconstruction.density) :
    IsDensityOperator (jointIterate (2*n) (E0 (FiniteQutritInvariantReconstruction.U q))) ∧
      clockMarginal (jointIterate (2*n) (E0 (FiniteQutritInvariantReconstruction.U q))) = P 0 :=
  encoded_density_even n ⟨hq.1,hq.2⟩

theorem quotient_physical_odd (n : ℕ)
    {q : FiniteQutritInvariantReconstruction.FeatureSpace}
    (hq : q ∈ FiniteQutritInvariantReconstruction.density) :
    IsDensityOperator (jointIterate (2*n+1) (E0 (FiniteQutritInvariantReconstruction.U q))) ∧
      clockMarginal (jointIterate (2*n+1) (E0 (FiniteQutritInvariantReconstruction.U q))) = P 1 :=
  encoded_density_odd n ⟨hq.1,hq.2⟩

theorem amplified_product (X : JointMat) (σ : Matrix F F ℂ) :
    amplified F (X ⊗ₖ σ) = J X ⊗ₖ σ := by
  ext ⟨s,f⟩ ⟨t,g⟩
  have h := amplified_block F (X ⊗ₖ σ) f g
  have hb : spectatorBlock F (X ⊗ₖ σ) f g = σ f g • X := by
    ext a b; simp [spectatorBlock, mul_comm]
  rw [hb, map_smul] at h
  exact (congrFun (congrFun h s) t).trans (by simp [mul_comm])

theorem amplified_iterate_product (n : ℕ) (X : JointMat) (σ : Matrix F F ℂ) :
    amplifiedJointIterate F n (X ⊗ₖ σ) = jointIterate n X ⊗ₖ σ := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih =>
    change amplifiedJointIterate F n (amplified F (X ⊗ₖ σ)) = _
    rw [amplified_product, ih]
    rfl

theorem all_records_joint (n : ℕ) (X : JointMat) :
    (∑ h, run Joint Unit 11 (recordTree Unit n) h (X ⊗ₖ (1 : Matrix Unit Unit ℂ))) =
      jointIterate n X ⊗ₖ (1 : Matrix Unit Unit ℂ) := by
  rw [all_records_sum, amplified_iterate_product]

theorem preparation_density (a : C) {Y : Matrix (Q × F) (Q × F) ℂ}
    (hY : IsDensityOperator Y) : IsDensityOperator (amplifiedPreparation F a Y) :=
  ⟨preparation_CP F a hY.1, (preparation_trace F a Y).trans hY.2⟩

theorem reduction_density {X : SpectatorMat F} (hX : IsDensityOperator X) :
    IsDensityOperator (amplifiedReduction F X) :=
  ⟨reduction_CP F hX.1, (reduction_trace F X).trans hX.2⟩

theorem amplified_iterate_density (n : ℕ) {X : SpectatorMat F} (hX : IsDensityOperator X) :
    IsDensityOperator (amplifiedJointIterate F n X) := by
  induction n generalizing X with
  | zero => exact hX
  | succ n ih => exact ih (amplified_density F hX)

theorem reset_amplified_normalized : IsKrausChannel (fun a => L a ⊗ₖ (1 : Matrix F F ℂ)) := by
  unfold IsKrausChannel
  simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  rw [sum_kronOne_general, L_normalized, Matrix.one_kronecker_one]

theorem reset_amplified_action (X : SpectatorMat F) :
    krausMap (fun a => L a ⊗ₖ (1 : Matrix F F ℂ)) X =
      amplifiedPreparation F 0 (amplifiedReduction F X) := by
  ext ⟨⟨s,c⟩,f⟩ ⟨⟨t,d⟩,g⟩
  rw [preparation_entry, reduction_entry]
  fin_cases c <;> fin_cases d <;>
    simp [krausMap, L, e, P, Matrix.single, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.one_apply, apply_ite, Matrix.sum_apply]

theorem experiments_physical :
    IsDensityOperator (D (J (J (E0 rho0)))) ∧
      IsDensityOperator (D (J (resetClock (J (E0 rho0))))) := by
  constructor
  · exact D_density (J_density (J_density encoded_rho0_density))
  · exact D_density (J_density (reset_density (J_density encoded_rho0_density)))

/-- The actual reduced maps fail the homogeneous system composition law. -/
theorem reduced_not_semigroup :
    D.comp (jointIterate 2 |>.comp E0) ≠
      (D.comp (J.comp E0)).comp (D.comp (J.comp E0)) := by
  intro h
  have hh := LinearMap.congr_fun h rho0
  change D (J (J (E0 rho0))) = D (J (E0 (D (J (E0 rho0))))) at hh
  have hr : D (J (E0 (D (J (E0 rho0))))) = rho0 := by
    rw [J_embed_zero, D_embed, J_embed_zero, D_embed]
  have he := congrArg event0 (hh.trans hr)
  rw [retained_event] at he
  have hright : event0 rho0 = 1 := by
    simpa only [reset_two_ticks] using reset_event
  rw [hright] at he
  norm_num at he

end SKEFTHawking.QuantumNetwork.FiniteQutritRetainedClock
