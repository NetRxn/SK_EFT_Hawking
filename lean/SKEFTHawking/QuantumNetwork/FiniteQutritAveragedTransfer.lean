import SKEFTHawking.QuantumNetwork.FiniteQutritInvariantExamples

/-!
# Uniformly discarded original setting and outcome

The Kraus alternatives carry both the independent uniform setting and its
binary outcome. Discarding all ten records gives the actual averaged map.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteQutritAveragedTransfer
open Matrix FiniteInterventionProcess FiniteAdaptiveKrausRealization
open FiniteQutritPhysicalMemory FiniteQutritInvariantCarrier
open FiniteQutritInvariantReconstruction
open scoped BigOperators ComplexOrder Kronecker InnerProductSpace

private theorem vec6_last {α : Type*} (a b c d e f : α) :
    ![a,b,c,d,e,f] (5 : Fin 6) = f := rfl

/-- Discard the original binary outcome at a fixed setting. -/
def pinching (j : Setting) : Mat →ₗ[ℂ] Mat := systemBranch j 0 + systemBranch j 1

/-- The actual uniform setting average, complex-linear on every matrix. -/
def transfer : Mat →ₗ[ℂ] Mat := (1/5 : ℂ) • ∑ j : Setting, pinching j

theorem pinching_apply (j : Setting) (X : Mat) :
    pinching j X = projector j * X * projector j +
      (1-projector j) * X * (1-projector j) := by
  simp [pinching, systemBranch, outcomeOperator]

theorem transfer_apply (X : Mat) :
    transfer X = (1/5 : ℂ) • ∑ j : Setting, pinching j X := by
  simp [transfer, LinearMap.sum_apply]

def amplitude : ℂ := (Real.sqrt 5 : ℂ)⁻¹

theorem amplitude_real : star amplitude = amplitude := by simp [amplitude]

theorem amplitude_square : amplitude * amplitude = 1/5 := by
  have hs : (Real.sqrt 5 : ℂ) * (Real.sqrt 5 : ℂ) = 5 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 5)
  unfold amplitude
  rw [← mul_inv, hs]
  norm_num

/-- The record is the ordered pair (fresh setting, original outcome). -/
def krausOperator (k : Fin 10) : Mat :=
  amplitude • outcomeOperator ((finProdFinEquiv (m := 5) (n := 2)).symm k).1 ((finProdFinEquiv (m := 5) (n := 2)).symm k).2

theorem kraus_pair (j : Setting) (a : Fin 2) :
    krausOperator (finProdFinEquiv (j,a)) = amplitude • outcomeOperator j a := by
  simp [krausOperator]

theorem scaled_sandwich (A X : Mat) :
    (amplitude • A) * X * (amplitude • A)ᴴ = (1/5 : ℂ) • (A * X * Aᴴ) := by
  simp only [Matrix.conjTranspose_smul, amplitude_real, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, amplitude_square]

theorem scaled_adjoint_product (A : Mat) :
    (amplitude • A)ᴴ * (amplitude • A) = (1/5 : ℂ) • (Aᴴ * A) := by
  simp only [Matrix.conjTranspose_smul, amplitude_real, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, amplitude_square]

theorem kraus_normalized : IsKrausChannel krausOperator := by
  unfold IsKrausChannel
  rw [← (finProdFinEquiv (m := 5) (n := 2)).sum_comp (fun k => (krausOperator k)ᴴ * krausOperator k)]
  simp only [Fintype.sum_prod_type, kraus_pair, scaled_adjoint_product,
    outcomeOperator_hermitian, outcomeOperator_idempotent, Fin.sum_univ_two,
    ← smul_add]
  simp only [outcomeOperator, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false]
  simp
  ext i j
  simp [Matrix.ofNat_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]

/-- Every one of the ten alternatives is retained by this normalized instrument. -/
def instrument : FiniteInstrument Q 10 where
  count := 1
  operators a _ := krausOperator a
  normalized := by simpa [IsKrausChannel] using kraus_normalized

/-- The one-outcome channel after both records have been discarded. -/
def channel : FiniteInstrument Q 1 := FiniteInstrument.singleton krausOperator kraus_normalized

theorem kraus_action (X : Mat) : krausMap krausOperator X = transfer X := by
  unfold krausMap
  rw [← (finProdFinEquiv (m := 5) (n := 2)).sum_comp (fun k => krausOperator k * X * (krausOperator k)ᴴ)]
  simp only [Fintype.sum_prod_type, kraus_pair, scaled_sandwich,
    outcomeOperator_hermitian, Fin.sum_univ_two, ← smul_add, ← Finset.smul_sum]
  rw [transfer_apply]
  rfl

theorem channel_action (X : Mat) : channel.branch 0 X = transfer X := kraus_action X

theorem record_action (j : Setting) (a : Fin 2) (X : Mat) :
    instrument.branch (finProdFinEquiv (j,a)) X = (1/5 : ℂ) • systemBranch j a X := by
  simp only [instrument, FiniteInstrument.branch, krausMap, Finset.univ_unique,
    Finset.sum_singleton, kraus_pair, scaled_sandwich, outcomeOperator_hermitian]
  rfl

theorem discard_records (X : Mat) : (∑ a, instrument.branch a X) = transfer X := by
  simpa [instrument, FiniteInstrument.branch, krausMap] using kraus_action X

theorem transfer_trace (X : Mat) : (transfer X).trace = X.trace := by
  have h := channel.sum_trace X
  simpa only [Fin.sum_univ_one, channel_action] using h

theorem pinching_one (j : Setting) : pinching j 1 = 1 := by
  rw [pinching_apply]
  simp only [Matrix.mul_one, outcomeOperator_idempotent]
  have hc := outcomeOperator_idempotent j 1
  change (1-projector j) * (1-projector j) = 1-projector j at hc
  rw [projector_idempotent, hc]
  abel

theorem transfer_one : transfer 1 = 1 := by
  rw [transfer_apply]
  simp only [pinching_one]
  ext i j
  simp [Matrix.ofNat_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]

theorem transfer_positive {X : Mat} (hX : X.PosSemidef) : (transfer X).PosSemidef := by
  rw [← kraus_action]
  exact krausMap_posSemidef _ hX

theorem transfer_invariant {X : Mat} (hX : X ∈ symmetricCarrier) :
    transfer X ∈ symmetricCarrier := by
  rw [transfer_apply]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro j _
  exact (branch_invariant j 0 hX).add (branch_invariant j 1 hX)

def restricted : symmetricCarrier →ₗ[ℂ] symmetricCarrier where
  toFun X := ⟨transfer X, transfer_invariant X.property⟩
  map_add' X Y := Subtype.ext (transfer.map_add X Y)
  map_smul' c X := Subtype.ext (transfer.map_smul c X)

/-- Conjugation through the existing genuine kernel quotient. -/
def quotientTransfer : FeatureSpace →ₗ[ℂ] FeatureSpace :=
  U.symm.toLinearMap.comp (restricted.comp U.toLinearMap)

theorem U_transfer (q : FeatureSpace) : (U (quotientTransfer q) : Mat) = transfer (U q) := by
  change (U (U.symm (restricted (U q))) : Mat) = _
  rw [U.apply_symm_apply]
  rfl

theorem quotient_trace (q : FeatureSpace) :
    FiniteQutritInvariantReconstruction.trace (quotientTransfer q) =
      FiniteQutritInvariantReconstruction.trace q := by
  change (U (quotientTransfer q) : Mat).trace = _
  rw [U_transfer, transfer_trace]
  rfl

theorem quotient_cone {q : FeatureSpace} (hq : q ∈ cone) : quotientTransfer q ∈ cone := by
  change (U (quotientTransfer q) : Mat).PosSemidef
  rw [U_transfer]
  exact transfer_positive hq


/-- Actual weighted Hilbert-Schmidt pairing, with no coordinate norm convention. -/
def pairing (X Y : Mat) : ℂ := ⟪operatorEmbedding X, operatorEmbedding Y⟫_ℂ

def hsNorm (X : Mat) : ℝ := ‖operatorEmbedding X‖

theorem pairing_trace (X Y : Mat) : pairing X Y = (Xᴴ * Y).trace / 3 :=
  FiniteQutritPhysicalMemoryExamples.operatorEmbedding_inner X Y

theorem pairing_self (X : Mat) : pairing X X = (hsNorm X ^ 2 : ℝ) :=
  by simpa [pairing, hsNorm] using (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (operatorEmbedding X))

theorem hsNorm_nonneg (X : Mat) : 0 ≤ hsNorm X := norm_nonneg _

theorem sandwich_pairing (A X Y : Mat) (hA : Aᴴ = A) :
    pairing (A * X * A) Y = pairing X (A * Y * A) := by
  simp only [pairing_trace, Matrix.conjTranspose_mul, hA]
  congr 1
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm A (Xᴴ * A * Y)

theorem pinching_selfadjoint (j : Setting) (X Y : Mat) :
    pairing (pinching j X) Y = pairing X (pinching j Y) := by
  simp only [pinching_apply, pairing, map_add, inner_add_left, inner_add_right]
  exact congrArg₂ (· + ·)
    (sandwich_pairing (projector j) X Y (projector_hermitian j).eq)
    (sandwich_pairing (1-projector j) X Y
      (Matrix.isHermitian_one.sub (projector_hermitian j)).eq)

private theorem sandwich_comp (A B X : Mat) :
    A * (B * X * B) * A = (A * B) * X * (B * A) := by simp only [Matrix.mul_assoc]

theorem pinching_idempotent (j : Setting) (X : Mat) :
    pinching j (pinching j X) = pinching j X := by
  have hp := projector_idempotent j
  have hq : (1-projector j) * (1-projector j) = 1-projector j :=
    outcomeOperator_idempotent j 1
  have hpq : projector j * (1-projector j) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hp, sub_self]
  have hqp : (1-projector j) * projector j = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hp, sub_self]
  simp only [pinching_apply, Matrix.mul_add, Matrix.add_mul, sandwich_comp,
    hp, hq, hpq, hqp, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]

theorem pinching_energy (j : Setting) (X : Mat) :
    pairing X (pinching j X) = (hsNorm (pinching j X) ^ 2 : ℝ) := by
  rw [← pinching_idempotent j X, ← pinching_selfadjoint, pinching_idempotent]
  exact pairing_self _

theorem transfer_selfadjoint (X Y : Mat) : pairing (transfer X) Y = pairing X (transfer Y) := by
  simp only [transfer_apply, pairing, map_smul, map_sum, inner_smul_left,
    inner_smul_right, sum_inner, inner_sum]
  have hr : star (1/5 : ℂ) = 1/5 := by norm_num
  simp only [map_div₀, map_one, map_ofNat]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact pinching_selfadjoint j X Y

/-- Hilbert positivity is derived separately from ambient Kraus positivity. -/
theorem transfer_energy (X : Mat) :
    pairing X (transfer X) = ((1/5 : ℝ) * ∑ j : Setting, hsNorm (pinching j X)^2 : ℝ) := by
  simp only [transfer_apply, pairing, map_smul, map_sum, inner_smul_right, inner_sum]
  change (1/5 : ℂ) * ∑ j : Setting, pairing X (pinching j X) = _
  simp_rw [pinching_energy]
  push_cast
  rfl

theorem pinching_pythagoras (j : Setting) (X : Mat) :
    hsNorm (X-pinching j X)^2 + hsNorm (pinching j X)^2 = hsNorm X^2 := by
  have h := pairing_self (X-pinching j X)
  have he := pinching_energy j X
  have ha := pinching_selfadjoint j X X
  simp only [pairing, map_sub, inner_sub_left, inner_sub_right] at h
  change pairing X X - pairing (pinching j X) X -
    (pairing X (pinching j X) - pairing (pinching j X) (pinching j X)) = _ at h
  rw [pairing_self, he, ha, he, pairing_self] at h
  have hr := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.ofReal_re] at hr
  linarith

theorem hilbert_positive_contraction (X : Mat) :
    0 ≤ (pairing X (transfer X)).re ∧
      (pairing X (transfer X)).re ≤ hsNorm X^2 := by
  rw [transfer_energy, Complex.ofReal_re]
  constructor
  · exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  · have h : (∑ j : Setting, hsNorm (pinching j X)^2) ≤ ∑ _j : Setting, hsNorm X^2 := by
      apply Finset.sum_le_sum
      intro j _
      have hp := pinching_pythagoras j X
      nlinarith [sq_nonneg (hsNorm (X-pinching j X))]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    norm_num at h ⊢
    linarith

def iterate : ℕ → Mat →ₗ[ℂ] Mat
  | 0 => LinearMap.id
  | n+1 => (iterate n).comp transfer

theorem iterate_eq_function (n : ℕ) (X : Mat) : iterate n X = (transfer : Mat → Mat)^[n] X := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih => exact ih (transfer X)

theorem iterate_trace (n : ℕ) (X : Mat) : (iterate n X).trace = X.trace := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih => exact (ih (transfer X)).trans (transfer_trace X)

theorem iterate_invariant (n : ℕ) {X : Mat} (hX : X ∈ symmetricCarrier) :
    iterate n X ∈ symmetricCarrier := by
  induction n generalizing X with
  | zero => exact hX
  | succ n ih => exact ih (transfer_invariant hX)

theorem iterate_positive (n : ℕ) {X : Mat} (hX : X.PosSemidef) :
    (iterate n X).PosSemidef := by
  induction n generalizing X with
  | zero => exact hX
  | succ n ih => exact ih (transfer_positive hX)

def quotientIterate : ℕ → FeatureSpace →ₗ[ℂ] FeatureSpace
  | 0 => LinearMap.id
  | n+1 => (quotientIterate n).comp quotientTransfer

theorem U_iterate (n : ℕ) (q : FeatureSpace) :
    (U (quotientIterate n q) : Mat) = iterate n (U q) := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    change (U (quotientIterate n (quotientTransfer q)) : Mat) = iterate n (transfer (U q))
    rw [ih, U_transfer]

theorem quotient_initial_fixed : quotientTransfer initial = initial := by
  apply U.injective
  apply Subtype.ext
  rw [U_transfer, U_initial]
  have hr : rho = (1/3 : ℂ) • (1 : Mat) := by ext a b; simp [rho]
  rw [hr, map_smul, transfer_one]

variable (E : Type*) [Fintype E] [DecidableEq E]

def amplified : Matrix (Q × E) (Q × E) ℂ →ₗ[ℂ] Matrix (Q × E) (Q × E) ℂ where
  toFun := krausMap (fun k => krausOperator k ⊗ₖ (1 : Matrix E E ℂ))
  map_add' := krausMap_add _
  map_smul' := krausMap_smul _

/-- All correlated positive ambient inputs, with no carrier premise. -/
theorem amplified_positive {X : Matrix (Q × E) (Q × E) ℂ} (hX : X.PosSemidef) :
    (amplified E X).PosSemidef := krausMap_posSemidef _ hX

theorem amplified_block (X : Matrix (Q × E) (Q × E) ℂ) (e f : E) :
    FiniteQutritInvariantExamples.block E e f (amplified E X) =
      transfer (FiniteQutritInvariantExamples.block E e f X) := by
  change FiniteQutritInvariantExamples.block E e f (krausMap _ X) = _
  rw [FiniteQutritInvariantExamples.amplified_kraus_block, kraus_action]

theorem amplified_invariant {X : Matrix (Q × E) (Q × E) ℂ}
    (hX : X ∈ FiniteQutritInvariantExamples.matrixCarrier E) :
    amplified E X ∈ FiniteQutritInvariantExamples.matrixCarrier E := by
  intro e f
  rw [amplified_block]
  exact transfer_invariant (hX e f)

theorem amplified_product (X : Mat) (σ : Matrix E E ℂ) :
    amplified E (X ⊗ₖ σ) = transfer X ⊗ₖ σ := by
  change krausMap _ _ = _
  rw [FiniteQutritInvariantExamples.amplified_channel_product, kraus_action]

def amplifiedIterate : ℕ → Matrix (Q × E) (Q × E) ℂ →ₗ[ℂ] Matrix (Q × E) (Q × E) ℂ
  | 0 => LinearMap.id
  | n+1 => (amplifiedIterate n).comp (amplified E)

/-- Every fresh setting/outcome record is retained at every intermediate node. -/
def recordTree : (n : ℕ) → Tree Q E 10 n
  | 0 => .done
  | n+1 => .node (localStep Q E 10 instrument) (fun _ => recordTree n)

theorem record_branch_sum (X : Matrix (Q × E) (Q × E) ℂ) :
    (∑ a, (localStep Q E 10 instrument).branch Q E 10 a X) = amplified E X := by
  simp only [localStep_branch, FiniteInstrument.branch, FiniteInstrument.lift, instrument,
    krausMap, Finset.univ_unique, Finset.sum_singleton]
  rfl

/-- Exact all-n coarse-graining, including zero and impossible leaves. -/
theorem discarded_history (n : ℕ) (X : Matrix (Q × E) (Q × E) ℂ) :
    (∑ h, run Q E 10 (recordTree E n) h X) = amplifiedIterate E n X := by
  induction n generalizing X with
  | zero =>
    change (∑ _ : Unit, X) = X
    simp
  | succ n ih =>
    change (∑ h : Fin 10 × History 10 n,
      run Q E 10 (recordTree E n) h.2
        ((localStep Q E 10 instrument).branch Q E 10 h.1 X)) = _
    rw [Fintype.sum_prod_type]
    simp_rw [ih]
    rw [← map_sum, record_branch_sum]
    rfl

theorem amplified_iterate_product (n : ℕ) (X : Mat) (σ : Matrix E E ℂ) :
    amplifiedIterate E n (X ⊗ₖ σ) = iterate n X ⊗ₖ σ := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih =>
    change amplifiedIterate E n (amplified E (X ⊗ₖ σ)) = iterate n (transfer X) ⊗ₖ σ
    rw [amplified_product, ih]

theorem discarded_history_system (n : ℕ) (X : Mat) :
    (∑ h, run Q Unit 10 (recordTree Unit n) h (joint X)) = joint (iterate n X) := by
  rw [discarded_history]
  exact amplified_iterate_product Unit n X 1

theorem all_records_normalized (n : ℕ) {X : Matrix (Q × E) (Q × E) ℂ}
    (hX : IsDensityOperator X) :
    (∀ h, 0 ≤ weight Q E 10 (recordTree E n) h X) ∧
      (∑ h, weight Q E 10 (recordTree E n) h X) = 1 :=
  FiniteInterventionProcess.normalized_weights Q E 10 _ hX

theorem all_records_card (n : ℕ) : Fintype.card (History 10 n) = 10^n := history_card 10 n

end SKEFTHawking.QuantumNetwork.FiniteQutritAveragedTransfer
