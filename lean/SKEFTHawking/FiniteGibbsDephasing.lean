import SKEFTHawking.FinitePositiveKernelChannel
import SKEFTHawking.QuantumNetwork.NamedChannels
import SKEFTHawking.LindbladCPSemigroup

/-! Concrete Gibbs dephasing and its actual Lindblad exponential.
The observable and state actions agree for these Hermitian Kraus operators. -/
noncomputable section
open Matrix
open scoped ComplexOrder InnerProductSpace
namespace SKEFTHawking.FinitePositiveKernel.GibbsDephasing
open QuantumNetwork QuantumNetwork.FiniteGibbsClock OpenSystems

theorem dephasing_kraus_hermitian (γ : ℝ) (i : Fin 2) :
    (dephasingKraus γ i)ᴴ = dephasingKraus γ i := by
  fin_cases i <;> simp [dephasingKraus, Matrix.conjTranspose_smul, pauliZ_conjTranspose]

/-- The Heisenberg Kraus sum agrees with the existing state channel. -/
theorem dephasing_heisenberg (γ : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    (∑ i, (dephasingKraus γ i)ᴴ * X * dephasingKraus γ i) =
      krausMap (dephasingKraus γ) X := by
  simp only [krausMap, dephasing_kraus_hermitian]

theorem dephasing_action {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1)
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    krausMap (dephasingKraus γ) X = ((1-γ : ℝ) : ℂ) • X +
      (γ : ℂ) • (pauliZ * X * pauliZ) := by
  simp only [krausMap, Fin.sum_univ_two, dephasingKraus, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, pauliZ_conjTranspose,
    smul_mul_assoc, mul_smul_comm, smul_smul, one_mul, mul_one]
  simp [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith : 0 ≤ 1-γ), Real.mul_self_sqrt h0]

theorem dephasing_entry {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1)
    (X : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    krausMap (dephasingKraus γ) X i j =
      (if i = j then 1 else (1-2*γ : ℂ)) * X i j := by
  rw [dephasing_action h0 h1]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    pauliZ, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> norm_num <;> ring

theorem dephasing_diagonal {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1)
    (d : Fin 2 → ℂ) : krausMap (dephasingKraus γ) (diagonal d) = diagonal d := by
  ext i j
  rw [dephasing_entry h0 h1]
  by_cases h : i = j <;> simp [h]

theorem gibbs_twoLevel_diagonal (Δ β : ℝ) :
    ∃ d : Fin 2 → ℂ, gibbs (twoLevel Δ) β = diagonal d := by
  unfold gibbs boltzmann twoLevel
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal, ← Matrix.diagonal_smul]
  exact ⟨_, rfl⟩

theorem dephasing_fixed_gibbs {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) (Δ β : ℝ) :
    krausMap (dephasingKraus γ) (gibbs (twoLevel Δ) β) = gibbs (twoLevel Δ) β := by
  obtain ⟨d, hd⟩ := gibbs_twoLevel_diagonal Δ β
  rw [hd, dephasing_diagonal h0 h1]

theorem dephasing_weighted_symmetry_diagonal {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1)
    (d : Fin 2 → ℂ) (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    (Y * diagonal d * (krausMap (dephasingKraus γ) X)ᴴ).trace =
      (krausMap (dephasingKraus γ) Y * diagonal d * Xᴴ).trace := by
  simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
    dephasing_entry h0 h1, Matrix.diagonal_apply]
  simp only [map_ofNat]
  ring

theorem dephasing_weighted_symmetry {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1)
    (Δ β : ℝ) (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    (Y * gibbs (twoLevel Δ) β * (krausMap (dephasingKraus γ) X)ᴴ).trace =
      (krausMap (dephasingKraus γ) Y * gibbs (twoLevel Δ) β * Xᴴ).trace := by
  obtain ⟨d, hd⟩ := gibbs_twoLevel_diagonal Δ β
  rw [hd]
  exact dephasing_weighted_symmetry_diagonal h0 h1 d X Y

theorem dephasing_E01 {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    krausMap (dephasingKraus γ) E01 = (1-2*γ : ℂ) • E01 := by
  ext i j
  rw [dephasing_entry h0 h1]
  fin_cases i <;> fin_cases j <;> simp [E01]

/-- The coherence multiplier is exact at every discrete iterate. -/
theorem dephasing_iterate_E01 {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) (k : ℕ) :
    (krausMap (dephasingKraus γ))^[k] E01 = (1-2*γ : ℂ)^k • E01 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, krausMap_smul, dephasing_E01 h0 h1,
      smul_smul, pow_succ]

/-- A faithful Gibbs coherence is a nonzero witness against Hilbert positivity at γ=1. -/
theorem dephasing_one_negative_pairing (Δ β : ℝ) :
    (⟪GibbsObservable.observable (gibbs_posDef (twoLevel_hermitian Δ) β).posSemidef E01,
      GibbsObservable.observable (gibbs_posDef (twoLevel_hermitian Δ) β).posSemidef
        (krausMap (dephasingKraus 1) E01)⟫_ℂ).re < 0 := by
  rw [dephasing_E01 (by norm_num) (by norm_num), GibbsObservable.observable_smul,
    inner_smul_right]
  have hp := norm_pos_iff.mpr (GibbsObservable.Clock.twoLevel_observable_nonzero Δ β)
  norm_num [← Complex.ofReal_pow]
  positivity

/-- One Hermitian dephasing jump, independent of the Gibbs Hamiltonian. -/
def dephasingJump (a : ℝ) : Fin 1 → Matrix (Fin 2) (Fin 2) ℂ :=
  fun _ => (Real.sqrt a : ℂ) • pauliZ

/-- The existing GKSL generator reduces to a genuine dissipative dephasing action. -/
theorem dephasing_generator {a : ℝ} (ha : 0 ≤ a) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    lindbladGenerator 0 (dephasingJump a) X = (a : ℂ) • (pauliZ * X * pauliZ - X) := by
  simp only [lindbladGenerator, LinearMap.add_apply, lindbladHamPart_apply,
    lindbladJump_apply, lindbladAnticommPart_apply, Fin.sum_univ_one, dephasingJump,
    Matrix.conjTranspose_smul, pauliZ_conjTranspose, zero_mul, mul_zero, sub_self,
    smul_zero, zero_add, smul_mul_assoc, mul_smul_comm, smul_smul, pauliZ_mul_self,
    one_mul, mul_one]
  simp [← Complex.ofReal_mul, Real.mul_self_sqrt ha]
  module

theorem dephasing_generator_entry {a : ℝ} (ha : 0 ≤ a)
    (X : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    lindbladGenerator 0 (dephasingJump a) X i j =
      (if i = j then 0 else (-2*a : ℂ)) * X i j := by
  rw [dephasing_generator ha]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, Matrix.mul_apply,
    pauliZ, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> norm_num <;> ring

/-- The actual vectorized Liouvillian is diagonal in the existing matrix-unit basis. -/
theorem dephasing_liouvillian {a : ℝ} (ha : 0 ≤ a) :
    lindbladLiouvillian 0 (dephasingJump a) =
      diagonal (fun p : Fin 2 × Fin 2 => if p.1 = p.2 then 0 else (-2*a : ℂ)) := by
  ext p q
  rw [lindbladLiouvillian, LinearMap.toMatrix_apply]
  change lindbladGenerator 0 (dephasingJump a) (Matrix.stdBasis ℂ (Fin 2) (Fin 2) q)
    p.1 p.2 = _
  rw [dephasing_generator_entry ha]
  rcases p with ⟨i,j⟩
  rcases q with ⟨k,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [Matrix.stdBasis]

/-- Evaluation of diagonal superoperators in the already-used matrix-unit coordinates. -/
theorem toLin_diagonal_entry (d : Fin 2 × Fin 2 → ℂ)
    (X : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    Matrix.toLin (Matrix.stdBasis ℂ (Fin 2) (Fin 2)) (Matrix.stdBasis ℂ (Fin 2) (Fin 2))
      (diagonal d) X i j = d (i,j) * X i j := by
  rw [Matrix.toLin_apply]
  simp [Matrix.stdBasis, Matrix.sum_apply, Fintype.sum_prod_type, Matrix.mulVec_diagonal,
    Pi.single_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp

/-- Exact entries of the existing Lindblad exponential; no substitute dynamics is defined. -/
theorem dephasing_propagator_entry {a : ℝ} (ha : 0 ≤ a) (t : ℝ)
    (X : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    lindbladPropagatorAction 0 (dephasingJump a) t X i j =
      (if i = j then 1 else (Real.exp (-2*a*t) : ℂ)) * X i j := by
  unfold lindbladPropagatorAction lindbladPropagator
  rw [dephasing_liouvillian ha, ← Matrix.diagonal_smul, Matrix.exp_diagonal,
    toLin_diagonal_entry]
  by_cases h : i = j
  · simp [h]
  · simp [h, ← Complex.exp_eq_exp_ℂ]
    left
    congr 1
    ring

/-- Nonnegative-time dephasing strength supplied by the actual generator. -/
def timeStrength (a t : ℝ) : ℝ := (1 - Real.exp (-2*a*t))/2

theorem timeStrength_bounds {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    0 ≤ timeStrength a t ∧ timeStrength a t ≤ 1/2 := by
  have he := Real.exp_pos (-2*a*t)
  have hl : Real.exp (-2*a*t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  unfold timeStrength
  constructor <;> linarith

/-- The Lindblad exponential is identified with the existing CPTP Kraus channel. -/
theorem dephasing_propagator_eq {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t)
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    lindbladPropagatorAction 0 (dephasingJump a) t X =
      krausMap (dephasingKraus (timeStrength a t)) X := by
  have hb := timeStrength_bounds ha ht
  ext i j
  rw [dephasing_propagator_entry ha, dephasing_entry hb.1 (by linarith [hb.2])]
  by_cases h : i = j
  · simp [h]
  · simp only [h, if_false]
    congr 1
    unfold timeStrength
    push_cast
    ring

/-- Complete positivity is consumed from the proved GKSL theorem. -/
theorem dephasing_propagator_CP (a : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    MatrixMap.IsCompletelyPositive (lindbladPropagatorAction 0 (dephasingJump a) t) :=
  isCompletelyPositive_lindbladPropagatorAction 0 Matrix.isHermitian_zero _ ht

/-- Composition comes from the actual vectorized semigroup theorem. -/
theorem dephasing_propagator_semigroup (a t s : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    lindbladPropagatorAction 0 (dephasingJump a) (t+s) X =
      lindbladPropagatorAction 0 (dephasingJump a) t
        (lindbladPropagatorAction 0 (dephasingJump a) s X) := by
  have h := congrArg (Matrix.toLinAlgEquiv (Matrix.stdBasis ℂ (Fin 2) (Fin 2)))
    (lindblad_semigroup 0 (dephasingJump a) t s)
  rw [map_mul] at h
  exact (LinearMap.congr_fun h X).symm

/-- Exact coherence decay, valid for every real time as an exponential identity. -/
theorem dephasing_propagator_E01 {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    lindbladPropagatorAction 0 (dephasingJump a) t E01 =
      (Real.exp (-2*a*t) : ℂ) • E01 := by
  ext i j
  rw [dephasing_propagator_entry ha]
  fin_cases i <;> fin_cases j <;> simp [E01]

/-- Gibbs stationarity is inherited through the proved identification. -/
theorem dephasing_propagator_fixed_gibbs {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t)
    (Δ β : ℝ) :
    lindbladPropagatorAction 0 (dephasingJump a) t (gibbs (twoLevel Δ) β) =
      gibbs (twoLevel Δ) β := by
  rw [dephasing_propagator_eq ha ht]
  have hb := timeStrength_bounds ha ht
  exact dephasing_fixed_gibbs hb.1 (by linarith [hb.2]) Δ β

section QuotientConsumers
open GibbsObservable

abbrev GibbsSpace (Δ β : ℝ) := Space (gram (gibbs (twoLevel Δ) β))
  (gram_posSemidef (gibbs_posDef (twoLevel_hermitian Δ) β).posSemidef)

/-- The existing faithful Gibbs reconstruction of the off-diagonal observable. -/
abbrev coherence (Δ β : ℝ) : GibbsSpace Δ β :=
  observable (gibbs_posDef (twoLevel_hermitian Δ) β).posSemidef E01

/-- The concrete channel consumes the stationary Kraus-to-quotient construction. -/
def quotientDephasing (Δ β γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    GibbsSpace Δ β →L[ℂ] GibbsSpace Δ β :=
  Channel.quotientChannel (gibbs_posDef (twoLevel_hermitian Δ) β).posSemidef
    (dephasingKraus γ) (isKrausChannel_dephasingKraus h0 h1)
    (dephasing_fixed_gibbs h0 h1 Δ β)

theorem quotientDephasing_observable (Δ β γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1)
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    quotientDephasing Δ β γ h0 h1 (observable (gibbs_posDef (twoLevel_hermitian Δ) β).posSemidef X) =
      observable (gibbs_posDef (twoLevel_hermitian Δ) β).posSemidef
        (krausMap (dephasingKraus γ) X) := by
  rw [quotientDephasing, Channel.quotientChannel_observable]
  exact congrArg (observable _) (dephasing_heisenberg γ X)

theorem dephasing_detailedBalance (Δ β γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    Channel.DetailedBalance (gibbs (twoLevel Δ) β) (dephasingKraus γ) := by
  intro X Y
  change (Y * _ * (∑ i, (dephasingKraus γ i)ᴴ * X * dephasingKraus γ i)ᴴ).trace =
    ((∑ i, (dephasingKraus γ i)ᴴ * Y * dephasingKraus γ i) * _ * Xᴴ).trace
  rw [dephasing_heisenberg, dephasing_heisenberg]
  exact dephasing_weighted_symmetry h0 h1 Δ β X Y

theorem quotientDephasing_selfAdjoint (Δ β γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    IsSelfAdjoint (quotientDephasing Δ β γ h0 h1) :=
  Channel.quotientChannel_selfAdjoint _ _ _ _ (dephasing_detailedBalance Δ β γ h0 h1)

theorem quotientDephasing_norm_le (Δ β γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1)
    (z : GibbsSpace Δ β) : ‖quotientDephasing Δ β γ h0 h1 z‖ ≤ ‖z‖ :=
  Channel.quotientChannel_norm_le _ _ _ _ z

theorem coherence_nonzero (Δ β : ℝ) : coherence Δ β ≠ 0 :=
  GibbsObservable.Clock.twoLevel_observable_nonzero Δ β

theorem quotientDephasing_coherence (Δ β γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    quotientDephasing Δ β γ h0 h1 (coherence Δ β) = (1-2*γ : ℂ) • coherence Δ β := by
  rw [coherence, quotientDephasing_observable, dephasing_E01 h0 h1, observable_smul]

theorem quotientDephasing_coherence_norm (Δ β γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    ‖quotientDephasing Δ β γ h0 h1 (coherence Δ β)‖ = |1-2*γ| * ‖coherence Δ β‖ := by
  rw [quotientDephasing_coherence, norm_smul]
  norm_cast

theorem quotientDephasing_pow_coherence (Δ β γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) (k : ℕ) :
    (quotientDephasing Δ β γ h0 h1 ^ k) (coherence Δ β) =
      (1-2*γ : ℂ)^k • coherence Δ β := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, ih, map_smul, quotientDephasing_coherence,
      smul_smul, pow_succ]

theorem quotientDephasing_pow_coherence_norm (Δ β γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) (k : ℕ) :
    ‖(quotientDephasing Δ β γ h0 h1 ^ k) (coherence Δ β)‖ =
      |1-2*γ|^k * ‖coherence Δ β‖ := by
  rw [quotientDephasing_pow_coherence, norm_smul, norm_pow]
  norm_cast

/-- Every strength above one half has a negative quadratic value on a surviving class. -/
theorem quotientDephasing_negative (Δ β γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1)
    (hhalf : 1/2 < γ) :
    (⟪quotientDephasing Δ β γ h0 h1 (coherence Δ β), coherence Δ β⟫_ℂ).re < 0 := by
  rw [quotientDephasing_coherence, inner_smul_left]
  have hp := norm_pos_iff.mpr (coherence_nonzero Δ β)
  norm_num [map_ofNat, Complex.mul_re, ← Complex.ofReal_pow]
  nlinarith [sq_pos_of_pos hp]

/-- The positive half of the dephasing family is the lazy version of another actual channel. -/
theorem quotientDephasing_eq_lazy (Δ β γ : ℝ) (h0 : 0 ≤ γ) (hhalf : γ ≤ 1/2) :
    quotientDephasing Δ β γ h0 (by linarith) =
      Channel.lazyChannel (gibbs_posDef (twoLevel_hermitian Δ) β).posSemidef
        (dephasingKraus (2*γ)) (isKrausChannel_dephasingKraus (by linarith) (by linarith))
        (dephasing_fixed_gibbs (by linarith) (by linarith) Δ β) := by
  ext z
  obtain ⟨X, rfl⟩ := observable_surjective (gibbs_posDef (twoLevel_hermitian Δ) β).posSemidef z
  rw [quotientDephasing_observable, Channel.lazyChannel_observable]
  change observable _ (krausMap (dephasingKraus γ) X) =
    observable _ ((1/2 : ℂ) • (X + ∑ i, (dephasingKraus (2*γ) i)ᴴ * X * dephasingKraus (2*γ) i))
  rw [dephasing_heisenberg]
  apply congrArg (observable _)
  ext i j
  rw [dephasing_entry h0 (by linarith)]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply,
    dephasing_entry (by linarith : 0 ≤ 2*γ) (by linarith : 2*γ ≤ 1)]
  by_cases h : i = j <;> simp [h] <;> ring

/-- Hilbert positivity has an exact threshold, strictly stronger than the CPTP parameter range. -/
theorem quotientDephasing_positive_iff (Δ β γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    (quotientDephasing Δ β γ h0 h1).IsPositive ↔ γ ≤ 1/2 := by
  constructor
  · intro h
    by_contra hn
    have hneg := quotientDephasing_negative Δ β γ h0 h1 (lt_of_not_ge hn)
    have hp := h.2 (coherence Δ β)
    change 0 ≤ (⟪quotientDephasing Δ β γ h0 h1 (coherence Δ β), coherence Δ β⟫_ℂ).re at hp
    linarith
  · intro hh
    rw [quotientDephasing_eq_lazy Δ β γ h0 hh]
    exact Channel.lazyChannel_positive _ _ _ _
      (dephasing_detailedBalance Δ β (2*γ) (by linarith) (by linarith))

theorem quotientDephasing_one_not_positive (Δ β : ℝ) :
    ¬ (quotientDephasing Δ β 1 (by norm_num) (by norm_num)).IsPositive := by
  rw [quotientDephasing_positive_iff]
  norm_num

/-- Quotient dynamics representing the actual Lindblad exponential through its proved Kraus identity. -/
def quotientLindblad (Δ β a t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    GibbsSpace Δ β →L[ℂ] GibbsSpace Δ β :=
  quotientDephasing Δ β (timeStrength a t) (timeStrength_bounds ha ht).1
    (by linarith [(timeStrength_bounds ha ht).2])

/-- Representatives evolve by the existing Lindblad propagator, not a replacement flow. -/
theorem quotientLindblad_observable (Δ β a t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t)
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    quotientLindblad Δ β a t ha ht
      (observable (gibbs_posDef (twoLevel_hermitian Δ) β).posSemidef X) =
      observable (gibbs_posDef (twoLevel_hermitian Δ) β).posSemidef
        (lindbladPropagatorAction 0 (dephasingJump a) t X) := by
  rw [quotientLindblad, quotientDephasing_observable, dephasing_propagator_eq ha ht]

theorem quotientLindblad_positive (Δ β a t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    (quotientLindblad Δ β a t ha ht).IsPositive :=
  (quotientDephasing_positive_iff _ _ _ _ _).mpr (timeStrength_bounds ha ht).2

theorem quotientLindblad_selfAdjoint (Δ β a t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    IsSelfAdjoint (quotientLindblad Δ β a t ha ht) :=
  (quotientLindblad_positive Δ β a t ha ht).isSelfAdjoint

theorem quotientLindblad_norm_le (Δ β a t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t)
    (z : GibbsSpace Δ β) : ‖quotientLindblad Δ β a t ha ht z‖ ≤ ‖z‖ :=
  quotientDephasing_norm_le _ _ _ _ _ z

theorem quotientLindblad_zero (Δ β a : ℝ) (ha : 0 ≤ a) :
    quotientLindblad Δ β a 0 ha (by norm_num) = 1 := by
  ext z
  obtain ⟨X, rfl⟩ := observable_surjective (gibbs_posDef (twoLevel_hermitian Δ) β).posSemidef z
  rw [quotientLindblad_observable]
  simp [lindbladPropagatorAction, lindblad_propagator_zero]

/-- The descended nonnegative-time maps obey the actual Lindblad composition law. -/
theorem quotientLindblad_add (Δ β a s t : ℝ) (ha : 0 ≤ a) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    quotientLindblad Δ β a (s+t) ha (add_nonneg hs ht) =
      quotientLindblad Δ β a s ha hs * quotientLindblad Δ β a t ha ht := by
  ext z
  obtain ⟨X, rfl⟩ := observable_surjective (gibbs_posDef (twoLevel_hermitian Δ) β).posSemidef z
  rw [mul_apply_eq_comp, quotientLindblad_observable, quotientLindblad_observable,
    quotientLindblad_observable, dephasing_propagator_semigroup]

/-- Every diagonal observable is fixed, excluding a global strict-contraction claim. -/
theorem quotientLindblad_diagonal (Δ β a t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t)
    (d : Fin 2 → ℂ) :
    quotientLindblad Δ β a t ha ht
      (observable (gibbs_posDef (twoLevel_hermitian Δ) β).posSemidef (diagonal d)) =
      observable (gibbs_posDef (twoLevel_hermitian Δ) β).posSemidef (diagonal d) := by
  have hb := timeStrength_bounds ha ht
  rw [quotientLindblad, quotientDephasing_observable,
    dephasing_diagonal hb.1 (by linarith [hb.2])]

theorem quotientLindblad_coherence (Δ β a t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    quotientLindblad Δ β a t ha ht (coherence Δ β) =
      (Real.exp (-2*a*t) : ℂ) • coherence Δ β := by
  rw [coherence, quotientLindblad_observable, dephasing_propagator_E01 ha, observable_smul]

/-- The exact decay rate is measured in the reconstructed Gibbs norm. -/
theorem quotientLindblad_coherence_norm (Δ β a t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    ‖quotientLindblad Δ β a t ha ht (coherence Δ β)‖ =
      Real.exp (-2*a*t) * ‖coherence Δ β‖ := by
  rw [quotientLindblad_coherence, norm_smul]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- A nonzero observable strictly decays at positive rate and time. -/
theorem quotientLindblad_coherence_strict (Δ β a t : ℝ) (ha : 0 < a) (ht : 0 < t) :
    ‖quotientLindblad Δ β a t ha.le ht.le (coherence Δ β)‖ < ‖coherence Δ β‖ := by
  rw [quotientLindblad_coherence_norm]
  have hp := norm_pos_iff.mpr (coherence_nonzero Δ β)
  have he : Real.exp (-2*a*t) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  nlinarith

end QuotientConsumers
end SKEFTHawking.FinitePositiveKernel.GibbsDephasing
