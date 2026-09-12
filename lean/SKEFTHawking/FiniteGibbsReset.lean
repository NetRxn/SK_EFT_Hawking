import SKEFTHawking.FiniteBlockConditionalExpectation

/-! Faithful finite reset dynamics. State and observable actions are trace dual,
with population relaxation to the normalized diagonal density. -/
noncomputable section
open Matrix Filter
open scoped ComplexOrder InnerProductSpace Topology
namespace SKEFTHawking.FinitePositiveKernel.GibbsReset
open QuantumNetwork OpenSystems GibbsObservable DiagonalLindblad
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A weighted matrix unit, indexed by its destination and source. -/
def jump (w : n → ℝ) (p : n × n) : Matrix n n ℂ :=
  fun i j => if i = p.1 ∧ j = p.2 then (Real.sqrt (w p.1) : ℂ) else 0

theorem jump_sandwich (w : n → ℝ) (hw : ∀ i, 0 ≤ w i)
    (p : n × n) (X : Matrix n n ℂ) (i j : n) :
    (jump w p * X * (jump w p)ᴴ) i j =
      if i = p.1 ∧ j = p.1 then (w p.1 : ℂ) * X p.2 p.2 else 0 := by
  by_cases hi : i = p.1 <;> by_cases hj : j = p.1 <;>
    simp [jump, Matrix.mul_apply, Matrix.conjTranspose_apply, apply_ite, hi, hj,
      mul_comm, mul_left_comm, ← Complex.ofReal_mul, Real.mul_self_sqrt (hw p.1)]

theorem jump_dual_sandwich (w : n → ℝ) (hw : ∀ i, 0 ≤ w i)
    (p : n × n) (X : Matrix n n ℂ) (i j : n) :
    ((jump w p)ᴴ * X * jump w p) i j =
      if i = p.2 ∧ j = p.2 then (w p.1 : ℂ) * X p.1 p.1 else 0 := by
  by_cases hi : i = p.2 <;> by_cases hj : j = p.2 <;>
    simp [jump, Matrix.mul_apply, Matrix.conjTranspose_apply, apply_ite, hi, hj,
      mul_comm, mul_left_comm, ← Complex.ofReal_mul, Real.mul_self_sqrt (hw p.1)]

/-- Reindex all destination-source pairs for the finite channel interface. -/
def resetKraus (w : n → ℝ) : Fin (Fintype.card (n × n)) → Matrix n n ℂ :=
  fun i => jump w ((Fintype.equivFin (n × n)).symm i)

theorem reset_state (w : n → ℝ) (hw : ∀ i, 0 ≤ w i) (X : Matrix n n ℂ) :
    krausMap (resetKraus w) X = X.trace • density w := by
  unfold krausMap resetKraus
  rw [(Fintype.equivFin (n × n)).symm.sum_comp (fun p => jump w p * X * (jump w p)ᴴ)]
  ext i j
  simp only [Matrix.sum_apply, jump_sandwich w hw, Fintype.sum_prod_type]
  by_cases h : i = j
  · subst j
    simp [density, Matrix.trace, Finset.mul_sum, mul_comm]
  · simp [density, h, Ne.symm h, ite_and]

theorem reset_observable (w : n → ℝ) (hw : ∀ i, 0 ≤ w i) (X : Matrix n n ℂ) :
    Channel.heisenberg (resetKraus w) X = (density w * X).trace • (1 : Matrix n n ℂ) := by
  unfold Channel.heisenberg resetKraus
  rw [(Fintype.equivFin (n × n)).symm.sum_comp (fun p => (jump w p)ᴴ * X * jump w p)]
  ext i j
  simp only [Matrix.sum_apply, jump_dual_sandwich w hw, Fintype.sum_prod_type]
  by_cases h : i = j
  · subst j
    simp [density, Matrix.trace]
  · simp [h, Ne.symm h, ite_and]

theorem density_trace (w : n → ℝ) : (density w).trace = (∑ i, w i : ℝ) := by
  simp [density, Matrix.trace]

theorem reset_normalized (w : n → ℝ) (hw : ∀ i, 0 ≤ w i) (hn : ∑ i, w i = 1) :
    IsKrausChannel (resetKraus w) := by
  have h := reset_observable w hw 1
  simpa [Channel.heisenberg, IsKrausChannel, density_trace, hn] using h

theorem reset_stationary (w : n → ℝ) (hw : ∀ i, 0 ≤ w i) (hn : ∑ i, w i = 1) :
    krausMap (resetKraus w) (density w) = density w := by
  rw [reset_state w hw, density_trace, hn]
  simp

/-- Rate-scaled reset jumps for the existing GKSL generator. -/
def jumps (w : n → ℝ) (γ : ℝ) := resetKraus (fun i => γ * w i)

omit [Fintype n] in
theorem density_scale (w : n → ℝ) (γ : ℝ) :
    density (fun i => γ * w i) = (γ : ℂ) • density w := by
  ext i j
  by_cases h : i = j <;> simp [density, h]

theorem jumps_square_sum (w : n → ℝ) (hw : ∀ i, 0 ≤ w i) (hn : ∑ i, w i = 1)
    (γ : ℝ) (hγ : 0 ≤ γ) :
    ∑ k, (jumps w γ k)ᴴ * jumps w γ k = (γ : ℂ) • (1 : Matrix n n ℂ) := by
  have h := reset_observable (fun i => γ*w i) (fun i => mul_nonneg hγ (hw i)) 1
  simpa [Channel.heisenberg, jumps, density_trace, ← Finset.mul_sum, hn] using h

theorem generator_state (w : n → ℝ) (hw : ∀ i, 0 ≤ w i) (hn : ∑ i, w i = 1)
    (γ : ℝ) (hγ : 0 ≤ γ) (X : Matrix n n ℂ) :
    lindbladGenerator 0 (jumps w γ) X = (γ : ℂ) • (X.trace • density w - X) := by
  have hj : (∑ k, jumps w γ k * X * (jumps w γ k)ᴴ) =
      X.trace • ((γ : ℂ) • density w) := by
    exact (reset_state (fun i => γ*w i) (fun i => mul_nonneg hγ (hw i)) X).trans
      (congrArg (fun Z => X.trace • Z) (density_scale w γ))
  simp only [lindbladGenerator, LinearMap.add_apply, lindbladHamPart_apply,
    lindbladJump_apply, lindbladAnticommPart_apply, zero_mul, mul_zero, sub_self,
    smul_zero, zero_add, hj, jumps_square_sum w hw hn γ hγ,
    smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  module

open scoped Matrix.Norms.Operator in
/-- Exact exponential on an idempotent and its complementary range. -/
theorem exp_idempotent_complement (P : Matrix n n ℂ) (hP : P * P = P) (c : ℂ) :
    NormedSpace.exp (c • (1-P)) = P + Complex.exp c • (1-P) := by
  have hPQ : P * (1-P) = 0 := by rw [mul_sub, mul_one, hP, sub_self]
  have hQP : (1-P) * P = 0 := by rw [sub_mul, one_mul, hP, sub_self]
  have hQQ : (1-P) * (1-P) = 1-P := by
    rw [sub_mul, one_mul, hPQ, sub_zero]
  let f : ℂ × ℂ →+* Matrix n n ℂ :=
    { toFun := fun z => z.1 • P + z.2 • (1-P)
      map_one' := by simp
      map_zero' := by simp
      map_add' := by intros; simp only [Prod.fst_add, Prod.snd_add, add_smul]; abel
      map_mul' := by
        intro x y
        simp only [Prod.fst_mul, Prod.snd_mul, add_mul, mul_add, smul_mul_assoc,
          mul_smul_comm, smul_smul, hP, hPQ, hQP, hQQ, smul_zero, add_zero, zero_add]
        simp only [mul_comm] }
  have hf : Continuous f :=
    (continuous_fst.smul continuous_const).add (continuous_snd.smul continuous_const)
  have h := NormedSpace.map_exp f hf (0,c)
  convert h.symm using 1 <;> simp [f, ← Complex.exp_eq_exp_ℂ]
  rfl

/-- Schrödinger reset as a linear endomorphism. -/
def stateReset (w : n → ℝ) : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun X := X.trace • density w
  map_add' X Y := by simp [Matrix.trace_add, add_smul]
  map_smul' c X := by simp [Matrix.trace_smul, smul_smul]

theorem stateReset_idempotent (w : n → ℝ) (hn : ∑ i, w i = 1) :
    stateReset w * stateReset w = stateReset w := by
  ext X i j
  simp [stateReset, Module.End.mul_apply, density_trace, hn]

theorem propagator_state (w : n → ℝ) (hw : ∀ i, 0 ≤ w i) (hn : ∑ i, w i = 1)
    (γ : ℝ) (hγ : 0 ≤ γ) (t : ℝ) (X : Matrix n n ℂ) :
    lindbladPropagatorAction 0 (jumps w γ) t X =
      (Real.exp (-γ*t) : ℂ) • X + (1-(Real.exp (-γ*t) : ℂ)) • (X.trace • density w) := by
  let b := Matrix.stdBasis ℂ n n
  let P := LinearMap.toMatrix b b (stateReset w)
  have hP : P * P = P := by
    rw [← LinearMap.toMatrix_mul]
    exact congrArg (LinearMap.toMatrix b b) (stateReset_idempotent w hn)
  have hL : lindbladLiouvillian 0 (jumps w γ) = (γ : ℂ) • (P-1) := by
    have hg : lindbladGenerator 0 (jumps w γ) = (γ : ℂ) • (stateReset w-1) := by
      ext Y i j
      exact congrFun (congrFun (generator_state w hw hn γ hγ Y) i) j
    simp [lindbladLiouvillian, hg, P, b, map_sub, map_smul]
  have ht : (t : ℂ) • ((γ : ℂ) • (P-1)) = ((-γ*t : ℝ) : ℂ) • (1-P) := by
    simp only [smul_smul, Complex.ofReal_mul, Complex.ofReal_neg]
    module
  unfold lindbladPropagatorAction lindbladPropagator
  rw [hL, ht]
  change (Matrix.toLin b b (NormedSpace.exp (((-γ*t : ℝ) : ℂ) • (1-P)))) X = _
  rw [exp_idempotent_complement P hP]
  simp only [map_add, map_smul, map_sub, Matrix.toLin_one, P, Matrix.toLin_toMatrix,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply,
    ← Complex.ofReal_exp]
  change X.trace • density w + (Real.exp (-γ*t) : ℂ) • (X-X.trace • density w) = _
  module

/-- Identity plus reset Kraus branches realize each convex time step. -/
def mixBranch (w : n → ℝ) (q : ℝ) : Option (n × n) → Matrix n n ℂ
  | none => (Real.sqrt q : ℂ) • 1
  | some p => (Real.sqrt (1-q) : ℂ) • jump w p

def timeKraus (w : n → ℝ) (q : ℝ) : Fin (Fintype.card (Option (n × n))) → Matrix n n ℂ :=
  fun i => mixBranch w q ((Fintype.equivFin (Option (n × n))).symm i)

theorem time_state (w : n → ℝ) (hw : ∀ i, 0 ≤ w i) (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (X : Matrix n n ℂ) : krausMap (timeKraus w q) X =
      (q : ℂ) • X + (1-(q : ℂ)) • (X.trace • density w) := by
  unfold krausMap timeKraus
  rw [(Fintype.equivFin (Option (n × n))).symm.sum_comp
    (fun p => mixBranch w q p * X * (mixBranch w q p)ᴴ)]
  simp only [Fintype.sum_option, mixBranch, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, smul_mul_assoc, mul_smul_comm, smul_smul,
    one_mul, mul_one]
  have hs := reset_state w hw X
  unfold krausMap resetKraus at hs
  rw [(Fintype.equivFin (n × n)).symm.sum_comp (fun p => jump w p * X * (jump w p)ᴴ)] at hs
  rw [← Finset.smul_sum, hs]
  simp
  simp only [← Complex.ofReal_mul, Real.mul_self_sqrt hq, Real.mul_self_sqrt (sub_nonneg.mpr hq1)]
  simp [smul_smul]

theorem time_observable (w : n → ℝ) (hw : ∀ i, 0 ≤ w i) (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (X : Matrix n n ℂ) : Channel.heisenberg (timeKraus w q) X =
      (q : ℂ) • X + (1-(q : ℂ)) • ((density w * X).trace • (1 : Matrix n n ℂ)) := by
  unfold Channel.heisenberg timeKraus
  rw [(Fintype.equivFin (Option (n × n))).symm.sum_comp
    (fun p => (mixBranch w q p)ᴴ * X * mixBranch w q p)]
  simp only [Fintype.sum_option, mixBranch, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, smul_mul_assoc, mul_smul_comm, smul_smul,
    one_mul, mul_one]
  have hs := reset_observable w hw X
  unfold Channel.heisenberg resetKraus at hs
  rw [(Fintype.equivFin (n × n)).symm.sum_comp (fun p => (jump w p)ᴴ * X * jump w p)] at hs
  rw [← Finset.smul_sum, hs]
  simp
  simp only [← Complex.ofReal_mul, Real.mul_self_sqrt hq, Real.mul_self_sqrt (sub_nonneg.mpr hq1)]
  simp [smul_smul]

theorem time_normalized (w : n → ℝ) (hw : ∀ i, 0 ≤ w i) (hn : ∑ i, w i = 1)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) : IsKrausChannel (timeKraus w q) := by
  have h := time_observable w hw q hq hq1 1
  simp only [mul_one, density_trace, hn, Complex.ofReal_one, one_smul] at h
  have hr : (q : ℂ) • (1 : Matrix n n ℂ) + (1-(q : ℂ)) • 1 = 1 := by module
  rw [hr] at h
  simpa [Channel.heisenberg, IsKrausChannel] using h

theorem time_stationary (w : n → ℝ) (hw : ∀ i, 0 ≤ w i) (hn : ∑ i, w i = 1)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) : krausMap (timeKraus w q) (density w) = density w := by
  rw [time_state w hw q hq hq1, density_trace, hn]
  simp only [Complex.ofReal_one, one_smul]
  module

theorem exp_rate_le_one (γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) : Real.exp (-γ*t) ≤ 1 :=
  Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hγ) ht)

theorem time_state_eq_propagator (w : n → ℝ) (hw : ∀ i, 0 ≤ w i) (hn : ∑ i, w i = 1)
    (γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (X : Matrix n n ℂ) :
    krausMap (timeKraus w (Real.exp (-γ*t))) X = lindbladPropagatorAction 0 (jumps w γ) t X := by
  rw [time_state w hw _ (Real.exp_pos _).le (exp_rate_le_one γ t hγ ht), propagator_state w hw hn γ hγ]

theorem expectation_star (w : n → ℝ) (X : Matrix n n ℂ) :
    (density w * Xᴴ).trace = star ((density w * X).trace) := by
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul]
  have hd : (density w)ᴴ = density w := by simp [density]
  rw [hd, Matrix.trace_mul_comm]

theorem reset_detailedBalance (w : n → ℝ) (hw : ∀ i, 0 ≤ w i) :
    Channel.DetailedBalance (density w) (resetKraus w) := by
  intro X Y
  rw [reset_observable w hw, reset_observable w hw]
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, mul_smul_comm,
    smul_mul_assoc, mul_one, one_mul, Matrix.trace_smul]
  rw [expectation_star, Matrix.trace_mul_comm Y]
  exact mul_comm _ _

/-- The reset channel on the existing faithful reconstructed space. -/
def scalarProjection (w : n → ℝ) (hw : ∀ i, 0 < w i) (hn : ∑ i, w i = 1) :
    WeightedSpace w hw →L[ℂ] WeightedSpace w hw :=
  Channel.quotientChannel (density_posDef w hw).posSemidef (resetKraus w)
    (reset_normalized w (fun i => (hw i).le) hn) (reset_stationary w (fun i => (hw i).le) hn)

theorem scalarProjection_observable (w : n → ℝ) (hw : ∀ i, 0 < w i) (hn : ∑ i, w i = 1)
    (X : Matrix n n ℂ) : scalarProjection w hw hn (observable (density_posDef w hw).posSemidef X) =
      (density w * X).trace • observable (density_posDef w hw).posSemidef 1 := by
  rw [scalarProjection, Channel.quotientChannel_observable, reset_observable w (fun i => (hw i).le), observable_smul]

theorem scalarProjection_idempotent (w : n → ℝ) (hw : ∀ i, 0 < w i) (hn : ∑ i, w i = 1)
    (z : WeightedSpace w hw) : scalarProjection w hw hn (scalarProjection w hw hn z) = scalarProjection w hw hn z := by
  obtain ⟨X, rfl⟩ := observable_surjective (density_posDef w hw).posSemidef z
  rw [scalarProjection_observable, map_smul, scalarProjection_observable]
  simp [density_trace, hn]

theorem scalarProjection_symmetric (w : n → ℝ) (hw : ∀ i, 0 < w i) (hn : ∑ i, w i = 1) :
    (scalarProjection w hw hn).IsSymmetric :=
  Channel.quotientChannel_symmetric _ _ _ _ (reset_detailedBalance w (fun i => (hw i).le))

theorem scalarProjection_inner (w : n → ℝ) (hw : ∀ i, 0 < w i) (hn : ∑ i, w i = 1)
    (z : WeightedSpace w hw) : ⟪scalarProjection w hw hn z, z⟫_ℂ =
      ⟪scalarProjection w hw hn z, scalarProjection w hw hn z⟫_ℂ := by
  have h := scalarProjection_symmetric w hw hn (scalarProjection w hw hn z) z
  change ⟪scalarProjection w hw hn (scalarProjection w hw hn z), z⟫_ℂ = _ at h
  rw [scalarProjection_idempotent] at h
  exact h

theorem scalarProjection_positive (w : n → ℝ) (hw : ∀ i, 0 < w i) (hn : ∑ i, w i = 1) :
    (scalarProjection w hw hn).IsPositive := by
  refine ⟨scalarProjection_symmetric w hw hn, ?_⟩
  intro z
  change 0 ≤ (⟪scalarProjection w hw hn z, z⟫_ℂ).re
  rw [scalarProjection_inner]
  exact inner_self_nonneg (𝕜 := ℂ) (x := scalarProjection w hw hn z)

/-- The actual observable time channel, with the prescribed reset density. -/
def evolution (w : n → ℝ) (hw : ∀ i, 0 < w i) (hn : ∑ i, w i = 1)
    (γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) : WeightedSpace w hw →L[ℂ] WeightedSpace w hw :=
  Channel.quotientChannel (density_posDef w hw).posSemidef (timeKraus w (Real.exp (-γ*t)))
    (time_normalized w (fun i => (hw i).le) hn _ (Real.exp_pos _).le (exp_rate_le_one γ t hγ ht))
    (time_stationary w (fun i => (hw i).le) hn _ (Real.exp_pos _).le (exp_rate_le_one γ t hγ ht))

theorem evolution_apply (w : n → ℝ) (hw : ∀ i, 0 < w i) (hn : ∑ i, w i = 1)
    (γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (z : WeightedSpace w hw) :
    evolution w hw hn γ t hγ ht z = (Real.exp (-γ*t) : ℂ) • z +
      (1-(Real.exp (-γ*t) : ℂ)) • scalarProjection w hw hn z := by
  obtain ⟨X, rfl⟩ := observable_surjective (density_posDef w hw).posSemidef z
  rw [evolution, Channel.quotientChannel_observable,
    time_observable w (fun i => (hw i).le) _ (Real.exp_pos _).le (exp_rate_le_one γ t hγ ht),
    scalarProjection_observable]
  change (observableLinear (density_posDef w hw).posSemidef) (_ + _) = _
  rw [map_add]
  simp only [map_smul]
  rfl

theorem evolution_error (w : n → ℝ) (hw : ∀ i, 0 < w i) (hn : ∑ i, w i = 1)
    (γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (z : WeightedSpace w hw) :
    evolution w hw hn γ t hγ ht z - scalarProjection w hw hn z =
      (Real.exp (-γ*t) : ℂ) • (z-scalarProjection w hw hn z) := by
  rw [evolution_apply]
  module

theorem evolution_error_norm (w : n → ℝ) (hw : ∀ i, 0 < w i) (hn : ∑ i, w i = 1)
    (γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (z : WeightedSpace w hw) :
    ‖evolution w hw hn γ t hγ ht z - scalarProjection w hw hn z‖ =
      Real.exp (-γ*t) * ‖z-scalarProjection w hw hn z‖ := by
  rw [evolution_error, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

theorem scalarProjection_error_orthogonal (w : n → ℝ) (hw : ∀ i, 0 < w i) (hn : ∑ i, w i = 1)
    (z : WeightedSpace w hw) : ⟪scalarProjection w hw hn z, z-scalarProjection w hw hn z⟫_ℂ = 0 := by
  rw [inner_sub_right, scalarProjection_inner, sub_self]

theorem scalarProjection_fixed_iff (w : n → ℝ) (hw : ∀ i, 0 < w i) (hn : ∑ i, w i = 1)
    (z : WeightedSpace w hw) : scalarProjection w hw hn z = z ↔
      ∃ c : ℂ, z = c • observable (density_posDef w hw).posSemidef 1 := by
  constructor
  · intro h
    obtain ⟨X, rfl⟩ := observable_surjective (density_posDef w hw).posSemidef z
    exact ⟨(density w * X).trace, h.symm.trans (scalarProjection_observable w hw hn X)⟩
  · rintro ⟨c, rfl⟩
    rw [map_smul, scalarProjection_observable]
    simp [density_trace, hn]

theorem evolution_positive (w : n → ℝ) (hw : ∀ i, 0 < w i) (hn : ∑ i, w i = 1)
    (γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) : (evolution w hw hn γ t hγ ht).IsPositive := by
  have he : evolution w hw hn γ t hγ ht = (Real.exp (-γ*t) : ℂ) • (1 : WeightedSpace w hw →L[ℂ] _) +
      (1-(Real.exp (-γ*t) : ℂ)) • scalarProjection w hw hn := by
    ext z
    exact evolution_apply w hw hn γ t hγ ht z
  rw [he]
  exact (ContinuousLinearMap.isPositive_one.smul_of_nonneg (by exact_mod_cast (Real.exp_pos (-γ*t)).le)).add
    ((scalarProjection_positive w hw hn).smul_of_nonneg (by exact_mod_cast sub_nonneg.mpr (exp_rate_le_one γ t hγ ht)))

theorem evolution_selfAdjoint (w : n → ℝ) (hw : ∀ i, 0 < w i) (hn : ∑ i, w i = 1)
    (γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) : IsSelfAdjoint (evolution w hw hn γ t hγ ht) :=
  (evolution_positive w hw hn γ t hγ ht).isSelfAdjoint

theorem evolution_tendsto (w : n → ℝ) (hw : ∀ i, 0 < w i) (hn : ∑ i, w i = 1)
    (γ : ℝ) (hγ : 0 < γ) (z : WeightedSpace w hw) :
    Tendsto (fun t : NNReal => evolution w hw hn γ t hγ.le t.property z) atTop
      (𝓝 (scalarProjection w hw hn z)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [evolution_error_norm]
  have hc : Tendsto (fun t : NNReal => (t : ℝ)) atTop atTop := NNReal.tendsto_coe_atTop.mpr tendsto_id
  have hm := Filter.Tendsto.const_mul_atTop hγ hc
  have he : Tendsto (fun t : NNReal => Real.exp (-γ*(t:ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul] using Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hm)
  simpa using he.mul_const ‖z-scalarProjection w hw hn z‖

theorem evolution_fixed_iff (w : n → ℝ) (hw : ∀ i, 0 < w i) (hn : ∑ i, w i = 1)
    (γ t : ℝ) (hγ : 0 < γ) (ht : 0 < t) (z : WeightedSpace w hw) :
    evolution w hw hn γ t hγ.le ht.le z = z ↔ scalarProjection w hw hn z = z := by
  constructor
  · intro h
    have he := evolution_error_norm w hw hn γ t hγ.le ht.le z
    rw [h] at he
    have hex : Real.exp (-γ*t) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
    have hz : ‖z-scalarProjection w hw hn z‖ = 0 := by nlinarith [norm_nonneg (z-scalarProjection w hw hn z)]
    exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm
  · intro h
    have he := evolution_error w hw hn γ t hγ.le ht.le z
    rw [h, sub_self, smul_zero, sub_eq_zero] at he
    exact he

theorem evolution_zero_rate (w : n → ℝ) (hw : ∀ i, 0 < w i) (hn : ∑ i, w i = 1)
    (t : ℝ) (ht : 0 ≤ t) : evolution w hw hn 0 t (by norm_num) ht = 1 := by
  ext z
  simp [evolution_apply]

theorem stationary_trace_one_iff (w : n → ℝ) (hw : ∀ i, 0 ≤ w i) (hn : ∑ i, w i = 1)
    (γ : ℝ) (hγ : 0 < γ) (X : Matrix n n ℂ) (hX : X.trace = 1) :
    lindbladGenerator 0 (jumps w γ) X = 0 ↔ X = density w := by
  rw [generator_state w hw hn γ hγ.le, hX, one_smul, smul_eq_zero]
  simp only [Complex.ofReal_eq_zero, hγ.ne', false_or, sub_eq_zero]
  exact eq_comm

/-- The finite-time Kraus identification connects the actual state exponential
and the observable action by trace duality. -/
theorem propagator_trace_duality (w : n → ℝ) (hw : ∀ i, 0 ≤ w i) (hn : ∑ i, w i = 1)
    (γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (S X : Matrix n n ℂ) :
    (S * Channel.heisenberg (timeKraus w (Real.exp (-γ*t))) X).trace =
      (lindbladPropagatorAction 0 (jumps w γ) t S * X).trace := by
  rw [Channel.trace_duality, time_state_eq_propagator w hw hn γ t hγ ht]

theorem propagator_trace_one_fixed_iff (w : n → ℝ) (hw : ∀ i, 0 ≤ w i) (hn : ∑ i, w i = 1)
    (γ t : ℝ) (hγ : 0 < γ) (ht : 0 < t) (X : Matrix n n ℂ) (hX : X.trace = 1) :
    lindbladPropagatorAction 0 (jumps w γ) t X = X ↔ X = density w := by
  have he : lindbladPropagatorAction 0 (jumps w γ) t X - X =
      (1-(Real.exp (-γ*t) : ℂ)) • (density w-X) := by
    rw [propagator_state w hw hn γ hγ.le, hX, one_smul]
    module
  have hnz : (1-(Real.exp (-γ*t) : ℂ)) ≠ 0 := by
    have hr : 0 < 1-Real.exp (-γ*t) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith))
    exact_mod_cast hr.ne'
  rw [← sub_eq_zero, he, smul_eq_zero]
  simp only [hnz, false_or, sub_eq_zero]
  exact eq_comm

theorem evolution_fixed_scalar_iff (w : n → ℝ) (hw : ∀ i, 0 < w i) (hn : ∑ i, w i = 1)
    (γ t : ℝ) (hγ : 0 < γ) (ht : 0 < t) (z : WeightedSpace w hw) :
    evolution w hw hn γ t hγ.le ht.le z = z ↔
      ∃ c : ℂ, z = c • observable (density_posDef w hw).posSemidef 1 := by
  rw [evolution_fixed_iff w hw hn γ t hγ ht, scalarProjection_fixed_iff]

section Gibbs
open FiniteGibbsClock
variable [Nonempty n]

/-- Boltzmann weights normalized by the existing partition function. -/
def gibbsWeights (E : n → ℝ) (β : ℝ) : n → ℝ :=
  fun i => (partition (density E) β)⁻¹ * Real.exp (-β * E i)

omit [Fintype n] [Nonempty n] in
theorem energy_hermitian (E : n → ℝ) : (density E).IsHermitian := by
  simp [density, Matrix.IsHermitian]

theorem gibbsWeights_pos (E : n → ℝ) (β : ℝ) (i : n) : 0 < gibbsWeights E β i :=
  mul_pos (inv_pos.mpr (partition_pos (energy_hermitian E) β)) (Real.exp_pos _)

omit [Nonempty n] in
theorem density_gibbsWeights (E : n → ℝ) (β : ℝ) : density (gibbsWeights E β) = gibbs (density E) β := by
  unfold gibbs boltzmann density
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal, ← Matrix.diagonal_smul]
  ext i j
  by_cases h : i = j <;>
    simp [gibbsWeights, h, ← Complex.exp_eq_exp_ℂ]
  simp [density]

theorem gibbsWeights_normalized (E : n → ℝ) (β : ℝ) : ∑ i, gibbsWeights E β i = 1 := by
  have h := gibbs_trace_one (energy_hermitian E) β
  rw [← density_gibbsWeights, density_trace] at h
  exact_mod_cast h

/-- The actual Gibbs state is stationary for the constructed population-mixing generator. -/
theorem gibbs_generator_stationary (E : n → ℝ) (β γ : ℝ) (hγ : 0 ≤ γ) :
    lindbladGenerator 0 (jumps (gibbsWeights E β) γ) (gibbs (density E) β) = 0 := by
  rw [← density_gibbsWeights,
    generator_state _ (fun i => (gibbsWeights_pos E β i).le) (gibbsWeights_normalized E β) γ hγ,
    density_trace, gibbsWeights_normalized]
  simp
end Gibbs

section Blocks
variable {κ : Type*} [Fintype κ]

theorem block_preserves_expectation (w : n → ℝ) (ell : κ → n → ℝ) (X : Matrix n n ℂ) :
    (density w * blockExpectation ell X).trace = (density w * X).trace := by
  simp [Matrix.trace, density, blockExpectation, rate_self]

theorem scalarProjection_after_block (w : n → ℝ) (hw : ∀ i, 0 < w i) (hn : ∑ i, w i = 1)
    (ell : κ → n → ℝ) : scalarProjection w hw hn * projection w hw ell = scalarProjection w hw hn := by
  ext z
  obtain ⟨X, rfl⟩ := observable_surjective (density_posDef w hw).posSemidef z
  simp only [mul_apply_eq_comp, projection_observable, scalarProjection_observable,
    block_preserves_expectation]

theorem block_after_scalarProjection (w : n → ℝ) (hw : ∀ i, 0 < w i) (hn : ∑ i, w i = 1)
    (ell : κ → n → ℝ) : projection w hw ell * scalarProjection w hw hn = scalarProjection w hw hn := by
  ext z
  obtain ⟨X, rfl⟩ := observable_surjective (density_posDef w hw).posSemidef z
  simp only [mul_apply_eq_comp, scalarProjection_observable, map_smul,
    projection_observable, BlockConditionalExpectation.expectation_one]
end Blocks

/-- A nonuniform faithful three-level equilibrium. -/
def threeWeights : Fin 3 → ℝ := ![1/2, 1/3, 1/6]

theorem threeWeights_pos (i : Fin 3) : 0 < threeWeights i := by fin_cases i <;> norm_num [threeWeights]
theorem threeWeights_normalized : ∑ i, threeWeights i = 1 := by norm_num [threeWeights, Fin.sum_univ_succ]

def concentrated : Matrix (Fin 3) (Fin 3) ℂ := diagonal ![1,0,0]

theorem concentrated_density : IsDensityOperator concentrated := by
  constructor
  · apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> norm_num
  · norm_num [concentrated, Matrix.trace, Fin.sum_univ_succ]

theorem population_transfer (γ t : ℝ) (hγ : 0 ≤ γ) :
    lindbladPropagatorAction 0 (jumps threeWeights γ) t concentrated 1 1 =
      ((1-Real.exp (-γ*t))/3 : ℝ) := by
  rw [propagator_state threeWeights (fun i => (threeWeights_pos i).le) threeWeights_normalized γ hγ]
  norm_num [concentrated, Matrix.trace, Fin.sum_univ_succ, density, threeWeights]
  ring

theorem population_transfer_pos (γ t : ℝ) (hγ : 0 < γ) (ht : 0 < t) :
    0 < (lindbladPropagatorAction 0 (jumps threeWeights γ) t concentrated 1 1).re := by
  rw [population_transfer γ t hγ.le, Complex.ofReal_re]
  exact div_pos (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith))) (by norm_num)

/-- A diagonal observable with zero equilibrium mean and nonzero reconstructed norm. -/
def centeredDiagonal : Matrix (Fin 3) (Fin 3) ℂ := diagonal ![1,-3/2,0]

def centered : WeightedSpace threeWeights threeWeights_pos :=
  observable (density_posDef threeWeights threeWeights_pos).posSemidef centeredDiagonal

theorem centered_mean_zero : (density threeWeights * centeredDiagonal).trace = 0 := by
  norm_num [density, threeWeights, centeredDiagonal, Matrix.trace, Fin.sum_univ_succ]

theorem centered_projection_zero : scalarProjection threeWeights threeWeights_pos threeWeights_normalized centered = 0 := by
  rw [centered, scalarProjection_observable, centered_mean_zero, zero_smul]

theorem centered_norm_pos : 0 < ‖centered‖ := by
  apply norm_pos_iff.mpr
  intro h
  have hz := (observable_eq_zero_iff (density_posDef threeWeights threeWeights_pos) centeredDiagonal).mp h
  have he := congrFun (congrFun hz 0) 0
  norm_num [centeredDiagonal] at he

theorem centered_decay_norm (γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) :
    ‖evolution threeWeights threeWeights_pos threeWeights_normalized γ t hγ ht centered‖ =
      Real.exp (-γ*t) * ‖centered‖ := by
  simpa only [centered_projection_zero, sub_zero] using
    evolution_error_norm threeWeights threeWeights_pos threeWeights_normalized γ t hγ ht centered

theorem centered_strict_decay (γ t : ℝ) (hγ : 0 < γ) (ht : 0 < t) :
    ‖evolution threeWeights threeWeights_pos threeWeights_normalized γ t hγ.le ht.le centered‖ < ‖centered‖ := by
  rw [centered_decay_norm]
  exact mul_lt_of_lt_one_left centered_norm_pos (Real.exp_lt_one_iff.mpr (by nlinarith))

/-- Nonuniform reset exhibits the genuine state/observable orientation difference. -/
theorem reset_orientation_distinct : krausMap (resetKraus threeWeights) 1 ≠
    Channel.heisenberg (resetKraus threeWeights) 1 := by
  rw [reset_state threeWeights (fun i => (threeWeights_pos i).le),
    reset_observable threeWeights (fun i => (threeWeights_pos i).le)]
  intro h
  have he := congrFun (congrFun h 0) 0
  norm_num [density, threeWeights, Matrix.trace, Fin.sum_univ_succ] at he

end SKEFTHawking.FinitePositiveKernel.GibbsReset
