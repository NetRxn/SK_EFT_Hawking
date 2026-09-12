import SKEFTHawking.FiniteGibbsReset

/-! Actual finite GKSL reset plus uniform signature-block projector noise.
The state and observable projections differ for nonuniform Gibbs weights. -/
noncomputable section
open Matrix Filter
open scoped ComplexOrder InnerProductSpace Topology
namespace SKEFTHawking.FinitePositiveKernel.GibbsBlockRelaxation
open QuantumNetwork OpenSystems GibbsObservable DiagonalLindblad BlockConditionalExpectation
variable {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ]

/-- The existing block expectation as a linear endomorphism. -/
def blockMap (ell : κ → n → ℝ) : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ :=
  Channel.heisenbergLinear (blockKraus ell)

theorem blockMap_apply (ell : κ → n → ℝ) (X : Matrix n n ℂ) :
    blockMap ell X = blockExpectation ell X := blockKraus_heisenberg ell X

omit [DecidableEq n] in
theorem block_trace (ell : κ → n → ℝ) (X : Matrix n n ℂ) :
    (blockExpectation ell X).trace = X.trace := by simp [Matrix.trace, blockExpectation]

omit [Fintype n] in
theorem block_density (ell : κ → n → ℝ) (w : n → ℝ) : blockExpectation ell (density w) = density w := by
  ext i j
  by_cases h : i = j <;> simp [blockExpectation, density, h]

theorem blockMap_idempotent (ell : κ → n → ℝ) : blockMap ell * blockMap ell = blockMap ell := by
  ext X i j
  simp [Module.End.mul_apply, blockMap_apply, blockExpectation_idempotent]

theorem stateReset_after_block (ell : κ → n → ℝ) (w : n → ℝ) :
    GibbsReset.stateReset w * blockMap ell = GibbsReset.stateReset w := by
  ext X i j
  simp [Module.End.mul_apply, GibbsReset.stateReset, blockMap_apply, block_trace]

theorem block_after_stateReset (ell : κ → n → ℝ) (w : n → ℝ) :
    blockMap ell * GibbsReset.stateReset w = GibbsReset.stateReset w := by
  ext X i j
  simp [Module.End.mul_apply, GibbsReset.stateReset, map_smul, blockMap_apply, block_density]

omit [Fintype κ] in
theorem scaled_sandwich {ι : Type*} [Fintype ι] (V : ι → Matrix n n ℂ)
    (a : ℝ) (ha : 0 ≤ a) (X : Matrix n n ℂ) :
    ∑ k, ((Real.sqrt a : ℂ) • V k) * X * ((Real.sqrt a : ℂ) • V k)ᴴ =
      (a : ℂ) • ∑ k, V k * X * (V k)ᴴ := by
  simp only [Matrix.conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
  simp
  simp only [← Complex.ofReal_mul, Real.mul_self_sqrt ha]
  rw [Finset.smul_sum]
  simp

omit [Fintype κ] in
theorem scaled_square {ι : Type*} [Fintype ι] (V : ι → Matrix n n ℂ)
    (a : ℝ) (ha : 0 ≤ a) :
    ∑ k, ((Real.sqrt a : ℂ) • V k)ᴴ * ((Real.sqrt a : ℂ) • V k) =
      (a : ℂ) • ∑ k, (V k)ᴴ * V k := by
  simp only [Matrix.conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
  simp
  simp only [← Complex.ofReal_mul, Real.mul_self_sqrt ha]
  rw [Finset.smul_sum]
  simp

/-- Concatenated actual reset and uniform block-projector jumps. -/
def jumps (ell : κ → n → ℝ) (w : n → ℝ) (γ η : ℝ) :
    Sum (Fin (Fintype.card (n × n))) (Fin (Fintype.card (Blocks ell))) → Matrix n n ℂ
  | .inl k => GibbsReset.jumps w γ k
  | .inr k => (Real.sqrt η : ℂ) • blockKraus ell k

theorem generator_state (ell : κ → n → ℝ) (w : n → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hn : ∑ i, w i = 1) (γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (X : Matrix n n ℂ) :
    lindbladGenerator 0 (jumps ell w γ η) X =
      (γ : ℂ) • (X.trace • density w-X) + (η : ℂ) • (blockExpectation ell X-X) := by
  have hs : (∑ k, jumps ell w γ η k * X * (jumps ell w γ η k)ᴴ) =
      (γ : ℂ) • (X.trace • density w) + (η : ℂ) • blockExpectation ell X := by
    simp only [Fintype.sum_sum_type, jumps, scaled_sandwich _ η hη]
    have hr := GibbsReset.reset_state (fun i => γ*w i) (fun i => mul_nonneg hγ (hw i)) X
    change (∑ k, GibbsReset.jumps w γ k * X * (GibbsReset.jumps w γ k)ᴴ) = _ at hr
    rw [GibbsReset.density_scale] at hr
    rw [hr]
    change X.trace • ((γ:ℂ) • density w) + (η:ℂ) • krausMap (blockKraus ell) X = _
    rw [blockKraus_action]
    module
  have hsq : ∑ k, (jumps ell w γ η k)ᴴ * jumps ell w γ η k = (γ+η : ℂ) • (1 : Matrix n n ℂ) := by
    simp only [Fintype.sum_sum_type, jumps, scaled_square _ η hη,
      GibbsReset.jumps_square_sum w hw hn γ hγ]
    rw [show (∑ k, (blockKraus ell k)ᴴ * blockKraus ell k) = 1 from blockKraus_channel ell]
    module
  simp only [lindbladGenerator, LinearMap.add_apply, lindbladHamPart_apply,
    lindbladJump_apply, lindbladAnticommPart_apply, zero_mul, mul_zero, sub_self,
    smul_zero, zero_add, hs, hsq, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  module

open scoped Matrix.Norms.Operator in
/-- Two nested commuting projections give two independently computed decay rates. -/
theorem exp_nested_projections (R B : Matrix n n ℂ) (hR : R*R=R) (hB : B*B=B)
    (hRB : R*B=R) (hBR : B*R=R) (c d : ℂ) :
    NormedSpace.exp (c • (1-R) + d • (1-B)) =
      R + Complex.exp c • (B-R) + (Complex.exp c * Complex.exp d) • (1-B) := by
  have hc : Commute (1-R) (1-B) := by
    change (1-R)*(1-B)=(1-B)*(1-R)
    simp [sub_mul, mul_sub, hRB, hBR]
  rw [Matrix.exp_add_of_commute _ _ ((hc.smul_left c).smul_right d),
    GibbsReset.exp_idempotent_complement R hR, GibbsReset.exp_idempotent_complement B hB]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    mul_sub, sub_mul, one_mul, mul_one, hRB]
  module

/-- Exact exponential of the actual concatenated generator, on state matrices. -/
theorem propagator_state (ell : κ → n → ℝ) (w : n → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hn : ∑ i, w i = 1) (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (X : Matrix n n ℂ) :
    lindbladPropagatorAction 0 (jumps ell w γ η) t X = X.trace • density w +
      (Real.exp (-γ*t) : ℂ) • (blockExpectation ell X-X.trace • density w) +
      (Real.exp (-(γ+η)*t) : ℂ) • (X-blockExpectation ell X) := by
  let b := Matrix.stdBasis ℂ n n
  let R := LinearMap.toMatrix b b (GibbsReset.stateReset w)
  let B := LinearMap.toMatrix b b (blockMap ell)
  have hR : R*R=R := by
    rw [← LinearMap.toMatrix_mul]
    exact congrArg (LinearMap.toMatrix b b) (GibbsReset.stateReset_idempotent w hn)
  have hB : B*B=B := by
    rw [← LinearMap.toMatrix_mul]
    exact congrArg (LinearMap.toMatrix b b) (blockMap_idempotent ell)
  have hRB : R*B=R := by
    rw [← LinearMap.toMatrix_mul]
    exact congrArg (LinearMap.toMatrix b b) (stateReset_after_block ell w)
  have hBR : B*R=R := by
    rw [← LinearMap.toMatrix_mul]
    exact congrArg (LinearMap.toMatrix b b) (block_after_stateReset ell w)
  have hL : lindbladLiouvillian 0 (jumps ell w γ η) = (γ:ℂ) • (R-1)+(η:ℂ) • (B-1) := by
    have hg : lindbladGenerator 0 (jumps ell w γ η) =
        (γ:ℂ) • (GibbsReset.stateReset w-1)+(η:ℂ) • (blockMap ell-1) := by
      ext Y i j
      simpa [GibbsReset.stateReset, blockMap_apply] using congrFun (congrFun (generator_state ell w hw hn γ η hγ hη Y) i) j
    simp [lindbladLiouvillian, hg, R, B, b, map_add, map_sub, map_smul]
  have ht : (t:ℂ) • ((γ:ℂ) • (R-1)+(η:ℂ) • (B-1)) =
      ((-γ*t:ℝ):ℂ) • (1-R)+((-η*t:ℝ):ℂ) • (1-B) := by
    simp only [Complex.ofReal_mul, Complex.ofReal_neg]
    module
  unfold lindbladPropagatorAction lindbladPropagator
  rw [hL, ht, exp_nested_projections R B hR hB hRB hBR]
  simp only [map_add, map_smul, map_sub, Matrix.toLin_one, R, B, b, Matrix.toLin_toMatrix,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply,
    ← Complex.ofReal_exp, ← Complex.ofReal_mul, ← Real.exp_add]
  have he : -γ*t+-η*t = -(γ+η)*t := by ring
  rw [he]
  simp only [GibbsReset.stateReset, LinearMap.coe_mk, AddHom.coe_mk, blockMap_apply]

omit [Fintype κ] in
theorem scaled_dual_sandwich {ι : Type*} [Fintype ι] (V : ι → Matrix n n ℂ)
    (a : ℝ) (ha : 0 ≤ a) (X : Matrix n n ℂ) :
    ∑ k, ((Real.sqrt a : ℂ) • V k)ᴴ * X * ((Real.sqrt a : ℂ) • V k) =
      (a : ℂ) • ∑ k, (V k)ᴴ * X * V k := by
  simp only [Matrix.conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
  simp
  simp only [← Complex.ofReal_mul, Real.mul_self_sqrt ha]
  rw [Finset.smul_sum]
  simp

/-- Three explicit Kraus sectors: reset, retained blocks, and identity. -/
def mixtureBranch (ell : κ → n → ℝ) (w : n → ℝ) (a b c : ℝ) :
    Sum (Fin (Fintype.card (n × n))) (Sum (Fin (Fintype.card (Blocks ell))) (Fin 1)) → Matrix n n ℂ
  | .inl k => (Real.sqrt a : ℂ) • GibbsReset.resetKraus w k
  | .inr (.inl k) => (Real.sqrt b : ℂ) • blockKraus ell k
  | .inr (.inr _) => (Real.sqrt c : ℂ) • 1

def mixtureKraus (ell : κ → n → ℝ) (w : n → ℝ) (a b c : ℝ) :=
  fun i : Fin (Fintype.card (Sum (Fin (Fintype.card (n × n))) (Sum (Fin (Fintype.card (Blocks ell))) (Fin 1)))) =>
    mixtureBranch ell w a b c ((Fintype.equivFin _).symm i)

theorem mixture_state (ell : κ → n → ℝ) (w : n → ℝ) (hw : ∀ i, 0 ≤ w i)
    (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (X : Matrix n n ℂ) :
    krausMap (mixtureKraus ell w a b c) X =
      (a:ℂ) • (X.trace • density w)+(b:ℂ) • blockExpectation ell X+(c:ℂ) • X := by
  unfold krausMap mixtureKraus
  rw [(Fintype.equivFin _).symm.sum_comp
    (fun k => mixtureBranch ell w a b c k * X * (mixtureBranch ell w a b c k)ᴴ)]
  simp only [Fintype.sum_sum_type, mixtureBranch, scaled_sandwich _ a ha, scaled_sandwich _ b hb]
  change (a:ℂ) • krausMap (GibbsReset.resetKraus w) X +
    ((b:ℂ) • krausMap (blockKraus ell) X + _) = _
  rw [GibbsReset.reset_state w hw, blockKraus_action]
  simp [Matrix.conjTranspose_smul, smul_smul]
  simp only [Real.mul_self_sqrt hc]
  module

theorem mixture_observable (ell : κ → n → ℝ) (w : n → ℝ) (hw : ∀ i, 0 ≤ w i)
    (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (X : Matrix n n ℂ) :
    Channel.heisenberg (mixtureKraus ell w a b c) X =
      (a:ℂ) • ((density w*X).trace • (1 : Matrix n n ℂ))+(b:ℂ) • blockExpectation ell X+(c:ℂ) • X := by
  unfold Channel.heisenberg mixtureKraus
  rw [(Fintype.equivFin _).symm.sum_comp
    (fun k => (mixtureBranch ell w a b c k)ᴴ * X * mixtureBranch ell w a b c k)]
  simp only [Fintype.sum_sum_type, mixtureBranch, scaled_dual_sandwich _ a ha, scaled_dual_sandwich _ b hb]
  change (a:ℂ) • Channel.heisenberg (GibbsReset.resetKraus w) X +
    ((b:ℂ) • Channel.heisenberg (blockKraus ell) X + _) = _
  rw [GibbsReset.reset_observable w hw, blockKraus_heisenberg]
  simp [Matrix.conjTranspose_smul, smul_smul]
  simp only [Real.mul_self_sqrt hc]
  module

theorem mixture_normalized (ell : κ → n → ℝ) (w : n → ℝ) (hw : ∀ i, 0 ≤ w i) (hn : ∑ i,w i=1)
    (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hs : a+b+c=1) :
    IsKrausChannel (mixtureKraus ell w a b c) := by
  have h := mixture_observable ell w hw a b c ha hb hc 1
  simp only [mul_one, GibbsReset.density_trace, hn, Complex.ofReal_one, one_smul, expectation_one] at h
  have hh : (a:ℂ) • (1 : Matrix n n ℂ)+(b:ℂ) • 1+(c:ℂ) • 1 = 1 := by
    rw [← add_smul, ← add_smul, ← Complex.ofReal_add, ← Complex.ofReal_add, hs]
    simp
  rw [hh] at h
  simpa [Channel.heisenberg, IsKrausChannel] using h

theorem mixture_stationary (ell : κ → n → ℝ) (w : n → ℝ) (hw : ∀ i, 0 ≤ w i) (hn : ∑ i,w i=1)
    (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hs : a+b+c=1) :
    krausMap (mixtureKraus ell w a b c) (density w) = density w := by
  rw [mixture_state ell w hw a b c ha hb hc, GibbsReset.density_trace, hn, block_density]
  simp only [Complex.ofReal_one, one_smul]
  rw [← add_smul, ← add_smul, ← Complex.ofReal_add, ← Complex.ofReal_add, hs]
  simp

/-- Decay multipliers at nonnegative time. -/
def slow (γ t : ℝ) : ℝ := Real.exp (-γ*t)
def fast (γ η t : ℝ) : ℝ := Real.exp (-(γ+η)*t)

theorem fast_le_slow (γ η t : ℝ) (hη : 0 ≤ η) (ht : 0 ≤ t) : fast γ η t ≤ slow γ t := by
  apply Real.exp_le_exp.mpr
  nlinarith

theorem time_coefficients_nonneg (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    0 ≤ 1-slow γ t ∧ 0 ≤ slow γ t-fast γ η t ∧ 0 ≤ fast γ η t :=
  ⟨sub_nonneg.mpr (GibbsReset.exp_rate_le_one γ t hγ ht),
    sub_nonneg.mpr (fast_le_slow γ η t hη ht), (Real.exp_pos _).le⟩

def timeKraus (ell : κ → n → ℝ) (w : n → ℝ) (γ η t : ℝ) :=
  mixtureKraus ell w (1-slow γ t) (slow γ t-fast γ η t) (fast γ η t)

theorem time_normalized (ell : κ → n → ℝ) (w : n → ℝ) (hw : ∀ i, 0 ≤ w i) (hn : ∑ i,w i=1)
    (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) : IsKrausChannel (timeKraus ell w γ η t) := by
  obtain ⟨ha,hb,hc⟩ := time_coefficients_nonneg γ η t hγ hη ht
  exact mixture_normalized ell w hw hn _ _ _ ha hb hc (by ring)

theorem time_stationary (ell : κ → n → ℝ) (w : n → ℝ) (hw : ∀ i, 0 ≤ w i) (hn : ∑ i,w i=1)
    (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) : krausMap (timeKraus ell w γ η t) (density w) = density w := by
  obtain ⟨ha,hb,hc⟩ := time_coefficients_nonneg γ η t hγ hη ht
  exact mixture_stationary ell w hw hn _ _ _ ha hb hc (by ring)

theorem time_state_eq_propagator (ell : κ → n → ℝ) (w : n → ℝ) (hw : ∀ i, 0 ≤ w i) (hn : ∑ i,w i=1)
    (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (X : Matrix n n ℂ) :
    krausMap (timeKraus ell w γ η t) X = lindbladPropagatorAction 0 (jumps ell w γ η) t X := by
  obtain ⟨ha,hb,hc⟩ := time_coefficients_nonneg γ η t hγ hη ht
  rw [timeKraus, mixture_state ell w hw _ _ _ ha hb hc, propagator_state ell w hw hn γ η t hγ hη]
  simp only [slow, fast, Complex.ofReal_sub, Complex.ofReal_one]
  module

theorem propagator_trace_duality (ell : κ → n → ℝ) (w : n → ℝ) (hw : ∀ i, 0 ≤ w i) (hn : ∑ i,w i=1)
    (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (S X : Matrix n n ℂ) :
    (S * Channel.heisenberg (timeKraus ell w γ η t) X).trace =
      (lindbladPropagatorAction 0 (jumps ell w γ η) t S * X).trace := by
  rw [Channel.trace_duality, time_state_eq_propagator ell w hw hn γ η t hγ hη ht]

section Quotient
variable (ell : κ → n → ℝ) (w : n → ℝ) (hw : ∀ i, 0 < w i) (hn : ∑ i,w i=1)
local notation "Q" => GibbsReset.scalarProjection w hw hn
local notation "B" => projection w hw ell

def evolution (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    WeightedSpace w hw →L[ℂ] WeightedSpace w hw :=
  Channel.quotientChannel (density_posDef w hw).posSemidef (timeKraus ell w γ η t)
    (time_normalized ell w (fun i => (hw i).le) hn γ η t hγ hη ht)
    (time_stationary ell w (fun i => (hw i).le) hn γ η t hγ hη ht)

theorem evolution_apply (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (z : WeightedSpace w hw) :
    evolution ell w hw hn γ η t hγ hη ht z = Q z+(slow γ t:ℂ) • (B z-Q z)+(fast γ η t:ℂ) • (z-B z) := by
  obtain ⟨X,rfl⟩ := observable_surjective (density_posDef w hw).posSemidef z
  obtain ⟨ha,hb,hc⟩ := time_coefficients_nonneg γ η t hγ hη ht
  rw [evolution, Channel.quotientChannel_observable, timeKraus,
    mixture_observable ell w (fun i => (hw i).le) _ _ _ ha hb hc,
    GibbsReset.scalarProjection_observable, projection_observable]
  change (observableLinear (density_posDef w hw).posSemidef) (_+_+_) = _
  rw [map_add, map_add]
  simp only [map_smul]
  change ((1-slow γ t:ℝ):ℂ) • ((density w*X).trace • observable (density_posDef w hw).posSemidef 1) +
    ((slow γ t-fast γ η t:ℝ):ℂ) • observable (density_posDef w hw).posSemidef (blockExpectation ell X) +
    (fast γ η t:ℂ) • observable (density_posDef w hw).posSemidef X = _
  simp only [Complex.ofReal_sub, Complex.ofReal_one]
  module

theorem projection_on_scalar (z : WeightedSpace w hw) : B (Q z)=Q z := by
  have h := GibbsReset.block_after_scalarProjection w hw hn ell
  exact congrArg (fun T : WeightedSpace w hw →L[ℂ] _ => T z) h

theorem scalar_on_projection (z : WeightedSpace w hw) : Q (B z)=Q z := by
  have h := GibbsReset.scalarProjection_after_block w hw hn ell
  exact congrArg (fun T : WeightedSpace w hw →L[ℂ] _ => T z) h

theorem scalar_block_inner (z : WeightedSpace w hw) : ⟪Q z,B z⟫_ℂ=⟪Q z,z⟫_ℂ := by
  have h := projection_symmetric ell w hw (Q z) z
  change ⟪B (Q z),z⟫_ℂ=⟪Q z,B z⟫_ℂ at h
  rw [projection_on_scalar] at h
  exact h.symm

/-- Scalar, centered within-block, and cross-block components are pairwise orthogonal. -/
theorem three_components_orthogonal (z : WeightedSpace w hw) :
    ⟪Q z,B z-Q z⟫_ℂ=0 ∧ ⟪Q z,z-B z⟫_ℂ=0 ∧ ⟪B z-Q z,z-B z⟫_ℂ=0 := by
  have hq := scalar_block_inner ell w hw hn z
  have hqq := GibbsReset.scalarProjection_inner w hw hn z
  have hb := projection_error_orthogonal ell w hw z
  constructor
  · rw [inner_sub_right, hq, hqq, sub_self]
  constructor
  · rw [inner_sub_right, hq, sub_self]
  · rw [inner_sub_left, hb, inner_sub_right, hq, sub_self, sub_self]

theorem evolution_error (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (z : WeightedSpace w hw) :
    evolution ell w hw hn γ η t hγ hη ht z-Q z =
      (slow γ t:ℂ) • (B z-Q z)+(fast γ η t:ℂ) • (z-B z) := by
  rw [evolution_apply]
  abel

theorem error_pythagoras (z : WeightedSpace w hw) : ‖z-Q z‖^2=‖B z-Q z‖^2+‖z-B z‖^2 := by
  have h := norm_add_sq (𝕜 := ℂ) (B z-Q z) (z-B z)
  rw [(three_components_orthogonal ell w hw hn z).2.2] at h
  have he : B z-Q z+(z-B z)=z-Q z := by abel
  simpa only [he, map_zero, mul_zero, add_zero] using h

theorem evolution_error_sq (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (z : WeightedSpace w hw) :
    ‖evolution ell w hw hn γ η t hγ hη ht z-Q z‖^2 =
      (slow γ t)^2*‖B z-Q z‖^2+(fast γ η t)^2*‖z-B z‖^2 := by
  rw [evolution_error, norm_add_sq (𝕜 := ℂ)]
  simp only [inner_smul_left, inner_smul_right, (three_components_orthogonal ell w hw hn z).2.2,
    mul_zero, map_zero, add_zero, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), slow, fast]
  ring

/-- Exact squared error, displaying both physical decay rates explicitly. -/
theorem evolution_two_rate_error (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (z : WeightedSpace w hw) :
    ‖evolution ell w hw hn γ η t hγ hη ht z-Q z‖^2 =
      Real.exp (-2*γ*t)*‖B z-Q z‖^2+Real.exp (-2*(γ+η)*t)*‖z-B z‖^2 := by
  rw [evolution_error_sq]
  have hs : (slow γ t)^2=Real.exp (-2*γ*t) := by
    rw [slow, pow_two, ← Real.exp_add]
    congr 1
    ring
  have hf : (fast γ η t)^2=Real.exp (-2*(γ+η)*t) := by
    rw [fast, pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hs,hf]

theorem evolution_convex (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    evolution ell w hw hn γ η t hγ hη ht =
      ((1-slow γ t:ℝ):ℂ) • Q+((slow γ t-fast γ η t:ℝ):ℂ) • B+
      (fast γ η t:ℂ) • (1 : WeightedSpace w hw →L[ℂ] _) := by
  ext z
  simp only [evolution_apply, _root_.add_apply, _root_.smul_apply,
    one_apply_eq_self, Complex.ofReal_sub, Complex.ofReal_one]
  module

theorem evolution_positive (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    (evolution ell w hw hn γ η t hγ hη ht).IsPositive := by
  rw [evolution_convex]
  obtain ⟨ha,hb,hc⟩ := time_coefficients_nonneg γ η t hγ hη ht
  exact (((GibbsReset.scalarProjection_positive w hw hn).smul_of_nonneg (by exact_mod_cast ha)).add
    ((projection_positive ell w hw).smul_of_nonneg (by exact_mod_cast hb))).add
    (ContinuousLinearMap.isPositive_one.smul_of_nonneg (by exact_mod_cast hc))

theorem evolution_selfAdjoint (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    IsSelfAdjoint (evolution ell w hw hn γ η t hγ hη ht) :=
  (evolution_positive ell w hw hn γ η t hγ hη ht).isSelfAdjoint

theorem evolution_error_sq_le (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (z : WeightedSpace w hw) :
    ‖evolution ell w hw hn γ η t hγ hη ht z-Q z‖^2 ≤ (slow γ t)^2*‖z-Q z‖^2 := by
  rw [evolution_error_sq, error_pythagoras ell w hw hn]
  have hh := fast_le_slow γ η t hη ht
  have hfast : 0 ≤ fast γ η t := (Real.exp_pos _).le
  have hslow : 0 ≤ slow γ t := (Real.exp_pos _).le
  have hs : (fast γ η t)^2 ≤ (slow γ t)^2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg ‖z-B z‖)]

theorem evolution_fixed_iff (γ η t : ℝ) (hγ : 0 < γ) (hη : 0 ≤ η) (ht : 0 < t) (z : WeightedSpace w hw) :
    evolution ell w hw hn γ η t hγ.le hη ht.le z=z ↔ Q z=z := by
  constructor
  · intro hz
    have h := evolution_error_sq_le ell w hw hn γ η t hγ.le hη ht.le z
    rw [hz] at h
    have hs : slow γ t < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
    have hp : 0 < slow γ t := Real.exp_pos _
    have hsq : (slow γ t)^2 < 1 := by nlinarith
    have he : ‖z-Q z‖=0 := by
      have hh : (1-(slow γ t)^2)*‖z-Q z‖^2 ≤ 0 := by nlinarith
      have hh' : ‖z-Q z‖^2 ≤ 0 := (mul_le_mul_iff_of_pos_left (sub_pos.mpr hsq)).mp (by simpa using hh)
      nlinarith [sq_nonneg ‖z-Q z‖, norm_nonneg (z-Q z)]
    exact (sub_eq_zero.mp (norm_eq_zero.mp he)).symm
  · intro hq
    have hb := projection_on_scalar ell w hw hn z
    rw [hq] at hb
    simp [evolution_apply, hq, hb]

theorem evolution_scalar_fixed_iff (γ η t : ℝ) (hγ : 0 < γ) (hη : 0 ≤ η) (ht : 0 < t) (z : WeightedSpace w hw) :
    evolution ell w hw hn γ η t hγ.le hη ht.le z=z ↔
      ∃ c : ℂ, z=c • observable (density_posDef w hw).posSemidef 1 := by
  rw [evolution_fixed_iff ell w hw hn γ η t hγ hη ht, GibbsReset.scalarProjection_fixed_iff]

theorem evolution_zero_reset (η t : ℝ) (hη : 0 ≤ η) (ht : 0 ≤ t) (z : WeightedSpace w hw) :
    evolution ell w hw hn 0 η t (by norm_num) hη ht z = B z+(slow η t:ℂ) • (z-B z) := by
  rw [evolution_apply]
  simp only [slow, fast, neg_zero, zero_mul, Real.exp_zero, Complex.ofReal_one, one_smul, zero_add]
  abel

theorem evolution_zero_dephasing (γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) :
    evolution ell w hw hn γ 0 t hγ (by norm_num) ht = GibbsReset.evolution w hw hn γ t hγ ht := by
  ext z
  rw [evolution_apply, GibbsReset.evolution_apply]
  simp only [slow, fast, add_zero]
  module

theorem evolution_zero_rates (t : ℝ) (ht : 0 ≤ t) :
    evolution ell w hw hn 0 0 t (by norm_num) (by norm_num) ht=1 := by
  rw [evolution_zero_dephasing, GibbsReset.evolution_zero_rate]

theorem zero_reset_fixed_iff (η t : ℝ) (hη : 0 < η) (ht : 0 < t) (z : WeightedSpace w hw) :
    evolution ell w hw hn 0 η t (by norm_num) hη.le ht.le z=z ↔ B z=z := by
  have he : evolution ell w hw hn 0 η t (by norm_num) hη.le ht.le z-B z=(slow η t:ℂ) • (z-B z) := by
    rw [evolution_zero_reset]
    abel
  constructor
  · intro hz
    rw [hz] at he
    have hn := congrArg norm he
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (show 0 < slow η t from Real.exp_pos _)] at hn
    have hs : slow η t<1 := Real.exp_lt_one_iff.mpr (by nlinarith)
    have hz0 : ‖z-B z‖=0 := by nlinarith [norm_nonneg (z-B z)]
    exact (sub_eq_zero.mp (norm_eq_zero.mp hz0)).symm
  · intro hb
    simp [evolution_zero_reset, hb]

theorem evolution_tendsto (γ η : ℝ) (hγ : 0 < γ) (hη : 0 ≤ η) (z : WeightedSpace w hw) :
    Tendsto (fun t : NNReal => evolution ell w hw hn γ η t hγ.le hη t.property z)
      atTop (𝓝 (Q z)) := by
  have decay (a : ℝ) (ha : 0 < a) :
      Tendsto (fun t : NNReal => (Real.exp (-a*(t:ℝ)):ℂ)) atTop (𝓝 0) := by
    have hc : Tendsto (fun t : NNReal => (t:ℝ)) atTop atTop := NNReal.tendsto_coe_atTop.mpr tendsto_id
    have hm := Filter.Tendsto.const_mul_atTop ha hc
    have he : Tendsto (fun t : NNReal => Real.exp (-a*(t:ℝ))) atTop (𝓝 0) := by
      simpa only [Function.comp_def, neg_mul] using Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hm)
    simpa only [Function.comp_def, Complex.ofReal_zero] using Complex.continuous_ofReal.continuousAt.tendsto.comp he
  have hs := decay γ hγ
  have hf := decay (γ+η) (by linarith)
  simpa only [evolution_apply, slow, fast, zero_smul, add_zero] using
    ((tendsto_const_nhds.add (hs.smul_const (B z-Q z))).add (hf.smul_const (z-B z)))

theorem zero_reset_tendsto (η : ℝ) (hη : 0 < η) (z : WeightedSpace w hw) :
    Tendsto (fun t : NNReal => evolution ell w hw hn 0 η t (by norm_num) hη.le t.property z)
      atTop (𝓝 (B z)) := by
  have hc : Tendsto (fun t : NNReal => (t:ℝ)) atTop atTop := NNReal.tendsto_coe_atTop.mpr tendsto_id
  have hm := Filter.Tendsto.const_mul_atTop hη hc
  have he : Tendsto (fun t : NNReal => Real.exp (-η*(t:ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul] using Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hm)
  have hex : Tendsto (fun t : NNReal => (Real.exp (-η*(t:ℝ)):ℂ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.ofReal_zero] using Complex.continuous_ofReal.continuousAt.tendsto.comp he
  simpa only [evolution_zero_reset, slow, zero_smul, add_zero] using
    (tendsto_const_nhds.add (hex.smul_const (z-B z)))

end Quotient

/-- The normalized state is stationary for the actual combined generator. -/
theorem generator_stationary (ell : κ → n → ℝ) (w : n → ℝ) (hw : ∀ i, 0 ≤ w i) (hn : ∑ i,w i=1)
    (γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) : lindbladGenerator 0 (jumps ell w γ η) (density w)=0 := by
  rw [generator_state ell w hw hn γ η hγ hη, GibbsReset.density_trace, hn, block_density]
  simp

theorem stationary_trace_one_iff (ell : κ → n → ℝ) (w : n → ℝ) (hw : ∀ i, 0 ≤ w i) (hn : ∑ i,w i=1)
    (γ η : ℝ) (hγ : 0 < γ) (hη : 0 ≤ η) (X : Matrix n n ℂ) (hX : X.trace=1) :
    lindbladGenerator 0 (jumps ell w γ η) X=0 ↔ X=density w := by
  constructor
  · intro h
    rw [generator_state ell w hw hn γ η hγ.le hη, hX, one_smul] at h
    have hb := congrArg (blockMap ell) h
    simp only [map_add, map_smul, map_sub, map_zero, blockMap_apply, block_density,
      blockExpectation_idempotent, sub_self, smul_zero, add_zero] at hb
    have hg : (γ:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ.ne'
    have hBX : blockExpectation ell X=density w := (sub_eq_zero.mp ((smul_eq_zero.mp hb).resolve_left hg)).symm
    rw [hBX, ← add_smul, ← Complex.ofReal_add] at h
    have hsum : ((γ+η:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
    exact (sub_eq_zero.mp ((smul_eq_zero.mp h).resolve_left hsum)).symm
  · rintro rfl
    exact generator_stationary ell w hw hn γ η hγ.le hη

/-- Positive reset rate removes every trace-one stationary state except the prescribed density. -/
theorem propagator_trace_one_fixed_iff (ell : κ → n → ℝ) (w : n → ℝ) (hw : ∀ i, 0 ≤ w i) (hn : ∑ i,w i=1)
    (γ η t : ℝ) (hγ : 0 < γ) (hη : 0 ≤ η) (ht : 0 < t) (X : Matrix n n ℂ) (hX : X.trace=1) :
    lindbladPropagatorAction 0 (jumps ell w γ η) t X=X ↔ X=density w := by
  constructor
  · intro hz
    rw [propagator_state ell w hw hn γ η t hγ.le hη, hX, one_smul] at hz
    have hb := congrArg (blockMap ell) hz
    simp only [map_add, map_smul, map_sub, blockMap_apply, block_density,
      blockExpectation_idempotent, sub_self, smul_zero, add_zero] at hb
    have hs : (1-(Real.exp (-γ*t):ℂ)) ≠ 0 := by
      have hpos : 0 < 1-Real.exp (-γ*t) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith))
      exact_mod_cast hpos.ne'
    have he : (1-(Real.exp (-γ*t):ℂ)) • (density w-blockExpectation ell X)=0 := by
      have hh : (1-(Real.exp (-γ*t):ℂ)) • (density w-blockExpectation ell X) =
          (density w+(Real.exp (-γ*t):ℂ) • (blockExpectation ell X-density w))-blockExpectation ell X := by module
      rw [hh,hb,sub_self]
    have hBX : blockExpectation ell X=density w := (sub_eq_zero.mp ((smul_eq_zero.mp he).resolve_left hs)).symm
    rw [hBX, sub_self, smul_zero, add_zero] at hz
    have hf : (1-(Real.exp (-(γ+η)*t):ℂ)) ≠ 0 := by
      have hpos : 0 < 1-Real.exp (-(γ+η)*t) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith))
      exact_mod_cast hpos.ne'
    have he' : (1-(Real.exp (-(γ+η)*t):ℂ)) • (density w-X)=0 := by
      have hh : (1-(Real.exp (-(γ+η)*t):ℂ)) • (density w-X) =
          (density w+(Real.exp (-(γ+η)*t):ℂ) • (X-density w))-X := by module
      rw [hh,hz,sub_self]
    exact (sub_eq_zero.mp ((smul_eq_zero.mp he').resolve_left hf)).symm
  · rintro rfl
    rw [propagator_state ell w hw hn γ η t hγ.le hη, GibbsReset.density_trace, hn, block_density]
    simp

omit [Fintype n] in
theorem block_diagonal (ell : κ → n → ℝ) (d : n → ℂ) : blockExpectation ell (diagonal d)=diagonal d := by
  ext i j
  by_cases h : i=j <;> simp [blockExpectation, h]

/-- Uniform block noise leaves population relaxation at the reset rate. -/
theorem propagator_diagonal (ell : κ → n → ℝ) (w : n → ℝ) (hw : ∀ i, 0 ≤ w i) (hn : ∑ i,w i=1)
    (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (d : n → ℂ) :
    lindbladPropagatorAction 0 (jumps ell w γ η) t (diagonal d) =
      lindbladPropagatorAction 0 (GibbsReset.jumps w γ) t (diagonal d) := by
  rw [propagator_state ell w hw hn γ η t hγ hη, GibbsReset.propagator_state w hw hn γ hγ,
    block_diagonal, sub_self, smul_zero, add_zero]
  module

theorem three_population_transfer (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) :
    lindbladPropagatorAction 0 (jumps duplicateJumps GibbsReset.threeWeights γ η) t GibbsReset.concentrated 1 1 =
      ((1-Real.exp (-γ*t))/3 : ℝ) := by
  rw [GibbsReset.concentrated, propagator_diagonal duplicateJumps GibbsReset.threeWeights
    (fun i => (GibbsReset.threeWeights_pos i).le) GibbsReset.threeWeights_normalized γ η t hγ hη]
  exact GibbsReset.population_transfer γ t hγ

theorem three_population_transfer_pos (γ η t : ℝ) (hγ : 0 < γ) (hη : 0 ≤ η) (ht : 0 < t) :
    0 < (lindbladPropagatorAction 0 (jumps duplicateJumps GibbsReset.threeWeights γ η) t GibbsReset.concentrated 1 1).re := by
  rw [three_population_transfer γ η t hγ.le hη, Complex.ofReal_re]
  exact div_pos (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith))) (by norm_num)

theorem three_centered_block_fixed :
    projection GibbsReset.threeWeights GibbsReset.threeWeights_pos duplicateJumps GibbsReset.centered = GibbsReset.centered := by
  rw [GibbsReset.centered, projection_observable, GibbsReset.centeredDiagonal, block_diagonal]

theorem three_centered_decay (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    ‖evolution duplicateJumps GibbsReset.threeWeights GibbsReset.threeWeights_pos GibbsReset.threeWeights_normalized
      γ η t hγ hη ht GibbsReset.centered‖ = slow γ t*‖GibbsReset.centered‖ := by
  rw [evolution_apply, three_centered_block_fixed, GibbsReset.centered_projection_zero]
  simp only [sub_zero, sub_self, smul_zero, add_zero, zero_add, norm_smul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (show 0 < slow γ t from Real.exp_pos _)]

/-- Cross-block coherence in the same nonuniform faithful space. -/
def crossCoherence : WeightedSpace GibbsReset.threeWeights GibbsReset.threeWeights_pos :=
  observable (density_posDef GibbsReset.threeWeights GibbsReset.threeWeights_pos).posSemidef (Matrix.single 0 2 1)

theorem crossCoherence_norm_pos : 0 < ‖crossCoherence‖ :=
  norm_pos_iff.mpr (observable_single_nonzero GibbsReset.threeWeights GibbsReset.threeWeights_pos 0 2)

theorem crossCoherence_block_zero :
    projection GibbsReset.threeWeights GibbsReset.threeWeights_pos duplicateJumps crossCoherence=0 := by
  rw [crossCoherence, projection_observable]
  have he : blockExpectation duplicateJumps (Matrix.single 0 2 (1:ℂ))=0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [blockExpectation, rate, duplicateJumps, Fin.sum_univ_one, Matrix.single_apply, Fin.ext_iff]
  rw [he]
  exact map_zero (observableLinear (density_posDef GibbsReset.threeWeights GibbsReset.threeWeights_pos).posSemidef)

theorem crossCoherence_scalar_zero :
    GibbsReset.scalarProjection GibbsReset.threeWeights GibbsReset.threeWeights_pos GibbsReset.threeWeights_normalized crossCoherence=0 := by
  rw [crossCoherence, GibbsReset.scalarProjection_observable]
  have he : (density GibbsReset.threeWeights * Matrix.single 0 2 (1:ℂ)).trace=0 := by
    rw [Matrix.trace_mul_single]
    norm_num [density, Matrix.diagonal_apply, Fin.ext_iff]
  rw [he, zero_smul]

theorem crossCoherence_decay (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    ‖evolution duplicateJumps GibbsReset.threeWeights GibbsReset.threeWeights_pos GibbsReset.threeWeights_normalized
      γ η t hγ hη ht crossCoherence‖ = fast γ η t*‖crossCoherence‖ := by
  rw [evolution_apply, crossCoherence_block_zero, crossCoherence_scalar_zero]
  simp only [sub_zero, smul_zero, zero_add, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (show 0 < fast γ η t from Real.exp_pos _)]

theorem distinct_decay_rates (γ η t : ℝ) (hη : 0 < η) (ht : 0 < t) : fast γ η t < slow γ t := by
  apply Real.exp_lt_exp.mpr
  nlinarith

theorem zero_reset_stationary_iff (ell : κ → n → ℝ) (w : n → ℝ) (hw : ∀ i, 0 ≤ w i) (hn : ∑ i,w i=1)
    (η : ℝ) (hη : 0 < η) (X : Matrix n n ℂ) :
    lindbladGenerator 0 (jumps ell w 0 η) X=0 ↔ blockExpectation ell X=X := by
  rw [generator_state ell w hw hn 0 η (by norm_num) hη.le]
  simp only [Complex.ofReal_zero, zero_smul, zero_add, smul_eq_zero,
    Complex.ofReal_eq_zero, hη.ne', false_or, sub_eq_zero]

theorem zero_rates_generator (ell : κ → n → ℝ) (w : n → ℝ) (hw : ∀ i, 0 ≤ w i) (hn : ∑ i,w i=1)
    (X : Matrix n n ℂ) : lindbladGenerator 0 (jumps ell w 0 0) X=0 := by
  rw [generator_state ell w hw hn 0 0 (by norm_num) (by norm_num)]
  simp

theorem three_centered_strict_decay (γ η t : ℝ) (hγ : 0 < γ) (hη : 0 ≤ η) (ht : 0 < t) :
    ‖evolution duplicateJumps GibbsReset.threeWeights GibbsReset.threeWeights_pos GibbsReset.threeWeights_normalized
      γ η t hγ.le hη ht.le GibbsReset.centered‖ < ‖GibbsReset.centered‖ := by
  rw [three_centered_decay]
  exact mul_lt_of_lt_one_left GibbsReset.centered_norm_pos (Real.exp_lt_one_iff.mpr (by nlinarith))

theorem crossCoherence_strict_decay (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (hs : 0 < γ+η) (ht : 0 < t) :
    ‖evolution duplicateJumps GibbsReset.threeWeights GibbsReset.threeWeights_pos GibbsReset.threeWeights_normalized
      γ η t hγ hη ht.le crossCoherence‖ < ‖crossCoherence‖ := by
  rw [crossCoherence_decay]
  exact mul_lt_of_lt_one_left crossCoherence_norm_pos (Real.exp_lt_one_iff.mpr (by nlinarith))

end SKEFTHawking.FinitePositiveKernel.GibbsBlockRelaxation
