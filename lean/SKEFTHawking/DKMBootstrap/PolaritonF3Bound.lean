/- Conditional growth implication and normalized MIR witnesses.

The growth premise below is supplied, not derived from pump energy or the
scalar pump comparison. sqrt(n_max) is an adopted scalar definition, not a
calibrated coupling or physical growth constant. Inheritance selects the
left side of an inclusive OR from all-one parameters, independently of
the growth arguments. Legacy names do not prove physical uniqueness.
The numerical companion computes incident photon equivalents only. Actual
pump/state/modal/reservoir/dephasing-to-growth, transport and uniqueness
remain BUILD; the distinct actual BEC growth task also remains required. -/
import SKEFTHawking.DKMBootstrap.HorizonTransportBootstrap

namespace SKEFTHawking.DKMBootstrap

open Real

/-! ## Adopted scalar and supplied growth predicate. -/

/-- Adopted scalar sqrt(n_max). No physical coupling/domain normalization is derived. -/
noncomputable def polaritonOperatorGrowthScale (n_max : ℝ) : ℝ :=
  Real.sqrt n_max

/-- The full HasOperatorGrowthBound premise at the adopted scalar and reference1. -/
def IsBoundedByPolaritonPumpScale (commutatorNorm : ℕ → ℝ) (n_max : ℝ) : Prop :=
  HasOperatorGrowthBound commutatorNorm (polaritonOperatorGrowthScale n_max) 1

/-- Scalar comparison pump < threshold only; it is not used to derive growth. -/
def IsPolaritonPumpBelowThreshold (pump threshold : ℝ) : Prop :=
  pump < threshold

/-! ## Conditional incompatibility of supplied growth with superfactorial growth. -/

/-- Given positive n_max and the full growth premise, refute IsSuperFactorialUnbounded. The legacy theorem name adds no pump-to-growth derivation. -/
theorem polariton_dkm_f3_holds_at_pump_below_threshold
    {commutatorNorm : ℕ → ℝ} {n_max : ℝ} (hn : 0 < n_max)
    (h : IsBoundedByPolaritonPumpScale commutatorNorm n_max) :
    ¬ IsSuperFactorialUnbounded commutatorNorm := by
  intro h_unbd
  -- Pick ε := √n_max, n0Norm := 1; both are strictly positive.
  have hε : 0 < polaritonOperatorGrowthScale n_max :=
    Real.sqrt_pos.mpr hn
  obtain ⟨κ, hκ⟩ :=
    h_unbd (polaritonOperatorGrowthScale n_max) 1 hε one_pos
  -- hκ : κ! · ε^κ · 1 < commutatorNorm κ
  -- h κ: commutatorNorm κ ≤ κ! · ε^κ · 1
  exact absurd (h κ) (not_le.mpr hκ)

/-! ## All-one normalized MIR witness, separate from physical transport.
The ratio is1 and the scalar1/2 is a lower-bound witness on that same tuple.
Numerical ordering against about0.0756 does not transfer a theorem to a material. -/

/-- Normalized all-one inequality 1/2 <= 1. No physical uniqueness follows. -/
theorem horizon_transport_uniqueness_polariton_witness_one_half :
    HorizonTransportUniquenessBound polaritonDKMParameters (1/2) := by
  show IsMIRBound polaritonDKMParameters (1/2)
  unfold IsMIRBound DKMParameters.collectiveMeanFreePath
  simp [polaritonDKMParameters]
  norm_num

/-- Select the inclusive OR left branch from the normalized witness. The supplied _hn/_h arguments are unused by this proof. -/
theorem polariton_inherits_graphene_uniqueness_result
    {commutatorNorm : ℕ → ℝ} {n_max : ℝ} (_hn : 0 < n_max)
    (_h : IsBoundedByPolaritonPumpScale commutatorNorm n_max) :
    PlatformBimodalOutcome polaritonDKMParameters (1/2) commutatorNorm := by
  left
  exact horizon_transport_uniqueness_polariton_witness_one_half

/-- Logical equivalence of two normalized MIR witnesses with the same fields. -/
theorem polariton_mir_witness_eq_graphene_mir_witness :
    HorizonTransportUniquenessBound polaritonDKMParameters (1/2) ↔
    HorizonTransportUniquenessBound grapheneDKMParameters (1/2) := by
  -- Both reduce to the same numerical inequality `1/2 ≤ √(1·1)/1`.
  constructor
  · intro _h
    exact horizon_transport_uniqueness_graphene_witness_one_half
  · intro _h
    exact horizon_transport_uniqueness_polariton_witness_one_half

/-! ## Scope retained.
These definitions and conditional proofs do not resolve a physical platform
branch. Incident photon-equivalent arithmetic and the adopted1e6 proxy do
not establish a hard cutoff or actual commutator growth. Physical pump,
state, dephasing, reservoir, mode, transport/MIR/uniqueness and BEC duties remain BUILD. -/

end SKEFTHawking.DKMBootstrap
