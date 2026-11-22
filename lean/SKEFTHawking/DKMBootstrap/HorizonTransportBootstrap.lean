/- Conditional scalar MIR and abstract growth predicates.

HorizonTransportUniquenessBound is a legacy name for IsMIRBound, a single
inequality, not uniqueness. The all-one witness proves1/2 <= 1.
IsSuperFactorialUnbounded is an abstract premise; its contradiction with
a supplied factorial-power bound is conditional. PlatformBimodalOutcome
is inclusive OR, with no exclusivity or universal physical-platform theorem.
Actual material correlators, parameters, physical growth, horizon transport
and uniqueness, including the distinct BEC Hamiltonian task, remain BUILD. -/
import SKEFTHawking.DKMBootstrap.E1E2CrossBridge

namespace SKEFTHawking.DKMBootstrap

/-! ## Transparent scalar MIR alias. -/

/-- Exactly mirConst <= sqrt(tau*D)/a. This alias asserts no coefficient uniqueness or physical applicability. -/
abbrev HorizonTransportUniquenessBound
    (p : DKMParameters) (mirConst : ℝ) : Prop :=
  IsMIRBound p mirConst

/-! ## Normalized scalar witness; no material identification. -/

/-- All-one parameters reduce this theorem to1/2 <= 1. A smaller lower-bound scalar weakens the same inequality; physical parameter matching is separate. -/
theorem horizon_transport_uniqueness_graphene_witness_one_half :
    HorizonTransportUniquenessBound grapheneDKMParameters (1/2) := by
  -- HorizonTransportUniquenessBound is an abbrev for IsMIRBound; show
  -- the underlying type so `unfold IsMIRBound` engages, then simp.
  show IsMIRBound grapheneDKMParameters (1/2)
  unfold IsMIRBound DKMParameters.collectiveMeanFreePath
  simp [grapheneDKMParameters]
  -- After simp the goal reduces to 2⁻¹ ≤ 1; discharge by norm_num.
  norm_num

/-! ## Conditional contradiction for abstract superfactorial sequences. -/

/-- For each positive epsilon and reference norm, some sequence value exceeds the factorial-power product. No physical sequence is identified here. -/
def IsSuperFactorialUnbounded (commutatorNorm : ℕ → ℝ) : Prop :=
  ∀ ε n0Norm : ℝ, 0 < ε → 0 < n0Norm →
    ∃ κ : ℕ, (Nat.factorial κ : ℝ) * ε^κ * n0Norm < commutatorNorm κ

/-- A sequence satisfying the supplied superfactorial premise cannot satisfy the given positive factorial-power bound. -/
theorem sharpened_no_go_super_factorial
    (commutatorNorm : ℕ → ℝ) (ε n0Norm : ℝ)
    (hε : 0 < ε) (hn : 0 < n0Norm)
    (h_unbd : IsSuperFactorialUnbounded commutatorNorm) :
    ¬ HasOperatorGrowthBound commutatorNorm ε n0Norm := by
  intro h_growth
  obtain ⟨κ, hκ⟩ := h_unbd ε n0Norm hε hn
  -- hκ : (Nat.factorial κ : ℝ) * ε^κ * n0Norm < commutatorNorm κ
  -- h_growth κ : commutatorNorm κ ≤ (Nat.factorial κ : ℝ) * ε^κ * n0Norm
  exact absurd (h_growth κ) (not_le.mpr hκ)

/-! ## Inclusive disjunction; no exclusive platform classification. -/

/-- Inclusive OR of the MIR inequality and the abstract growth predicate. Neither exclusivity nor applicability to every physical platform is proved. -/
def PlatformBimodalOutcome
    (p : DKMParameters) (mirConst : ℝ) (commutatorNorm : ℕ → ℝ) : Prop :=
  HorizonTransportUniquenessBound p mirConst ∨
  IsSuperFactorialUnbounded commutatorNorm

/-- Left-branch witness for the normalized tuple and prescribed zero sequence. -/
theorem graphene_bimodal_outcome :
    PlatformBimodalOutcome grapheneDKMParameters (1/2) (fun _ => 0) := by
  left
  exact horizon_transport_uniqueness_graphene_witness_one_half

/-! ## Scope retained.
The scalar inequality, normalized witness and conditional contradiction are
useful substrate results. They do not establish actual graphene uniqueness
or a physical BEC no-go. The full correlator/state/window, growth, transport
and material/horizon construction remains BUILD. -/

end SKEFTHawking.DKMBootstrap
