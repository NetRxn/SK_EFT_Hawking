/- Legacy platform tags and normalized positive parameter witnesses.

All three parameter records below set every real field to1. Their names
do not calibrate a device, lattice spacing, state, transport or KMS law.
The classifier is a String-to-constructor function; rfl and constructor
distinctness prove label facts only. Physical KMS/state and correlator
identification, transport/growth, polariton pump/dephasing/reservoir and
the distinct actual BEC construction remain BUILD. -/
import SKEFTHawking.DKMBootstrap.SKEFTSpecialization

namespace SKEFTHawking.DKMBootstrap

/-! ## Legacy three-way classifier labels, not a theorem about a quantum state. -/

/-- Three syntactic labels retained for compatibility; physical KMS needs a state/evolution proof. -/
inductive PlatformKMSQuality
  | Strong          -- legacy graphene label
  | Approximate     -- legacy BEC label
  | EffectiveOnly   -- legacy polariton label
  deriving DecidableEq, Repr

/-! ## All-one positive parameter records, not material data. -/

/-- All-one graphene-named tuple. Physical parameters are not supplied by this record. -/
noncomputable def grapheneDKMParameters : DKMParameters where
  τ := 1
  D := 1
  χ := 1
  a := 1
  ε := 1
  τ_pos := by norm_num
  D_pos := by norm_num
  χ_pos := by norm_num
  a_pos := by norm_num
  ε_pos := by norm_num

/-- All-one BEC-named tuple. It is not an acoustic-Hawking state or Hamiltonian. -/
noncomputable def becDKMParameters : DKMParameters where
  τ := 1
  D := 1
  χ := 1
  a := 1
  ε := 1
  τ_pos := by norm_num
  D_pos := by norm_num
  χ_pos := by norm_num
  a_pos := by norm_num
  ε_pos := by norm_num

/-- All-one polariton-named tuple. No driven state or physical KMS law is constructed. -/
noncomputable def polaritonDKMParameters : DKMParameters where
  τ := 1
  D := 1
  χ := 1
  a := 1
  ε := 1
  τ_pos := by norm_num
  D_pos := by norm_num
  χ_pos := by norm_num
  a_pos := by norm_num
  ε_pos := by norm_num

/-! ## String-to-label classifier. -/

/-- Return a legacy label by String matching; unknown strings use EffectiveOnly. -/
def platformKMSQuality : String → PlatformKMSQuality
  | "graphene"  => .Strong
  | "BEC"       => .Approximate
  | "polariton" => .EffectiveOnly
  | _           => .EffectiveOnly  -- default label only

/-- The graphene String maps to the Strong constructor by definition. -/
theorem graphene_kms_quality_strong :
    platformKMSQuality "graphene" = PlatformKMSQuality.Strong := rfl

/-- The BEC String maps to the Approximate constructor by definition. -/
theorem bec_kms_quality_approximate :
    platformKMSQuality "BEC" = PlatformKMSQuality.Approximate := rfl

/-- The polariton String maps to the EffectiveOnly constructor by definition. -/
theorem polariton_kms_quality_effective_only :
    platformKMSQuality "polariton" = PlatformKMSQuality.EffectiveOnly := rfl

/-! ## Generic witnesses remain separate from physical applicability.
zero_correlator_isLDPCompatible and mir_bound_at_zero are generic substrate
witnesses. Downstream all-one MIR and prescribed-sequence growth proofs
remain mathematical statements about their declared inputs, not material
uniqueness, physical KMS or actual Hamiltonian growth. -/

/-! ## Constructor-label comparison. -/

/-- Pairwise distinct constructor labels. This does not establish a physical KMS or growth contrast between platforms. -/
theorem platform_kms_qualities_pairwise_distinct :
    platformKMSQuality "graphene" ≠ platformKMSQuality "BEC" ∧
    platformKMSQuality "BEC" ≠ platformKMSQuality "polariton" ∧
    platformKMSQuality "graphene" ≠ platformKMSQuality "polariton" := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## Scope retained.
Labels, all-one records and conditional downstream witnesses do not
classify real platforms or discharge physical KMS/growth/transport.
The full original graphene, polariton and distinct BEC tasks remain BUILD. -/

end SKEFTHawking.DKMBootstrap
