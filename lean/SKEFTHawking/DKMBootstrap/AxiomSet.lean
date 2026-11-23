/-
# Phase 6q Wave 1b.1 — DKM Transport Bootstrap: CHHK ↔ CGL axiom-set bridge

The historical closest-field comparisons come from the Wave 1a.1 DR
return §2 table (`Lit-Search/Phase-6q/DKM Transport Bootstrap
Axiom-Replacement Substrate for SK-EFT-Hawking.md`). The last column
describes the Lean declarations and their proof scope.

| CHHK family | Closest CGL field in the DR | Lean declaration scope |
|---|---|---|
| F1 DKM form | `hasLocalEquilibrium` | Names the proposed implication |
| F2 thermal spectral bound | `hasLocalEquilibrium` | Zero-correlator control for the legacy pointwise bound |
| F3 operator growth | `hasLargestTime` | Zero-sequence control for the standalone bound |
| F4 positive-frequency positivity | `hasReflectionPositivity` | Projects the supplied implication |
| F5 causal response | `hasLargestTime` + `hasHermiticity` | Projects the supplied implication to the legacy real-value existential |
| F6 fixed-momentum frequency oddness | `hasHermiticity` | Projects the supplied implication |

`IsDKMSpectralFunction` supplies the F4, F5 and F6 implications as
fields. The corresponding theorems project those fields. A physical use
requires identification of the retarded correlator and evidence for the
implications, including the symmetry behind fixed-momentum oddness.

References:
- Wave 1a.1 DR: `Lit-Search/Phase-6q/DKM Transport Bootstrap Axiom-Replacement Substrate for SK-EFT-Hawking.md`
- Wave 1a.2 substrate: `SKEFTHawking.DKMBootstrap.Predicates`
- CGL six-axiom skeleton: `SKEFTHawking.GloriosoLiu.Axioms`
- CHHK primary source: arXiv:2509.18255
-/
import SKEFTHawking.DKMBootstrap.Predicates
import SKEFTHawking.GloriosoLiu.Axioms

namespace SKEFTHawking.DKMBootstrap

open SKEFTHawking.GloriosoLiu SKEFTHawking.SKDoubling

/-! ## §1. The action–correlator link predicate.

The substantive content of the CHHK ↔ CGL bridge requires linking an
abstract `Correlator` (representing `Im G^R(Ω,k)`) to an `SKAction`
(representing the SK effective action). Without the full SK-Green's-
function machinery, we operationalize this as a predicate-substrate
statement of the spectral-function ↔ action relationship.

**Predicate semantics.** `IsDKMSpectralFunction action G` supplies
implications to F4, legacy F5 and F6 for a given signed correlator
`G(Ω,k)`. Constructing the microscopic retarded response and matching
the DKM form on a finite window are separate obligations. -/

/-- **Action–correlator link.** Bundles the supplied implications from
action properties to the F4, legacy F5 and F6 predicates. -/
structure IsDKMSpectralFunction (action : SKAction) (G : Correlator) : Prop where
  /-- Supplied F4 implication to positivity on nonnegative frequencies. -/
  positivity_of_reflection : hasReflectionPositivity action → IsImGRetardedNonneg G
  /-- Supplied implication to the legacy real-value F5 predicate. -/
  uhp_analytic_of_lt_herm :
      hasLargestTime action → hasHermiticity action → IsUpperHalfPlaneAnalytic G
  /-- Supplied F6 implication to fixed-momentum frequency oddness. -/
  pt_symmetry_of_hermiticity : hasHermiticity action → HasParityTimeReversal G

/-! ## §2. The F4 bridge — positivity. -/

/-- **F4 bridge — CHHK positivity from CGL reflection-positivity.**
Under the action-correlator link, any SK action satisfying the
reflection-positivity (SK-3) axiom gives F4 for the supplied correlator
by projection from the link. F4 applies at nonnegative frequencies. -/
theorem dkm_positivity_from_reflection_positivity
    {action : SKAction} {G : Correlator}
    (link : IsDKMSpectralFunction action G)
    (h_refl : hasReflectionPositivity action) :
    IsImGRetardedNonneg G :=
  link.positivity_of_reflection h_refl

/-- **F4 bridge from `SKEFTAxioms`.** Direct corollary: any action
satisfying the full CGL six-axiom skeleton (at any β) gives a CHHK F4-
compatible correlator under the spectral-function link. -/
theorem dkm_positivity_from_skeft_axioms
    {action : SKAction} {β : ℝ} {G : Correlator}
    (link : IsDKMSpectralFunction action G)
    (A : SKEFTAxioms action β) :
    IsImGRetardedNonneg G :=
  dkm_positivity_from_reflection_positivity link A.reflection_pos

/-! ## §3. The legacy F5 projection. -/

/-- Apply the supplied implication to the legacy real-value existential.
Complex upper-half-plane analyticity requires separate evidence. -/
theorem dkm_uhp_analyticity_from_largest_time_hermiticity
    {action : SKAction} {G : Correlator}
    (link : IsDKMSpectralFunction action G)
    (h_lt : hasLargestTime action) (h_herm : hasHermiticity action) :
    IsUpperHalfPlaneAnalytic G :=
  link.uhp_analytic_of_lt_herm h_lt h_herm

/-- Project legacy F5 using `SKEFTAxioms` and the supplied link. -/
theorem dkm_uhp_analyticity_from_skeft_axioms
    {action : SKAction} {β : ℝ} {G : Correlator}
    (link : IsDKMSpectralFunction action G)
    (A : SKEFTAxioms action β) :
    IsUpperHalfPlaneAnalytic G :=
  dkm_uhp_analyticity_from_largest_time_hermiticity link A.largest_time A.hermiticity

/-! ## §4. The F6 bridge — parity / time-reversal. -/

/-- Project fixed-momentum oddness from the supplied link. -/
theorem dkm_pt_symmetry_from_hermiticity
    {action : SKAction} {G : Correlator}
    (link : IsDKMSpectralFunction action G)
    (h_herm : hasHermiticity action) :
    HasParityTimeReversal G :=
  link.pt_symmetry_of_hermiticity h_herm

/-- **F6 bridge from `SKEFTAxioms`.** -/
theorem dkm_pt_symmetry_from_skeft_axioms
    {action : SKAction} {β : ℝ} {G : Correlator}
    (link : IsDKMSpectralFunction action G)
    (A : SKEFTAxioms action β) :
    HasParityTimeReversal G :=
  dkm_pt_symmetry_from_hermiticity link A.hermiticity

/-! ## §5. Proposed implication from DKM form to local equilibrium.

The Wave 1a.1 DR proposes relating an identified effective DKM response
to a local-equilibrium witness. -/

/-- Names the directional implication proposed by the DR. A proof of
that implication and a strictness witness remain separate obligations. -/
def F1StrictlyStrengthensLE
    (action : SKAction) (G : Correlator) (p : DKMParameters) : Prop :=
  IsDKMTransportCorrelator G p → hasLocalEquilibrium action

/-! ## §6. Controls for legacy F2 and F3 parameters.

The examples vary admissible bounds while keeping the zero correlator or
zero norm sequence fixed. Establishing the microscopic lattice inputs
used in CHHK's transport inference requires separate bounds. -/

/-- The zero correlator satisfies the legacy pointwise F2 bound at
`boundData = 0` and `boundData = 1`. The existential also includes the
zero action's `SKEFTAxioms` witness at β. -/
theorem f2_orthogonal_to_skeft_axioms (β : ℝ) :
    ∃ action : SKAction, ∃ _ : SKEFTAxioms action β, ∃ G : Correlator,
      ∃ boundData_1 boundData_2 : ℝ,
        boundData_1 ≠ boundData_2 ∧
        HasFSumRule G boundData_1 ∧
        HasFSumRule G boundData_2 := by
  refine ⟨zeroAction, (SKEFTAxioms_zero_action β).some, zeroCorrelator,
          0, 1, ?_, ?_, ?_⟩
  · norm_num
  · exact zeroCorrelator_hasFSumRule 0 le_rfl
  · exact zeroCorrelator_hasFSumRule 1 (by norm_num)

/-- The zero sequence satisfies the standalone F3 bound with
`n0Norm = 0` at both positive rates `ε = 1` and `ε = 2`. -/
theorem f3_orthogonal_to_skeft_axioms :
    ∃ commutatorNorm : ℕ → ℝ, ∃ n0Norm : ℝ,
      ∃ ε_1 ε_2 : ℝ,
        ε_1 ≠ ε_2 ∧ 0 < ε_1 ∧ 0 < ε_2 ∧
        HasOperatorGrowthBound commutatorNorm ε_1 n0Norm ∧
        HasOperatorGrowthBound commutatorNorm ε_2 n0Norm := by
  refine ⟨fun _ => 0, 0, 1, 2, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num
  · exact zeroCommutatorNorm_hasOperatorGrowthBound 1 0 (by norm_num) le_rfl
  · exact zeroCommutatorNorm_hasOperatorGrowthBound 2 0 (by norm_num) le_rfl

/-! ## §7. Zero-action and zero-correlator control. -/

/-- The zero action and zero correlator instantiate the supplied-link
interface. Each field ignores its premises and returns a predicate
witness for the zero correlator. -/
def trivialLink : IsDKMSpectralFunction zeroAction zeroCorrelator where
  positivity_of_reflection := fun _ => zeroCorrelator_isImGRetardedNonneg
  uhp_analytic_of_lt_herm := fun _ _ => zeroCorrelator_isUpperHalfPlaneAnalytic
  pt_symmetry_of_hermiticity := fun _ => zeroCorrelator_hasParityTimeReversal

/-- **Trivial-link witness for F4 / F5 / F6 from CGL.** The zero action
satisfies all six CGL axioms (at any β); under the trivial link, the
zero correlator witnesses F4, legacy F5 and F6. This checks the
three projections on the zero example. -/
theorem trivial_link_witness (β : ℝ) :
    IsImGRetardedNonneg zeroCorrelator ∧
    IsUpperHalfPlaneAnalytic zeroCorrelator ∧
    HasParityTimeReversal zeroCorrelator := by
  -- The substantive content: the zero action carries SKEFTAxioms at β,
  -- and the bridge theorems descend through `trivialLink`.
  have A : SKEFTAxioms zeroAction β := (SKEFTAxioms_zero_action β).some
  exact ⟨dkm_positivity_from_skeft_axioms trivialLink A,
         dkm_uhp_analyticity_from_skeft_axioms trivialLink A,
         dkm_pt_symmetry_from_skeft_axioms trivialLink A⟩

/-! ## §8. Scope.

The link projections and zero controls describe the predicate interfaces.
Physical spectral positivity, causal analyticity, time reversal and
thermal bounds require evidence for the microscopic correlator. -/

end SKEFTHawking.DKMBootstrap
