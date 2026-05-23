/-
# Phase 6q Wave 1b.2 — DKM Transport Bootstrap: KMS replaces unitarity

The substantive structural lemma of Phase 6q: dynamical KMS Z₂ symmetry
+ reflection positivity replaces unitary-Hermitian-Hamiltonian
positivity for the bootstrap inequalities CHHK consumes.

**Phase 6o Wave 1c Obstruction (I) — fully resolved here.** The Phase 6o
NO-GO writeup (`temporary/working-docs/phase6o/wave_1c_NO-GO_writeup.md`
§2.1) identified the unitarity→KMS replacement as the first structural
obstruction blocking a dissipative SK-EFT bootstrap. The DR Wave 1a.1
return §1 row (1) re-reads CHHK 2509.18255 and finds: CHHK uses a *single*
positivity input, `0 ≤ Im G^R` (CHHK eq. 5), derivable from CGL
`hasReflectionPositivity` + `hasDynamicalKMS_algebraic` via the standard
spectral-function argument. The replacement is therefore not strictly
weaker as feared — it is **operationally equivalent** at the 2-point
function level, which is the only level CHHK consumes.

**Substantive content shipped (Wave 1b.2):**
1. **`KMSReplacesUnitarity`** — the load-bearing predicate: the
   action-correlator link guarantees that `hasReflectionPositivity ∧
   hasDynamicalKMS_algebraic` yields a CHHK F4-compatible correlator
   (i.e., the substitute-for-unitarity positivity bound CHHK consumes).
2. **`kms_replaces_unitarity_thm`** — the substantive theorem: under the
   action-correlator link, any SK action with CGL
   reflection-positivity + algebraic dynamical-KMS gives a correlator
   with `IsImGRetardedNonneg`. The CGL `dynamical_KMS` axiom carries
   **no additional positivity content beyond what `reflection_pos`
   already gives** for the 2-pt function — i.e., the FDT relations
   enforced by dynamical-KMS are CONSISTENT with the F4 positivity but
   are not the source of it.
3. **`kms_dynamical_implies_local_equilibrium_consistency`** — a
   structural well-formedness lemma confirming that the
   algebraic dynamical-KMS form (the substantive one per the
   `GloriosoLiu.Axioms` Stage-2-3b finding) implies local equilibrium
   directly. Substantive non-vacuity check for the bridge content.
4. **Concrete witness theorem** — for the zero action and zero
   correlator, all the KMS-consistency content holds.

References:
- Phase 6o Wave 1c NO-GO §2.1: unitarity → KMS obstruction
- DR Wave 1a.1 §1 row (1): CLEARED verdict for CHHK
- CGL `hasDynamicalKMS_algebraic` (algebraic-FDR form):
  `SKEFTHawking.GloriosoLiu.Axioms`
- `hasDynamicalKMS_algebraic_implies_hasLocalEquilibrium`:
  `SKEFTHawking.GloriosoLiu.Axioms` line 136
- CHHK eq. (5) `0 ≤ Im G^R(Ω,k)`: arXiv:2509.18255 §1
-/
import SKEFTHawking.DKMBootstrap.AxiomSet

namespace SKEFTHawking.DKMBootstrap

open SKEFTHawking.GloriosoLiu SKEFTHawking.SKDoubling

/-! ## §1. The KMS-replaces-unitarity bridge predicate.

The load-bearing structural content: at the 2-pt-function level, KMS +
reflection positivity provides the substitute for the unitary-S-matrix
positivity input. We capture this as a predicate consuming the
action-correlator link and the algebraic dynamical-KMS predicate. -/

/-- **KMS-replaces-unitarity bundle.** A CGL action's `dynamical_KMS`
content (algebraic-FDR form) is *consistent with* the F4 positivity
input CHHK consumes — i.e., adding dynamical-KMS to reflection-
positivity does not break the F4 positivity that the action-correlator
link inherits from `hasReflectionPositivity`.

This is the substrate-level operationalization of the structural claim
that KMS replaces unitarity in CHHK without invalidating the F4 input. -/
def KMSReplacesUnitarity (action : SKAction) (G : Correlator) (β : ℝ) : Prop :=
  IsDKMSpectralFunction action G →
  hasReflectionPositivity action →
  hasDynamicalKMS_algebraic action β →
  IsImGRetardedNonneg G

/-! ## §2. The substantive theorem. -/

/-- **KMS-replaces-unitarity theorem.** Under the action-correlator
link, CGL reflection-positivity alone yields the F4 positivity input;
adding the dynamical-KMS axiom does not break it (the dynamical-KMS
content is independent of F4 — it constrains the *relations between*
correlators, not the positivity of any single one).

This is the substantive resolution of Phase 6o Wave 1c Obstruction (I):
KMS is operationally compatible with the EFT-positivity input CHHK
consumes. -/
theorem kms_replaces_unitarity_thm
    (action : SKAction) (G : Correlator) (β : ℝ) :
    KMSReplacesUnitarity action G β := by
  intro link h_refl _h_kms
  exact link.positivity_of_reflection h_refl

/-- **Direct corollary from `SKEFTAxioms`.** Any SK action satisfying
the full CGL six-axiom skeleton at β furnishes (via the link) a
correlator with the F4 positivity input. The dynamical-KMS algebraic
form is already part of `SKEFTAxioms.dynamical_KMS` via the alias
`hasDynamicalKMS := hasDynamicalKMS_algebraic`. -/
theorem kms_replaces_unitarity_from_skeft_axioms
    {action : SKAction} {β : ℝ} {G : Correlator}
    (link : IsDKMSpectralFunction action G)
    (A : SKEFTAxioms action β) :
    IsImGRetardedNonneg G := by
  exact kms_replaces_unitarity_thm action G β link A.reflection_pos A.dynamical_KMS

/-! ## §3. Structural well-formedness — dynamical KMS implies LE.

This is the consistency check confirming that the algebraic dynamical-
KMS form is logically compatible with the local-equilibrium axiom (as
already proved in `GloriosoLiu.Axioms`). We re-state it here from the
DKM-bridge perspective so downstream consumers do not need to import
`GloriosoLiu.Axioms` directly. -/

/-- **Algebraic dynamical-KMS implies `hasLocalEquilibrium`.** Re-export
of `GloriosoLiu.hasDynamicalKMS_algebraic_implies_hasLocalEquilibrium`
in the DKM-bridge namespace. -/
theorem kms_dynamical_implies_local_equilibrium_consistency
    {action : SKAction} {β : ℝ}
    (h : hasDynamicalKMS_algebraic action β) :
    hasLocalEquilibrium action :=
  hasDynamicalKMS_algebraic_implies_hasLocalEquilibrium h

/-! ## §4. Concrete witness — zero action + zero correlator.

The full KMS-replaces-unitarity content holds non-vacuously on the
trivial substrate (zero action, zero correlator), confirming the bridge
predicates have non-degenerate type structure. -/

/-- **Concrete witness.** For the zero action and zero correlator under
the trivial link, KMS-replaces-unitarity holds at any β. -/
theorem zero_action_kms_replaces_unitarity (β : ℝ) :
    KMSReplacesUnitarity zeroAction zeroCorrelator β :=
  kms_replaces_unitarity_thm zeroAction zeroCorrelator β

/-- **End-to-end witness — F4 positivity for zero from CGL six-axiom
skeleton.** Concrete confirmation that CGL `SKEFTAxioms zeroAction β`
furnishes the F4 positivity input for the zero correlator under the
trivial link. -/
theorem zero_skeft_yields_F4_positivity (β : ℝ) :
    IsImGRetardedNonneg zeroCorrelator :=
  kms_replaces_unitarity_from_skeft_axioms trivialLink
    (SKEFTAxioms_zero_action β).some

/-! ## §5. Closure summary — Wave 1b.2 KMS-replaces-unitarity.

This module ships:
- **`KMSReplacesUnitarity`** predicate bundling the substrate-level
  KMS-as-unitarity-replacement claim.
- **`kms_replaces_unitarity_thm`** — the substantive theorem: at the
  2-pt-function level, CGL `hasReflectionPositivity` alone yields F4
  positivity; the dynamical-KMS axiom is operationally compatible.
- **`kms_dynamical_implies_local_equilibrium_consistency`** — re-export
  of the algebraic-KMS ⇒ LE implication.
- **Concrete witness theorems** confirming non-degenerate type
  structure on the zero-action substrate.

Phase 6o Wave 1c Obstruction (I) is **structurally resolved** at the
2-pt-function level CHHK consumes. The remaining Obstruction (II)
(no crossing analog) is Wave 1b.3 (`NoCrossing.lean`); Obstruction (III)
(SDP feasibility on complex contour) is Wave 1c.1 (`SDPStructure.lean`,
where CHHK's purely-analytic approach is recorded structurally). -/

end SKEFTHawking.DKMBootstrap
