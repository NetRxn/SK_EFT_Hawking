/-
# Phase 6q Wave 1b.2 — DKM Transport Bootstrap: KMS replaces unitarity

The Phase 6o Wave 1c obstruction motivates checking compatibility of
dynamical KMS with CHHK's F4 positivity at nonnegative frequencies
(arXiv:2509.18255v2 §7.1, following Eq. (24)). The Lean proof applies a
supplied positivity implication to reflection positivity. The additional
algebraic dynamical-KMS premise is unused.

**Wave 1b.2 interfaces:**
1. **`KMSReplacesUnitarity`** — the load-bearing predicate: the
   action-correlator link guarantees that `hasReflectionPositivity ∧
   hasDynamicalKMS_algebraic` yields a CHHK F4-compatible correlator
   (i.e., the substitute-for-unitarity positivity bound CHHK consumes).
2. **`kms_replaces_unitarity_thm`** — the link projection: under the
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
   directly. This is re-exported from the CGL module.
4. **Concrete witness theorem** — for the zero action and zero
   correlator, all the KMS-consistency content holds.

References:
- Phase 6o Wave 1c NO-GO §2.1: unitarity → KMS obstruction
- DR Wave 1a.1 §1 row (1): historical motivation
- CGL `hasDynamicalKMS_algebraic` (algebraic-FDR form):
  `SKEFTHawking.GloriosoLiu.Axioms`
- `hasDynamicalKMS_algebraic_implies_hasLocalEquilibrium`:
  `SKEFTHawking.GloriosoLiu.Axioms` line 136
- CHHK arXiv:2509.18255v2 §7.1, positivity after Eq. (24)
-/
import SKEFTHawking.DKMBootstrap.AxiomSet

namespace SKEFTHawking.DKMBootstrap

open SKEFTHawking.GloriosoLiu SKEFTHawking.SKDoubling

/-! ## §1. The KMS-replaces-unitarity bridge predicate.

The predicate asks for F4 under a supplied action–correlator link,
reflection positivity and algebraic dynamical KMS. -/

/-- **KMS-replaces-unitarity bundle.** A CGL action's `dynamical_KMS`
content (algebraic-FDR form) is *consistent with* the F4 positivity
input CHHK consumes — i.e., adding dynamical-KMS to reflection-
positivity does not break the F4 positivity that the action-correlator
link inherits from `hasReflectionPositivity`.

A physical replacement for unitarity requires a microscopic
action–correlator identification and a proof of the spectral implication. -/
def KMSReplacesUnitarity (action : SKAction) (G : Correlator) (β : ℝ) : Prop :=
  IsDKMSpectralFunction action G →
  hasReflectionPositivity action →
  hasDynamicalKMS_algebraic action β →
  IsImGRetardedNonneg G

/-! ## §2. Projecting F4 from the supplied link. -/

/-- Apply the link's F4 field to reflection positivity. The additional
dynamical-KMS hypothesis is unused. -/
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

The zero pair checks the compatibility interface with supplied fields. -/

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
  conditional F4 compatibility claim.
- **`kms_replaces_unitarity_thm`** — project F4 through the supplied
  reflection-positivity implication.
- **`kms_dynamical_implies_local_equilibrium_consistency`** — re-export
  of the algebraic-KMS ⇒ LE implication.
- **Concrete witness theorems** on the zero-action substrate.

The physical positivity argument motivated by Phase 6o Wave 1c
Obstruction (I) remains separate from these projections. -/

end SKEFTHawking.DKMBootstrap
