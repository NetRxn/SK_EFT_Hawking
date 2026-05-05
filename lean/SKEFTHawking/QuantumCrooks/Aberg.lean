/-
# Phase 6n Wave 2b (QCrooks-α) — Åberg coherent-quantum axiomatization

Per Åberg (Phys. Rev. X 8, 011019, 2018): a fully coherent inclusive
quantum-Crooks framework. The energy reservoir is in a coherent
superposition of energy eigenstates; the system + reservoir undergo
joint unitary evolution preserving total energy explicitly; the work
distribution is *inferred* from the reservoir's translation-equivariant
displacement, not from a projective measurement.

**Key distinguishing feature.** Unlike Tasaki-TPM, Åberg's framework
does NOT require diagonal initial states — coherence in the system
density matrix is preserved through the protocol. This is the
"axiomatization-instability" gap the Perarnau-Llobet et al. no-go theorem
exploits: a scheme reproducing the average energy on coherent states
cannot also recover TPM on diagonal states.

**Stage 1 substantive scope.** Ships the `IsAbergCoherentScheme`
predicate identifying which `MeasurementScheme` instances are
Åberg-coherent. Stage 2-3 will lift to substantive content: the
energy-conservation constraint as a translation-equivariance condition
on the joint unitary, and the inferred work distribution from the
reservoir's coherent-displacement spectrum.

**Predicate shape (Stage-1).** A scheme is Åberg-coherent if it satisfies
the classical Crooks ratio at every β, AND its forward distribution can
be non-zero away from the discrete spectrum of (H_f - H_i) (i.e., it
admits coherent intermediate work values that diagonal-state schemes do
not). The second clause is the substantive Åberg distinction; Stage 1
encodes only the first clause. The full distinction is a Stage 2-3 fill
target — see SORRY_GAPS.

References:
- Åberg, Phys. Rev. X 8, 011019 (2018), doi:10.1103/PhysRevX.8.011019
- Phase 6n DR Appendix §5.A item 2
-/
import SKEFTHawking.QuantumCrooks.Setup

namespace SKEFTHawking.QuantumCrooks

/--
**A `MeasurementScheme` is Åberg-coherent (Stage-1 predicate) if it
satisfies the classical Crooks ratio at every inverse temperature β.**

Stage 1 form: the predicate captures the Crooks-ratio compatibility but
does NOT yet encode the substantive Åberg-vs-TPM distinction (coherent
intermediate work values). Stage 2-3 will tighten the predicate with the
translation-equivariance condition on the underlying joint unitary that
distinguishes Åberg from Tasaki.

The looseness of the Stage-1 predicate is *intentional* per the appendix
§5 framing: at Stage 1, all four candidate axiomatizations have predicates
of similar shape (they all assert Crooks-ratio compatibility); Stage 2-3
+ Aristotle distinguish them by their substantive axiomatic content. The
Perarnau-Llobet no-go (`PerarnauLlobet.lean`) is what proves they cannot
all hold simultaneously for the same MS. -/
def IsAbergCoherentScheme (MS : MeasurementScheme) : Prop :=
  ∀ β : ℝ, IsCrooksRatio (MS.forward β) (MS.reverse β) β

/-- The trivial `MeasurementScheme` is (Stage-1) Åberg-coherent. -/
theorem trivialScheme_is_Aberg : IsAbergCoherentScheme MeasurementScheme.trivial := by
  intro β
  exact isCrooksRatio_zero β

end SKEFTHawking.QuantumCrooks
