/-
# Phase 6n Wave 2b (QCrooks-α) — Kafri-Deffner unital-channel axiomatization

Per Kafri-Deffner (Phys. Rev. A 86, 044302, 2012): Holevo's bound from a
quantum fluctuation theorem; entropy production for unital channels (those
preserving the identity, Φ(1) = 1).

For a unital quantum channel Φ acting on a density matrix ρ, the entropy
production satisfies a Crooks-style relation, with the average entropy
production bounded below by the Holevo information of the
forward/reverse channels.

**Key distinguishing feature.** The Kafri-Deffner framework operates at
the channel level rather than the unitary-evolution level — it abstracts
over CPTP (completely positive trace-preserving) maps with the additional
unital constraint Φ(1) = 1. This makes it *broader* than Tasaki-TPM (which
specializes to unitary U via Φ(ρ) = UρU†), and *narrower* than Åberg
(which allows non-unital protocols via the reservoir's energy
non-conservation).

**Stage 1 substantive scope.** Ships the `IsKafriDeffnerUnitalScheme`
predicate. Stage 2-3 will lift to the substantive Petz-monotonicity +
Holevo-bound content. The unital-channel substrate (CPTP maps + Φ(1) = 1
condition) is currently abstracted at Stage 1 via the same
`MeasurementScheme` interface as the other axiomatizations.

References:
- Kafri-Deffner, Phys. Rev. A 86, 044302 (2012),
  doi:10.1103/PhysRevA.86.044302
- Petz, Quantum Information Theory and Quantum Statistics (2008)
  (Petz monotonicity)
- Holevo, Probabilistic and Statistical Aspects of Quantum Theory (1980)
- Phase 6n DR Appendix §5.A item 3
-/
import SKEFTHawking.QuantumCrooks.Setup

namespace SKEFTHawking.QuantumCrooks

/--
**A `MeasurementScheme` is a Kafri-Deffner unital-channel scheme
(Stage-1 predicate) if it satisfies the classical Crooks ratio at every
inverse temperature β.**

Stage 1 form: predicate captures Crooks-ratio compatibility. Stage 2-3
will tighten with the substantive unital-channel constraint (Φ(1) = 1)
and the Holevo-bound-saturating entropy production. -/
def IsKafriDeffnerUnitalScheme (MS : MeasurementScheme) : Prop :=
  ∀ β : ℝ, IsCrooksRatio (MS.forward β) (MS.reverse β) β

/-- The trivial `MeasurementScheme` is (Stage-1) a Kafri-Deffner
unital-channel scheme. -/
theorem trivialScheme_is_KafriDeffner :
    IsKafriDeffnerUnitalScheme MeasurementScheme.trivial := by
  intro β
  exact isCrooksRatio_zero β

end SKEFTHawking.QuantumCrooks
