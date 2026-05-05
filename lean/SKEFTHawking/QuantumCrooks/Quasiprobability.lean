/-
# Phase 6n Wave 2b (QCrooks-α) — Kirkwood-Dirac quasiprobability axiomatization

Per Levy-Lostaglio (Phys. Rev. Research 2, 043220, 2020) and the broader
quasiprobability literature (Margenau-Hill, Kirkwood-Dirac, Francica):
work as a quasiprobability with possibly negative or complex values.

The Kirkwood-Dirac quasiprobability:

    q(E_f, E_i) := ⟨E_f| U ρ U† |E_i⟩⟨E_i|E_f⟩

is real-valued only when ρ commutes with H_i; in general it is complex.
The "Crooks ratio" lifts to a relation between q(E_f, E_i) and
q(E_i, E_f) acquiring an exp(β·(E_f - E_i)) factor on diagonal ρ, plus a
phase factor for coherent ρ.

**Key distinguishing feature.** The quasiprobability framework allows
*negative* probability densities — the `nonneg` field of
`WorkDistribution` from `Setup.lean` is therefore TOO STRONG for
quasiprobability schemes. Stage 1 abstracts over this by stating the
predicate at the Crooks-ratio level (which is well-defined for
non-negative distributions); Stage 2-3 will introduce a
`SignedWorkDistribution` (or `Quasiprobability`) type that drops the
non-negativity constraint and re-states the predicate appropriately.

**Stage 1 substantive scope.** Ships the `IsKirkwoodDiracScheme`
predicate. Stage 2-3 will tighten with the substantive quasiprobability
content (signed densities, phase factors for coherent states).

References:
- Levy-Lostaglio, Phys. Rev. Research 2, 043220 (2020),
  doi:10.1103/PhysRevResearch.2.043220
- Lostaglio, "Quantum Fluctuation Theorems, Contextuality, and Work
  Quasiprobabilities," Phys. Rev. Lett. 120, 040602 (2018)
- Francica, Phys. Rev. E 105, L052101 (2022) (broad-class quasiprobabilities)
- Phase 6n DR Appendix §5.A item 4
-/
import SKEFTHawking.QuantumCrooks.Setup

namespace SKEFTHawking.QuantumCrooks

/--
**A `MeasurementScheme` is a Kirkwood-Dirac quasiprobability scheme
(Stage-1 predicate) if it satisfies the classical Crooks ratio at every
inverse temperature β.**

Stage 1 form: predicate captures Crooks-ratio compatibility on the
restriction to non-negative distributions (the `WorkDistribution.P ≥ 0`
condition forces the Stage-1 predicate to operate only on the
non-quasiprobability sub-class). Stage 2-3 will introduce a
`SignedWorkDistribution` type and re-state the predicate to allow
negative densities, capturing the substantive quasiprobability content. -/
def IsKirkwoodDiracScheme (MS : MeasurementScheme) : Prop :=
  ∀ β : ℝ, IsCrooksRatio (MS.forward β) (MS.reverse β) β

/-- The trivial `MeasurementScheme` is (Stage-1) a Kirkwood-Dirac
quasiprobability scheme. -/
theorem trivialScheme_is_KirkwoodDirac :
    IsKirkwoodDiracScheme MeasurementScheme.trivial := by
  intro β
  exact isCrooksRatio_zero β

end SKEFTHawking.QuantumCrooks
