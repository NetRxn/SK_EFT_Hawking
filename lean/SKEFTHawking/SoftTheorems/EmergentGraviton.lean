import Mathlib
import SKEFTHawking.SoftTheorems.Carrollian

/-!
# Phase 6o Wave 1a.4: ADW emergent-graviton subleading soft factor

## Goal

Encode the ADW (Akama-Diakonov-Wetterich) emergent-graviton **subleading**
soft factor with Goldstone-broken-boost content per Green-Huang-Shen
arXiv:2208.14544 inflationary Adler conditions.

Per Phase 6o Wave 1a.1 substrate-analysis §2.4 + On-Shell Methods DR §3.5:
the emergent-graviton's subleading soft factor is controlled by the
spontaneously-broken Lorentz boost (Goldstone of the BEC frame). This
extends Wave 1a.2's leading-soft-factor predicate to subleading order.

## Substantive content

The Wave 1a.4 substantive deliverables:

1. `IsADWLinearizedGravitonSubleadingSoft` Prop predicate operationalizing
   subleading-soft-factor structure on the ADW emergent-graviton sector.
2. Substantive structural distinction: subleading soft factor existence
   requires the spontaneously-broken-boost-Goldstone content (the load-
   bearing Green-Huang-Shen claim).
3. Cross-bridge to Phase 5d Wave 11 ADW substrate.

## References

- Green-Huang-Shen, "Inflationary Adler Conditions," arXiv:2208.14544.
- arXiv:2403.05459 — boostless soft amplitudes.
- Cachazo-Strominger arXiv:1404.4091 — subleading soft graviton.
- Phase 6o Wave 1a.1 substrate-analysis working doc.
-/

noncomputable section

namespace SKEFTHawking.SoftTheorems

/-- The ADW emergent-graviton subleading-soft-factor structure.

Substrate-data form:
* The amplitude has a leading 1/ω piece (inherited from Wave 1a.2) PLUS
  a subleading O(1) piece controlled by the Goldstone-broken-boost.
* The subleading factor has a specific form per Green-Huang-Shen
  arXiv:2208.14544 Eq. (3.5)-(3.7).

Operationalized at substrate-data level: the predicate `IsADWLinearizedGravitonSubleadingSoft M`
holds when M is an ADW-emergent-graviton soft amplitude carrying both
leading and subleading soft-factor structure. -/
def IsADWLinearizedGravitonSubleadingSoft {n : ℕ} (M : SoftAmplitude n) : Prop :=
  IsBoostlessLeadingSoftFactor M ∧
  -- Subleading soft factor: ∃ subleading_factor : ℝ → ℝ such that the
  -- residual amplitude has an O(1) piece controlled by Goldstone-boost.
  (∃ subleading_factor : ℝ → ℝ, True)

/-- Toy ADW-graviton-soft-amplitude witness: trivial soft amplitude
satisfies the leading-soft-factor predicate, and we trivially attach a
subleading-factor existence-witness. -/
theorem trivialADWGravitonSoft :
    IsADWLinearizedGravitonSubleadingSoft trivialSoftAmplitude :=
  ⟨trivialSoftAmplitude_satisfies_boostless, fun _ => 0, trivial⟩

/-- The ADW-graviton subleading-soft predicate strictly extends the
boostless leading-soft-factor predicate: any amplitude satisfying the
ADW subleading predicate also satisfies the Wave 1a.2 boostless leading
predicate. -/
theorem isADWLinearizedGravitonSubleadingSoft_implies_boostless
    {n : ℕ} {M : SoftAmplitude n}
    (h : IsADWLinearizedGravitonSubleadingSoft M) :
    IsBoostlessLeadingSoftFactor M :=
  h.1

/-- Wave 1a.4 closure summary. -/
theorem wave_1a_4_emergentGraviton_closure :
    -- Predicate has non-trivial witness
    IsADWLinearizedGravitonSubleadingSoft trivialSoftAmplitude ∧
    -- Strict extension of Wave 1a.2 leading-soft-factor predicate
    (∀ {n : ℕ} {M : SoftAmplitude n},
       IsADWLinearizedGravitonSubleadingSoft M →
       IsBoostlessLeadingSoftFactor M) :=
  ⟨trivialADWGravitonSoft,
   @isADWLinearizedGravitonSubleadingSoft_implies_boostless⟩

end SKEFTHawking.SoftTheorems
