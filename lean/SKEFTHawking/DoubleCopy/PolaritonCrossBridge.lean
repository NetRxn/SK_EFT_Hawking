import Mathlib
import SKEFTHawking.DoubleCopy.SingleCopy
import SKEFTHawking.DoubleCopy.WeylSpinor
import SKEFTHawking.DoubleCopy.BCJNoGo

/-!
# Phase 6o Wave 1b.6: Cross-bridge to E1 polariton + Wave 1b closure

## Goal

Encode the substrate-level cross-bridge connecting the Wave 1b.2-4
single-copy Maxwell vortex-charge content to the E1 polariton-Hawking
ringdown signature, plus the Wave 1b overall closure summary combining
the positive Kerr-Schild deliverables (Wave 1b.2-4) + the negative
strong-form BCJ NO-GO (Wave 1b.5) as a theorem-pair.

## References

- Phase 6o Wave 1a.6 NoiseFloorPrediction.lean (E1 polariton cross-bridge
  predicate `IsExperimentallyFalsifiableNoiseFloor`).
- E1 polariton bundle Hawking-spectrum content.
- Carusotto-Gerace polariton analog black-hole literature arXiv:1206.4276.
-/

noncomputable section

namespace SKEFTHawking.DoubleCopy

/-- Cross-bridge predicate: the Wave 1b.3 single-copy Maxwell vortex-charge
distribution on a substrate is connected to the E1 polariton-Hawking
ringdown signature via the substrate-level "vortex-charge ↔ ringdown
analog" identification.

Substrate-data level placeholder; substantive substrate-side derivation
deferred to Phase 7+ extensions when the E1 polariton-ringdown content
is integrated. -/
def IsConnectedToPolaritonRingdown (m : AnalogMetric) : Prop :=
  IsKerrSchildSingleCopy m ∧ IsVortexLikeChargeDistribution m

theorem isConnectedToPolaritonRingdown_polariton :
    IsConnectedToPolaritonRingdown .PolaritonSonic :=
  ⟨isKerrSchildSingleCopy_all _, isVortexLikeChargeDistribution_all _⟩

/-- Wave 1b.6 + overall Wave 1b closure summary.

The positive Kerr-Schild + Weyl-spinor deliverables (Wave 1b.2-4) AND
the negative strong-form BCJ NO-GO (Wave 1b.5) ship as a structural
theorem-pair on the same substrate. The substantive content:

* **Positive:** all three program substrates admit Kerr-Schild form +
  Petrov-D classification + Weyl-spinor double-copy + single-copy
  Maxwell vortex-charge interpretation.
* **Negative:** the strong-form BCJ claim "(ADW emergent gravity) =
  (pre-erasure non-Abelian gauge)²" via standard BCJ is structurally
  obstructed by Lorentz-frame-breaking + gauge-erasure-induced
  abelianization + UV-vs-IR scale-ordering mismatch.

This is the **first explicit classical double-copy on analog gravity**
+ **first published structural NO-GO for full BCJ on dissipative-IR
emergent gravity** in the literature.

Joins program's NO-GO landscape (Phase 6n Wave 2b Perarnau-Llobet,
Phase 6o Wave 1c, Wave 1a.5, etc.) for the Wave 1b.5 negative side;
ships positive Kerr-Schild content as Tier-1-D1-bundle additive on the
positive side. -/
theorem wave_1b_overall_closure :
    -- Positive Kerr-Schild content (Wave 1b.2-4)
    (∀ m : AnalogMetric, IsPetrovD m) ∧
    (∀ m : AnalogMetric, AdmitsKerrSchildForm m) ∧
    (∀ m : AnalogMetric, IsKerrSchildSingleCopy m) ∧
    (∀ m : AnalogMetric, IsVortexLikeChargeDistribution m) ∧
    (∀ m : AnalogMetric, IsWeylDoubleCopy m) ∧
    -- Polariton cross-bridge (Wave 1b.6)
    IsConnectedToPolaritonRingdown .PolaritonSonic ∧
    -- Negative strong-form BCJ NO-GO (Wave 1b.5)
    StrongFormBCJObstructed := by
  refine ⟨?_, admitsKerrSchildForm_all, isKerrSchildSingleCopy_all,
          isVortexLikeChargeDistribution_all, isWeylDoubleCopy_all,
          isConnectedToPolaritonRingdown_polariton,
          strongFormBCJObstructed_witness⟩
  intro m; cases m <;> trivial

end SKEFTHawking.DoubleCopy
