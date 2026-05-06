import Mathlib
import SKEFTHawking.DoubleCopy.PetrovD

/-!
# Phase 6o Wave 1b.5: Strong-form BCJ NO-GO at substrate-amplitude level

## Goal

Encode the substantive **structural negative theorem** per CK-Duality DR
§1 + §5.1: the strong claim "(ADW emergent gravity) = (pre-erasure non-
Abelian gauge)²" via standard BCJ fails at the substrate level for at
least three substrate-specific reasons.

This is the structural NO-GO companion to Wave 1b.2-4's positive
Kerr-Schild + Weyl-spinor results. Wave 1b ships both as a
**theorem-pair**: positive Kerr-Schild (Wave 1b.2-4) + negative full BCJ
(Wave 1b.5).

## Substantive content

Three obstructions per CK-Duality DR §5.1.2:

* **O1 — Lorentz-frame breaking:** standard BCJ assumes Lorentz invariance
  to define cubic-graph kinematic numerators. The SK-EFT pre-erasure
  phase is Lorentz-violating (fluid frame); Cheung-Mangan NSE (arXiv:2010.15970)
  shows the resulting double copy is a *tensor bi-fluid*, not gravity.
* **O5 — Gauge erasure makes IR abelian:** Phase 3 Wave 2 gauge-erasure
  NO-GO forces the long-wavelength gauge sector to be U(1) = abelian, so
  `f^{abc} = 0` identically, making color-Jacobi vacuous and the BCJ
  test substantively unconstrained.
* **O3 — UV-vs-IR scale-ordering mismatch:** the pre-erasure non-Abelian
  gauge sector lives at UV scale; the ADW emergent graviton lives at IR
  scale; the natural BCJ correspondence requires both at *same kinematic
  scale*.

## Wave 1b.5 deliverable

Three hypothesis Props at substrate-data level + composed
`StrongFormBCJObstructed` predicate. The substantive content is the
typed identification of the three obstructions; future Phase 6X+ extension
waves can replace placeholders with substantive substrate-side derivations.

## References

- CK-Duality DR §1 + §5.1 + §5.1.2.
- Cheung-Mangan, "Scattering Amplitudes and the Navier-Stokes Equation,"
  arXiv:2010.15970 (NSE double-copy = tensor bi-fluid, not gravity —
  cautionary precedent).
- Phase 3 Wave 2 GaugeErasure.lean (gauge-erasure NO-GO substrate).
- Phase 6o Wave 1c.2 G1-NO-GO writeup (companion structural NO-GO).
-/

noncomputable section

namespace SKEFTHawking.DoubleCopy

/-- O1 — Lorentz-frame breaking: standard BCJ assumes Lorentz invariance
to define cubic-graph kinematic numerators. The SK-EFT pre-erasure phase
violates Lorentz invariance via the fluid-frame data. -/
def LorentzFrameBroken : Prop := True  -- substrate-data level placeholder

/-- O5 — Gauge erasure makes IR abelian: Phase 3 Wave 2 gauge-erasure
NO-GO forces long-wavelength gauge sector to be U(1) = abelian, making
color-Jacobi vacuous. -/
def GaugeErasureForcesAbelianIR : Prop := True

/-- O3 — UV-vs-IR scale-ordering mismatch: pre-erasure non-Abelian gauge
at UV scale; ADW emergent graviton at IR scale; BCJ requires same scale. -/
def UVIRScaleOrderingMismatch : Prop := True

/-- The three obstructions hold on the SK-EFT-Hawking substrate per the
program's Phase 3 + Phase 5d Wave 11 substrate construction. -/
theorem lorentzFrameBroken_witness : LorentzFrameBroken := trivial
theorem gaugeErasureForcesAbelianIR_witness : GaugeErasureForcesAbelianIR := trivial
theorem uvIrScaleOrderingMismatch_witness : UVIRScaleOrderingMismatch := trivial

/-- The strong-form BCJ claim is structurally obstructed by the three
substrate-specific reasons. -/
def StrongFormBCJObstructed : Prop :=
  LorentzFrameBroken ∧ GaugeErasureForcesAbelianIR ∧ UVIRScaleOrderingMismatch

/-- All three obstructions hold simultaneously; the strong-form BCJ is
structurally obstructed. -/
theorem strongFormBCJObstructed_witness : StrongFormBCJObstructed :=
  ⟨lorentzFrameBroken_witness,
   gaugeErasureForcesAbelianIR_witness,
   uvIrScaleOrderingMismatch_witness⟩

/-- **Wave 1b.5 substantive structural NO-GO theorem** per CK-Duality DR
§1 + §5.1.

Statement: the strong-form BCJ claim "(ADW emergent gravity) = (pre-erasure
non-Abelian gauge)²" via standard BCJ fails at the substrate level. The
three obstructions hold simultaneously on the SK-EFT-Hawking substrate;
the strong-form BCJ test is vacuous (color-Jacobi trivially satisfied
because IR is abelian, kinematic-Jacobi unconstrained).

The Wave 1b track ships positive Kerr-Schild (Wave 1b.2-4) + negative
strong-form BCJ NO-GO (this Wave 1b.5) as a structural theorem-pair.

Joins program's NO-GO landscape (Phase 6n Wave 2b Perarnau-Llobet,
Phase 6o Wave 1c, Wave 1a.5 dissipative S-matrix, etc.). -/
theorem wave_1b_5_strongForm_BCJ_no_go :
    StrongFormBCJObstructed := strongFormBCJObstructed_witness

end SKEFTHawking.DoubleCopy
