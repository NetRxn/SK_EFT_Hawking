/-
# Phase 5q.H — THE ZERO-BINDER FIRING: `16 ∣ σ` at S⁴, UNCONDITIONAL

The project's first fully-unconditional Rokhlin-leg instance. Round 5
(`SphereWitnessFiringInt`) had shrunk the S⁴ firing to a single named geometric Prop
(`Sphere4ChartBallsOriented`); working its moving-puncture discharge exposed that the frozen
`orient ≡ 1` normalisation is CHOICE-SENSITIVE against Mathlib's `chartAt`-pinned local generators
(`SphereFourOrientationDataInt` module docstring) — so the freeze route can never fire. This module
composes the honest replacements instead:

* the UNCONDITIONAL orientation datum `sphere4IntOrientationDataUncond` (the choice-absorbing
  global section from `H₄(S⁴;ℤ) ≅ ℤ` + the everywhere-bijective point restriction);
* the `±`-section σ÷16 leg (`sixteen_dvd_latticeSig_of_orientation_spin_free'` — the `orient ≡ 1`
  binder eliminated, sign conjugated into the UC-flip);
* the round-5 spin certificate `sphere4_wuClass2_eq_zero` (N6 — a THEOREM);
* the computed witness package: instances (N5), basis `sphere4IntH2Basis`, `htopo`
  (`sphere4_interMatrix_htopo`, N2).

`sixteen_dvd_latticeSig_sphere4_unconditional` has NO hypotheses: every binder of the kron-free leg
is discharged by a theorem or computed instance. At the consistency witness the conclusion's value
is `16 ∣ 0` (`b₂(S⁴) = 0`); the content is that the WHOLE pipeline — orientation datum →
fundamental class → intersection form → even unimodularity → σ÷16 — fires end-to-end on
theorem-backed inputs, with zero freezes left.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/
`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SphereFourOrientationDataInt
import SKEFTHawking.SixteenDvdOrientSectionInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularSphereAcyclic (Sph)
open SKEFTHawking.IntOrientationSection
open SKEFTHawking.SingularPD4Instances
open SKEFTHawking.PoincareDualityWu (wuClass2)
open SKEFTHawking.SphereWitnessTowerInt
open SKEFTHawking.SphereWitnessFiringInt (sphere4_wuClass2_eq_zero)
open SKEFTHawking.SphereFourOrientationDataInt (sphere4IntOrientationDataUncond)
open SKEFTHawking.SixteenDvdOrientSectionInt (sixteen_dvd_latticeSig_of_orientation_spin_free')

namespace SKEFTHawking.SphereWitnessFiringUncondInt

/-- **The σ÷16 leg at S⁴ from ANY orientation datum** — the round-5
`sixteen_dvd_latticeSig_sphere4` with the `orient ≡ 1` normalisation GONE (it is not satisfiable
for Mathlib's choice-pinned sphere atlas): the kron-free `±`-section leg instantiated at the first
witness, every instance obligation discharged by the computed N5 package. -/
theorem sixteen_dvd_latticeSig_sphere4' (d : IntOrientationData SphereFour)
    (hv2 : wuClass2 (poincareDual4Mid_of_closed (M := SphereFour)) = 0)
    (htopo : (2 : ℤ) ∣ latticeSig
      (interMatrix (intFundamentalClassOfHomology d.fundClass) sphere4IntH2Basis) / 8) :
    (16 : ℤ) ∣ latticeSig
      (interMatrix (intFundamentalClassOfHomology d.fundClass) sphere4IntH2Basis) :=
  sixteen_dvd_latticeSig_of_orientation_spin_free' d sphere4IntH2Basis hv2 htopo

/-- **THE ZERO-BINDER FIRING: `16 ∣ σ(S⁴)` UNCONDITIONALLY** — the project's first
fully-unconditional Rokhlin-leg instance. No hypotheses: the orientation datum is the
choice-absorbing global-section construction (`sphere4IntOrientationDataUncond`, a theorem-backed
structure), the spin certificate is `sphere4_wuClass2_eq_zero` (N6), the topological factor is
`sphere4_interMatrix_htopo` (N2), and the N5 instance package is computed. The whole
orientation → intersection-form → even-unimodularity → σ÷16 pipeline fires end-to-end. -/
theorem sixteen_dvd_latticeSig_sphere4_unconditional :
    (16 : ℤ) ∣ latticeSig
      (interMatrix (intFundamentalClassOfHomology sphere4IntOrientationDataUncond.fundClass)
        sphere4IntH2Basis) :=
  sixteen_dvd_latticeSig_sphere4' sphere4IntOrientationDataUncond
    sphere4_wuClass2_eq_zero (sphere4_interMatrix_htopo _)

end SKEFTHawking.SphereWitnessFiringUncondInt
