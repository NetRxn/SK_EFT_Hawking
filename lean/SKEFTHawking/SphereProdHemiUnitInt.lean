/-
# Phase 5q.H — DISCHARGING the hemisphere-class unit: the UNCONDITIONAL `hcross_pm`

The single residual left by the MV cup–Stokes peel (`SphereProdCrossWitnessInt`) was
`IsUnit (topSphereIsoInt 1 hemiClass)` — "the hemisphere-difference cycle is a fundamental class of
`S²`". This module discharges it and lands the unconditional cross value.

The chase (no winding computation, no sign bookkeeping):

* §0–§1 — **the generator criterion**: a class that pairs to a UNIT against SOME cocycle is a
  generator, for ANY coordinate iso `Hₙ(X;ℤ) ≃ ℤ`. (`Hom_ℤ(ℤ,ℤ) = ℤ` forces every functional to be
  a multiple of the coordinate; a unit value forces the coordinate to be a unit.) Applied to the
  banked winding pairing `⟨windS, t1chain⟩ = 1`, this makes `[t1chain]` a generator of `H₁(S¹;ℤ)`.
* §2 — **the dimension-reduction chase** `dimReductionEquivInt vN 0 hemiClass = [t1chain]`, ON THE
  NOSE. Three collapses do all the work:
  - the NORTH cap filling `fillA` is a chain of `S²∖{vN}` — the very subspace of the pair — so it
    DIES in `Hₙ(S², S²∖{vN})`; the `−` of `hemiDiff` never reaches the answer, hence no sign;
  - the SOUTH cap filling `fillB` is literally an excision preimage (a chain of `S²∖{−vN}` whose
    boundary lies in the doubly-punctured seam), so `excisionEquivInt.symm` is computed by
    `LinearEquiv.symm_apply_eq` with `fillB` as the witness — no inverse is ever unfolded;
  - `connectingInt` on that lift is `∂fillB` = the pushed equator loop, and the banked
    `normalize_equatorMap_eqSeam : normalize ∘ equatorMap vN ∘ eqSeam = id` returns it to `t1chain`.
* §3 — `hemiClass_unit`, then the **UNCONDITIONAL** `hcross_pm` and the fed `s2s2_hyp_of_congr`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SphereProdCrossValueFeed

namespace SKEFTHawking.SphereProdHemiUnitInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularFunctorialityInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularSphereAcyclic (Sph Apunc antipode ne_antipode polar_cover equatorMap)
open SKEFTHawking.SingularExcisionIso (restr)
open SKEFTHawking.SingularExcisionIsoInt (excisionEquivInt excisionMapInt relChainInclInt
  relChainInclInt_mk excisionMapInt_mk)
open SKEFTHawking.SingularSphereHomologyInt (dimReductionEquivInt sphere_suspensionInt_bijective
  equatorInt_to_sphere_bijective)
open SKEFTHawking.SingularLineMinusPointInt (topSphereIsoInt circleH1EquivInt)
open SKEFTHawking.SingularPuncturedRetract (normalize)
open SKEFTHawking.SingularConvexRadialBaseInt (mapChainInt_ambIncl)
open SKEFTHawking.SingularMayerVietorisLES (ambIncl)
open SKEFTHawking.CircleWindingCocycle (windS windS_cocycle)
open SKEFTHawking.KummerT4GramCross (t1chain t1_cycle kronecker_windS_t1)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularSphereBottom (basePoint)
open SKEFTHawking.SphereProdHFourInt (sphereProdIntFundClassHonest)
open SKEFTHawking.SphereProdCrossInt (alphaOf betaOf crossFamily)
open SKEFTHawking.SphereWitnessTowerInt (sphereProdIntH2Basis)
open SKEFTHawking.SphereProdCrossWitnessInt

/-! ## §0. The generator criterion -/

/-- **A unit functional value forces a unit coordinate.** If `e : M ≃ₗ[ℤ] ℤ` is any coordinate
isomorphism and SOME linear functional `f : M →ₗ[ℤ] ℤ` takes a unit value at `x`, then `e x` is a
unit — because `f` factors through `e` as multiplication by `f (e.symm 1)`. -/
theorem isUnit_of_functional {M : Type*} [AddCommGroup M] [Module ℤ M]
    (e : M ≃ₗ[ℤ] ℤ) (f : M →ₗ[ℤ] ℤ) {x : M} (h : IsUnit (f x)) : IsUnit (e x) := by
  set g : ℤ →ₗ[ℤ] ℤ := f.comp e.symm.toLinearMap with hgdef
  have hgx : g (e x) = f x := by
    rw [hgdef, LinearMap.comp_apply, LinearEquiv.coe_coe, e.symm_apply_apply]
  have hlin : ∀ z : ℤ, g z = z * g 1 := fun z => by
    conv_lhs => rw [← mul_one z, ← smul_eq_mul]
    rw [LinearMap.map_smul, smul_eq_mul]
  rw [← hgx, hlin] at h
  exact isUnit_of_mul_isUnit_left h

/-- **The Kronecker generator criterion**: a cycle that pairs to a unit against some cocycle has a
unit coordinate under EVERY coordinate isomorphism `Hₙ(X;ℤ) ≃ₗ ℤ`. -/
theorem isUnit_of_kronecker_unit {X : TopCat} {n : ℕ} (e : Homology X n ≃ₗ[ℤ] ℤ)
    (w : LinearMap.ker (coboundaryₗ X n)) (z : cycles X n) (h : IsUnit (kronecker w.1 z.1)) :
    IsUnit (e (Homology.mk X n z)) :=
  isUnit_of_functional e (kroneckerHInt n (Submodule.Quotient.mk w)) h

/-! ## §1. `[t1chain]` generates `H₁(S¹;ℤ)` — from the banked winding pairing -/

/-- The glued two-arc loop as a 1-cycle of `S¹`. -/
noncomputable def t1cyc : cycles (Sph 1) 1 := ⟨t1chain, LinearMap.mem_ker.mpr t1_cycle⟩

/-- **The circle generator**: `⟨windS, t1chain⟩ = 1` makes `[t1chain]` a generator of `H₁(S¹;ℤ)`,
i.e. its `circleH1EquivInt`-coordinate is `±1`. -/
theorem circleH1EquivInt_t1_isUnit :
    IsUnit (circleH1EquivInt (Homology.mk (Sph 1) 1 t1cyc)) :=
  isUnit_of_kronecker_unit circleH1EquivInt ⟨windS, LinearMap.mem_ker.mpr windS_cocycle⟩ t1cyc
    (by rw [show kronecker windS t1cyc.1 = kronecker windS t1chain from rfl, kronecker_windS_t1]
        exact isUnit_one)

/-! ## §2. The dimension-reduction chase -/

/-- The equatorial-pair subspace of the south cap. -/
abbrev eqPair : Set ↑(Apunc 2 (antipode vN)) :=
  restr ({vN}ᶜ : Set ↑(Sph 2)) ({antipode vN}ᶜ)

/-- The equator loop, intrinsically on the doubly-punctured seam. -/
noncomputable def seamLoop : SingularChainInt (sub eqPair) 1 := mapChainInt eqSeam 1 t1chain

/-- The seam loop pushes to the south-cap loop: `ambIncl ∘ eqSeam = eqInclCapB` on the nose. -/
theorem chainIncl_seamLoop : chainIncl eqPair 1 seamLoop = loopCapB := by
  rw [seamLoop, ← mapChainInt_ambIncl, ← mapChainInt_comp, loopCapB]
  exact congrArg (fun φ => mapChainInt φ 1 t1chain)
    (ContinuousMap.ext fun _ => Subtype.ext rfl)

/-- `fillB` is a relative-cycle lift for the equatorial pair: its boundary is the seam loop. -/
theorem fillB_mem_relCycleLift : fillB ∈ relCycleLift eqPair 1 := by
  show chainBoundary (Apunc 2 (antipode vN)) 1 fillB ∈ subspaceChainsInt eqPair 1
  rw [fillB_spec, ← chainIncl_seamLoop]
  exact LinearMap.mem_range_self _ _

/-- The extracted boundary of `fillB` IS the seam loop. -/
theorem boundaryExtract_fillB :
    boundaryExtract eqPair 1 ⟨fillB, fillB_mem_relCycleLift⟩ = seamLoop := by
  apply chainIncl_injective eqPair 1
  rw [chainIncl_boundaryExtract, chainIncl_seamLoop]
  exact fillB_spec

/-- **The north cap dies in the relative quotient**: `fillA` is a chain of the very subspace
`S²∖{vN}`, so the relative 2-chain of `hemiDiff` is that of `fillB` alone — this is why no sign
survives the chase. -/
theorem relMk_hemiDiff :
    RelativeChainInt.mk ({vN}ᶜ : Set ↑(Sph 2)) 2 hemiDiff
      = RelativeChainInt.mk ({vN}ᶜ : Set ↑(Sph 2)) 2
          (chainIncl ({antipode vN}ᶜ : Set ↑(Sph 2)) 2 fillB) := by
  refine (Submodule.Quotient.eq _).2 ?_
  have hsub : hemiDiff - chainIncl ({antipode vN}ᶜ : Set ↑(Sph 2)) 2 fillB
      = -chainIncl ({vN}ᶜ : Set ↑(Sph 2)) 2 fillA := by
    rw [hemiDiff, ← mapChainInt_ambIncl, ← mapChainInt_ambIncl,
      show puncIncl (antipode vN) = ambIncl ({antipode vN}ᶜ : Set ↑(Sph 2)) from rfl,
      show puncIncl vN = ambIncl ({vN}ᶜ : Set ↑(Sph 2)) from rfl]
    abel
  rw [hsub]
  exact Submodule.neg_mem _ (LinearMap.mem_range_self _ _)

/-- **The excision preimage of the projected hemisphere class is `fillB`.** -/
theorem homProjInt_hemiClass :
    homProjInt ({vN}ᶜ : Set ↑(Sph 2)) 2 hemiClass
      = excisionMapInt ({vN}ᶜ : Set ↑(Sph 2)) ({antipode vN}ᶜ) 2
          (relCycleToHom eqPair 1 ⟨fillB, fillB_mem_relCycleLift⟩) := by
  rw [hemiClass, homProjInt_mk, relCycleToHom_apply, excisionMapInt_mk]
  refine congrArg (RelHomologyInt.mk ({vN}ᶜ : Set ↑(Sph 2)) 2) (Subtype.ext ?_)
  show RelativeChainInt.mk ({vN}ᶜ : Set ↑(Sph 2)) 2 hemiDiff
    = relChainInclInt ({vN}ᶜ : Set ↑(Sph 2)) ({antipode vN}ᶜ) 2
        (RelativeChainInt.mk eqPair 2 fillB)
  rw [relChainInclInt_mk]
  exact relMk_hemiDiff

/-- **THE CHASE**: the banked suspension isomorphism carries the hemisphere class to the circle's
glued loop, on the nose. -/
theorem dimReductionEquivInt_hemiClass :
    dimReductionEquivInt (n := 2) vN 0 hemiClass = Homology.mk (Sph 1) 1 t1cyc := by
  have hexc : (excisionEquivInt ({vN}ᶜ : Set ↑(Sph 2)) ({antipode vN}ᶜ) 1
        (polar_cover (ne_antipode vN))).symm (homProjInt ({vN}ᶜ : Set ↑(Sph 2)) 2 hemiClass)
      = relCycleToHom eqPair 1 ⟨fillB, fillB_mem_relCycleLift⟩ := by
    rw [LinearEquiv.symm_apply_eq, excisionEquivInt, LinearEquiv.ofBijective_apply]
    exact homProjInt_hemiClass
  have hseam : connectingLift eqPair 1 ⟨fillB, fillB_mem_relCycleLift⟩
      = Homology.mapInt eqSeam 1 (Homology.mk (Sph 1) 1 t1cyc) := by
    rw [connectingLift_apply, Homology.mapInt_mk]
    exact congrArg (Homology.mk (sub eqPair) 1) (Subtype.ext boundaryExtract_fillB)
  rw [dimReductionEquivInt, LinearEquiv.trans_apply]
  simp only [LinearEquiv.ofBijective_apply, LinearMap.comp_apply]
  show Homology.mapInt (normalize (n := 2)) 1 (Homology.mapInt (equatorMap vN) 1
      (connectingInt (restr ({vN}ᶜ : Set ↑(Sph 2)) ({antipode vN}ᶜ)) 1
        ((excisionEquivInt ({vN}ᶜ : Set ↑(Sph 2)) ({antipode vN}ᶜ) 1
            (polar_cover (ne_antipode vN))).symm
          (homProjInt ({vN}ᶜ : Set ↑(Sph 2)) 2 hemiClass))))
    = Homology.mk (Sph 1) 1 t1cyc
  rw [hexc, connectingInt_relCycleToHom, hseam,
    ← LinearMap.comp_apply, ← Homology.mapInt_comp, ← LinearMap.comp_apply,
    ← Homology.mapInt_comp, ContinuousMap.comp_assoc, normalize_equatorMap_eqSeam,
    Homology.mapInt_id, LinearMap.id_apply]

/-! ## §3. The headline -/

/-- The full top-sphere reduction `H₂(S²;ℤ) ≅ H₁(S¹;ℤ)` carries the hemisphere class to `[t1chain]`
(the reduction at `m = 1` is one `dimReductionEquivInt` followed by the identity). -/
theorem topSphereReduceInt_hemiClass :
    SingularSphereHomologyInt.topSphereReduceInt 1 hemiClass = Homology.mk (Sph 1) 1 t1cyc := by
  rw [show SingularSphereHomologyInt.topSphereReduceInt 1
      = (dimReductionEquivInt (basePoint 2) 0).trans
        (SingularSphereHomologyInt.topSphereReduceInt 0) from rfl,
    LinearEquiv.trans_apply,
    show SingularSphereHomologyInt.topSphereReduceInt 0 = LinearEquiv.refl ℤ _ from rfl,
    LinearEquiv.refl_apply]
  exact dimReductionEquivInt_hemiClass

/-- **THE HEMISPHERE UNIT** — the discharged residual of the MV cup–Stokes peel: the
hemisphere-difference cycle IS a fundamental class of `S²`, so its `H₂(S²;ℤ) ≅ ℤ` coordinate is
`±1`. Together with `hcross_pm_of_hemiUnit` this makes the Eilenberg–Zilber cross value
unconditional. -/
theorem hemiClass_unit : IsUnit (topSphereIsoInt 1 hemiClass) := by
  rw [topSphereIsoInt, LinearEquiv.trans_apply, topSphereReduceInt_hemiClass]
  exact circleH1EquivInt_t1_isUnit

/-- **THE ±-SIGN CROSS VALUE, UNCONDITIONAL.** The Eilenberg–Zilber cross value
`⟨fst*xS ⌣ snd*xS, [S²×S²]⟩` is a unit — no hypotheses. -/
theorem hcross_pm :
    IsUnit (interFormInt sphereProdIntFundClassHonest (alphaOf xS) (betaOf xS)) :=
  hcross_pm_of_hemiUnit hemiClass_unit

/-- **The unconditional feed**: the `S²×S²` hyperbolic pin from the basis-ID congruence ALONE —
the cross-value and hemisphere-class hypotheses are both discharged. -/
theorem sphereProd_s2s2_hyp_of_congr
    (hcong : IntCongr (interMatrix sphereProdIntFundClassHonest sphereProdIntH2Basis)
      (Matrix.of fun i j => interFormInt sphereProdIntFundClassHonest
        (crossFamily xS i) (crossFamily xS j))) :
    ∃ N, IsHyperbolicForm N ∧
      IntCongr (interMatrix sphereProdIntFundClassHonest sphereProdIntH2Basis) N :=
  SphereProdCrossValueFeed.sphereProd_s2s2_hyp_of_congr_of_hemiUnit hemiClass_unit hcong

end SKEFTHawking.SphereProdHemiUnitInt
