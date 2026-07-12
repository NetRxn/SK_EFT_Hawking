/-
# Phase 5q.H — the choice-absorbing global orientation section at GENERAL M (the N3 device)

`SphereFourOrientationDataInt` built the UNCONDITIONAL S⁴ orientation datum by absorbing Mathlib's
per-point `stdOrthonormalBasis` choice-pattern into the section itself: `orient z := iso_z (ρ_z g)`
for a single global class `g`, so the `restricts` law holds definitionally and no cross-chart sign
is ever compared (the comparison is INDEPENDENT over Lean's axioms — settled fork
`5qH-orient-normalized-vs-chartAt-pinned-generators`). Sections §2–§4 of that construction never
used the sphere — only (i) a global class restricting to a local generator at every point and
(ii) the proved 18e–18h gluing chain, both already stated at general `M`. This module extracts the
device to class level:

* `IntGlobalGenerator M` — a global `H₄(M;ℤ)` class whose point restriction is a generator of the
  local group `H₄(M|z;ℤ) ≅ ℤ` at every `z`;
* `IntGlobalGenerator.orient` — the recorded (choice-absorbing) `±1` section; its restriction law
  `cls_restricts` is definitional, the whole point of recording instead of normalising;
* `IntGlobalGenerator.orientationData` — the full `IntOrientationData M` (per-ball realisability
  by restricting the global class, then the proved `univ` induction + 18e–18h chain);
* `intGlobalGeneratorOfEquiv` — the generator-supply constructor: any `E : H₄(M;ℤ) ≃+ ℤ` together
  with point-restriction bijectivity yields the datum (the S⁴ §3 unit argument, made generic);
* `restrictHomologyToPointInt_bijective_of_punctured_acyclic` and
  `intGlobalGeneratorOfPuncturedAcyclic` — the pair-LES sandwich criterion: `H₄(M∖z;ℤ) = 0` and
  `H₃(M∖z;ℤ) = 0` at every point make every point restriction bijective (the S⁴ §2 sandwich, made
  generic). S²×S² minus a point is homotopy-`S²∨S²` (`H₄ = H₃ = 0`), so this is the exact shape
  the second witness's orientation input takes.

Every future witness's orientation datum thus reduces to: supply `E` + the two puncture vanishings.
Non-vacuity: S⁴ instantiates the device (`sphere4GlobalGenerator`), recovering the hand-built
section definitionally (kernel-checked `example` below).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/
`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SphereFourOrientationDataInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularIntFundamentalClassExist
open SKEFTHawking.IntOrientationSection
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularReducedGeneratorInt (intLocalHomologyIso_of_manifold')
open SKEFTHawking.SingularIntFundClassChartBall (intAddEquiv_apply_one_isUnit smul_symm_one)

namespace SKEFTHawking.IntOrientationGlobalSection

/-! ## §1. The pair-LES sandwich criterion at general M -/

/-- **Punctured acyclicity makes every point restriction bijective** (integral, general `M`): if
`H₄(M∖z;ℤ) = 0` and `H₃(M∖z;ℤ) = 0` then the pair-LES sandwich
`H₄(M∖z) → H₄(M) → H₄(M|z) → H₃(M∖z)` forces `ρ_z : H₄(M;ℤ) → H₄(M|z;ℤ)` bijective — injectivity
from exactness at `H₄(M)` (`exact_homIncl_homProjInt`), surjectivity from exactness at `H₄(M|z)`
(`exact_homProjInt_connectingInt`). The S⁴ §2 sandwich (`restrictHomologyToPointInt_sphere4_bijective`)
with the sphere-specific acyclicity abstracted into the two hypotheses. -/
theorem restrictHomologyToPointInt_bijective_of_punctured_acyclic
    {M : Type} [TopologicalSpace M] (z : M)
    (h4 : ∀ x : Homology (sub ({p | p ≠ z} : Set ↑(TopCat.of M))) 4, x = 0)
    (h3 : ∀ x : Homology (sub ({p | p ≠ z} : Set ↑(TopCat.of M))) 3, x = 0) :
    Function.Bijective (restrictHomologyToPointInt (X := TopCat.of M) z 4) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨w, hw⟩ := (SKEFTHawking.SingularSphereHomologyInt.exact_homIncl_homProjInt
      ({y | y ≠ z} : Set ↑(TopCat.of M)) 4 a).mp ha
    rw [← hw, h4 w, map_zero]
  · intro y
    have h0 : connectingInt ({y | y ≠ z} : Set ↑(TopCat.of M)) 3 y = 0 := h3 _
    exact (SKEFTHawking.SingularLocalHomologyInt.exact_homProjInt_connectingInt
      ({y | y ≠ z} : Set ↑(TopCat.of M)) 3 y).mp h0

/-! ## §2. The global-generator datum and its recorded section -/

/-- **A global integral generator class on `M`**: a class of `H₄(M;ℤ)` whose restriction to the
local homology `H₄(M|z;ℤ) ≅ ℤ` is a generator (unit coordinate in the proved local iso) at EVERY
point. This is the exact input the choice-absorbing orientation section records — no normalisation
of the per-point coordinate is ever asserted, so the datum is insensitive to Mathlib's per-point
`stdOrthonormalBasis` choices. -/
structure IntGlobalGenerator (M : Type) [TopologicalSpace M] [T1Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] where
  /-- The global class. -/
  cls : Homology (TopCat.of M) 4
  /-- Its point restriction is a generator at every point. -/
  unit : ∀ z : M, IsUnit ((intLocalHomologyIso_of_manifold' z).iso
    (restrictHomologyToPointInt (X := TopCat.of M) z 4 cls))

variable {M : Type} [TopologicalSpace M] [T1Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]

/-- **The recorded (choice-absorbing) orientation section** of a global generator class:
`orient z := iso_z (ρ_z cls)` — the coordinate of the restricted global class in the `chartAt z`-
pinned local iso. Whatever orientation pattern the per-point choices realise, the section RECORDS
it instead of fighting it. -/
noncomputable def IntGlobalGenerator.orient (d : IntGlobalGenerator M) (z : M) : ℤ :=
  (intLocalHomologyIso_of_manifold' z).iso
    (restrictHomologyToPointInt (X := TopCat.of M) z 4 d.cls)

/-- The recorded section is `±1`-valued. -/
theorem IntGlobalGenerator.orient_unit (d : IntGlobalGenerator M) (z : M) :
    d.orient z = 1 ∨ d.orient z = -1 :=
  Int.isUnit_iff.mp (d.unit z)

/-- **The global class restricts at every point to the oriented local generator** — definitionally,
because the section is defined as the restricted class's coordinate:
`ρ_z cls = iso_z⁻¹(orient z) = orient z • iso_z⁻¹(1)`. The general form of `sphere4Gen_restricts`;
this definitional law is the entire content of absorbing the choice-pattern into the section. -/
theorem IntGlobalGenerator.cls_restricts (d : IntGlobalGenerator M) (z : M) :
    restrictHomologyToPointInt (X := TopCat.of M) z 4 d.cls
      = orientedLocalGenerator z (d.orient z) := by
  rw [orientedLocalGenerator, SKEFTHawking.SingularRelHomologyInt.localGenerator, smul_symm_one,
    IntGlobalGenerator.orient, AddEquiv.symm_apply_apply]

/-! ## §3. Per-ball realisability and THE DATUM at general M -/

/-- **Every chart ball realises the recorded section** — the `hballs` input of the `univ`
induction, discharged by restricting the GLOBAL class to the ball (`restrictHomologyToSetInt`) and
factoring point restrictions through it. Generic form of `sphere4_hballs`: realising a PRESCRIBED
section against the chartAt-pinned generators is choice-sensitive, realising the RECORDED section
is definitional. -/
theorem IntGlobalGenerator.hballs (d : IntGlobalGenerator M) :
    ∀ (x : M) (ρ : ℝ), 0 ≤ ρ →
      Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin 4)) x x) ρ
        ⊆ (chartAt (EuclideanSpace ℝ (Fin 4)) x).target →
      hasOrientedFundClassInt d.orient
        ((chartAt (EuclideanSpace ℝ (Fin 4)) x).symm ''
          Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin 4)) x x) ρ) := by
  intro x ρ hρ hsub
  refine ⟨SKEFTHawking.SingularBaseCaseD0Int.restrictHomologyToSetInt (X := TopCat.of M)
    _ 4 d.cls, ?_⟩
  intro y hy
  rw [SKEFTHawking.SingularBaseCaseD0Int.restrictToPoint_restrictHomologyToSetInt hy 4,
    d.cls_restricts y]

/-- **THE ORIENTATION DATUM AT GENERAL M**: a global generator class yields the full
`IntOrientationData M` — the recorded section, its `±1`-valuedness, per-ball realisability, and the
proved 18e–18h chain (`hasOrientedFundClassInt_univ` → `intFundClass` / `intFundClass_restricts` /
`redCompat_intFundClass`). The general form of `sphere4IntOrientationDataUncond`: every future
witness's orientation input reduces to supplying an `IntGlobalGenerator`. -/
noncomputable def IntGlobalGenerator.orientationData
    {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
    [PreconnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (d : IntGlobalGenerator M) : IntOrientationData M :=
  haveI hUniv := SKEFTHawking.SingularIntFundClassUnivInt.hasOrientedFundClassInt_univ
    (M := M) d.orient d.hballs
  { orient := d.orient
    orient_unit := d.orient_unit
    fundClass := SKEFTHawking.SingularIntOrientationDataConstruct.intFundClass hUniv
    restricts := SKEFTHawking.SingularIntOrientationDataConstruct.intFundClass_restricts hUniv
    redCompat := SKEFTHawking.SingularIntOrientationDataConstruct.redCompat_intFundClass hUniv
      d.orient_unit }

/-! ## §4. Constructors: generator supply, and the punctured-acyclicity criterion -/

set_option maxRecDepth 4000 in
/-- **The generator-supply constructor**: any equivalence `E : H₄(M;ℤ) ≃+ ℤ` together with
bijectivity of every point restriction yields a global generator class — take `cls := E.symm 1`;
the composite `ℤ ≃ H₄(M;ℤ) ≃ H₄(M|z;ℤ) ≃ ℤ` is an additive automorphism of `ℤ`, so it sends `1`
to a unit (`intAddEquiv_apply_one_isUnit`). The S⁴ §3 unit argument (`sphere4Orient_unit`), made
generic — with the automorphism packaged as an `AddEquiv` instead of the by-hand linear map.
(`maxRecDepth` raised for the one composite-apply defeq seam `(E.symm.trans …).trans iso 1 =
iso (ρ_z (E.symm 1))` — elaborator stack depth, not a compute budget; invariant #10 concerns
`maxHeartbeats` only, same precedent as `sphere4Orient_unit`.) -/
noncomputable def intGlobalGeneratorOfEquiv (E : Homology (TopCat.of M) 4 ≃+ ℤ)
    (hbij : ∀ z : M, Function.Bijective (restrictHomologyToPointInt (X := TopCat.of M) z 4)) :
    IntGlobalGenerator M where
  cls := E.symm 1
  unit z := intAddEquiv_apply_one_isUnit
    ((E.symm.trans (AddEquiv.ofBijective
      (restrictHomologyToPointInt (X := TopCat.of M) z 4).toAddMonoidHom (hbij z))).trans
      (intLocalHomologyIso_of_manifold' z).iso)

/-- **The punctured-acyclicity constructor**: `E : H₄(M;ℤ) ≃+ ℤ` plus the two puncture vanishings
`H₄(M∖z;ℤ) = H₃(M∖z;ℤ) = 0` at every point yield the global generator datum — the sandwich (§1)
supplies bijectivity pointwise. The complete general-M reduction: an orientation datum from one
global computation plus two local vanishing computations. -/
noncomputable def intGlobalGeneratorOfPuncturedAcyclic (E : Homology (TopCat.of M) 4 ≃+ ℤ)
    (h4 : ∀ (z : M) (x : Homology (sub ({p | p ≠ z} : Set ↑(TopCat.of M))) 4), x = 0)
    (h3 : ∀ (z : M) (x : Homology (sub ({p | p ≠ z} : Set ↑(TopCat.of M))) 3), x = 0) :
    IntGlobalGenerator M :=
  intGlobalGeneratorOfEquiv E fun z =>
    restrictHomologyToPointInt_bijective_of_punctured_acyclic z (h4 z) (h3 z)

/-! ## §5. Non-vacuity: S⁴ instantiates the device -/

open SKEFTHawking.SphereWitnessTowerInt (SphereFour)
open SKEFTHawking.SingularLineMinusPointInt (topSphereIsoInt)

/-- **S⁴ through the general device**: the in-tree sphere-tower equivalence + the proved point-
restriction bijectivity instantiate `IntGlobalGenerator SphereFour`. Non-vacuity witness for the
class-level construction; its recorded section recovers the hand-built `sphere4Orient`
definitionally (kernel-checked example below). -/
noncomputable def sphere4GlobalGenerator : IntGlobalGenerator SphereFour :=
  intGlobalGeneratorOfEquiv (topSphereIsoInt 3).toAddEquiv
    SKEFTHawking.SphereFourOrientationDataInt.restrictHomologyToPointInt_sphere4_bijective

set_option maxRecDepth 4000 in
example : sphere4GlobalGenerator.orient
    = SKEFTHawking.SphereFourOrientationDataInt.sphere4Orient := rfl

end SKEFTHawking.IntOrientationGlobalSection
