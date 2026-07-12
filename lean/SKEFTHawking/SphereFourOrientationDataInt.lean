/-
# Phase 5q.H — the UNCONDITIONAL S⁴ integral orientation datum (the choice-absorbing global section)

Round 5 (`SphereWitnessFiringInt`) isolated the S⁴ orientation freeze `Sphere4ChartBallsOriented`:
the CONSTANT `+1` section is realisable on every chart ball, i.e. some class restricts at every `y`
to the `+1` local generator *pinned to Mathlib's `chartAt y`*. Working the assigned moving-puncture
discharge exposed a STATEMENT-LEVEL wall, and this module ships the honest replacement:

**The wall (why the `+1`-normalised freeze is not provable as stated).** The pinned local generator
at `y` is built through `chartAt y = stereographic' 4 (-y)`, whose identification of `(ℝ∙(-y))ᗮ`
with `ℝ⁴` is `OrthonormalBasis.fromOrthogonalSpanSingleton` = a `stdOrthonormalBasis`, i.e. a
`Classical.choose`-picked basis chosen INDEPENDENTLY per point `y` (an `irreducible_def` over
`exists_orthonormalBasis`). The SIGN of the pinned generator at `y` therefore carries the
orientation of an opaque per-point basis choice, with no axiom or lemma relating the choices at two
different points. A constant-`+1` section against these generators on a positive-radius ball would
pin uncountably many independent choice-orientations to a single coherent pattern — nothing in the
kernel's interface to `Classical.choice` can prove (or refute) that. The freeze (and any
`orient ≡ 1`-normalised orientation datum for Mathlib's sphere atlas) is choice-sensitive:
NOT provable, NOT refutable. The moving-puncture device can compare generators transported through
a FIXED chart (that part is honest geometry), but never across two `chartAt`-pinned charts.

**The fix (this module): absorb the choice-pattern into the section.** `IntOrientationData` never
needed `orient ≡ 1` — the section is data. On S⁴ the global class is available OUTRIGHT:
`S⁴ ∖ {z} ≅ ℝ⁴` (stereographic projection FROM `z`), so `H₄(S⁴∖z;ℤ) = H₃(S⁴∖z;ℤ) = 0`, and the
integral pair LES forces `ρ_z : H₄(S⁴;ℤ) → H₄(S⁴|z;ℤ)` bijective at EVERY `z` (§1–§2). Taking the
in-tree generator `g = (topSphereIsoInt 3).symm 1` of `H₄(S⁴;ℤ) ≅ ℤ`, the section
`orient z := iso_z (ρ_z g)` is `±1`-valued (an additive automorphism of `ℤ` sends `1` to a unit)
and `ρ_z g = orientedLocalGenerator z (orient z)` holds DEFINITIONALLY — no cross-chart coherence
is ever compared (§3). Every chart ball then realises THIS global section (restrict `g`, §4), the
proved 18e–18h chain glues `hasOrientedFundClassInt orient univ`, and the FULL
`IntOrientationData SphereFour` lands with NO hypothesis (`sphere4IntOrientationDataUncond`).

The `orient ≡ 1` normalisation consumed by the round-5 leg is weakened downstream
(`SingularBaseCaseD0OrientInt` / `SphereWitnessFiringUncondInt`): the leg's PD tower uses the
normalisation only through `E g = 1` for the generic UC-flip, which a `±1` section supplies after
conjugating `E` by the sign.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/
`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SphereWitnessFiringInt
import SKEFTHawking.SingularIntFundClassUnivInt
import SKEFTHawking.SingularBaseCaseD0Int
import SKEFTHawking.SingularSphereHomologyInt
import SKEFTHawking.SingularLocalHomologyInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularFunctorialityInt
open SKEFTHawking.SingularSphereAcyclic (Sph)
open SKEFTHawking.SingularEuclideanAcyclic (Eucl)
open SKEFTHawking.SingularIntFundamentalClassExist
open SKEFTHawking.IntOrientationSection
open SKEFTHawking.SphereWitnessTowerInt (SphereFour)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularLineMinusPointInt (topSphereIsoInt)
open SKEFTHawking.SingularReducedGeneratorInt (intLocalHomologyIso_of_manifold')
open SKEFTHawking.SingularIntFundClassChartBall (intAddEquiv_apply_one_isUnit smul_symm_one)

namespace SKEFTHawking.SphereFourOrientationDataInt

/-! ## §1. The punctured 4-sphere is integrally acyclic in positive degrees -/

/-- **The punctured 4-sphere is homeomorphic to `ℝ⁴`** — stereographic projection FROM the deleted
point `z` (`stereographic' 4 z`: source exactly `{z}ᶜ`, target all of `ℝ⁴`). The geometric input
that makes the point-restriction `ρ_z` a global iso on S⁴. -/
noncomputable def puncturedSphereHomeo (z : SphereFour) :
    ↥({p : SphereFour | p ≠ z}) ≃ₜ EuclideanSpace ℝ (Fin 4) :=
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 5)) = 4 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  (Homeomorph.setCongr (show ({p : SphereFour | p ≠ z} : Set SphereFour)
        = (stereographic' 4 z).source by rw [stereographic'_source]; rfl)).trans
    ((stereographic' 4 z).toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr (stereographic'_target z)).trans (Homeomorph.Set.univ _)))

/-- **Transport of integral-homology triviality along mutually-inverse continuous maps**: if
`g ∘ f = id` and `Hₙ(Y;ℤ) = 0` then every class of `Hₙ(X;ℤ)` dies (it factors through `Hₙ(Y;ℤ)`). -/
theorem homology_eq_zero_of_comp_id {X Y : TopCat} (f : C(↑X, ↑Y)) (g : C(↑Y, ↑X))
    (hgf : g.comp f = ContinuousMap.id ↑X) (n : ℕ)
    (hY : ∀ y : Homology Y n, y = 0) (x : Homology X n) : x = 0 :=
  calc x = Homology.mapInt (ContinuousMap.id ↑X) n x := by rw [Homology.mapInt_id]; rfl
  _ = Homology.mapInt (g.comp f) n x := by rw [hgf]
  _ = Homology.mapInt g n (Homology.mapInt f n x) := by rw [Homology.mapInt_comp]; rfl
  _ = Homology.mapInt g n 0 := by rw [hY (Homology.mapInt f n x)]
  _ = 0 := map_zero _

/-- **`Hₖ₊₁(S⁴∖z; ℤ) = 0`** — the punctured 4-sphere is integrally acyclic in positive degrees
(homeomorphic to `ℝ⁴`, which is integrally acyclic). At `k = 2, 3` these are the two vanishings the
pair-LES sandwich for `ρ_z` consumes. -/
theorem punctured_sphere4_homology_eq_zero (z : SphereFour) (k : ℕ)
    (x : Homology (sub ({p | p ≠ z} : Set ↑(TopCat.of SphereFour))) (k + 1)) : x = 0 :=
  homology_eq_zero_of_comp_id
    (⟨puncturedSphereHomeo z, (puncturedSphereHomeo z).continuous⟩ :
      C(↑(sub ({p | p ≠ z} : Set ↑(TopCat.of SphereFour))), ↑(Eucl 4)))
    (⟨(puncturedSphereHomeo z).symm, (puncturedSphereHomeo z).symm.continuous⟩ :
      C(↑(Eucl 4), ↑(sub ({p | p ≠ z} : Set ↑(TopCat.of SphereFour)))))
    (ContinuousMap.ext fun p => (puncturedSphereHomeo z).symm_apply_apply p) (k + 1)
    (SKEFTHawking.SingularLocalHomologyInt.eucl_homology_trivialInt 4 k) x

/-! ## §2. The point restriction `ρ_z : H₄(S⁴;ℤ) → H₄(S⁴|z;ℤ)` is bijective at every point -/

/-- **The point restriction is BIJECTIVE at every point of S⁴** (integral): the pair-LES sandwich
`H₄(S⁴∖z) → H₄(S⁴) → H₄(S⁴|z) → H₃(S⁴∖z)` with both outer groups `0`
(`punctured_sphere4_homology_eq_zero`), using the in-tree integral exactness at `H₄(X)`
(`exact_homIncl_homProjInt`) and at `H₄(X,S)` (`exact_homProjInt_connectingInt`). This is what
lets S⁴ take its orientation section from a single GLOBAL generator — no chart-to-chart
sign comparison ever happens. -/
theorem restrictHomologyToPointInt_sphere4_bijective (z : SphereFour) :
    Function.Bijective (restrictHomologyToPointInt (X := TopCat.of SphereFour) z 4) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨w, hw⟩ := (SKEFTHawking.SingularSphereHomologyInt.exact_homIncl_homProjInt
      ({y | y ≠ z} : Set ↑(TopCat.of SphereFour)) 4 a).mp ha
    have hw0 : w = 0 := punctured_sphere4_homology_eq_zero z 3 w
    rw [← hw, hw0, map_zero]
  · intro y
    have h0 : connectingInt ({y | y ≠ z} : Set ↑(TopCat.of SphereFour)) 3 y = 0 :=
      punctured_sphere4_homology_eq_zero z 2 _
    exact (SKEFTHawking.SingularLocalHomologyInt.exact_homProjInt_connectingInt
      ({y | y ≠ z} : Set ↑(TopCat.of SphereFour)) 3 y).mp h0

/-! ## §3. The choice-absorbing orientation section from the global generator -/

/-- **The global integral fundamental class of S⁴**: the generator `(topSphereIsoInt 3).symm 1` of
`H₄(S⁴;ℤ) ≅ ℤ` — computed by the in-tree integral sphere tower, chart-free. -/
noncomputable def sphere4GenInt : Homology (TopCat.of SphereFour) 4 :=
  (topSphereIsoInt 3).symm 1

/-- **The choice-absorbing S⁴ orientation section**: `orient z := iso_z (ρ_z g)` — the coordinate of
the restricted global generator in the `chartAt z`-pinned local iso. Whatever orientation pattern
Mathlib's per-point `stdOrthonormalBasis` choices realise, this section RECORDS it instead of
fighting it; no cross-chart coherence is ever asserted. -/
noncomputable def sphere4Orient (z : SphereFour) : ℤ :=
  (intLocalHomologyIso_of_manifold' z).iso
    (restrictHomologyToPointInt (X := TopCat.of SphereFour) z 4 sphere4GenInt)

set_option maxRecDepth 4000 in
/-- **The section is `±1`-valued**: `orient z` is the image of `1` under the composite additive
automorphism `ℤ ≅ H₄(S⁴;ℤ) ≅ H₄(S⁴|z;ℤ) ≅ ℤ` (generator iso ∘ point restriction ∘ pinned local
iso), and an additive automorphism of `ℤ` sends `1` to a unit. (`maxRecDepth` raised for the one
sphere-spelling seam defeq `F 1 = sphere4Orient z` — elaborator stack depth, not a compute budget;
invariant #10 concerns `maxHeartbeats` only.) -/
theorem sphere4Orient_unit (z : SphereFour) : sphere4Orient z = 1 ∨ sphere4Orient z = -1 := by
  have hbij := restrictHomologyToPointInt_sphere4_bijective z
  let F : ℤ →ₗ[ℤ] ℤ :=
    ((intLocalHomologyIso_of_manifold' z).iso.toAddMonoidHom.toIntLinearMap.comp
      (restrictHomologyToPointInt (X := TopCat.of SphereFour) z 4)).comp
      (topSphereIsoInt 3).symm.toLinearMap
  have hF1 : F 1 = sphere4Orient z := rfl
  have hFbij : Function.Bijective ⇑F :=
    (((intLocalHomologyIso_of_manifold' z).iso.bijective.comp hbij).comp
      (topSphereIsoInt 3).symm.bijective : Function.Bijective
        (⇑(intLocalHomologyIso_of_manifold' z).iso ∘
          (⇑(restrictHomologyToPointInt (X := TopCat.of SphereFour) z 4) ∘
            ⇑(topSphereIsoInt 3).symm)))
  obtain ⟨t₀, ht₀⟩ := hFbij.surjective 1
  have hsm : F t₀ = t₀ * F 1 := by
    conv_lhs => rw [show t₀ = t₀ • (1 : ℤ) by rw [smul_eq_mul, mul_one]]
    rw [map_smul, smul_eq_mul]
  have hunit : IsUnit (F 1) :=
    ⟨Units.mkOfMulEqOne (F 1) t₀ (show F 1 * t₀ = 1 by rw [mul_comm, ← hsm, ht₀]), rfl⟩
  rw [← hF1]
  exact Int.isUnit_iff.mp hunit

/-- **The global generator restricts at EVERY point to the oriented local generator** — the
`restricts` law holds definitionally for the recorded section: `ρ_z g = iso_z⁻¹(orient z)
= orient z • iso_z⁻¹(1)`. This is the whole point of absorbing the choice-pattern into `orient`. -/
theorem sphere4Gen_restricts (z : SphereFour) :
    restrictHomologyToPointInt (X := TopCat.of SphereFour) z 4 sphere4GenInt
      = orientedLocalGenerator z (sphere4Orient z) := by
  rw [orientedLocalGenerator, SKEFTHawking.SingularRelHomologyInt.localGenerator, smul_symm_one,
    sphere4Orient, AddEquiv.symm_apply_apply]

/-! ## §4. Per-ball realisability of the global section, and THE DATUM -/

/-- **Every chart ball of S⁴ realises the global section** — the `hballs` input of the 18g `univ`
induction, discharged for `sphere4Orient` by restricting the GLOBAL generator to the ball
(`restrictHomologyToSetInt`) and factoring point restrictions through it
(`restrictToPoint_restrictHomologyToSetInt`). Contrast with the frozen constant-`+1` form
(`Sphere4ChartBallsOriented`): realising a PRESCRIBED section against the chartAt-pinned
generators is choice-sensitive; realising the RECORDED section is definitional. -/
theorem sphere4_hballs :
    ∀ (x : SphereFour) (ρ : ℝ), 0 ≤ ρ →
      Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin 4)) x x) ρ
        ⊆ (chartAt (EuclideanSpace ℝ (Fin 4)) x).target →
      hasOrientedFundClassInt sphere4Orient
        ((chartAt (EuclideanSpace ℝ (Fin 4)) x).symm ''
          Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin 4)) x x) ρ) := by
  intro x ρ hρ hsub
  refine ⟨SKEFTHawking.SingularBaseCaseD0Int.restrictHomologyToSetInt (X := TopCat.of SphereFour)
    _ 4 sphere4GenInt, ?_⟩
  intro y hy
  rw [SKEFTHawking.SingularBaseCaseD0Int.restrictToPoint_restrictHomologyToSetInt hy 4,
    sphere4Gen_restricts y]

/-- **THE UNCONDITIONAL S⁴ INTEGRAL ORIENTATION DATUM.** The full `IntOrientationData SphereFour`
with NO hypothesis: the choice-absorbing global section (§3), its per-ball realisability (§4), and
the proved 18e–18h chain (`hasOrientedFundClassInt_univ` → `intFundClass` / `intFundClass_restricts`
/ `redCompat_intFundClass`). This replaces the choice-sensitive freeze route
(`Sphere4ChartBallsOriented` + `sphere4IntOrientationData`) with a theorem-backed datum. -/
noncomputable def sphere4IntOrientationDataUncond : IntOrientationData SphereFour :=
  haveI hUniv := SKEFTHawking.SingularIntFundClassUnivInt.hasOrientedFundClassInt_univ
    (M := SphereFour) sphere4Orient sphere4_hballs
  { orient := sphere4Orient
    orient_unit := sphere4Orient_unit
    fundClass := SKEFTHawking.SingularIntOrientationDataConstruct.intFundClass hUniv
    restricts := SKEFTHawking.SingularIntOrientationDataConstruct.intFundClass_restricts hUniv
    redCompat := SKEFTHawking.SingularIntOrientationDataConstruct.redCompat_intFundClass hUniv
      sphere4Orient_unit }

end SKEFTHawking.SphereFourOrientationDataInt
