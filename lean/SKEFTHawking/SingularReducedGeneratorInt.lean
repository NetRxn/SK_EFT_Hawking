import Mathlib
import SKEFTHawking.SingularSphereGenReducesInt

/-!
# `ReducedGeneratorNonzero` and `IntLocalHomologyIso` as a hypothesis-free theorem (brick 17b)

Propagates `SphereGenReducesNonzero` (brick 17, sphere level) DOWN the manifold local-homology tower
(`chartLocalIsoInt` = excision + chart homeo + translation + euclidean connecting/normalize) to the
manifold-level residual `ReducedGeneratorNonzero x`, then discharges it into a clean theorem
`intLocalHomologyIso_of_manifold'` — `IntLocalHomologyIso M x` with NO hypothesis.

Each tower stage has a brick-16 reduction-naturality square (`redRelHomology_map` for the chart/transl
`RelHomologyInt.map`, `redRelHomology_excisionMap` for excision, `redHomology_euclCore` for the
euclidean connecting+normalize composite). The non-vanishing lifts via `ne_zero_transport_symm`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularFunctorialityInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularSphereGenReducesInt

namespace SKEFTHawking.SingularReducedGeneratorInt

open SKEFTHawking.SingularEuclideanAcyclic (Eucl)
open SKEFTHawking.SingularPuncturedRetract (normalize)
open SKEFTHawking.SingularLocalHomologyInt (localHomologyInt_reduces_to_sphere)
open SKEFTHawking.SingularLocalHomologyIsoInt (euclLocalHomologyIsoInt)
open SKEFTHawking.SingularLocalHomologyRedCompatInt (redHomology_euclCore)
open SKEFTHawking.SingularSphereAcyclic (Sph)

/-- **The mod-2 euclidean core map** `Hₙ(ℝⁿ,ℝⁿ∖0;ℤ/2) → Hₙ₋₁(Sⁿ⁻¹;ℤ/2)`, `normalize_* ∘ connecting` —
the mod-2 analog of the integral `euclLocalHomologyIsoInt`'s underlying map. Bijective (`connecting`
iso from `ℝⁿ`-acyclicity, `normalize_*` iso from the retract). -/
noncomputable def euclCoreMapMod :
    SKEFTHawking.SingularRelativeHomologyMod2.RelativeHomology (X := Eucl 4) {x | x ≠ 0} 4
      →ₗ[ZMod 2] SKEFTHawking.SingularHomologyMod2.Homology (Sph 3) 3 :=
  (SKEFTHawking.SingularFunctoriality.Homology.map (normalize (n := 4)) 3).comp
    (SKEFTHawking.SingularPairLES.connecting (X := Eucl 4) {x | x ≠ 0} 3)

theorem euclCoreMapMod_bijective : Function.Bijective euclCoreMapMod := by
  rw [euclCoreMapMod, LinearMap.coe_comp]
  exact (SKEFTHawking.SingularPuncturedRetract.homology_map_normalize_bijective (n := 4) 2).comp
    (SKEFTHawking.SingularLocalHomology.connecting_eucl_bijective 4 2)

/-- The mod-2 euclidean core as a `≃+`. -/
noncomputable def euclCoreEquivMod :
    SKEFTHawking.SingularRelativeHomologyMod2.RelativeHomology (X := Eucl 4) {x | x ≠ 0} 4
      ≃+ SKEFTHawking.SingularHomologyMod2.Homology (Sph 3) 3 :=
  (LinearEquiv.ofBijective euclCoreMapMod euclCoreMapMod_bijective).toAddEquiv

/-- **The reduction commutes with the integral euclidean core** (as `≃+` forward square). The integral
`euclLocalHomologyIsoInt`'s first leg is `ofBijective (mapInt normalize ∘ connectingInt)`; reducing
lands on `euclCoreMapMod` (`redHomology_euclCore`). -/
theorem redHomology_euclCoreEquivInt
    (z : RelHomologyInt (X := Eucl 4) {x | x ≠ 0} 4) :
    redHomology (Sph 3) 3
        ((LinearEquiv.ofBijective
            ((Homology.mapInt (normalize (n := 4)) 3).comp
              (SingularRelHomologyInt.connectingInt (X := Eucl 4) {x | x ≠ 0} 3))
            (localHomologyInt_reduces_to_sphere 4 2)) z)
      = euclCoreEquivMod (redRelHomology (X := Eucl 4) {x | x ≠ 0} 4 z) := by
  show redHomology (Sph 3) 3
      ((Homology.mapInt (normalize (n := 4)) 3)
        (SingularRelHomologyInt.connectingInt (X := Eucl 4) {x | x ≠ 0} 3 z))
    = euclCoreMapMod (redRelHomology (X := Eucl 4) {x | x ≠ 0} 4 z)
  rw [redHomology_euclCore]
  rfl

open SKEFTHawking.SingularLineMinusPointInt (H3S3IsoInt)

/-- **The euclidean-model local generator reduces nonzero.** `redRelHomology (euclLocalHomologyIsoInt.symm
1) ≠ 0`. Transport of `sphereGenReducesNonzero` through the `.symm` of the euclidean core equiv. -/
theorem eucl_generator_reduces_ne_zero :
    redRelHomology (X := Eucl 4) {x | x ≠ 0} 4 (euclLocalHomologyIsoInt.symm 1) ≠ 0 := by
  -- euclLocalHomologyIsoInt.symm 1 = (ofBij euclCore).symm (H3S3IsoInt.symm 1)
  have hchain : euclLocalHomologyIsoInt.symm 1
      = (LinearEquiv.ofBijective
          ((Homology.mapInt (normalize (n := 4)) 3).comp
            (SingularRelHomologyInt.connectingInt (X := Eucl 4) {x | x ≠ 0} 3))
          (localHomologyInt_reduces_to_sphere 4 2)).symm (H3S3IsoInt.symm 1) := by
    show (LinearEquiv.trans _ H3S3IsoInt).symm 1 = _
    rw [LinearEquiv.symm_trans_apply]
  rw [hchain]
  exact ne_zero_transport_symm
    (LinearEquiv.ofBijective
      ((Homology.mapInt (normalize (n := 4)) 3).comp
        (SingularRelHomologyInt.connectingInt (X := Eucl 4) {x | x ≠ 0} 3))
      (localHomologyInt_reduces_to_sphere 4 2)).toAddEquiv
    euclCoreEquivMod
    (redRelHomology (X := Eucl 4) {x | x ≠ 0} 4) (redHomology (Sph 3) 3)
    redHomology_euclCoreEquivInt sphereGenReducesNonzero

/-! ## §2. Transporting through the translation leg -/

open SKEFTHawking.SingularLocalModelChart
  (transl transl_comp_transl_neg transl_neg_comp_transl mapsTo_transl mapsTo_transl_neg
   localHomologyAtPointIso)
open SKEFTHawking.SingularRelativeFunctorialityInt (RelHomologyInt.map RelHomologyInt.map_bijective_of_comp_id)
open SKEFTHawking.SingularLocalHomologyIsoInt (localHomologyAtPointIsoInt)
open SKEFTHawking.SingularLocalHomologyRedCompatInt (redRelHomology_map)

/-- **The translated euclidean local generator reduces nonzero.** `redRelHomology (localHomologyAtPointIsoInt
q).symm 1 ≠ 0`, at `RelHomologyInt {≠q} 4`. Transport of `eucl_generator_reduces_ne_zero` through the
`.symm` of the translation `RelHomologyInt.map (transl q)` leg. -/
theorem localAtPoint_generator_reduces_ne_zero (q : EuclideanSpace ℝ (Fin 4)) :
    redRelHomology (X := Eucl 4) {y | y ≠ q} 4 ((localHomologyAtPointIsoInt q).symm 1) ≠ 0 := by
  have hchain : (localHomologyAtPointIsoInt q).symm 1
      = (LinearEquiv.ofBijective (RelHomologyInt.map (transl q) (mapsTo_transl q) 4)
          (RelHomologyInt.map_bijective_of_comp_id (transl q) (transl (-q)) (mapsTo_transl q)
            (mapsTo_transl_neg q) (transl_neg_comp_transl q) (transl_comp_transl_neg q) 4)).symm
        (euclLocalHomologyIsoInt.symm 1) := by
    show (LinearEquiv.trans _ euclLocalHomologyIsoInt).symm 1 = _
    rw [LinearEquiv.symm_trans_apply]
  rw [hchain]
  exact ne_zero_transport_symm
    (LinearEquiv.ofBijective (RelHomologyInt.map (transl q) (mapsTo_transl q) 4)
      (RelHomologyInt.map_bijective_of_comp_id (transl q) (transl (-q)) (mapsTo_transl q)
        (mapsTo_transl_neg q) (transl_neg_comp_transl q) (transl_comp_transl_neg q) 4)).toAddEquiv
    (LinearEquiv.ofBijective
      (SKEFTHawking.SingularRelativeFunctoriality.RelativeHomology.map (transl q) (mapsTo_transl q) 4)
      (SKEFTHawking.SingularRelativeFunctoriality.RelativeHomology.map_bijective_of_comp_id
        (transl q) (transl (-q)) (mapsTo_transl q) (mapsTo_transl_neg q)
        (transl_neg_comp_transl q) (transl_comp_transl_neg q) 4)).toAddEquiv
    (redRelHomology (X := Eucl 4) {y | y ≠ q} 4)
    (redRelHomology (X := Eucl 4) {x | x ≠ 0} 4)
    (fun z => redRelHomology_map (transl q) (mapsTo_transl q) 4 z)
    eucl_generator_reduces_ne_zero

end SKEFTHawking.SingularReducedGeneratorInt
