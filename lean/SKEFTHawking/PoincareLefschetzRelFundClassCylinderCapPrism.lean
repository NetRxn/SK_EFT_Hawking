import Mathlib
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderCapProj
import SKEFTHawking.SingularCapCrossProjection
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderNumerics

/-!
# Phase 5q.H Track 2 B2 — the cylinder cap-cross projection from the normalization residual

Instantiates the generic Eilenberg–Zilber cap-cross projection
`SingularCapCrossProjection.capRelH_crossH_of_prismDegNull` at the reflexive cylinder to discharge the
residual `CapCrossPullbackProj{23,14}` of `…CylinderCapProj` — gated on the single classical residual
`PrismDegNull` (singular normalization: the `t`-independent projection prism is null-homologous). The
`fst_*` injectivity input is supplied concretely (`prodFst_homology_bijective` at the contractible
interval factor). With `CapCrossPullbackProj{23,14}` in hand, the nondeg side of `CylinderWAdmPinned`
(via `ofClosedPDSuspIntertwinePullbackProj`) consumes only the normalization residual + `{hwu, basePD,
M-finiteness}`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
new `axiom`.
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularCohomologyFunctoriality SKEFTHawking.SingularKroneckerFunctoriality
open SKEFTHawking.SingularCapHomology SKEFTHawking.SingularRelativeCapHomology
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.SingularCapCrossProjection
open SKEFTHawking.SingularFundamentalClass
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCross
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderIntertwine
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspDual
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderNumerics
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCapProj

namespace SKEFTHawking.PoincareLefschetzRelFundClassCylinderCapPrism

noncomputable section

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]

omit [T2Space M] [CompactSpace M] [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M] in
/-- `cylCollapse2.symm` on a representative cocycle IS the `fst`-pullback class (`π* = fst^*`, `rfl`). -/
theorem cylCollapse2_symm_mk (g : LinearMap.ker (coboundaryₗ (TopCat.of M) 2)) :
    cylCollapse2 (M := M).symm (Cohomology.mk (TopCat.of M) 2 g)
      = Cohomology.mk (cyl (TopCat.of M)) 2
          ⟨pullbackCochainMap (fstCyl (TopCat.of M)) 2 g.1,
            coboundary_pullback_fstCyl_eq_zero g.1 g.2⟩ :=
  rfl

omit [T2Space M] [CompactSpace M] [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M] in
/-- `cylCollapse1.symm` on a representative cocycle IS the `fst`-pullback class (`rfl`). -/
theorem cylCollapse1_symm_mk (g : LinearMap.ker (coboundaryₗ (TopCat.of M) 1)) :
    cylCollapse1 (M := M).symm (Cohomology.mk (TopCat.of M) 1 g)
      = Cohomology.mk (cyl (TopCat.of M)) 1
          ⟨pullbackCochainMap (fstCyl (TopCat.of M)) 1 g.1,
            coboundary_pullback_fstCyl_eq_zero g.1 g.2⟩ :=
  rfl

omit [T2Space M] [CompactSpace M] [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M] in
/-- `fst_*` is injective on `H₃(M × I)` (contractible interval factor, `prodFst_homology_bijective`). -/
theorem fstCyl_map_injective3 :
    Function.Injective (Homology.map (fstCyl (TopCat.of M)) 3) :=
  (prodFst_homology_bijective (TopCat.of M) (TopCat.of unitInterval) ⊥ iccContraction
    slice_iccContraction_zero slice_iccContraction_one 2).injective

omit [T2Space M] [CompactSpace M] [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M] in
/-- `fst_*` is injective on `H₄(M × I)`. -/
theorem fstCyl_map_injective4 :
    Function.Injective (Homology.map (fstCyl (TopCat.of M)) 4) :=
  (prodFst_homology_bijective (TopCat.of M) (TopCat.of unitInterval) ⊥ iccContraction
    slice_iccContraction_zero slice_iccContraction_one 3).injective

/-- **The `(2,3)` cap-cross pullback projection, from the normalization residual.** For any base class
`u ∈ H²(M)`, `(π* u) ⌢ ([M] × [I,∂I]) = (u ⌢ [M]) × [I,∂I]`, gated on `PrismDegNull` (singular
normalization) for a fundamental-cycle representative `z_fund`. -/
theorem capCrossPullbackProj23_of_prismDegNull
    (z_fund : cycles (TopCat.of M) 4)
    (hzfund : Homology.mk (TopCat.of M) 4 z_fund = fundamentalClass (m := 2))
    (hnull : ∀ (g : LinearMap.ker (coboundaryₗ (TopCat.of M) 2)),
      PrismDegNull (k := 2) (m := 1) g.1 z_fund.1)
    (u : Cohomology (TopCat.of M) 2) :
    CapCrossPullbackProj23 (M := M) u := by
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  show capRelH 2 2 (cylCollapse2 (M := M).symm (Cohomology.mk (TopCat.of M) 2 g))
        (crossH (slice_one_mapsTo (M := M) (m' := 2)) (slice_zero_mapsTo (M := M) (m' := 2)) 3
          (fundamentalClass (m := 2)))
      = crossH (slice_one_mapsTo (M := M) (m' := 2)) (slice_zero_mapsTo (M := M) (m' := 2)) 1
          (capH 2 1 (Cohomology.mk (TopCat.of M) 2 g) (fundamentalClass (m := 2)))
  rw [cylCollapse2_symm_mk, ← hzfund]
  exact capRelH_crossH_of_prismDegNull (slice_one_mapsTo (M := M) (m' := 2))
    (slice_zero_mapsTo (M := M) (m' := 2)) fstCyl_map_injective3 g z_fund (hnull g)

/-- **The `(1,4)` cap-cross pullback projection, from the normalization residual.** -/
theorem capCrossPullbackProj14_of_prismDegNull
    (z_fund : cycles (TopCat.of M) 4)
    (hzfund : Homology.mk (TopCat.of M) 4 z_fund = fundamentalClass (m := 2))
    (hnull : ∀ (g : LinearMap.ker (coboundaryₗ (TopCat.of M) 1)),
      PrismDegNull (k := 1) (m := 2) g.1 z_fund.1)
    (u : Cohomology (TopCat.of M) 1) :
    CapCrossPullbackProj14 (M := M) u := by
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  show capRelH 1 3 (cylCollapse1 (M := M).symm (Cohomology.mk (TopCat.of M) 1 g))
        (crossH (slice_one_mapsTo (M := M) (m' := 2)) (slice_zero_mapsTo (M := M) (m' := 2)) 3
          (fundamentalClass (m := 2)))
      = crossH (slice_one_mapsTo (M := M) (m' := 2)) (slice_zero_mapsTo (M := M) (m' := 2)) 2
          (capH 1 2 (Cohomology.mk (TopCat.of M) 1 g) (fundamentalClass (m := 2)))
  rw [cylCollapse1_symm_mk, ← hzfund]
  exact capRelH_crossH_of_prismDegNull (slice_one_mapsTo (M := M) (m' := 2))
    (slice_zero_mapsTo (M := M) (m' := 2)) fstCyl_map_injective4 g z_fund (hnull g)

end

end SKEFTHawking.PoincareLefschetzRelFundClassCylinderCapPrism
