/-
# Phase 5q.H (W-A arm 4, ROUND 5 fix) — THE HONEST CYLINDER REALIZATION (non-vacuity).

`PinPlusCharPairRealizationTied.GeoRealizationTied` is the derived-basis membrane-realization datum
that closes the round-5 gate finding F2 (its boundary homology bases are DERIVED from the carried
cohomology bases, never free). This module proves that datum is INHABITED by genuine compact-T2
geometry: for a closed surface `Σ` (a `TopCat` with `T2Space`/`CompactSpace`) carrying a cohomology
enhancement basis, the reflexive cylinder `Q = Σ × [0,1]` is a `GeoRealizationTied Σ Σ basis basis`.

Every piece is honest and per-object:

* `Q := Σ × [0,1]` is compact + T2 (product of compact/T2), with `H₁(Q) ≅ H₁(Σ)` collapsed through the
  contractible `[0,1]` factor (`prodContractibleHomologyEquiv`) then read in the DERIVED homology
  basis (`homologyBasisOfCohomologyBasis basis`).
* `∂Q := Σ ⊔ Σ` (the two cylinder ends) is compact + T2 (sum of compact/T2); the clopen split is
  `range Sum.inl`; each component identifies homeomorphically with `Σ` (`IsClosedEmbedding.inl/inr`).
* `ι : ∂Q → Q` is the two-slice inclusion `inl x ↦ (x,0)`, `inr x ↦ (x,1)` — continuous, injective,
  hence an `IsClosedEmbedding` (a continuous injection from a compact space to a Hausdorff space,
  `Continuous.isClosedEmbedding`).

The construction supplies EVERY field of the strengthened structure with real topology, so the
F2-fix shape is not vacuous.

**§2 — THE GEOMETRIC KERNEL IDENTITY (proved).** `cylRealizationTied_transportedBInc`:
`transportedBInc (cylRealizationTied Y basis).toData = cylBd n` (the fold `x ↦ (i ↦ x(inl i) + x(inr i))`),
whence `cylRealizationTied_toMembrane_L : (…toMembrane q q).L = cylLagrangian n` — the geometric
anti-diagonal, never a free field (F1 discharged on the cylinder). The homological core:
`homology_map_prodSect_eq_cylCollapse_symm` proves BOTH slice inclusions `prodSect ⊥`/`prodSect ⊤`
induce the SAME `H₁(Σ)` iso (`= (cylCollapse).symm`, since `prodFst ∘ prodSect c₀ = id` makes each a
right inverse of the bijection `H₁(prodFst)`); the boundary inclusion restricted to each end is that
slice (`cylBdryIncl_comp_subInclCM_left/right`), and `srcEquiv_symm_apply` +
`homIncl_eq_map`/`Homology.map_comp` assemble the two ends into the fold. This is exactly the homological
content that feeds the realization into the tied op witnesses (Stage 3/4).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusCharPairRealizationTied
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderNumerics
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspension

open Topology unitInterval
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularKroneckerBasisBridge
open SKEFTHawking.SingularPairLES SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularCohomologyPairRestrict
open SKEFTHawking.SingularProdContractibleInt
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderNumerics
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspension
open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic
open SKEFTHawking.PinPlusCharPairData (cylBd cylLagrangian)
open SKEFTHawking.PinPlusCharPairMembraneGeoRealization
open SKEFTHawking.PinPlusCharPairRealizationTied

namespace SKEFTHawking.PinPlusCharPairCylRealization

variable {n : ℕ} (Y : TopCat) [T2Space (Y : Type)] [CompactSpace (Y : Type)]
  (basis : Cohomology Y 1 ≃ₗ[ZMod 2] (Fin n → ZMod 2))

/-- The two-slice boundary inclusion `Σ ⊔ Σ → Σ × [0,1]`, `inl x ↦ (x,0)`, `inr x ↦ (x,1)`. -/
noncomputable def cylBdryIncl : C(↑Y ⊕ ↑Y, ↑Y × I) :=
  ⟨Sum.elim (fun x => (x, (0 : I))) (fun x => (x, (1 : I))), by fun_prop⟩

omit [T2Space (Y : Type)] [CompactSpace (Y : Type)] in
theorem cylBdryIncl_injective : Function.Injective (cylBdryIncl Y) := by
  rintro (a | a) (b | b) h <;>
    simp only [cylBdryIncl, ContinuousMap.coe_mk, Sum.elim_inl, Sum.elim_inr, Prod.mk.injEq] at h
  · rw [h.1]
  · exact absurd (congrArg Subtype.val h.2) (by norm_num)
  · exact absurd (congrArg Subtype.val h.2) (by norm_num)
  · rw [h.1]

/-- **THE HONEST CYLINDER REALIZATION** — the reflexive cylinder `Q = Σ × [0,1]` as a genuine
`GeoRealizationTied` for the end pair `(Σ, Σ)` with the carried enhancement `basis`. Non-vacuity of
the derived-basis realization structure: every field is real compact-T2 topology, the boundary bases
are DERIVED from `basis` (not free), the interior basis is the contractible-collapse image of
`basis`. -/
noncomputable def cylRealizationTied : GeoRealizationTied Y Y basis basis where
  bdry := TopCat.of (↑Y ⊕ ↑Y)
  Q := ProdSp Y (TopCat.of unitInterval)
  U := Set.range (Sum.inl : ↑Y → ↑Y ⊕ ↑Y)
  hU := ⟨isClosed_range_inl, isOpen_range_inl⟩
  bdryT2 := inferInstanceAs (T2Space (↑Y ⊕ ↑Y))
  bdryCompact := inferInstanceAs (CompactSpace (↑Y ⊕ ↑Y))
  QT2 := inferInstanceAs (T2Space (↑Y × I))
  QCompact := inferInstanceAs (CompactSpace (↑Y × I))
  ι := cylBdryIncl Y
  hιce := (cylBdryIncl Y).continuous.isClosedEmbedding (cylBdryIncl_injective Y)
  homσ := IsClosedEmbedding.inl.isEmbedding.toHomeomorph.symm
  homτ := (Homeomorph.setCongr Set.compl_range_inl).trans
    IsClosedEmbedding.inr.isEmbedding.toHomeomorph.symm
  mid := n
  eQ := (prodContractibleHomologyEquiv Y (TopCat.of unitInterval) ⊥ iccContraction
      slice_iccContraction_zero slice_iccContraction_one 0).trans
    (homologyBasisOfCohomologyBasis basis)

/-- The cylinder realization's derived σ-boundary basis is the UCT dual of the carried cohomology
basis, pulled back along the left-slice identification — the F2 pin, on a concrete inhabitant. -/
theorem cylRealizationTied_derivedEσ :
    (cylRealizationTied Y basis).derivedEσ
      = (homeoHomologyEquiv IsClosedEmbedding.inl.isEmbedding.toHomeomorph.symm 1).trans
          (homologyBasisOfCohomologyBasis basis) :=
  rfl

/-! ## §2. THE GEOMETRIC KERNEL IDENTITY — the transported boundary-inclusion is the fold `cylBd`,
so `L = cylLagrangian` (the anti-diagonal). This is what lets the honest cylinder realization feed the
tied op witnesses. -/

omit [T2Space (Y : Type)] [CompactSpace (Y : Type)] in
/-- **The contractible-factor collapse** `H₁(Σ × [0,1]) ≃ H₁(Σ)` — the forward map is `H₁(prodFst)`. -/
noncomputable def cylCollapse :
    Homology (ProdSp Y (TopCat.of unitInterval)) 1 ≃ₗ[ZMod 2] Homology Y 1 :=
  prodContractibleHomologyEquiv Y (TopCat.of unitInterval) ⊥ iccContraction
    slice_iccContraction_zero slice_iccContraction_one 0

omit [T2Space (Y : Type)] [CompactSpace (Y : Type)] in
/-- **Both slice inclusions collapse to the same iso.** For EITHER endpoint `c₀`, the slice inclusion
`Σ ↪ Σ×[0,1]` (`prodSect c₀`) induces the inverse of the contractible collapse — because
`prodFst ∘ prodSect c₀ = id` makes `H₁(prodSect c₀)` a right inverse of the bijection `H₁(prodFst)`.
This is the geometric core: the two ends of the cylinder are homologically identified. -/
theorem homology_map_prodSect_eq_cylCollapse_symm (c₀ : ↑(TopCat.of unitInterval)) :
    Homology.map (prodSect Y (TopCat.of unitInterval) c₀) 1 = (cylCollapse Y).symm.toLinearMap := by
  ext z
  rw [LinearEquiv.coe_toLinearMap]
  symm
  rw [LinearEquiv.symm_apply_eq]
  show z = (Homology.map (prodFst Y (TopCat.of unitInterval)) 1)
      (Homology.map (prodSect Y (TopCat.of unitInterval) c₀) 1 z)
  rw [← LinearMap.comp_apply, ← Homology.map_comp, prodFst_comp_prodSect, Homology.map_id,
    LinearMap.id_apply]

/-- The boundary inclusion restricted to the σ-end `Σ_σ = sub U` IS the bottom slice inclusion
`prodSect ⊥` read through the identification homeomorphism `homσ`. -/
theorem cylBdryIncl_comp_subInclCM_left :
    (cylRealizationTied Y basis).toData.ι.comp
        (subInclCM (cylRealizationTied Y basis).toData.U)
      = (prodSect Y (TopCat.of unitInterval) ⊥).comp
          ⟨IsClosedEmbedding.inl.isEmbedding.toHomeomorph.symm,
           (IsClosedEmbedding.inl (Y := ↑Y)).isEmbedding.toHomeomorph.symm.continuous⟩ := by
  apply ContinuousMap.ext; rintro ⟨p, y, rfl⟩
  show cylBdryIncl Y (Sum.inl y)
      = prodSect Y (TopCat.of unitInterval) ⊥
          (IsClosedEmbedding.inl.isEmbedding.toHomeomorph.symm ⟨Sum.inl y, y, rfl⟩)
  rw [IsEmbedding.toHomeomorph_symm_apply]
  rfl

/-- The boundary inclusion restricted to the τ-end `Σ_τ = sub Uᶜ` IS the top slice inclusion
`prodSect ⊤` read through the identification homeomorphism `homτ`. -/
theorem cylBdryIncl_comp_subInclCM_right :
    (cylRealizationTied Y basis).toData.ι.comp
        (subInclCM ((cylRealizationTied Y basis).toData.U)ᶜ)
      = (prodSect Y (TopCat.of unitInterval) ⊤).comp
          ⟨(Homeomorph.setCongr Set.compl_range_inl).trans
              IsClosedEmbedding.inr.isEmbedding.toHomeomorph.symm,
           ((Homeomorph.setCongr (Set.compl_range_inl (β := ↑Y))).trans
              (IsClosedEmbedding.inr (X := ↑Y)).isEmbedding.toHomeomorph.symm).continuous⟩ := by
  apply ContinuousMap.ext; rintro ⟨(a | y), hp⟩
  · exact absurd ⟨a, rfl⟩ hp
  · show cylBdryIncl Y (Sum.inr y)
        = prodSect Y (TopCat.of unitInterval) ⊤
            (((Homeomorph.setCongr Set.compl_range_inl).trans
              IsClosedEmbedding.inr.isEmbedding.toHomeomorph.symm) ⟨Sum.inr y, hp⟩)
    rw [Homeomorph.trans_apply,
      show (Homeomorph.setCongr (Set.compl_range_inl (β := ↑Y))) ⟨Sum.inr y, hp⟩
          = ⟨Sum.inr y, ⟨y, rfl⟩⟩ from rfl, IsEmbedding.toHomeomorph_symm_apply]
    rfl

/-- **THE GEOMETRIC KERNEL IDENTITY.** The transported boundary-inclusion of the honest cylinder
realization is EXACTLY the fold `cylBd n`, `x ↦ (i ↦ x(inl i) + x(inr i))`. Both slice inclusions
induce the same `H₁(Σ)` iso (`homology_map_prodSect_eq_cylCollapse_symm`), so on the coordinatized
boundary homology the inclusion-into-`Q` map adds the two ends. Hence the computed Taylor-leg submodule
is the geometric anti-diagonal, never a free field — the F1/F2 obligation discharged on the cylinder. -/
theorem cylRealizationTied_transportedBInc :
    transportedBInc (cylRealizationTied Y basis).toData = cylBd n := by
  have hσ : ∀ a : Homology (sub (cylRealizationTied Y basis).toData.U) 1,
      Homology.map (cylRealizationTied Y basis).toData.ι 1
          (homIncl (cylRealizationTied Y basis).toData.U 1 a)
        = (cylCollapse Y).symm
            (homeoHomologyEquiv IsClosedEmbedding.inl.isEmbedding.toHomeomorph.symm 1 a) := by
    intro a
    rw [homIncl_eq_map, ← LinearMap.comp_apply, ← Homology.map_comp,
      cylBdryIncl_comp_subInclCM_left]
    erw [Homology.map_comp, LinearMap.comp_apply, homology_map_prodSect_eq_cylCollapse_symm]
    rfl
  have hτ : ∀ b : Homology (sub ((cylRealizationTied Y basis).toData.U)ᶜ) 1,
      Homology.map (cylRealizationTied Y basis).toData.ι 1
          (homIncl ((cylRealizationTied Y basis).toData.U)ᶜ 1 b)
        = (cylCollapse Y).symm
            (homeoHomologyEquiv ((Homeomorph.setCongr Set.compl_range_inl).trans
              IsClosedEmbedding.inr.isEmbedding.toHomeomorph.symm) 1 b) := by
    intro b
    rw [homIncl_eq_map, ← LinearMap.comp_apply, ← Homology.map_comp,
      cylBdryIncl_comp_subInclCM_right]
    erw [Homology.map_comp, LinearMap.comp_apply, homology_map_prodSect_eq_cylCollapse_symm]
    rfl
  -- the three carried bases of the cylinder realization, unfolded to their derived/collapse forms
  have heσ : (cylRealizationTied Y basis).toData.eσ
      = (homeoHomologyEquiv IsClosedEmbedding.inl.isEmbedding.toHomeomorph.symm 1).trans
          (homologyBasisOfCohomologyBasis basis) := rfl
  have heτ : (cylRealizationTied Y basis).toData.eτ
      = (homeoHomologyEquiv ((Homeomorph.setCongr Set.compl_range_inl).trans
            IsClosedEmbedding.inr.isEmbedding.toHomeomorph.symm) 1).trans
          (homologyBasisOfCohomologyBasis basis) := rfl
  have heQ : (cylRealizationTied Y basis).toData.eQ
      = (cylCollapse Y).trans (homologyBasisOfCohomologyBasis basis) := rfl
  refine LinearMap.ext fun x => ?_
  show (cylRealizationTied Y basis).toData.eQ
      (Homology.map (cylRealizationTied Y basis).toData.ι 1
        ((srcEquiv (cylRealizationTied Y basis).toData).symm x)) = cylBd n x
  rw [srcEquiv_symm_apply, map_add, hσ, hτ, heQ, heσ, heτ]
  simp only [LinearEquiv.symm_trans_apply, LinearEquiv.apply_symm_apply]
  erw [LinearEquiv.trans_apply, LinearEquiv.map_add, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply, LinearEquiv.map_add, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]
  funext i
  rfl

/-- **The cylinder realization's membrane kernel is the honest anti-diagonal** `cylLagrangian n` —
the geometric `half-lives–half-dies` submodule the e₈ exploit omits. Discharges the F1 obligation
(`L` a genuine geometric fold-kernel) on the cylinder membrane. -/
theorem cylRealizationTied_toMembrane_L (q : Z4Quadratic (Fin n)) :
    ((cylRealizationTied Y basis).toMembrane q q).L = cylLagrangian n := by
  show LinearMap.ker (transportedBInc (cylRealizationTied Y basis).toData) = _
  rw [cylRealizationTied_transportedBInc]
  rfl

end SKEFTHawking.PinPlusCharPairCylRealization
