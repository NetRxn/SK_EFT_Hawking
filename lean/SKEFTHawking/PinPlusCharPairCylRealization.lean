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

**Named remaining route (Stage 2→4).** The geometric kernel identity — `toMembrane.L = cylLagrangian`,
i.e. that the two slice inclusions `Σ ↪ Σ×[0,1]` induce the SAME `H₁(Σ)` iso (both are sections of the
contractible collapse `prodFst`), so the transported boundary-inclusion is the fold with anti-diagonal
kernel — is the homological content needed to feed this realization into the tied op witnesses. It
reduces to `Homology.map (slice ⊥) 1 = Homology.map (slice ⊤) 1 = (prodContractibleHomologyEquiv …).symm`
via `prodFst ∘ slice = id`, `Homology.map_comp`/`map_id`, and `splitHnEquiv` — mirroring the
`ptPieceToM`/`prodFst_homology_bijective` pattern of the (5-manifold) cylinder numerics, transported to
the abstract surface product.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusCharPairRealizationTied
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderNumerics

open Topology unitInterval
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularKroneckerBasisBridge
open SKEFTHawking.SingularProdContractibleInt
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderNumerics
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

end SKEFTHawking.PinPlusCharPairCylRealization
