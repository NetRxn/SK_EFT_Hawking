/-
# Phase 5q.H (W-A arm 4) — STAGE 3c COMPLETION: THE DISJOINT-UNION REALIZATION (`addBor`).

`PinPlusCharPairBorRealizedOps` realized seven of the eight tied ops (unit/comm/assoc via the twisted
cylinder; cyl/rev/neg/symm in `PinPlusCharPairBorRealized`). This module realizes the EIGHTH and final
op — `addBor`, the genuine `⊔` of two membrane realizations — the realized geometric witness for
`charPairAddBorTied`'s `(σ₁ ⊔ σ₂) → (τ₁ ⊔ τ₂)` disjoint-union law.

Unlike the twisted cylinders, this is NOT a `mapCylinder`; it is the honest disjoint union of the two
input realizations `Q₁ ⊔ Q₂`, with boundary `∂Q₁ ⊔ ∂Q₂` (`ι = ι₁ ⊔ ι₂`) clopen-split so the σ-end is
`Σσ₁ ⊔ Σσ₂` and the τ-end is `Στ₁ ⊔ Στ₂` (the block clopen split `Sum.inl '' U₁ ∪ Sum.inr '' U₂`). The
one genuinely new topological ingredient is the **block-sub homeomorphism** `blockSubHomeo`: the σ-part
`sub (inl '' U₁ ∪ inr '' U₂)` of the disjoint-union boundary IS the disjoint union `sub U₁ ⊔ sub U₂` of
the two components' σ-parts, realized as the range of the closed embedding `Sum.map val val`. The
per-object T2/Compact/closed-embedding certificates are all COMPONENTWISE (⊔ of T2 is T2, ⊔ of compact
is compact), never inherited from an ambient space (the membrane-level non-Hausdorff no-go).

Its transported boundary-inclusion is the block map of the two components' `transportedBInc`s, regrouped
(`sumSumSumComm`) and de-reindexed (`sumCongr finSumFinEquiv`) — landing the computed kernel EXACTLY on
`charPairAddBorTied`'s `hmeta` submodule (`IsMetabolic.orthSum` on the block Lagrangian). So the sum
membrane's Taylor-leg submodule is a REALIZED block fold-kernel, never a free/synthetic `bInc`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusCharPairBorRealizedOps

open scoped Manifold
open Topology
open SKEFTHawking.BordismTheory
open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularCohomologyFunctoriality
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularPairLES
open SKEFTHawking.SingularCohomologyPairRestrict
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspension
open SKEFTHawking.SingularDisjointUnion SKEFTHawking.SingularDisjointUnionHn
open SKEFTHawking.SingularCohomologyDisjointSum
open SKEFTHawking.SingularKroneckerBasisBridge
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCharPairSurfaceTie
open SKEFTHawking.PinPlusCharPairMembraneGeoRealization
open SKEFTHawking.PinPlusCharPairRealizationTied
open SKEFTHawking.PinPlusCharPairNegRealization
open SKEFTHawking.PinPlusCharPairMapCylRealization
open SKEFTHawking.PinPlusWAdmPinned
open SKEFTHawking.PinPlusCharPairBorRealized

namespace SKEFTHawking.PinPlusCharPairAddRealization

/-- Applied form of `Homology.map_comp` — collapses `map ψ (map φ x)` to `map (ψ ∘ φ) x` in one step. -/
theorem Homology_map_comp_apply {X Y Z : TopCat} (ψ : C(↑Y, ↑Z)) (φ : C(↑X, ↑Y)) (n : ℕ)
    (x : Homology X n) :
    Homology.map (ψ.comp φ) n x = Homology.map ψ n (Homology.map φ n x) := by
  rw [Homology.map_comp, LinearMap.comp_apply]

/-! ## §1. The block-sub homeomorphism — the one genuinely new topological ingredient. -/

section BlockSub
variable {A B : Type} [TopologicalSpace A] [TopologicalSpace B]

/-- The disjoint-union sub-inclusion `↥U₁ ⊔ ↥U₂ → A ⊔ B` (`Sum.map val val`) — its range is the block
clopen set `inl '' U₁ ∪ inr '' U₂`. -/
def blockSubIncl (U₁ : Set A) (U₂ : Set B) : (↥U₁ ⊕ ↥U₂) → A ⊕ B :=
  Sum.map Subtype.val Subtype.val

omit [TopologicalSpace A] [TopologicalSpace B] in
theorem range_blockSubIncl (U₁ : Set A) (U₂ : Set B) :
    Set.range (blockSubIncl U₁ U₂) = Sum.inl '' U₁ ∪ Sum.inr '' U₂ := by
  ext x
  cases x with
  | inl a => simp [blockSubIncl, Sum.map]
  | inr b => simp [blockSubIncl, Sum.map]

theorem blockSubIncl_continuous (U₁ : Set A) (U₂ : Set B) :
    Continuous (blockSubIncl U₁ U₂) :=
  continuous_subtype_val.sumMap continuous_subtype_val

omit [TopologicalSpace A] [TopologicalSpace B] in
theorem blockSubIncl_injective (U₁ : Set A) (U₂ : Set B) :
    Function.Injective (blockSubIncl U₁ U₂) :=
  Function.Injective.sumMap Subtype.val_injective Subtype.val_injective

/-- **THE BLOCK-SUB HOMEOMORPHISM** — `↥U₁ ⊔ ↥U₂ ≃ₜ ↥(inl '' U₁ ∪ inr '' U₂)`: the σ-part of the
disjoint-union boundary IS the disjoint union of the two components' σ-parts. Built as the range
homeomorphism of the closed embedding `Sum.map val val` (a continuous injection from a compact source to
a Hausdorff target), then `setCongr` to the block clopen set. -/
noncomputable def blockSubHomeo [CompactSpace A] [CompactSpace B] [T2Space A] [T2Space B]
    (U₁ : Set A) (U₂ : Set B) (hU₁ : IsClosed U₁) (hU₂ : IsClosed U₂) :
    (↥U₁ ⊕ ↥U₂) ≃ₜ ↥(Sum.inl '' U₁ ∪ Sum.inr '' U₂) :=
  haveI : CompactSpace ↥U₁ := isCompact_iff_compactSpace.mp hU₁.isCompact
  haveI : CompactSpace ↥U₂ := isCompact_iff_compactSpace.mp hU₂.isCompact
  (IsEmbedding.toHomeomorph
      ((blockSubIncl_continuous U₁ U₂).isClosedEmbedding
        (blockSubIncl_injective U₁ U₂)).isEmbedding).trans
    (Homeomorph.setCongr (range_blockSubIncl U₁ U₂))

/-- `blockSubHomeo` sends `inl a` to `⟨inl a.1, _⟩` — the σ₁-component of the block boundary includes
as the `inl` summand. -/
theorem blockSubHomeo_inl [CompactSpace A] [CompactSpace B] [T2Space A] [T2Space B]
    (U₁ : Set A) (U₂ : Set B) (hU₁ : IsClosed U₁) (hU₂ : IsClosed U₂) (a : ↥U₁) :
    (blockSubHomeo U₁ U₂ hU₁ hU₂ (Sum.inl a) : A ⊕ B) = Sum.inl a.1 := rfl

theorem blockSubHomeo_inr [CompactSpace A] [CompactSpace B] [T2Space A] [T2Space B]
    (U₁ : Set A) (U₂ : Set B) (hU₁ : IsClosed U₁) (hU₂ : IsClosed U₂) (b : ↥U₂) :
    (blockSubHomeo U₁ U₂ hU₁ hU₂ (Sum.inr b) : A ⊕ B) = Sum.inr b.1 := rfl

/-- The block clopen set of a disjoint union is clopen (`inl`/`inr` are clopen embeddings). -/
theorem isClopen_block {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    {U₁ : Set A} {U₂ : Set B} (h₁ : IsClopen U₁) (h₂ : IsClopen U₂) :
    IsClopen (Sum.inl '' U₁ ∪ Sum.inr '' U₂) := by
  refine IsClopen.union ⟨?_, ?_⟩ ⟨?_, ?_⟩
  · exact IsClosedEmbedding.inl.isClosedMap _ h₁.1
  · exact IsOpenEmbedding.inl.isOpenMap _ h₁.2
  · exact IsClosedEmbedding.inr.isClosedMap _ h₂.1
  · exact IsOpenEmbedding.inr.isOpenMap _ h₂.2

/-- The complement of a block clopen set is the block clopen set of the complements. -/
theorem compl_block {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (U₁ : Set A) (U₂ : Set B) :
    (Sum.inl '' U₁ ∪ Sum.inr '' U₂)ᶜ = Sum.inl '' U₁ᶜ ∪ Sum.inr '' U₂ᶜ := by
  ext x
  cases x with
  | inl a => simp
  | inr b => simp

end BlockSub

/-! ## §1b. The disjoint-union `H₁`-additivity `H₁(Q₁ ⊔ Q₂) ≅ H₁(Q₁) × H₁(Q₂)`, expressed through the
`inlMap`/`inrMap` summand inclusions (the interior basis `eQ` rides this). -/

section DisjointSumHn
variable {Q₁ Q₂ : TopCat}

/-- The `range inl` clopen split of the disjoint union `Q₁ ⊔ Q₂`. -/
def rangeInlSet (Q₁ Q₂ : TopCat) : Set ↑(sumSpace Q₁ Q₂) :=
  Set.range (Sum.inl : ↑Q₁ → ↑Q₁ ⊕ ↑Q₂)

/-- `sub (range inl) ≃ₜ Q₁` in the disjoint union `Q₁ ⊔ Q₂`. -/
noncomputable def qInlHomeo :
    (↑(sub (rangeInlSet Q₁ Q₂)) : Type) ≃ₜ (↑Q₁ : Type) :=
  IsClosedEmbedding.inl.isEmbedding.toHomeomorph.symm

/-- `sub (range inl)ᶜ ≃ₜ Q₂` in the disjoint union `Q₁ ⊔ Q₂`. -/
noncomputable def qInrHomeo :
    (↑(sub (rangeInlSet Q₁ Q₂)ᶜ) : Type) ≃ₜ (↑Q₂ : Type) :=
  (Homeomorph.setCongr Set.compl_range_inl).trans
    IsClosedEmbedding.inr.isEmbedding.toHomeomorph.symm

/-- **The disjoint-union `H₁`-additivity** `H₁(Q₁) × H₁(Q₂) ≃ₗ H₁(Q₁ ⊔ Q₂)` — the `range inl` clopen
split (`splitHnEquiv`) with each factor identified with its summand through `qInlHomeo`/`qInrHomeo`. -/
noncomputable def disjointSumHnEquiv :
    (Homology Q₁ 1 × Homology Q₂ 1) ≃ₗ[ZMod 2] Homology (sumSpace Q₁ Q₂) 1 :=
  (LinearEquiv.prodCongr (homeoHomologyEquiv qInlHomeo 1) (homeoHomologyEquiv qInrHomeo 1)).symm.trans
    (splitHnEquiv (X := sumSpace Q₁ Q₂) (U := rangeInlSet Q₁ Q₂)
      ⟨isClosed_range_inl, isOpen_range_inl⟩ 1)

/-- **The additivity in coordinates**: the forward map sends `(w₁, w₂)` to `inl₊ w₁ + inr₊ w₂`, the
pushforwards of the two summand classes through the summand inclusions. -/
theorem disjointSumHnEquiv_apply (w₁ : Homology Q₁ 1) (w₂ : Homology Q₂ 1) :
    disjointSumHnEquiv (w₁, w₂)
      = Homology.map (inlMap Q₁ Q₂) 1 w₁ + Homology.map (inrMap Q₁ Q₂) 1 w₂ := by
  show splitHnEquiv (X := sumSpace Q₁ Q₂) (U := rangeInlSet Q₁ Q₂)
      ⟨isClosed_range_inl, isOpen_range_inl⟩ 1
      ((homeoHomologyEquiv qInlHomeo 1).symm w₁, (homeoHomologyEquiv qInrHomeo 1).symm w₂) = _
  rw [splitHnEquiv_apply]
  show homIncl (rangeInlSet Q₁ Q₂) 1 ((homeoHomologyEquiv qInlHomeo 1).symm w₁)
      + homIncl (rangeInlSet Q₁ Q₂)ᶜ 1 ((homeoHomologyEquiv qInrHomeo 1).symm w₂) = _
  congr 1
  · rw [homIncl_eq_map, homeoHomologyEquiv_symm_apply, ← LinearMap.comp_apply, ← Homology.map_comp]
    rfl
  · rw [homIncl_eq_map, homeoHomologyEquiv_symm_apply, ← LinearMap.comp_apply, ← Homology.map_comp]
    rfl

end DisjointSumHn

/-! ## §1c. The UCT-dual of a sum-cohomology basis splits through the summand inclusions (homology
side) — the mirror of the neg module's source-coordinate identity, isolated and generalized. -/

/-- **The homology-side sum-basis splitting**: the UCT-dual of `sumBasis bσ bτ`, applied to a vector,
is the sum of the two summands' UCT-duals pushed forward through `inlMap`/`inrMap` (reindexed by
`finSumFinEquiv`). -/
theorem hbob_sumBasis_symm {A B : TopCat} {nσ nτ : ℕ}
    (bσ : Cohomology A 1 ≃ₗ[ZMod 2] (Fin nσ → ZMod 2))
    (bτ : Cohomology B 1 ≃ₗ[ZMod 2] (Fin nτ → ZMod 2)) (v : Fin (nσ + nτ) → ZMod 2) :
    (homologyBasisOfCohomologyBasis (sumBasis bσ bτ)).symm v
      = Homology.map (inlMap A B) 1
          ((homologyBasisOfCohomologyBasis bσ).symm (fun i => v (finSumFinEquiv (Sum.inl i))))
        + Homology.map (inrMap A B) 1
          ((homologyBasisOfCohomologyBasis bτ).symm (fun i => v (finSumFinEquiv (Sum.inr i)))) := by
  have hcoordsσ : homologyCoords bσ
      ((homologyBasisOfCohomologyBasis bσ).symm (fun i => v (finSumFinEquiv (Sum.inl i))))
      = fun i => v (finSumFinEquiv (Sum.inl i)) := by
    rw [← homologyBasisOfCohomologyBasis_apply]
    exact (homologyBasisOfCohomologyBasis bσ).apply_symm_apply _
  have hcoordsτ : homologyCoords bτ
      ((homologyBasisOfCohomologyBasis bτ).symm (fun i => v (finSumFinEquiv (Sum.inr i))))
      = fun i => v (finSumFinEquiv (Sum.inr i)) := by
    rw [← homologyBasisOfCohomologyBasis_apply]
    exact (homologyBasisOfCohomologyBasis bτ).apply_symm_apply _
  refine (homologyBasisOfCohomologyBasis (sumBasis bσ bτ)).injective ?_
  rw [LinearEquiv.apply_symm_apply, map_add]
  funext j
  rw [Pi.add_apply, homologyBasisOfCohomologyBasis_apply, homologyBasisOfCohomologyBasis_apply,
    homologyCoords_sumBasis_map_inlMap, homologyCoords_sumBasis_map_inrMap, hcoordsσ, hcoordsτ]
  have hsum : ∀ (F : Fin (nσ + nτ) → ZMod 2),
      (∑ i, F (finSumFinEquiv (Sum.inl i))) + (∑ i, F (finSumFinEquiv (Sum.inr i))) = ∑ m, F m := by
    intro F
    rw [← Equiv.sum_comp finSumFinEquiv F, Fintype.sum_sum_type]
  have hdelta : (∑ m, (Pi.single j (1 : ZMod 2) : Fin (nσ + nτ) → ZMod 2) m * v m) = v j := by
    simp [Pi.single_apply]
  show v j
    = (∑ i, (fun m => (Pi.single j (1 : ZMod 2) : Fin (nσ + nτ) → ZMod 2) m * v m)
          (finSumFinEquiv (Sum.inl i)))
      + ∑ i, (fun m => (Pi.single j (1 : ZMod 2) : Fin (nσ + nτ) → ZMod 2) m * v m)
          (finSumFinEquiv (Sum.inr i))
  rw [hsum (fun m => (Pi.single j (1 : ZMod 2) : Fin (nσ + nτ) → ZMod 2) m * v m)]
  exact hdelta.symm

/-! ## §2. The disjoint-union realization datum `GeoRealizationTied.sum`. -/

section Sum
variable {nσ₁ nτ₁ nσ₂ nτ₂ : ℕ}
variable {Sσ₁ Sτ₁ Sσ₂ Sτ₂ : TopCat}
variable {bσ₁ : Cohomology Sσ₁ 1 ≃ₗ[ZMod 2] (Fin nσ₁ → ZMod 2)}
variable {bτ₁ : Cohomology Sτ₁ 1 ≃ₗ[ZMod 2] (Fin nτ₁ → ZMod 2)}
variable {bσ₂ : Cohomology Sσ₂ 1 ≃ₗ[ZMod 2] (Fin nσ₂ → ZMod 2)}
variable {bτ₂ : Cohomology Sτ₂ 1 ≃ₗ[ZMod 2] (Fin nτ₂ → ZMod 2)}

/-- **THE DISJOINT-UNION REALIZATION** — the genuine `⊔` of two derived-basis realizations `d₁`, `d₂`.
`∂Q = ∂Q₁ ⊔ ∂Q₂`, `Q = Q₁ ⊔ Q₂`, `ι = ι₁ ⊔ ι₂`; the clopen split groups the two σ-parts
(`Sum.inl '' U₁ ∪ Sum.inr '' U₂`), so `Σσ = Σσ₁ ⊔ Σσ₂` (the `blockSubHomeo`) and `Στ = Στ₁ ⊔ Στ₂`.
Per-object T2/Compact/closed-embedding certs are all COMPONENTWISE. The carried σ/τ bases are the
`sumBasis`s of the components' bases. -/
noncomputable def GeoRealizationTied.sum
    (d₁ : GeoRealizationTied Sσ₁ Sτ₁ bσ₁ bτ₁) (d₂ : GeoRealizationTied Sσ₂ Sτ₂ bσ₂ bτ₂) :
    GeoRealizationTied (sumSpace Sσ₁ Sσ₂) (sumSpace Sτ₁ Sτ₂)
      (sumBasis bσ₁ bσ₂) (sumBasis bτ₁ bτ₂) where
  bdry := sumSpace d₁.bdry d₂.bdry
  Q := sumSpace d₁.Q d₂.Q
  U := Sum.inl '' d₁.U ∪ Sum.inr '' d₂.U
  hU := isClopen_block d₁.hU d₂.hU
  bdryT2 := by
    haveI := d₁.bdryT2; haveI := d₂.bdryT2
    exact inferInstanceAs (T2Space (↑d₁.bdry ⊕ ↑d₂.bdry))
  bdryCompact := by
    haveI := d₁.bdryCompact; haveI := d₂.bdryCompact
    exact inferInstanceAs (CompactSpace (↑d₁.bdry ⊕ ↑d₂.bdry))
  QT2 := by
    haveI := d₁.QT2; haveI := d₂.QT2
    exact inferInstanceAs (T2Space (↑d₁.Q ⊕ ↑d₂.Q))
  QCompact := by
    haveI := d₁.QCompact; haveI := d₂.QCompact
    exact inferInstanceAs (CompactSpace (↑d₁.Q ⊕ ↑d₂.Q))
  ι := ⟨Sum.map d₁.ι d₂.ι, d₁.ι.continuous.sumMap d₂.ι.continuous⟩
  hιce := by
    haveI := d₁.bdryCompact; haveI := d₂.bdryCompact
    haveI := d₁.QT2; haveI := d₂.QT2
    haveI : CompactSpace (↑d₁.bdry ⊕ ↑d₂.bdry) := inferInstance
    haveI : T2Space (↑d₁.Q ⊕ ↑d₂.Q) := inferInstance
    exact (d₁.ι.continuous.sumMap d₂.ι.continuous).isClosedEmbedding
      (Function.Injective.sumMap d₁.hιce.injective d₂.hιce.injective)
  homσ := by
    haveI := d₁.bdryCompact; haveI := d₂.bdryCompact
    haveI := d₁.bdryT2; haveI := d₂.bdryT2
    exact (blockSubHomeo d₁.U d₂.U d₁.hU.1 d₂.hU.1).symm.trans (d₁.homσ.sumCongr d₂.homσ)
  homτ := by
    haveI := d₁.bdryCompact; haveI := d₂.bdryCompact
    haveI := d₁.bdryT2; haveI := d₂.bdryT2
    exact (Homeomorph.setCongr (compl_block d₁.U d₂.U)).trans
      ((blockSubHomeo d₁.Uᶜ d₂.Uᶜ d₁.hU.compl.1 d₂.hU.compl.1).symm.trans
        (d₁.homτ.sumCongr d₂.homτ))
  mid := d₁.mid + d₂.mid
  eQ := disjointSumHnEquiv.symm.trans
    ((d₁.eQ.prodCongr d₂.eQ).trans
      ((LinearEquiv.sumArrowLequivProdArrow (Fin d₁.mid) (Fin d₂.mid) (ZMod 2) (ZMod 2)).symm.trans
        (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) finSumFinEquiv.symm)))

/-! ## §3. The interior-basis block injections — `eQ` sends an `inl`/`inr` pushforward into the
corresponding `mid`-block, coordinatized by the component's own `eQ`. -/

/-- `eQ ∘ inl₊ = <inl-block of finSumFinEquiv-de-reindexed component eQ>`. -/
theorem sum_eQ_inlMap (d₁ : GeoRealizationTied Sσ₁ Sτ₁ bσ₁ bτ₁)
    (d₂ : GeoRealizationTied Sσ₂ Sτ₂ bσ₂ bτ₂) (w : Homology d₁.Q 1) :
    (GeoRealizationTied.sum d₁ d₂).toData.eQ (Homology.map (inlMap d₁.Q d₂.Q) 1 w)
      = LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) finSumFinEquiv.symm
          (Sum.elim (d₁.eQ w) 0) := by
  have hkey : (disjointSumHnEquiv (Q₁ := d₁.Q) (Q₂ := d₂.Q)).symm
      (Homology.map (inlMap d₁.Q d₂.Q) 1 w) = (w, 0) := by
    rw [LinearEquiv.symm_apply_eq, disjointSumHnEquiv_apply, map_zero, add_zero]
  show LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) finSumFinEquiv.symm
      ((LinearEquiv.sumArrowLequivProdArrow (Fin d₁.mid) (Fin d₂.mid) (ZMod 2) (ZMod 2)).symm
        ((d₁.eQ.prodCongr d₂.eQ) ((disjointSumHnEquiv (Q₁ := d₁.Q) (Q₂ := d₂.Q)).symm
          (Homology.map (inlMap d₁.Q d₂.Q) 1 w)))) = _
  rw [hkey, LinearEquiv.prodCongr_apply, map_zero]
  rfl

/-- `eQ ∘ inr₊ = <inr-block of finSumFinEquiv-de-reindexed component eQ>`. -/
theorem sum_eQ_inrMap (d₁ : GeoRealizationTied Sσ₁ Sτ₁ bσ₁ bτ₁)
    (d₂ : GeoRealizationTied Sσ₂ Sτ₂ bσ₂ bτ₂) (w : Homology d₂.Q 1) :
    (GeoRealizationTied.sum d₁ d₂).toData.eQ (Homology.map (inrMap d₁.Q d₂.Q) 1 w)
      = LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) finSumFinEquiv.symm
          (Sum.elim 0 (d₂.eQ w)) := by
  have hkey : (disjointSumHnEquiv (Q₁ := d₁.Q) (Q₂ := d₂.Q)).symm
      (Homology.map (inrMap d₁.Q d₂.Q) 1 w) = (0, w) := by
    rw [LinearEquiv.symm_apply_eq, disjointSumHnEquiv_apply, map_zero, zero_add]
  show LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) finSumFinEquiv.symm
      ((LinearEquiv.sumArrowLequivProdArrow (Fin d₁.mid) (Fin d₂.mid) (ZMod 2) (ZMod 2)).symm
        ((d₁.eQ.prodCongr d₂.eQ) ((disjointSumHnEquiv (Q₁ := d₁.Q) (Q₂ := d₂.Q)).symm
          (Homology.map (inrMap d₁.Q d₂.Q) 1 w)))) = _
  rw [hkey, LinearEquiv.prodCongr_apply, map_zero]
  rfl

/-! ## §4. The source-coordinate identity — how `srcEquiv (sum).symm` splits through the summand
boundary inclusions (the block-homeo naturality). -/

/-- σ-side block-homeo naturality: including a `Sσ₁`-summand class through `sum.homσ` and the sum
boundary inclusion IS pushing it forward through `inlMap∂` after including through `d₁.homσ` and the
`d₁` boundary inclusion. -/
theorem sum_homσ_inl (d₁ : GeoRealizationTied Sσ₁ Sτ₁ bσ₁ bτ₁)
    (d₂ : GeoRealizationTied Sσ₂ Sτ₂ bσ₂ bτ₂) (w : Homology Sσ₁ 1) :
    homIncl (GeoRealizationTied.sum d₁ d₂).U 1
        ((homeoHomologyEquiv (GeoRealizationTied.sum d₁ d₂).homσ 1).symm
          (Homology.map (inlMap Sσ₁ Sσ₂) 1 w))
      = Homology.map (inlMap d₁.bdry d₂.bdry) 1
          (homIncl d₁.U 1 ((homeoHomologyEquiv d₁.homσ 1).symm w)) := by
  rw [homIncl_eq_map, homIncl_eq_map, homeoHomologyEquiv_symm_apply, homeoHomologyEquiv_symm_apply,
    ← Homology_map_comp_apply, ← Homology_map_comp_apply, ← Homology_map_comp_apply,
    ← Homology_map_comp_apply]
  exact congrArg (fun f => Homology.map f 1 w) (ContinuousMap.ext fun _ => rfl)

/-- σ-side block-homeo naturality, `inr` summand. -/
theorem sum_homσ_inr (d₁ : GeoRealizationTied Sσ₁ Sτ₁ bσ₁ bτ₁)
    (d₂ : GeoRealizationTied Sσ₂ Sτ₂ bσ₂ bτ₂) (w : Homology Sσ₂ 1) :
    homIncl (GeoRealizationTied.sum d₁ d₂).U 1
        ((homeoHomologyEquiv (GeoRealizationTied.sum d₁ d₂).homσ 1).symm
          (Homology.map (inrMap Sσ₁ Sσ₂) 1 w))
      = Homology.map (inrMap d₁.bdry d₂.bdry) 1
          (homIncl d₂.U 1 ((homeoHomologyEquiv d₂.homσ 1).symm w)) := by
  rw [homIncl_eq_map, homIncl_eq_map, homeoHomologyEquiv_symm_apply, homeoHomologyEquiv_symm_apply,
    ← Homology_map_comp_apply, ← Homology_map_comp_apply, ← Homology_map_comp_apply,
    ← Homology_map_comp_apply]
  exact congrArg (fun f => Homology.map f 1 w) (ContinuousMap.ext fun _ => rfl)

/-- τ-side block-homeo naturality, `inl` summand (the complement clopen split). -/
theorem sum_homτ_inl (d₁ : GeoRealizationTied Sσ₁ Sτ₁ bσ₁ bτ₁)
    (d₂ : GeoRealizationTied Sσ₂ Sτ₂ bσ₂ bτ₂) (w : Homology Sτ₁ 1) :
    homIncl (GeoRealizationTied.sum d₁ d₂).Uᶜ 1
        ((homeoHomologyEquiv (GeoRealizationTied.sum d₁ d₂).homτ 1).symm
          (Homology.map (inlMap Sτ₁ Sτ₂) 1 w))
      = Homology.map (inlMap d₁.bdry d₂.bdry) 1
          (homIncl d₁.Uᶜ 1 ((homeoHomologyEquiv d₁.homτ 1).symm w)) := by
  rw [homIncl_eq_map, homIncl_eq_map, homeoHomologyEquiv_symm_apply, homeoHomologyEquiv_symm_apply,
    ← Homology_map_comp_apply, ← Homology_map_comp_apply, ← Homology_map_comp_apply,
    ← Homology_map_comp_apply]
  exact congrArg (fun f => Homology.map f 1 w) (ContinuousMap.ext fun _ => rfl)

/-- τ-side block-homeo naturality, `inr` summand. -/
theorem sum_homτ_inr (d₁ : GeoRealizationTied Sσ₁ Sτ₁ bσ₁ bτ₁)
    (d₂ : GeoRealizationTied Sσ₂ Sτ₂ bσ₂ bτ₂) (w : Homology Sτ₂ 1) :
    homIncl (GeoRealizationTied.sum d₁ d₂).Uᶜ 1
        ((homeoHomologyEquiv (GeoRealizationTied.sum d₁ d₂).homτ 1).symm
          (Homology.map (inrMap Sτ₁ Sτ₂) 1 w))
      = Homology.map (inrMap d₁.bdry d₂.bdry) 1
          (homIncl d₂.Uᶜ 1 ((homeoHomologyEquiv d₂.homτ 1).symm w)) := by
  rw [homIncl_eq_map, homIncl_eq_map, homeoHomologyEquiv_symm_apply, homeoHomologyEquiv_symm_apply,
    ← Homology_map_comp_apply, ← Homology_map_comp_apply, ← Homology_map_comp_apply,
    ← Homology_map_comp_apply]
  exact congrArg (fun f => Homology.map f 1 w) (ContinuousMap.ext fun _ => rfl)

/-- `toData.eσ.symm` expands as `homeoHomologyEquiv homσ⁻¹ ∘ (UCT-dual of bσ)⁻¹`. -/
theorem toData_eσ_symm {n₁ n₂ : ℕ} {S₁ S₂ : TopCat}
    {b₁ : Cohomology S₁ 1 ≃ₗ[ZMod 2] (Fin n₁ → ZMod 2)}
    {b₂ : Cohomology S₂ 1 ≃ₗ[ZMod 2] (Fin n₂ → ZMod 2)}
    (d : GeoRealizationTied S₁ S₂ b₁ b₂) (w : Fin n₁ → ZMod 2) :
    d.toData.eσ.symm w
      = (homeoHomologyEquiv d.homσ 1).symm ((homologyBasisOfCohomologyBasis b₁).symm w) := by
  rw [GeoRealizationTied.toData_eσ]
  rfl

/-- `toData.eτ.symm` expands as `homeoHomologyEquiv homτ⁻¹ ∘ (UCT-dual of bτ)⁻¹`. -/
theorem toData_eτ_symm {n₁ n₂ : ℕ} {S₁ S₂ : TopCat}
    {b₁ : Cohomology S₁ 1 ≃ₗ[ZMod 2] (Fin n₁ → ZMod 2)}
    {b₂ : Cohomology S₂ 1 ≃ₗ[ZMod 2] (Fin n₂ → ZMod 2)}
    (d : GeoRealizationTied S₁ S₂ b₁ b₂) (w : Fin n₂ → ZMod 2) :
    d.toData.eτ.symm w
      = (homeoHomologyEquiv d.homτ 1).symm ((homologyBasisOfCohomologyBasis b₂).symm w) := by
  rw [GeoRealizationTied.toData_eτ]
  rfl

/-- **σ-side source-coordinate identity** — the σ-boundary block of `srcEquiv (sum).symm` splits into
the two components' σ-blocks pushed through the summand boundary inclusions. -/
theorem sum_srcEquiv_σ (d₁ : GeoRealizationTied Sσ₁ Sτ₁ bσ₁ bτ₁)
    (d₂ : GeoRealizationTied Sσ₂ Sτ₂ bσ₂ bτ₂) (v : Fin (nσ₁ + nσ₂) → ZMod 2) :
    homIncl (GeoRealizationTied.sum d₁ d₂).U 1 ((GeoRealizationTied.sum d₁ d₂).toData.eσ.symm v)
      = Homology.map (inlMap d₁.bdry d₂.bdry) 1
          (homIncl d₁.U 1 (d₁.toData.eσ.symm (fun i => v (finSumFinEquiv (Sum.inl i)))))
        + Homology.map (inrMap d₁.bdry d₂.bdry) 1
          (homIncl d₂.U 1 (d₂.toData.eσ.symm (fun i => v (finSumFinEquiv (Sum.inr i))))) := by
  rw [toData_eσ_symm, hbob_sumBasis_symm, map_add, map_add, sum_homσ_inl, sum_homσ_inr,
    toData_eσ_symm, toData_eσ_symm]
  rfl

/-- **τ-side source-coordinate identity**. -/
theorem sum_srcEquiv_τ (d₁ : GeoRealizationTied Sσ₁ Sτ₁ bσ₁ bτ₁)
    (d₂ : GeoRealizationTied Sσ₂ Sτ₂ bσ₂ bτ₂) (v : Fin (nτ₁ + nτ₂) → ZMod 2) :
    homIncl (GeoRealizationTied.sum d₁ d₂).Uᶜ 1 ((GeoRealizationTied.sum d₁ d₂).toData.eτ.symm v)
      = Homology.map (inlMap d₁.bdry d₂.bdry) 1
          (homIncl d₁.Uᶜ 1 (d₁.toData.eτ.symm (fun i => v (finSumFinEquiv (Sum.inl i)))))
        + Homology.map (inrMap d₁.bdry d₂.bdry) 1
          (homIncl d₂.Uᶜ 1 (d₂.toData.eτ.symm (fun i => v (finSumFinEquiv (Sum.inr i))))) := by
  rw [toData_eτ_symm, hbob_sumBasis_symm, map_add, map_add, sum_homτ_inl, sum_homτ_inr,
    toData_eτ_symm, toData_eτ_symm]
  rfl

/-! ## §5. The `ι`-naturality — `ι = ι₁ ⊔ ι₂` commutes with the summand inclusions. -/

theorem sum_ι_inl (d₁ : GeoRealizationTied Sσ₁ Sτ₁ bσ₁ bτ₁)
    (d₂ : GeoRealizationTied Sσ₂ Sτ₂ bσ₂ bτ₂) (z : Homology d₁.bdry 1) :
    Homology.map (GeoRealizationTied.sum d₁ d₂).toData.ι 1
        (Homology.map (inlMap d₁.bdry d₂.bdry) 1 z)
      = Homology.map (inlMap d₁.Q d₂.Q) 1 (Homology.map d₁.toData.ι 1 z) := by
  have hCM : (GeoRealizationTied.sum d₁ d₂).toData.ι.comp (inlMap d₁.bdry d₂.bdry)
      = (inlMap d₁.Q d₂.Q).comp d₁.toData.ι := ContinuousMap.ext fun _ => rfl
  exact (Homology_map_comp_apply _ _ 1 z).symm.trans (by rw [hCM]; exact Homology_map_comp_apply _ _ 1 z)

theorem sum_ι_inr (d₁ : GeoRealizationTied Sσ₁ Sτ₁ bσ₁ bτ₁)
    (d₂ : GeoRealizationTied Sσ₂ Sτ₂ bσ₂ bτ₂) (z : Homology d₂.bdry 1) :
    Homology.map (GeoRealizationTied.sum d₁ d₂).toData.ι 1
        (Homology.map (inrMap d₁.bdry d₂.bdry) 1 z)
      = Homology.map (inrMap d₁.Q d₂.Q) 1 (Homology.map d₂.toData.ι 1 z) := by
  have hCM : (GeoRealizationTied.sum d₁ d₂).toData.ι.comp (inrMap d₁.bdry d₂.bdry)
      = (inrMap d₁.Q d₂.Q).comp d₂.toData.ι := ContinuousMap.ext fun _ => rfl
  exact (Homology_map_comp_apply _ _ 1 z).symm.trans (by rw [hCM]; exact Homology_map_comp_apply _ _ 1 z)

/-- **THE FULL SOURCE-COORDINATE IDENTITY** — `srcEquiv (sum).symm` splits as the two components'
boundary-class decompositions pushed through the summand boundary inclusions (σ- and τ-halves
assembled), in the direct `homIncl d.U`/`d.Uᶜ` form (each summand-block lands in `H₁(∂Q_i)`). -/
theorem sum_srcEquiv_symm (d₁ : GeoRealizationTied Sσ₁ Sτ₁ bσ₁ bτ₁)
    (d₂ : GeoRealizationTied Sσ₂ Sτ₂ bσ₂ bτ₂)
    (x : (Fin (nσ₁ + nσ₂) ⊕ Fin (nτ₁ + nτ₂)) → ZMod 2) :
    (srcEquiv (GeoRealizationTied.sum d₁ d₂).toData).symm x
      = Homology.map (inlMap d₁.bdry d₂.bdry) 1
          (homIncl d₁.U 1 (d₁.toData.eσ.symm (fun i => x (Sum.inl (finSumFinEquiv (Sum.inl i)))))
            + homIncl d₁.Uᶜ 1 (d₁.toData.eτ.symm (fun j => x (Sum.inr (finSumFinEquiv (Sum.inl j))))))
        + Homology.map (inrMap d₁.bdry d₂.bdry) 1
          (homIncl d₂.U 1 (d₂.toData.eσ.symm (fun i => x (Sum.inl (finSumFinEquiv (Sum.inr i)))))
            + homIncl d₂.Uᶜ 1 (d₂.toData.eτ.symm (fun j => x (Sum.inr (finSumFinEquiv (Sum.inr j)))))) := by
  rw [srcEquiv_symm_apply]
  show homIncl (GeoRealizationTied.sum d₁ d₂).U 1
        ((GeoRealizationTied.sum d₁ d₂).toData.eσ.symm (fun i => x (Sum.inl i)))
      + homIncl (GeoRealizationTied.sum d₁ d₂).Uᶜ 1
        ((GeoRealizationTied.sum d₁ d₂).toData.eτ.symm (fun i => x (Sum.inr i))) = _
  rw [sum_srcEquiv_σ, sum_srcEquiv_τ, map_add, map_add]
  abel

/-! ## §6. THE TRANSPORTED-BOUNDARY-INCLUSION IDENTITY — `transportedBInc (sum)` is the block map of
the two components' `transportedBInc`s, regrouped and de-reindexed (the exact shape of the tied
`charPairAddBorTied`'s `bInc`). -/

theorem sum_transportedBInc (d₁ : GeoRealizationTied Sσ₁ Sτ₁ bσ₁ bτ₁)
    (d₂ : GeoRealizationTied Sσ₂ Sτ₂ bσ₂ bτ₂) :
    transportedBInc (GeoRealizationTied.sum d₁ d₂).toData
      = (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2)
            (finSumFinEquiv (m := d₁.mid) (n := d₂.mid)).symm).toLinearMap ∘ₗ
        (blockMap (transportedBInc d₁.toData) (transportedBInc d₂.toData) ∘ₗ
          (LinearMap.funLeft (ZMod 2) (ZMod 2)
              (Equiv.sumSumSumComm (Fin nσ₁) (Fin nτ₁) (Fin nσ₂) (Fin nτ₂)) ∘ₗ
            LinearMap.funLeft (ZMod 2) (ZMod 2) (Equiv.sumCongr finSumFinEquiv finSumFinEquiv))) := by
  refine LinearMap.ext fun x => ?_
  show (GeoRealizationTied.sum d₁ d₂).toData.eQ
      (Homology.map (GeoRealizationTied.sum d₁ d₂).toData.ι 1
        ((srcEquiv (GeoRealizationTied.sum d₁ d₂).toData).symm x)) = _
  rw [sum_srcEquiv_symm]
  erw [map_add (Homology.map (GeoRealizationTied.sum d₁ d₂).toData.ι 1)]
  rw [sum_ι_inl, sum_ι_inr]
  erw [map_add (GeoRealizationTied.sum d₁ d₂).toData.eQ]
  rw [sum_eQ_inlMap, sum_eQ_inrMap]
  -- fold each `d_i.eQ (H₁(ι_i) (srcEquiv-decomposition))` back into `transportedBInc d_i.toData x_i`
  have hfold₁ : d₁.eQ ((Homology.map d₁.toData.ι 1)
        (homIncl d₁.U 1 (d₁.toData.eσ.symm fun i => x (Sum.inl (finSumFinEquiv (Sum.inl i))))
          + homIncl d₁.Uᶜ 1 (d₁.toData.eτ.symm fun j => x (Sum.inr (finSumFinEquiv (Sum.inl j))))))
      = transportedBInc d₁.toData
          (Sum.elim (fun i => x (Sum.inl (finSumFinEquiv (Sum.inl i))))
                    (fun j => x (Sum.inr (finSumFinEquiv (Sum.inl j))))) := by
    rw [transportedBInc, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.coe_coe, srcEquiv_symm_apply]
    rfl
  have hfold₂ : d₂.eQ ((Homology.map d₂.toData.ι 1)
        (homIncl d₂.U 1 (d₂.toData.eσ.symm fun i => x (Sum.inl (finSumFinEquiv (Sum.inr i))))
          + homIncl d₂.Uᶜ 1 (d₂.toData.eτ.symm fun j => x (Sum.inr (finSumFinEquiv (Sum.inr j))))))
      = transportedBInc d₂.toData
          (Sum.elim (fun i => x (Sum.inl (finSumFinEquiv (Sum.inr i))))
                    (fun j => x (Sum.inr (finSumFinEquiv (Sum.inr j))))) := by
    rw [transportedBInc, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.coe_coe, srcEquiv_symm_apply]
    rfl
  rw [hfold₁, hfold₂]
  funext m
  show (Sum.elim (transportedBInc d₁.toData _) (0 : Fin d₂.mid → ZMod 2)) (finSumFinEquiv.symm m)
      + (Sum.elim (0 : Fin d₁.mid → ZMod 2) (transportedBInc d₂.toData _)) (finSumFinEquiv.symm m)
    = blockMap (transportedBInc d₁.toData) (transportedBInc d₂.toData)
        (LinearMap.funLeft (ZMod 2) (ZMod 2)
            (Equiv.sumSumSumComm (Fin nσ₁) (Fin nτ₁) (Fin nσ₂) (Fin nτ₂))
          (LinearMap.funLeft (ZMod 2) (ZMod 2) (finSumFinEquiv.sumCongr finSumFinEquiv) x))
        (finSumFinEquiv.symm m)
  rcases finSumFinEquiv.symm m with a | a
  · show transportedBInc d₁.toData _ a + (0 : Fin d₁.mid → ZMod 2) a
        = transportedBInc d₁.toData _ a
    rw [Pi.zero_apply, add_zero]
    congr 1
  · show (0 : Fin d₂.mid → ZMod 2) a + transportedBInc d₂.toData _ a
        = transportedBInc d₂.toData _ a
    rw [Pi.zero_apply, zero_add]
    congr 1

/-- **THE KERNEL IDENTITY** — the sum membrane's computed Taylor-leg submodule lands EXACTLY on the
tied `charPairAddBorTied`'s `hmeta` submodule: the block Lagrangian of the two components' kernels,
regrouped (`sumSumSumComm`) and de-reindexed (`sumCongr finSumFinEquiv`). Never a free submodule. -/
theorem sum_ker_transportedBInc (d₁ : GeoRealizationTied Sσ₁ Sτ₁ bσ₁ bτ₁)
    (d₂ : GeoRealizationTied Sσ₂ Sτ₂ bσ₂ bτ₂) :
    LinearMap.ker (transportedBInc (GeoRealizationTied.sum d₁ d₂).toData)
      = ((blockSub (LinearMap.ker (transportedBInc d₁.toData))
            (LinearMap.ker (transportedBInc d₂.toData))).comap
          (LinearMap.funLeft (ZMod 2) (ZMod 2)
            (Equiv.sumSumSumComm (Fin nσ₁) (Fin nτ₁) (Fin nσ₂) (Fin nτ₂)))).comap
        (LinearMap.funLeft (ZMod 2) (ZMod 2) (finSumFinEquiv.sumCongr finSumFinEquiv)) := by
  rw [sum_transportedBInc]
  ext v
  rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.mem_comap]
  show LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (finSumFinEquiv (m := d₁.mid) (n := d₂.mid)).symm
        (blockMap (transportedBInc d₁.toData) (transportedBInc d₂.toData)
          (LinearMap.funLeft (ZMod 2) (ZMod 2)
              (Equiv.sumSumSumComm (Fin nσ₁) (Fin nτ₁) (Fin nσ₂) (Fin nτ₂))
            (LinearMap.funLeft (ZMod 2) (ZMod 2) (finSumFinEquiv.sumCongr finSumFinEquiv) v))) = 0
      ↔ LinearMap.funLeft (ZMod 2) (ZMod 2)
            (Equiv.sumSumSumComm (Fin nσ₁) (Fin nτ₁) (Fin nσ₂) (Fin nτ₂))
          (LinearMap.funLeft (ZMod 2) (ZMod 2) (finSumFinEquiv.sumCongr finSumFinEquiv) v)
        ∈ blockSub (LinearMap.ker (transportedBInc d₁.toData))
            (LinearMap.ker (transportedBInc d₂.toData))
  rw [EmbeddingLike.map_eq_zero_iff, ← LinearMap.mem_ker, ker_blockMap]

end Sum

/-! ## §7. `addBorRealized` — the realized+pinned `⊔` op, matching the tied `charPairAddBorTied`. -/

section AddBor
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {k : WithTop ℕ∞}
variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]

/-- **`addBor` REALIZED** — the genuine disjoint union of two realized+pinned bordism data. The
membrane is `GeoRealizationTied.sum β₁.real β₂.real` (the honest `Q₁ ⊔ Q₂`), whose computed Taylor-leg
submodule is the block Lagrangian of the two components' realized kernels regrouped exactly onto
`charPairAddBorTied`'s metabolic submodule (`IsMetabolic.orthSum` + `sumSumSumComm`/`sumCongr`
reindexes). Pins/P14/P23/hwu descend from the pinned provider. The synthetic-`bInc` e₈ exploit has no
`GeoRealizationTied.sum` source. -/
noncomputable def addBorRealized (prov : CharPairWProviderPinned I k)
    {s₁ t₁ s₂ t₂ : SingularManifold.{0} PUnit.{1} k I}
    {b₁ : Bordism (I.prod (𝓡∂ 1)) s₁ t₁} {b₂ : Bordism (I.prod (𝓡∂ 1)) s₂ t₂}
    {σ₁ : CharPairStrBundled I s₁} {τ₁ : CharPairStrBundled I t₁}
    {σ₂ : CharPairStrBundled I s₂} {τ₂ : CharPairStrBundled I t₂}
    (β₁ : CharPairBorRealized b₁ σ₁ τ₁) (β₂ : CharPairBorRealized b₂ σ₂ τ₂) :
    CharPairBorRealized (b₁.add b₂) (charPairBundledSumStr σ₁ σ₂) (charPairBundledSumStr τ₁ τ₂) :=
  haveI := (charPairBundledSumStr σ₁ σ₂).surfT2
  haveI := (charPairBundledSumStr τ₁ τ₂).surfT2
  have hblock : IsMetabolic
      (Z4Quadratic.orthSum (Z4Quadratic.orthSum σ₁.q (Z4Quadratic.neg τ₁.q))
        (Z4Quadratic.orthSum σ₂.q (Z4Quadratic.neg τ₂.q)))
      (blockSub (β₁.real.toMembrane σ₁.q τ₁.q).L (β₂.real.toMembrane σ₂.q τ₂.q).L) :=
    IsMetabolic.orthSum ⟨β₁.htaylor, β₁.hlag⟩ ⟨β₂.htaylor, β₂.hlag⟩
  have hregroup : Z4Quadratic.orthSum (Z4Quadratic.orthSum σ₁.q σ₂.q)
        (Z4Quadratic.neg (Z4Quadratic.orthSum τ₁.q τ₂.q))
      = (Z4Quadratic.orthSum (Z4Quadratic.orthSum σ₁.q (Z4Quadratic.neg τ₁.q))
          (Z4Quadratic.orthSum σ₂.q (Z4Quadratic.neg τ₂.q))).reindex
          (Equiv.sumSumSumComm (Fin σ₁.n) (Fin τ₁.n) (Fin σ₂.n) (Fin τ₂.n)) := by
    rw [neg_orthSum, orthSum_regroup]
  have hbase' := hblock.reindex (Equiv.sumSumSumComm (Fin σ₁.n) (Fin τ₁.n) (Fin σ₂.n) (Fin τ₂.n))
  have hbase : IsMetabolic (Z4Quadratic.orthSum (Z4Quadratic.orthSum σ₁.q σ₂.q)
        (Z4Quadratic.neg (Z4Quadratic.orthSum τ₁.q τ₂.q)))
      ((blockSub (β₁.real.toMembrane σ₁.q τ₁.q).L (β₂.real.toMembrane σ₂.q τ₂.q).L).comap
        (LinearMap.funLeft (ZMod 2) (ZMod 2)
          (Equiv.sumSumSumComm (Fin σ₁.n) (Fin τ₁.n) (Fin σ₂.n) (Fin τ₂.n)))) := by
    rw [hregroup]; exact hbase'
  have hform : jointEnhancement (charPairBundledSumStr σ₁ σ₂).q (charPairBundledSumStr τ₁ τ₂).q
      = (Z4Quadratic.orthSum (Z4Quadratic.orthSum σ₁.q σ₂.q)
          (Z4Quadratic.neg (Z4Quadratic.orthSum τ₁.q τ₂.q))).reindex
          (Equiv.sumCongr finSumFinEquiv finSumFinEquiv) :=
    jointEnhancement_reindex (orthSum σ₁.q σ₂.q) (orthSum τ₁.q τ₂.q) finSumFinEquiv finSumFinEquiv
  have hmeta : IsMetabolic
      (jointEnhancement (charPairBundledSumStr σ₁ σ₂).q (charPairBundledSumStr τ₁ τ₂).q)
      (((blockSub (β₁.real.toMembrane σ₁.q τ₁.q).L (β₂.real.toMembrane σ₂.q τ₂.q).L).comap
          (LinearMap.funLeft (ZMod 2) (ZMod 2)
            (Equiv.sumSumSumComm (Fin σ₁.n) (Fin τ₁.n) (Fin σ₂.n) (Fin τ₂.n)))).comap
        (LinearMap.funLeft (ZMod 2) (ZMod 2) (Equiv.sumCongr finSumFinEquiv finSumFinEquiv))) := by
    rw [hform]; exact hbase.reindex (Equiv.sumCongr finSumFinEquiv finSumFinEquiv)
  mkCharPairBorRealized prov (b₁.add b₂)
    (by haveI : T2Space b₁.W := β₁.hWT2; haveI : T2Space b₂.W := β₂.hWT2
        exact inferInstanceAs (T2Space (b₁.W ⊕ b₂.W)))
    (GeoRealizationTied.sum β₁.real β₂.real)
    (by
      show TaylorLegVanishes _ _ (LinearMap.ker (transportedBInc
        (GeoRealizationTied.sum β₁.real β₂.real).toData))
      rw [sum_ker_transportedBInc]
      exact hmeta.1)
    (by
      show JointLagrangian _ _ (LinearMap.ker (transportedBInc
        (GeoRealizationTied.sum β₁.real β₂.real).toData))
      rw [sum_ker_transportedBInc]
      exact hmeta.2)

end AddBor

end SKEFTHawking.PinPlusCharPairAddRealization
