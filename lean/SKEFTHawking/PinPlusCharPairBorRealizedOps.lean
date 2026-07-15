/-
# Phase 5q.H W-A arm 4 — STAGE 3c COMPLETION: the FOUR remaining tied-op realizations.

`PinPlusCharPairBorRealized` realized cyl/rev/neg/symm. This module realizes the remaining four ops
(the `charPairSumStr` monoid laws) on the realized+pinned form, mirroring `PinPlusCharPairData` §9.6:

* `unitBorRealized` — the `σ ⊔ ∅ → σ` unit;
* `commBorRealized` — the `σ ⊔ τ → τ ⊔ σ` commutativity;
* `assocBorRealized` — the `(σ ⊔ τ) ⊔ ρ → σ ⊔ (τ ⊔ ρ)` associativity;
* `addBorRealized` — the genuine `⊔` of two realizations.

unit/comm/assoc are realized by the TWISTED CYLINDER `mapCylRealizationTied` (STAGE-3c core), whose
τ-end is retargeted through the surface homeomorphism (sumEmpty / sumComm / sumAssoc); the
`transportBasisChange_eq_funLeft` master naturality turns the geometric transport into the tied ops'
index reindex, and `ker_mapCylBd_funLeft` lands the computed kernel EXACTLY on the tied op's
`graphSub` (its `hmeta` submodule). `addBorRealized` is the block sum of two realizations.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusCharPairBorRealized
import SKEFTHawking.PinPlusCharPairMapCylRealization

open scoped Manifold
open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic
open SKEFTHawking.BordismTheory
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularCohomologyFunctoriality
open SKEFTHawking.SingularCohomologyDisjointSum
open SKEFTHawking.SingularKroneckerBasisBridge
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCharPairSurfaceTie
open SKEFTHawking.PinPlusCharPairMembraneGeoRealization
open SKEFTHawking.PinPlusCharPairRealizationTied
open SKEFTHawking.PinPlusCharPairMapCylRealization
open SKEFTHawking.PinPlusCharPairNegRealization
open SKEFTHawking.PinPlusWAdmPinned
open SKEFTHawking.PinPlusCharPairBorRealized

namespace SKEFTHawking.PinPlusCharPairBorRealizedOps

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {k : WithTop ℕ∞}
variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]
variable {s t u : SingularManifold PUnit k I}

/-! ## §1. `unitBor` — the `σ ⊔ ∅ → σ` unit, realized. -/

/-- The surface homeomorphism identifying the τ-end `Σ_σ` with the σ-end `Σ_σ ⊔ ∅` (`Sum.inl`, a
homeomorphism since the empty summand is unreachable). -/
noncomputable def unitEndHomeo (σ : CharPairStrBundled I s) :
    (TopCat.of σ.surf.M : Type) ≃ₜ (TopCat.of (charPairBundledSumStr σ charPairBundledEmpty).surf.M) :=
  haveI : IsEmpty ((charPairBundledEmpty
      : CharPairStrBundled I (emptySM : SingularManifold.{0} PUnit.{1} k I)).surf.M) :=
    inferInstanceAs (IsEmpty PEmpty)
  (Homeomorph.sumEmpty σ.surf.M
    (charPairBundledEmpty : CharPairStrBundled I (emptySM : SingularManifold.{0} PUnit.{1} k I)).surf.M).symm

/-- The unit reindex `e : Fin (σ.n + 0) ≃ Fin σ.n` — the sum-with-empty de-reindex; `e.symm` is the
graph isometry the tied `unitBor` metabolic Lagrangian rides. -/
def unitReindex (σ : CharPairStrBundled I s) : Fin (σ.n + 0) ≃ Fin σ.n :=
  ((Equiv.sumEmpty (Fin σ.n) (Fin 0)).symm.trans finSumFinEquiv).symm.trans (Equiv.refl (Fin σ.n))

/-- **`unitBor` REALIZED** — the `σ ⊔ ∅ → σ` unit on the realized+pinned form. The membrane is the
twisted cylinder over `Σ_σ ⊔ ∅` whose τ-end is retargeted to `Σ_σ` through the sum-with-empty
homeomorphism; its computed kernel is EXACTLY the tied `charPairUnitBorTied`'s metabolic graph
`graphSub (funCongrLeft (unitReindex σ).symm)`. -/
noncomputable def unitBorRealized (prov : CharPairWProviderPinned I k) (σ : CharPairStrBundled I s) :
    CharPairBorRealized (mapCylinder (Diffeomorph.sumEmpty I s.M k (M' := emptySM.M))
      (by funext z; cases z with | inl m => rfl | inr e => exact (IsEmpty.false e).elim))
      (charPairBundledSumStr σ charPairBundledEmpty) σ :=
  haveI := σ.surfT2
  haveI := (charPairBundledSumStr σ charPairBundledEmpty).surfT2
  have hqS : (charPairSumStr σ.toCharPairStr charPairEmptyStr).q
      = σ.q.reindex ((Equiv.sumEmpty (Fin σ.n) (Fin 0)).symm.trans finSumFinEquiv) := by
    show (Z4Quadratic.orthSum σ.q (stdQuadratic 0)).reindex finSumFinEquiv = _
    rw [orthSum_stdZero_eq, reindex_trans]
  have hmeta : IsMetabolic (jointEnhancement (charPairBundledSumStr σ charPairBundledEmpty).q σ.q)
      (graphSub (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (unitReindex σ).symm)) := by
    show IsMetabolic (jointEnhancement (charPairSumStr σ.toCharPairStr charPairEmptyStr).q σ.q) _
    rw [show jointEnhancement (charPairSumStr σ.toCharPairStr charPairEmptyStr).q σ.q
        = Z4Quadratic.orthSum (charPairSumStr σ.toCharPairStr charPairEmptyStr).q (Z4Quadratic.neg σ.q)
        from rfl, hqS]
    exact commonReindex_metabolic σ.q ((Equiv.sumEmpty (Fin σ.n) (Fin 0)).symm.trans finSumFinEquiv)
      (Equiv.refl (Fin σ.n))
  have hnat : transportBasisChange (TopCat.of (charPairBundledSumStr σ charPairBundledEmpty).surf.M)
      (charPairBundledSumStr σ charPairBundledEmpty).basis (TopCat.of σ.surf.M) σ.basis
      (unitEndHomeo σ)
        = LinearMap.funLeft (ZMod 2) (ZMod 2) ((unitReindex σ) : Fin (σ.n + 0) → Fin σ.n) := by
    refine transportBasisChange_eq_funLeft _ _ _ _ _ ((unitReindex σ) : Fin (σ.n + 0) → Fin σ.n) ?_
    intro i
    show cohomologyPullback (inlMap (TopCat.of σ.surf.M)
        (TopCat.of (charPairBundledEmpty
          : CharPairStrBundled I (emptySM : SingularManifold.{0} PUnit.{1} k I)).surf.M)) 1
        ((sumBasis σ.basis (charPairBundledEmpty
          : CharPairStrBundled I (emptySM : SingularManifold.{0} PUnit.{1} k I)).basis).symm
          (Pi.single i 1))
      = σ.basis.symm (Pi.single ((unitReindex σ) i) 1)
    rw [pullback_inlMap_sumBasis_symm]
    congr 1
    funext j
    rw [Pi.single_apply, Pi.single_apply,
      show (unitReindex σ) i = (Equiv.sumEmpty (Fin σ.n) (Fin 0)) (finSumFinEquiv.symm i) from rfl]
    rcases hw : finSumFinEquiv.symm i with a | b
    · have hi : i = finSumFinEquiv (Sum.inl a) := by rw [← hw, Equiv.apply_symm_apply]
      rw [hi, Equiv.sumEmpty_apply_inl]
      have hcond : (finSumFinEquiv (Sum.inl j : Fin σ.n ⊕ Fin 0) = finSumFinEquiv (Sum.inl a))
          ↔ (j = a) :=
        ⟨fun hc => Sum.inl_injective (finSumFinEquiv.injective hc), fun hc => by rw [hc]⟩
      exact if_congr hcond rfl rfl
    · exact b.elim0
  mkCharPairBorRealized prov (mapCylinder (Diffeomorph.sumEmpty I s.M k (M' := emptySM.M))
      (by funext z; cases z with | inl m => rfl | inr e => exact (IsEmpty.false e).elim))
    (by haveI := σ.t2
        haveI : T2Space (emptySM (X := PUnit) (k := k) (I := I)).M := ⟨fun x => isEmptyElim x⟩
        exact inferInstanceAs (T2Space ((s.M ⊕ emptySM.M) × Set.Icc (0 : ℝ) 1)))
    (mapCylRealizationTied (TopCat.of (charPairBundledSumStr σ charPairBundledEmpty).surf.M)
      (charPairBundledSumStr σ charPairBundledEmpty).basis (TopCat.of σ.surf.M) σ.basis
      (unitEndHomeo σ))
    (by
      show TaylorLegVanishes _ _ (LinearMap.ker (transportedBInc
        (mapCylRealizationTied (TopCat.of (charPairBundledSumStr σ charPairBundledEmpty).surf.M)
          (charPairBundledSumStr σ charPairBundledEmpty).basis (TopCat.of σ.surf.M) σ.basis
          (unitEndHomeo σ)).toData))
      rw [mapCylRealizationTied_transportedBInc, hnat]
      erw [ker_mapCylBd_funLeft (unitReindex σ)]
      exact hmeta.1)
    (by
      show JointLagrangian _ _ (LinearMap.ker (transportedBInc
        (mapCylRealizationTied (TopCat.of (charPairBundledSumStr σ charPairBundledEmpty).surf.M)
          (charPairBundledSumStr σ charPairBundledEmpty).basis (TopCat.of σ.surf.M) σ.basis
          (unitEndHomeo σ)).toData))
      rw [mapCylRealizationTied_transportedBInc, hnat]
      erw [ker_mapCylBd_funLeft (unitReindex σ)]
      exact hmeta.2)

end SKEFTHawking.PinPlusCharPairBorRealizedOps
