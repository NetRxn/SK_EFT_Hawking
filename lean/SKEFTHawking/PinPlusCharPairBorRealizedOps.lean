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

/-! ## §2. `commBor` — the `σ ⊔ τ → τ ⊔ σ` commutativity, realized. -/

/-- The surface swap homeomorphism identifying the τ-end `Σ_τ ⊔ Σ_σ` with the σ-end `Σ_σ ⊔ Σ_τ`. -/
noncomputable def commEndHomeo (σ : CharPairStrBundled I s) (τ : CharPairStrBundled I t) :
    (TopCat.of (charPairBundledSumStr τ σ).surf.M : Type)
      ≃ₜ (TopCat.of (charPairBundledSumStr σ τ).surf.M) :=
  Homeomorph.sumComm τ.surf.M σ.surf.M

/-- The commutativity reindex `e : Fin (σ.n + τ.n) ≃ Fin (τ.n + σ.n)` — the flat index swap. -/
def commReindex (σ : CharPairStrBundled I s) (τ : CharPairStrBundled I t) :
    Fin (σ.n + τ.n) ≃ Fin (τ.n + σ.n) :=
  finSumFinEquiv.symm.trans ((Equiv.sumComm (Fin σ.n) (Fin τ.n)).trans finSumFinEquiv)

/-- **The swap-pullback of the sum basis** — pulling back the `A ⊔ B` sum-basis covector along the
surface swap `Σ_B ⊔ Σ_A → Σ_A ⊔ Σ_B` gives the `B ⊔ A` sum-basis covector reindexed by the flat swap. -/
theorem pullback_sumComm_sumBasis_symm
    {A B : TopCat} {nA nB : ℕ}
    (bA : Cohomology A 1 ≃ₗ[ZMod 2] (Fin nA → ZMod 2))
    (bB : Cohomology B 1 ≃ₗ[ZMod 2] (Fin nB → ZMod 2)) (i : Fin (nA + nB)) :
    cohomologyPullback (⟨Homeomorph.sumComm (B : Type) (A : Type),
        (Homeomorph.sumComm (B : Type) (A : Type)).continuous⟩ :
        C(↑(sumSpace B A), ↑(sumSpace A B))) 1
        ((sumBasis bA bB).symm (Pi.single i 1))
      = (sumBasis bB bA).symm
          (Pi.single (finSumFinEquiv ((Equiv.sumComm (Fin nA) (Fin nB))
            (finSumFinEquiv.symm i))) 1) := by
  set sw : C(↑(sumSpace B A), ↑(sumSpace A B)) :=
    ⟨Homeomorph.sumComm (B : Type) (A : Type),
      (Homeomorph.sumComm (B : Type) (A : Type)).continuous⟩ with hsw
  -- the swap intertwines the summand inclusions
  have hinl : sw.comp (inlMap B A) = inrMap A B := by ext b; rfl
  have hinr : sw.comp (inrMap B A) = inlMap A B := by ext a; rfl
  refine (LinearEquiv.eq_symm_apply _).mpr ?_
  refine (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) finSumFinEquiv).injective ?_
  simp only [LinearEquiv.funCongrLeft_apply]
  rw [sumBasis_funLeft]
  -- LHS-inl block: pullback along inl_{B⊕A} ∘ sw = inr_{A⊕B}
  rw [show cohomologyPullback (inlMap B A) 1 (cohomologyPullback sw 1
        ((sumBasis bA bB).symm (Pi.single i 1)))
      = cohomologyPullback (inrMap A B) 1 ((sumBasis bA bB).symm (Pi.single i 1)) from by
    rw [← LinearMap.comp_apply, ← cohomologyPullback_comp, hinl]]
  rw [show cohomologyPullback (inrMap B A) 1 (cohomologyPullback sw 1
        ((sumBasis bA bB).symm (Pi.single i 1)))
      = cohomologyPullback (inlMap A B) 1 ((sumBasis bA bB).symm (Pi.single i 1)) from by
    rw [← LinearMap.comp_apply, ← cohomologyPullback_comp, hinr]]
  rw [pullback_inrMap_sumBasis_symm, pullback_inlMap_sumBasis_symm,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hRHS : (LinearMap.funLeft (ZMod 2) (ZMod 2) (finSumFinEquiv (m := nB) (n := nA)))
      (Pi.single (finSumFinEquiv ((Equiv.sumComm (Fin nA) (Fin nB)) (finSumFinEquiv.symm i))) 1)
      = Pi.single ((Equiv.sumComm (Fin nA) (Fin nB)) (finSumFinEquiv.symm i)) 1 := by
    funext m
    rw [LinearMap.funLeft_apply, Pi.single_apply, Pi.single_apply]
    by_cases hm : m = (Equiv.sumComm (Fin nA) (Fin nB)) (finSumFinEquiv.symm i)
    · rw [if_pos hm, hm, if_pos rfl]
    · rw [if_neg hm, if_neg (fun hc => hm (finSumFinEquiv.injective hc))]
  rw [hRHS]
  funext m
  rcases m with mB | mA
  · rw [Sum.elim_inl, Pi.single_apply, Pi.single_apply]
    have hc : (finSumFinEquiv (Sum.inr mB) = i)
        ↔ (Sum.inl mB = (Equiv.sumComm (Fin nA) (Fin nB)) (finSumFinEquiv.symm i)) := by
      rw [Equiv.apply_eq_iff_eq_symm_apply, ← Equiv.symm_apply_eq (Equiv.sumComm (Fin nA) (Fin nB))]
      rfl
    exact if_congr hc rfl rfl
  · rw [Sum.elim_inr, Pi.single_apply, Pi.single_apply]
    have hc : (finSumFinEquiv (Sum.inl mA) = i)
        ↔ (Sum.inr mA = (Equiv.sumComm (Fin nA) (Fin nB)) (finSumFinEquiv.symm i)) := by
      rw [Equiv.apply_eq_iff_eq_symm_apply, ← Equiv.symm_apply_eq (Equiv.sumComm (Fin nA) (Fin nB))]
      rfl
    exact if_congr hc rfl rfl

/-- **`commBor` REALIZED** — the `σ ⊔ τ → τ ⊔ σ` commutativity on the realized+pinned form. The membrane
is the twisted cylinder over `Σ_σ ⊔ Σ_τ` whose τ-end is retargeted to `Σ_τ ⊔ Σ_σ` through the surface
swap; its computed kernel is EXACTLY the reparametrized-cylinder metabolic graph
`graphSub (funCongrLeft (commReindex σ τ).symm)` (the tied `charPairCommBorTied` kernel). -/
noncomputable def commBorRealized (prov : CharPairWProviderPinned I k)
    (σ : CharPairStrBundled I s) (τ : CharPairStrBundled I t) :
    CharPairBorRealized (mapCylinder (Diffeomorph.sumComm I s.M k t.M)
      (by funext z; rcases z with z | z <;> rfl))
      (charPairBundledSumStr σ τ) (charPairBundledSumStr τ σ) :=
  haveI := (charPairBundledSumStr σ τ).surfT2
  haveI := (charPairBundledSumStr τ σ).surfT2
  have hmeta : IsMetabolic
      (jointEnhancement (charPairBundledSumStr σ τ).q (charPairBundledSumStr τ σ).q)
      (graphSub (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (commReindex σ τ).symm)) := by
    show IsMetabolic (Z4Quadratic.orthSum (charPairSumStr σ.toCharPairStr τ.toCharPairStr).q
      (Z4Quadratic.neg (charPairSumStr τ.toCharPairStr σ.toCharPairStr).q)) _
    rw [show (charPairSumStr σ.toCharPairStr τ.toCharPairStr).q
          = (Z4Quadratic.orthSum σ.q τ.q).reindex finSumFinEquiv from rfl,
        show (charPairSumStr τ.toCharPairStr σ.toCharPairStr).q
          = (Z4Quadratic.orthSum σ.q τ.q).reindex
              ((Equiv.sumComm (Fin σ.n) (Fin τ.n)).trans finSumFinEquiv) from by
          show (Z4Quadratic.orthSum τ.q σ.q).reindex finSumFinEquiv = _
          rw [orthSum_comm_eq σ.q τ.q, reindex_trans]]
    exact commonReindex_metabolic (Z4Quadratic.orthSum σ.q τ.q) finSumFinEquiv
      ((Equiv.sumComm (Fin σ.n) (Fin τ.n)).trans finSumFinEquiv)
  have hnat : transportBasisChange (TopCat.of (charPairBundledSumStr σ τ).surf.M)
      (charPairBundledSumStr σ τ).basis (TopCat.of (charPairBundledSumStr τ σ).surf.M)
      (charPairBundledSumStr τ σ).basis (commEndHomeo σ τ)
        = LinearMap.funLeft (ZMod 2) (ZMod 2)
            ((commReindex σ τ) : Fin (σ.n + τ.n) → Fin (τ.n + σ.n)) := by
    refine transportBasisChange_eq_funLeft _ _ _ _ _
      ((commReindex σ τ) : Fin (σ.n + τ.n) → Fin (τ.n + σ.n)) ?_
    intro i
    show cohomologyPullback (⟨Homeomorph.sumComm (τ.surf.M) (σ.surf.M),
        (Homeomorph.sumComm (τ.surf.M) (σ.surf.M)).continuous⟩ :
        C(↑(sumSpace (TopCat.of τ.surf.M) (TopCat.of σ.surf.M)),
          ↑(sumSpace (TopCat.of σ.surf.M) (TopCat.of τ.surf.M)))) 1
        ((sumBasis σ.basis τ.basis).symm (Pi.single i 1))
      = (sumBasis τ.basis σ.basis).symm (Pi.single ((commReindex σ τ) i) 1)
    erw [pullback_sumComm_sumBasis_symm]
    rfl
  mkCharPairBorRealized prov (mapCylinder (Diffeomorph.sumComm I s.M k t.M)
      (by funext z; rcases z with z | z <;> rfl))
    (by haveI := σ.t2; haveI := τ.t2
        exact inferInstanceAs (T2Space ((s.M ⊕ t.M) × Set.Icc (0 : ℝ) 1)))
    (mapCylRealizationTied (TopCat.of (charPairBundledSumStr σ τ).surf.M)
      (charPairBundledSumStr σ τ).basis (TopCat.of (charPairBundledSumStr τ σ).surf.M)
      (charPairBundledSumStr τ σ).basis (commEndHomeo σ τ))
    (by
      show TaylorLegVanishes _ _ (LinearMap.ker (transportedBInc
        (mapCylRealizationTied (TopCat.of (charPairBundledSumStr σ τ).surf.M)
          (charPairBundledSumStr σ τ).basis (TopCat.of (charPairBundledSumStr τ σ).surf.M)
          (charPairBundledSumStr τ σ).basis (commEndHomeo σ τ)).toData))
      rw [mapCylRealizationTied_transportedBInc, hnat]
      erw [ker_mapCylBd_funLeft (commReindex σ τ)]
      exact hmeta.1)
    (by
      show JointLagrangian _ _ (LinearMap.ker (transportedBInc
        (mapCylRealizationTied (TopCat.of (charPairBundledSumStr σ τ).surf.M)
          (charPairBundledSumStr σ τ).basis (TopCat.of (charPairBundledSumStr τ σ).surf.M)
          (charPairBundledSumStr τ σ).basis (commEndHomeo σ τ)).toData))
      rw [mapCylRealizationTied_transportedBInc, hnat]
      erw [ker_mapCylBd_funLeft (commReindex σ τ)]
      exact hmeta.2)

/-! ## §3. `assocBor` — the `(σ ⊔ τ) ⊔ ρ → σ ⊔ (τ ⊔ ρ)` associativity, realized. -/

/-- The surface reassociation homeomorphism `Σ_σ ⊔ (Σ_τ ⊔ Σ_ρ) ≃ₜ (Σ_σ ⊔ Σ_τ) ⊔ Σ_ρ`. -/
noncomputable def assocEndHomeo (σ : CharPairStrBundled I s) (τ : CharPairStrBundled I t)
    (ρ : CharPairStrBundled I u) :
    (TopCat.of (charPairBundledSumStr σ (charPairBundledSumStr τ ρ)).surf.M : Type)
      ≃ₜ (TopCat.of (charPairBundledSumStr (charPairBundledSumStr σ τ) ρ).surf.M) :=
  (Homeomorph.sumAssoc σ.surf.M τ.surf.M ρ.surf.M).symm

/-- The associativity reindex `Fin ((σ.n + τ.n) + ρ.n) ≃ Fin (σ.n + (τ.n + ρ.n))` (`e₁.symm.trans e₂`
of the tied `assocBor`'s common-reindex pair). -/
def assocReindex (σ : CharPairStrBundled I s) (τ : CharPairStrBundled I t)
    (ρ : CharPairStrBundled I u) : Fin (σ.n + τ.n + ρ.n) ≃ Fin (σ.n + (τ.n + ρ.n)) :=
  ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin ρ.n))).trans finSumFinEquiv).symm.trans
    ((Equiv.sumAssoc (Fin σ.n) (Fin τ.n) (Fin ρ.n)).trans
      ((Equiv.sumCongr (Equiv.refl (Fin σ.n)) finSumFinEquiv).trans finSumFinEquiv))

/-- **The reassociation-pullback of the nested sum basis** — pulling back the `(A ⊔ B) ⊔ C` nested
sum-basis covector along the surface reassociation `A ⊔ (B ⊔ C) → (A ⊔ B) ⊔ C` gives the
`A ⊔ (B ⊔ C)` nested sum-basis covector reindexed by the flat associativity permutation. -/
theorem pullback_sumAssoc_sumBasis_symm
    {A B C : TopCat} {nA nB nC : ℕ}
    (bA : Cohomology A 1 ≃ₗ[ZMod 2] (Fin nA → ZMod 2))
    (bB : Cohomology B 1 ≃ₗ[ZMod 2] (Fin nB → ZMod 2))
    (bC : Cohomology C 1 ≃ₗ[ZMod 2] (Fin nC → ZMod 2)) (i : Fin (nA + nB + nC)) :
    cohomologyPullback (⟨(Homeomorph.sumAssoc (A : Type) (B : Type) (C : Type)).symm,
        (Homeomorph.sumAssoc (A : Type) (B : Type) (C : Type)).symm.continuous⟩ :
        C(↑(sumSpace A (sumSpace B C)), ↑(sumSpace (sumSpace A B) C))) 1
        ((sumBasis (sumBasis bA bB) bC).symm (Pi.single i 1))
      = (sumBasis bA (sumBasis bB bC)).symm
          (Pi.single (finSumFinEquiv ((Equiv.sumCongr (Equiv.refl (Fin nA)) finSumFinEquiv)
            ((Equiv.sumAssoc (Fin nA) (Fin nB) (Fin nC))
              ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin nC))).symm
                (finSumFinEquiv.symm i))))) 1) := by
  set sw : C(↑(sumSpace A (sumSpace B C)), ↑(sumSpace (sumSpace A B) C)) :=
    ⟨(Homeomorph.sumAssoc (A : Type) (B : Type) (C : Type)).symm,
      (Homeomorph.sumAssoc (A : Type) (B : Type) (C : Type)).symm.continuous⟩ with hsw
  have hAl : sw.comp (inlMap A (sumSpace B C))
      = (inlMap (sumSpace A B) C).comp (inlMap A B) := by ext a; rfl
  have hBl : sw.comp ((inrMap A (sumSpace B C)).comp (inlMap B C))
      = (inlMap (sumSpace A B) C).comp (inrMap A B) := by ext b; rfl
  have hCr : sw.comp ((inrMap A (sumSpace B C)).comp (inrMap B C))
      = inrMap (sumSpace A B) C := by ext c; rfl
  set X := (sumBasis (sumBasis bA bB) bC).symm (Pi.single i 1) with hX
  refine (LinearEquiv.eq_symm_apply _).mpr ?_
  refine (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) finSumFinEquiv).injective ?_
  simp only [LinearEquiv.funCongrLeft_apply]
  rw [sumBasis_funLeft]
  have hA : cohomologyPullback (inlMap A (sumSpace B C)) 1 (cohomologyPullback sw 1 X)
      = bA.symm (fun j => (Pi.single i 1 : Fin (nA + nB + nC) → ZMod 2)
          (finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inl j))))) := by
    rw [← LinearMap.comp_apply, ← cohomologyPullback_comp, hAl, cohomologyPullback_comp,
      LinearMap.comp_apply, hX, pullback_inlMap_sumBasis_symm, pullback_inlMap_sumBasis_symm]
  have hB : cohomologyPullback (inlMap B C) 1
        (cohomologyPullback (inrMap A (sumSpace B C)) 1 (cohomologyPullback sw 1 X))
      = bB.symm (fun j => (Pi.single i 1 : Fin (nA + nB + nC) → ZMod 2)
          (finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inr j))))) := by
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← cohomologyPullback_comp,
      ← cohomologyPullback_comp, hBl, cohomologyPullback_comp, LinearMap.comp_apply, hX,
      pullback_inlMap_sumBasis_symm, pullback_inrMap_sumBasis_symm]
  have hC : cohomologyPullback (inrMap B C) 1
        (cohomologyPullback (inrMap A (sumSpace B C)) 1 (cohomologyPullback sw 1 X))
      = bC.symm (fun j => (Pi.single i 1 : Fin (nA + nB + nC) → ZMod 2)
          (finSumFinEquiv (Sum.inr j))) := by
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← cohomologyPullback_comp,
      ← cohomologyPullback_comp, hCr, hX, pullback_inrMap_sumBasis_symm]
  set assocFlatE : Fin (nA + nB + nC) ≃ Fin nA ⊕ Fin (nB + nC) :=
    finSumFinEquiv.symm.trans ((finSumFinEquiv.sumCongr (Equiv.refl (Fin nC))).symm.trans
      ((Equiv.sumAssoc (Fin nA) (Fin nB) (Fin nC)).trans
        ((Equiv.refl (Fin nA)).sumCongr finSumFinEquiv))) with hAE
  set Y : Fin nA ⊕ Fin (nB + nC) :=
    ((Equiv.refl (Fin nA)).sumCongr finSumFinEquiv)
      ((Equiv.sumAssoc (Fin nA) (Fin nB) (Fin nC))
        ((finSumFinEquiv.sumCongr (Equiv.refl (Fin nC))).symm (finSumFinEquiv.symm i))) with hY
  have hYE : Y = assocFlatE i := rfl
  have hRHS : (LinearMap.funLeft (ZMod 2) (ZMod 2) (finSumFinEquiv (m := nA) (n := nB + nC)))
      (Pi.single (finSumFinEquiv Y) 1) = Pi.single Y 1 := by
    funext m
    rw [LinearMap.funLeft_apply, Pi.single_apply, Pi.single_apply]
    by_cases hm : m = Y
    · rw [if_pos hm, hm, if_pos rfl]
    · rw [if_neg hm, if_neg (fun hc => hm (finSumFinEquiv.injective hc))]
  rw [hRHS, hA, LinearEquiv.apply_symm_apply]
  -- reduce the B⊕C block to explicit leaf deltas
  have hBCfun : (LinearMap.funLeft (ZMod 2) (ZMod 2) (finSumFinEquiv (m := nB) (n := nC)))
      ((sumBasis bB bC) (cohomologyPullback (inrMap A (sumSpace B C)) 1 (cohomologyPullback sw 1 X)))
      = Sum.elim (fun j => (Pi.single i 1 : Fin (nA + nB + nC) → ZMod 2)
          (finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inr j)))))
          (fun j => (Pi.single i 1 : Fin (nA + nB + nC) → ZMod 2) (finSumFinEquiv (Sum.inr j))) := by
    rw [sumBasis_funLeft, hB, hC, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  funext m
  rcases m with a | bc
  · rw [Sum.elim_inl, Pi.single_apply, Pi.single_apply]
    have hc : (finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inl a))) = i) ↔ (Sum.inl a = Y) := by
      rw [hYE, show finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inl a)))
        = assocFlatE.symm (Sum.inl a) from rfl]
      exact Equiv.symm_apply_eq assocFlatE
    exact if_congr hc rfl rfl
  · rw [Sum.elim_inr,
      show (sumBasis bB bC) (cohomologyPullback (inrMap A (sumSpace B C)) 1
          (cohomologyPullback sw 1 X)) bc
        = (LinearMap.funLeft (ZMod 2) (ZMod 2) (finSumFinEquiv (m := nB) (n := nC)))
            ((sumBasis bB bC) (cohomologyPullback (inrMap A (sumSpace B C)) 1
              (cohomologyPullback sw 1 X))) (finSumFinEquiv.symm bc) from by
        rw [LinearMap.funLeft_apply, Equiv.apply_symm_apply], hBCfun, Pi.single_apply]
    rcases hbc : finSumFinEquiv.symm bc with jB | jC
    · rw [Sum.elim_inl, Pi.single_apply]
      have hc : (finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inr jB))) = i)
          ↔ (Sum.inr bc = Y) := by
        rw [hYE, show finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inr jB)))
          = assocFlatE.symm (Sum.inr bc) from by
            simp only [hAE, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.sumCongr_symm,
              Equiv.refl_symm, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
              hbc, Equiv.sumAssoc_symm_apply_inr_inl]]
        exact Equiv.symm_apply_eq assocFlatE
      exact if_congr hc rfl rfl
    · rw [Sum.elim_inr, Pi.single_apply]
      have hc : (finSumFinEquiv (Sum.inr jC) = i) ↔ (Sum.inr bc = Y) := by
        rw [hYE, show finSumFinEquiv (Sum.inr jC)
          = assocFlatE.symm (Sum.inr bc) from by
            simp only [hAE, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.sumCongr_symm,
              Equiv.refl_symm, Equiv.sumCongr_apply, Equiv.refl_apply, Sum.map_inr,
              hbc, Equiv.sumAssoc_symm_apply_inr_inr]]
        exact Equiv.symm_apply_eq assocFlatE
      exact if_congr hc rfl rfl

/-- **`assocBor` REALIZED** — the `(σ ⊔ τ) ⊔ ρ → σ ⊔ (τ ⊔ ρ)` associativity on the realized+pinned form.
The membrane is the twisted cylinder over `(Σ_σ ⊔ Σ_τ) ⊔ Σ_ρ` whose τ-end is retargeted to
`Σ_σ ⊔ (Σ_τ ⊔ Σ_ρ)` through the surface reassociation; its computed kernel is EXACTLY the tied
`charPairAssocBorTied` metabolic graph `graphSub (funCongrLeft (assocReindex σ τ ρ).symm)`. -/
noncomputable def assocBorRealized (prov : CharPairWProviderPinned I k)
    (σ : CharPairStrBundled I s) (τ : CharPairStrBundled I t) (ρ : CharPairStrBundled I u) :
    CharPairBorRealized (mapCylinder (Diffeomorph.sumAssoc I s.M k t.M u.M)
      (by funext w; rcases w with (w | w) | w <;> rfl))
      (charPairBundledSumStr (charPairBundledSumStr σ τ) ρ)
      (charPairBundledSumStr σ (charPairBundledSumStr τ ρ)) :=
  haveI := (charPairBundledSumStr (charPairBundledSumStr σ τ) ρ).surfT2
  haveI := (charPairBundledSumStr σ (charPairBundledSumStr τ ρ)).surfT2
  have hqS : (charPairSumStr (charPairSumStr σ.toCharPairStr τ.toCharPairStr) ρ.toCharPairStr).q
      = (Z4Quadratic.orthSum (Z4Quadratic.orthSum σ.q τ.q) ρ.q).reindex
          ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin ρ.n))).trans finSumFinEquiv) := by
    show (Z4Quadratic.orthSum ((Z4Quadratic.orthSum σ.q τ.q).reindex finSumFinEquiv) ρ.q).reindex
        finSumFinEquiv = _
    conv_lhs => rw [← reindex_refl ρ.q]
    rw [orthSum_reindex, reindex_trans]
  have hqT : (charPairSumStr σ.toCharPairStr (charPairSumStr τ.toCharPairStr ρ.toCharPairStr)).q
      = (Z4Quadratic.orthSum (Z4Quadratic.orthSum σ.q τ.q) ρ.q).reindex
          ((Equiv.sumAssoc (Fin σ.n) (Fin τ.n) (Fin ρ.n)).trans
            ((Equiv.sumCongr (Equiv.refl (Fin σ.n)) finSumFinEquiv).trans finSumFinEquiv)) := by
    show (Z4Quadratic.orthSum σ.q ((Z4Quadratic.orthSum τ.q ρ.q).reindex finSumFinEquiv)).reindex
        finSumFinEquiv = _
    conv_lhs => rw [← reindex_refl σ.q]
    rw [orthSum_reindex, reindex_trans, orthSum_assoc_eq, reindex_trans]
  have hmeta : IsMetabolic
      (jointEnhancement (charPairBundledSumStr (charPairBundledSumStr σ τ) ρ).q
        (charPairBundledSumStr σ (charPairBundledSumStr τ ρ)).q)
      (graphSub (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (assocReindex σ τ ρ).symm)) := by
    show IsMetabolic (Z4Quadratic.orthSum
      (charPairSumStr (charPairSumStr σ.toCharPairStr τ.toCharPairStr) ρ.toCharPairStr).q
      (Z4Quadratic.neg
        (charPairSumStr σ.toCharPairStr (charPairSumStr τ.toCharPairStr ρ.toCharPairStr)).q)) _
    rw [hqS, hqT]
    exact commonReindex_metabolic (Z4Quadratic.orthSum (Z4Quadratic.orthSum σ.q τ.q) ρ.q)
      ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin ρ.n))).trans finSumFinEquiv)
      ((Equiv.sumAssoc (Fin σ.n) (Fin τ.n) (Fin ρ.n)).trans
        ((Equiv.sumCongr (Equiv.refl (Fin σ.n)) finSumFinEquiv).trans finSumFinEquiv))
  have hnat : transportBasisChange
      (TopCat.of (charPairBundledSumStr (charPairBundledSumStr σ τ) ρ).surf.M)
      (charPairBundledSumStr (charPairBundledSumStr σ τ) ρ).basis
      (TopCat.of (charPairBundledSumStr σ (charPairBundledSumStr τ ρ)).surf.M)
      (charPairBundledSumStr σ (charPairBundledSumStr τ ρ)).basis (assocEndHomeo σ τ ρ)
        = LinearMap.funLeft (ZMod 2) (ZMod 2)
            ((assocReindex σ τ ρ) : Fin (σ.n + τ.n + ρ.n) → Fin (σ.n + (τ.n + ρ.n))) := by
    refine transportBasisChange_eq_funLeft _ _ _ _ _
      ((assocReindex σ τ ρ) : Fin (σ.n + τ.n + ρ.n) → Fin (σ.n + (τ.n + ρ.n))) ?_
    intro i
    show cohomologyPullback (⟨(Homeomorph.sumAssoc σ.surf.M τ.surf.M ρ.surf.M).symm,
        (Homeomorph.sumAssoc σ.surf.M τ.surf.M ρ.surf.M).symm.continuous⟩ :
        C(↑(sumSpace (TopCat.of σ.surf.M) (sumSpace (TopCat.of τ.surf.M) (TopCat.of ρ.surf.M))),
          ↑(sumSpace (sumSpace (TopCat.of σ.surf.M) (TopCat.of τ.surf.M)) (TopCat.of ρ.surf.M)))) 1
        ((sumBasis (sumBasis σ.basis τ.basis) ρ.basis).symm (Pi.single i 1))
      = (sumBasis σ.basis (sumBasis τ.basis ρ.basis)).symm
          (Pi.single ((assocReindex σ τ ρ) i) 1)
    erw [pullback_sumAssoc_sumBasis_symm]
    rfl
  mkCharPairBorRealized prov (mapCylinder (Diffeomorph.sumAssoc I s.M k t.M u.M)
      (by funext w; rcases w with (w | w) | w <;> rfl))
    (by haveI := σ.t2; haveI := τ.t2; haveI := ρ.t2
        exact inferInstanceAs (T2Space (((s.M ⊕ t.M) ⊕ u.M) × Set.Icc (0 : ℝ) 1)))
    (mapCylRealizationTied (TopCat.of (charPairBundledSumStr (charPairBundledSumStr σ τ) ρ).surf.M)
      (charPairBundledSumStr (charPairBundledSumStr σ τ) ρ).basis
      (TopCat.of (charPairBundledSumStr σ (charPairBundledSumStr τ ρ)).surf.M)
      (charPairBundledSumStr σ (charPairBundledSumStr τ ρ)).basis (assocEndHomeo σ τ ρ))
    (by
      show TaylorLegVanishes _ _ (LinearMap.ker (transportedBInc
        (mapCylRealizationTied
          (TopCat.of (charPairBundledSumStr (charPairBundledSumStr σ τ) ρ).surf.M)
          (charPairBundledSumStr (charPairBundledSumStr σ τ) ρ).basis
          (TopCat.of (charPairBundledSumStr σ (charPairBundledSumStr τ ρ)).surf.M)
          (charPairBundledSumStr σ (charPairBundledSumStr τ ρ)).basis (assocEndHomeo σ τ ρ)).toData))
      rw [mapCylRealizationTied_transportedBInc, hnat]
      erw [ker_mapCylBd_funLeft (assocReindex σ τ ρ)]
      exact hmeta.1)
    (by
      show JointLagrangian _ _ (LinearMap.ker (transportedBInc
        (mapCylRealizationTied
          (TopCat.of (charPairBundledSumStr (charPairBundledSumStr σ τ) ρ).surf.M)
          (charPairBundledSumStr (charPairBundledSumStr σ τ) ρ).basis
          (TopCat.of (charPairBundledSumStr σ (charPairBundledSumStr τ ρ)).surf.M)
          (charPairBundledSumStr σ (charPairBundledSumStr τ ρ)).basis (assocEndHomeo σ τ ρ)).toData))
      rw [mapCylRealizationTied_transportedBInc, hnat]
      erw [ker_mapCylBd_funLeft (assocReindex σ τ ρ)]
      exact hmeta.2)

end SKEFTHawking.PinPlusCharPairBorRealizedOps
