/-
# Phase 5q.H (W-A arm 4) — STAGE 3b: THE DOUBLING REALIZATION.

`PinPlusCharPairCylRealization` built the honest cylinder realization `cylRealizationTied`
(`transportedBInc = cylBd ⟹ L = cylLagrangian`, the reflexive `Σ ⊔ Σ → ∅` op's realized fold-kernel).
This module builds the OTHER discriminating op the Stage-4 swap needs — the **doubling realization**,
the realized geometric witness for `charPairNegBorTied`'s `(M,σ̄) ⊔ (M,σ) → ∅` law.

Its geometry is the SAME cylinder membrane `Q = Σ × [0,1]` with the SAME two-slice boundary inclusion
`ι = cylBdryIncl`, but the clopen split groups BOTH ends onto the **σ-side** (`U = Set.univ`), so the
σ-end is the whole boundary `Σ ⊔ Σ` (rank `n + n`, basis `sumBasisW … basis basis`) and the τ-end is
the EMPTY space (rank `0`, the degenerate empty-end form). The transported boundary-inclusion is then
EXACTLY `negBorBInc n` (the fold after de-reindexing, ignoring the empty τ-block), whence its computed
Taylor-leg submodule is the reindexed anti-diagonal — never a free/synthetic `bInc`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusCharPairCylRealization

open Topology unitInterval
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularCohomologyFunctoriality
open SKEFTHawking.SingularKroneckerBasisBridge SKEFTHawking.SingularKroneckerEquiv
open SKEFTHawking.SingularPairLES SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularCohomologyPairRestrict
open SKEFTHawking.SingularProdContractibleInt
open SKEFTHawking.SingularDisjointUnion SKEFTHawking.SingularDisjointUnionHn
open SKEFTHawking.SingularCohomologyDisjointSum
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderNumerics
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspension
open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic
open SKEFTHawking.PinPlusCharPairData (negBorBInc negBorBInc_ker cylBd cylLagrangian)
open SKEFTHawking.PinPlusCharPairMembraneGeoRealization
open SKEFTHawking.PinPlusCharPairRealizationTied
open SKEFTHawking.PinPlusCharPairSurfaceTie
open SKEFTHawking.PinPlusCharPairCylRealization

namespace SKEFTHawking.PinPlusCharPairNegRealization

/-- A homeomorphism between any two empty spaces (used for the degenerate empty τ-end). -/
noncomputable def emptyHomeo {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    [IsEmpty A] [IsEmpty B] : A ≃ₜ B where
  toFun := isEmptyElim
  invFun := isEmptyElim
  left_inv := fun a => isEmptyElim a
  right_inv := fun b => isEmptyElim b
  continuous_toFun := by continuity
  continuous_invFun := by continuity

variable {n : ℕ} (Y : TopCat) [T2Space (Y : Type)] [CompactSpace (Y : Type)]
  (basis : Cohomology Y 1 ≃ₗ[ZMod 2] (Fin n → ZMod 2))
  (Sτ : TopCat) [IsEmpty (Sτ : Type)] (bτ : Cohomology Sτ 1 ≃ₗ[ZMod 2] (Fin 0 → ZMod 2))

/-- **THE DOUBLING REALIZATION** — the cylinder membrane `Q = Σ × [0,1]` as a `GeoRealizationTied` for
the end pair `(Σ ⊔ Σ, ∅)`: both cylinder ends are grouped onto the σ-side (`U = Set.univ`), so
`Σ_σ = ∂Q = Σ ⊔ Σ` (basis `sumBasisW basis basis`, rank `n + n`) and `Σ_τ = ∅` (the empty-end form,
rank `0`). Same geometry as `cylRealizationTied`; different clopen split. -/
noncomputable def doublingRealizationTied :
    GeoRealizationTied (TopCat.of ((Y : Type) ⊕ (Y : Type))) Sτ
      (sumBasisW (TopCat.of ((Y : Type) ⊕ (Y : Type))) rfl basis basis) bτ where
  bdry := TopCat.of ((Y : Type) ⊕ (Y : Type))
  Q := ProdSp Y (TopCat.of unitInterval)
  U := Set.univ
  hU := isClopen_univ
  bdryT2 := inferInstanceAs (T2Space ((Y : Type) ⊕ (Y : Type)))
  bdryCompact := inferInstanceAs (CompactSpace ((Y : Type) ⊕ (Y : Type)))
  QT2 := inferInstanceAs (T2Space (↑Y × I))
  QCompact := inferInstanceAs (CompactSpace (↑Y × I))
  ι := cylBdryIncl Y
  hιce := (cylBdryIncl Y).continuous.isClosedEmbedding (cylBdryIncl_injective Y)
  homσ := Homeomorph.Set.univ ((Y : Type) ⊕ (Y : Type))
  homτ := (Homeomorph.setCongr Set.compl_univ).trans emptyHomeo
  mid := n
  eQ := (prodContractibleHomologyEquiv Y (TopCat.of unitInterval) ⊥ iccContraction
      slice_iccContraction_zero slice_iccContraction_one 0).trans
    (homologyBasisOfCohomologyBasis basis)

/-! ## §2. THE GEOMETRIC REDUCTION — the doubling realization shares `Q`, `ι`, `eQ` with the cylinder
realization, so its transported boundary-inclusion is the cylinder fold `cylBd n` precomposed with the
change-of-source-coordinates `srcEquiv_cyl ∘ srcEquiv_dbl.symm`. This routes ALL the geometry
(collapse, two-slice inclusions) through the already-proved `cylRealizationTied_transportedBInc`, so the
remaining obligation is purely algebraic (§3). -/

theorem doublingRealizationTied_transportedBInc_eq_reindex :
    transportedBInc (doublingRealizationTied Y basis Sτ bτ).toData
      = (cylBd n).comp
          ((srcEquiv (cylRealizationTied Y basis).toData).toLinearMap.comp
            (srcEquiv (doublingRealizationTied Y basis Sτ bτ).toData).symm.toLinearMap) := by
  refine LinearMap.ext fun x => ?_
  set w := (srcEquiv (doublingRealizationTied Y basis Sτ bτ).toData).symm x with hw
  have key : (cylRealizationTied Y basis).toData.eQ
        (Homology.map (cylRealizationTied Y basis).toData.ι 1 w)
      = cylBd n ((srcEquiv (cylRealizationTied Y basis).toData) w) := by
    have hpt := LinearMap.congr_fun (cylRealizationTied_transportedBInc Y basis)
      ((srcEquiv (cylRealizationTied Y basis).toData) w)
    rw [transportedBInc] at hpt
    -- v4.32, two independent breakages, hence the two-step shape:
    -- (1) `simp` no longer breaks up the `∘ₗ` chain on its own, so `hpt` stays composed with
    --     `(srcEquiv _).symm` applied to `(srcEquiv _) w` rather than collapsing to `w` — name
    --     the composition-application and round-trip lemmas explicitly.
    -- (2) Mathlib v4.32 ships TWO distinct `EquivLike (M ≃ₛₗ[σ] M₂) M M₂` instances
    --     (`LinearEquiv.instEquivLike` and `DFinsupp.instEquivLikeLinearEquiv`). The goal carries
    --     one and `hpt` the other, and they are defeq but not syntactically equal, so `simpa`'s
    --     closing step — which unifies at reducible transparency — cannot bridge them. Splitting
    --     the normalization (`simp only … at hpt`) from the close (bare `exact`, default
    --     transparency) lets defeq do it. Do NOT recombine these into one `simpa`.
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at hpt
    exact hpt
  exact key

/-! ## §3. THE SOURCE-COORDINATE IDENTITY (the UCT-dual-of-disjoint-union threading). -/

/-- **The doubling realization's source-inverse** — since the σ-end is the WHOLE boundary
(`U = univ`, identified with `Σ ⊔ Σ` via `Homeomorph.Set.univ`) and the τ-end is empty, the inverse
source-coordinate map is just the UCT-dual of the carried sum-cohomology basis, applied to the σ-block
of `x`. -/
theorem doublingRealizationTied_srcEquiv_symm (x : Fin (n + n) ⊕ Fin 0 → ZMod 2) :
    (srcEquiv (doublingRealizationTied Y basis Sτ bτ).toData).symm x
      = (homologyBasisOfCohomologyBasis (sumBasis basis basis)).symm (fun i => x (Sum.inl i)) := by
  rw [srcEquiv_symm_apply]
  have hτ0 : homIncl ((doublingRealizationTied Y basis Sτ bτ).toData.U)ᶜ 1
      ((doublingRealizationTied Y basis Sτ bτ).toData.eτ.symm (fun i => x (Sum.inr i))) = 0 := by
    haveI : IsEmpty (↑(sub ((doublingRealizationTied Y basis Sτ bτ).toData.U)ᶜ)) := by
      show IsEmpty (↥((Set.univ : Set ((Y : Type) ⊕ (Y : Type)))ᶜ))
      rw [Set.compl_univ]; infer_instance
    rw [Subsingleton.elim ((doublingRealizationTied Y basis Sτ bτ).toData.eτ.symm
      (fun i => x (Sum.inr i))) 0, map_zero]
  rw [hτ0, add_zero]
  have heσ : (doublingRealizationTied Y basis Sτ bτ).toData.eσ
      = (homeoHomologyEquiv (Homeomorph.Set.univ ((Y : Type) ⊕ (Y : Type))) 1).trans
          (homologyBasisOfCohomologyBasis (sumBasis basis basis)) := rfl
  rw [heσ, LinearEquiv.symm_trans_apply]
  set w0 := (homologyBasisOfCohomologyBasis (sumBasis basis basis)).symm (fun i => x (Sum.inl i))
    with hw0
  rw [homIncl_eq_map, homeoHomologyEquiv_symm_apply, ← LinearMap.comp_apply, ← Homology.map_comp]
  have hcomp : (subInclCM (doublingRealizationTied Y basis Sτ bτ).toData.U).comp
      ⟨(Homeomorph.Set.univ ((Y : Type) ⊕ (Y : Type))).symm,
        (Homeomorph.Set.univ ((Y : Type) ⊕ (Y : Type))).symm.continuous⟩
      = ContinuousMap.id _ := by ext z; rfl
  erw [hcomp, Homology.map_id, LinearMap.id_apply]

/-- **The cylinder realization's source-inverse** — the two ends `Σ ⊔ Σ` are the two summands of the
boundary; the inverse source-coordinate map reassembles the two blocks of `r` through the individual
UCT-dual basis `homologyBasisOfCohomologyBasis basis` and the summand inclusions `inlMap`/`inrMap`. -/
theorem cylRealizationTied_srcEquiv_symm (r : Fin n ⊕ Fin n → ZMod 2) :
    (srcEquiv (cylRealizationTied Y basis).toData).symm r
      = Homology.map (inlMap Y Y) 1
          ((homologyBasisOfCohomologyBasis basis).symm (fun i => r (Sum.inl i)))
        + Homology.map (inrMap Y Y) 1
          ((homologyBasisOfCohomologyBasis basis).symm (fun i => r (Sum.inr i))) := by
  have heσ : (cylRealizationTied Y basis).toData.eσ
      = (homeoHomologyEquiv (IsClosedEmbedding.inl (X := (Y : Type))).isEmbedding.toHomeomorph.symm
            1).trans (homologyBasisOfCohomologyBasis basis) := rfl
  have heτ : (cylRealizationTied Y basis).toData.eτ
      = (homeoHomologyEquiv ((Homeomorph.setCongr Set.compl_range_inl).trans
            (IsClosedEmbedding.inr (X := (Y : Type))).isEmbedding.toHomeomorph.symm) 1).trans
          (homologyBasisOfCohomologyBasis basis) := rfl
  rw [srcEquiv_symm_apply, heσ, heτ, LinearEquiv.symm_trans_apply, LinearEquiv.symm_trans_apply,
    homIncl_eq_map, homIncl_eq_map, homeoHomologyEquiv_symm_apply, homeoHomologyEquiv_symm_apply,
    ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← Homology.map_comp, ← Homology.map_comp]
  rfl

/-- The `inl`-pullback of the sum-cohomology-basis inverse is the summand basis inverse of the
`inl`-reindexed block. Derived from `sumBasis_funLeft`. -/
theorem pullback_inlMap_sumBasis_symm {nσ nτ : ℕ} {A B : TopCat}
    (bσ : Cohomology A 1 ≃ₗ[ZMod 2] (Fin nσ → ZMod 2))
    (bτ : Cohomology B 1 ≃ₗ[ZMod 2] (Fin nτ → ZMod 2)) (w : Fin (nσ + nτ) → ZMod 2) :
    cohomologyPullback (inlMap A B) 1 ((sumBasis bσ bτ).symm w)
      = bσ.symm (fun i => w (finSumFinEquiv (Sum.inl i))) := by
  have h := sumBasis_funLeft bσ bτ ((sumBasis bσ bτ).symm w)
  rw [LinearEquiv.apply_symm_apply] at h
  rw [LinearEquiv.eq_symm_apply]
  funext i
  have hi := congrFun h (Sum.inl i)
  simpa using hi.symm

/-- The `inr`-pullback of the sum-cohomology-basis inverse. -/
theorem pullback_inrMap_sumBasis_symm {nσ nτ : ℕ} {A B : TopCat}
    (bσ : Cohomology A 1 ≃ₗ[ZMod 2] (Fin nσ → ZMod 2))
    (bτ : Cohomology B 1 ≃ₗ[ZMod 2] (Fin nτ → ZMod 2)) (w : Fin (nσ + nτ) → ZMod 2) :
    cohomologyPullback (inrMap A B) 1 ((sumBasis bσ bτ).symm w)
      = bτ.symm (fun i => w (finSumFinEquiv (Sum.inr i))) := by
  have h := sumBasis_funLeft bσ bτ ((sumBasis bσ bτ).symm w)
  rw [LinearEquiv.apply_symm_apply] at h
  rw [LinearEquiv.eq_symm_apply]
  funext i
  have hi := congrFun h (Sum.inr i)
  simpa using hi.symm

/-- The `j`-th sum-basis homology coordinate of a class pushed forward from the σ-summand: a `finSumFinEquiv∘inl`-weighted sum of the summand coordinates. -/
theorem homologyCoords_sumBasis_map_inlMap {nσ nτ : ℕ} {A B : TopCat}
    (bσ : Cohomology A 1 ≃ₗ[ZMod 2] (Fin nσ → ZMod 2))
    (bτ : Cohomology B 1 ≃ₗ[ZMod 2] (Fin nτ → ZMod 2)) (α : Homology A 1) (j : Fin (nσ + nτ)) :
    homologyCoords (sumBasis bσ bτ) (Homology.map (inlMap A B) 1 α) j
      = ∑ i, (Pi.single j (1 : ZMod 2) : Fin (nσ + nτ) → ZMod 2) (finSumFinEquiv (Sum.inl i))
          * homologyCoords bσ α i := by
  rw [homologyCoords_apply, ← kroneckerH_cohomologyPullback, pullback_inlMap_sumBasis_symm,
    kroneckerH_symm_eq_sum]

/-- The `j`-th sum-basis homology coordinate of a class pushed forward from the τ-summand. -/
theorem homologyCoords_sumBasis_map_inrMap {nσ nτ : ℕ} {A B : TopCat}
    (bσ : Cohomology A 1 ≃ₗ[ZMod 2] (Fin nσ → ZMod 2))
    (bτ : Cohomology B 1 ≃ₗ[ZMod 2] (Fin nτ → ZMod 2)) (β : Homology B 1) (j : Fin (nσ + nτ)) :
    homologyCoords (sumBasis bσ bτ) (Homology.map (inrMap A B) 1 β) j
      = ∑ i, (Pi.single j (1 : ZMod 2) : Fin (nσ + nτ) → ZMod 2) (finSumFinEquiv (Sum.inr i))
          * homologyCoords bτ β i := by
  rw [homologyCoords_apply, ← kroneckerH_cohomologyPullback, pullback_inrMap_sumBasis_symm,
    kroneckerH_symm_eq_sum]

/-- **THE SOURCE-COORDINATE IDENTITY** — the doubling source-inverse coincides with the cylinder
source-inverse after the `Sum.inl`/`finSumFinEquiv` reindex. The UCT-dual of the sum-cohomology basis,
split through the two summand inclusions, IS the reindexed pair of individual UCT-duals. -/
theorem doublingRealizationTied_srcEquiv_symm_eq_cyl (x : Fin (n + n) ⊕ Fin 0 → ZMod 2) :
    (srcEquiv (doublingRealizationTied Y basis Sτ bτ).toData).symm x
      = (srcEquiv (cylRealizationTied Y basis).toData).symm
          (LinearMap.funLeft (ZMod 2) (ZMod 2) finSumFinEquiv
            (LinearMap.funLeft (ZMod 2) (ZMod 2)
              (Sum.inl : Fin (n + n) → Fin (n + n) ⊕ Fin 0) x)) := by
  rw [doublingRealizationTied_srcEquiv_symm, cylRealizationTied_srcEquiv_symm]
  have hcoords : ∀ v : Fin n → ZMod 2,
      homologyCoords basis ((homologyBasisOfCohomologyBasis basis).symm v) = v := fun v => by
    rw [← homologyBasisOfCohomologyBasis_apply]
    exact (homologyBasisOfCohomologyBasis basis).apply_symm_apply v
  refine (homologyBasisOfCohomologyBasis (sumBasis basis basis)).injective ?_
  rw [LinearEquiv.apply_symm_apply, map_add]
  funext j
  rw [Pi.add_apply, homologyBasisOfCohomologyBasis_apply, homologyBasisOfCohomologyBasis_apply,
    homologyCoords_sumBasis_map_inlMap, homologyCoords_sumBasis_map_inrMap, hcoords, hcoords]
  simp only [LinearMap.funLeft_apply]
  have hsum : ∀ (F : Fin (n + n) → ZMod 2),
      (∑ i, F (finSumFinEquiv (Sum.inl i))) + (∑ i, F (finSumFinEquiv (Sum.inr i))) = ∑ m, F m := by
    intro F
    rw [← Equiv.sum_comp finSumFinEquiv F, Fintype.sum_sum_type]
  have hdelta : (∑ m, (Pi.single j (1 : ZMod 2) : Fin (n + n) → ZMod 2) m * x (Sum.inl m))
      = x (Sum.inl j) := by simp [Pi.single_apply]
  show x (Sum.inl j)
    = (∑ i, (fun m => (Pi.single j (1 : ZMod 2) : Fin (n + n) → ZMod 2) m * x (Sum.inl m))
          (finSumFinEquiv (Sum.inl i)))
      + ∑ i, (fun m => (Pi.single j (1 : ZMod 2) : Fin (n + n) → ZMod 2) m * x (Sum.inl m))
          (finSumFinEquiv (Sum.inr i))
  rw [hsum (fun m => (Pi.single j (1 : ZMod 2) : Fin (n + n) → ZMod 2) m * x (Sum.inl m))]
  exact hdelta.symm

/-! ## §4. THE KERNEL IDENTITY — `transportedBInc = negBorBInc`. -/

/-- **THE DOUBLING GEOMETRIC KERNEL IDENTITY.** The transported boundary-inclusion of the doubling
realization is EXACTLY `negBorBInc n` — the fold after de-reindexing, ignoring the empty τ-block.
Combining the geometric reduction (`…_eq_reindex`) with the source-coordinate identity (`…_eq_cyl`)
and the cylinder fold `cylBd`. So the doubling membrane's computed Taylor-leg submodule is the honest
reindexed anti-diagonal `ker (negBorBInc n)`, never a free/synthetic `bInc`. -/
theorem doublingRealizationTied_transportedBInc :
    transportedBInc (doublingRealizationTied Y basis Sτ bτ).toData = negBorBInc n := by
  rw [doublingRealizationTied_transportedBInc_eq_reindex]
  refine LinearMap.ext fun x => ?_
  show cylBd n ((srcEquiv (cylRealizationTied Y basis).toData)
      ((srcEquiv (doublingRealizationTied Y basis Sτ bτ).toData).symm x)) = negBorBInc n x
  rw [doublingRealizationTied_srcEquiv_symm_eq_cyl, LinearEquiv.apply_symm_apply]
  rfl

/-- **The doubling membrane's kernel is the reindexed anti-diagonal** `ker (negBorBInc n)` — the honest
geometric fold-kernel of the `(M,σ̄) ⊔ (M,σ) → ∅` doubling op, read through the DERIVED sum-basis. Never
a free submodule; the synthetic-`bInc` e₈ exploit has no `GeoRealizationTied` source. -/
theorem doublingRealizationTied_toMembrane_L (qσ : Z4Quadratic (Fin (n + n)))
    (qτ : Z4Quadratic (Fin 0)) :
    ((doublingRealizationTied Y basis Sτ bτ).toMembrane qσ qτ).L = LinearMap.ker (negBorBInc n) := by
  show LinearMap.ker (transportedBInc (doublingRealizationTied Y basis Sτ bτ).toData) = _
  rw [doublingRealizationTied_transportedBInc]
  rfl

end SKEFTHawking.PinPlusCharPairNegRealization
