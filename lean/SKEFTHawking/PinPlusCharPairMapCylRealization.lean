/-
# Phase 5q.H (W-A arm 4) — STAGE 3c support: THE TWISTED-CYLINDER REALIZATION.

`PinPlusCharPairCylRealization` built the honest reflexive cylinder realization `cylRealizationTied`
(`transportedBInc = cylBd`). This module generalizes it to the **twisted cylinder** — the cylinder
`Q = Y × [0,1]` whose σ-end (bottom slice) IS the surface `Y` (basis `bσ`), but whose τ-end (top slice)
is identified with a DIFFERENT closed surface `Sτ` (basis `bτ`) through a homeomorphism `h : Sτ ≃ₜ Y`.

Its transported boundary-inclusion is the fold `cylBd` twisted by the h-induced homology basis change:
`transportedBInc = x ↦ (i ↦ x(inl i) + T_h(x∘inr)(i))` where
`T_h := (homologyBasisOfCohomologyBasis bσ) ∘ homeoHomologyEquiv h ∘ (homologyBasisOfCohomologyBasis bτ).symm`
is the transport of bτ-coordinates to bσ-coordinates along h (`mapCylRealizationTied_transportedBInc`).

The master naturality lemma `transportBasisChange_eq_funLeft` turns `T_h` into an algebraic index-reindex
`funLeft e` whenever the two carried bases are `h`-compatible on the standard covectors
(`cohomologyPullback ⟨h⟩ (bσ.symm δᵢ) = bτ.symm δ_{e i}`). This is what lets the twisted cylinder realize
`unitBor`/`commBor`/`assocBor` (each a `mapCylinder` of a diffeomorphism: sumEmpty / sumComm / sumAssoc).

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
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderNumerics
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspension
open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic
open SKEFTHawking.PinPlusCharPairData (cylBd cylLagrangian)
open SKEFTHawking.PinPlusCharPairMembraneGeoRealization
open SKEFTHawking.PinPlusCharPairRealizationTied
open SKEFTHawking.PinPlusCharPairCylRealization

namespace SKEFTHawking.PinPlusCharPairMapCylRealization

variable {nσ nτ : ℕ} (Y : TopCat) [T2Space (Y : Type)] [CompactSpace (Y : Type)]
  (bσ : Cohomology Y 1 ≃ₗ[ZMod 2] (Fin nσ → ZMod 2))
  (Sτ : TopCat) (bτ : Cohomology Sτ 1 ≃ₗ[ZMod 2] (Fin nτ → ZMod 2))
  (h : (Sτ : Type) ≃ₜ (Y : Type))

/-- **THE TWISTED-CYLINDER REALIZATION** — the cylinder `Q = Y × [0,1]` as a `GeoRealizationTied` for the
end pair `(Y, Sτ)`: the σ-end is the bottom slice `Y` (identity, basis `bσ`); the τ-end is the top slice,
identified with `Sτ` through `h : Sτ ≃ₜ Y` (basis `bτ`). Same geometry as `cylRealizationTied`; the τ-end
homeomorphism is post-composed with `h.symm` to retarget the boundary component onto `Sτ`. -/
noncomputable def mapCylRealizationTied : GeoRealizationTied Y Sτ bσ bτ where
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
  homτ := ((Homeomorph.setCongr Set.compl_range_inl).trans
    IsClosedEmbedding.inr.isEmbedding.toHomeomorph.symm).trans h.symm
  mid := nσ
  eQ := (prodContractibleHomologyEquiv Y (TopCat.of unitInterval) ⊥ iccContraction
      slice_iccContraction_zero slice_iccContraction_one 0).trans
    (homologyBasisOfCohomologyBasis bσ)

/-- **The h-induced homology basis change** `(Fin nτ → ℤ/2) →ₗ (Fin nσ → ℤ/2)` — read a `bτ`-coordinate
vector as an `H₁(Sτ)` class, transport it to `H₁(Y)` along `h`, read in `bσ`-coordinates. This is the
`T_h` the twisted cylinder's τ-end contributes to the fold. -/
noncomputable def transportBasisChange :
    (Fin nτ → ZMod 2) →ₗ[ZMod 2] (Fin nσ → ZMod 2) :=
  (homologyBasisOfCohomologyBasis bσ).toLinearMap ∘ₗ (homeoHomologyEquiv h 1).toLinearMap ∘ₗ
    (homologyBasisOfCohomologyBasis bτ).symm.toLinearMap

/-- **The twisted fold** `x ↦ (i ↦ x(inl i) + T(x∘inr)(i))` — the cylinder fold `cylBd` with the τ-block
transported by `T`. -/
def mapCylBd (T : (Fin nτ → ZMod 2) →ₗ[ZMod 2] (Fin nσ → ZMod 2)) :
    (Fin nσ ⊕ Fin nτ → ZMod 2) →ₗ[ZMod 2] (Fin nσ → ZMod 2) where
  toFun x := fun i => x (Sum.inl i) + T (fun j => x (Sum.inr j)) i
  map_add' a b := by
    funext i
    show (a + b) (Sum.inl i) + T (fun j => (a + b) (Sum.inr j)) i
      = (a (Sum.inl i) + T (fun j => a (Sum.inr j)) i)
        + (b (Sum.inl i) + T (fun j => b (Sum.inr j)) i)
    rw [show (fun j => (a + b) (Sum.inr j)) = (fun j => a (Sum.inr j)) + (fun j => b (Sum.inr j))
      from rfl, map_add]
    simp only [Pi.add_apply]
    ring
  map_smul' c a := by
    funext i
    show (c • a) (Sum.inl i) + T (fun j => (c • a) (Sum.inr j)) i
      = (c • fun i => a (Sum.inl i) + T (fun j => a (Sum.inr j)) i) i
    rw [show (fun j => (c • a) (Sum.inr j)) = c • (fun j => a (Sum.inr j)) from rfl, map_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- Functoriality of the homeomorphism-induced homology equivalence over a composition. -/
theorem homeoHomologyEquiv_trans {X Y Z : TopCat} (f : (X : Type) ≃ₜ (Y : Type))
    (g : (Y : Type) ≃ₜ (Z : Type)) (n : ℕ) (z : Homology X n) :
    homeoHomologyEquiv (f.trans g) n z = homeoHomologyEquiv g n (homeoHomologyEquiv f n z) := by
  show Homology.map ⟨f.trans g, (f.trans g).continuous⟩ n z
    = Homology.map ⟨g, g.continuous⟩ n (Homology.map ⟨f, f.continuous⟩ n z)
  rw [← LinearMap.comp_apply, ← Homology.map_comp]
  rfl

/-- `homeoHomologyEquiv`'s inverse is the induced map of the reverse homeomorphism (as an equiv). -/
theorem homeoHomologyEquiv_symm {X Z : TopCat} (g : (X : Type) ≃ₜ (Z : Type)) (n : ℕ) :
    (homeoHomologyEquiv g n).symm = homeoHomologyEquiv g.symm n := by
  ext y; rw [homeoHomologyEquiv_symm_apply]; rfl

/-- **The twisted τ-boundary basis inverse routes through the untwisted cylinder's τ-basis inverse
after the `T_h` transport** — the geometric core of the reduction to `cylRealizationTied`. -/
theorem mapCyl_eτ_symm (v : Fin nτ → ZMod 2) :
    (mapCylRealizationTied Y bσ Sτ bτ h).toData.eτ.symm v
      = (cylRealizationTied Y bσ).toData.eτ.symm (transportBasisChange Y bσ Sτ bτ h v) := by
  have hbσ : (homologyBasisOfCohomologyBasis bσ).symm (transportBasisChange Y bσ Sτ bτ h v)
      = homeoHomologyEquiv h 1 ((homologyBasisOfCohomologyBasis bτ).symm v) := by
    rw [transportBasisChange, LinearMap.comp_apply, LinearMap.comp_apply]
    simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [GeoRealizationTied.toData_eτ, GeoRealizationTied.toData_eτ, LinearEquiv.symm_apply_eq,
    show (mapCylRealizationTied Y bσ Sτ bτ h).homτ
      = (cylRealizationTied Y bσ).homτ.trans h.symm from rfl]
  show v = homologyBasisOfCohomologyBasis bτ (homeoHomologyEquiv
      ((cylRealizationTied Y bσ).homτ.trans h.symm) 1
      ((homeoHomologyEquiv (cylRealizationTied Y bσ).homτ 1).symm
        ((homologyBasisOfCohomologyBasis bσ).symm ((transportBasisChange Y bσ Sτ bτ h) v))))
  rw [hbσ, homeoHomologyEquiv_trans, LinearEquiv.apply_symm_apply, ← homeoHomologyEquiv_symm,
    LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

theorem mapCylRealizationTied_transportedBInc :
    transportedBInc (mapCylRealizationTied Y bσ Sτ bτ h).toData
      = mapCylBd (transportBasisChange Y bσ Sτ bτ h) := by
  refine LinearMap.ext fun x => ?_
  have hsrc : (srcEquiv (mapCylRealizationTied Y bσ Sτ bτ h).toData).symm x
      = (srcEquiv (cylRealizationTied Y bσ).toData).symm
          (Sum.elim (fun i => x (Sum.inl i))
            (transportBasisChange Y bσ Sτ bτ h (fun j => x (Sum.inr j)))) := by
    rw [srcEquiv_symm_apply, srcEquiv_symm_apply, mapCyl_eτ_symm]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rfl
  have hcyl := LinearMap.congr_fun (cylRealizationTied_transportedBInc Y bσ)
    (Sum.elim (fun i => x (Sum.inl i))
      (transportBasisChange Y bσ Sτ bτ h (fun j => x (Sum.inr j))))
  have key : transportedBInc (mapCylRealizationTied Y bσ Sτ bτ h).toData x
      = transportedBInc (cylRealizationTied Y bσ).toData
          (Sum.elim (fun i => x (Sum.inl i))
            (transportBasisChange Y bσ Sτ bτ h (fun j => x (Sum.inr j)))) := by
    show (mapCylRealizationTied Y bσ Sτ bτ h).toData.eQ
        (Homology.map (mapCylRealizationTied Y bσ Sτ bτ h).toData.ι 1
          ((srcEquiv (mapCylRealizationTied Y bσ Sτ bτ h).toData).symm x))
      = (cylRealizationTied Y bσ).toData.eQ
        (Homology.map (cylRealizationTied Y bσ).toData.ι 1
          ((srcEquiv (cylRealizationTied Y bσ).toData).symm
            (Sum.elim (fun i => x (Sum.inl i))
              (transportBasisChange Y bσ Sτ bτ h (fun j => x (Sum.inr j))))))
    rw [hsrc]
    rfl
  rw [key, hcyl]
  funext i
  show (fun i => x (Sum.inl i)) i + transportBasisChange Y bσ Sτ bτ h (fun j => x (Sum.inr j)) i
    = x (Sum.inl i) + transportBasisChange Y bσ Sτ bτ h (fun j => x (Sum.inr j)) i
  rfl

omit [T2Space (Y : Type)] [CompactSpace (Y : Type)] in
/-- **MASTER NATURALITY** — the h-induced homology basis change `T_h` IS the algebraic index-reindex
`funLeft e` whenever the two carried bases are `h`-compatible on the standard covectors:
`cohomologyPullback ⟨h⟩ (bσ.symm δᵢ) = bτ.symm δ_{e i}`. This is the Kronecker-adjunction bridge that
turns geometric transport into the tied ops' index algebra. -/
theorem transportBasisChange_eq_funLeft (e : Fin nσ → Fin nτ)
    (hcompat : ∀ i, cohomologyPullback ⟨h, h.continuous⟩ 1 (bσ.symm (Pi.single i 1))
      = bτ.symm (Pi.single (e i) 1)) :
    transportBasisChange Y bσ Sτ bτ h = LinearMap.funLeft (ZMod 2) (ZMod 2) e := by
  refine LinearMap.ext fun v => ?_
  funext i
  show homologyCoords bσ (homeoHomologyEquiv h 1 ((homologyBasisOfCohomologyBasis bτ).symm v)) i
    = v (e i)
  rw [homologyCoords_apply, homeoHomologyEquiv_apply, ← kroneckerH_cohomologyPullback, hcompat]
  show homologyCoords bτ ((homologyBasisOfCohomologyBasis bτ).symm v) (e i) = v (e i)
  rw [← homologyBasisOfCohomologyBasis_apply, LinearEquiv.apply_symm_apply]

/-- **The twisted fold's kernel is a reindex graph** — for a bijective reindex `e`, the twisted
cylinder's computed kernel `ker (mapCylBd (funLeft e))` is exactly `graphSub (funCongrLeft e.symm)`, the
reparametrized-cylinder membrane kernel the tied `unitBor`/`commBor`/`assocBor` ops consume. -/
theorem ker_mapCylBd_funLeft {nσ nτ : ℕ} (e : Fin nσ ≃ Fin nτ) :
    LinearMap.ker (mapCylBd (LinearMap.funLeft (ZMod 2) (ZMod 2) (e : Fin nσ → Fin nτ)))
      = SKEFTHawking.PinPlusCharPairData.graphSub
          (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) e.symm) := by
  have hval : ∀ (x : Fin nσ ⊕ Fin nτ → ZMod 2) (i : Fin nσ),
      (mapCylBd (LinearMap.funLeft (ZMod 2) (ZMod 2) (e : Fin nσ → Fin nτ))) x i
        = x (Sum.inl i) + x (Sum.inr (e i)) := fun x i => by
    show x (Sum.inl i) + (LinearMap.funLeft (ZMod 2) (ZMod 2) (e : Fin nσ → Fin nτ))
      (fun j => x (Sum.inr j)) i = _
    rw [LinearMap.funLeft_apply]
  ext x
  rw [LinearMap.mem_ker, SKEFTHawking.PinPlusCharPairData.mem_graphSub]
  constructor
  · intro hk
    funext j
    show x (Sum.inr j) = (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) e.symm)
      (fun i => x (Sum.inl i)) j
    rw [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
    have hi := congrFun hk (e.symm j)
    rw [hval, Equiv.apply_symm_apply] at hi
    have h2 : x (Sum.inr j) = - x (Sum.inl (e.symm j)) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact hi
    rwa [CharTwo.neg_eq] at h2
  · intro hg
    funext i
    rw [hval]
    have hj := congrFun hg (e i)
    rw [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, Equiv.symm_apply_apply] at hj
    rw [show x (Sum.inr (e i)) = x (Sum.inl i) from hj]
    rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul, Pi.zero_apply]

end SKEFTHawking.PinPlusCharPairMapCylRealization
