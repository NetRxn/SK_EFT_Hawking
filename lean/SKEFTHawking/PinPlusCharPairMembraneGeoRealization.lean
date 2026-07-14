/-
# Phase 5q.H (W-A Round 4) — THE GEOMETRIC-REALIZATION SEAM for `GeoMembrane.bInc`.

The membrane tie (`PinPlusCharPairMembraneTie`) COMPUTES the Taylor-leg submodule `L` as
`LinearMap.ker mem.bInc` of a `GeoMembrane` datum, killing the free-`L` exploit
(`free-membrane-kernel-kills-nonsplit`). Its module docstring flags ONE remaining structural
obligation: the *geometric realization* of `bInc` by an actual membrane `Q` whose boundary
`∂Q = Σ_σ ⊔ Σ_τ` is two closed surfaces, transported through the enhancement bases.

This module discharges the **algebraic transport half** of that obligation — the seam that a genuine
compact-T2 3-manifold-with-boundary realization plugs into. Given the substrate data:

* a boundary object `∂Q` (a `TopCat`) presented as a clopen split `Σ_σ ⊔ Σ_τ` (`U`/`Uᶜ`);
* the ambient membrane `Q` and the boundary inclusion `ι : ∂Q → Q` (a `ContinuousMap`);
* the `H₁` enhancement bases `eσ : H₁(Σ_σ) ≃ (Fin nσ → ℤ/2)`, `eτ : H₁(Σ_τ) ≃ (Fin nτ → ℤ/2)`,
  `eQ : H₁(Q) ≃ (Fin mid → ℤ/2)`,

we build the **transported boundary-inclusion** `transportedBInc : (Fin nσ ⊕ Fin nτ → ℤ/2) →ₗ
(Fin mid → ℤ/2)` — precisely the map `H₁(∂Q) → H₁(Q)` of the substrate (`Homology.map ι 1`)
read through the bases — using the degree-general ⊔-additivity `SingularDisjointUnionHn.splitHnEquiv`
to split `H₁(∂Q) ≅ H₁(Σ_σ) × H₁(Σ_τ)`. The **kernel-correspondence** theorem `transportedBInc_ker`
states exactly what the tie needs: the transported map's kernel is the image, under the composite
basis equiv, of `ker(H₁(∂Q) → H₁(Q))` — so `GeoMembrane.ofGeometric`'s `L` is a genuine geometric
fold-kernel, never a free field.

DIMENSION DISCIPLINE: `Q` is a 3-dim membrane, the `Σ`'s are 2-dim closed surfaces, all homology is
the project's mod-2 singular substrate; nothing here drops the T2 hypotheses (they live in the
eventual realization of the abstract `TopCat`s). NEGATIVE FRONTIER respected: `L` stays a COMPUTED
kernel (`free-membrane-kernel-kills-nonsplit`), never a free `Submodule` field.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.SingularDisjointUnionHn
import SKEFTHawking.PinPlusCharPairMembraneTie

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularDisjointUnion
open SKEFTHawking.SingularDisjointUnionHn
open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic
open SKEFTHawking.PinPlusCharPairMembraneTie

namespace SKEFTHawking.PinPlusCharPairMembraneGeoRealization

/-! ## §1. The geometric-realization datum -/

/-- **The substrate data a geometric membrane realization supplies.** `bdry` is the boundary object
`∂Q`, presented as a clopen split `Σ_σ ⊔ Σ_τ` via `U`/`Uᶜ`; `Q` is the ambient 3-dim membrane; `ι` is
the boundary inclusion `∂Q → Q`; and `eσ`/`eτ`/`eQ` are the `H₁` enhancement bases. The abstract
`TopCat`s stand for the eventual compact-T2 manifolds (whose realization is the wt3
rel-Lefschetz/PD obligation); what is kernel-checked here is the algebraic transport. -/
structure GeoRealizationData (nσ nτ mid : ℕ) where
  /-- the boundary object `∂Q`. -/
  bdry : TopCat
  /-- the ambient membrane `Q`. -/
  Q : TopCat
  /-- the clopen set splitting `∂Q = Σ_σ ⊔ Σ_τ`; `Σ_σ = sub U`, `Σ_τ = sub Uᶜ`. -/
  U : Set ↑bdry
  /-- the split is clopen (two disjoint closed surfaces). -/
  hU : IsClopen U
  /-- the boundary inclusion `∂Q ↪ Q`. -/
  ι : C(↑bdry, ↑Q)
  /-- `H₁(Σ_σ)` enhancement basis. -/
  eσ : Homology (sub U) 1 ≃ₗ[ZMod 2] (Fin nσ → ZMod 2)
  /-- `H₁(Σ_τ)` enhancement basis. -/
  eτ : Homology (sub Uᶜ) 1 ≃ₗ[ZMod 2] (Fin nτ → ZMod 2)
  /-- `H₁(Q)` enhancement basis. -/
  eQ : Homology Q 1 ≃ₗ[ZMod 2] (Fin mid → ZMod 2)

variable {nσ nτ mid : ℕ}

/-- **The composite basis equivalence** `H₁(∂Q) ≃ (Fin nσ ⊕ Fin nτ → ℤ/2)`: split `H₁(∂Q)` across the
clopen partition (degree-1 ⊔-additivity `splitHnEquiv`), transport each summand through its
enhancement (`eσ`, `eτ`), then repackage the product as a sum-indexed function
(`sumArrowLequivProdArrow`). This is "the basis equivs" the kernel-correspondence refers to. -/
noncomputable def srcEquiv (d : GeoRealizationData nσ nτ mid) :
    Homology d.bdry 1 ≃ₗ[ZMod 2] (Fin nσ ⊕ Fin nτ → ZMod 2) :=
  (splitHnEquiv d.hU 1).symm.trans
    ((LinearEquiv.prodCongr d.eσ d.eτ).trans
      (LinearEquiv.sumArrowLequivProdArrow (Fin nσ) (Fin nτ) (ZMod 2) (ZMod 2)).symm)

/-- **The transported boundary-inclusion** `(Fin nσ ⊕ Fin nτ → ℤ/2) →ₗ (Fin mid → ℤ/2)` — the
substrate map `H₁(∂Q) → H₁(Q)` (`Homology.map ι 1`) read through the source basis `srcEquiv` and the
target basis `eQ`. This is the concrete map `GeoMembrane.bInc` becomes under a geometric realization. -/
noncomputable def transportedBInc (d : GeoRealizationData nσ nτ mid) :
    (Fin nσ ⊕ Fin nτ → ZMod 2) →ₗ[ZMod 2] (Fin mid → ZMod 2) :=
  d.eQ.toLinearMap ∘ₗ (Homology.map d.ι 1) ∘ₗ (srcEquiv d).symm.toLinearMap

/-- **THE KERNEL-CORRESPONDENCE.** The transported map's kernel is the image, under the composite
basis equiv `srcEquiv`, of `ker(H₁(∂Q) → H₁(Q))`. So the Taylor-leg submodule
`(GeoMembrane.ofGeometric …).L = ker (transportedBInc d)` is genuinely the basis image of a geometric
boundary-inclusion kernel — never a free field. Pure transport: post-composition by the equiv `eQ`
leaves the kernel (`LinearEquiv.ker_comp`), and pre-composition by `srcEquiv.symm` conjugates the
kernel to `map srcEquiv (·)` (`LinearMap.ker_comp` + `comap_equiv_eq_map_symm`). -/
theorem transportedBInc_ker (d : GeoRealizationData nσ nτ mid) :
    LinearMap.ker (transportedBInc d)
      = Submodule.map (srcEquiv d).toLinearMap (LinearMap.ker (Homology.map d.ι 1)) := by
  rw [transportedBInc, LinearEquiv.ker_comp, LinearMap.ker_comp,
    Submodule.comap_equiv_eq_map_symm, LinearEquiv.symm_symm]

/-! ## §2. The `GeoMembrane` constructor -/

/-- **`GeoMembrane.ofGeometric`** — assemble a `GeoMembrane` from a geometric-realization datum. Its
`bInc` is the transported boundary-inclusion, so its computed Taylor-leg submodule
`L = ker (transportedBInc d)` is the basis image of the geometric kernel `ker(H₁(∂Q) → H₁(Q))`
(`ofGeometric_L`). The quadratic forms `qσ`, `qτ` are phantom rank parameters; `bInc` is
enhancement-agnostic (index-rank data only), matching `GeoMembrane`'s design. -/
noncomputable def GeoMembrane.ofGeometric (qσ : Z4Quadratic (Fin nσ)) (qτ : Z4Quadratic (Fin nτ))
    (d : GeoRealizationData nσ nτ mid) :
    SKEFTHawking.PinPlusCharPairMembraneTie.GeoMembrane qσ qτ :=
  ⟨mid, transportedBInc d⟩

/-- The constructed membrane's `L` is the basis image of the geometric boundary-inclusion kernel —
the honest "`L = ker(H₁∂ → H₁Q)`" the design demanded, discharged through the transport seam. -/
theorem GeoMembrane.ofGeometric_L (qσ : Z4Quadratic (Fin nσ)) (qτ : Z4Quadratic (Fin nτ))
    (d : GeoRealizationData nσ nτ mid) :
    (GeoMembrane.ofGeometric qσ qτ d).L
      = Submodule.map (srcEquiv d).toLinearMap (LinearMap.ker (Homology.map d.ι 1)) :=
  transportedBInc_ker d

end SKEFTHawking.PinPlusCharPairMembraneGeoRealization
