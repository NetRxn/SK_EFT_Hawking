import Mathlib
import SKEFTHawking.SingularKroneckerEquiv
import SKEFTHawking.SingularSubHomologyMV

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD6f-c4-L1b) — the absolute cohomology MV connecting `absCohomConn`

The Poincaré-duality `5`-lemma's connecting square pairs the **homology** MV connecting `subHomConnecting`
(`= seamI ∘ mvDelta`, the bottom row) against cohomology. By universal coefficients over `ℤ/2` the
absolute Kronecker pairing is a **perfect pairing** (`SingularKroneckerEquiv.kroneckerHEquiv`), so the
homology connecting dualises to an **absolute cohomology MV connecting**
  `absCohomConn : Hᵖ⁺¹(sub(U∩V)) → Hᵖ⁺²(sub(U∪V))`,
built exactly as `SingularRelativeCohomologyMVConnecting.relCohomMvConnecting` is built from `relMvDelta`
(the `dualMap`-conjugate through the Kronecker iso — no contravariant excision, no finite-dimensionality).
Its **defining adjunction** `⟨absCohomConn a', w⟩ = ⟨a', subHomConnecting w⟩` is the kronecker-naturality
that moves the cohomology argument `a'` of the LHS connecting-square pairing through the homology
connecting — the LHS analogue of the RHS's `relKroneckerH_relCohomMvConnecting`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularSubsetHomology
  SKEFTHawking.SingularKroneckerEquiv SKEFTHawking.SingularSubHomologyMV

namespace SKEFTHawking.SingularSubHomologyMVCohomConn

variable {X : TopCat}

/-- **The absolute cohomology MV connecting** `absCohomConn : Hᵖ⁺¹(sub(U∩V)) → Hᵖ⁺²(sub(U∪V))`, the
`dualMap`-conjugate of the homology MV connecting `subHomConnecting` through the perfect Kronecker pairing
`kroneckerHEquiv` (over `ℤ/2`). Mirror of `relCohomMvConnecting`. -/
noncomputable def absCohomConn (U V : Set ↑X) (hU : IsOpen U) (hV : IsOpen V) (p : ℕ) :
    Cohomology (sub (U ∩ V)) (p + 1) →ₗ[ZMod 2] Cohomology (sub (U ∪ V)) (p + 2) :=
  (kroneckerHEquiv (X := sub (U ∪ V)) (p + 1)).symm.toLinearMap ∘ₗ
    (subHomConnecting U V hU hV (p + 1)).dualMap ∘ₗ
    (kroneckerHEquiv (X := sub (U ∩ V)) p).toLinearMap

/-- **The defining adjunction of `absCohomConn`**: `⟨absCohomConn a', w⟩_{sub(U∪V)} = ⟨a', subHomConnecting
w⟩_{sub(U∩V)}`. The sole interface used downstream (the LHS leg of the PD connecting-square match). -/
theorem kroneckerH_absCohomConn (U V : Set ↑X) (hU : IsOpen U) (hV : IsOpen V) (p : ℕ)
    (a' : Cohomology (sub (U ∩ V)) (p + 1)) (w : Homology (sub (U ∪ V)) (p + 2)) :
    kroneckerH (X := sub (U ∪ V)) (p + 2) (absCohomConn U V hU hV p a') w
      = kroneckerH (X := sub (U ∩ V)) (p + 1) a' (subHomConnecting U V hU hV (p + 1) w) := by
  rw [absCohomConn, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_coe, kroneckerH_symm, LinearMap.dualMap_apply, kroneckerHEquiv_apply]

end SKEFTHawking.SingularSubHomologyMVCohomConn
