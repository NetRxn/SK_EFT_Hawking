/-
# Phase 5q.H close-out (#196) — THE NovikovRealPairLES GEOMETRIC INSTANTIATION (⊗ℝ layer, part 2)

The genuine bounding-`W` tower road for the σ-descent's last atom, discharging the fork
`novikov-substrate-synthetic-inhabitation` (KernelNoGos #20) the HONEST way: the substrate's fields are
supplied by the genuine integral geometric objects — the relative cap `capRelHInt`, the connecting map
`deltaRelHInt`, the restriction `ι*`, the relative Kronecker `relKroneckerHInt`, and the PD-square
`hadj_integral_core` — base-changed to ℝ, **NOT** by a linear-algebra Lagrangian / synthetic quotient
(the refuted `ofLagrangian` route, kernel-proven zero progress via `novikovLagrangian_iff_hbord`).

## §1 — the geometric `hadj`, at the class level (the "named wall", DISCHARGED)

`#190`'s tower-bridge docstring escalated the substrate's PD-intertwining
`hadj : ⟨ι*a ∪ v, [∂W]⟩ = ⟨a, δv⟩` as a "named wall" — the cup-vs-Kronecker mediation of the pair
`(W, ∂W)` that was "NOT in-tree". It is now in-tree: `#192`'s `hadj_integral_core`
(`⟨ι*v, (ι*a) ⌢ [∂W]⟩ = ⟨δv, a ⌢ [W,∂W]⟩`) composed with the closed-boundary cup-cap adjunction
`interFormInt_eq_kroneckerHInt_capHInt` (`⟨a ∪ b, [∂W]⟩ = ⟨b, a ⌢ [∂W]⟩`) yields the geometric `hadj`
directly in the boundary intersection-form language:

  `interFormInt [∂W] (ι*a) (ι*v) = relKroneckerHInt (δv) (a ⌢ [W,∂W])`   (`interFormInt_boundary_eq_relKroneckerHInt`),

where `[∂W] = ∂[W,∂W] = connectingInt (relCycleToHom Z)` is the geometric boundary fundamental class of the
tethered relative cycle `Z`. This is the FULL discharge of the wall — the boundary form on the LHS is now the
genuine `interFormInt` of the boundary manifold, coupled to the pair connecting map on the RHS.

## §2 — the ⊗ℝ coordinate `hadj` (basis-repr-direct)

Base-changing §1 through the `#196` FORM layer (`SingularRelativeRealBaseChange.interFormInt_eq_matrix_
dotProduct_repr`) puts the LHS in the substrate's coordinate language: for the boundary basis `B` (the
`#190` disclosed `IntH2Basis (sub S)` datum carrying `interFormInt` to `Bd`), the `ℝ`-cast geometric `hadj`
is `coord(ι*a) ⬝ᵥ (interMatrix [∂W] B).map cast *ᵥ coord(ι*v) = (relKroneckerHInt (δv)(a ⌢ [W,∂W]) : ℝ)` —
exactly the shape the substrate's `hadj` field consumes, its LHS the boundary Gram form on `Fin n → ℝ`.

The remaining wiring to a full `NovikovRealPairLES` instance — the finite-free-basis coordinatization of the
whole tower (`rest2`/`delta`/`pairing` as base-changed maps between the coordinate spaces `H²(W;ℝ)`,
`H²(∂W;ℝ) = Fin n → ℝ`, `H³(W,∂W;ℝ)`) and the relative-UCT ℝ-nondegeneracy (`hnondeg`) — is the residual
geometric datum of the bounding `W`, named precisely in §3 (the honest-reduction pattern). This module lands
the FORM/`hadj` girder of that instantiation, not the full coordinate glue.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
new `axiom`.
-/
import Mathlib
import SKEFTHawking.SingularRelativeCapHadjInt
import SKEFTHawking.SingularRelativeRealBaseChange
import SKEFTHawking.IntCapProductInt

namespace SKEFTHawking.PinPlusKTNovikovTowerInstantiate

open scoped Matrix
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularRelativeUCInt
open SKEFTHawking.SingularRelativeCohomDeltaInt
open SKEFTHawking.SingularRelativeCapHomologyInt
open SKEFTHawking.SingularRelativeCapConnectingInt
open SKEFTHawking.SingularRelativeCapHadjInt
open SKEFTHawking.SingularRelativeRealBaseChange
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)

variable {X : TopCat} {S : Set X}

/-! ## §1. The geometric `hadj` at the class level — the named cup-vs-Kronecker wall, DISCHARGED -/

/-- **The geometric PD-intertwining `hadj`, in boundary intersection-form language.**
`interFormInt [∂W] (ι*a) (ι*v) = ⟨δv, a ⌢ [W,∂W]⟩`. The LHS is the genuine integral intersection form of the
boundary manifold `∂W` (fundamental class `[∂W] = ∂[W,∂W] = connectingInt (relCycleToHom Z)`) evaluated on
the restrictions `ι*a, ι*v`; the RHS is the relative Kronecker pairing of the pair connecting map `δv`
against the relative cap `a ⌢ [W,∂W]`. Proof: the closed-boundary cup-cap adjunction
`interFormInt_eq_kroneckerHInt_capHInt` rewrites the LHS form as `⟨ι*v, (ι*a) ⌢ [∂W]⟩`, then
`hadj_integral_core` (`#192`) converts that to the RHS. This is the in-tree discharge of the
`#190` "named wall" — the substrate's `hadj` field, geometrically grounded. -/
theorem interFormInt_boundary_eq_relKroneckerHInt
    (a : LinearMap.ker (coboundaryₗ X 2)) (v : SingularCochainInt X 2)
    (hv : coboundaryₗ X 2 v ∈ relCochainsInt S (2 + 1)) (Z : relCycleLift S (2 + 1 + 1)) :
    interFormInt
        (intFundamentalClassOfHomology
          (connectingInt S (2 + 1 + 1) (relCycleToHom S (2 + 1 + 1) Z)))
        (Cohomology.mk (sub S) 2 (restrictCocycleInt a))
        (Cohomology.mk (sub S) 2 (restrictLiftCocycleInt v hv))
      = relKroneckerHInt S (deltaRelHInt v hv)
          (capRelHInt 2 2 (Cohomology.mk X 2 a) (relCycleToHom S (2 + 1 + 1) Z)) := by
  rw [interFormInt_eq_kroneckerHInt_capHInt]
  exact hadj_integral_core a v hv Z

/-! ## §2. The ⊗ℝ coordinate `hadj` — the substrate's `hadj`-field shape (basis-repr-direct) -/

/-- **The geometric `hadj`, in the substrate's ℝ coordinate language.** For a disclosed finite free basis
`B` of `H²(∂W;ℤ)` (the `#190`/`#164` datum carrying `interFormInt` to `Bd = interMatrix [∂W] B`), the
boundary Gram form on the real coordinate vectors of the restrictions equals the `ℝ`-cast relative Kronecker
pairing:
`coord(ι*a) ⬝ᵥ (interMatrix [∂W] B).map cast *ᵥ coord(ι*v) = ⟨δv, a ⌢ [W,∂W]⟩`.
This is exactly the LHS shape of `NovikovRealPairLES.hadj` (`polarBilin (Bd.map cast).toQuadraticMap'` up to
the polarization factor of `polarBilin_toQuadraticMap'_isSymm`), its RHS the substrate's `pairing a (delta
v)` — the ⊗ℝ base-change of the geometric `hadj` (§1) through the `#196` FORM layer. -/
theorem coord_hadj_eq_relKroneckerHInt
    (a : LinearMap.ker (coboundaryₗ X 2)) (v : SingularCochainInt X 2)
    (hv : coboundaryₗ X 2 v ∈ relCochainsInt S (2 + 1)) (Z : relCycleLift S (2 + 1 + 1))
    (B : IntH2Basis (sub S)) :
    coord B (Cohomology.mk (sub S) 2 (restrictCocycleInt a)) ⬝ᵥ
        (((interMatrix
            (intFundamentalClassOfHomology
              (connectingInt S (2 + 1 + 1) (relCycleToHom S (2 + 1 + 1) Z))) B).map
              (Int.cast : ℤ → ℝ)) *ᵥ coord B (Cohomology.mk (sub S) 2 (restrictLiftCocycleInt v hv)))
      = ((relKroneckerHInt S (deltaRelHInt v hv)
          (capRelHInt 2 2 (Cohomology.mk X 2 a) (relCycleToHom S (2 + 1 + 1) Z)) : ℤ) : ℝ) := by
  rw [← interFormInt_eq_matrix_dotProduct_repr, interFormInt_boundary_eq_relKroneckerHInt]

end SKEFTHawking.PinPlusKTNovikovTowerInstantiate
