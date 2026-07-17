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
import SKEFTHawking.PinPlusKTSpinSigmaNovikovRealSubstrate

namespace SKEFTHawking.PinPlusKTNovikovTowerInstantiate

open scoped Matrix
open SKEFTHawking
open SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.PinPlusKTSpinSigmaNovikovRealSubstrate
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

/-! ## §3. The substrate's `hadj` field, geometrically realized in `polarBilin` form -/

/-- **The substrate's `NovikovRealPairLES.hadj` field, geometrically realized.** In the exact `polarBilin`
form the substrate consumes:
`polarBilin (Bd.map cast).toQuadraticMap' (coord ι*a) (coord ι*v) = 2 · ⟨δv, a ⌢ [W,∂W]⟩`,
`Bd = interMatrix [∂W] B` (symmetric from `interMatrix_isSymm`). The `polarBilin` of the boundary quadratic
form on the restriction coordinates equals twice the relative Kronecker pairing — precisely the substrate's
`hadj : polarBilin Q (rest2 a) v = pairing a (delta v)` with the geometric `rest2 a = coord(ι*a)` and the
substrate `pairing` absorbing the polarization factor `2` (exactly as `ofLagrangian`'s `pairing` is the
descended `polarBilin`). Proof: `polarBilin_toQuadraticMap'_isSymm` (the factor `2`) then §2's `coord_hadj`.
This is the honest geometric population of `hadj` from the genuine tower — contrast the synthetic
`ofLagrangian`, whose `hadj` holds by the *definition* of its quotient `pairing`. -/
theorem polarBilin_boundary_eq_two_relKroneckerHInt
    (a : LinearMap.ker (coboundaryₗ X 2)) (v : SingularCochainInt X 2)
    (hv : coboundaryₗ X 2 v ∈ relCochainsInt S (2 + 1)) (Z : relCycleLift S (2 + 1 + 1))
    (B : IntH2Basis (sub S)) :
    QuadraticMap.polarBilin
        ((interMatrix (intFundamentalClassOfHomology
            (connectingInt S (2 + 1 + 1) (relCycleToHom S (2 + 1 + 1) Z))) B).map
            (Int.cast : ℤ → ℝ)).toQuadraticMap'
        (coord B (Cohomology.mk (sub S) 2 (restrictCocycleInt a)))
        (coord B (Cohomology.mk (sub S) 2 (restrictLiftCocycleInt v hv)))
      = 2 * ((relKroneckerHInt S (deltaRelHInt v hv)
          (capRelHInt 2 2 (Cohomology.mk X 2 a) (relCycleToHom S (2 + 1 + 1) Z)) : ℤ) : ℝ) := by
  rw [polarBilin_toQuadraticMap'_isSymm _ ((interMatrix_isSymm _ B).map _),
    coord_hadj_eq_relKroneckerHInt]

/-! ## §4. The genuine-tower carrier and the honest reduction to `NovikovRealPairLES`

`NovikovGeometricPairLESData Bd` bundles the ⊗ℝ base-change of an actual bordism `W`'s pair-LES tower —
`rest2` = ι* base-changed, `delta` = the connecting `deltaRelHInt` base-changed, `pairing` = the relative
Kronecker `relKroneckerHInt` base-changed, `hexact` = the `#187` middle exactness `im ι* = ker δ`, and — the
crux — `hadjDot`, the geometric PD-square `⟨ι*a ∪ v, [∂W]⟩ = ⟨a, δv⟩` in the natural dot-product/Kronecker
form (`§3`'s `polarBilin_boundary_eq_two_relKroneckerHInt`, extended `ℝ`-linearly). It is the "genuine
bounding-W tower" the fork `novikov-substrate-synthetic-inhabitation` binds a discharge to exhibit — NOT a
Lagrangian. `ofGeometricPairLESData` REDUCES such a tower to `NovikovRealPairLES Bd` (it does NOT inhabit the
tower — supplying `NovikovGeometricPairLESData` is exactly the residual geometric obligation of a concrete
`W`), genuinely deriving the substrate's `hadj` from `hadjDot` via the polarization factor and scaling
`pairing` to absorb it. Contrast `NovikovRealPairLES.ofLagrangian`, which fabricates the whole tower from the
boundary FORM alone (the synthetic quotient) — kernel-proven zero progress by `novikovLagrangian_iff_hbord`.
-/

open scoped QuadraticMap in
/-- **The genuine ⊗ℝ pair-LES tower carrier of a bounding `W`.** Bundles the base-changed geometric tower:
the restriction `rest2 = ι*`, the connecting `delta = δ`, the relative-Kronecker half-`pairing`, the pair-LES
middle exactness `hexact`, the Kronecker nondegeneracy `hnondeg`, the even-unimodular boundary
nondegeneracy `hbdnd`, boundary symmetry `hsymm`, and the geometric PD-square `hadjDot`
(`⟨ι*a ∪ v, [∂W]⟩ = ⟨a, δv⟩` in dot-product/Kronecker form). Populating this from a concrete `W` is the
residual geometric obligation; here it is the honest INPUT to the reduction (never inhabited synthetically). -/
structure NovikovGeometricPairLESData {n : ℕ} (Bd : Matrix (Fin n) (Fin n) ℤ) where
  /-- `H²(W;ℝ)`. -/
  H2W : Type
  [instAcgW2 : AddCommGroup H2W]
  [instModW2 : Module ℝ H2W]
  /-- `H³(W,∂W;ℝ)`. -/
  H3rel : Type
  [instAcgR3 : AddCommGroup H3rel]
  [instModR3 : Module ℝ H3rel]
  /-- The base-changed restriction `ι* : H²(W;ℝ) → H²(∂W;ℝ) = Fin n → ℝ`. -/
  rest2 : H2W →ₗ[ℝ] (Fin n → ℝ)
  /-- The base-changed connecting map `δ : H²(∂W;ℝ) → H³(W,∂W;ℝ)`. -/
  delta : (Fin n → ℝ) →ₗ[ℝ] H3rel
  /-- The base-changed relative Kronecker half-pairing `H²(W;ℝ) × H³(W,∂W;ℝ) → ℝ`. -/
  pairing : H2W →ₗ[ℝ] H3rel →ₗ[ℝ] ℝ
  /-- Pair-LES middle exactness `im ι* = ker δ` (`#187`). -/
  hexact : Function.Exact rest2 delta
  /-- Kronecker nondegeneracy — the `H²(W)`-family separates `H³(W,∂W)`. -/
  hnondeg : ∀ x : H3rel, (∀ a : H2W, pairing a x = 0) → x = 0
  /-- Boundary-form `ℝ`-nondegeneracy (even-unimodularity, `#190`). -/
  hbdnd : (Bd.map (Int.cast : ℤ → ℝ)).toQuadraticMap'.radical = ⊥
  /-- The boundary intersection matrix is symmetric. -/
  hsymm : Bd.IsSymm
  /-- **The geometric PD-square** `⟨ι*a ∪ v, [∂W]⟩ = ⟨a, δv⟩`, dot-product/Kronecker form (`§3`). -/
  hadjDot : ∀ (a : H2W) (v : Fin n → ℝ),
    rest2 a ⬝ᵥ ((Bd.map (Int.cast : ℤ → ℝ)) *ᵥ v) = pairing a (delta v)

attribute [instance] NovikovGeometricPairLESData.instAcgW2 NovikovGeometricPairLESData.instModW2
  NovikovGeometricPairLESData.instAcgR3 NovikovGeometricPairLESData.instModR3

/-- **The honest reduction: a genuine ⊗ℝ tower BUILDS the substrate.** From
`NovikovGeometricPairLESData Bd` (the base-changed pair-LES tower of an actual bordism `W`) construct
`NovikovRealPairLES Bd`, with the substrate's `pairing := 2 • D.pairing` absorbing the polarization factor,
and `hadj` genuinely DERIVED from the geometric `hadjDot` via `polarBilin_toQuadraticMap'_isSymm` (not
holding by definition of a synthetic quotient). This is the fork-`novikov-substrate-synthetic-inhabitation`
compliant road: the tower data comes from the genuine geometric objects (`§1`/`§2`/`§3` — the real
`capRelHInt`/`deltaRelHInt`/`hadj_integral_core` base-changed), NOT a Lagrangian. -/
noncomputable def NovikovRealPairLES.ofGeometricPairLESData {n : ℕ} {Bd : Matrix (Fin n) (Fin n) ℤ}
    (D : NovikovGeometricPairLESData Bd) :
    NovikovRealPairLES Bd where
  H2W := D.H2W
  H3rel := D.H3rel
  rest2 := D.rest2
  delta := D.delta
  pairing := (2 : ℝ) • D.pairing
  hexact := D.hexact
  hadj := by
    intro a v
    rw [polarBilin_toQuadraticMap'_isSymm _ (D.hsymm.map _), D.hadjDot a v,
      LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]
  hnondeg := by
    intro x hx
    refine D.hnondeg x (fun a => ?_)
    have h2 := hx a
    rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul] at h2
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
  hbdnd := D.hbdnd

/-! ## §5. Which consumers fire — the σ-descent `half`/`lagrangian` and the hcob `latticeSig` sibling -/

/-- **The Novikov `half`/`lagrangian` residual fires from a genuine tower.** A `NovikovGeometricPairLESData
Bd` (the base-changed pair-LES tower of an actual `W`) produces the half-dimensional isotropic Lagrangian of
the boundary form `Bd` — the `NovikovLagrangianAtom` body — via `ofGeometricPairLESData` + the substrate's
DERIVED `NovikovRealPairLES.lagrangian`. The σ-descent's residual half-dim atom, from genuine tower data. -/
theorem NovikovGeometricPairLESData.lagrangian {n : ℕ} {Bd : Matrix (Fin n) (Fin n) ℤ}
    (D : NovikovGeometricPairLESData Bd) :
    ∃ L : Submodule ℝ (Fin n → ℝ),
      n = 2 * Module.finrank ℝ L ∧
      ∀ x ∈ L, (Bd.map (Int.cast : ℤ → ℝ)).toQuadraticMap' x = 0 :=
  (NovikovRealPairLES.ofGeometricPairLESData D).lagrangian

/-- **The hcob-sibling consumer fires: σ is a cobordism invariant, from a genuine tower.** For even-
unimodular ends `A`, `B` and a genuine pair-LES tower on the block form `blockDiag A (−B)` (the ℝ relative-
cohomology data of an orientable cobordism `W`), the lattice signatures agree: `σ(A) = σ(B)`. Routed through
`ofGeometricPairLESData` + `latticeSig_eq_of_realPairLES`. The shared σ-lane-floor / dA-leaf engine, now fed
by the genuine tower rather than a synthetic Lagrangian. -/
theorem NovikovGeometricPairLESData.latticeSig_eq {r s : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (B : Matrix (Fin s) (Fin s) ℤ) (hA : IsEvenUnimodular A) (hB : IsEvenUnimodular B)
    (D : NovikovGeometricPairLESData (blockDiag A (-B))) :
    latticeSig A = latticeSig B :=
  latticeSig_eq_of_realPairLES A B hA hB (NovikovRealPairLES.ofGeometricPairLESData D)

end SKEFTHawking.PinPlusKTNovikovTowerInstantiate
