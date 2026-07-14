/-
# Phase 5q.H W-A arm 4 — the CONCRETE-CYLINDER residual-set, machine-readable in ONE place

The stretch payoff (spec item 3): a `WAdmPinned`-shaped consolidation of the ENTIRE
W-admissibility residual-set for the concrete reflexive cylinder `W = M × [0,1]` over a **closed
4-manifold** `M` (`m' = 2`, `dim W = 5`), assembled from the honestly-remaining inputs as named
fields. This is the concrete-frame analogue of `PinPlusWAdmPinned.WAdmPinned` — the same
`{P14, P23, hwu} + {pin14, pin23}` shape — but **standalone** for the concrete cylinder-pair data,
so it does NOT depend on the abstract-`I` ↔ concrete-`𝓡 4` bridge (a named parameter of the arc,
NOT forced here).

## What `CylinderWAdmPinned` banks (the residual-set, precisely)

The structure's FIELDS are exactly the arc's honestly-open residuals; everything else is DERIVED:

* `hcls` — the **existence** hole: a `HasRelFundClass` witness for `[W,∂W]` (the honest product
  cross-product route `[W,∂W] = [M] × [I,∂I]`, a separate deep arc). Named, not forced.
* `findimM1`/`findimM2` — `M`'s own absolute Betti finiteness `b_1(M), b_2(M) < ∞`. The cylinder's
  `findimAbs` numerics are DERIVED from these via
  `PoincareLefschetzRelFundClassCylinderNumerics.cylinder_findimAbs14/23` (the contractible-factor
  collapse) — the residual-shrinking win folded in: `findimAbs` is an `M`-side input here.
* `findimRel14`/`findimRel23`, `nondeg14`/`nondeg23`, `dimeq14`/`dimeq23` — the three PL-duality
  numerics NOT yet in-tree-reducible (cohomology pair-LES exactness / pair-suspension iso / `M`'s
  own Poincaré-duality pairing walls; see `…CylinderNumerics`). Named as explicit parameters.
* `hwu` — the **Wu obstruction** vanishing `wuW2 P14 P23 = 0` (the `v₂(W) = v₁(W)²` computation, a
  separate deep arc). Named, not forced.
* `hdet` — the **Wall-2 slab determinedness** `determinedByPoints 5 (interiorSlab M)` (the
  closed-case degree-5 determination on `K = M × [¼,¾]`; general-compact good-compact determination
  in the boundaryless product interior is not in-tree — only whole-compact-manifold `goodCompact_univ`
  is). Named, not forced.

## What is DERIVED (theorems over the structure)

* `P14`/`P23` — the concrete Lefschetz–Wu data (`cylinderP14`/`cylinderP23`), with `findimAbs` fed
  from `M` internally.
* `pin14`/`pin23` — the substrate pins (`cylinderP14_pinned`/`cylinderP23_pinned`): `μ`, `cup`, `sqOp`
  are all the substrate operations. So this is a genuine `w₂(W) = 0` filter, NOT the F3 free-`sqOp`
  artefact.
* `wuFunctional23_honest` — the `(2,3)` Wu functional is the honest `⟨relSq² ·, [W,∂W]⟩`.
* `determinedByInteriorPoints` / the uniqueness of `[W,∂W]` — Wall 2 collapsed from `hdet` alone
  (the collar-injectivity residual is already discharged by the explicit product collar).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusWAdmPinned
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderNumerics

open scoped Manifold
open SKEFTHawking.PoincareLefschetzWu5
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.SingularRelativeCup SKEFTHawking.SingularRelativeBockstein
open SKEFTHawking.SingularRelativeSteenrodSq2
open SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularManifoldFundamentalClass
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCollar
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderWu
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderNumerics
open SKEFTHawking.PinPlusWAdmPinned

namespace SKEFTHawking.PinPlusCylinderWAdmPinned

noncomputable section

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]

/-! ## §1. The concrete-cylinder residual-set structure -/

/-- **The concrete-cylinder W-admissibility residual-set** for `W = M × [0,1]` over a closed
4-manifold `M`. The `WAdmPinned`-shaped consolidation: the FIELDS are exactly the arc's
honestly-open residuals (existence `hcls`, `M`'s Betti finiteness `findimM1/2`, the three
un-reduced numerics per leg, the Wu vanishing `hwu`, the Wall-2 slab determinedness `hdet`);
the two Lefschetz–Wu data, their substrate pins, and Wall 2 are all DERIVED (below). -/
structure CylinderWAdmPinned (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M] where
  /-- **Existence** of `[W,∂W]` (the product cross-product route). -/
  hcls : HasRelFundClass (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M))
    (cylGen (M := M) (m' := 2))
  /-- `b_1(M) < ∞` — feeds the `(1,4)` `findimAbs` via the contractible-factor collapse. -/
  findimM1 : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of M) 1)
  /-- `b_2(M) < ∞` — feeds the `(2,3)` `findimAbs` via the contractible-factor collapse. -/
  findimM2 : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of M) 2)
  /-- `(1,4)` relative finite-dimensionality `H^4(W,∂W) < ∞` (pair-LES wall). -/
  findimRel14 : FiniteDimensional (ZMod 2)
    (RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 4)
  /-- `(1,4)` Lefschetz non-degeneracy (`M`'s PD-pairing wall). -/
  nondeg14 : Function.Injective
    ⇑((relCupH14 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M))).compr₂
      (cylinderDatum hcls).mu)
  /-- `(1,4)` Lefschetz Betti equality `dim H^1(W) = dim H^4(W,∂W)` (pair-suspension iso wall). -/
  dimeq14 : Module.finrank (ZMod 2) (Cohomology (TopCat.of (cylW M)) 1)
          = Module.finrank (ZMod 2)
            (RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 4)
  /-- `(2,3)` relative finite-dimensionality `H^3(W,∂W) < ∞` (pair-LES wall). -/
  findimRel23 : FiniteDimensional (ZMod 2)
    (RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 3)
  /-- `(2,3)` Lefschetz non-degeneracy (`M`'s PD-pairing wall). -/
  nondeg23 : Function.Injective
    ⇑((relCupH23 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M))).compr₂
      (cylinderDatum hcls).mu)
  /-- `(2,3)` Lefschetz Betti equality `dim H^2(W) = dim H^3(W,∂W)` (pair-suspension iso wall). -/
  dimeq23 : Module.finrank (ZMod 2) (Cohomology (TopCat.of (cylW M)) 2)
          = Module.finrank (ZMod 2)
            (RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 3)
  /-- **The Wall-2 slab determinedness** `determinedByPoints 5 (M × [¼,¾])` (closed-case degree-5
  determination on the interior slab). -/
  hdet : determinedByPoints (X := TopCat.of (cylW M)) (2 + 1 + 2) (interiorSlab M)
  /-- **The Wu obstruction vanishes** `wuW2 P14 P23 = 0` (`v₂(W) = v₁(W)²` computation). -/
  hwu : wuW2
      (cylinderP14 hcls (cylinder_findimAbs14 findimM1) findimRel14 nondeg14 dimeq14)
      (cylinderP23 hcls (cylinder_findimAbs23 findimM2) findimRel23 nondeg23 dimeq23) = 0

/-! ## §2. The derived Lefschetz–Wu data, their substrate pins, and the honest-`w₂` seam -/

variable (W : CylinderWAdmPinned M)

/-- The derived `(1,4)` Lefschetz–Wu datum (with `findimAbs` fed from `M`). -/
def CylinderWAdmPinned.P14 : LefschetzWuDatum (TopCat.of (cylW M))
    ((cylModel 2).boundary (cylW M)) 1 4 5 :=
  cylinderP14 W.hcls (cylinder_findimAbs14 W.findimM1) W.findimRel14 W.nondeg14 W.dimeq14

/-- The derived `(2,3)` Lefschetz–Wu datum (with `findimAbs` fed from `M`). -/
def CylinderWAdmPinned.P23 : LefschetzWuDatum (TopCat.of (cylW M))
    ((cylModel 2).boundary (cylW M)) 2 3 5 :=
  cylinderP23 W.hcls (cylinder_findimAbs23 W.findimM2) W.findimRel23 W.nondeg23 W.dimeq23

/-- **The `(1,4)` datum is substrate-pinned** (`μ`, `cup := relCupH14`, `sqOp := relSq1` are all the
substrate operations) — so this consolidation is a genuine `w₂` filter, not the F3 free-`sqOp`
artefact. -/
theorem CylinderWAdmPinned.pin14 : LefschetzWuPinned14 W.P14 :=
  cylinderP14_pinned W.hcls (cylinder_findimAbs14 W.findimM1) W.findimRel14 W.nondeg14 W.dimeq14

/-- **The `(2,3)` datum is substrate-pinned.** -/
theorem CylinderWAdmPinned.pin23 : LefschetzWuPinned23 W.P23 :=
  cylinderP23_pinned W.hcls (cylinder_findimAbs23 W.findimM2) W.findimRel23 W.nondeg23 W.dimeq23

/-- **The consolidated admissibility** `wuW2 P14 P23 = 0`, restated over the derived data. -/
theorem CylinderWAdmPinned.hwu' : wuW2 W.P14 W.P23 = 0 := W.hwu

/-- **The `(2,3)` Wu functional is the HONEST one** `⟨relSq² ·, [W,∂W]⟩` — the crux of the pin: the
admissibility `hwu` is a genuine `w₂(W) = 0`, not gameable by a free `sqOp` (`not_sqOpPinned23_*`). -/
theorem CylinderWAdmPinned.wuFunctional23_honest :
    wuFunctional W.P23 = W.P23.mu.comp relSq2 :=
  W.pin23.wuFunctional_eq

/-- **The `(1,4)` Wu functional is the honest `⟨relSq¹ ·, [W,∂W]⟩`.** -/
theorem CylinderWAdmPinned.wuFunctional14_honest :
    wuFunctional W.P14 = W.P14.mu.comp (relSq1 (n := 3)) :=
  W.pin14.wuFunctional_eq

/-! ## §3. Wall 2 (`DeterminedByInteriorPoints`) and the uniqueness of `[W,∂W]`, from `hdet` alone -/

include W in
/-- **Wall 2 for the consolidation**, from the slab determinedness `hdet` alone: the
collar-injectivity residual is already discharged by the explicit product collar
(`cylinder_determinedByInteriorPoints_of_slab`). -/
theorem CylinderWAdmPinned.determinedByInteriorPoints :
    DeterminedByInteriorPoints (X := TopCat.of (cylW M))
      ((cylModel 2).boundary (cylW M)) (2 + 1 + 2) :=
  cylinder_determinedByInteriorPoints_of_slab W.hdet

include W in
/-- **The cylinder relative fundamental class is UNIQUE**, from the residual-set's `hdet`: two
classes restricting to the interior generator family `gen` everywhere agree (Wall 2 collapsed from
the slab determinedness; the collar residual is internally discharged). -/
theorem CylinderWAdmPinned.relFundClass_unique
    (gen : ∀ x : ↑(TopCat.of (cylW M)), x ∉ (cylModel 2).boundary (cylW M) →
      (RelativeHomology ({x}ᶜ) (2 + 1 + 2) ≃ₗ[ZMod 2] ZMod 2))
    {α β : RelativeHomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) (2 + 1 + 2)}
    (hα : RestrictsToRelGen (X := TopCat.of (cylW M)) (m := 2 + 1)
      ((cylModel 2).boundary (cylW M)) gen α)
    (hβ : RestrictsToRelGen (X := TopCat.of (cylW M)) (m := 2 + 1)
      ((cylModel 2).boundary (cylW M)) gen β) : α = β :=
  cylinderRelFundClass_unique_of_slab gen W.hdet hα hβ

end

end SKEFTHawking.PinPlusCylinderWAdmPinned
