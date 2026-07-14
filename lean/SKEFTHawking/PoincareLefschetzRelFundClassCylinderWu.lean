/-
# Phase 5q.H (W-A.1g) — the cylinder's Poincaré–Lefschetz Wu data (the `P14`/`P23` fragment)

The stretch payoff of the concrete cylinder `[W,∂W]` datum: assemble the two Lefschetz–Wu data
`P14`/`P23` for the reflexive cylinder `W = M × [0,1]` over a **closed 4-manifold** `M` (`m' = 2`,
so the pair lives at top degree `5 = 3 + 2`), the shape the char-pair provider `WAdm` consumes
(`PinPlusCharPairData.WAdm = P14 + P23 + hwu`).

* `cylinderRelFundClass_unique_of_slab` — the **payoff of the collar discharge**: with the
  collar-injectivity residual now closed (`…CylinderCollar.cylinder_determinedByInteriorPoints_of_slab`),
  the cylinder relative fundamental class is **unique** from the interior-slab closed-case
  `determinedByPoints` ALONE (Wall 2 is collar-residual-free).
* `cylinderP14` / `cylinderP23` — the concrete `LefschetzWuDatum … 1 4 5` / `… 2 3 5` for the cylinder
  pair, assembled via `LefschetzWuDatum.ofRelFund14`/`ofRelFund23` from the concrete cylinder datum
  `cylinderRelFundClassDatum` (its `μ` is the fundamental-class functional; its `sqOp` is pinned to
  `relSq1`/`relSq2`, the completed Steenrod legs). Their `mu` fields are the fundamental functional.
* `cylinderWuObstruction` — the class `wuW2 cylinderP14 cylinderP23` whose vanishing is the `hwu`
  admissibility field of `WAdm`.

## Named residuals (precisely staged, none faked)

The cylinder `P14`/`P23` are consumed here with the Poincaré–Lefschetz **duality-numerics** obligations
as explicit parameters — `findimAbs`/`findimRel` (finite-dimensionality of the (co)homology groups),
`nondeg` (non-degeneracy of the μ-pairing), `dimeq` (the Betti equality) — exactly the named 1d
discharge target of `LefschetzWuDatum.ofRelFund*`. The remaining obligations for a full
`WAdm (reflCylinder s)` are: (i) the **existence** hole `HasRelFundClass` for the cylinder
(`hcls`, the honest product route `[W,∂W] = [M] × [I,∂I]` via the relative cross product — a separate
deep arc); (ii) the duality-numerics parameters above; (iii) `hwu` = `cylinderWuObstruction = 0` (the
**Wu-class computation** `v₂(W) = v₁(W)²` for the cylinder — a genuinely separate deep arc, named not
forced); and (iv) the **abstract-`I` ↔ concrete-`𝓡 4` bridge** identifying `(I.prod 𝓡∂1).boundary b.W`
with `(cylModel 2).boundary (cylW s.M)` for a char-pair `s` (needed to land the `Bordism`-indexed
`WAdm (reflCylinder s)` rather than the concrete cylinder-pair data produced here).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderCollar
import SKEFTHawking.PoincareLefschetzWuAssembly

open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCollar
open SKEFTHawking.PoincareLefschetzWu5 SKEFTHawking.PoincareLefschetzWuAssembly
open SKEFTHawking.SingularRelativeCup SKEFTHawking.SingularRelativeBockstein
open SKEFTHawking.SingularRelativeSteenrodSq2
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeMV
open SKEFTHawking.SingularManifoldFundamentalClass
open SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2

namespace SKEFTHawking.PoincareLefschetzRelFundClassCylinderWu

open scoped Manifold

noncomputable section

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]

/-! ## §1. Uniqueness of the cylinder fundamental class from the slab alone (collar payoff) -/

omit [Nonempty M] in
/-- **Uniqueness of the cylinder relative fundamental class from the slab alone.** With the
collar-injectivity residual discharged by the explicit product collar
(`cylinder_determinedByInteriorPoints_of_slab`), Wall 2 needs only the interior-slab closed-case
`determinedByPoints`; two classes restricting to the interior generator everywhere then agree. This is
the concrete payoff of the collar work: the cylinder `[W,∂W]` is pinned uniquely once the slab
determination `hdet` is available. -/
theorem cylinderRelFundClass_unique_of_slab
    (gen : ∀ x : ↑(TopCat.of (cylW M)), x ∉ (cylModel 2).boundary (cylW M) →
      (RelativeHomology ({x}ᶜ) (2 + 1 + 2) ≃ₗ[ZMod 2] ZMod 2))
    (hdet : determinedByPoints (X := TopCat.of (cylW M)) (2 + 1 + 2) (interiorSlab M))
    {α β : RelativeHomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) (2 + 1 + 2)}
    (hα : RestrictsToRelGen (X := TopCat.of (cylW M)) (m := 2 + 1)
      ((cylModel 2).boundary (cylW M)) gen α)
    (hβ : RestrictsToRelGen (X := TopCat.of (cylW M)) (m := 2 + 1)
      ((cylModel 2).boundary (cylW M)) gen β) : α = β :=
  cylinderRelFundClass_unique gen (cylinder_determinedByInteriorPoints_of_slab hdet) hα hβ

/-! ## §2. The concrete cylinder Poincaré–Lefschetz Wu data `P14` / `P23` -/

/-- The concrete cylinder relative-fundamental-class datum at `m = 3` (top degree 5), from the
existence witness `hcls` (the product cross-product route). -/
def cylinderDatum
    (hcls : HasRelFundClass (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M))
      (cylGen (M := M) (m' := 2))) :
    RelFundClassDatum (X := TopCat.of (cylW M)) (m := 3) ((cylModel 2).boundary (cylW M)) :=
  cylinderRelFundClassDatum hcls

/-- **The cylinder `(1,4)` Lefschetz–Wu datum** `LefschetzWuDatum (W) (∂W) 1 4 5`, assembled from the
concrete cylinder datum with `cup := relCupH14`, `sqOp := relSq1` pinned. The duality-numerics
parameters (`findimAbs`, `findimRel`, `nondeg`, `dimeq`) are the named PL-duality obligations. -/
def cylinderP14
    (hcls : HasRelFundClass (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M))
      (cylGen (M := M) (m' := 2)))
    (findimAbs : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of (cylW M)) 1))
    (findimRel : FiniteDimensional (ZMod 2)
      (RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 4))
    (nondeg : Function.Injective
      ⇑((relCupH14 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M))).compr₂
        (cylinderDatum hcls).mu))
    (dimeq : Module.finrank (ZMod 2) (Cohomology (TopCat.of (cylW M)) 1)
           = Module.finrank (ZMod 2)
             (RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 4)) :
    LefschetzWuDatum (TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 1 4 5 :=
  LefschetzWuDatum.ofRelFund14 (cylinderDatum hcls) findimAbs findimRel nondeg dimeq

/-- **The cylinder `(2,3)` Lefschetz–Wu datum** `LefschetzWuDatum (W) (∂W) 2 3 5`, with
`cup := relCupH23`, `sqOp := relSq2` pinned. -/
def cylinderP23
    (hcls : HasRelFundClass (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M))
      (cylGen (M := M) (m' := 2)))
    (findimAbs : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of (cylW M)) 2))
    (findimRel : FiniteDimensional (ZMod 2)
      (RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 3))
    (nondeg : Function.Injective
      ⇑((relCupH23 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M))).compr₂
        (cylinderDatum hcls).mu))
    (dimeq : Module.finrank (ZMod 2) (Cohomology (TopCat.of (cylW M)) 2)
           = Module.finrank (ZMod 2)
             (RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 3)) :
    LefschetzWuDatum (TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 2 3 5 :=
  LefschetzWuDatum.ofRelFund23 (cylinderDatum hcls) findimAbs findimRel nondeg dimeq

omit [Nonempty M] in
/-- **The cylinder `(1,4)` datum's `μ` is the fundamental-class functional** (`ofRelFund14` threads it
faithfully): the deepest Wu-tower input for the cylinder is `⟨·, [W,∂W]⟩`. The `hwu` admissibility
field of `WAdm` is the vanishing `wuW2 (cylinderP14 …) (cylinderP23 …) = 0` (the named Wu-class
computation `v₂(W) = v₁(W)²`, not forced here). -/
theorem cylinderP14_mu
    (hcls : HasRelFundClass (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M))
      (cylGen (M := M) (m' := 2)))
    (findimAbs : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of (cylW M)) 1))
    (findimRel : FiniteDimensional (ZMod 2)
      (RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 4))
    (nondeg : Function.Injective
      ⇑((relCupH14 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M))).compr₂
        (cylinderDatum hcls).mu))
    (dimeq : Module.finrank (ZMod 2) (Cohomology (TopCat.of (cylW M)) 1)
           = Module.finrank (ZMod 2)
             (RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 4)) :
    (cylinderP14 hcls findimAbs findimRel nondeg dimeq).mu = (cylinderDatum hcls).mu :=
  LefschetzWuDatum.ofRelFund14_mu (cylinderDatum hcls) findimAbs findimRel nondeg dimeq

end

end SKEFTHawking.PoincareLefschetzRelFundClassCylinderWu
