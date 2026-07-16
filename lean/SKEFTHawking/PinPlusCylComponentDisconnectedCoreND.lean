import Mathlib
import SKEFTHawking.PinPlusCylComponentExcisionBridgeFinite
import SKEFTHawking.PinPlusCylDataDischargeWuLeaf

/-!
# Phase 5q.H — THE DISCONNECTED `DisconnectedCylCoreND`, D DISCHARGED, reduced to the named Fubini leaves

The disconnected residual `DisconnectedCylCoreND M = {D, nd14, nd23, hwu}` (four-field, `hM4` already
discharged connectedness-free by `topHomology_finite`). This module discharges its `D` field
UNCONDITIONALLY (the k-component `cylinderRelFundClassDatum_of_components`, no disconnected-specific
posit) and reduces the remaining three fields to their **honest named residuals**, connectedness-free:

* **`nd14`/`nd23`** (the Poincaré–Lefschetz non-degeneracy of the disconnected cylinder pairing against
  the k-component `D.mu`) reduce — via the class-parametric, connectedness-free
  `cylinder_nondeg{14,23}_of_intertwining` with the α-collapse pinned to `cylCollapse{1,2}` — to the
  disconnected **cup-suspension intertwining** `(β, hcompat)`: the β-suspension iso plus the cup-cross
  **Fubini** identity `⟨a ∪ b, [W,∂W]⟩ = ⟨α a ∪ β b, [M]⟩` for `[W,∂W] = [M] × [I,∂I]`
  (`DisconnectedCylSuspIntertwineData`). This is the SAME missing Eilenberg–Zilber cross-product layer
  the connected case reduces to (`…CylinderIntertwine.CylinderSuspIntertwineData`) — now for the
  k-component class. The block-diagonal alternative is fenced: the relative-⊔ cohomology decomposition
  (`SingularRelativeCohomologyDisjointSum`) is stated over the LITERAL `sumSpace`, requiring the
  `cylW M ≅ sumSpace` homeo (the settled sum-route fence).

* **`hwu`** (`wuW2(discP14, discP23) = 0`) reduces — via the connectedness-free `cylinderWu_of_desuspend`
  (the α-collapse ring-iso carrying `wuW2(cyl) ↦ wuW2(M)`) — to `σ.cert` (`w₂(M) = 0`) plus the two
  disconnected Wu-class desuspension identities `DiscCylV{1,2}Desuspend` (the disconnected twins of the
  connected `CylV{1,2}Desuspend` atoms, against the k-component `D`).

So the honest disconnected residual, D discharged, is exactly
`{disconnected-intertwining, DiscCylV1Desuspend, DiscCylV2Desuspend}` — the disconnected cup-cross Fubini
/ Steenrod-suspension leaves — NOT the monolithic four-field core. These residuals are STATED (genuine
geometric identities, not completeness Props) and NOT inhabited here (the EZ/Fubini wall); the provider
corollary threads them per-`σ`, making the sharpened disconnected row visible.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new axiom, no
`native_decide`, no `maxHeartbeats`.
-/

open scoped Manifold
open SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularRelativeCup
open SKEFTHawking.PoincareLefschetzWu5
open SKEFTHawking.PoincareDualityWu
open SKEFTHawking.PoincareDualityWuFormula
open SKEFTHawking.PoincareDualityConstruct
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderWu
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderNondeg
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderIntertwine
open SKEFTHawking.SingularPD4Instances
open SKEFTHawking.PinPlusCylDataDischargeDisconnected
open SKEFTHawking.PinPlusCylDataDischargeDisconnectedComponents
open SKEFTHawking.PinPlusCylDataDischargeWuLeaf
open SKEFTHawking.PinPlusCylComponentExcisionBridgeFinite
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCharPairBorTethered

namespace SKEFTHawking.PinPlusCylComponentDisconnectedCoreND

noncomputable section

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M] [T1Space (cylW M)]

/-! ## §1. The k-component disconnected `D` (fully discharged), packaged as `cylinderDatum`. -/

/-- **The disconnected cylinder relative fundamental class**, k-component partition, as the concrete
`cylinderDatum` (so its `.mu` matches the intertwining/Wu lemmas syntactically). Fully discharged — no
disconnected-specific posit. -/
def discD : RelFundClassDatum (X := TopCat.of (cylW M)) (m := 3) ((cylModel 2).boundary (cylW M)) :=
  cylinderDatum (hasRelFundClass_cylGen_components (m' := 2) (M := M))

/-! ## §2. `nd14`/`nd23` reduced to the disconnected cup-suspension intertwining (α discharged). -/

/-- **The disconnected cup-suspension intertwining residual** (α-collapse pinned). The two legs of the
disconnected cylinder Poincaré–Lefschetz non-degeneracy against the k-component `discD.mu`, each a
suspension iso `β` plus the cup-cross Fubini compatibility `⟨a ∪ b, [W,∂W]⟩ = ⟨(cylCollapse a) ∪ β b,
[M]⟩`. The disconnected twin of `…CylinderIntertwine.CylinderSuspIntertwineData` — the SAME missing
Eilenberg–Zilber layer, now for the disconnected class. NOT inhabited here (the EZ/Fubini wall). -/
structure DisconnectedCylSuspIntertwineData (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M] [T1Space (cylW M)] where
  /-- The `(2,3)` suspension iso `β : H³(W,∂W) ≃ H²(M)`. -/
  β23 : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 3
      ≃ₗ[ZMod 2] Cohomology (TopCat.of M) 2
  /-- The `(2,3)` cup-suspension Fubini compatibility (α pinned to `cylCollapse2`). -/
  hcompat23 : ∀ (a : Cohomology (TopCat.of (cylW M)) 2)
      (b : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 3),
      (discD (M := M)).mu
          (relCupH23 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M)) a b)
        = fundamentalFunctional (m := 2) (M := M) (cupH24 (cylCollapse2 a) (β23 b))
  /-- The `(1,4)` suspension iso `β : H⁴(W,∂W) ≃ H³(M)`. -/
  β14 : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 4
      ≃ₗ[ZMod 2] Cohomology (TopCat.of M) 3
  /-- The `(1,4)` cup-suspension Fubini compatibility (α pinned to `cylCollapse1`). -/
  hcompat14 : ∀ (a : Cohomology (TopCat.of (cylW M)) 1)
      (b : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 4),
      (discD (M := M)).mu
          (relCupH14 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M)) a b)
        = fundamentalFunctional (m := 2) (M := M) (cupH13 (cylCollapse1 a) (β14 b))

/-- The disconnected `(2,3)` non-degeneracy from the intertwining (connectedness-free, class-parametric). -/
theorem DisconnectedCylSuspIntertwineData.nd23 (D : DisconnectedCylSuspIntertwineData M) :
    Function.Injective
      ⇑((relCupH23 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M))).compr₂
        (discD (M := M)).mu) :=
  cylinder_nondeg23_of_intertwining (hasRelFundClass_cylGen_components (m' := 2) (M := M))
    cylCollapse2 D.β23 D.hcompat23

/-- The disconnected `(1,4)` non-degeneracy from the intertwining (connectedness-free, class-parametric). -/
theorem DisconnectedCylSuspIntertwineData.nd14 (D : DisconnectedCylSuspIntertwineData M) :
    Function.Injective
      ⇑((relCupH14 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M))).compr₂
        (discD (M := M)).mu) :=
  cylinder_nondeg14_of_intertwining (hasRelFundClass_cylGen_components (m' := 2) (M := M))
    cylCollapse1 D.β14 D.hcompat14

/-! ## §3. The two disconnected Wu-class desuspension leaves (against the k-component `D`). -/

/-- **The disconnected `(2,3)` Wu-desuspension leaf** — the disconnected twin of `CylV2Desuspend`: the
k-component cylinder's `(2,3)` Lefschetz–Wu class `v₂(W)`, collapsed to `H²(M)`, is `M`'s middle Wu class
`wuClass2 (pd4Mid M)`. The nd leg is `Prop`-quantified (proof-irrelevant). -/
def DiscCylV2Desuspend : Prop :=
  ∀ (nd23 : Function.Injective
      ⇑((relCupH23 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M))).compr₂
        (discD (M := M)).mu)),
    cylCollapse2 (wuClassW2 (discP23 M (discD (M := M)) nd23))
      = wuClass2 (poincareDual4Mid_of_closed (M := M))

/-- **The disconnected `(1,4)` Wu-desuspension leaf** — the disconnected twin of `CylV1Desuspend`. -/
def DiscCylV1Desuspend : Prop :=
  ∀ (nd14 : Function.Injective
      ⇑((relCupH14 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M))).compr₂
        (discD (M := M)).mu)),
    cylCollapse1 (wuClassW1 (discP14 M (discD (M := M)) (topHomology_finite M) nd14))
      = wuClass1 (poincareDual4Lo_of_closed (M := M))

/-! ## §4. The disconnected core assembled from the named residuals (D + hM4 discharged). -/

/-- **THE DISCONNECTED CORE, D DISCHARGED, from the named leaves.** `DisconnectedCylCoreND M` from the
disconnected intertwining data (→ `nd14`/`nd23`) + the base certificate `σ.cert` (`hcert`) + the two
disconnected Wu-desuspension leaves (→ `hwu` via `cylinderWu_of_desuspend`). The `D` field is the fully
discharged k-component class; `hM4` is `topHomology_finite`; connectedness-free throughout. This is the
honest named reduction of the disconnected core: its only open content is the disconnected cup-cross
Fubini intertwining + the two Steenrod-suspension Wu leaves. -/
def disconnectedCylCoreND_of_named (D : DisconnectedCylSuspIntertwineData M)
    (hcert : PoincareDualityWuFormula.wuW2 (poincareDual4Mid_of_closed (M := M))
      (poincareDual4Lo_of_closed (M := M)) = 0)
    (hA : DiscCylV2Desuspend (M := M)) (hB : DiscCylV1Desuspend (M := M)) :
    DisconnectedCylCoreND M where
  D := discD (M := M)
  nd14 := D.nd14
  nd23 := D.nd23
  hwu := cylinderWu_of_desuspend (discP14 M (discD (M := M)) (topHomology_finite M) D.nd14)
    (discP23 M (discD (M := M)) D.nd23) hcert (hA D.nd23) (hB D.nd14)

end

/-! ## §5. The sharpened provider row — the disconnected residual made visible.

The disconnected leg of the provider row, previously the monolithic four-field `DisconnectedCylCoreND`,
is now the honest named residual `{disconnected-intertwining, DiscCylV1Desuspend, DiscCylV2Desuspend}` +
`σ.cert` (the `D` and `hM4` fields fully discharged; the `nd`/`hwu` fields reduced to the disconnected
cup-cross Fubini leaves). The connected leg (`CylV1Desuspend`/`CylV2Desuspend`) is unchanged. -/

/-- **The provider on the SHARPENED disconnected residual.** Identical to
`PinPlusCylDataDischargeWuLeaf.nonempty_provider_of_desuspendLeaves_and_disconnectedCoreND` except the
disconnected hypothesis supplies the disconnected core through its honest named leaves — the disconnected
cup-suspension intertwining (`DisconnectedCylSuspIntertwineData`, → `nd14`/`nd23`) and the two disconnected
Wu-desuspension identities (`DiscCylV{1,2}Desuspend`, → `hwu` via `σ.cert`) — rather than the monolithic
four-field `DisconnectedCylCoreND`. The `D` field is the fully discharged k-component class; `hM4` is
`topHomology_finite`. The disconnected residual is thereby the disconnected Eilenberg–Zilber Fubini /
Steenrod-suspension leaves, the twins of the connected atoms. -/
theorem nonempty_provider_of_desuspendLeaves_and_disconnectedNamed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {k : WithTop ℕ∞} {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]
    (hA : ∀ {s : SingularManifold.{0} PUnit.{1} k I} (_σ : CharPairStrBundled I s)
      [T2Space s.M] [Nonempty s.M] [PreconnectedSpace s.M] [T1Space (cylW s.M)],
      CylV2Desuspend (M := s.M))
    (hB : ∀ {s : SingularManifold.{0} PUnit.{1} k I} (_σ : CharPairStrBundled I s)
      [T2Space s.M] [Nonempty s.M] [PreconnectedSpace s.M] [T1Space (cylW s.M)],
      CylV1Desuspend (M := s.M))
    (hInt : ∀ {s : SingularManifold.{0} PUnit.{1} k I} (_σ : CharPairStrBundled I s)
      [T2Space s.M] [Nonempty s.M] [T1Space (cylW s.M)],
      ¬ PreconnectedSpace s.M → DisconnectedCylSuspIntertwineData s.M)
    (hAdisc : ∀ {s : SingularManifold.{0} PUnit.{1} k I} (_σ : CharPairStrBundled I s)
      [T2Space s.M] [Nonempty s.M] [T1Space (cylW s.M)],
      ¬ PreconnectedSpace s.M → DiscCylV2Desuspend (M := s.M))
    (hBdisc : ∀ {s : SingularManifold.{0} PUnit.{1} k I} (_σ : CharPairStrBundled I s)
      [T2Space s.M] [Nonempty s.M] [T1Space (cylW s.M)],
      ¬ PreconnectedSpace s.M → DiscCylV1Desuspend (M := s.M)) :
    Nonempty (CharPairWProviderPerOp I k) := by
  refine SKEFTHawking.PinPlusCylDataDischargeWuLeaf.nonempty_provider_of_desuspendLeaves_and_disconnectedCoreND
    hA hB ?_
  intro s σ _ _ hpc
  haveI : T1Space (cylW s.M) := inferInstance
  exact disconnectedCylCoreND_of_named (hInt σ hpc) σ.cert (hAdisc σ hpc) (hBdisc σ hpc)

end SKEFTHawking.PinPlusCylComponentDisconnectedCoreND
