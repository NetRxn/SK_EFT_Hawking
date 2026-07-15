import Mathlib
import SKEFTHawking.PinPlusCylDataDischarge

/-!
# Phase 5q.H — THE DISCONNECTED `CylWAdmData` (provider residual (b))

The merged `cylData` discharge (`PinPlusCylDataDischarge`) inhabited the provider modulo TWO residuals;
this module attacks residual **(b)**: `CylWAdmData s` for a σ-carrying `s` with NONEMPTY DISCONNECTED
`s.M` (the `hdisc` hypothesis of `nonempty_provider_of_wuLeaf_and_disconnected`). The blocker: the
connected engine `CylinderWAdmPinned.ofClosedPDSuspIntertwineNorm` requires `[PreconnectedSpace M]`
because the cylinder relative fundamental class `hasRelFundClass_cylGen` routes through
`SingularFundamentalClass.fundamentalClass` (a *connected* closed 4-manifold's `ℤ/2`-generator of
`H₄`; `…CrossLocalAlphaU.alphaU_ne_zero` is `omit [PreconnectedSpace M]`, so the connectedness
dependence localises entirely to that generator). An arbitrary disconnected compact 4-manifold is not a
literal `.sum`, so the `datumTransport` (fixed-carrier set-equality) that closes the abstract-bordism
`⊔`-tower (`WAdmPinned.add`, whose `(b₁.add b₂).W` is *defeq* to `b₁.W ⊕ b₂.W`) does NOT apply — there
is no defeq `cylW s.M ≅ (defeq) A ⊕ B`.

## What this module does — the HONEST decomposition (connectedness-free ⟂ connectedness-dependent)

`CylWAdmData s` is assembled by `LefschetzWuDatum.ofRelFund14`/`ofRelFund23` from **thirteen** inputs
(`{D, findimAbs, findimRel, nondeg, dimeq}` per leg, shared `D`, plus two pins and `hwu`). This module
proves — GREEN, kernel-pure, WITHOUT `[PreconnectedSpace]` — that **eight of the thirteen** discharge
from the connectedness-FREE closed-manifold stock (`finiteDimensional_cohomology_of_closed` +
`finiteDimensional_homology_of_closed`, neither of which needs connectedness):

* `findimAbs14`, `findimAbs23` — `cylinder_findimAbs{14,23}` ∘ cohomology findims (degrees 1,2);
* `findimRel23` — `cylinder_findimRel23` ∘ `cylinder_findimRelHom23_of_base` (homology degrees 3,2);
* `dimeq14`, `dimeq23` — `cylinder_dimeq14_of_basePD` / `cylinder_dimeq23_holds` (basePD + degree 2);
* `pin14`, `pin23` — `ofRelFund{14,23}_pinned` (substrate-pinned by construction);
* `findimRel14` — `cylinder_findimRel14` ∘ `cylinder_findimRelHom14_of_base`, MODULO the single
  connectedness-dependent finiteness input `hM4` (`b₄(M) < ∞`).

The residual is thereby SHARPENED from `CylWAdmData s` (thirteen inputs) to the **five-field**
connectedness-dependent core `DisconnectedCylCore s.M = {D, hM4, nd14, nd23, hwu}` — exactly the pieces
the disconnected fundamental-class detection controls: the cylinder relative fundamental-class datum
`D`, the top-homology finiteness `hM4`, the two Lefschetz non-degeneracies, and the Wu obstruction.
`cylWAdmData_of_disconnectedCore` then builds `CylWAdmData s` from this core with NO `PreconnectedSpace`
instance, and `nonempty_provider_of_wuLeaf_and_disconnectedCore` re-states the provider on the sharpened
residual.

The core is the honest banked leaf: its five fields are genuinely tied to the connectedness-free
fundamental-class detection (Route 2 of the lead's brief) / the `cylW(A ⊔ B) ≃ cylW A ⊕ cylW B`
distribution-transport (Route 1) — neither of which is in-tree infrastructure yet (there is no
homeomorphism-transport of relative Lefschetz–Wu data; `datumTransport` is fixed-carrier only). The
eight discharged inputs certify (kernel-pure) that finiteness / Poincaré-duality / pinning are NOT the
disconnected obstruction — only the fundamental-class core is.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/

open scoped Manifold
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularRelativeCup
open SKEFTHawking.PoincareLefschetzWu5
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderNumerics
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspension
open SKEFTHawking.PoincareLefschetzWuAssembly
open SKEFTHawking.PinPlusWAdmPinned
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCharPairWProviderTransport
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.SingularClosedHomologyFinite
open SKEFTHawking.SingularPD4Instances

namespace SKEFTHawking.PinPlusCylDataDischargeDisconnected

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {k : WithTop ℕ∞}
variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]

/-! ## §1. The connectedness-FREE `(1,4)`/`(2,3)` datum builders.

Both legs are assembled from a supplied relative fundamental-class datum `D` and non-degeneracy, with
every finiteness/duality input pulled from the connectedness-free closed-manifold stock. The ONLY
connectedness-dependent finiteness input is `hM4` (feeding the `(1,4)` `findimRel`). NO
`[PreconnectedSpace M]` instance appears. -/

variable (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]

/-- The `(1,4)` cylinder Lefschetz–Wu datum from a supplied `D`, `hM4`, and non-degeneracy — every
other input (`findimAbs14`, `findimRel14` modulo `hM4`, `dimeq14`) from connectedness-free stock. -/
def discP14
    (D : RelFundClassDatum (X := TopCat.of (cylW M)) (m := 3) ((cylModel 2).boundary (cylW M)))
    (hM4 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 4))
    (nd14 : Function.Injective
      ⇑((relCupH14 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M))).compr₂ D.mu)) :
    LefschetzWuDatum (TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 1 4 5 :=
  LefschetzWuDatum.ofRelFund14 D
    (cylinder_findimAbs14 (finiteDimensional_cohomology_of_closed (M := M)).1)
    (cylinder_findimRel14 (cylinder_findimRelHom14_of_base hM4
      (finiteDimensional_homology_of_closed (M := M)).2.2.1))
    nd14
    (cylinder_dimeq14_of_basePD (finiteDimensional_homology_of_closed (M := M)).2.2.1
      (finiteDimensional_homology_of_closed (M := M)).2.2.2)

/-- The `(2,3)` cylinder Lefschetz–Wu datum from a supplied `D` and non-degeneracy — EVERY finiteness/
duality input (`findimAbs23`, `findimRel23`, `dimeq23`) from connectedness-free stock (no `hM4`). -/
def discP23
    (D : RelFundClassDatum (X := TopCat.of (cylW M)) (m := 3) ((cylModel 2).boundary (cylW M)))
    (nd23 : Function.Injective
      ⇑((relCupH23 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M))).compr₂ D.mu)) :
    LefschetzWuDatum (TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 2 3 5 :=
  LefschetzWuDatum.ofRelFund23 D
    (cylinder_findimAbs23 (finiteDimensional_cohomology_of_closed (M := M)).2.1)
    (cylinder_findimRel23 (cylinder_findimRelHom23_of_base
      (finiteDimensional_homology_of_closed (M := M)).2.2.1
      (finiteDimensional_homology_of_closed (M := M)).2.1))
    nd23
    (cylinder_dimeq23_holds (finiteDimensional_homology_of_closed (M := M)).2.1)

/-- The `(1,4)` datum is substrate-pinned — connectedness-free (`ofRelFund14_pinned`). -/
theorem discP14_pinned
    (D : RelFundClassDatum (X := TopCat.of (cylW M)) (m := 3) ((cylModel 2).boundary (cylW M)))
    (hM4 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 4))
    (nd14 : Function.Injective
      ⇑((relCupH14 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M))).compr₂ D.mu)) :
    LefschetzWuPinned14 (discP14 M D hM4 nd14) :=
  ofRelFund14_pinned D _ _ nd14 _

/-- The `(2,3)` datum is substrate-pinned — connectedness-free (`ofRelFund23_pinned`). -/
theorem discP23_pinned
    (D : RelFundClassDatum (X := TopCat.of (cylW M)) (m := 3) ((cylModel 2).boundary (cylW M)))
    (nd23 : Function.Injective
      ⇑((relCupH23 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M))).compr₂ D.mu)) :
    LefschetzWuPinned23 (discP23 M D nd23) :=
  ofRelFund23_pinned D _ _ nd23 _

/-! ## §2. The sharpened connectedness-dependent core. -/

/-- **The disconnected cylinder core** — the FIVE-field connectedness-dependent residual to which the
disconnected `CylWAdmData` reduces after the eight connectedness-free inputs are discharged (§1). Each
field is exactly a piece the (missing) disconnected fundamental-class detection would supply: the
cylinder relative fundamental-class datum `D`, the top-homology finiteness `hM4` (`b₄(M) < ∞`), the two
Lefschetz non-degeneracies (`nd14`/`nd23`), and the Wu obstruction `hwu`. This is the honest banked
leaf for residual (b): NO `[PreconnectedSpace]` appears, and the eight discharged inputs certify that
finiteness/duality/pinning are NOT the disconnected obstruction. -/
structure DisconnectedCylCore (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M] where
  /-- the cylinder relative fundamental-class datum (the connectedness-free fundamental class). -/
  D : RelFundClassDatum (X := TopCat.of (cylW M)) (m := 3) ((cylModel 2).boundary (cylW M))
  /-- the top mod-2 homology of the base is finite-dimensional (`b₄(M) < ∞`). -/
  hM4 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 4)
  /-- the `(1,4)` Lefschetz pairing is non-degenerate. -/
  nd14 : Function.Injective
    ⇑((relCupH14 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M))).compr₂ D.mu)
  /-- the `(2,3)` Lefschetz pairing is non-degenerate. -/
  nd23 : Function.Injective
    ⇑((relCupH23 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M))).compr₂ D.mu)
  /-- the Wu obstruction of the assembled data vanishes. -/
  hwu : wuW2 (discP14 M D hM4 nd14) (discP23 M D nd23) = 0

/-! ## §3. The `CylWAdmData` build from the core — NO `PreconnectedSpace`. -/

/-- **THE DISCONNECTED BUILD**: `CylWAdmData s` from the five-field `DisconnectedCylCore s.M`, with the
eight connectedness-free inputs discharged from stock. NO `[PreconnectedSpace s.M]` instance — the only
topological instances are `T2Space`/`Nonempty` (from `σ.t2` and the disconnected-branch hypothesis at
the call site), plus the ambient `CompactSpace`/`ChartedSpace` every `SingularManifold` carries. -/
def cylWAdmData_of_disconnectedCore {s : SingularManifold.{0} PUnit.{1} k I}
    [T2Space s.M] [Nonempty s.M] (core : DisconnectedCylCore s.M) : CylWAdmData s where
  P14 := discP14 s.M core.D core.hM4 core.nd14
  P23 := discP23 s.M core.D core.nd23
  pin14 := discP14_pinned s.M core.D core.hM4 core.nd14
  pin23 := discP23_pinned s.M core.D core.nd23
  hwu := core.hwu

/-! ## §4. The provider on the SHARPENED disconnected residual.

Identical to `PinPlusCylDataDischarge.nonempty_provider_of_wuLeaf_and_disconnected` except the
disconnected hypothesis is the sharpened five-field `DisconnectedCylCore s.M` (via
`cylWAdmData_of_disconnectedCore`) rather than the full thirteen-input `CylWAdmData s`. Same empty and
nonempty-connected branches (`cylWAdmData_empty` / `cylWAdmData_of_wuResidual`). -/
theorem nonempty_provider_of_wuLeaf_and_disconnectedCore
    (hwu : ∀ {s : SingularManifold.{0} PUnit.{1} k I} (_σ : CharPairStrBundled I s)
      [T2Space s.M] [Nonempty s.M] [PreconnectedSpace s.M] [T1Space (cylW s.M)],
      SKEFTHawking.PinPlusCylDataDischarge.CylinderWuResidual s.M)
    (hdiscCore : ∀ {s : SingularManifold.{0} PUnit.{1} k I} (_σ : CharPairStrBundled I s)
      [T2Space s.M] [Nonempty s.M], ¬ PreconnectedSpace s.M → DisconnectedCylCore s.M) :
    Nonempty (CharPairWProviderPerOp I k) := by
  refine SKEFTHawking.PinPlusKTLeafGate.nonempty_provider_of_cylData (fun {s} σ => ?_)
  by_cases hne : Nonempty s.M
  · by_cases hpc : PreconnectedSpace s.M
    · haveI := hne
      haveI := hpc
      haveI : T2Space s.M := σ.t2
      haveI : T2Space (cylW s.M) := inferInstance
      haveI : T1Space (cylW s.M) := inferInstance
      exact SKEFTHawking.PinPlusCylDataDischarge.cylWAdmData_of_wuResidual (hwu σ)
    · haveI := hne
      haveI : T2Space s.M := σ.t2
      exact cylWAdmData_of_disconnectedCore (hdiscCore σ hpc)
  · haveI : IsEmpty s.M := not_nonempty_iff.mp hne
    exact SKEFTHawking.PinPlusCylDataDischarge.cylWAdmData_empty

end

end SKEFTHawking.PinPlusCylDataDischargeDisconnected
