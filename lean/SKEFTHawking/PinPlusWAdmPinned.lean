/-
# Phase 5q.H W-A arm 4 — the ADMISSIBILITY PIN (spec item 3), as a STANDALONE LAYER

The FIX for the round-5 vacuity finding **F3** (`PinPlusCharPairGeoRealizationGate` §5, fork
`wadm-sqop-gauge-w2-filter-vacuous`): `LefschetzWuDatum.sqOp` is a FREE field — it appears in NEITHER
of the datum's constraints (`nondeg`, `dimeq`) — so `LefschetzWuDatum.zeroSq` replaces it with `0`,
after which both Wu classes vanish (`wuClass_zeroSq`), `wuW2 = 0` holds DEFINITIONALLY for every `W`
whatever its honest `w₂` (`wuW2_zeroSq`), and a full `CharPairWProvider` is dischargeable from bare
Lefschetz-duality data with ZERO Steenrod input (`charPairWProviderOfDuality`). W-admissibility, as
shaped, is not a `w₂(W) = 0` filter. This module builds the layer that MAKES it one.

## The pin (design decision: per-field CERTIFICATE, not a re-defined structure)

We do NOT touch `LefschetzWuDatum` (wt2/carrier lane; it is consumed by the frozen `WAdm`/`Bor`).
Instead we add a *certificate* layer over an existing datum, asserting that its three operational
fields ARE the substrate's actual operations:

* `SqOpPinned14 P := (P.sqOp = relSq1)` / `SqOpPinned23 P := (P.sqOp = relSq2)` — the datum's Steenrod
  square IS the substrate relative Steenrod square (`SingularRelativeBockstein.relSq1` at the `(1,4)`
  leg's `Sq¹ : H⁴(W,∂W) → H⁵(W,∂W)`, `SingularRelativeSteenrodSq2.relSq2` at the `(2,3)` leg's
  `Sq² : H³(W,∂W) → H⁵(W,∂W)`). **This is the load-bearing discriminator** — see below.
* `CupPinned14 P := (P.cup = relCupH14)` / `CupPinned23 P := (P.cup = relCupH23)` — the datum's cup IS
  the substrate relative cup product (`SingularRelativeCup`).
* `MuPinned P := ∃ D : RelFundClassDatum (m := 3) S, P.mu = D.mu` — the datum's `μ` IS the relative
  fundamental-class functional `⟨·, [W,∂W]⟩` of a genuine `RelFundClassDatum` (whose `cls` is pinned
  by its own `restricts` field to a class hitting the interior generator everywhere).

`LefschetzWuPinned14`/`23` bundle all three. Certificate over definitional: the frozen `WAdm`/`Bor`
carry an *existing* `LefschetzWuDatum`, so re-defining the structure would ripple the carrier
(wt1's lane); a `Prop`-certificate over the datum is additive and folds into the carrier as a
refinement (item 3 below) with no structural surgery.

## The `mu`/`cup` audit verdict

F3 is sharpest for `sqOp` because `sqOp` is the ONLY field that appears in `wuFunctional`
(`μ ∘ sqOp`) yet in NO constraint — zeroing it kills the Wu functional unconditionally with no
Steenrod input. `μ` and `cup` DO appear in `nondeg` (via `cup.compr₂ μ`), so they cannot be zeroed
(that breaks non-degeneracy). BUT `nondeg` only forces the pairing to be *perfect*, not to be the
*actual* Poincaré–Lefschetz pairing: a perfect-but-wrong `cup`/`μ` still yields a well-defined Wu
class that is DECOUPLED from the manifold's actual `w₂(W)`. Since `wuClass` is the `pairing`-dual
(`pairing = cup.compr₂ μ`) of `wuFunctional = μ ∘ sqOp`, `wuClass` depends on all three fields.
**Verdict: `sqOp` MUST be pinned (sharp exploit); `cup` and `μ` MUST ALSO be pinned (faithfulness —
so the datum's `wuW2` IS the manifold's `w₂`), and the honest cylinder data pin all three.** The
`μ`-pin inherits exactly the honesty bar of `RelFundClassDatum` already in-tree (its `gen`-family
honesty is the pre-existing `interiorPoint_hasEuclChart` obligation, NOT introduced here).

## Discrimination (both directions), all kernel-checked

* (a) **zeroSq route EXCLUDED**: `sqOpPinned23_zeroSq_iff` — a `zeroSq`-ed datum satisfies the pin
  IFF the honest `relSq² = 0` (the *honestly*-vanishing case); so wherever `relSq² ≠ 0` the F3
  exploit `WAdm.ofLefschetzNoWu` produces UN-pinnable data (`not_sqOpPinned23_ofLefschetzNoWu`), and
  no `CharPairWProviderPinned` can be built from bare duality on a genuine-Steenrod bordism. The
  shortcut becomes pin-satisfying exactly when it is harmless.
* (b) **honest cylinder data SATISFY the pin** (non-vacuity): every `ofRelFund14`/`23`-assembled
  datum is pinned (`ofRelFund14_pinned`), so in particular `cylinderP14`/`cylinderP23` are pinned
  (`cylinderP14_pinned`/`cylinderP23_pinned`) — the concrete witness.

## The consumption seam (item 3, STATEMENT LAYER only — not wired into the carrier)

`CharPairBorTiedPinned` refines a `CharPairBorTied` with pin certificates on its `P14`/`P23` copies;
`CharPairBorTiedPinned.wuFunctional23_honest` shows a pinned Bor's `(2,3)` Wu functional is the
honest `⟨relSq² ·, [W,∂W]⟩`, so its `hwu` (`wuW2 = 0`) is the genuine `w₂(W) = 0` condition, not a
free-`sqOp` artefact. The lead folds this into `CharPairBorTied` after the carrier lane merges.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusCharPairGeoRealizationGate
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderWu

open scoped Manifold
open SKEFTHawking.BordismTheory
open SKEFTHawking.PoincareLefschetzWu5
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzWuAssembly
open SKEFTHawking.SingularRelativeCup SKEFTHawking.SingularRelativeBockstein
open SKEFTHawking.SingularRelativeSteenrodSq2
open SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCharPairGeoRealizationGate
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderWu

namespace SKEFTHawking.PinPlusWAdmPinned

/-! ## §1. The per-field pin certificates -/

section Certificates

variable {X : TopCat} {S : Set X}

/-- **The `(1,4)` Steenrod pin**: the datum's `sqOp` IS the substrate relative `Sq¹`
(`relSq1 : H⁴(W,∂W) → H⁵(W,∂W)`, `n = 3`). -/
def SqOpPinned14 (P : LefschetzWuDatum X S 1 4 5) : Prop := P.sqOp = relSq1 (n := 3)

/-- **The `(2,3)` Steenrod pin**: the datum's `sqOp` IS the substrate relative `Sq²`
(`relSq2 : H³(W,∂W) → H⁵(W,∂W)`). -/
def SqOpPinned23 (P : LefschetzWuDatum X S 2 3 5) : Prop := P.sqOp = relSq2

/-- **The `(1,4)` cup pin**: the datum's `cup` IS the substrate relative cup product `relCupH14`. -/
def CupPinned14 (P : LefschetzWuDatum X S 1 4 5) : Prop := P.cup = relCupH14

/-- **The `(2,3)` cup pin**: the datum's `cup` IS the substrate relative cup product `relCupH23`. -/
def CupPinned23 (P : LefschetzWuDatum X S 2 3 5) : Prop := P.cup = relCupH23

/-- **The `μ` pin**: the datum's `μ` IS the relative fundamental-class functional `⟨·, [W,∂W]⟩` of a
genuine `RelFundClassDatum` (`cls` pinned by its own `restricts` field). -/
def MuPinned {k nk : ℕ} (P : LefschetzWuDatum X S k nk 5) : Prop :=
  ∃ D : RelFundClassDatum (m := 3) S, P.mu = D.mu

/-- **The pinned `(1,4)` Lefschetz–Wu datum**: `μ`, `cup`, `sqOp` are all the substrate operations. -/
structure LefschetzWuPinned14 (P : LefschetzWuDatum X S 1 4 5) : Prop where
  /-- `μ` is a genuine relative fundamental-class functional. -/
  muPin : MuPinned P
  /-- `cup` is the substrate relative cup product `relCupH14`. -/
  cupPin : CupPinned14 P
  /-- `sqOp` is the substrate relative `Sq¹` (`relSq1`). -/
  sqPin : SqOpPinned14 P

/-- **The pinned `(2,3)` Lefschetz–Wu datum**: `μ`, `cup`, `sqOp` are all the substrate operations. -/
structure LefschetzWuPinned23 (P : LefschetzWuDatum X S 2 3 5) : Prop where
  /-- `μ` is a genuine relative fundamental-class functional. -/
  muPin : MuPinned P
  /-- `cup` is the substrate relative cup product `relCupH23`. -/
  cupPin : CupPinned23 P
  /-- `sqOp` is the substrate relative `Sq²` (`relSq2`). -/
  sqPin : SqOpPinned23 P

end Certificates

/-! ## §2. Discrimination (a): the F3 `zeroSq` route is EXCLUDED wherever the honest Steenrod
square is nonzero. -/

section Discrimination

variable {X : TopCat} {S : Set X}

/-- **The `zeroSq` route satisfies the `(2,3)` Steenrod pin IFF the honest `relSq² = 0`.** Since
`(zeroSq P).sqOp = 0` definitionally, the pin `0 = relSq²` holds exactly when the substrate Steenrod
square itself vanishes — i.e. the F3 shortcut becomes pin-satisfying precisely in the *honestly*-
vanishing case, and NOWHERE else. -/
theorem sqOpPinned23_zeroSq_iff (P : LefschetzWuDatum X S 2 3 5) :
    SqOpPinned23 (LefschetzWuDatum.zeroSq P) ↔ (relSq2 : RelativeCohomology S 3 →ₗ[ZMod 2]
      RelativeCohomology S 5) = 0 :=
  eq_comm

/-- **The `zeroSq` route satisfies the `(1,4)` Steenrod pin IFF the honest `relSq¹ = 0`.** -/
theorem sqOpPinned14_zeroSq_iff (P : LefschetzWuDatum X S 1 4 5) :
    SqOpPinned14 (LefschetzWuDatum.zeroSq P) ↔ (relSq1 (n := 3) : RelativeCohomology S 4 →ₗ[ZMod 2]
      RelativeCohomology S 5) = 0 :=
  eq_comm

/-- Wherever the honest relative `Sq² ≠ 0`, a `zeroSq`-ed datum is NOT Steenrod-pinned. -/
theorem not_sqOpPinned23_zeroSq (P : LefschetzWuDatum X S 2 3 5)
    (h : (relSq2 : RelativeCohomology S 3 →ₗ[ZMod 2] RelativeCohomology S 5) ≠ 0) :
    ¬ SqOpPinned23 (LefschetzWuDatum.zeroSq P) :=
  fun hp => h ((sqOpPinned23_zeroSq_iff P).mp hp)

end Discrimination

/-! ## §3. Discrimination (b) / non-vacuity: every `ofRelFund`-assembled datum is pinned, so the
honest cylinder data are pinned. -/

section NonVacuity

variable {X : TopCat} {S : Set ↑X}

/-- **Every `ofRelFund14`-assembled datum is pinned** — `μ := D.mu`, `cup := relCupH14`,
`sqOp := relSq1` are all wired to the substrate by construction. The generic non-vacuity engine. -/
theorem ofRelFund14_pinned (D : RelFundClassDatum (m := 3) S)
    (findimAbs : FiniteDimensional (ZMod 2) (Cohomology X 1))
    (findimRel : FiniteDimensional (ZMod 2) (RelativeCohomology S 4))
    (nondeg : Function.Injective ⇑((relCupH14 (X := X) (S := S)).compr₂ D.mu))
    (dimeq : Module.finrank (ZMod 2) (Cohomology X 1)
           = Module.finrank (ZMod 2) (RelativeCohomology S 4)) :
    LefschetzWuPinned14 (LefschetzWuDatum.ofRelFund14 D findimAbs findimRel nondeg dimeq) :=
  ⟨⟨D, rfl⟩, rfl, rfl⟩

/-- **Every `ofRelFund23`-assembled datum is pinned.** -/
theorem ofRelFund23_pinned (D : RelFundClassDatum (m := 3) S)
    (findimAbs : FiniteDimensional (ZMod 2) (Cohomology X 2))
    (findimRel : FiniteDimensional (ZMod 2) (RelativeCohomology S 3))
    (nondeg : Function.Injective ⇑((relCupH23 (X := X) (S := S)).compr₂ D.mu))
    (dimeq : Module.finrank (ZMod 2) (Cohomology X 2)
           = Module.finrank (ZMod 2) (RelativeCohomology S 3)) :
    LefschetzWuPinned23 (LefschetzWuDatum.ofRelFund23 D findimAbs findimRel nondeg dimeq) :=
  ⟨⟨D, rfl⟩, rfl, rfl⟩

end NonVacuity

section CylinderWitness

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]

omit [Nonempty M] in
/-- **The honest cylinder `(1,4)` datum is pinned** (non-vacuity witness): `cylinderP14` is
`ofRelFund14 (cylinderDatum hcls) …`, whose `sqOp := relSq1`, `cup := relCupH14`, `μ := (cylinder
fundamental class functional)` are all substrate operations. -/
theorem cylinderP14_pinned
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
    LefschetzWuPinned14 (cylinderP14 hcls findimAbs findimRel nondeg dimeq) :=
  ofRelFund14_pinned (cylinderDatum hcls) findimAbs findimRel nondeg dimeq

omit [Nonempty M] in
/-- **The honest cylinder `(2,3)` datum is pinned** (non-vacuity witness). -/
theorem cylinderP23_pinned
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
    LefschetzWuPinned23 (cylinderP23 hcls findimAbs findimRel nondeg dimeq) :=
  ofRelFund23_pinned (cylinderDatum hcls) findimAbs findimRel nondeg dimeq

end CylinderWitness

/-! ## §4. `WAdmPinned` + `CharPairWProviderPinned` (spec item 2) and the provider-route
discrimination. -/

section Provider

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {k : WithTop ℕ∞}
variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]

/-- **The PINNED W-admissibility datum**: a `WAdm b` whose two Lefschetz–Wu data are pinned to the
substrate. This is the shape that IS a genuine `w₂(W) = 0` filter. -/
structure WAdmPinned {s t : SingularManifold PUnit k I} (b : Bordism (I.prod (𝓡∂ 1)) s t) where
  /-- the underlying (frozen-shape) W-admissibility datum. -/
  wadm : WAdm b
  /-- the `(1,4)` datum is substrate-pinned. -/
  pin14 : LefschetzWuPinned14 wadm.P14
  /-- the `(2,3)` datum is substrate-pinned. -/
  pin23 : LefschetzWuPinned23 wadm.P23

/-- **The PINNED W-admissibility provider**: supplies a `WAdmPinned` for every bordism. The honest
discharge target (wt3's rel-PD/Wu tower produces `ofRelFund`-assembled data, which `ofRelFund*_pinned`
certifies as pinned). -/
structure CharPairWProviderPinned (I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2))))
    [I.Boundaryless] (k : WithTop ℕ∞) : Type (u_1 + 1) where
  /-- pinned admissibility for every bordism between closed 4-manifolds. -/
  wadm : ∀ {s t : SingularManifold.{0} PUnit.{1} k I}
    (b : Bordism.{0} (I.prod (𝓡∂ 1)) s t), WAdmPinned b

/-- Forget the pins: a pinned provider yields an ordinary `CharPairWProvider`. -/
def CharPairWProviderPinned.toProvider (prov : CharPairWProviderPinned I k) :
    CharPairWProvider I k :=
  ⟨fun b => (prov.wadm b).wadm⟩

omit [I.Boundaryless] in
/-- **The F3 exploit route is UN-pinnable on genuine-Steenrod bordisms.** `WAdm.ofLefschetzNoWu`
(the engine behind `charPairWProviderOfDuality`) hands each bordism a `zeroSq`-ed `P23`, so it is
Steenrod-pinned only where the honest `relSq² = 0`. Hence no `WAdmPinned` — and no
`CharPairWProviderPinned` — can be assembled from bare Lefschetz-duality data on a bordism whose
`W` carries genuine `Sq²`. -/
theorem not_sqOpPinned23_ofLefschetzNoWu {s t : SingularManifold PUnit k I}
    {b : Bordism (I.prod (𝓡∂ 1)) s t}
    (P14 : LefschetzWuDatum (TopCat.of b.W) ((I.prod (𝓡∂ 1)).boundary b.W) 1 4 5)
    (P23 : LefschetzWuDatum (TopCat.of b.W) ((I.prod (𝓡∂ 1)).boundary b.W) 2 3 5)
    (h : relSq2 (X := TopCat.of b.W) (S := (I.prod (𝓡∂ 1)).boundary b.W) ≠ 0) :
    ¬ SqOpPinned23 ((WAdm.ofLefschetzNoWu P14 P23).P23) :=
  fun hp => h ((sqOpPinned23_zeroSq_iff P23).mp hp)

end Provider

/-! ## §5. The consumption seam (spec item 3, STATEMENT LAYER): `CharPairBorTiedPinned` and the
honest-`w₂` lemma. -/

section HonestWu

variable {X : TopCat} {S : Set X}

/-- **For a pinned `(2,3)` datum, its Wu functional is the HONEST one** — `μ ∘ relSq²`, the substrate
Steenrod square against the fundamental class. This is the crux of the pin's value: no free-`sqOp`
gaming, the Wu functional is `⟨relSq² ·, [W,∂W]⟩`. -/
theorem LefschetzWuPinned23.wuFunctional_eq {P : LefschetzWuDatum X S 2 3 5}
    (h : LefschetzWuPinned23 P) : wuFunctional P = P.mu.comp relSq2 := by
  show P.mu.comp P.sqOp = P.mu.comp relSq2
  rw [h.sqPin]

/-- **For a pinned `(1,4)` datum, its Wu functional is the honest `μ ∘ relSq¹`.** -/
theorem LefschetzWuPinned14.wuFunctional_eq {P : LefschetzWuDatum X S 1 4 5}
    (h : LefschetzWuPinned14 P) : wuFunctional P = P.mu.comp (relSq1 (n := 3)) := by
  show P.mu.comp P.sqOp = P.mu.comp (relSq1 (n := 3))
  rw [h.sqPin]

/-- **For a pinned `(2,3)` datum, the pairing defining its Wu class is the substrate cup pairing**
`relCupH23.compr₂ μ` — so `wuClass` is the genuine Lefschetz-dual, not a perfect-but-wrong pairing's
dual. -/
theorem LefschetzWuPinned23.pairing_eq {P : LefschetzWuDatum X S 2 3 5}
    (h : LefschetzWuPinned23 P) : pairing P = relCupH23.compr₂ P.mu := by
  show P.cup.compr₂ P.mu = relCupH23.compr₂ P.mu
  rw [h.cupPin]

/-- **For a pinned `(2,3)` datum, its Wu class is dual (under the substrate cup pairing) to the
honest Steenrod–Kronecker functional** `⟨relSq² ·, [W,∂W]⟩`. Combines the `sqOp` and `cup` pins:
both the functional AND the pairing that define `wuClass` are the actual substrate operations, so
the Wu class cannot be gamed by free `sqOp`/`cup`. -/
theorem LefschetzWuPinned23.wuClass_honest {P : LefschetzWuDatum X S 2 3 5}
    (h : LefschetzWuPinned23 P) : pairing P (wuClass P) = P.mu.comp relSq2 := by
  have hkey : pairing P (wuClass P) = wuFunctional P :=
    (Equiv.ofBijective _ (pairing_bijective P)).apply_symm_apply (wuFunctional P)
  rw [hkey, h.wuFunctional_eq]

end HonestWu

section Seam

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {k : WithTop ℕ∞}
variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]

/-- **The PINNED tied characteristic-pair bordism datum** (spec item 3): a `CharPairBorTied` whose
`P14`/`P23` item-1 copies are substrate-pinned. This is the refinement the lead folds into
`CharPairBorTied` after the carrier lane merges — either as extra fields or as this side certificate.
Stated here, NOT wired into the carrier (wt1's lane). -/
structure CharPairBorTiedPinned {s t : SingularManifold PUnit k I}
    (b : Bordism (I.prod (𝓡∂ 1)) s t) (σ : CharPairStr I s) (τ : CharPairStr I t) where
  /-- the underlying tied bordism datum. -/
  bor : CharPairBorTied b σ τ
  /-- its `(1,4)` Lefschetz–Wu datum is substrate-pinned. -/
  pin14 : LefschetzWuPinned14 bor.P14
  /-- its `(2,3)` Lefschetz–Wu datum is substrate-pinned. -/
  pin23 : LefschetzWuPinned23 bor.P23

/-- Forget the pins: a pinned tied Bor yields an ordinary `CharPairBorTied`. -/
def CharPairBorTiedPinned.toBor {s t : SingularManifold PUnit k I}
    {b : Bordism (I.prod (𝓡∂ 1)) s t} {σ : CharPairStr I s} {τ : CharPairStr I t}
    (β : CharPairBorTiedPinned b σ τ) : CharPairBorTied b σ τ :=
  β.bor

/-- **THE SEAM LEMMA — a pinned tied Bor's admissibility is the HONEST `w₂(W) = 0` condition.** The
`(2,3)` leg's Wu functional is `⟨relSq² ·, [W,∂W]⟩` (substrate Steenrod square against the
fundamental class), so `bor.hwu : wuW2 P14 P23 = 0` is a genuine `w₂(W)` vanishing — NOT a free-`sqOp`
artefact, and in particular NOT dischargeable by the F3 `zeroSq` route (which is un-pinnable wherever
`relSq² ≠ 0`, `not_sqOpPinned23_ofLefschetzNoWu`). This is the statement the lead folds into the
carrier: pinned `hwu` ⟺ honest `w₂ = 0`. -/
theorem CharPairBorTiedPinned.wuFunctional23_honest {s t : SingularManifold PUnit k I}
    {b : Bordism (I.prod (𝓡∂ 1)) s t} {σ : CharPairStr I s} {τ : CharPairStr I t}
    (β : CharPairBorTiedPinned b σ τ) :
    wuFunctional β.bor.P23 = β.bor.P23.mu.comp relSq2 :=
  β.pin23.wuFunctional_eq

/-- The pinned tied Bor still carries the frozen admissibility `wuW2 P14 P23 = 0` — now certified
honest by `wuFunctional23_honest`. -/
theorem CharPairBorTiedPinned.hwu {s t : SingularManifold PUnit k I}
    {b : Bordism (I.prod (𝓡∂ 1)) s t} {σ : CharPairStr I s} {τ : CharPairStr I t}
    (β : CharPairBorTiedPinned b σ τ) : wuW2 β.bor.P14 β.bor.P23 = 0 :=
  β.bor.hwu

end Seam

end SKEFTHawking.PinPlusWAdmPinned
