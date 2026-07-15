/-
# Phase 5q.H W-A arm 4 — THE PROVIDER-INHABITATION TRANSPORT (the zero-posit convergence brick)

The re-flipped carrier's `CharPairWProviderPerOp I k` (`PinPlusCharPairBorTethered`) is parameterized
by four W-admissibility fields — `cyl` (of `reflCylinder`), `doubling` (of `doublingBordism`), `mapCyl`
(the `mapCylinder` family), and `addClosure` (the `⊔`-closure). This module builds the TRANSPORT that
turns Track-2's concrete `CylinderWAdmPinned M` engine (data on the CONCRETE product cylinder
`cylW M = M × [0,1]` under `cylModel 2`) into that abstract-`I` provider — converting the carrier's
provider HYPOTHESIS into Track-2's named residuals.

## The identification (per op-family)

All three cylinder-type op bordisms share ONE carrier: `(reflCylinder s).W`, `(doublingBordism s).W`,
and `(mapCylinder φ hf).W` are ALL **defeq** to `cylW s.M = s.M × Set.Icc 0 1`. The only gap to
Track-2's `CylinderWAdmPinned s.M` data is the boundary SET: the abstract provider wants
`(I.prod (𝓡∂ 1)).boundary b.W`, while the engine produces data on `(cylModel 2).boundary (cylW s.M)`.
Both equal `Set.univ ×ˢ {⊥, ⊤}` by `boundary_product` (`I` and `𝓡 4` are BOTH boundaryless), so the
transport is a single **boundary-set-equality** transport of the pinned Lefschetz–Wu data — carrier
defeq, `S`-set propositional-equal, **instance-free** (no `T2`/`Nonempty` needed for the data; those
are the ENGINE's inputs, Track-2's job).

## The zero-posit convergence

`CylWAdmData s` is the concrete-cylinder residual bundle (`{P14, P23, pin14, pin23, hwu}` on
`(cylW s.M, (cylModel 2).boundary (cylW s.M))`) — statable for EVERY structured `s` with NO `T2`/
`Nonempty` instances (only `s.M`'s ambient `TopologicalSpace`/`ChartedSpace`/`CompactSpace`, all from
`SingularManifold`). Track-2's `CylinderWAdmPinned s.M` discharges it for a nice (`T2`, `Nonempty`,
connected, finite-Betti) `s.M` via `CylinderWAdmPinned.toCylWAdmData`. The transport
`CylWAdmData s → WAdmPinned (reflCylinder s)` (and the doubling / mapCylinder variants) is instance-
free, so `CharPairWProviderPerOp.ofCylinderEngine` reduces the carrier's abstract provider hypothesis
to `(∀ s, CylWAdmData s) + addClosure` — the concrete Track-2 residual set.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusCharPairBorTethered
import SKEFTHawking.PinPlusCylinderWAdmPinned

open scoped Manifold
open SKEFTHawking.BordismTheory
open SKEFTHawking.PoincareLefschetzWu5
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.PinPlusWAdmPinned
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCylinderWAdmPinned
open SKEFTHawking.PinPlusCharPairBorTethered

namespace SKEFTHawking.PinPlusCharPairWProviderTransport

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {k : WithTop ℕ∞}
variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]

/-! ## §1. The concrete-cylinder residual bundle `CylWAdmData s` (instance-free). -/

/-- **The concrete-cylinder W-admissibility residual bundle** for a structured `s`: the pinned
Lefschetz–Wu data on the CONCRETE product cylinder `cylW s.M = s.M × [0,1]` under `cylModel 2`. This
is exactly the `WAdmPinned`-shaped output of Track-2's `CylinderWAdmPinned s.M` engine, bundled as a
residual STATABLE FOR EVERY `s` (no `T2`/`Nonempty` — only the ambient instances every
`SingularManifold` carries). The transport (§3) moves it onto the abstract op bordisms. -/
structure CylWAdmData (s : SingularManifold.{0} PUnit.{1} k I) where
  /-- the concrete `(1,4)` Lefschetz–Wu datum on `(cylW s.M, ∂cylW s.M)`. -/
  P14 : LefschetzWuDatum (TopCat.of (cylW s.M)) ((cylModel 2).boundary (cylW s.M)) 1 4 5
  /-- the concrete `(2,3)` Lefschetz–Wu datum. -/
  P23 : LefschetzWuDatum (TopCat.of (cylW s.M)) ((cylModel 2).boundary (cylW s.M)) 2 3 5
  /-- the `(1,4)` datum is substrate-pinned. -/
  pin14 : LefschetzWuPinned14 P14
  /-- the `(2,3)` datum is substrate-pinned. -/
  pin23 : LefschetzWuPinned23 P23
  /-- the Wu obstruction vanishes. -/
  hwu : wuW2 P14 P23 = 0

/-- **The Track-2 plug-in bridge**: a `CylinderWAdmPinned s.M` (for a nice — `T2`, `Nonempty`,
connected, finite-Betti — `s.M`) yields the concrete residual bundle. This is where Track-2's engine
discharges the residual for the nice case. -/
def CylinderWAdmPinned.toCylWAdmData {s : SingularManifold.{0} PUnit.{1} k I}
    [T2Space s.M] [Nonempty s.M] (W : CylinderWAdmPinned s.M) : CylWAdmData s where
  P14 := W.P14
  P23 := W.P23
  pin14 := W.pin14
  pin23 := W.pin23
  hwu := W.hwu'

/-! ## §2. The generic boundary-set-equality transport of pinned Lefschetz–Wu data.

A `LefschetzWuDatum X S k nk d` is topological data on `(X, S)`; along a set-equality `S₁ = S₂` (same
carrier `X`) the datum and its pins/Wu-vanishing transport unchanged (`subst` collapses the rewrite). -/

section Transport
variable {X : TopCat}

/-- Transport a Lefschetz–Wu datum along a boundary-set equality (carrier fixed). -/
def datumTransport {S₁ S₂ : Set ↑X} (hS : S₁ = S₂) {a b c : ℕ}
    (P : LefschetzWuDatum X S₁ a b c) : LefschetzWuDatum X S₂ a b c := hS ▸ P

/-- The `(1,4)` pin survives the boundary-set transport. -/
theorem datumTransport_pin14 {S₁ S₂ : Set ↑X} (hS : S₁ = S₂)
    (P : LefschetzWuDatum X S₁ 1 4 5) (h : LefschetzWuPinned14 P) :
    LefschetzWuPinned14 (datumTransport hS P) := by
  subst hS; exact h

/-- The `(2,3)` pin survives the boundary-set transport. -/
theorem datumTransport_pin23 {S₁ S₂ : Set ↑X} (hS : S₁ = S₂)
    (P : LefschetzWuDatum X S₁ 2 3 5) (h : LefschetzWuPinned23 P) :
    LefschetzWuPinned23 (datumTransport hS P) := by
  subst hS; exact h

/-- The Wu-obstruction vanishing survives the boundary-set transport (both data moved together). -/
theorem datumTransport_hwu {S₁ S₂ : Set ↑X} (hS : S₁ = S₂)
    (P14 : LefschetzWuDatum X S₁ 1 4 5) (P23 : LefschetzWuDatum X S₁ 2 3 5)
    (h : wuW2 P14 P23 = 0) :
    wuW2 (datumTransport hS P14) (datumTransport hS P23) = 0 := by
  subst hS; exact h

end Transport

/-! ## §3. The per-op boundary identifications and the transports onto the abstract op bordisms. -/

/-- **The reflexive-cylinder boundary identification**: `∂cylW s.M` (concrete `cylModel 2`) equals the
abstract `(I.prod (𝓡∂ 1))`-boundary of `(reflCylinder s).W` — both are `univ ×ˢ {⊥, ⊤}` because `𝓡 4`
AND `I` are boundaryless (`boundary_product`). -/
theorem reflCylinder_boundary_eq (s : SingularManifold.{0} PUnit.{1} k I) :
    (cylModel 2).boundary (cylW s.M)
      = (I.prod (𝓡∂ 1)).boundary (reflCylinder s).W := by
  rw [cyl_boundary_eq]
  exact (boundary_product (I := I)).symm

/-- **Transport onto `reflCylinder`** — `(reflCylinder s).W = cylW s.M` (defeq), so the concrete
residual bundle IS the abstract `WAdmPinned` after the boundary-set transport. -/
def CylWAdmData.toReflCylinder {s : SingularManifold.{0} PUnit.{1} k I} (d : CylWAdmData s) :
    WAdmPinned (reflCylinder s) where
  wadm :=
    { P14 := datumTransport (reflCylinder_boundary_eq s) d.P14
      P23 := datumTransport (reflCylinder_boundary_eq s) d.P23
      hwu := datumTransport_hwu (reflCylinder_boundary_eq s) d.P14 d.P23 d.hwu }
  pin14 := datumTransport_pin14 (reflCylinder_boundary_eq s) d.P14 d.pin14
  pin23 := datumTransport_pin23 (reflCylinder_boundary_eq s) d.P23 d.pin23

/-- **The doubling boundary identification** — `(doublingBordism s).W = cylW s.M` (defeq). -/
theorem doublingBordism_boundary_eq (s : SingularManifold.{0} PUnit.{1} k I) :
    (cylModel 2).boundary (cylW s.M)
      = (I.prod (𝓡∂ 1)).boundary (doublingBordism s).W := by
  rw [cyl_boundary_eq]
  exact (boundary_product (I := I)).symm

/-- **Transport onto `doublingBordism`** — `(doublingBordism s).W = cylW s.M` (defeq), so the SAME
concrete residual bundle discharges the doubling op's admissibility (`WAdm` reads only `b.W`). -/
def CylWAdmData.toDoublingBordism {s : SingularManifold.{0} PUnit.{1} k I} (d : CylWAdmData s) :
    WAdmPinned (doublingBordism s) where
  wadm :=
    { P14 := datumTransport (doublingBordism_boundary_eq s) d.P14
      P23 := datumTransport (doublingBordism_boundary_eq s) d.P23
      hwu := datumTransport_hwu (doublingBordism_boundary_eq s) d.P14 d.P23 d.hwu }
  pin14 := datumTransport_pin14 (doublingBordism_boundary_eq s) d.P14 d.pin14
  pin23 := datumTransport_pin23 (doublingBordism_boundary_eq s) d.P23 d.pin23

/-- **The mapping-cylinder boundary identification** — `(mapCylinder φ hf).W = cylW s.M` (defeq). -/
theorem mapCylinder_boundary_eq {s t : SingularManifold.{0} PUnit.{1} k I}
    (φ : Diffeomorph I I s.M t.M k) (hf : t.f ∘ φ = s.f) :
    (cylModel 2).boundary (cylW s.M)
      = (I.prod (𝓡∂ 1)).boundary (mapCylinder φ hf).W := by
  rw [cyl_boundary_eq]
  exact (boundary_product (I := I)).symm

/-- **Transport onto `mapCylinder`** — `(mapCylinder φ hf).W = cylW s.M` (defeq, the SOURCE `s`'s
cylinder), so the source's concrete residual bundle discharges every `mapCylinder` op. -/
def CylWAdmData.toMapCylinder {s t : SingularManifold.{0} PUnit.{1} k I} (d : CylWAdmData s)
    (φ : Diffeomorph I I s.M t.M k) (hf : t.f ∘ φ = s.f) :
    WAdmPinned (mapCylinder φ hf) where
  wadm :=
    { P14 := datumTransport (mapCylinder_boundary_eq φ hf) d.P14
      P23 := datumTransport (mapCylinder_boundary_eq φ hf) d.P23
      hwu := datumTransport_hwu (mapCylinder_boundary_eq φ hf) d.P14 d.P23 d.hwu }
  pin14 := datumTransport_pin14 (mapCylinder_boundary_eq φ hf) d.P14 d.pin14
  pin23 := datumTransport_pin23 (mapCylinder_boundary_eq φ hf) d.P23 d.pin23

end

end SKEFTHawking.PinPlusCharPairWProviderTransport

/-! ## §4. THE ASSEMBLY — `CharPairWProviderPerOp.ofCylinderEngine`.

The zero-posit convergence point: the carrier's abstract provider hypothesis
`CharPairWProviderPerOp I k` is inhabited from the CONCRETE Track-2 residual set
`(∀ s, CylWAdmData s) + addClosure`. The three cylinder-type fields (`cyl`/`doubling`/`mapCyl`) are
ALL discharged from ONE `CylWAdmData s` per structured `s` (they share carrier `cylW s.M`), via the
instance-free boundary-set transports. The `addClosure` field — the genuine `⊔`-block-diagonal
admissibility on `b₁.W ⊕ b₂.W` — is NOT a cylinder and is carried as an explicit honest hypothesis
(the named residual: the disjoint-union Lefschetz–Wu assembly). -/

namespace SKEFTHawking.PinPlusCharPairBorTethered

open SKEFTHawking.BordismTheory
open SKEFTHawking.PinPlusWAdmPinned
open SKEFTHawking.PinPlusCharPairWProviderTransport

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {k : WithTop ℕ∞}
variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]

/-- **THE PROVIDER-INHABITATION ASSEMBLY** — a `CharPairWProviderPerOp I k` from the concrete
Track-2 residual set. The HONEST hypothesis row:

* `cylData : ∀ s, CylWAdmData s` — the concrete-cylinder residual bundle for every structured `s`
  (pinned Lefschetz–Wu data on `cylW s.M = s.M × [0,1]`). Discharged for a nice — `T2`, `Nonempty`,
  connected, finite-Betti — `s.M` by Track-2's `CylinderWAdmPinned.toCylWAdmData`. This single family
  feeds `cyl`, `doubling`, AND `mapCyl` (all three op bordisms share `W = cylW s.M`).
* `addClosure` — the `⊔`-block-diagonal admissibility `WAdmPinned b₁ → WAdmPinned b₂ →
  WAdmPinned (b₁.add b₂)` on `b₁.W ⊕ b₂.W` (NOT a cylinder; the disjoint-union Lefschetz–Wu assembly,
  a named Track-2 residual). -/
def CharPairWProviderPerOp.ofCylinderEngine
    (cylData : ∀ {s : SingularManifold.{0} PUnit.{1} k I}, CylWAdmData s)
    (addClosure : ∀ {s₁ t₁ s₂ t₂ : SingularManifold.{0} PUnit.{1} k I}
      {b₁ : Bordism (I.prod (𝓡∂ 1)) s₁ t₁} {b₂ : Bordism (I.prod (𝓡∂ 1)) s₂ t₂},
      WAdmPinned b₁ → WAdmPinned b₂ → WAdmPinned (b₁.add b₂)) :
    CharPairWProviderPerOp I k where
  cyl := fun {s} => (cylData (s := s)).toReflCylinder
  doubling := fun {s} => (cylData (s := s)).toDoublingBordism
  mapCyl := fun {_s _t} φ hf => (cylData).toMapCylinder φ hf
  addClosure := addClosure

end

end SKEFTHawking.PinPlusCharPairBorTethered
