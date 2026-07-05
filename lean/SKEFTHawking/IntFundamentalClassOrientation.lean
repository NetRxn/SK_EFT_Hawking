/-
# Phase 5q.H · E1 — the integral fundamental class `[M] : H₄(M;ℤ)` as an orientation datum

Substrate-G foundation brick (Option-A from-scratch). This module isolates the **single
orientation-dependent input** that `SingularHomologyInt.intFundamentalClassOfHomology` (brick 6)
consumes — the integral fundamental class `[M] : Homology(M;ℤ) 4` — as a *disclosed tracked datum*
`IntOrientation X`, with the honest discharge path spelled out, and it lands the **provable
partials**: the ℤ→ℤ/2 chain reduction bridge `redChain`/`redHomology` (kernel-pure, unconditional)
and the mod-2 compatibility that ties the integral `[M]` to the ON-MAIN mod-2 fundamental class
(`SingularFundamentalClass.fundamentalClass`), which needs no orientation.

## Why this is the genuine new content over mod-2

The on-main mod-2 blueprint (`SingularFundamentalClass`, `SingularFundamentalClassExist`) builds a
`ZMod 2` fundamental class `[M]₂ ∈ H₄(M;ℤ/2)` UNCONDITIONALLY — `hasFundClass_univ` glues local
generators over a chart-ball cover with NO sign/orientation choice, because over the field `ℤ/2`
every local homology group `H₄(M | x; ℤ/2) ≅ ℤ/2` has a *unique* generator (`1`), so the union step
(`hasFundClass_union`) closes by `x + x = 0` (`ZModModule.add_self`).

Over ℤ the local groups are `H₄(M | x; ℤ) ≅ ℤ` with **two** generators `±1`; gluing across chart
overlaps forces a *coherent* choice of local generators — the orientation local system being trivial
plus a global section. That coherence is EXACTLY the extra datum `[M] ∈ H₄(M;ℤ)` carries over `[M]₂`.
It requires an integral relative/local-homology tower (`H₄(M, M∖x; ℤ) ≅ ℤ`) which is absent from both
Mathlib and this project's on-main substrate (the on-main homology/Kronecker tower is entirely over
`ZMod 2`). So the orientation is the community-scale residual, carried here as ONE structure field.

## What is proved here (kernel-pure, unconditional — NOT part of the disclosed datum)

* `redChain X n : SingularChainInt X n →+ SingularHomologyMod2.SingularChain X n` — the pointwise
  `Int.cast : ℤ → ZMod 2` reduction of integral chains (both models are `Finsupp` over the SAME
  singular-simplex basis; the dual of the on-main cochain bridge `IntersectionFormEvenInt.redC`).
* `redChain_boundaryBasis`, `redChain_chainBoundary` — the reduction commutes with `∂`
  (the integral alternating sign `(-1)ⁱ` reduces to `1` in char 2, matching the mod-2 boundary).
* `redHomology X n : Homology(X;ℤ) n →+ SingularHomologyMod2.Homology X n` — the induced map on
  homology (a chain map descends to homology).

## The disclosed datum

`IntOrientation X` carries the coherent-orientation-produced class `fundClass : Homology X 4` (the
`[M]`), and the mod-2 compatibility `redCompat : redHomology X 4 fundClass = [M]₂` tying it to the
on-main mod-2 fundamental class. The bridge `intFundamentalClassOfIntOrientation` discharges the
`intFundamentalClassOfHomology` input directly from an `IntOrientation`. Registered in
`HYPOTHESIS_REGISTRY` as `intOrientation_datum`.

All proofs kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/
`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularHomologyInt
import SKEFTHawking.SingularFundamentalClassExist

namespace SKEFTHawking.SingularHomologyInt

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt

variable {X : TopCat}

/-! ## §1. The ℤ→ℤ/2 chain reduction bridge (unconditional, kernel-pure) -/

/-- **The ℤ→ℤ/2 reduction of integral singular chains.** Both `SingularChainInt X n = (simplices →₀ ℤ)`
and the on-main mod-2 `SingularHomologyMod2.SingularChain X n = (simplices →₀ ZMod 2)` are `Finsupp`
over the SAME singular-simplex basis; this is the pointwise cast `Int.cast : ℤ → ZMod 2`, as an
additive monoid hom. The homological dual of the cochain reduction `IntersectionFormEvenInt.redC`. -/
noncomputable def redChain (X : TopCat) (n : ℕ) :
    SingularChainInt X n →+ SKEFTHawking.SingularHomologyMod2.SingularChain X n :=
  Finsupp.mapRange.addMonoidHom (Int.castAddHom (ZMod 2))

@[simp] theorem redChain_single (X : TopCat) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) (a : ℤ) :
    redChain X n (Finsupp.single σ a) = Finsupp.single σ (a : ZMod 2) := by
  rw [redChain, Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_single]
  rfl

/-- **The reduction sends the integral boundary of a basis simplex to the mod-2 boundary.** The
integral `boundaryBasis = ∑ᵢ (-1)ⁱ • single (face i σ) 1`; each sign `(-1)ⁱ` casts to `1` in `ZMod 2`,
so the reduction is `∑ᵢ single (face i σ) 1 = SingularHomologyMod2.boundaryBasis`. -/
theorem redChain_boundaryBasis (X : TopCat) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) :
    redChain X n (boundaryBasis X n σ)
      = SKEFTHawking.SingularHomologyMod2.boundaryBasis X n σ := by
  rw [boundaryBasis, SingularHomologyMod2.boundaryBasis, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_zsmul, redChain_single, Int.cast_one, Finsupp.smul_single]
  congr 1
  rw [zsmul_eq_mul, mul_one]
  push_cast
  rw [show (-1 : ZMod 2) = 1 by decide, one_pow]

/-- **The reduction is a chain map** — it intertwines the integral and mod-2 boundaries:
`redChain ∘ ∂_ℤ = ∂_{ℤ/2} ∘ redChain`. Proved on the `Finsupp` basis via `redChain_boundaryBasis`
and additivity (`Finsupp` linearity of both boundaries + additivity of `redChain`). -/
theorem redChain_chainBoundary (X : TopCat) (n : ℕ) (c : SingularChainInt X (n + 1)) :
    redChain X n (chainBoundary X n c)
      = SKEFTHawking.SingularHomologyMod2.chainBoundary X n (redChain X (n + 1) c) := by
  induction c using Finsupp.induction with
  | zero => simp
  | single_add σ a c ha hc ih =>
    rw [map_add, map_add, map_add, map_add, ih]
    congr 1
    rw [chainBoundary_single_smul, map_zsmul, redChain_boundaryBasis, redChain_single,
      SingularHomologyMod2.chainBoundary_single_smul]
    rw [Int.cast_smul_eq_zsmul]

/-- **The reduction maps integral cycles to mod-2 cycles.** A chain map preserves cycles:
`∂_{ℤ/2}(redChain z) = redChain(∂_ℤ z) = redChain 0 = 0`. -/
theorem redChain_mem_cycles (X : TopCat) (n : ℕ) {z : SingularChainInt X n}
    (hz : z ∈ cycles X n) : redChain X n z ∈ SKEFTHawking.SingularHomologyMod2.cycles X n := by
  cases n with
  | zero => exact Submodule.mem_top
  | succ m =>
    show SKEFTHawking.SingularHomologyMod2.chainBoundary X m (redChain X (m + 1) z) = 0
    rw [← redChain_chainBoundary]
    have : chainBoundary X m z = 0 := hz
    rw [this, map_zero]

/-- **The reduction maps integral boundaries to mod-2 boundaries.** `redChain(∂_ℤ c) = ∂_{ℤ/2}(redChain c)`
is a boundary. -/
theorem redChain_mem_boundaries (X : TopCat) (n : ℕ) {b : SingularChainInt X n}
    (hb : b ∈ boundaries X n) : redChain X n b ∈ SKEFTHawking.SingularHomologyMod2.boundaries X n := by
  obtain ⟨c, hc⟩ := hb
  refine ⟨redChain X (n + 1) c, ?_⟩
  rw [← redChain_chainBoundary, hc]

/-- **The reduction restricted to cycles**, `redCyclesHom X n : cycles(X;ℤ) n →+ cycles(X;ℤ/2) n`,
using `redChain_mem_cycles`. -/
noncomputable def redCyclesHom (X : TopCat) (n : ℕ) :
    (cycles X n) →+ (SKEFTHawking.SingularHomologyMod2.cycles X n) where
  toFun z := ⟨redChain X n z.1, redChain_mem_cycles X n z.2⟩
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

/-- **The reduction descends to homology**, `redHomology X n : Hₙ(X;ℤ) →+ Hₙ(X;ℤ/2)`. A chain map
sends cycles to cycles (`redCyclesHom`) and boundaries to boundaries (`redChain_mem_boundaries`), so it
descends to the quotient `cycles / boundaries`. This is the unconditional ℤ→ℤ/2 comparison map on
homology, the homological dual of the on-main cochain reduction bridge. -/
noncomputable def redHomology (X : TopCat) (n : ℕ) :
    Homology X n →+ SKEFTHawking.SingularHomologyMod2.Homology X n :=
  QuotientAddGroup.lift _
    ((QuotientAddGroup.mk' _).comp (redCyclesHom X n).toIntLinearMap.toAddMonoidHom) (by
      rintro ⟨z, hz⟩ hmem
      rw [AddMonoidHom.mem_ker]
      exact (QuotientAddGroup.eq_zero_iff _).mpr (redChain_mem_boundaries X n hmem))

/-- **`redHomology` on a homology class** — `redHomology [z] = [redChain z]` (the reduction of the
class of a cycle `z` is the class of its reduced cycle). The computation rule for the comparison map. -/
@[simp] theorem redHomology_mk (X : TopCat) (n : ℕ) (z : cycles X n) :
    redHomology X n (Homology.mk X n z)
      = SKEFTHawking.SingularHomologyMod2.Homology.mk X n (redCyclesHom X n z) :=
  rfl

/-! ## §2. The integral orientation datum `[M] : H₄(M;ℤ)` (disclosed) -/

/-- **The integral orientation datum of a closed charted 4-manifold `M`.**

This carries the SINGLE orientation-dependent input the integral intersection form needs — the integral
fundamental class `[M] ∈ H₄(M;ℤ)` — as a disclosed field `fundClass`, together with the **mod-2
compatibility** `redCompat` that ties it to the ON-MAIN mod-2 fundamental class
`SingularFundamentalClass.fundamentalClass` (which needs no orientation, being ℤ/2-valued).

**Why disclosed, not constructed:** the mod-2 `[M]₂` is built UNCONDITIONALLY on main
(`hasFundClass_univ`), because over the field `ℤ/2` each local group `H₄(M|x;ℤ/2) ≅ ℤ/2` has a unique
generator, so gluing needs no sign choice. Over ℤ the local groups are `H₄(M|x;ℤ) ≅ ℤ` with two
generators `±1`; a global class exists only when the local generators can be chosen **coherently across
overlaps** — the trivialisation of the orientation local system plus a global section, i.e. an
orientation of `M`. That coherence requires an integral relative/local-homology tower
(`H₄(M, M∖x; ℤ) ≅ ℤ`) which is ABSENT from Mathlib and this project's on-main substrate (the on-main
homology/Kronecker tower is entirely over `ZMod 2`); it is the community-scale residual.

**Discharge path** (mirrors the on-main mod-2 tower, adding ℤ-orientation coherence): build integral
relative homology `RelativeHomologyInt Kᶜ n` + the local iso `H₄(M|x;ℤ) ≅ ℤ`, define
`restrictsToGeneratorInt`/`hasFundClassInt` with a COHERENT generator choice (orientation), replay
`hasFundClass_chartBall`/`_union`/`_biUnion`/`_univ` where the union step now matches the two local `±1`
generators via the orientation (the ℤ/2 collapse `x + x = 0` is replaced by an honest sign match), and
extract `fundClass`. The `redCompat` field then holds by naturality of the ℤ→ℤ/2 reduction on the
local-generator condition (`redChain`/`redHomology` here provide the homology-level comparison map).

The mod-2 compatibility is what makes this datum FALSIFIABLE and non-vacuous: `fundClass` is not an
arbitrary `H₄(M;ℤ)` element — its reduction must equal the genuine mod-2 `[M]₂`, so it lies over the
canonical mod-2 orientation class. Registered as `intOrientation_datum` in `HYPOTHESIS_REGISTRY`. -/
structure IntOrientation (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] where
  /-- The integral fundamental class `[M] ∈ H₄(M;ℤ)`, produced by a coherent orientation of `M`. -/
  fundClass : Homology (TopCat.of M) 4
  /-- **Mod-2 compatibility**: the ℤ→ℤ/2 reduction of the integral `[M]` is the on-main mod-2 fundamental
  class `[M]₂` (`SingularFundamentalClass.fundamentalClass`, orientation-free). This ties the disclosed
  integral orientation to the constructed mod-2 orientation, so `fundClass` is not a free `H₄(M;ℤ)`
  element but the integral lift of the canonical class. -/
  redCompat : redHomology (TopCat.of M) 4 fundClass
    = SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := M)

/-- **The orientation datum discharges the `intFundamentalClassOfHomology` input.** From an
`IntOrientation M` we obtain the integral fundamental class `fundClass : Homology (TopCat.of M) 4`,
exactly the `[M]` that `intFundamentalClassOfHomology` consumes to build the `IntFundamentalClass` /
integral intersection-form evaluation functional. So the entire `intFundamentalClass_eval_datum` chain
(the ℤ-valued intersection form `interFormInt` + its symmetry) is discharged the moment an
`IntOrientation M` is supplied — its ONE unproved input is the disclosed orientation coherence. -/
noncomputable def intFundamentalClassOfIntOrientation {M : Type} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (o : IntOrientation M) : IntFundamentalClass (TopCat.of M) :=
  intFundamentalClassOfHomology o.fundClass

/-- **The discharged evaluation is `⟨·, [M]⟩` against the oriented fundamental class.** Confirms the
orientation datum feeds the integral Kronecker pairing directly (no mod-2 shortcut over ℤ). -/
@[simp] theorem intFundamentalClassOfIntOrientation_eval {M : Type} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (o : IntOrientation M) (ω : Cohomology (TopCat.of M) 4) :
    (intFundamentalClassOfIntOrientation o).eval ω = kroneckerHInt 4 ω o.fundClass :=
  rfl

/-- **The mod-2 shadow of the oriented fundamental class is the on-main mod-2 `[M]₂`.** The provable
partial: unpacking `redCompat`, the ℤ→ℤ/2 reduction of the integral orientation's `[M]` is exactly the
orientation-free mod-2 fundamental class. This is the compatibility the discharge's `redCompat` field
will satisfy by naturality; here it is the immediate consequence for any supplied datum. -/
theorem intOrientation_redHomology_fundClass {M : Type} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] (o : IntOrientation M) :
    redHomology (TopCat.of M) 4 o.fundClass
      = SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := M) :=
  o.redCompat

end SKEFTHawking.SingularHomologyInt
