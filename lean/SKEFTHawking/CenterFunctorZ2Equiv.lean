/-
Phase 5s Wave 9 (session 2): Building the CenterFunctor equivalence for G = ℤ/2.

Extends `CenterFunctorZ2.lean` with the categorical infrastructure needed to
discharge the `H_CF1_center_functor` and `H_CF2_center_equivalence` hypotheses
(from `CenterFunctor.lean`) specialized to G = G2 = Multiplicative (ZMod 2).

## Scope

This module is the continuation of Phase 5s Wave 9's scaffold. Where
`CenterFunctorZ2.lean` built the 4 characters `chiTrivTriv` … `chiFlipSign`
as algebra homomorphisms `DG k G2 →ₐ[k] k` plus their `Module (DG k G2)`
wrappers and the `simpleRepModule` bundling, this module builds the
categorical bridge:

  `centerToRepZ2 : Center (VecG_Cat k G2) ⥤ ModuleCat (DG k G2)`

plus the companion inverse and the `Equivalence.ofFullyFaithfulEssSurj`
(or `Equivalence.mk`) assembly.

## References

- `CenterFunctorZ2.lean` — Wave 9 scaffold
- `VecGMonoidal.lean` — `MonoidalCategory (Center (VecG_Cat k G))` instance
  for `[Group G]` and `BraidedCategory` when `[CommGroup G]`
- `DrinfeldCenterBridge.lean` — `VecG_Cat`, `singleGraded`, the algebraic
  half-braiding ↔ D(G)-module bijection
- `CenterFunctor.lean` — `H_CF1_center_functor`, `H_CF2_center_equivalence`
- Deep research: `Lit-Search/Phase-5s/CenterFunctor Z2 finite matrix feasibility.md`
- Deep research: `Lit-Search/Phase-5s/Closing the Drinfeld center sorry stubs in Lean 4.md`
- Working state: `temporary/working-docs/phase5s_wave9_centerfunctor_z2_state.md`
-/

import Mathlib
import SKEFTHawking.CenterFunctorZ2
import SKEFTHawking.VecGMonoidal
import SKEFTHawking.CenterFunctor

open CategoryTheory MonoidalCategory

noncomputable section

namespace SKEFTHawking.CenterFunctorZ2Equiv

open SKEFTHawking SKEFTHawking.CenterFunctorZ2 SKEFTHawking.CenterFunctor

variable (k : Type) [CommRing k]

/-! ## 1. Underlying `VecG_Cat k G2` objects for the 4 toric anyons

Each toric anyon has an underlying Vec_G object (its "flux sector"):
  - trivTriv / trivSign → carrier concentrated at the identity e
  - flipTriv / flipSign → carrier concentrated at the generator a

The distinction between trivTriv vs trivSign (and flipTriv vs flipSign) is
in the *half-braiding*, not the underlying object. This matches the physics:
electric and fermionic excitations share the flux sector of vacuum/magnetic
respectively, but differ in their braiding with the other sectors. -/

/-- The k-module `k` concentrated at degree `d ∈ Additive G2`, zero elsewhere.
    This is a specialisation of `singleGraded` for the single-line module `k`
    and is the underlying object of each toric anyon. -/
def lineGraded (d : Additive G2) : VecG_Cat k G2 :=
  singleGraded k G2 d (ModuleCat.of k k)

/-- The identity element of `Additive G2`. Corresponds to `e = 1 : G2`. -/
abbrev eAdd : Additive G2 := Additive.ofMul e

/-- The generator of `Additive G2`. Corresponds to `a = Multiplicative.ofAdd 1`. -/
abbrev aAdd : Additive G2 := Additive.ofMul a

/-- The underlying `VecG_Cat` object of each toric anyon. The trivTriv and
    trivSign anyons both have carrier `k` concentrated at `eAdd`; the flipTriv
    and flipSign anyons both have carrier `k` concentrated at `aAdd`. The
    difference between the two "pairs" is encoded in the half-braiding, not
    the underlying VecG object. -/
def anyonObject : DZ2Simple → VecG_Cat k G2
  | .trivTriv => lineGraded k eAdd
  | .trivSign => lineGraded k eAdd
  | .flipTriv => lineGraded k aAdd
  | .flipSign => lineGraded k aAdd

/-- The "flux sector" of each anyon — the degree at which its underlying
    VecG_Cat object is supported. -/
def anyonFluxSector : DZ2Simple → Additive G2
  | .trivTriv => eAdd
  | .trivSign => eAdd
  | .flipTriv => aAdd
  | .flipSign => aAdd

/-- The anyon object is `lineGraded k` at the flux sector. -/
lemma anyonObject_eq (s : DZ2Simple) :
    anyonObject k s = lineGraded k (anyonFluxSector s) := by
  cases s <;> rfl

/-! ## 2. Module summary (session 2, intermediate)

This module is under active multi-session development. Current state:

  ✅ Session 1 (landed): CenterFunctorZ2.lean — 4 characters, 4 modules,
      simpleChi_injective, simpleRepModule (649 LOC, zero sorry).

  🔄 Session 2 (this module, in progress):
      ✅ `lineGraded`, `eAdd`, `aAdd` abbreviations
      ✅ `anyonObject` function DZ2Simple → VecG_Cat k G2
      ✅ `anyonFluxSector` projection
      ⏳ HalfBraiding data for each of the 4 anyons
      ⏳ `toricAnyon : DZ2Simple → Center (VecG_Cat k G2)` bundler
      ⏳ `centerToRepZ2` functor definition
      ⏳ Full + Faithful + EssSurj
      ⏳ Equivalence assembly
      ⏳ H_CF1 + H_CF2 discharge for G2

  See `temporary/working-docs/phase5s_wave9_centerfunctor_z2_state.md`
  for the full multi-session action plan, hypothesis tracker, and
  DISPROVED-approaches log. -/
theorem wave9_session2_intermediate_summary : True := trivial

end SKEFTHawking.CenterFunctorZ2Equiv

end
