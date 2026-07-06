/-
# Phase 5q.H (E1 CSC-PD tower) — the integral connecting-square vertical (reduced to its cycle core)

Integral (`ZMod 2 → ℤ`) mirror of `SingularOpenDualityMVConnSquare`. The hard vertical of the integral
Poincaré-duality `5`-lemma ladder is the **connecting square**
  `subHomConnectingInt ∘ D_{U∪V} = D_{U∩V} ∘ cscMvConnectingInt`,
where `D` is the open integral PD cap map (`SingularOpenDualityInt.openDuality`), `cscMvConnectingInt` is
the integral compactly-supported-cohomology MV connecting map (raising the cohomology degree by one), and
`subHomConnectingInt` is the bottom-row homology MV connecting map.

This module supplies the degree-recast infrastructure `castChainInt` (irreducible, to keep the heavy
`Module.DirectLimit` colimit elaboration from whnf-ing through the `Eq.rec` and timing out) and reduces
the connecting square (for a general colimit class `γ`) to the **per-`K` cycle core** `hcore`
  `subHomConnectingInt (legW K g) = D_{U∩V} (legδInt K g)`
via `DirectLimit.induction_on` + `openDuality_of` + `cscMvConnectingInt_of`. Everything around that
`hcore` (the recasts, the colimit lift, the two `*_of` leg-readoffs) is discharged here; `hcore` itself is
the remaining chain-level cap-commutes-with-connecting brick (the integral analogue of the `L2` grind
`SingularConnSquareCloseNC.subHomConnecting_openDuality`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularSubHomologyMVInt
import SKEFTHawking.SingularOpenDualityInt
import SKEFTHawking.SingularCSCMayerVietorisConnectingInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCompactlySupportedOpenInt
open SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularOpenDualityInt
open SKEFTHawking.SingularCSCMayerVietorisConnectingInt

namespace SKEFTHawking.SingularOpenDualityMVConnSquareInt

variable {X : TopCat} [T2Space ↑X]

/-- A degree-recast of an integral singular chain (degree equality `e : a = b`). Marked irreducible so the
heavy `openDuality` colimit elaboration does not whnf through the underlying `Eq.rec` (which times out). -/
@[irreducible] def castChainInt {a b : ℕ} (e : a = b) (z : SingularChainInt X a) : SingularChainInt X b :=
  e ▸ z

omit [T2Space ↑X] in
theorem castChainInt_eq {a b : ℕ} (e : a = b) (z : SingularChainInt X a) :
    castChainInt e z = e ▸ z := by rw [castChainInt]

omit [T2Space ↑X] in
/-- A recast cycle is a cycle (in the recast degree). -/
theorem chainBoundary_castChainInt_eq_zero {a b : ℕ} (e : a + 1 = b + 1) (eb : a = b)
    (z : SingularChainInt X (a + 1)) (hz : chainBoundary X a z = 0) :
    chainBoundary X b (castChainInt e z) = 0 := by
  rw [castChainInt_eq]; subst eb; rw [show e = rfl from rfl]; simpa using hz

/-- **The integral connecting square, reduced to its per-compact cycle core.** The full colimit/leg
reduction of the connecting-square vertical, packaged as a deduction from the per-`K` cycle core `hcore`
(`subHomConnectingInt (legW K g) = D_{U∩V} (legδInt K g)`). The degree recasts, the colimit lift, and the
two `*_of` leg-readoffs are discharged here; `hcore` is the remaining chain-level cap-vs-connecting brick. -/
theorem subHomConnecting_openDuality_of_coreInt {N p : ℕ} {U V : Set ↑X} (hU : IsOpen U) (hV : IsOpen V)
    (z₀ : SingularChainInt X (N + p + 3)) (hz₀ : chainBoundary X (N + p + 2) z₀ = 0)
    (hcore : ∀ (K : CompactsIn (U ∪ V)) (g : cohomGWInt (U ∪ V) (N + 1) K),
      SKEFTHawking.SingularSubHomologyMVInt.subHomConnectingInt U V hU hV (p + 1)
          (legW (k := N + 1) (m := p + 1) (hU.union hV)
            (castChainInt (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
            (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z₀ hz₀) K g)
        = openDuality (k := N + 2) (m := p) (hU.inter hV)
            (castChainInt (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
            (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z₀ hz₀)
            (legδInt U V hU hV N K g))
    (γ : CompactlySupportedCohomologyOpenInt (U ∪ V) (N + 1)) :
    SKEFTHawking.SingularSubHomologyMVInt.subHomConnectingInt U V hU hV (p + 1)
        (openDuality (k := N + 1) (m := p + 1) (hU.union hV)
          (castChainInt (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
          (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z₀ hz₀) γ)
      = openDuality (k := N + 2) (m := p) (hU.inter hV)
          (castChainInt (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
          (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z₀ hz₀)
          (cscMvConnectingInt U V hU hV N γ) := by
  induction γ using Module.DirectLimit.induction_on with
  | ih K g =>
    rw [openDuality_of, cscMvConnectingInt_of]
    exact hcore K g

end SKEFTHawking.SingularOpenDualityMVConnSquareInt
