/-
# Phase 5q.H (E1 CSC-PD tower) — the integral BOTTOM connecting-square vertical (reduced to its core)

Integral (`ZMod 2 → ℤ`) bottom analogue of `SingularOpenDualityMVConnSquareInt.subHomConnecting_openDuality_of_coreInt`,
mirroring the mod-2 `SingularConnSquareCloseNCBotApex.subHomConnecting_openDuality₀_colimit`. This is `hc₃` of the
integral PD BOTTOM-window five-lemma: the connecting vertical
  `subHomConnectingInt ∘ D_{U∪V} = D⁰_{U∩V} ∘ cscMvConnectingInt`
where the `U∩V` side lands in the bottom (`H₀`-valued) duality `openDuality₀Int` (not the general `openDuality`).

Like the general connecting square, the whole colimit/leg reduction is discharged here via
`DirectLimit.induction_on` + `openDuality_of` + `cscMvConnectingInt_of`; the remaining chain-level
cap-commutes-with-connecting brick is threaded as the per-`K` bottom core hypothesis `hcore₀` (= the bottom
instance of the deep torsion-safe `hcoreInt`, NOT a project axiom).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularOpenDualityMVConnSquareInt
import SKEFTHawking.SingularOpenDualityBotInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCompactlySupportedOpenInt
open SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularOpenDualityInt
open SKEFTHawking.SingularCSCMayerVietorisConnectingInt
open SKEFTHawking.SingularOpenDualityBotInt

namespace SKEFTHawking.SingularOpenDualityBotConnSquareInt

variable {X : TopCat} [T2Space ↑X]

/-- **The integral BOTTOM connecting square, reduced to its per-compact cycle core.** The colimit/leg
reduction of the bottom connecting-square vertical (`hc₃` of the bottom five-lemma), packaged as a deduction
from the per-`K` bottom cycle core `hcore₀`
(`subHomConnectingInt (legW K g) = D⁰_{U∩V} (legδInt K g)`). Mirrors the general `_of_coreInt`; the
degree-frame is shared (bottom, `m = 0`), so no `castChainInt` recast is needed. -/
theorem subHomConnecting_openDuality₀_of_coreInt {N : ℕ} {U V : Set ↑X}
    (hU : IsOpen U) (hV : IsOpen V)
    (z₀ : SingularChainInt X (N + 1 + 0 + 1)) (hz₀ : chainBoundary X (N + 1 + 0) z₀ = 0)
    (hcore₀ : ∀ (K : CompactsIn (U ∪ V)) (g : cohomGWInt (U ∪ V) (N + 1) K),
      SKEFTHawking.SingularSubHomologyMVInt.subHomConnectingInt U V hU hV 0
          (legW (k := N + 1) (m := 0) (hU.union hV) z₀ hz₀ K g)
        = openDuality₀Int (hU.inter hV) z₀ hz₀ (legδInt U V hU hV N K g))
    (α : CompactlySupportedCohomologyOpenInt (U ∪ V) (N + 1)) :
    SKEFTHawking.SingularSubHomologyMVInt.subHomConnectingInt U V hU hV 0
        (openDuality (k := N + 1) (m := 0) (hU.union hV) z₀ hz₀ α)
      = openDuality₀Int (hU.inter hV) z₀ hz₀ (cscMvConnectingInt U V hU hV N α) := by
  induction α using Module.DirectLimit.induction_on with
  | ih K g =>
    rw [openDuality_of, cscMvConnectingInt_of]
    exact hcore₀ K g

end SKEFTHawking.SingularOpenDualityBotConnSquareInt
