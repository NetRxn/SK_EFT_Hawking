import Mathlib
import SKEFTHawking.SingularSubHomologyMV
import SKEFTHawking.SingularOpenDuality
import SKEFTHawking.SingularCSCMayerVietorisConnecting

/-!
# Phase 5q.F (w₂-foundation) — degree-recast infrastructure for the connecting-square vertical

The hard vertical of the Poincaré-duality `5`-lemma ladder is the **connecting square**
  `subHomConnecting ∘ D_{U∪V} = D_{U∩V} ∘ cscMvConnecting`,
where `D` is the open Poincaré-duality cap map (`SingularOpenDuality.openDuality`),
`cscMvConnecting` is the compactly-supported-cohomology MV connecting map
(`SingularCSCMayerVietorisConnecting.cscMvConnecting`, raising the cohomology degree by one), and
`subHomConnecting` is the bottom-row homology MV connecting map
(`SingularSubHomologyMV.subHomConnecting`).

The two `D` calls in that square cap **one** fundamental cycle `z₀` at **two different degree splits**
— `(k, m) = (N+1, p+1)` on the `U∪V` side (cohomology degree `N+1`, homology degree `p+2`) and
`(k, m) = (N+2, p)` on the `U∩V` side (cohomology degree `N+2`, homology degree `p+1`). The connecting
maps shift the cohomology degree up by one while leaving `k + m + 1` (`= N + p + 3`, the degree of `z₀`)
invariant. The two split degrees `N + 1 + (p + 1) + 1` and `N + 2 + p + 1` are *propositionally* equal to
`N + p + 3` but **not** definitionally so, and neither equals the other definitionally; a single `z₀` must
therefore be degree-recast to feed each `openDuality` call.

A bare `Eq.rec` recast (`e ▸ z₀`) fed into `openDuality` makes the heavy `Module.DirectLimit` colimit
elaboration whnf through the cast and time out. This module provides an **irreducible** recast
`castChain`, whose unfolding lemma `castChain_eq` and cycle-preservation lemma
`chainBoundary_castChain_eq_zero` are the interface used to state the connecting square without the
elaboration blowing up.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCompactlySupportedOpen
  SKEFTHawking.SingularOpenDuality SKEFTHawking.SingularSubsetHomology

namespace SKEFTHawking.SingularOpenDualityMVConnSquare

variable {X : TopCat} [T2Space ↑X]

/-- A degree-recast of a singular chain (degree equality `e : a = b`). Marked irreducible so the heavy
`openDuality` colimit elaboration does not whnf through the underlying `Eq.rec` (which times out). -/
@[irreducible] def castChain {a b : ℕ} (e : a = b) (z : SingularChain X a) : SingularChain X b :=
  e ▸ z

omit [T2Space ↑X] in
/-- Unfolding `castChain` (the irreducible degree-recast) to the underlying `Eq.rec`. -/
theorem castChain_eq {a b : ℕ} (e : a = b) (z : SingularChain X a) :
    castChain e z = e ▸ z := by rw [castChain]

omit [T2Space ↑X] in
/-- A recast cycle is a cycle: `chainBoundary` of `castChain e z` at the matching shifted degree
vanishes whenever `z` is a cycle. The boundary obligation for each `openDuality` call in the connecting
square (the recast `z₀` is still a cycle, in the recast degree). -/
theorem chainBoundary_castChain_eq_zero {a b : ℕ} (e : a + 1 = b + 1) (eb : a = b)
    (z : SingularChain X (a + 1)) (hz : chainBoundary X a z = 0) :
    chainBoundary X b (castChain e z) = 0 := by
  rw [castChain_eq]; subst eb; rw [show e = rfl from rfl]; simpa using hz

/-- **The connecting square, reduced to its per-compact cycle core.** This is the full colimit/leg
reduction of the connecting-square vertical
  `subHomConnecting ∘ D_{U∪V} = D_{U∩V} ∘ cscMvConnecting`
— the `Module.DirectLimit.induction_on` over the colimit class `γ` plus the colimit computation rules
`openDuality_of` and `cscMvConnecting_of` — packaged as a deduction from the **per-`K` cycle core**
`hcore`:
  `subHomConnecting (legW K g) = D_{U∩V} (legδ K g)`   (`g` a `K`-stage class).
`hcore` is exactly the cap-commutes-with-the-connecting computation (the chain-level intertwining of the
absolute-homology MV connecting `mvDelta` of `sub(U∪V)` with the relative-cohomology MV connecting
`relCohomMvConnecting`, through the cap with the per-`K` fundamental cycle) — the remaining
chain-level brick. Everything *around* that core (the degree recasts, the colimit lift, the two
`*_of` leg-readoffs) is discharged here. -/
theorem subHomConnecting_openDuality_of_core {N p : ℕ} {U V : Set ↑X} (hU : IsOpen U) (hV : IsOpen V)
    (z₀ : SingularChain X (N + p + 3)) (hz₀ : chainBoundary X (N + p + 2) z₀ = 0)
    (hcore : ∀ (K : SingularCompactsInOpen.CompactsIn (U ∪ V))
        (g : cohomGW (U ∪ V) (N + 1) K),
      SKEFTHawking.SingularSubHomologyMV.subHomConnecting U V hU hV (p + 1)
          (SKEFTHawking.SingularOpenDuality.legW (k := N + 1) (m := p + 1) (hU.union hV)
            (castChain (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
            (chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀) K g)
        = openDuality (k := N + 2) (m := p) (hU.inter hV)
            (castChain (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
            (chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
            (SKEFTHawking.SingularCSCMayerVietorisConnecting.legδ U V hU hV N K g))
    (γ : CompactlySupportedCohomologyOpen (U ∪ V) (N + 1)) :
    SKEFTHawking.SingularSubHomologyMV.subHomConnecting U V hU hV (p + 1)
        (openDuality (k := N + 1) (m := p + 1) (hU.union hV)
          (castChain (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
          (chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀) γ)
      = openDuality (k := N + 2) (m := p) (hU.inter hV)
          (castChain (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
          (chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
          (SKEFTHawking.SingularCSCMayerVietorisConnecting.cscMvConnecting U V hU hV N γ) := by
  induction γ using Module.DirectLimit.induction_on with
  | ih K g =>
    rw [openDuality_of, SingularCSCMayerVietorisConnecting.cscMvConnecting_of]
    exact hcore K g

end SKEFTHawking.SingularOpenDualityMVConnSquare
