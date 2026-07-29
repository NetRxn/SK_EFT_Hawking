/-
# Phase 5q.H (E1 CSC-PD tower) — the integral BOTTOM-window Mayer–Vietoris five-lemma

Integral (`ZMod 2 → ℤ`) mirror of `SingularConnSquareCloseNCBotApex.openDuality_union_bijective_bot`. The
`(3,0)`-center step of the integral Poincaré-duality open-cover induction: bijectivity of the union duality
`D_{U∪V} : Hᵏ⁺¹_c(U∪V;ℤ) → H₁(sub (U∪V);ℤ)` from bijectivity on the pieces, via the Mathlib five-lemma on
the Mayer–Vietoris ladder — top row the compactly-supported-cohomology MV LES, bottom row the sub-homology
MV LES — glued by the four commuting duality squares.

All four squares are now integral: `hc₁`/`hc₂` = the generic Δ/Σ squares (`subHomDiagInt_openDuality` /
`subHomSumInt_openDuality`, `SingularOpenDualityMVSquareInt`), `hc₃` = the bottom connecting square
(`subHomConnecting_openDuality₀_of_coreInt`, threading the per-`K` bottom core `hcore₀`), `hc₄` = the bottom
Δ square (`subHomDiagInt_openDuality₀`, `SingularOpenDualityBotNatInt`). Both LES-exactness rows are the
already-built `cscMv_exact_*Int` + `subHom_exact_*Int`. The deep torsion-safe `hcoreInt` enters ONLY through
`hcore₀`, threaded as a hypothesis — no project axiom.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularOpenDualityBotNatInt
import SKEFTHawking.SingularOpenDualityBotConnSquareInt
import SKEFTHawking.SingularCSCMayerVietorisMiddleInt
import SKEFTHawking.SingularCSCMayerVietorisConnExactInt
import SKEFTHawking.SingularCSCMayerVietorisSumExactInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCompactlySupportedOpenInt
open SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularOpenDualityInt
open SKEFTHawking.SingularCSCMayerVietorisInt
open SKEFTHawking.SingularCSCMayerVietorisConnectingInt
open SKEFTHawking.SingularCSCMayerVietorisMiddleInt
open SKEFTHawking.SingularCSCMayerVietorisConnExactInt
open SKEFTHawking.SingularCSCMayerVietorisSumExactInt
open SKEFTHawking.SingularSubHomologyMVInt
open SKEFTHawking.SingularOpenDualityMVSquareInt
open SKEFTHawking.SingularOpenDualityBotInt
open SKEFTHawking.SingularOpenDualityBotNatInt
open SKEFTHawking.SingularOpenDualityBotConnSquareInt

namespace SKEFTHawking.SingularOpenDualityBotFiveLemmaInt

variable {X : TopCat} [T2Space ↑X]

/-- **The integral bottom-window MV five-lemma step**: bijectivity of `D_{U∪V}` at the `(3,0)`-center
from the piece bijectivities + the per-`K` bottom connecting core `hcore₀`. Threads `hcore₀` (the bottom
instance of the deep `hcoreInt`) as a hypothesis; NO project axiom. -/
theorem openDuality_union_bijective_botInt {N : ℕ} {U V : Set ↑X}
    (hU : IsOpen U) (hV : IsOpen V)
    (z₀ : SingularChainInt X (N + 1 + 0 + 1)) (hz₀ : chainBoundary X (N + 1 + 0) z₀ = 0)
    (hcore₀ : ∀ (K : CompactsIn (U ∪ V)) (g : cohomGWInt (U ∪ V) (N + 1) K),
      subHomConnectingInt U V hU hV 0 (legW (k := N + 1) (m := 0) (hU.union hV) z₀ hz₀ K g)
        = -openDuality₀Int (hU.inter hV) z₀ hz₀ (legδInt U V hU hV N K g))
    (hDI : Function.Surjective (openDuality (k := N + 1) (m := 0) (hU.inter hV) z₀ hz₀))
    (hDU : Function.Bijective (openDuality (k := N + 1) (m := 0) hU z₀ hz₀))
    (hDV : Function.Bijective (openDuality (k := N + 1) (m := 0) hV z₀ hz₀))
    (hD0I : Function.Bijective (openDuality₀Int (hU.inter hV) z₀ hz₀))
    (hD0U : Function.Injective (openDuality₀Int hU z₀ hz₀))
    (hD0V : Function.Injective (openDuality₀Int hV z₀ hz₀)) :
    Function.Bijective (openDuality (k := N + 1) (m := 0) (hU.union hV) z₀ hz₀) := by
  have hc₁ : (subHomDiagInt U V (0 + 1)).comp
        (openDuality (k := N + 1) (m := 0) (hU.inter hV) z₀ hz₀)
      = ((openDuality (k := N + 1) (m := 0) hU z₀ hz₀).prodMap
          (openDuality (k := N + 1) (m := 0) hV z₀ hz₀)).comp (cscMvDiagInt U V (N + 1)) := by
    refine LinearMap.ext fun α => ?_
    simp only [LinearMap.comp_apply, LinearMap.prodMap_apply, cscMvDiagInt, LinearMap.prod_apply,
      Function.prod_def]
    exact subHomDiagInt_openDuality (k := N + 1) (m := 0) hU hV z₀ hz₀ α
  have hc₂ : (subHomSumInt U V (0 + 1)).comp
        ((openDuality (k := N + 1) (m := 0) hU z₀ hz₀).prodMap
          (openDuality (k := N + 1) (m := 0) hV z₀ hz₀))
      = (openDuality (k := N + 1) (m := 0) (hU.union hV) z₀ hz₀).comp
          (cscMvSumInt U V (N + 1)) := by
    refine LinearMap.ext fun p => ?_
    simp only [LinearMap.comp_apply, LinearMap.prodMap_apply]
    exact (subHomSumInt_openDuality (k := N + 1) (m := 0) hU hV z₀ hz₀ p.1 p.2).symm
  -- the ANTI-commuting square (the ℤ bot sign): absorb the −1 into the CSC-row connecting
  -- (`ker`/`range` are negation-invariant, so the row exactness transports)
  have hc₃ : (subHomConnectingInt U V hU hV 0).comp
        (openDuality (k := N + 1) (m := 0) (hU.union hV) z₀ hz₀)
      = (openDuality₀Int (hU.inter hV) z₀ hz₀).comp (-cscMvConnectingInt U V hU hV N) := by
    refine LinearMap.ext fun α => ?_
    simp only [LinearMap.comp_apply, LinearMap.neg_apply, map_neg]
    exact subHomConnecting_openDuality₀_of_coreInt hU hV z₀ hz₀ hcore₀ α
  have hc₄ : (subHomDiagInt U V 0).comp (openDuality₀Int (hU.inter hV) z₀ hz₀)
      = ((openDuality₀Int hU z₀ hz₀).prodMap
          (openDuality₀Int hV z₀ hz₀)).comp (cscMvDiagInt U V (N + 2)) := by
    refine LinearMap.ext fun α => ?_
    simp only [LinearMap.comp_apply, LinearMap.prodMap_apply, cscMvDiagInt, LinearMap.prod_apply,
      Function.prod_def]
    exact subHomDiagInt_openDuality₀ hU hV z₀ hz₀ α
  have hi₂ : Function.Bijective
      ⇑((openDuality (k := N + 1) (m := 0) hU z₀ hz₀).prodMap
        (openDuality (k := N + 1) (m := 0) hV z₀ hz₀)) := by
    rw [LinearMap.coe_prodMap]
    exact hDU.prodMap hDV
  have hi₅ : Function.Injective
      ⇑((openDuality₀Int hU z₀ hz₀).prodMap
        (openDuality₀Int hV z₀ hz₀)) := by
    rw [LinearMap.coe_prodMap]
    exact hD0U.prodMap hD0V
  -- row exactness transports across the negated connecting (ker/range are neg-invariant)
  have hex_sum_neg : Function.Exact ⇑(cscMvSumInt U V (N + 1))
      ⇑(-cscMvConnectingInt U V hU hV N) := fun y => by
    rw [LinearMap.neg_apply, neg_eq_zero]
    exact cscMv_exact_sumInt U V hU hV y
  have hex_conn_neg : Function.Exact ⇑(-cscMvConnectingInt U V hU hV N)
      ⇑(cscMvDiagInt U V (N + 2)) := fun y =>
    (cscMv_exact_connectingInt U V hU hV y).trans
      ⟨fun ⟨x, hx⟩ => ⟨-x, by rw [LinearMap.neg_apply, map_neg, neg_neg]; exact hx⟩,
        fun ⟨x, hx⟩ => ⟨-x, by rw [map_neg, ← LinearMap.neg_apply]; exact hx⟩⟩
  exact LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (f₁ := cscMvDiagInt U V (N + 1)) (f₂ := cscMvSumInt U V (N + 1))
    (f₃ := -cscMvConnectingInt U V hU hV N) (f₄ := cscMvDiagInt U V (N + 2))
    (g₁ := subHomDiagInt U V (0 + 1)) (g₂ := subHomSumInt U V (0 + 1))
    (g₃ := subHomConnectingInt U V hU hV 0)
    (g₄ := subHomDiagInt U V 0)
    (i₁ := openDuality (k := N + 1) (m := 0) (hU.inter hV) z₀ hz₀)
    (i₂ := (openDuality (k := N + 1) (m := 0) hU z₀ hz₀).prodMap
      (openDuality (k := N + 1) (m := 0) hV z₀ hz₀))
    (i₃ := openDuality (k := N + 1) (m := 0) (hU.union hV) z₀ hz₀)
    (i₄ := openDuality₀Int (hU.inter hV) z₀ hz₀)
    (i₅ := (openDuality₀Int hU z₀ hz₀).prodMap (openDuality₀Int hV z₀ hz₀))
    hc₁ hc₂ hc₃ hc₄
    (cscMv_exact_middleInt U V hU hV) hex_sum_neg
    hex_conn_neg
    (subHom_exact_middleInt U V hU hV) (subHom_exact_sumInt U V hU hV)
    (subHom_exact_connectingInt U V hU hV)
    hDI hi₂ hD0I hi₅

end SKEFTHawking.SingularOpenDualityBotFiveLemmaInt
