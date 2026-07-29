/-
# Phase 5q.H (E1 CSC-PD tower) — the integral UPPER-window Mayer–Vietoris five-lemma

Integral (`ZMod 2 → ℤ`) mirror of `SingularConnSquareCloseNCBotApex.openDuality_union_bijective_upper`. The
generic (`m ≥ 1`) MV five-lemma step of the integral Poincaré-duality open-cover induction: bijectivity of
the union duality `D_{U∪V}` at window `(N+1, p+1)` from bijectivity on the pieces, via the Mathlib five-lemma
on the two MV LES rows glued by the four commuting duality squares — all verticals general `openDuality`
(no bottom `H₀` truncation), the `z₀`-frame carried through `castChainInt` recasts at the two window
spellings `N+1+(p+1)+1` and `N+2+p+1` (both `= N+p+3`).

`hc₁`/`hc₂`/`hc₄` = the generic Δ/Σ squares (`subHomDiagInt_openDuality` / `subHomSumInt_openDuality` at
`(N+1,p+1)` and `(N+2,p)`); `hc₃` = the connecting square via the already-built
`subHomConnecting_openDuality_of_coreInt`, threading the per-`K` core `hcore` (the deep torsion-safe
`hcoreInt`) as a hypothesis — no project axiom. Both LES-exactness rows = the built `cscMv_exact_*Int` +
`subHom_exact_*Int`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularOpenDualityMVConnSquareInt
import SKEFTHawking.SingularOpenDualityMVSquareInt
import SKEFTHawking.SingularCSCMayerVietorisMiddleInt
import SKEFTHawking.SingularCSCMayerVietorisConnExactInt
import SKEFTHawking.SingularCSCMayerVietorisSumExactInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCompactlySupportedOpenInt
open SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularOpenDualityInt
open SKEFTHawking.SingularOpenDualityMVConnSquareInt
open SKEFTHawking.SingularCSCMayerVietorisInt
open SKEFTHawking.SingularCSCMayerVietorisConnectingInt
open SKEFTHawking.SingularCSCMayerVietorisMiddleInt
open SKEFTHawking.SingularCSCMayerVietorisConnExactInt
open SKEFTHawking.SingularCSCMayerVietorisSumExactInt
open SKEFTHawking.SingularSubHomologyMVInt
open SKEFTHawking.SingularOpenDualityMVSquareInt

namespace SKEFTHawking.SingularOpenDualityUpperFiveLemmaInt

variable {X : TopCat} [T2Space ↑X]

/-- **The integral upper-window MV five-lemma step**: bijectivity of `D_{U∪V}` at the generic window
`(N+1, p+1)` from the piece bijectivities + the per-`K` connecting core `hcore`. Threads `hcore` (the deep
`hcoreInt`) as a hypothesis; NO project axiom. The `(2,1)`-center of the degree-4 ladder is `p := 0`. -/
theorem openDuality_union_bijective_upperInt {N p : ℕ} {U V : Set ↑X}
    (hU : IsOpen U) (hV : IsOpen V)
    (z₀ : SingularChainInt X (N + p + 3)) (hz₀ : chainBoundary X (N + p + 2) z₀ = 0)
    (hcore : ∀ (K : CompactsIn (U ∪ V)) (g : cohomGWInt (U ∪ V) (N + 1) K),
      subHomConnectingInt U V hU hV (p + 1)
          (legW (k := N + 1) (m := p + 1) (hU.union hV)
            (castChainInt (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
            (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z₀ hz₀) K g)
        = openDuality (k := N + 2) (m := p) (hU.inter hV)
            (castChainInt (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
            (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z₀ hz₀)
            (legδInt U V hU hV N K g))
    (hDI : Function.Surjective (openDuality (k := N + 1) (m := p + 1) (hU.inter hV)
      (castChainInt (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
      (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z₀ hz₀)))
    (hDU : Function.Bijective (openDuality (k := N + 1) (m := p + 1) hU
      (castChainInt (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
      (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z₀ hz₀)))
    (hDV : Function.Bijective (openDuality (k := N + 1) (m := p + 1) hV
      (castChainInt (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
      (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z₀ hz₀)))
    (hDI' : Function.Bijective (openDuality (k := N + 2) (m := p) (hU.inter hV)
      (castChainInt (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
      (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z₀ hz₀)))
    (hDU' : Function.Injective (openDuality (k := N + 2) (m := p) hU
      (castChainInt (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
      (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z₀ hz₀)))
    (hDV' : Function.Injective (openDuality (k := N + 2) (m := p) hV
      (castChainInt (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
      (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z₀ hz₀))) :
    Function.Bijective (openDuality (k := N + 1) (m := p + 1) (hU.union hV)
      (castChainInt (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
      (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z₀ hz₀)) := by
  have hc₁ : (subHomDiagInt U V (p + 1 + 1)).comp
        (openDuality (k := N + 1) (m := p + 1) (hU.inter hV)
          (castChainInt (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
          (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z₀ hz₀))
      = ((openDuality (k := N + 1) (m := p + 1) hU
          (castChainInt (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
          (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z₀ hz₀)).prodMap
          (openDuality (k := N + 1) (m := p + 1) hV
            (castChainInt (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
            (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z₀ hz₀))).comp
          (cscMvDiagInt U V (N + 1)) := by
    refine LinearMap.ext fun α => ?_
    simp only [LinearMap.comp_apply, LinearMap.prodMap_apply, cscMvDiagInt, LinearMap.prod_apply,
      Function.prod_def]
    exact subHomDiagInt_openDuality (k := N + 1) (m := p + 1) hU hV
      (castChainInt (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
      (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z₀ hz₀) α
  have hc₂ : (subHomSumInt U V (p + 1 + 1)).comp
        ((openDuality (k := N + 1) (m := p + 1) hU
          (castChainInt (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
          (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z₀ hz₀)).prodMap
          (openDuality (k := N + 1) (m := p + 1) hV
            (castChainInt (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
            (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z₀ hz₀)))
      = (openDuality (k := N + 1) (m := p + 1) (hU.union hV)
          (castChainInt (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
          (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z₀ hz₀)).comp
          (cscMvSumInt U V (N + 1)) := by
    refine LinearMap.ext fun q => ?_
    simp only [LinearMap.comp_apply, LinearMap.prodMap_apply]
    exact (subHomSumInt_openDuality (k := N + 1) (m := p + 1) hU hV
      (castChainInt (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
      (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z₀ hz₀) q.1 q.2).symm
  have hc₃ : (subHomConnectingInt U V hU hV (p + 1)).comp
        (openDuality (k := N + 1) (m := p + 1) (hU.union hV)
          (castChainInt (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
          (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z₀ hz₀))
      = (openDuality (k := N + 2) (m := p) (hU.inter hV)
          (castChainInt (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
          (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z₀ hz₀)).comp
          (cscMvConnectingInt U V hU hV N) := by
    refine LinearMap.ext fun α => ?_
    simp only [LinearMap.comp_apply]
    exact subHomConnecting_openDuality_of_coreInt hU hV z₀ hz₀ hcore α
  have hc₄ : (subHomDiagInt U V (p + 1)).comp
        (openDuality (k := N + 2) (m := p) (hU.inter hV)
          (castChainInt (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
          (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z₀ hz₀))
      = ((openDuality (k := N + 2) (m := p) hU
          (castChainInt (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
          (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z₀ hz₀)).prodMap
          (openDuality (k := N + 2) (m := p) hV
            (castChainInt (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
            (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z₀ hz₀))).comp
          (cscMvDiagInt U V (N + 2)) := by
    refine LinearMap.ext fun α => ?_
    simp only [LinearMap.comp_apply, LinearMap.prodMap_apply, cscMvDiagInt, LinearMap.prod_apply,
      Function.prod_def]
    exact subHomDiagInt_openDuality (k := N + 2) (m := p) hU hV
      (castChainInt (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
      (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z₀ hz₀) α
  have hi₂ : Function.Bijective
      ⇑((openDuality (k := N + 1) (m := p + 1) hU
          (castChainInt (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
          (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z₀ hz₀)).prodMap
        (openDuality (k := N + 1) (m := p + 1) hV
          (castChainInt (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
          (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z₀ hz₀))) := by
    rw [LinearMap.coe_prodMap]
    exact hDU.prodMap hDV
  have hi₅ : Function.Injective
      ⇑((openDuality (k := N + 2) (m := p) hU
          (castChainInt (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
          (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z₀ hz₀)).prodMap
        (openDuality (k := N + 2) (m := p) hV
          (castChainInt (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
          (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z₀ hz₀))) := by
    rw [LinearMap.coe_prodMap]
    exact hDU'.prodMap hDV'
  exact LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (f₁ := cscMvDiagInt U V (N + 1)) (f₂ := cscMvSumInt U V (N + 1))
    (f₃ := cscMvConnectingInt U V hU hV N) (f₄ := cscMvDiagInt U V (N + 2))
    (g₁ := subHomDiagInt U V (p + 1 + 1)) (g₂ := subHomSumInt U V (p + 1 + 1))
    (g₃ := subHomConnectingInt U V hU hV (p + 1))
    (g₄ := subHomDiagInt U V (p + 1))
    (i₁ := openDuality (k := N + 1) (m := p + 1) (hU.inter hV)
      (castChainInt (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
      (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z₀ hz₀))
    (i₂ := (openDuality (k := N + 1) (m := p + 1) hU
      (castChainInt (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
      (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z₀ hz₀)).prodMap
      (openDuality (k := N + 1) (m := p + 1) hV
        (castChainInt (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
        (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z₀ hz₀)))
    (i₃ := openDuality (k := N + 1) (m := p + 1) (hU.union hV)
      (castChainInt (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
      (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z₀ hz₀))
    (i₄ := openDuality (k := N + 2) (m := p) (hU.inter hV)
      (castChainInt (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
      (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z₀ hz₀))
    (i₅ := (openDuality (k := N + 2) (m := p) hU
      (castChainInt (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
      (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z₀ hz₀)).prodMap
      (openDuality (k := N + 2) (m := p) hV
        (castChainInt (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
        (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z₀ hz₀)))
    hc₁ hc₂ hc₃ hc₄
    (cscMv_exact_middleInt U V hU hV) (cscMv_exact_sumInt U V hU hV)
    (cscMv_exact_connectingInt U V hU hV)
    (subHom_exact_middleInt U V hU hV) (subHom_exact_sumInt U V hU hV)
    (subHom_exact_connectingInt U V hU hV)
    hDI hi₂ hDI' hi₅

end SKEFTHawking.SingularOpenDualityUpperFiveLemmaInt
