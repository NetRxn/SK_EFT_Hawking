/-
# Phase 5q.H (E1 CSC-PD tower) — the integral D⁰ (H₀-truncated) Mayer–Vietoris five-lemma

Integral (`ZMod 2 → ℤ`) mirror of `SingularConnSquareCloseNCBotApex.openDuality₀_union_bijective`. The LAST
five-lemma of the integral PD open-cover induction ladder: bijectivity of `D⁰_{U∪V} : Hᴺ⁺²_c(U∪V;ℤ) →
H₀(sub (U∪V);ℤ)` from the pieces. The homology row is EXTENDED BY THE ZERO MODULE (`PUnit`) below `H₀` — the
two far verticals are zero maps whose bijectivity/injectivity is exactly the csc-top vanishing (`hvan…`,
supplied by the geometry at the induction stage). Exactness past `subHomSumInt 0` degenerates to the H₀-end
surjectivity `subHomSumInt_zero_surjective` (`hg₂`) and a `PUnit` triviality (`hg₃`); `hg₁ =
subHom_exact_middle₀Int`.

All commuting squares are integral: `hc₁` = `subHomDiagInt_openDuality₀`, `hc₂` = `subHomSumInt_openDuality₀`
(both `SingularOpenDualityBotNatInt`); `hc₃`/`hc₄` are `PUnit`-trivial (`Subsingleton.elim`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularOpenDualityBotNatInt
import SKEFTHawking.SingularMayerVietorisLESBotInt
import SKEFTHawking.SingularSubHomSumEndInt
import SKEFTHawking.SingularCSCMayerVietorisMiddleInt
import SKEFTHawking.SingularCSCMayerVietorisConnExactInt
import SKEFTHawking.SingularCSCMayerVietorisSumExactInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCompactlySupportedOpenInt
open SKEFTHawking.SingularCSCMayerVietorisInt
open SKEFTHawking.SingularCSCMayerVietorisConnectingInt
open SKEFTHawking.SingularCSCMayerVietorisMiddleInt
open SKEFTHawking.SingularCSCMayerVietorisConnExactInt
open SKEFTHawking.SingularCSCMayerVietorisSumExactInt
open SKEFTHawking.SingularSubHomologyMVInt
open SKEFTHawking.SingularOpenDualityMVSquareInt
open SKEFTHawking.SingularOpenDualityBotInt
open SKEFTHawking.SingularOpenDualityBotNatInt
open SKEFTHawking.SingularMayerVietorisLESBotInt
open SKEFTHawking.SingularSubHomSumEndInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)

namespace SKEFTHawking.SingularOpenDualityD0FiveLemmaInt

variable {X : TopCat} [T2Space ↑X]

/-- **The integral D⁰ MV five-lemma step** (the LAST five-lemma of the PD-induction ladder): bijectivity of
`D⁰_{U∪V}` from the pieces, with the homology row extended by the zero module below `H₀`. The far verticals
are zero maps into `PUnit` whose bij/inj is the csc-top vanishing (`hvan…`). -/
theorem openDuality₀_union_bijectiveInt {N : ℕ} {U V : Set ↑X}
    (hU : IsOpen U) (hV : IsOpen V)
    (z₀ : SingularChainInt X (N + 1 + 0 + 1)) (hz₀ : chainBoundary X (N + 1 + 0) z₀ = 0)
    (hvanI : ∀ α : CompactlySupportedCohomologyOpenInt (U ∩ V) (N + 1 + 2), α = 0)
    (hvanU : ∀ α : CompactlySupportedCohomologyOpenInt U (N + 1 + 2), α = 0)
    (hvanV : ∀ α : CompactlySupportedCohomologyOpenInt V (N + 1 + 2), α = 0)
    (hD0I : Function.Surjective (openDuality₀Int (hU.inter hV) z₀ hz₀))
    (hD0U : Function.Bijective (openDuality₀Int hU z₀ hz₀))
    (hD0V : Function.Bijective (openDuality₀Int hV z₀ hz₀)) :
    Function.Bijective (openDuality₀Int (hU.union hV) z₀ hz₀) := by
  have hc₁ : (subHomDiagInt U V 0).comp (openDuality₀Int (hU.inter hV) z₀ hz₀)
      = ((openDuality₀Int hU z₀ hz₀).prodMap
          (openDuality₀Int hV z₀ hz₀)).comp (cscMvDiagInt U V (N + 1 + 1)) := by
    refine LinearMap.ext fun α => ?_
    simp only [LinearMap.comp_apply, LinearMap.prodMap_apply, cscMvDiagInt, LinearMap.prod_apply,
      Function.prod_def]
    exact subHomDiagInt_openDuality₀ hU hV z₀ hz₀ α
  have hc₂ : (subHomSumInt U V 0).comp
        ((openDuality₀Int hU z₀ hz₀).prodMap (openDuality₀Int hV z₀ hz₀))
      = (openDuality₀Int (hU.union hV) z₀ hz₀).comp (cscMvSumInt U V (N + 1 + 1)) := by
    refine LinearMap.ext fun p => ?_
    simp only [LinearMap.comp_apply, LinearMap.prodMap_apply]
    exact (subHomSumInt_openDuality₀ hU hV z₀ hz₀ p.1 p.2).symm
  have hc₃ : (0 : Homology (sub (U ∪ V)) 0 →ₗ[ℤ] PUnit.{1}).comp
        (openDuality₀Int (hU.union hV) z₀ hz₀)
      = (0 : CompactlySupportedCohomologyOpenInt (U ∩ V) (N + 1 + 2) →ₗ[ℤ] PUnit.{1}).comp
          (cscMvConnectingInt U V hU hV (N + 1)) :=
    LinearMap.ext fun _ => Subsingleton.elim _ _
  have hc₄ : (0 : PUnit.{1} →ₗ[ℤ] PUnit.{1}).comp
        (0 : CompactlySupportedCohomologyOpenInt (U ∩ V) (N + 1 + 2) →ₗ[ℤ] PUnit.{1})
      = ((0 : CompactlySupportedCohomologyOpenInt U (N + 1 + 2)
            × CompactlySupportedCohomologyOpenInt V (N + 1 + 2) →ₗ[ℤ] PUnit.{1})).comp
          (cscMvDiagInt U V (N + 1 + 2)) :=
    LinearMap.ext fun _ => Subsingleton.elim _ _
  have hg₂ : Function.Exact (subHomSumInt U V 0)
      (0 : Homology (sub (U ∪ V)) 0 →ₗ[ℤ] PUnit.{1}) := by
    intro y
    exact ⟨fun _ => subHomSumInt_zero_surjective U V y, fun _ => rfl⟩
  have hg₃ : Function.Exact (0 : Homology (sub (U ∪ V)) 0 →ₗ[ℤ] PUnit.{1})
      (0 : PUnit.{1} →ₗ[ℤ] PUnit.{1}) := by
    intro y
    exact ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩
  have hi₂ : Function.Bijective
      ⇑((openDuality₀Int hU z₀ hz₀).prodMap (openDuality₀Int hV z₀ hz₀)) := by
    rw [LinearMap.coe_prodMap]
    exact hD0U.prodMap hD0V
  have hi₄ : Function.Bijective
      ⇑(0 : CompactlySupportedCohomologyOpenInt (U ∩ V) (N + 1 + 2) →ₗ[ℤ] PUnit.{1}) :=
    ⟨fun a b _ => (hvanI a).trans (hvanI b).symm, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
  have hi₅ : Function.Injective
      ⇑(0 : CompactlySupportedCohomologyOpenInt U (N + 1 + 2)
          × CompactlySupportedCohomologyOpenInt V (N + 1 + 2) →ₗ[ℤ] PUnit.{1}) :=
    fun p q _ => Prod.ext ((hvanU p.1).trans (hvanU q.1).symm)
      ((hvanV p.2).trans (hvanV q.2).symm)
  exact LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (f₁ := cscMvDiagInt U V (N + 1 + 1)) (f₂ := cscMvSumInt U V (N + 1 + 1))
    (f₃ := cscMvConnectingInt U V hU hV (N + 1)) (f₄ := cscMvDiagInt U V (N + 1 + 2))
    (g₁ := subHomDiagInt U V 0) (g₂ := subHomSumInt U V 0)
    (g₃ := (0 : Homology (sub (U ∪ V)) 0 →ₗ[ℤ] PUnit.{1}))
    (g₄ := (0 : PUnit.{1} →ₗ[ℤ] PUnit.{1}))
    (i₁ := openDuality₀Int (hU.inter hV) z₀ hz₀)
    (i₂ := (openDuality₀Int hU z₀ hz₀).prodMap (openDuality₀Int hV z₀ hz₀))
    (i₃ := openDuality₀Int (hU.union hV) z₀ hz₀)
    (i₄ := (0 : CompactlySupportedCohomologyOpenInt (U ∩ V) (N + 1 + 2) →ₗ[ℤ] PUnit.{1}))
    (i₅ := (0 : CompactlySupportedCohomologyOpenInt U (N + 1 + 2)
        × CompactlySupportedCohomologyOpenInt V (N + 1 + 2) →ₗ[ℤ] PUnit.{1}))
    hc₁ hc₂ hc₃ hc₄
    (cscMv_exact_middleInt U V hU hV) (cscMv_exact_sumInt U V hU hV)
    (cscMv_exact_connectingInt U V hU hV)
    (subHom_exact_middle₀Int U V hU hV) hg₂ hg₃
    hD0I hi₂ hi₄ hi₅

end SKEFTHawking.SingularOpenDualityD0FiveLemmaInt
