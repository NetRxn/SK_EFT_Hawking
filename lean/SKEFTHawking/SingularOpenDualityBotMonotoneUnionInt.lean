/-
# Phase 5q.H (E1 CSC-PD tower) — monotone-union stability of the bottom duality `D_W⁰` (integral)

Integral (`ZMod 2 → ℤ`) mirror of `SingularConnSquareCloseNCBotApex.openDuality₀_monotone_union_bijective`:
the bottom-degree open duality `D_W⁰` passes to increasing unions. Reuses the generic monotone-union driver
`duality_monotone_union_bijectiveInt` (degree-agnostic in the codomain `d`, here `d = 0`) fed the `D_·⁰` map
family + its naturality `openDuality₀Int_cscOpenMonotone`. The `D⁰`-conjunct of `pdWindowPInt_monotone_union`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularOpenDualityMonotoneUnionInt
import SKEFTHawking.SingularOpenDualityBotNatInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCompactlySupportedOpenInt
open SKEFTHawking.SingularOpenDualityBotInt (openDuality₀Int)
open SKEFTHawking.SingularOpenDualityBotNatInt (openDuality₀Int_cscOpenMonotone)
open SKEFTHawking.SingularOpenDualityMonotoneUnionInt (duality_monotone_union_bijectiveInt)

namespace SKEFTHawking.SingularOpenDualityBotMonotoneUnionInt

variable {X : TopCat} {W : ℕ → Set ↑X}

/-- **Monotone-union stability of `D_W⁰`** (integral): if `D_{Wₙ}⁰` is bijective on every stage of an
increasing open family, so is `D_{⋃Wₙ}⁰`. -/
theorem openDuality₀_monotone_union_bijectiveInt [T2Space ↑X] {k : ℕ}
    (hmono : ∀ n, W n ⊆ W (n + 1)) (hopen : ∀ n, IsOpen (W n))
    (z₀ : SingularChainInt X (k + 0 + 1)) (hz₀ : chainBoundary X (k + 0) z₀ = 0)
    (hbij : ∀ n, Function.Bijective (openDuality₀Int (hopen n) z₀ hz₀)) :
    Function.Bijective (openDuality₀Int (isOpen_iUnion hopen) z₀ hz₀) :=
  duality_monotone_union_bijectiveInt (k := k + 1) (d := 0) hmono hopen
    (fun _V hV => openDuality₀Int hV z₀ hz₀)
    (fun _V _V' hV hV' hVV' α =>
      openDuality₀Int_cscOpenMonotone hV hV' hVV' z₀ hz₀ α)
    hbij

end SKEFTHawking.SingularOpenDualityBotMonotoneUnionInt
