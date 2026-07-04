import SKEFTHawking.PoincareDualityWuFormula
import SKEFTHawking.SingularBockstein

/-!
# The Wu third class `w₃ = Sq¹(v₂)` and the `w₁w₃` SW-number reduction

Phase 5q.H — completing the SW-number vanishing (review finding 5.1). On a closed 4-manifold the Wu formula
`w = Sq(v)` gives `w₃ = Sq⁰v₃ + Sq¹v₂ = Sq¹v₂` (since `v₃ = 0` by dimension). This module defines the Wu third
class as the genuine singular Bockstein `Sq¹` (`SingularBockstein.Sq1`) of the middle Wu class, and reduces
its Pin⁺ vanishing to a single Bockstein-nilpotence fact.

For a Pin⁺ 4-manifold (`w₂ = 0`, so `v₂ = v₁²` via `wuW2_eq_zero_iff`), `w₃ = Sq¹(v₁²)`. Since `v₁² = Sq¹v₁`
(the degree-1 Wu identity `Sq1_on_H1`), this is `Sq¹(Sq¹v₁)`, which vanishes by `Sq¹∘Sq¹ = 0` (Bockstein
nilpotence — a follow-up brick; the even-defect template is `SingularBockstein.Sq1cochain_coboundary`). Then
the degree-4 SW number `⟨w₁∪w₃,[M]⟩ = ⟨w₁∪0,[M]⟩ = 0` — the fifth and final degree-4 SW monomial, closing the
`swNumbers_vanish` enumeration to genuinely ALL SW numbers.
-/

namespace SKEFTHawking.WuThirdClass

open SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.PoincareDualityWu
open SKEFTHawking.PoincareDualityWuFormula SKEFTHawking.SingularBockstein

variable {X : TopCat}

/-- The **singular Wu third class** `w₃ := Sq¹(v₂) = Sq1 (wuClass2 P)` on a closed 4-manifold — the Wu-formula
expression `w₃ = Sq¹v₂` (higher terms vanish: `v₃ = 0` by dimension, `Sq⁰v₃ = 0`). -/
noncomputable def wuW3 (P : PoincareDual4Mid X) : Cohomology X 3 := Sq1 (wuClass2 P)

/-- **The Pin⁺ Wu-third reduction** `w₃ = Sq¹(v₁²)`: for `w₂ = 0` (so `v₂ = v₁²`), the Wu third class is the
Bockstein of `v₁²`. Its vanishing (`w₃ = 0`) reduces to `Sq¹(v₁²) = Sq¹(Sq¹v₁) = 0` (Bockstein nilpotence,
the tracked follow-up). -/
theorem wuW3_eq_Sq1_v1sq (P : PoincareDual4Mid X) (P₁₃ : PoincareDual4Lo X) (hw2 : wuW2 P P₁₃ = 0) :
    wuW3 P = Sq1 (cupSquareₗ (wuClass1 P₁₃)) := by
  rw [wuW3, (wuW2_eq_zero_iff P P₁₃).mp hw2, cupSquareₗ_apply]

end SKEFTHawking.WuThirdClass
