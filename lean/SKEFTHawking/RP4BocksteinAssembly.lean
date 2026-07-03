import Mathlib
import SKEFTHawking.SingularBocksteinLeibniz
import SKEFTHawking.RP4WuAssembly

/-!
# Phase 5q.G (B-arc, M4-c5..c6) — the Bockstein ladder on `ℝP⁴`: `Sq¹x = x²`, `Sq¹x² = 0`,
`Sq¹x³ = x⁴`

The class-level Bockstein computation on the `ℝP⁴` cup ladder, at pinned degrees (the
`(p+1)+q ≡ p+q+1` index seam is rfl only for literals):

* `Sq¹(xpow 1) = xpow 2` — the in-tree degree-1 Wu identity `Sq1_on_H1` + `xpow_two_eq_cupH`.
* `Sq¹(xpow 2) = xpow 3 + xpow 3 = 0` — Leibniz at `(1,1)` on the `[x ⌣ x]`-representative;
  both cross terms are `xpow 3` (left: the `(2,0)`-seeded Leibniz applied to the cup-shaped
  representative; right: the `(1,1)`-Leibniz form + a second-slot coboundary swap).
* `Sq¹(xpow 3) = x² ⌣ x² = xpow 4` — Leibniz at `(2,1)` on `[x² ⌣ x]`; the `Sq¹x²`-term dies.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.RP4PointSet SKEFTHawking.RP4CohomologyLadder SKEFTHawking.RP4CupLadder
open SKEFTHawking.RP4SmithCochain
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularBockstein SKEFTHawking.SingularBocksteinLeibniz

namespace SKEFTHawking.RP4BocksteinAssembly

/-! ## §1. Pinned-degree cochain Leibniz + cup-coboundary helpers -/

/-- The Bockstein–Leibniz at `(1,1)` as a cochain-function identity (the Big/Small-vs-cup
face seams are one-`rfl` at literal degrees). -/
theorem Sq1cochain_cup_11 {X : TopCat} (a b : SingularCochain X 1)
    (ha : coboundary X 1 a = 0) (hb : coboundary X 1 b = 0) :
    Sq1cochain (cup a b) = cup (Sq1cochain a) b + cup a (Sq1cochain b) := by
  funext τ
  rw [Pi.add_apply, Sq1cochain_cup a ha b hb τ, cup_apply, cup_apply]
  rfl

/-- The Bockstein–Leibniz at `(2,1)` as a cochain-function identity. -/
theorem Sq1cochain_cup_21 {X : TopCat} (a : SingularCochain X 2) (b : SingularCochain X 1)
    (ha : coboundary X 2 a = 0) (hb : coboundary X 1 b = 0) :
    Sq1cochain (cup a b) = cup (Sq1cochain a) b + cup a (Sq1cochain b) := by
  funext τ
  rw [Pi.add_apply, Sq1cochain_cup a ha b hb τ, cup_apply, cup_apply]
  rfl

/-- **Right coboundary absorbs**: `a ⌣ δw = δ(a ⌣ w)` for a cocycle `a` (the `δa`-term of the
Leibniz rule dies) — at `(1,1)`: `a, w ∈ C¹`. -/
theorem cup_coboundary_right_11 {X : TopCat} (a w : SingularCochain X 1)
    (ha : coboundary X 1 a = 0) :
    cup a (coboundary X 1 w) = coboundary X (1 + 1) (cup a w) := by
  funext τ
  rw [cup_apply, coboundary_cup]
  have h1 : coboundary X 1 a (frontBig τ) = 0 := congrFun ha (frontBig τ)
  rw [h1, zero_mul, zero_add]
  rfl

/-- **Left coboundary absorbs**: `δw ⌣ b = δ(w ⌣ b)` for a cocycle `b` — at `(2→3, 1)`:
`w ∈ C²`, `b ∈ C¹`. -/
theorem cup_coboundary_left_31 {X : TopCat} (w : SingularCochain X 2) (b : SingularCochain X 1)
    (hb : coboundary X 1 b = 0) :
    cup (coboundary X 2 w) b = coboundary X (2 + 1) (cup w b) := by
  funext τ
  rw [cup_apply, coboundary_cup]
  have h1 : coboundary X 1 b (backSmall τ) = 0 := congrFun hb (backSmall τ)
  rw [h1, mul_zero, add_zero]
  rfl

end SKEFTHawking.RP4BocksteinAssembly
