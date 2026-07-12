/-
# Phase 5q.H (E1) — `SpinWuDatum` from the mod-2 PD datum: the Wu "Spin ⟹ even" step, derived

The registry-named elimination step for `spinWu_even_datum` (`HYPOTHESIS_REGISTRY`): instead of
disclosing `wu_vanish` raw, DERIVE it from the mod-2 middle Poincaré-duality datum via the proven
Wu machinery — `⟨y ∪ y, [M]₂⟩ = ⟨Sq²y, [M]₂⟩ = ⟨v₂ ∪ y, [M]₂⟩ = 0` when `v₂ = 0` (`wu_relation`),
and on an ORIENTED manifold `v₂ = 0 ⟺ w₂ = 0` (`wuW2_eq_zero_iff` with `v₁ = 0`). After this brick
the spin/Wu input to intersection-form EVENNESS is exactly: the mod-2 PD datum (`PoincareDual4Mid`,
+ `PoincareDual4Lo` for the `w₂` form), the ℤ→ℤ/2 evaluation compatibility, and the honest spin
condition (`v₂ = 0`, or `w₂ = 0` + orientedness `v₁ = 0`) — no independent `wu_vanish` disclosure.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.IntersectionFormEvenInt
import SKEFTHawking.PoincareDualityWuFormula

open SKEFTHawking.SingularCohomologyMod2 (cupH24 cupSquare2 cupSquare2_apply cupH)
open SKEFTHawking.PoincareDualityWu (PoincareDual4Mid wuClass2 wu_relation)
open SKEFTHawking.PoincareDualityWuFormula (PoincareDual4Lo wuClass1 wuW2 wuW2_eq_zero_iff)
open SKEFTHawking.SingularCohomologyInt (SpinWuDatum IntFundamentalClass redH)

namespace SKEFTHawking.SpinWuFromPD

variable {X : TopCat}

/-- **`SpinWuDatum` from the mod-2 PD datum + `v₂ = 0`** — the Wu "Spin ⟹ even" derivation. The
`wu_vanish` field is not disclosed but PROVED: `⟨y∪y,[M]₂⟩ = ⟨Sq²y,[M]₂⟩ = ⟨v₂∪y,[M]₂⟩` by the defining
Wu relation (`PoincareDualityWu.wu_relation`), which vanishes when the middle Wu class `v₂` does. The
remaining honest inputs: the mod-2 middle PD datum `P`, the ℤ→ℤ/2 fundamental-class evaluation
compatibility, and the spin condition in `v₂`-form. -/
noncomputable def spinWuDatum_of_pd4Mid (fc : IntFundamentalClass X) (P : PoincareDual4Mid X)
    (hcompat : ∀ ω : SKEFTHawking.SingularCohomologyInt.Cohomology X 4,
      ((fc.eval ω : ℤ) : ZMod 2) = P.mu (redH X 4 ω))
    (hv2 : wuClass2 P = 0) : SpinWuDatum fc where
  mu2 := P.mu
  eval_compat := hcompat
  wu_vanish y := by
    calc P.mu (cupH24 y y)
        = P.mu (cupSquare2 y) := by rw [cupSquare2_apply]
      _ = P.mu (cupH24 (wuClass2 P) y) := (wu_relation P y).symm
      _ = 0 := by rw [hv2]; simp

/-- **`SpinWuDatum` from ORIENTED (`v₁ = 0`) + SPIN (`w₂ = 0`)** — the `w₂`-form of the derivation. On an
oriented manifold the first Wu class vanishes, so the singular Wu formula `w₂ = v₂ + v₁²`
(`wuW2_eq_zero_iff`) collapses `w₂ = 0` to `v₂ = 0`, and `spinWuDatum_of_pd4Mid` applies. This is the
exact statement shape of the classical input "closed oriented spin 4-manifold ⟹ even intersection
form". -/
noncomputable def spinWuDatum_of_oriented_spin (fc : IntFundamentalClass X)
    (P : PoincareDual4Mid X) (P₁₃ : PoincareDual4Lo X)
    (hcompat : ∀ ω : SKEFTHawking.SingularCohomologyInt.Cohomology X 4,
      ((fc.eval ω : ℤ) : ZMod 2) = P.mu (redH X 4 ω))
    (hv1 : wuClass1 P₁₃ = 0) (hw2 : wuW2 P P₁₃ = 0) : SpinWuDatum fc :=
  spinWuDatum_of_pd4Mid fc P hcompat (by
    have h := (wuW2_eq_zero_iff P P₁₃).mp hw2
    rw [h, hv1]; simp)

end SKEFTHawking.SpinWuFromPD
