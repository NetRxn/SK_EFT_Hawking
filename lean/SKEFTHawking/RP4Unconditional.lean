import Mathlib
import SKEFTHawking.RP4BocksteinAssembly
import SKEFTHawking.RP4Witness
import SKEFTHawking.RP4Manifold

/-!
# Phase 5q.G (B-arc, M4-d) — THE REDUCTION DISCHARGED: the unconditional tied `ℤ/16`

The two `ℝP⁴` hypotheses of `dataBordismTied_equiv_zmod16_of_rp4` are now **theorems**:

* **`rp4_hcert`** — `wuW2(ℝP⁴) = 0`: by the Pin⁺ characterization `wuW2_eq_zero_iff`, this is
  `v₂ = v₁²`; the M-ladder computed `v₂ = x²` (`wuClass2_eq_xpow2`) and `v₁ = x`
  (`wuClass1_eq_xpow1`), and `x² = x ⌣ x` is the ladder square (`xpow_two_eq_cupH`).
* **`rp4_htie`** — `w₁⁴[ℝP⁴] = 1`: with `w₁ = v₁ = x`, the number is
  `μ((x⌣x) ⌣₂₄ (x⌣x)) = μ(x²⌣x²) = 1` (`mu_cupH24_xpow2_xpow2`).

**`rp4_dataBordismTied_equiv_zmod16`** is therefore the GENUINE unconditional tied `ℤ/16` —
no `ℝP⁴`-hypothesis binder remains; the entire residual geometry of the B-checkpoint is
discharged through the Smith double-cover tower (M1–M4).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.RP4PointSet SKEFTHawking.RP4CohomologyLadder SKEFTHawking.RP4CupLadder
open SKEFTHawking.RP4WuAssembly SKEFTHawking.RP4BocksteinAssembly
open SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularPD4Instances SKEFTHawking.PoincareDualityWu
open SKEFTHawking.PoincareDualityWuFormula
open SKEFTHawking.PinPlusTiedData SKEFTHawking.RP4Witness SKEFTHawking.SingularSWNumber
open scoped Manifold

namespace SKEFTHawking.RP4Unconditional

/-- **`hcert` is a THEOREM**: `ℝP⁴` is `w₂`-admissible — `wuW2(ℝP⁴) = 0`, since
`v₂ = x² = x ⌣ x = v₁²`. -/
theorem rp4_hcert : PinPlusCertK (𝓡 4) rp4SM := by
  intro _ _
  refine (wuW2_eq_zero_iff _ _).mpr ?_
  show wuClass2 (poincareDual4Mid_of_closed (M := RP4))
    = cupH (wuClass1 (poincareDual4Lo_of_closed (M := RP4)))
        (wuClass1 (poincareDual4Lo_of_closed (M := RP4)))
  rw [wuClass2_eq_xpow2, wuClass1_eq_xpow1]
  exact xpow_two_eq_cupH

/-- **THE REGULARITY-GENERIC `hcert`** (the `k`-lift of `rp4_hcert`) — `ℝP⁴` is `w₂`-admissible as a
`C^k` singular manifold for **every** regularity `k : WithTop ℕ∞`, in particular the smooth/analytic
`k = ⊤`. The certificate's content (`wuW2 = 0`) is a statement about the carrier space `RP4` alone,
so the proof is verbatim `rp4_hcert`'s; what changes is the ambient `SingularManifold`'s regularity
exponent, which `RP4Manifold.isManifold_rp4` supplies at every `k`. At `k = 0` this is
**definitionally** `rp4_hcert` (`rp4SM = rp4SM_k 0` by `rfl`) — the lift strictly extends, it does
not replace. -/
theorem rp4_hcert_k {k : WithTop ℕ∞} :
    PinPlusCertK (𝓡 4) (SKEFTHawking.RP4Manifold.rp4SM_k k) := by
  intro _ _
  refine (wuW2_eq_zero_iff _ _).mpr ?_
  show wuClass2 (poincareDual4Mid_of_closed (M := RP4))
    = cupH (wuClass1 (poincareDual4Lo_of_closed (M := RP4)))
        (wuClass1 (poincareDual4Lo_of_closed (M := RP4)))
  rw [wuClass2_eq_xpow2, wuClass1_eq_xpow1]
  exact xpow_two_eq_cupH

/-- **`htie` is a THEOREM**: the Stiefel–Whitney number `w₁⁴[ℝP⁴] = 1` — with `w₁ = v₁ = x`,
the number is `μ(x² ⌣ x²) = 1`. -/
theorem rp4_htie : swNumberW14 RP4 = 1 := by
  show (poincareDual4Mid_of_closed (M := RP4)).mu
    (cupH24 (cupH (w1 RP4) (w1 RP4)) (cupH (w1 RP4) (w1 RP4))) = 1
  rw [show w1 RP4 = wuClass1 (poincareDual4Lo_of_closed (M := RP4)) from rfl,
    wuClass1_eq_xpow1, ← xpow_two_eq_cupH]
  exact mu_cupH24_xpow2_xpow2

/-- **THE REDUCTION, DISCHARGED — the GENUINE unconditional tied `ℤ/16`**: the parity-tied
Pin⁺ carrier's ABK quotient is the whole `ZMod 16`, with **no residual hypothesis** — both
`ℝP⁴` inputs are theorems computed through the Smith double-cover tower. -/
noncomputable def rp4_dataBordismTied_equiv_zmod16 :
    (SKEFTHawking.TangentialDataBordism.DataBordismGrp (pinPlusTiedData (k := 0) (𝓡 4)) ⧸
      ((abkTiedGrade (I := 𝓡 4) (k := 0)) :
        SKEFTHawking.TangentialDataBordism.DataBordismGrp (pinPlusTiedData (k := 0) (𝓡 4))
          →+ ZMod 16).ker) ≃+ ZMod 16 :=
  dataBordismTied_equiv_zmod16_of_rp4 rp4_hcert rp4_htie

end SKEFTHawking.RP4Unconditional
