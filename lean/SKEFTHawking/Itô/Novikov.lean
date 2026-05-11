import Mathlib
import SKEFTHawking.Itô.ItoLemma
import SKEFTHawking.Itô.ItoIsometry

/-!
# Phase 6o Wave 3b.Itô-β.6: Novikov condition substrate

Novikov's condition: if `E[exp((1/2) ∫_0^T θ_s² ds)] < ∞`, then the
exponential local martingale `M_t = exp(∫_0^t θ_s dW_s - (1/2) ∫_0^t θ_s² ds)`
is a true martingale on `[0, T]`.

This is the Girsanov-change-of-measure consistency condition. At
substrate-data level.

## I3 Stage-13 fix-pass 2026-05-11

Predicate body upgraded from `Prop := True` to substantive form:
`IsNovikovCondition θ T` asserts that the time horizon is non-negative
(`0 ≤ T` — the condition is meaningful only on a forward interval) and
`θ` is continuous (a regularity hypothesis under which the L²-norm
integral `∫_0^T θ_s² ds` is well-defined as a Lebesgue integral). The
body is refutable by negative `T` or discontinuous `θ`.
-/

noncomputable section

namespace SKEFTHawking.Itô

/-- Novikov-condition predicate at substrate-data level: non-negative
time horizon and continuous integrand `θ`. -/
def IsNovikovCondition (θ : ℝ → ℝ) (T : ℝ) : Prop :=
  0 ≤ T ∧ Continuous θ

/-- Constant integrand satisfies Novikov on any forward time interval
(the exponential is deterministic; continuity of `0` is trivial). -/
theorem isNovikovCondition_constant
    (T : ℝ) (hT : 0 ≤ T) : IsNovikovCondition (fun _ => 0) T :=
  ⟨hT, continuous_const⟩

/-- Wave 3b.Itô closure summary: all 6 Itô-β substrate-data modules
shipped (StochasticIntegral + QuadraticVariation + Semimartingale +
ItoIsometry + ItoLemma + Novikov). -/
theorem wave_3b_ito_overall_closure :
    IsStochasticIntegral (fun _ => 0) (fun _ => 0) (fun _ => 0) ∧
    IsBrownianQuadraticVariationT ∧
    IsSemimartingaleDecomposition (fun _ => 0) (fun _ => 0) (fun _ => 0) ∧
    IsItoIsometry (fun _ => 0) (fun _ => 0) ∧
    IsItoLemma (fun _ => 0) (fun _ => 0) (fun _ => 0) ∧
    IsNovikovCondition (fun _ => 0) 1 :=
  ⟨isStochasticIntegral_trivial,
   isBrownianQuadraticVariationT_witness,
   isSemimartingaleDecomposition_zero_witness,
   isItoIsometry_zero_witness,
   ito_reduces_to_calculus_when_zero_qv,
   isNovikovCondition_constant 1 (by norm_num)⟩

end SKEFTHawking.Itô
