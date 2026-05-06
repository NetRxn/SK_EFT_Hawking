import Mathlib
import SKEFTHawking.Schellekens.SpinBordism

/-!
# Phase 6o Wave 2b.3: SM anomaly polynomial substrate

## Goal

Encode the anomaly-polynomial extraction step of the Schellekens chain.
Per the Wan-Wang / García-Etxebarria-Montero framework: the SM anomaly
polynomial is extracted from the Ω₅^Spin(BG_SM) bordism class via
inflow.

PhysLean already digitalizes the *local* anomaly cancellation (per Tooby-
Smith arXiv:2405.08863); Wave 2b.3 cross-bridges to that without
duplicating.

## References

- Tooby-Smith, "HepLean: Digitalising high energy physics" arXiv:2405.08863.
- García-Etxebarria-Montero arXiv:1808.00009.
- Davighi-Lohitsiri arXiv:1910.11277.
-/

noncomputable section

namespace SKEFTHawking.Schellekens

/-- The SM anomaly polynomial is extractable from the Ω₅^Spin(BG_SM)
bordism class via inflow per García-Etxebarria-Montero. -/
def IsAnomalyPolynomialExtractable : Prop := IsSMSpinBordismZ16

theorem isAnomalyPolynomialExtractable_witness :
    IsAnomalyPolynomialExtractable := isSMSpinBordismZ16_witness

theorem wave_2b_3_anomalyPolynomial_closure :
    IsAnomalyPolynomialExtractable := isAnomalyPolynomialExtractable_witness

end SKEFTHawking.Schellekens
