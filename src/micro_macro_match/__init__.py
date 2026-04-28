"""Phase 6e Wave 5: Microscopic-to-Macroscopic Coefficient Match.

Numerical companion to ``lean/SKEFTHawking/MicroscopicCoefficientMatch.lean``.

Combines the Wave 1 heat-kernel result ``a_0(N_f) = 4 N_f / (4π)²`` with
the Wave 2 Stelle-basis higher-curvature triple ``(α, β, γ)`` and the
Phase 6a.1 ADW-rescaling ``G_N^emerg = α_ADW · G_N_sakharov`` into a
unified microscopic prediction surface and assesses the **Decision Gate
E.4** outcome:

  Under natural microscopic parameters ``(Λ_UV ≃ M_Pl, N_f = N_f^SM)``,
  the heat-kernel-induced ``Λ^emerg = a_0(N_f) · Λ_UV⁴`` exceeds the
  Planck-2018 observed value ``Λ_obs ≃ 2.6 × 10⁻⁴⁷ GeV⁴`` by ~10¹²².
  The classical cosmological-constant problem is **reproduced** in the
  emergent-gravity formulation; no fine-tuning of ``(Λ_UV, N_f)``
  resolves it within the natural parameter band.

Submodules:

- ``lambda_emerg_from_micro`` — ``Λ^emerg(Λ_UV, N_f)`` evaluator,
  parameter scan, decision-gate verdict labelling.
- ``g_n_emerg_from_micro`` — microscopic ``G_N`` and Wave-5 match
  residual evaluator over ``α_ADW`` scans.
- ``cc_problem_assessment`` — natural-parameter scan, resolution-locus
  diagnostic, Decision Gate E.4 verdict aggregator.
"""

from src.micro_macro_match.lambda_emerg_from_micro import (
    LambdaEmergPrediction,
    lambda_emerg_at_point,
    lambda_emerg_scan_over_lambdaUV,
    lambda_emerg_scan_over_N_f,
    decision_gate_e4_verdict,
)
from src.micro_macro_match.g_n_emerg_from_micro import (
    GNMatchResult,
    g_n_microscopic_at_point,
    match_residual_scan_over_alpha,
    match_holds,
)
from src.micro_macro_match.cc_problem_assessment import (
    CCProblemAssessment,
    assess_cc_problem,
    natural_parameter_scan,
    resolution_locus_diagnostic,
)

__all__ = [
    "LambdaEmergPrediction",
    "lambda_emerg_at_point",
    "lambda_emerg_scan_over_lambdaUV",
    "lambda_emerg_scan_over_N_f",
    "decision_gate_e4_verdict",
    "GNMatchResult",
    "g_n_microscopic_at_point",
    "match_residual_scan_over_alpha",
    "match_holds",
    "CCProblemAssessment",
    "assess_cc_problem",
    "natural_parameter_scan",
    "resolution_locus_diagnostic",
]
