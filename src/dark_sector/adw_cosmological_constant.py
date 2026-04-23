"""Phase 5x Wave 3: ADW-Derived Cosmological Constant.

Computational companion to ``lean/SKEFTHawking/CosmologicalConstant.lean``.

Implements:

- **Volovik de Sitter double-temperature relation** — T_dS = 2 × T_GH, where
  T_GH = H/(2π) is Gibbons-Hawking and T_dS = H/π is the Volovik
  de Sitter temperature governing local KMS processes.
- **ADW vacuum energy magnitude** — ρ_vac ~ (2.8 meV)⁴ vs observed
  ρ_Λ ~ (2.3 meV)⁴ (Planck ΛCDM). The ~20% magnitude match is the
  surviving empirical hook of the ADW/Klinkhamer-Volovik framework
  after ⚡W1b (see below).
- **Klinkhamer-Volovik ⚡W1b correction** — KV oscillating vacuum
  predicts (w₀, wₐ) = (-1, 0) for the current epoch (CDM-like),
  excluded at 2.9σ (Pantheon+) to 4.4σ (DESY5) by DESI DR2. The
  oscillations are Planck-scale (~10⁻⁴⁴ s) with w_eff=0, not
  cosmological. This module encodes the corrected claims, not the
  pre-W1b "explains DESI" claim.
- **Comparative DE context** — QCD topological dark energy bridge
  (Van Waerbeke-Zhitnitsky 2025) is the strongest surviving
  DESI-compatible empirical hook from the KV framework.

Physics references
------------------
- Volovik, JLTP 2025 — de Sitter double-temperature mechanism (T_dS=H/π)
- Klinkhamer-Volovik, PRD 2024 — oscillating vacuum (now W1b-corrected)
- Van Waerbeke-Zhitnitsky 2025, arXiv:2506.14182 — QCD topological DE
- Planck 2018 + DESI DR2 — observed ρ_Λ ~ (2.3 meV)⁴, evolving-DE
  tension 2.8-4.2σ

Lean anchors
------------
- CosmologicalConstant.T_dS_double_TGH
- CosmologicalConstant.T_dS_pos / T_GH_pos / T_dS_gt_T_GH
- CosmologicalConstant.quartic_CW_critical_point
- CosmologicalConstant.lambda_magnitude_ratio
"""

from __future__ import annotations

import math
from dataclasses import dataclass

#: Volovik-predicted vacuum energy scale (in meV).
#:
#: Derived from the ADW infrared dominant-energy-density argument.
#: See Volovik JLTP 2025 §4 and Phase 5x Wave 1 Task 2 deep research.
T_ADW_PREDICTED_meV = 2.8

#: Observed Planck ΛCDM vacuum energy scale (in meV).
#:
#: ρ_Λ^obs ≈ (2.3 meV)⁴ from ρ_crit = 3 H₀² / (8πG) × Ω_Λ with
#: H₀ ≈ 67.4 km/s/Mpc, Ω_Λ ≈ 0.685.
T_OBSERVED_meV = 2.3

#: Approximate ADW/observed Λ-magnitude ratio ≈ (2.8/2.3)⁴.
#:
#: Equals ``lambda_magnitude_ratio(T_ADW_PREDICTED_meV, T_OBSERVED_meV)``.
#: ~20% accuracy on the scale, the tightest structural coincidence
#: known for the CC problem.
LAMBDA_RATIO_ADW_OBSERVED = (T_ADW_PREDICTED_meV / T_OBSERVED_meV) ** 4


def gibbons_hawking_temperature(H: float) -> float:
    """Gibbons-Hawking de Sitter temperature `T_GH = H / (2π)`.

    Standard horizon temperature from the analytic continuation of the
    de Sitter metric.

    Lean: ``CosmologicalConstant.gibbons_hawking_temperature``.
    """
    return H / (2.0 * math.pi)


def de_sitter_temperature_volovik(H: float) -> float:
    """Volovik de Sitter temperature `T_dS = H / π`.

    Derived from the "modified spatial translation" symmetry
    r → r - e^{Ht}·a of the de Sitter metric. Governs local de Sitter
    processes (ionization, proton decay) via KMS at this temperature —
    distinct from the Gibbons-Hawking horizon temperature.

    Lean: ``CosmologicalConstant.de_sitter_temperature_volovik``.
    """
    return H / math.pi


def volovik_gh_ratio() -> float:
    """Exact ratio T_dS / T_GH = 2.

    Lean: ``CosmologicalConstant.T_dS_double_TGH``.
    """
    return 2.0


def lambda_magnitude_ratio(T_predicted_meV: float, T_observed_meV: float) -> float:
    """Ratio of predicted to observed vacuum energy density magnitudes.

    Both inputs are IR energy scales in meV; the returned ratio is
    `(T_predicted / T_observed)⁴` — the factor by which the predicted
    ρ_vac exceeds the observed ρ_Λ.

    For the W1b-corrected ADW claim: `(2.8/2.3)⁴ ≈ 2.20`, i.e. ~20%
    accuracy on the energy scale.

    Lean: ``CosmologicalConstant.lambda_magnitude_ratio``.
    """
    if T_predicted_meV <= 0 or T_observed_meV <= 0:
        raise ValueError(
            "Both T_predicted_meV and T_observed_meV must be positive"
        )
    return (T_predicted_meV / T_observed_meV) ** 4


def lambda_energy_density_meV4(T_meV: float) -> float:
    """Volovik prediction `ρ_vac ≈ T⁴` with T the IR dominant scale.

    Returns the energy density in (meV)⁴ units. Multiply by
    1.602e-3 to convert to (eV)⁴, or use physical-unit conversions
    via constants.py for SI/cosmology joules-per-volume.
    """
    if T_meV <= 0:
        raise ValueError("T_meV must be positive")
    return T_meV**4


@dataclass(frozen=True)
class KlinkhamerVolovikPrediction:
    """Frozen-plateau prediction of the Klinkhamer-Volovik model.

    ⚡W1b correction: the original KV prediction of cosmological-scale
    oscillations was excluded by DESI DR2 (Pantheon+ 2.9σ, DESY5
    4.4σ). At the current epoch KV predicts (w₀, wₐ) = (-1, 0) —
    identical to a frozen cosmological constant — and the oscillations
    are Planck-scale (period ~ 10⁻⁴⁴ s) with time-averaged w_eff = 0.

    See Phase 5x Wave 1b Task 7 deep research for the full analysis.
    """

    w0: float = -1.0
    wa: float = 0.0
    oscillation_period_seconds: float = 1e-44  # Planck scale
    w_effective_time_averaged: float = 0.0
    desi_dr2_exclusion_sigma_pantheon_plus: float = 2.9
    desi_dr2_exclusion_sigma_desy5: float = 4.4


def klinkhamer_volovik_prediction() -> KlinkhamerVolovikPrediction:
    """Return the W1b-corrected Klinkhamer-Volovik DE prediction.

    This is a **withdrawn** phenomenological claim — the oscillations
    do not produce cosmological-scale evolving w(z); the observed
    DESI DR2 dynamics are NOT explained by KV alone. The surviving
    hooks are: (a) Λ magnitude prediction (see
    ``lambda_magnitude_ratio``); (b) QCD topological DE bridge
    (external to this module; see Van Waerbeke-Zhitnitsky 2025).

    Use this return value for KV-vs-DESI comparisons; do not use it
    as evidence that KV explains the DESI signal.
    """
    return KlinkhamerVolovikPrediction()


def adw_predicted_vs_observed_energy_ratio() -> float:
    """Canonical ADW/observed Λ-magnitude ratio.

    Equals ``lambda_magnitude_ratio(T_ADW_PREDICTED_meV, T_OBSERVED_meV)``,
    i.e. (2.8/2.3)⁴ ≈ 2.20. Surviving W1b empirical hook.
    """
    return lambda_magnitude_ratio(T_ADW_PREDICTED_meV, T_OBSERVED_meV)


def quartic_CW_critical_point(A: float, B: float) -> tuple[float, float]:
    """Critical point of the quartic Coleman-Weinberg potential.

    For `V_CW(C) = -A·C² + B·C⁴` with A, B > 0, returns the pair
    (C₀, V_eff(C₀)) where C₀² = A/(2B) and V_eff(C₀) = -A²/(4B).

    Algebraic backbone of the ADW effective-potential minimum;
    the specific ADW identity `V_eff(C₀) = -Λ⁴/(4e)` at
    `C₀ = Λ·e^(-1/4)` requires fitting the full one-loop
    logarithmic potential to this quartic form, which is deferred.

    Lean: ``CosmologicalConstant.quartic_CW_critical_point``.
    """
    if A <= 0 or B <= 0:
        raise ValueError("A and B must both be positive")
    C0 = math.sqrt(A / (2.0 * B))
    V0 = -(A**2) / (4.0 * B)
    return C0, V0


@dataclass(frozen=True)
class CosmologicalConstantAssessment:
    """Summary of the W1b-corrected ADW cosmological-constant case.

    Fields record: the ADW Λ-magnitude accuracy (surviving hook),
    the withdrawn KV evolving-DE prediction, and the recommended
    Paper 17 claim status.
    """

    lambda_ratio_adw_observed: float
    lambda_accuracy_percent: float  # deviation in energy scale (not ρ)
    kv_prediction: KlinkhamerVolovikPrediction
    kv_explains_desi: bool  # ⚡W1b: False; was True pre-W1b
    surviving_hook_notes: tuple[str, ...]


def assess_cosmological_constant_status() -> CosmologicalConstantAssessment:
    """Structured W1b-corrected assessment of ADW's CC case.

    Returns a `CosmologicalConstantAssessment` with the surviving
    empirical hooks after the Phase 5x Wave 1b deep-research
    correction. No new claims — just structured reporting.
    """
    ratio = adw_predicted_vs_observed_energy_ratio()
    # Magnitude accuracy on the energy scale:
    # T_predicted / T_observed = 2.8/2.3 ≈ 1.217; |1 − 1.217| ≈ 21.7%
    accuracy_pct = abs(T_ADW_PREDICTED_meV - T_OBSERVED_meV) / T_OBSERVED_meV * 100.0
    return CosmologicalConstantAssessment(
        lambda_ratio_adw_observed=ratio,
        lambda_accuracy_percent=accuracy_pct,
        kv_prediction=klinkhamer_volovik_prediction(),
        kv_explains_desi=False,  # ⚡W1b
        surviving_hook_notes=(
            "ADW predicts ρ_vac ~ (2.8 meV)⁴ vs observed (2.3 meV)⁴ "
            f"({accuracy_pct:.1f}% accuracy on scale)",
            "KV oscillations are Planck-scale (~10⁻⁴⁴ s), not cosmological",
            "DESI DR2 excludes KV (w₀,wₐ)=(-1,0) at 2.9σ Pantheon+ / 4.4σ DESY5",
            "QCD topological DE (Van Waerbeke-Zhitnitsky 2025) is the "
            "strongest surviving DESI-compatible bridge from the framework",
            "Falsifiable: DESI DR3 (2026-2027) will either reinforce or "
            "weaken the evolving-DE signal",
        ),
    )
