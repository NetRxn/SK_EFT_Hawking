"""Experimental prediction tables for BEC analog Hawking radiation.

Synthesizes results from Papers 1-4 into platform-specific, publication-ready
prediction tables. Each table provides concrete observables at representative
frequencies, detector sensitivity requirements, and noise floor thresholds.

The predictions include:
    1. Spectral occupation n(omega) at 5 representative frequencies per platform
    2. Correction decomposition: dispersive, dissipative (all orders), noise floor
    3. Required detector sensitivity to distinguish corrections from Planckian
    4. Frequency range where exact WKB deviates >1% from perturbative EFT
    5. Measurement time estimates for noise floor detection
    6. Platform comparison: which platform is best for which measurement

Sources:
    - Paper 1: First-order dissipative correction (delta_diss)
    - Paper 2: Second-order + CGL derivation (delta^(2), positivity constraint)
    - Paper 3: Gauge erasure (structural: only U(1) survives)
    - Paper 4: Exact WKB connection formula (delta_k, n_noise, omega_max)

Lean formalization: References theorems from WKBConnection.lean,
    HawkingUniversality.lean, SecondOrderSK.lean

References:
    - de Nova et al., Nature 569, 688 (2019) — Steinhauer spectrum
    - Sparn et al., PRL 133, 260201 (2024) — Heidelberg analog cosmology
    - Berti et al., Comptes Rendus (2025) — Trento spin-sonic proposal
    - Falque et al., PRL (2025) — Paris polariton negative-energy modes
"""

from dataclasses import dataclass, field
from typing import Optional

import numpy as np

from src.wkb.spectrum import (
    PlatformParams,
    HawkingSpectrum,
    SpectrumPoint,
    compute_spectrum,
    compare_exact_vs_perturbative,
    spectrum_summary,
    steinhauer_platform,
    heidelberg_platform,
    trento_platform,
    ALL_PLATFORMS,
)
from src.core.formulas import (
    dispersive_correction,
    damping_rate,
    decoherence_parameter,
    fdr_noise_floor,
)


# ═══════════════════════════════════════════════════════════════════
# Data structures
# ═══════════════════════════════════════════════════════════════════

@dataclass
class FrequencyPrediction:
    """Prediction at a single frequency for a specific platform.

    Attributes:
        omega_over_T_H: Frequency in units of Hawking temperature.
        n_total: Total occupation number (Hawking + noise).
        n_planck: Standard Planck occupation at T_H.
        n_noise: FDR noise floor contribution.
        fractional_deviation: (n_total - n_planck) / n_planck.
        delta_disp: Dispersive correction.
        delta_diss: Dissipative correction (first-order).
        delta_k: Decoherence parameter.
        dominant_correction: Name of the dominant correction at this frequency.
        snr_per_shot: Signal-to-noise ratio per shot for detecting deviation.
    """
    omega_over_T_H: float
    n_total: float
    n_planck: float
    n_noise: float
    fractional_deviation: float
    delta_disp: float
    delta_diss: float
    delta_k: float
    dominant_correction: str
    snr_per_shot: float


@dataclass
class PredictionTable:
    """Complete prediction table for one experimental platform.

    Attributes:
        platform_name: Human-readable platform identifier.
        atom: Atomic species (e.g., '87Rb').
        params: Platform parameters in natural units.
        T_H: Hawking temperature (natural units).
        omega_max: Critical frequency for UV cutoff.
        omega_max_over_T_H: omega_max in units of T_H.
        predictions: List of FrequencyPrediction at representative omegas.
        summary: Dictionary of summary diagnostics.
        noise_floor_threshold: Minimum n detectable above noise.
        measurement_time_hours: Estimated hours for 3-sigma detection.
        best_frequency_range: (omega_min, omega_max) for optimal detection.
    """
    platform_name: str
    atom: str
    params: PlatformParams
    T_H: float
    omega_max: float
    omega_max_over_T_H: float
    predictions: list[FrequencyPrediction]
    summary: dict
    noise_floor_threshold: float
    measurement_time_hours: float
    best_frequency_range: tuple[float, float]


@dataclass
class DetectorRequirements:
    """Detector sensitivity requirements for a specific measurement goal.

    Attributes:
        platform_name: Platform identifier.
        goal: Description of the measurement goal.
        required_precision: Fractional precision needed (per frequency bin).
        required_shots: Number of experimental shots needed.
        required_time_hours: Measurement time at typical repetition rate.
        frequency_range: Optimal frequency range for this measurement.
        feasible: Whether achievable with current technology.
        limiting_factor: What limits feasibility.
    """
    platform_name: str
    goal: str
    required_precision: float
    required_shots: int
    required_time_hours: float
    frequency_range: tuple[float, float]
    feasible: bool
    limiting_factor: str


@dataclass
class PlatformComparison:
    """Cross-platform comparison for a specific observable.

    Attributes:
        observable: Name of the observable being compared.
        rankings: Dict mapping platform name to rank (1 = best).
        values: Dict mapping platform name to the observable value.
        recommendation: Text recommendation for experimentalists.
    """
    observable: str
    rankings: dict[str, int]
    values: dict[str, float]
    recommendation: str


@dataclass
class MeasurementStrategy:
    """Measurement strategy for a specific platform.

    Attributes:
        platform_name: Platform identifier.
        priority_measurements: Ordered list of measurement targets.
        detector_requirements: Requirements for each measurement.
        comparison: How this platform compares to alternatives.
    """
    platform_name: str
    priority_measurements: list[str]
    detector_requirements: list[DetectorRequirements]
    comparison: dict[str, PlatformComparison]


# ═══════════════════════════════════════════════════════════════════
# Core prediction computation
# ═══════════════════════════════════════════════════════════════════

# Representative frequencies in units of T_H
REPRESENTATIVE_OMEGAS = [0.5, 1.0, 2.0, 3.0, 5.0]

# Typical experimental repetition rate (shots per hour)
SHOTS_PER_HOUR = {
    'Steinhauer_Rb87': 500,     # Steinhauer: ~1 shot/7s
    'Heidelberg_K39': 600,      # Heidelberg: faster cycle
    'Trento_Na23': 400,         # Trento: spin preparation overhead
}

# Current best per-bin precision (Steinhauer 2019: ~30% at 7000 shots)
CURRENT_PRECISION = 0.30
CURRENT_SHOTS = 7000


def _dominant_correction(delta_disp: float, delta_diss: float,
                         n_noise: float, n_planck: float) -> str:
    """Identify which correction dominates at a given frequency."""
    corrections = {
        'dispersive': abs(delta_disp),
        'dissipative': abs(delta_diss),
        'noise_floor': n_noise / max(n_planck, 1e-30),
    }
    return max(corrections, key=corrections.get)


def _snr_per_shot(deviation: float, n_total: float) -> float:
    """Signal-to-noise ratio per shot for detecting the deviation.

    Assumes Poissonian counting statistics: sigma = sqrt(n).
    SNR = |deviation * n_planck| / sqrt(n_total)
    """
    if n_total <= 0 or abs(deviation) < 1e-30:
        return 0.0
    # Signal is the deviation in occupation number
    signal = abs(deviation) * n_total
    # Noise is sqrt(n_total) per shot (counting statistics)
    noise = np.sqrt(max(n_total, 1e-30))
    return signal / noise


def compute_prediction_table(
    platform: PlatformParams,
    omegas_over_T_H: list[float] | None = None,
) -> PredictionTable:
    """Compute a complete prediction table for one platform.

    Evaluates the exact WKB spectrum at representative frequencies and
    packages results into a publication-ready table.

    Args:
        platform: Platform parameters.
        omegas_over_T_H: Frequencies in units of T_H. Defaults to
            REPRESENTATIVE_OMEGAS.

    Returns:
        PredictionTable with all predictions and diagnostics.
    """
    if omegas_over_T_H is None:
        omegas_over_T_H = REPRESENTATIVE_OMEGAS

    # Compute full spectrum for summary diagnostics
    spectrum = compute_spectrum(platform, omega_min=0.1, omega_max_factor=8.0)
    summ = spectrum_summary(spectrum)

    T_H = platform.T_H
    predictions = []

    for omega_ratio in omegas_over_T_H:
        omega = omega_ratio * T_H

        # Find the closest spectrum point
        idx = int(np.argmin(np.abs(spectrum.omega_array - omega)))
        point = spectrum.points[idx]

        dominant = _dominant_correction(
            point.delta_disp, point.delta_diss,
            point.n_noise, point.n_planck,
        )
        snr = _snr_per_shot(point.relative_deviation, point.n_total)

        predictions.append(FrequencyPrediction(
            omega_over_T_H=omega_ratio,
            n_total=point.n_total,
            n_planck=point.n_planck,
            n_noise=point.n_noise,
            fractional_deviation=point.relative_deviation,
            delta_disp=point.delta_disp,
            delta_diss=point.delta_diss,
            delta_k=point.delta_k,
            dominant_correction=dominant,
            snr_per_shot=snr,
        ))

    # Noise floor threshold: minimum n detectable above noise
    noise_threshold = summ.get('n_noise_at_T_H', 0.0)

    # Measurement time estimate
    max_dev = summ.get('max_deviation', 0.0)
    shots_needed = summ.get('shots_needed', float('inf'))
    rate = SHOTS_PER_HOUR.get(platform.name, 500)
    time_hours = shots_needed / rate if shots_needed < float('inf') else float('inf')

    # Best frequency range for detection
    deviations = [abs(p.relative_deviation) for p in spectrum.points]
    if deviations:
        threshold = max(deviations) * 0.5  # frequencies with >50% of peak deviation
        good_indices = [i for i, d in enumerate(deviations) if d > threshold]
        if good_indices:
            best_min = float(spectrum.omega_array[good_indices[0]]) / T_H
            best_max = float(spectrum.omega_array[good_indices[-1]]) / T_H
        else:
            best_min, best_max = 1.0, 3.0
    else:
        best_min, best_max = 1.0, 3.0

    return PredictionTable(
        platform_name=platform.name,
        atom=platform.description.split()[1] if platform.description else platform.name,
        params=platform,
        T_H=T_H,
        omega_max=spectrum.omega_max,
        omega_max_over_T_H=spectrum.omega_max / T_H,
        predictions=predictions,
        summary=summ,
        noise_floor_threshold=noise_threshold,
        measurement_time_hours=time_hours,
        best_frequency_range=(best_min, best_max),
    )


def compute_all_predictions(
    omegas_over_T_H: list[float] | None = None,
) -> dict[str, PredictionTable]:
    """Compute prediction tables for all three BEC platforms.

    Args:
        omegas_over_T_H: Optional custom frequency points.

    Returns:
        Dict mapping platform key to PredictionTable.
    """
    results = {}
    for name, factory in ALL_PLATFORMS.items():
        platform = factory()
        results[name] = compute_prediction_table(platform, omegas_over_T_H)
    return results


# ═══════════════════════════════════════════════════════════════════
# Detector requirements
# ═══════════════════════════════════════════════════════════════════

def compute_detector_requirements(
    platform: PlatformParams,
) -> list[DetectorRequirements]:
    """Compute detector requirements for three measurement goals.

    Goals:
    1. Detect dissipative correction (delta_diss) at 3-sigma
    2. Detect noise floor (n_noise) at 3-sigma
    3. Distinguish exact WKB from perturbative EFT at 3-sigma

    Args:
        platform: Platform parameters.

    Returns:
        List of DetectorRequirements for each goal.
    """
    T_H = platform.T_H
    spectrum = compute_spectrum(platform, omega_min=0.1, omega_max_factor=8.0)
    summ = spectrum_summary(spectrum)
    comparison = compare_exact_vs_perturbative(platform)
    rate = SHOTS_PER_HOUR.get(platform.name, 500)

    requirements = []

    # Goal 1: Detect dissipative correction
    delta_diss = summ['delta_diss_at_T_H']
    if delta_diss > 0:
        precision_1 = delta_diss / 3.0
        shots_1 = int(CURRENT_SHOTS * (CURRENT_PRECISION / precision_1)**2)
        time_1 = shots_1 / rate
        requirements.append(DetectorRequirements(
            platform_name=platform.name,
            goal="Detect first-order dissipative correction (delta_diss)",
            required_precision=precision_1,
            required_shots=shots_1,
            required_time_hours=time_1,
            frequency_range=(0.5, 3.0),
            feasible=shots_1 < 1_000_000,
            limiting_factor="shot noise" if shots_1 < 1_000_000 else "precision below current technology",
        ))
    else:
        requirements.append(DetectorRequirements(
            platform_name=platform.name,
            goal="Detect first-order dissipative correction (delta_diss)",
            required_precision=0.0,
            required_shots=0,
            required_time_hours=0.0,
            frequency_range=(0.5, 3.0),
            feasible=False,
            limiting_factor="delta_diss is zero (no damping)",
        ))

    # Goal 2: Detect noise floor
    n_noise = summ['n_noise_at_T_H']
    n_planck_at_TH = 1.0 / (np.exp(1.0) - 1.0)  # n_Planck at omega = T_H
    if n_noise > 0:
        noise_fraction = n_noise / n_planck_at_TH
        precision_2 = noise_fraction / 3.0
        shots_2 = int(CURRENT_SHOTS * (CURRENT_PRECISION / precision_2)**2)
        time_2 = shots_2 / rate
        requirements.append(DetectorRequirements(
            platform_name=platform.name,
            goal="Detect FDR noise floor (n_noise)",
            required_precision=precision_2,
            required_shots=shots_2,
            required_time_hours=time_2,
            frequency_range=(3.0, 6.0),
            feasible=shots_2 < 10_000_000,
            limiting_factor="shot noise" if shots_2 < 10_000_000 else "noise floor below detector sensitivity",
        ))
    else:
        requirements.append(DetectorRequirements(
            platform_name=platform.name,
            goal="Detect FDR noise floor (n_noise)",
            required_precision=0.0,
            required_shots=0,
            required_time_hours=0.0,
            frequency_range=(3.0, 6.0),
            feasible=False,
            limiting_factor="no noise floor (no damping)",
        ))

    # Goal 3: Distinguish exact WKB from perturbative EFT
    if comparison.crossover_omega is not None:
        crossover_ratio = comparison.crossover_omega / T_H
        precision_3 = 0.01 / 3.0  # need 1% precision for 1% deviation
        shots_3 = int(CURRENT_SHOTS * (CURRENT_PRECISION / precision_3)**2)
        time_3 = shots_3 / rate
        requirements.append(DetectorRequirements(
            platform_name=platform.name,
            goal="Distinguish exact WKB from perturbative EFT (>1% deviation)",
            required_precision=precision_3,
            required_shots=shots_3,
            required_time_hours=time_3,
            frequency_range=(crossover_ratio, 8.0),
            feasible=shots_3 < 100_000_000,
            limiting_factor="shot noise" if shots_3 < 100_000_000 else "difference too small for current detectors",
        ))
    else:
        requirements.append(DetectorRequirements(
            platform_name=platform.name,
            goal="Distinguish exact WKB from perturbative EFT (>1% deviation)",
            required_precision=0.0,
            required_shots=0,
            required_time_hours=0.0,
            frequency_range=(5.0, 8.0),
            feasible=False,
            limiting_factor="no crossover found in computed range",
        ))

    return requirements


# ═══════════════════════════════════════════════════════════════════
# Platform comparison
# ═══════════════════════════════════════════════════════════════════

def compare_platforms(
    tables: dict[str, PredictionTable] | None = None,
) -> list[PlatformComparison]:
    """Compare platforms across key observables.

    Compares Steinhauer, Heidelberg, and Trento on:
    1. Maximum spectral deviation (best for initial detection)
    2. Noise floor visibility (best for FDR test)
    3. UV range (highest omega_max/T_H)
    4. Measurement feasibility (fewest shots needed)

    Args:
        tables: Precomputed prediction tables. If None, computes them.

    Returns:
        List of PlatformComparison for each observable.
    """
    if tables is None:
        tables = compute_all_predictions()

    comparisons = []

    # Observable 1: Maximum spectral deviation
    devs = {name: t.summary['max_deviation'] for name, t in tables.items()}
    ranked = sorted(devs, key=devs.get, reverse=True)
    comparisons.append(PlatformComparison(
        observable="Maximum spectral deviation from Planckian",
        rankings={name: i + 1 for i, name in enumerate(ranked)},
        values=devs,
        recommendation=f"{ranked[0]} has the largest deviation ({devs[ranked[0]]:.1e}), "
                       f"making it the best platform for initial detection of EFT corrections.",
    ))

    # Observable 2: Noise floor relative to signal
    noise_ratios = {}
    for name, t in tables.items():
        n_noise = t.summary.get('n_noise_at_T_H', 0.0)
        n_planck = 1.0 / (np.exp(1.0) - 1.0)
        noise_ratios[name] = n_noise / n_planck if n_planck > 0 else 0.0
    ranked = sorted(noise_ratios, key=noise_ratios.get, reverse=True)
    comparisons.append(PlatformComparison(
        observable="FDR noise floor visibility (n_noise/n_Planck at T_H)",
        rankings={name: i + 1 for i, name in enumerate(ranked)},
        values=noise_ratios,
        recommendation=f"{ranked[0]} has the most visible noise floor ({noise_ratios[ranked[0]]:.1e}), "
                       f"best for testing the fluctuation-dissipation relation.",
    ))

    # Observable 3: UV range
    uv = {name: t.omega_max_over_T_H for name, t in tables.items()}
    ranked = sorted(uv, key=uv.get, reverse=True)
    comparisons.append(PlatformComparison(
        observable="UV spectral range (omega_max / T_H)",
        rankings={name: i + 1 for i, name in enumerate(ranked)},
        values=uv,
        recommendation=f"{ranked[0]} has the widest UV range ({uv[ranked[0]]:.1f} T_H), "
                       f"best for probing non-perturbative WKB effects.",
    ))

    # Observable 4: Measurement feasibility (fewest shots)
    shots = {name: t.summary.get('shots_needed', float('inf'))
             for name, t in tables.items()}
    ranked = sorted(shots, key=shots.get)
    comparisons.append(PlatformComparison(
        observable="Measurement feasibility (shots for 3-sigma detection)",
        rankings={name: i + 1 for i, name in enumerate(ranked)},
        values=shots,
        recommendation=f"{ranked[0]} requires the fewest shots ({shots[ranked[0]]:.2e}), "
                       f"though all platforms need >> 10^6 shots for direct detection.",
    ))

    return comparisons


# ═══════════════════════════════════════════════════════════════════
# Measurement strategy
# ═══════════════════════════════════════════════════════════════════

def measurement_strategy(
    platform: PlatformParams,
    tables: dict[str, PredictionTable] | None = None,
) -> MeasurementStrategy:
    """Generate a measurement strategy for a specific platform.

    Provides an ordered list of measurement priorities, detector
    requirements, and how the platform compares to alternatives.

    Args:
        platform: Platform to generate strategy for.
        tables: Precomputed prediction tables for comparison.

    Returns:
        MeasurementStrategy with prioritized measurement targets.
    """
    table = compute_prediction_table(platform)
    reqs = compute_detector_requirements(platform)

    if tables is None:
        tables = compute_all_predictions()
    comps = compare_platforms(tables)

    # Prioritize measurements by feasibility
    feasible_first = sorted(reqs, key=lambda r: (not r.feasible, r.required_shots))
    priorities = [r.goal for r in feasible_first]

    comp_dict = {c.observable: c for c in comps}

    return MeasurementStrategy(
        platform_name=platform.name,
        priority_measurements=priorities,
        detector_requirements=reqs,
        comparison=comp_dict,
    )


# ═══════════════════════════════════════════════════════════════════
# Kappa-scaling test predictions
# ═══════════════════════════════════════════════════════════════════

@dataclass
class KappaScalingPrediction:
    """Prediction for the kappa-scaling test.

    The Heidelberg K-39 platform can tune scattering length via Feshbach
    resonance, allowing direct measurement of how the Hawking spectrum
    changes with surface gravity kappa.

    The SK-EFT prediction:
        T_eff(kappa) / T_H(kappa) = 1 + delta_disp(kappa) + delta_diss(kappa)

    where delta_disp ~ kappa^2 and delta_diss ~ kappa^0 (constant).

    Attributes:
        kappa_values: Surface gravity values tested.
        T_eff_ratio: T_eff/T_H at each kappa.
        delta_disp_values: Dispersive correction at each kappa.
        delta_diss_values: Dissipative correction at each kappa.
        scaling_exponent_disp: Fitted exponent for delta_disp vs kappa.
        scaling_exponent_diss: Fitted exponent for delta_diss vs kappa.
    """
    kappa_values: np.ndarray
    T_eff_ratio: np.ndarray
    delta_disp_values: np.ndarray
    delta_diss_values: np.ndarray
    scaling_exponent_disp: float
    scaling_exponent_diss: float


def kappa_scaling_prediction(
    n_points: int = 10,
    D_range: tuple[float, float] = (0.01, 0.05),
    gamma_dim: float = 0.002,
) -> KappaScalingPrediction:
    """Compute the kappa-scaling prediction for Heidelberg K-39.

    Varies the adiabaticity parameter D (proportional to kappa at fixed
    xi, c_s) and tracks how corrections scale.

    The key discriminant:
        - delta_disp scales as D^2 ~ kappa^2 (quadratic)
        - delta_diss is approximately constant in D (independent of kappa
          at leading order, since Gamma_H and kappa scale together)

    This difference in scaling provides an experimental handle to separate
    dispersive from dissipative corrections.

    Args:
        n_points: Number of kappa values to evaluate.
        D_range: Range of adiabaticity parameter D.
        gamma_dim: Dimensionless damping rate Gamma_Bel/kappa.

    Returns:
        KappaScalingPrediction with scaling analysis.
    """
    D_values = np.linspace(D_range[0], D_range[1], n_points)
    kappa_values = np.ones(n_points)  # Natural units: kappa = 1
    T_eff_ratios = np.zeros(n_points)
    delta_disp_vals = np.zeros(n_points)
    delta_diss_vals = np.zeros(n_points)

    for i, D in enumerate(D_values):
        platform = PlatformParams(
            name=f"scan_D={D:.3f}",
            D=D,
            gamma_dim=gamma_dim,
        )
        spectrum = compute_spectrum(platform, omega_min=0.8, omega_max_factor=1.2, n_points=5)
        # Evaluate at omega ~ T_H
        mid = len(spectrum.points) // 2
        point = spectrum.points[mid]

        delta_disp_vals[i] = point.delta_disp
        delta_diss_vals[i] = point.delta_diss

        T_eff_ratios[i] = 1.0 + point.delta_disp + point.delta_diss

    # Fit scaling exponents: delta ~ D^alpha
    # log(|delta|) = alpha * log(D) + const
    valid_disp = np.abs(delta_disp_vals) > 1e-30
    if np.sum(valid_disp) > 2:
        log_D = np.log(D_values[valid_disp])
        log_delta = np.log(np.abs(delta_disp_vals[valid_disp]))
        alpha_disp = np.polyfit(log_D, log_delta, 1)[0]
    else:
        alpha_disp = 2.0  # Expected: D^2

    valid_diss = np.abs(delta_diss_vals) > 1e-30
    if np.sum(valid_diss) > 2:
        log_D_d = np.log(D_values[valid_diss])
        log_delta_d = np.log(np.abs(delta_diss_vals[valid_diss]))
        alpha_diss = np.polyfit(log_D_d, log_delta_d, 1)[0]
    else:
        alpha_diss = 0.0  # Expected: D^0

    return KappaScalingPrediction(
        kappa_values=kappa_values,
        T_eff_ratio=T_eff_ratios,
        delta_disp_values=delta_disp_vals,
        delta_diss_values=delta_diss_vals,
        scaling_exponent_disp=alpha_disp,
        scaling_exponent_diss=alpha_diss,
    )
