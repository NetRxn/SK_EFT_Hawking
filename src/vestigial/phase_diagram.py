"""Phase diagram for the vestigial gravity model.

Scans the coupling constant G/G_c and maps the three phases:
    Phase I   (pre-geometric):    M_E = 0,  M_g = 0
    Phase II  (vestigial metric): M_E = 0,  M_g != 0
    Phase III (full tetrad):      M_E != 0, M_g != 0

The scan can use either mean-field or Monte Carlo.

The phase boundaries are determined by:
    G_c1: pre-geometric -> vestigial (metric susceptibility peak)
    G_c2: vestigial -> full tetrad (tetrad susceptibility peak)

If G_c1 = G_c2, there is no vestigial phase (direct transition).
"""

from dataclasses import dataclass
import numpy as np
from typing import Optional

from src.vestigial.lattice_model import LatticeParams
from src.vestigial.mean_field import (
    MeanFieldParams, MeanFieldResult, full_mean_field_analysis,
    vestigial_phase_window,
)
from src.vestigial.monte_carlo import MCParams, MCResult, run_monte_carlo


@dataclass
class PhasePoint:
    """Phase classification at a single coupling value.

    Attributes:
        coupling_ratio: G / G_c.
        phase: Phase classification string.
        tetrad_vev: Tetrad VEV magnitude.
        metric_mag: Metric correlator magnitude.
        method: "mean_field" or "monte_carlo".
    """
    coupling_ratio: float
    phase: str
    tetrad_vev: float
    metric_mag: float
    method: str


@dataclass
class PhaseDiagramResult:
    """Result of a phase diagram scan.

    Attributes:
        points: List of PhasePoint.
        coupling_ratios: Array of G/G_c values scanned.
        tetrad_values: Array of tetrad VEV values.
        metric_values: Array of metric correlator values.
        phases: List of phase labels.
        vestigial_exists: Whether a vestigial phase window was found.
        vestigial_window: (G_c1/G_c, G_c2/G_c) if vestigial exists.
        method: Method used for the scan.
    """
    points: list[PhasePoint]
    coupling_ratios: np.ndarray
    tetrad_values: np.ndarray
    metric_values: np.ndarray
    phases: list[str]
    vestigial_exists: bool
    vestigial_window: tuple[float, float]
    method: str


def classify_phase_point(tetrad_vev: float, metric_mag: float,
                         threshold_tetrad: float = 0.1,
                         threshold_metric: float = 0.1) -> str:
    """Classify the phase based on order parameters.

    Args:
        tetrad_vev: Tetrad VEV magnitude.
        metric_mag: Metric correlator magnitude.
        threshold_tetrad: Threshold for nonzero tetrad VEV.
        threshold_metric: Threshold for nonzero metric.

    Returns:
        Phase classification string.
    """
    if tetrad_vev > threshold_tetrad:
        return "full_tetrad"
    elif metric_mag > threshold_metric:
        return "vestigial"
    else:
        return "pre_geometric"


def scan_coupling(
    method: str = "mean_field",
    Lambda: float = 1.0,
    N_f: int = 4,
    coupling_range: tuple[float, float] = (0.3, 3.0),
    n_points: int = 30,
    L: int = 4,
    mc_params: Optional[MCParams] = None,
) -> PhaseDiagramResult:
    """Scan coupling constant G/G_c to map the phase diagram.

    Args:
        method: "mean_field" or "monte_carlo".
        Lambda: UV cutoff.
        N_f: Number of fermion species.
        coupling_range: (min, max) of G/G_c to scan.
        n_points: Number of coupling values.
        L: Lattice size (for Monte Carlo).
        mc_params: MC parameters (for Monte Carlo).

    Returns:
        PhaseDiagramResult with the full phase diagram.
    """
    from src.adw.gap_equation import critical_coupling

    G_c = critical_coupling(Lambda, N_f)
    ratios = np.linspace(coupling_range[0], coupling_range[1], n_points)

    points = []
    tetrad_values = []
    metric_values = []
    phases = []

    if method == "mean_field":
        for r in ratios:
            result = full_mean_field_analysis(G=r * G_c, Lambda=Lambda, N_f=N_f)
            C = result.C_tetrad
            G_m = result.G_metric

            # Normalize for comparison
            C_norm = C / Lambda if Lambda > 0 else C
            G_norm = G_m / Lambda**2 if Lambda > 0 else G_m

            phase = classify_phase_point(C_norm, G_norm)

            points.append(PhasePoint(
                coupling_ratio=r,
                phase=phase,
                tetrad_vev=C_norm,
                metric_mag=G_norm,
                method="mean_field",
            ))
            tetrad_values.append(C_norm)
            metric_values.append(G_norm)
            phases.append(phase)

    elif method == "monte_carlo":
        if mc_params is None:
            mc_params = MCParams(
                n_thermalize=50, n_measure=100, n_skip=3,
                step_size=0.3, seed=42,
            )

        for r in ratios:
            lattice_params = LatticeParams(L=L, d=4, G=r * G_c, N_f=N_f)
            mc_result = run_monte_carlo(lattice_params, mc_params)

            C = mc_result.mean_tetrad_vev
            G_m = mc_result.mean_metric_mag
            phase = mc_result.phase_estimate

            points.append(PhasePoint(
                coupling_ratio=r,
                phase=phase,
                tetrad_vev=C,
                metric_mag=G_m,
                method="monte_carlo",
            ))
            tetrad_values.append(C)
            metric_values.append(G_m)
            phases.append(phase)

    else:
        raise ValueError(f"Unknown method: {method}")

    # Check for vestigial window
    vestigial_indices = [i for i, p in enumerate(phases) if p == "vestigial"]
    if vestigial_indices:
        v_min = float(ratios[vestigial_indices[0]])
        v_max = float(ratios[vestigial_indices[-1]])
        vestigial_exists = True
    else:
        v_min = v_max = 0.0
        vestigial_exists = False

    return PhaseDiagramResult(
        points=points,
        coupling_ratios=ratios,
        tetrad_values=np.array(tetrad_values),
        metric_values=np.array(metric_values),
        phases=phases,
        vestigial_exists=vestigial_exists,
        vestigial_window=(v_min, v_max),
        method=method,
    )
