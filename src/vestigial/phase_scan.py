"""Coupling scan for the 4D ADW phase diagram.

Scans the Einstein-Hilbert coupling at fixed cosmological coupling,
measuring tetrad and metric order parameters via fermion-bag MC.
The Binder cumulant crossings between different lattice sizes
locate phase transitions and diagnose the vestigial metric phase.

Go/no-go criterion (from Phase 5 roadmap):
  If two distinct Binder cumulant crossings appear (T_metric > T_tetrad),
  the vestigial phase exists.

References:
    Volovik, JETP Lett. 119, 330 (2024) — vestigial metric phase
    Binder, Z. Phys. B 43, 119 (1981) — Binder cumulant method
"""

import numpy as np
from dataclasses import dataclass, field
from typing import Optional

from src.core.constants import ADW_4D_COUPLING_SCAN, ADW_4D_LATTICE_SIZES
from src.core.formulas import vestigial_phase_indicator
from src.vestigial.lattice_4d import Lattice4DParams
from src.vestigial.fermion_bag import (
    FermionBagParams, FermionBagResult, run_fermion_bag_mc,
)


@dataclass
class PhaseScan4DResult:
    """Result of a 4D coupling scan.

    Attributes:
        g_cosmo: fixed cosmological coupling
        g_EH_values: array of EH couplings scanned
        L: lattice size used
        binder_tetrad: Binder cumulant for tetrad at each coupling
        binder_metric: Binder cumulant for metric at each coupling
        metric_correlator: connected metric correlator at each coupling
        phases: phase classification at each coupling
        acceptance_rates: MC acceptance rate at each coupling
        action_means: mean action at each coupling
    """
    g_cosmo: float
    g_EH_values: np.ndarray
    L: int
    binder_tetrad: np.ndarray
    binder_metric: np.ndarray
    metric_correlator: np.ndarray
    phases: list[str]
    acceptance_rates: np.ndarray
    action_means: np.ndarray


def scan_coupling_4d(g_cosmo: float = ADW_4D_COUPLING_SCAN['g_cosmo'],
                      g_EH_range: tuple[float, float] = ADW_4D_COUPLING_SCAN['g_EH_range'],
                      n_points: int = ADW_4D_COUPLING_SCAN['n_points'],
                      L: int = 4,
                      mc_params: Optional[FermionBagParams] = None) -> PhaseScan4DResult:
    """Scan the Einstein-Hilbert coupling to map the 4D phase diagram.

    At fixed g_cosmo and lattice size L, varies g_EH and runs
    fermion-bag MC at each point. Returns Binder cumulants and
    phase classifications.

    Args:
        g_cosmo: fixed cosmological coupling
        g_EH_range: (min, max) for g_EH scan
        n_points: number of coupling values
        L: lattice size (L^4)
        mc_params: MC parameters

    Returns:
        PhaseScan4DResult with observables at each coupling
    """
    if mc_params is None:
        mc_params = FermionBagParams(
            n_thermalize=100, n_measure=200, n_skip=3, seed=42,
        )

    g_values = np.linspace(g_EH_range[0], g_EH_range[1], n_points)
    binder_t = np.zeros(n_points)
    binder_m = np.zeros(n_points)
    met_corr = np.zeros(n_points)
    phases = []
    acc_rates = np.zeros(n_points)
    act_means = np.zeros(n_points)

    for i, g_EH in enumerate(g_values):
        params = Lattice4DParams(L=L, g_cosmo=g_cosmo, g_EH=g_EH)
        result = run_fermion_bag_mc(params, mc_params)

        binder_t[i] = result.binder_tetrad
        binder_m[i] = result.binder_metric
        met_corr[i] = result.metric_correlator
        phases.append(result.phase)
        acc_rates[i] = result.acceptance_rate
        act_means[i] = result.action_mean

    return PhaseScan4DResult(
        g_cosmo=g_cosmo,
        g_EH_values=g_values,
        L=L,
        binder_tetrad=binder_t,
        binder_metric=binder_m,
        metric_correlator=met_corr,
        phases=phases,
        acceptance_rates=acc_rates,
        action_means=act_means,
    )


@dataclass
class BinderCrossing4DResult:
    """Result of multi-size Binder crossing analysis.

    Attributes:
        g_cosmo: fixed cosmological coupling
        lattice_sizes: L values used
        scans: PhaseScan4DResult for each L
        tetrad_crossing: estimated g_EH at tetrad Binder crossing (or None)
        metric_crossing: estimated g_EH at metric Binder crossing (or None)
        vestigial_window: width of vestigial phase window (or None)
        vestigial_detected: True if two distinct crossings found
    """
    g_cosmo: float
    lattice_sizes: list[int]
    scans: list[PhaseScan4DResult]
    tetrad_crossing: Optional[float]
    metric_crossing: Optional[float]
    vestigial_window: Optional[float]
    vestigial_detected: bool


def _find_crossing(g_values: np.ndarray,
                    binder1: np.ndarray,
                    binder2: np.ndarray) -> Optional[float]:
    """Find the coupling where two Binder cumulant curves cross.

    The crossing is the point where binder1(g) - binder2(g) changes sign.
    Uses linear interpolation between the sign-change points.

    Args:
        g_values: coupling values (shared x-axis)
        binder1: Binder cumulant for lattice size L1
        binder2: Binder cumulant for lattice size L2

    Returns:
        Estimated coupling at crossing, or None if no crossing found
    """
    diff = binder1 - binder2
    sign_changes = np.where(np.diff(np.sign(diff)))[0]

    if len(sign_changes) == 0:
        return None

    # Use the first crossing
    i = sign_changes[0]
    # Linear interpolation
    g_cross = g_values[i] - diff[i] * (g_values[i+1] - g_values[i]) / (diff[i+1] - diff[i])
    return float(g_cross)


def binder_crossing_analysis(g_cosmo: float = ADW_4D_COUPLING_SCAN['g_cosmo'],
                              g_EH_range: tuple[float, float] = ADW_4D_COUPLING_SCAN['g_EH_range'],
                              n_points: int = ADW_4D_COUPLING_SCAN['n_points'],
                              lattice_sizes: list[int] = None,
                              mc_params: Optional[FermionBagParams] = None,
                              ) -> BinderCrossing4DResult:
    """Multi-size Binder cumulant crossing analysis.

    Runs coupling scans at multiple lattice sizes and finds the crossing
    points. Two distinct crossings (metric before tetrad as coupling
    increases) indicate a vestigial phase.

    Args:
        g_cosmo: fixed cosmological coupling
        g_EH_range: coupling range to scan
        n_points: points per scan
        lattice_sizes: list of L values (default: [4, 6])
        mc_params: MC parameters

    Returns:
        BinderCrossing4DResult with crossing analysis
    """
    if lattice_sizes is None:
        lattice_sizes = [4, 6]

    scans = []
    for L in lattice_sizes:
        scan = scan_coupling_4d(g_cosmo, g_EH_range, n_points, L, mc_params)
        scans.append(scan)

    # Find crossings between smallest and largest lattice
    tetrad_crossing = None
    metric_crossing = None

    if len(scans) >= 2:
        tetrad_crossing = _find_crossing(
            scans[0].g_EH_values,
            scans[0].binder_tetrad,
            scans[-1].binder_tetrad,
        )
        metric_crossing = _find_crossing(
            scans[0].g_EH_values,
            scans[0].binder_metric,
            scans[-1].binder_metric,
        )

    # Vestigial window
    vestigial_window = None
    vestigial_detected = False

    if tetrad_crossing is not None and metric_crossing is not None:
        window = abs(metric_crossing - tetrad_crossing)
        if window > 0.01:  # significant separation
            vestigial_window = window
            vestigial_detected = True

    return BinderCrossing4DResult(
        g_cosmo=g_cosmo,
        lattice_sizes=lattice_sizes,
        scans=scans,
        tetrad_crossing=tetrad_crossing,
        metric_crossing=metric_crossing,
        vestigial_window=vestigial_window,
        vestigial_detected=vestigial_detected,
    )


# ════════════════════════════════════════════════════════════════════
# Phase 5d: MF-guided targeted scan
# ════════════════════════════════════════════════════════════════════


@dataclass
class TargetedScanParams:
    """Parameters for a mean-field-guided targeted coupling scan.

    The gap equation predicts G_c = 8π²/(N_f·Λ²). The MC scan
    centers on this prediction with a window accounting for
    fluctuation corrections (G_c^MC ≈ O(1) × G_c^MF).

    Attributes:
        G_c_mf: Mean-field critical coupling from gap equation
        scan_center: Center of the MC scan (= G_c_mf)
        scan_width_factor: Scan ± this factor × G_c_mf
        n_points: Coupling points in the scan
        lattice_sizes: L values for Binder analysis
    """
    G_c_mf: float
    scan_center: float
    scan_width_factor: float = 0.5
    n_points: int = 40
    lattice_sizes: list[int] = field(default_factory=lambda: [4, 6, 8])


def mf_guided_scan_params(
    Lambda: float = np.pi,
    N_f: int = 2,
    width_factor: float = 0.5,
) -> TargetedScanParams:
    """Compute targeted scan parameters from the MF gap equation.

    The scan covers [G_c·(1−width), G_c·(1+width)] to capture
    both the MF prediction and the O(1) fluctuation correction.

    At d=4 (upper critical dimension), the pseudo-critical shift
    scales as ΔG_c ~ L⁻² (from mean-field ν = 1/2):
      L=4:  6.25% shift
      L=6:  2.78% shift
      L=8:  1.56% shift

    Args:
        Lambda: UV cutoff (lattice: π/a with a=1)
        N_f: Dirac fermion species
        width_factor: Scan window as fraction of G_c

    Returns:
        TargetedScanParams with MF-guided scan region
    """
    from src.core.formulas import tetrad_critical_coupling_integral

    G_c_mf = tetrad_critical_coupling_integral(Lambda, N_f)

    return TargetedScanParams(
        G_c_mf=G_c_mf,
        scan_center=G_c_mf,
        scan_width_factor=width_factor,
    )


def targeted_binder_analysis(
    params: TargetedScanParams,
    g_cosmo: float = 1.0,
    mc_params: Optional[FermionBagParams] = None,
) -> BinderCrossing4DResult:
    """Run Binder crossing analysis centered on the MF-predicted G_c.

    Maps g_EH = −G (attractive convention) around the predicted
    critical coupling. The sign convention: g_EH < 0 means attractive
    bonds, which is the physical ADW regime.

    Args:
        params: Targeted scan parameters (from mf_guided_scan_params)
        g_cosmo: Cosmological coupling (fixed)
        mc_params: MC parameters

    Returns:
        BinderCrossing4DResult with MF-guided scan
    """
    # Convert G_c to g_EH convention: g_EH = -G (attractive)
    g_center = -params.scan_center
    g_width = params.scan_width_factor * abs(g_center)
    g_EH_range = (g_center - g_width, g_center + g_width)

    return binder_crossing_analysis(
        g_cosmo=g_cosmo,
        g_EH_range=g_EH_range,
        n_points=params.n_points,
        lattice_sizes=params.lattice_sizes,
        mc_params=mc_params,
    )
