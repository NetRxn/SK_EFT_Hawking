"""Finite-size scaling analysis for the vestigial gravity simulation.

Strengthens the vestigial phase detection by:
1. Running MC at multiple lattice sizes (L=4,6,8)
2. Computing Binder cumulants for tetrad and metric order parameters
3. Testing whether the vestigial phase window survives L → infinity
4. Sign reweighting from the Euclidean ensemble to probe Lorentzian signature

The Binder cumulant U_L = 1 - <m^4>/(3<m^2>^2) crosses at a universal
value at a second-order phase transition. If the tetrad and metric Binder
cumulant crossings occur at different couplings, the vestigial phase
exists as a separate thermodynamic phase (not a crossover artifact).

Sign reweighting: for the Lorentzian case, eta_ab = diag(-1,+1,+1,+1)
and the action acquires a sign. The average sign <sign> = <exp(-Delta S)>_E
measures whether the Lorentzian signal survives. If <sign> > 0.01, the
vestigial phase is detectable in the Lorentzian theory.

Reference: Fernandes et al., Phys. Rep. 932, 1 (2021) — vestigial order review
Reference: Binder, Z. Phys. B 43, 119 (1981) — Binder cumulant method
"""

from dataclasses import dataclass, field
import numpy as np
from typing import Optional

from src.core.constants import FERMION_BAG, ADW_4D_FSS
from src.core.formulas import binder_cumulant as _binder_cumulant
from src.vestigial.lattice_model import (
    LatticeParams, LatticeConfig, create_lattice,
    tetrad_order_parameter, metric_order_parameter,
    site_action,
)
from src.vestigial.monte_carlo import MCParams, MCResult, run_monte_carlo


@dataclass
class BinderCumulant:
    """Binder cumulant for an order parameter at a given (L, G/G_c).

    U_L = 1 - <m^4> / (3 <m^2>^2)

    At a second-order phase transition, U_L crosses at a universal value
    independent of L. If metric and tetrad cumulants cross at different
    G/G_c, the vestigial phase is a genuine thermodynamic phase.

    Attributes:
        L: Lattice size.
        coupling_ratio: G / G_c.
        U_tetrad: Binder cumulant for the tetrad order parameter.
        U_metric: Binder cumulant for the metric order parameter.
        m2_tetrad: <|M_E|^2>.
        m4_tetrad: <|M_E|^4>.
        m2_metric: <|M_g|^2>.
        m4_metric: <|M_g|^4>.
    """
    L: int
    coupling_ratio: float
    U_tetrad: float
    U_metric: float
    m2_tetrad: float
    m4_tetrad: float
    m2_metric: float
    m4_metric: float


@dataclass
class SusceptibilityPeak:
    """Location and height of a susceptibility peak.

    The susceptibility chi = L^d * (<m^2> - <|m|>^2) diverges at a
    phase transition. The peak location gives G_c and the peak height
    scales as L^{gamma/nu} for a second-order transition.

    Attributes:
        L: Lattice size.
        peak_coupling: G/G_c at the susceptibility peak.
        peak_height: Maximum chi value.
        order_param_type: "tetrad" or "metric".
    """
    L: int
    peak_coupling: float
    peak_height: float
    order_param_type: str


@dataclass
class FiniteSizeResult:
    """Complete finite-size scaling analysis.

    Attributes:
        lattice_sizes: List of L values used.
        binder_data: Dict mapping L to list of BinderCumulant at each coupling.
        susceptibility_peaks_tetrad: Peak locations for tetrad chi.
        susceptibility_peaks_metric: Peak locations for metric chi.
        tetrad_crossing: G/G_c where tetrad Binder cumulants cross (if found).
        metric_crossing: G/G_c where metric Binder cumulants cross (if found).
        vestigial_survives: Whether the vestigial phase window persists at all L.
        split_transition: Whether tetrad and metric transitions are at different G/G_c.
    """
    lattice_sizes: list[int]
    binder_data: dict[int, list[BinderCumulant]]
    susceptibility_peaks_tetrad: list[SusceptibilityPeak]
    susceptibility_peaks_metric: list[SusceptibilityPeak]
    tetrad_crossing: Optional[float]
    metric_crossing: Optional[float]
    vestigial_survives: bool
    split_transition: bool


@dataclass
class SignReweightingResult:
    """Result of Lorentzian sign reweighting from the Euclidean ensemble.

    The average sign <sign> = <exp(-Delta S)>_Euclidean where
    Delta S = S_Lorentzian - S_Euclidean measures the overlap between
    Euclidean and Lorentzian ensembles.

    Attributes:
        coupling_ratio: G / G_c.
        L: Lattice size.
        avg_sign: <sign> — the reweighting factor.
        avg_sign_err: Standard error of <sign>.
        delta_S_mean: Mean action difference.
        delta_S_std: Std of action difference.
        lorentzian_viable: Whether <sign> is large enough for reliable extraction.
        n_configs: Number of configurations used.
    """
    coupling_ratio: float
    L: int
    avg_sign: float
    avg_sign_err: float
    delta_S_mean: float
    delta_S_std: float
    lorentzian_viable: bool
    n_configs: int


def compute_binder_cumulant(mc_result: MCResult,
                            coupling_ratio: float) -> BinderCumulant:
    """Compute Binder cumulants from MC measurements.

    U_L = 1 - <m^4> / (3 <m^2>^2)

    Args:
        mc_result: Monte Carlo result with measurements.
        coupling_ratio: G/G_c for this run.

    Returns:
        BinderCumulant with both tetrad and metric cumulants.
    """
    L = mc_result.lattice_params.L

    tetrad_mags = np.array([m.tetrad_vev for m in mc_result.measurements])
    metric_mags = np.array([m.metric_mag for m in mc_result.measurements])

    m2_t = float(np.mean(tetrad_mags**2))
    m4_t = float(np.mean(tetrad_mags**4))
    m2_g = float(np.mean(metric_mags**2))
    m4_g = float(np.mean(metric_mags**4))

    U_t = _binder_cumulant(m2_t, m4_t)
    U_g = _binder_cumulant(m2_g, m4_g)

    return BinderCumulant(
        L=L, coupling_ratio=coupling_ratio,
        U_tetrad=U_t, U_metric=U_g,
        m2_tetrad=m2_t, m4_tetrad=m4_t,
        m2_metric=m2_g, m4_metric=m4_g,
    )


def find_susceptibility_peak(
    coupling_ratios: np.ndarray,
    chi_values: np.ndarray,
    L: int,
    order_param_type: str,
) -> SusceptibilityPeak:
    """Find the susceptibility peak from a coupling scan.

    Args:
        coupling_ratios: Array of G/G_c values.
        chi_values: Susceptibility at each coupling.
        L: Lattice size.
        order_param_type: "tetrad" or "metric".

    Returns:
        SusceptibilityPeak at the maximum.
    """
    i_peak = int(np.argmax(chi_values))
    return SusceptibilityPeak(
        L=L,
        peak_coupling=float(coupling_ratios[i_peak]),
        peak_height=float(chi_values[i_peak]),
        order_param_type=order_param_type,
    )


def find_binder_crossing(
    binders_L1: list[BinderCumulant],
    binders_L2: list[BinderCumulant],
    param_type: str = "tetrad",
) -> Optional[float]:
    """Find where Binder cumulants for two lattice sizes cross.

    Args:
        binders_L1: Binder data for smaller L.
        binders_L2: Binder data for larger L.
        param_type: "tetrad" or "metric".

    Returns:
        G/G_c at the crossing point, or None if no crossing found.
    """
    get_U = lambda b: b.U_tetrad if param_type == "tetrad" else b.U_metric

    # Match coupling ratios
    couplings_1 = {b.coupling_ratio: get_U(b) for b in binders_L1}
    couplings_2 = {b.coupling_ratio: get_U(b) for b in binders_L2}

    common = sorted(set(couplings_1.keys()) & set(couplings_2.keys()))
    if len(common) < 2:
        return None

    # Find sign change of (U_L1 - U_L2)
    for i in range(len(common) - 1):
        g1, g2 = common[i], common[i + 1]
        diff1 = couplings_1[g1] - couplings_2[g1]
        diff2 = couplings_1[g2] - couplings_2[g2]
        if diff1 * diff2 < 0:
            # Linear interpolation for crossing point
            t = diff1 / (diff1 - diff2)
            return g1 + t * (g2 - g1)

    return None


def finite_size_scaling(
    lattice_sizes: list[int] = [4, 6, 8],
    coupling_range: tuple[float, float] = (0.5, 2.5),
    n_couplings: int = 15,
    mc_params: Optional[MCParams] = None,
    N_f: int = 4,
) -> FiniteSizeResult:
    """Run finite-size scaling analysis across multiple lattice sizes.

    For each (L, G/G_c), runs MC and computes Binder cumulants and
    susceptibilities. Then finds crossing points and susceptibility peaks
    to determine whether the vestigial phase is a genuine thermodynamic phase.

    Args:
        lattice_sizes: List of L values to simulate.
        coupling_range: (min, max) G/G_c range.
        n_couplings: Number of coupling values to scan.
        mc_params: MC parameters (defaults to moderate statistics).
        N_f: Number of fermion species.

    Returns:
        FiniteSizeResult with the complete analysis.
    """
    if mc_params is None:
        mc_params = MCParams(
            n_thermalize=FERMION_BAG['n_thermalize'],
            n_measure=FERMION_BAG['n_measure'],
            n_skip=FERMION_BAG['n_skip'],
            step_size=0.3, seed=42,
        )

    from src.adw.gap_equation import critical_coupling
    Lambda = 1.0
    G_c = critical_coupling(Lambda, N_f)
    ratios = np.linspace(coupling_range[0], coupling_range[1], n_couplings)

    binder_data: dict[int, list[BinderCumulant]] = {}
    susc_peaks_tetrad: list[SusceptibilityPeak] = []
    susc_peaks_metric: list[SusceptibilityPeak] = []

    for L in lattice_sizes:
        binders_L = []
        chi_tetrad = []
        chi_metric = []

        for r in ratios:
            lattice_params = LatticeParams(L=L, d=4, G=r * G_c, N_f=N_f)
            mc_result = run_monte_carlo(lattice_params, mc_params)

            binder = compute_binder_cumulant(mc_result, r)
            binders_L.append(binder)

            # Susceptibility: chi = V * (<m^2> - <|m|>^2)
            V = L**4
            tetrad_mags = [m.tetrad_vev for m in mc_result.measurements]
            metric_mags = [m.metric_mag for m in mc_result.measurements]

            chi_t = V * (np.mean(np.array(tetrad_mags)**2)
                         - np.mean(np.abs(tetrad_mags))**2)
            chi_m = V * (np.mean(np.array(metric_mags)**2)
                         - np.mean(np.abs(metric_mags))**2)
            chi_tetrad.append(chi_t)
            chi_metric.append(chi_m)

        binder_data[L] = binders_L

        susc_peaks_tetrad.append(
            find_susceptibility_peak(ratios, np.array(chi_tetrad), L, "tetrad")
        )
        susc_peaks_metric.append(
            find_susceptibility_peak(ratios, np.array(chi_metric), L, "metric")
        )

    # Find Binder crossings between smallest and largest L
    L_min, L_max = min(lattice_sizes), max(lattice_sizes)
    tetrad_crossing = find_binder_crossing(
        binder_data[L_min], binder_data[L_max], "tetrad"
    )
    metric_crossing = find_binder_crossing(
        binder_data[L_min], binder_data[L_max], "metric"
    )

    # Determine if vestigial phase survives
    # Check: do susceptibility peaks for tetrad and metric occur at different couplings?
    if susc_peaks_tetrad and susc_peaks_metric:
        peak_diff = abs(susc_peaks_tetrad[-1].peak_coupling
                        - susc_peaks_metric[-1].peak_coupling)
        split = peak_diff > 0.05  # threshold for "different"
    else:
        split = False

    # Vestigial survives if the metric transition precedes the tetrad transition
    # at all lattice sizes
    vestigial_survives = True
    for L in lattice_sizes:
        t_peak = next((p for p in susc_peaks_tetrad if p.L == L), None)
        m_peak = next((p for p in susc_peaks_metric if p.L == L), None)
        if t_peak and m_peak:
            if m_peak.peak_coupling >= t_peak.peak_coupling:
                vestigial_survives = False

    return FiniteSizeResult(
        lattice_sizes=lattice_sizes,
        binder_data=binder_data,
        susceptibility_peaks_tetrad=susc_peaks_tetrad,
        susceptibility_peaks_metric=susc_peaks_metric,
        tetrad_crossing=tetrad_crossing,
        metric_crossing=metric_crossing,
        vestigial_survives=vestigial_survives,
        split_transition=split,
    )


def sign_reweighting(
    coupling_ratio: float,
    L: int = 4,
    mc_params: Optional[MCParams] = None,
    N_f: int = 4,
) -> SignReweightingResult:
    """Estimate the Lorentzian average sign from the Euclidean ensemble.

    The Lorentzian action differs from Euclidean by the sign of the
    e^0_mu components: S_L - S_E = -(1/G) sum_x (e^0_mu)^2.

    The average sign is <exp(-Delta S)>_E. If this is O(1), the
    Lorentzian physics is accessible from the Euclidean ensemble.
    If it's exponentially small in volume, the sign problem is severe.

    Args:
        coupling_ratio: G / G_c.
        L: Lattice size.
        mc_params: MC parameters for the Euclidean run.
        N_f: Number of fermion species.

    Returns:
        SignReweightingResult with the sign estimate.
    """
    if mc_params is None:
        mc_params = MCParams(
            n_thermalize=FERMION_BAG['n_thermalize'],
            n_measure=FERMION_BAG['n_measure'],
            n_skip=FERMION_BAG['n_skip'],
            step_size=0.3, seed=42,
        )

    from src.adw.gap_equation import critical_coupling
    Lambda = 1.0
    G_c = critical_coupling(Lambda, N_f)
    G = coupling_ratio * G_c

    # Run Euclidean MC
    lattice_params = LatticeParams(L=L, d=4, G=G, N_f=N_f, euclidean=True)
    mc_result = run_monte_carlo(lattice_params, mc_params)

    # For each Euclidean config, get Delta S = S_Lorentzian - S_Euclidean
    # ΔS = -(1/G) Σ_x (e^0_μ(x))^2  (always negative)
    delta_S_values = []

    # Use exact ΔS computed from full config during MC (preferred)
    if mc_result.measurements and mc_result.measurements[0].delta_S_lorentzian is not None:
        delta_S_values = [m.delta_S_lorentzian for m in mc_result.measurements]
    else:
        import warnings
        warnings.warn(
            f"sign_reweighting(L={L}): exact delta_S_lorentzian not available. "
            f"Falling back to approximate ΔS (underflows at large L).",
            stacklevel=2,
        )
        d = 4
        V = L**d
        if G <= 0:
            raise ValueError(f"G must be positive for sign reweighting, got G={G}")
        for meas in mc_result.measurements:
            e_sq_per_site = 2.0 * G * meas.action / V if V > 0 else 0.0
            delta_S = -(1.0 / G) * V * (1.0 / d) * e_sq_per_site
            delta_S_values.append(delta_S)

    delta_S_arr = np.array(delta_S_values)
    # Average sign = <exp(Delta S)>_E (note: Delta S is typically negative)
    # Use log-sum-exp for numerical stability
    max_dS = np.max(delta_S_arr)
    log_avg_sign = max_dS + np.log(np.mean(np.exp(delta_S_arr - max_dS)))
    avg_sign = float(np.exp(log_avg_sign))

    # Standard error via jackknife (log-sum-exp stabilized)
    n = len(delta_S_values)
    if n > 1:
        jackknife_means = []
        for i in range(n):
            jk = np.delete(delta_S_arr, i)
            jk_max = np.max(jk)
            jk_mean = float(np.exp(jk_max + np.log(np.mean(np.exp(jk - jk_max)))))
            jackknife_means.append(jk_mean)
        jk_arr = np.array(jackknife_means)
        avg_sign_err = float(np.sqrt((n - 1) * np.var(jk_arr)))
    else:
        avg_sign_err = avg_sign

    return SignReweightingResult(
        coupling_ratio=coupling_ratio,
        L=L,
        avg_sign=avg_sign,
        avg_sign_err=avg_sign_err,
        delta_S_mean=float(np.mean(delta_S_arr)),
        delta_S_std=float(np.std(delta_S_arr)),
        lorentzian_viable=avg_sign > 0.01,
        n_configs=n,
    )


def lorentzian_pilot(
    coupling_ratios: list[float] = [0.5, 0.8, 1.0, 1.2, 1.5, 2.0],
    L: int = 4,
    mc_params: Optional[MCParams] = None,
) -> list[SignReweightingResult]:
    """Run the Lorentzian pilot study across multiple couplings.

    Args:
        coupling_ratios: G/G_c values to probe.
        L: Lattice size.
        mc_params: MC parameters.

    Returns:
        List of SignReweightingResult at each coupling.
    """
    results = []
    for r in coupling_ratios:
        results.append(sign_reweighting(r, L=L, mc_params=mc_params))
    return results
