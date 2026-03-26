"""Mean-field analysis for vestigial gravity.

Extends the Phase 3 gap equation analysis to include the metric
correlator <e^a_mu e^b_nu>. The vestigial phase exists where
the tetrad VEV is zero but the metric correlator is nonzero.

The mean-field self-consistency equations:
    C_tetrad = <e^a_mu>     (tetrad VEV)
    G_metric = <e^a_mu e^b_nu>  (metric correlator)

Phase classification:
    C_tetrad = 0, G_metric = 0    -> pre-geometric
    C_tetrad = 0, G_metric != 0   -> vestigial metric
    C_tetrad != 0, G_metric != 0  -> full tetrad

Reference: Volovik, JETP Lett. 119, 330 (2024) — vestigial phase
Reference: Vladimirov-Diakonov, PRD 86, 104019 (2012) — cavity method
"""

from dataclasses import dataclass
import numpy as np
from scipy.optimize import minimize_scalar, brentq
from src.adw.gap_equation import effective_potential, critical_coupling


@dataclass
class MeanFieldParams:
    """Parameters for the mean-field calculation.

    Attributes:
        G: ADW coupling constant.
        Lambda: UV cutoff (lattice scale).
        N_f: Number of Dirac fermion species.
        d: Spacetime dimension.
        temperature: Finite temperature for thermal fluctuations.
    """
    G: float
    Lambda: float
    N_f: int = 4
    d: int = 4
    temperature: float = 0.0

    @property
    def G_c(self) -> float:
        return critical_coupling(self.Lambda, self.N_f)

    @property
    def coupling_ratio(self) -> float:
        return self.G / self.G_c


@dataclass
class MeanFieldResult:
    """Result of the mean-field analysis.

    Attributes:
        params: Input parameters.
        C_tetrad: Tetrad VEV magnitude.
        G_metric: Metric correlator magnitude.
        V_eff: Effective potential at the solution.
        phase: Phase classification string.
        is_vestigial: Whether we are in the vestigial phase.
        metric_eigenvalues: Eigenvalues of the mean-field metric.
        is_lorentzian: Whether the metric has Lorentzian signature.
    """
    params: MeanFieldParams
    C_tetrad: float
    G_metric: float
    V_eff: float
    phase: str
    is_vestigial: bool
    metric_eigenvalues: np.ndarray
    is_lorentzian: bool


def mean_field_gap_equation(params: MeanFieldParams) -> float:
    """Solve for the tetrad VEV in mean-field.

    This wraps the Phase 3 gap equation to get C_tetrad.

    Args:
        params: Mean-field parameters.

    Returns:
        C_tetrad (tetrad VEV magnitude, 0 if below G_c).
    """
    G, Lambda, N_f = params.G, params.Lambda, params.N_f
    G_c = params.G_c

    if params.coupling_ratio <= 1.0:
        return 0.0

    # Find minimum of V_eff(C)
    result = minimize_scalar(
        lambda c: effective_potential(c, G, Lambda, N_f),
        bounds=(1e-6 * Lambda, Lambda),
        method='bounded',
    )

    if result.success and result.x > 1e-10 * Lambda:
        V_min = effective_potential(result.x, G, Lambda, N_f)
        if V_min < 0:
            return result.x

    return 0.0


def mean_field_metric_correlator(params: MeanFieldParams) -> float:
    """Compute the metric correlator in mean-field.

    The metric correlator <e^a_mu e^b_nu> receives contributions from:
    1. Tetrad VEV: <e>^2 (present in Phase III)
    2. Fluctuations: <(e - <e>)^2> (present in Phases II and III)

    In the vestigial phase, <e> = 0 but fluctuations give a nonzero
    metric. The fluctuation contribution is computed from the second
    derivative of the effective potential at C = 0:

        <e^2> ~ N_f * T / |d^2V/dC^2|_{C=0}|

    For the Euclidean pilot, "temperature" is the lattice coupling.

    Args:
        params: Mean-field parameters.

    Returns:
        G_metric (metric correlator magnitude).
    """
    G, Lambda, N_f = params.G, params.Lambda, params.N_f
    d = params.d

    # Tetrad VEV contribution
    C = mean_field_gap_equation(params)

    if C > 1e-10:
        # Full tetrad phase: metric comes from VEV + fluctuations
        # g ~ C^2 + fluctuation correction
        metric_vev = C ** 2
        # Fluctuation correction is subleading
        return metric_vev

    # No tetrad VEV: check for vestigial phase
    # Curvature at origin: d^2V/dC^2|_{C=0} = 1/G - N_f Lambda^2 / (8 pi^2)
    curvature = 1.0 / G - N_f * Lambda**2 / (8.0 * np.pi**2)

    if curvature > 0:
        # Origin is a minimum: pre-geometric phase
        # Metric fluctuations are finite but small
        # <e^2> ~ d^2 * T / (curvature * V)  where V is volume
        # For T=0 mean-field: quantum fluctuations give
        T_eff = max(params.temperature, Lambda / (4 * np.pi))  # zero-point
        metric_fluct = d**2 * T_eff / (curvature + 1e-30)

        # Vestigial phase exists when fluctuations are large enough
        # to produce a nonzero metric but not large enough for <e> != 0
        # This happens when curvature is small (near G_c)
        return metric_fluct
    else:
        # Origin is unstable: this shouldn't happen if C = 0
        # Unless we're right at the transition
        return abs(curvature) * Lambda**2


def vestigial_phase_window(Lambda: float, N_f: int,
                           n_points: int = 50) -> dict:
    """Compute the coupling window where the vestigial phase exists.

    Scans G/G_c and identifies where:
    - C_tetrad = 0 (no tetrad VEV)
    - G_metric > threshold (metric correlator nonzero)

    The vestigial window is between G_vestigial_min and G_c.

    Args:
        Lambda: UV cutoff.
        N_f: Number of fermion species.
        n_points: Number of coupling values to scan.

    Returns:
        Dict with coupling_ratios, C_tetrad, G_metric, phase labels,
        and vestigial window boundaries.
    """
    G_c = critical_coupling(Lambda, N_f)
    ratios = np.linspace(0.5, 2.0, n_points)

    C_values = []
    G_metric_values = []
    phases = []

    for r in ratios:
        params = MeanFieldParams(G=r * G_c, Lambda=Lambda, N_f=N_f)
        C = mean_field_gap_equation(params)
        G_m = mean_field_metric_correlator(params)

        C_values.append(C)
        G_metric_values.append(G_m)

        if C > 1e-10 * Lambda:
            phases.append("full_tetrad")
        elif G_m > 0.01 * Lambda**2:  # threshold for "nonzero"
            phases.append("vestigial")
        else:
            phases.append("pre_geometric")

    # Find vestigial window
    vestigial_indices = [i for i, p in enumerate(phases) if p == "vestigial"]
    if vestigial_indices:
        vestigial_min = ratios[vestigial_indices[0]]
        vestigial_max = ratios[vestigial_indices[-1]]
    else:
        vestigial_min = vestigial_max = 0.0

    return {
        'coupling_ratios': ratios,
        'C_tetrad': np.array(C_values),
        'G_metric': np.array(G_metric_values),
        'phases': phases,
        'vestigial_min': vestigial_min,
        'vestigial_max': vestigial_max,
        'vestigial_exists': len(vestigial_indices) > 0,
    }


def full_mean_field_analysis(G: float, Lambda: float,
                             N_f: int = 4) -> MeanFieldResult:
    """Run the complete mean-field analysis.

    Args:
        G: ADW coupling constant.
        Lambda: UV cutoff.
        N_f: Number of fermion species.

    Returns:
        MeanFieldResult with full analysis.
    """
    params = MeanFieldParams(G=G, Lambda=Lambda, N_f=N_f)

    C = mean_field_gap_equation(params)
    G_m = mean_field_metric_correlator(params)
    V = effective_potential(C, G, Lambda, N_f) if C > 0 else 0.0

    # Phase classification
    if C > 1e-10 * Lambda:
        phase = "full_tetrad"
        is_vestigial = False
    elif G_m > 0.01 * Lambda**2:
        phase = "vestigial"
        is_vestigial = True
    else:
        phase = "pre_geometric"
        is_vestigial = False

    # Metric eigenvalues (isotropic mean-field: all equal)
    d = params.d
    if C > 0:
        metric_eigs = np.array([C**2] * d)
    elif G_m > 0:
        metric_eigs = np.array([G_m / d] * d)
    else:
        metric_eigs = np.zeros(d)

    is_lorentzian = bool(np.all(metric_eigs > 0))

    return MeanFieldResult(
        params=params,
        C_tetrad=C,
        G_metric=G_m,
        V_eff=V,
        phase=phase,
        is_vestigial=is_vestigial,
        metric_eigenvalues=metric_eigs,
        is_lorentzian=is_lorentzian,
    )
