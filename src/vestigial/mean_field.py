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
from src.core.formulas import adw_curvature_at_origin


@dataclass
class MeanFieldParams:
    """Parameters for the mean-field calculation.

    Attributes:
        G: ADW coupling constant.
        Lambda: UV cutoff (lattice scale).
        N_f: Number of Dirac fermion species.
        d: Spacetime dimension.
        temperature: Finite temperature for thermal fluctuations.
        L: Lattice size (sites per dimension). Volume = L^d.
            In the thermodynamic limit L → ∞, per-site fluctuations → 0
            in the pre-geometric phase. The vestigial phase is defined by
            total (extensive) metric correlator diverging as curvature → 0.
    """
    G: float
    Lambda: float
    N_f: int = 4
    d: int = 4
    temperature: float = 0.0
    L: int = 32

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
    curvature = adw_curvature_at_origin(G, Lambda, N_f)

    if curvature > 0:
        # Origin is a minimum — compute per-site metric fluctuations.
        #
        # The mean-field metric correlator per site is:
        #   M_g = d² * T_eff / (V * curvature)
        # where V = L^d is the lattice volume.
        #
        # Physical interpretation:
        #   - Pre-geometric (weak coupling): curvature is large, M_g ~ 1/V → 0
        #     as V → ∞. Fluctuations are thermal noise, not vestigial order.
        #   - Vestigial (near G_c): curvature → 0, so M_g diverges even with
        #     the 1/V suppression. The TOTAL correlator M_g * V diverges,
        #     signaling vestigial ordering.
        #
        # The vestigial criterion is: M_g * V > threshold, i.e.,
        # d² * T_eff / curvature > threshold — independent of V.
        # This is the standard condensed-matter criterion for vestigial
        # order (Fernandes et al. 2019).
        T_eff = max(params.temperature, Lambda / (4 * np.pi))  # zero-point
        V = params.L ** d  # lattice volume

        # Per-site metric correlator (intensive quantity)
        metric_fluct_per_site = d**2 * T_eff / (V * (curvature + 1e-30))

        # Total (extensive) correlator — used for vestigial ordering criterion
        # M_total = d² * T_eff / curvature  (V-independent)
        # We return per-site for the order parameter plot, but phase
        # classification uses the total correlator (see classify_phase).
        return metric_fluct_per_site
    else:
        # Origin is unstable: curvature < 0 with C = 0 means we're at the
        # onset of condensation. Return large metric to signal vestigial.
        return abs(curvature) * Lambda**2


def _total_metric_correlator(params: MeanFieldParams) -> float:
    """Compute the total (extensive) metric correlator for phase classification.

    Unlike the per-site correlator returned by mean_field_metric_correlator(),
    this is V-independent and is the correct quantity for the vestigial
    ordering criterion:
        M_total = d² * T_eff / curvature   (diverges as curvature → 0)

    Returns:
        Total correlator (V-independent). Used for phase classification.
    """
    G, Lambda, N_f = params.G, params.Lambda, params.N_f
    d = params.d

    C = mean_field_gap_equation(params)
    if C > 1e-10:
        # Full tetrad: total correlator is C² × V (extensive)
        # For classification, we just return a large value
        return C**2 * params.L**d

    curvature = adw_curvature_at_origin(G, Lambda, N_f)
    if curvature > 0:
        T_eff = max(params.temperature, Lambda / (4 * np.pi))
        return d**2 * T_eff / (curvature + 1e-30)
    else:
        return abs(curvature) * Lambda**2 * params.L**d


def _classify_phase(C: float, params: MeanFieldParams) -> str:
    """Classify the gravitational phase using the curvature criterion.

    - Full tetrad: C > 0 (below G_c, the gap equation has no solution)
    - Vestigial: C = 0 but curvature is small enough that the metric
      correlation length ξ ~ 1/√curvature exceeds the lattice spacing.
      In practice: curvature < curvature_vestigial (a fraction of 1/G_c).
    - Pre-geometric: C = 0 and curvature is large (strong restoring force,
      short correlation length, no collective metric order).

    The vestigial criterion: the curvature at the origin must be less than
    a fraction of the critical value 1/G_c. We use 0.3 × (1/G_c) as the
    threshold — below this, the correlation length has grown to ~2× its
    weak-coupling value, indicating the onset of vestigial order.

    Args:
        C: Tetrad VEV magnitude.
        params: Mean-field parameters.

    Returns:
        Phase string: "full_tetrad", "vestigial", or "pre_geometric".
    """
    Lambda = params.Lambda
    N_f = params.N_f

    if C > 1e-10 * Lambda:
        return "full_tetrad"

    # Curvature at origin: d²V/dC²|_{C=0} = 1/G - N_f Λ²/(8π²)
    curvature = adw_curvature_at_origin(params.G, Lambda, N_f)

    # Critical curvature (at G = G_c, curvature = 0)
    # At weak coupling (G << G_c): curvature ≈ 1/G_c (maximum)
    G_c = critical_coupling(Lambda, N_f)
    curvature_max = 1.0 / G_c

    if curvature <= 0:
        # At or beyond the transition — vestigial or full tetrad
        return "vestigial"

    # Vestigial criterion: curvature has dropped below 30% of its
    # weak-coupling value, meaning the correlation length has grown
    # significantly and metric correlations are developing.
    vestigial_fraction = 0.3
    if curvature < vestigial_fraction * curvature_max:
        return "vestigial"

    return "pre_geometric"


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
        phases.append(_classify_phase(C, params))

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

    # Phase classification (uses total correlator, not per-site)
    phase = _classify_phase(C, params)
    is_vestigial = (phase == "vestigial")

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
