"""Gap Equation Solver for ADW Tetrad Condensation.

Solves the self-consistent gap equation for the tetrad VEV:
    delta S_eff / delta e^a_mu = 0

The effective potential after one-loop fermion integration:
    V_eff(C) = C^2/(2G) - (N_f/16pi^2)[Lambda^2 C^2 - C^4 ln(Lambda^2/C^2 + 1)]

where C = |det(e)|^(1/4) parameterizes the tetrad magnitude.

The gap equation dV_eff/dC = 0 has:
    - Trivial solution C = 0 (pre-geometric phase) — always exists
    - Nontrivial solution C != 0 (tetrad condensation) — exists iff G > G_c

Critical coupling:
    G_c = 8 pi^2 / (N_f Lambda^2)

Derived from d^2V_eff/dC^2|_{C=0} = 0 with the HS tree-level
potential V_tree = C^2/(2G).

Phase classification follows Vladimirov-Diakonov (2012) and Volovik (2024):
    - Pre-geometric: e = 0, g = 0
    - Vestigial metric: <E^a_mu> = 0 but <E^a_mu E^b_nu> != 0 (metric exists)
    - Full tetrad: <E^a_mu> = C * delta^a_mu != 0 (gravity + fermion coupling)

Lean: ADWMechanism.lean (critical_coupling_pos, gap_nontrivial_above_Gc,
       phase_classification, lorentzian_signature_automatic)
"""

from dataclasses import dataclass
from enum import Enum
import numpy as np
from scipy.optimize import minimize_scalar, brentq

from src.adw.hubbard_stratonovich import TetradField


class PhaseType(Enum):
    """Classification of gravitational phases."""
    PRE_GEOMETRIC = "pre_geometric"       # e = 0, g = 0
    VESTIGIAL_METRIC = "vestigial_metric"  # <e> = 0 but <ee> != 0
    FULL_TETRAD = "full_tetrad"            # <e> != 0, g != 0


@dataclass
class GapEquationParams:
    """Parameters for the gap equation.

    Attributes:
        G: ADW coupling constant
        Lambda: UV cutoff (lattice scale or Planck scale)
        N_f: Number of Dirac fermion species
    """
    G: float
    Lambda: float
    N_f: int

    @property
    def G_c(self) -> float:
        """Critical coupling for tetrad condensation.

        G_c = 4 pi^2 / (N_f Lambda^2)

        Lean: critical_coupling_pos
        """
        return critical_coupling(self.Lambda, self.N_f)

    @property
    def coupling_ratio(self) -> float:
        """G / G_c — condensation occurs for ratio > 1."""
        return self.G / self.G_c


@dataclass
class TetradSolution:
    """Solution of the gap equation.

    Attributes:
        C: Tetrad magnitude |det(e)|^(1/4)
        tetrad: The full tetrad field
        V_eff: Effective potential at the solution
        is_minimum: Whether this is a minimum (not saddle point)
        phase: Phase classification
        is_lorentzian: Whether induced metric has Lorentzian signature
    """
    C: float
    tetrad: TetradField
    V_eff: float
    is_minimum: bool
    phase: PhaseType
    is_lorentzian: bool


@dataclass
class GapEquationResult:
    """Complete result of the gap equation analysis.

    Attributes:
        params: Input parameters
        trivial_solution: The C=0 (pre-geometric) solution
        nontrivial_solution: The C!=0 solution (None if G < G_c)
        global_minimum: Which solution is the global minimum
        phase: Phase of the global minimum
        G_c: Critical coupling
        coupling_ratio: G / G_c
        success_criteria: Dict of success/failure checks
    """
    params: GapEquationParams
    trivial_solution: TetradSolution
    nontrivial_solution: TetradSolution | None
    global_minimum: TetradSolution
    phase: PhaseType
    G_c: float
    coupling_ratio: float
    success_criteria: dict


def effective_potential(C: float, G: float, Lambda: float, N_f: int) -> float:
    """Effective potential V_eff(C) for the tetrad magnitude.

    V_eff(C) = C^2/(2G) - (N_f/16pi^2)[Lambda^2 C^2 - C^4 ln(Lambda^2/C^2 + 1)]

    The first term is the tree-level HS potential.
    The second term is the one-loop Coleman-Weinberg contribution
    from integrating out N_f Dirac fermions in the tetrad background.

    Lean: effective_potential_structure

    Args:
        C: Tetrad magnitude (order parameter)
        G: ADW coupling constant
        Lambda: UV cutoff
        N_f: Number of Dirac fermion species

    Returns:
        V_eff(C) [dimensionless in natural units]
    """
    if C < 1e-15:
        return 0.0

    V_tree = C**2 / (2.0 * G)
    prefactor = N_f / (16.0 * np.pi**2)
    ratio_sq = Lambda**2 / C**2
    V_1loop = -prefactor * (Lambda**2 * C**2 - C**4 * np.log(ratio_sq + 1.0))

    return V_tree + V_1loop


def effective_potential_derivative(C: float, G: float, Lambda: float,
                                   N_f: int) -> float:
    """Derivative dV_eff/dC for finding extrema.

    dV_eff/dC = C/G - (N_f/16pi^2)[2 Lambda^2 C - 4C^3 ln(Lambda^2/C^2+1)
                                      + 2C^3 Lambda^2/(Lambda^2 + C^2)]

    The gap equation is dV_eff/dC = 0.

    Args:
        C: Tetrad magnitude
        G: ADW coupling constant
        Lambda: UV cutoff
        N_f: Number of Dirac fermion species

    Returns:
        dV_eff/dC
    """
    if C < 1e-15:
        return 0.0

    dV_tree = C / G
    prefactor = N_f / (16.0 * np.pi**2)
    ratio_sq = Lambda**2 / C**2
    dV_1loop = -prefactor * (
        2.0 * Lambda**2 * C
        - 4.0 * C**3 * np.log(ratio_sq + 1.0)
        + 2.0 * C**3 * Lambda**2 / (Lambda**2 + C**2)
    )

    return dV_tree + dV_1loop


def critical_coupling(Lambda: float, N_f: int) -> float:
    """Critical coupling for tetrad condensation.

    G_c = 8 pi^2 / (N_f Lambda^2)

    Derived from the condition that d^2V_eff/dC^2|_{C=0} = 0:
        1/G_c = N_f Lambda^2 / (8 pi^2)

    For G > G_c, the origin becomes unstable and the effective potential
    develops a nontrivial minimum at C != 0 (tetrad condensation).

    Lean: critical_coupling_pos

    Args:
        Lambda: UV cutoff
        N_f: Number of Dirac fermion species

    Returns:
        G_c (positive)
    """
    return 8.0 * np.pi**2 / (N_f * Lambda**2)


def curvature_at_origin(G: float, Lambda: float, N_f: int) -> float:
    """Second derivative of V_eff at C=0.

    d^2V/dC^2|_{C=0} = 1/G - N_f Lambda^2 / (8 pi^2)

    Sign change at G = G_c: positive for G < G_c, negative for G > G_c.

    Args:
        G: ADW coupling constant
        Lambda: UV cutoff
        N_f: Number of Dirac fermion species

    Returns:
        d^2V/dC^2|_{C=0}
    """
    return 1.0 / G - N_f * Lambda**2 / (8.0 * np.pi**2)


def solve_gap_equation(params: GapEquationParams) -> GapEquationResult:
    """Solve the gap equation and classify the phase.

    Strategy:
    1. Check if G > G_c (necessary for nontrivial solution)
    2. Find the nontrivial minimum by minimizing V_eff(C)
    3. Compare V_eff at C=0 and C=C_min to determine global minimum
    4. Classify phase and check success criteria

    Lean: gap_nontrivial_above_Gc

    Args:
        params: Gap equation parameters (G, Lambda, N_f)

    Returns:
        GapEquationResult with complete analysis.
    """
    G, Lambda, N_f = params.G, params.Lambda, params.N_f
    G_c = params.G_c
    ratio = params.coupling_ratio

    # Trivial solution: C = 0
    trivial = TetradSolution(
        C=0.0,
        tetrad=TetradField.zero(),
        V_eff=0.0,
        is_minimum=(ratio <= 1.0),  # minimum when G < G_c
        phase=PhaseType.PRE_GEOMETRIC,
        is_lorentzian=False,
    )

    nontrivial = None
    global_min = trivial

    if ratio > 1.0:
        # Nontrivial solution exists: find it by minimizing V_eff
        C_max = Lambda  # Search up to the cutoff scale
        result = minimize_scalar(
            lambda c: effective_potential(c, G, Lambda, N_f),
            bounds=(1e-6 * Lambda, C_max),
            method='bounded',
        )

        if result.success and result.x > 1e-10 * Lambda:
            C_min = result.x
            V_min = result.fun
            tetrad = TetradField.flat_spacetime(C_min)

            nontrivial = TetradSolution(
                C=C_min,
                tetrad=tetrad,
                V_eff=V_min,
                is_minimum=True,
                phase=PhaseType.FULL_TETRAD,
                is_lorentzian=tetrad.is_lorentzian,
            )

            # Compare with trivial solution
            if V_min < 0:  # V(0) = 0, so V_min < 0 means nontrivial wins
                global_min = nontrivial
                trivial.is_minimum = False  # Origin is now a local max

    # Classify phase
    phase = global_min.phase

    # Success criteria from roadmap
    success_criteria = {
        'nontrivial_exists': nontrivial is not None,
        'lorentzian_signature': nontrivial.is_lorentzian if nontrivial else False,
        'is_global_minimum': (nontrivial is not None and
                              global_min.phase == PhaseType.FULL_TETRAD),
        'coupling_above_critical': ratio > 1.0,
    }

    return GapEquationResult(
        params=params,
        trivial_solution=trivial,
        nontrivial_solution=nontrivial,
        global_minimum=global_min,
        phase=phase,
        G_c=G_c,
        coupling_ratio=ratio,
        success_criteria=success_criteria,
    )


def classify_phase(C: float, has_metric_fluctuations: bool = False) -> PhaseType:
    """Classify the gravitational phase based on order parameters.

    Vladimirov-Diakonov + Volovik phase hierarchy:
    - Pre-geometric: C = 0, no metric fluctuations
    - Vestigial metric: C = 0, but metric fluctuations nonzero
    - Full tetrad: C > 0

    Lean: phase_classification

    Args:
        C: Tetrad magnitude (order parameter)
        has_metric_fluctuations: Whether <E^a E^b> != 0 even if <E^a> = 0

    Returns:
        PhaseType classification.
    """
    if C > 1e-10:
        return PhaseType.FULL_TETRAD
    elif has_metric_fluctuations:
        return PhaseType.VESTIGIAL_METRIC
    else:
        return PhaseType.PRE_GEOMETRIC


def vestigial_metric_condition(G: float, G_c: float) -> bool:
    """Check if parameters allow a vestigial metric phase.

    The vestigial metric phase exists in a window near the critical
    coupling where the tetrad is disordered (<e> = 0) but metric
    fluctuations are nonzero (<ee> != 0).

    Following Volovik (2024), this is analogous to nematic order in
    liquid crystals: the director-squared tensor orders while the
    director itself does not.

    Lean: vestigial_metric_possible

    Args:
        G: ADW coupling constant
        G_c: Critical coupling

    Returns:
        True if vestigial metric phase is possible.
    """
    # Vestigial phase exists near the critical coupling
    # The window is approximately 0.8 G_c < G < G_c
    ratio = G / G_c
    return 0.8 < ratio <= 1.0


def effective_potential_landscape(G: float, Lambda: float, N_f: int,
                                  n_points: int = 200) -> dict:
    """Compute V_eff(C) over a range of C values for plotting.

    Args:
        G: ADW coupling constant
        Lambda: UV cutoff
        N_f: Number of Dirac fermion species
        n_points: Number of evaluation points

    Returns:
        Dictionary with 'C' and 'V_eff' arrays, plus metadata.
    """
    C_values = np.linspace(0, Lambda, n_points)
    V_values = np.array([effective_potential(c, G, Lambda, N_f) for c in C_values])

    G_c = critical_coupling(Lambda, N_f)

    return {
        'C': C_values,
        'V_eff': V_values,
        'G': G,
        'G_c': G_c,
        'Lambda': Lambda,
        'N_f': N_f,
        'coupling_ratio': G / G_c,
    }


def full_gap_analysis(G: float, Lambda: float, N_f: int) -> GapEquationResult:
    """Convenience wrapper: run the full gap equation analysis.

    Args:
        G: ADW coupling constant
        Lambda: UV cutoff
        N_f: Number of Dirac fermion species

    Returns:
        GapEquationResult with complete analysis.
    """
    params = GapEquationParams(G=G, Lambda=Lambda, N_f=N_f)
    return solve_gap_equation(params)
