"""Bounded numerical exploration of an illustrative regulated scalar ansatz.

The canonical potential is
    V_exact(C)=C²/(2G)-N_f[Lambda²C²-C⁴log(1+Lambda²/C²)]/(16pi²),
with its continuous origin value zero and positive supplied G,Lambda,N_f.
A microscopic ADW Hubbard-Stratonovich/one-loop derivation of this scalar
model is UNCOMPUTED; partial bosonization in the literature does not specify
this particular expression. TetradField.flat_spacetime adopts a Lorentzian
background, so the returned signature is kinematic input, not derived gravity.

Production V_num is flat at zero for |C|<1e-15, an absolute C guard. Exact
threshold/minimum/curvature/scaling statements concern V_exact;
the idealized real piecewise prescription is locally constant inside its guard.
No derivative of an unrestricted IEEE-valued program is asserted. The coefficient
changes sign at G_c=8pi²/(N_f Lambda²). At equality the exact origin is a
strict degenerate minimum. Above it an exact positive scalar root exists,
but the minimizer searches only (1e-6 Lambda,Lambda) and compares its
candidate with zero. Success/global_minimum/is_minimum fields do not certify
unrestricted stationarity/global optimality or the microscopic field theory.
The separate NJL fixed-point integral shares G_c, not nonzero stationary roots.

Existing phase labels and conditional algebra are retained as model metadata;
they do not establish full tetrad dynamics, physical gravity or vacuum magnitude.
"""

from dataclasses import dataclass
from enum import Enum
import numpy as np
from scipy.optimize import minimize_scalar

from src.core.formulas import (
    adw_effective_potential as _canonical_V_eff,
    adw_critical_coupling as _canonical_G_c,
    adw_curvature_at_origin as _canonical_curv,
)
from src.adw.hubbard_stratonovich import TetradField


class PhaseType(Enum):
    """Adopted phase labels, not a derivation of microscopic gravity."""
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

        G_c = 8 pi^2 / (N_f Lambda^2)

        Lean: critical_coupling_pos
        """
        return critical_coupling(self.Lambda, self.N_f)

    @property
    def coupling_ratio(self) -> float:
        """G/G_c, the exact scalar-ansatz bifurcation parameter."""
        return self.G / self.G_c


@dataclass
class TetradSolution:
    """Solution of the gap equation.

    Attributes:
        C: Tetrad magnitude |det(e)|^(1/4)
        tetrad: The full tetrad field
        V_eff: Effective potential at the solution
        is_minimum: Legacy scalar classification flag; not a global-optimality certificate
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
        global_minimum: Lower-energy candidate among zero and the bounded optimizer result
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
    """Guarded numerical scalar ansatz; delegates to canonical formulas.py.

    Physical derivation is UNCOMPUTED. The |C|<1e-15 zero branch differs
    from the continuous exact ansatz; no new Lean potential proof is claimed.
    """
    return _canonical_V_eff(C, G, Lambda, N_f)


def effective_potential_derivative(C: float, G: float, Lambda: float,
                                   N_f: int) -> float:
    """Signed derivative utility for the written scalar ansatz outside its guard.

    Returns zero on |C|<1e-15, matching the flat numerical interval.
    Outside it, the analytic expression differentiates V_exact; do not infer
    differentiability across the guard boundary or full floating-point accuracy.
    Evenness of the potential requires an odd signed derivative. The bounded
    minimizer uses V_num directly and does not call this utility.

    dV/dC = C/G - (N_f/16pi²)[2Lambda²C-4C³log(1+Lambda²/C²)
                              +2C³Lambda²/(Lambda²+C²)].
    """
    if abs(C) < 1e-15:
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
    """Critical coupling G_c = 8pi²/(N_f Λ²). Delegates to canonical formulas.py.

    Lean: critical_coupling_pos
    """
    return _canonical_G_c(Lambda, N_f)


def curvature_at_origin(G: float, Lambda: float, N_f: int) -> float:
    """Theoretical V_exact curvature coefficient; not the flat V_num derivative."""
    return _canonical_curv(G, Lambda, N_f)


def solve_gap_equation(params: GapEquationParams) -> GapEquationResult:
    """Minimize V_num in a fixed positive window and compare with zero.

    For positive supplied parameters, the nontrivial search is bounded to
    (1e-6 Lambda,Lambda). Exact ansatz roots can lie below/above that window
    or inside the absolute numerical guard. Optimizer success and the legacy
    global_minimum/is_minimum labels do not certify unrestricted stationarity
    or a global minimum. The selected flat tetrad/signature is an adopted
    ansatz; no microscopic ADW derivation or physical gravity is computed.

    Existing return fields and numerical search policy are retained.
    """
    G, Lambda, N_f = params.G, params.Lambda, params.N_f
    G_c = params.G_c
    ratio = params.coupling_ratio

    # Trivial solution: C = 0
    trivial = TetradSolution(
        C=0.0,
        tetrad=TetradField.zero(),
        V_eff=0.0,
        is_minimum=(ratio <= 1.0),  # exact-ansatz threshold classification
        phase=PhaseType.PRE_GEOMETRIC,
        is_lorentzian=False,
    )

    nontrivial = None
    global_min = trivial

    if ratio > 1.0:
        # Search for a candidate only within the fixed positive cutoff window.
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
                trivial.is_minimum = False  # Exact-ansatz instability; legacy scalar flag

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
    # Vestigial phase exists near the critical coupling.
    # The lower bound 0.8 is a mean-field estimate from the Ginzburg-Landau
    # expansion: vestigial order appears when beta_eff > 0 (quartic coefficient
    # positive), which requires G > G_c * (1 - epsilon) with epsilon ~ 0.2
    # from the one-loop correction. See ginzburg_landau.py for details.
    ratio = G / G_c
    return 0.8 < ratio <= 1.0


def effective_potential_landscape(G: float, Lambda: float, N_f: int,
                                  n_points: int = 200) -> dict:
    """Sample the guarded scalar potential over C in [0,Lambda].

    The absolute |C|<1e-15 guard can affect scaling at very small Lambda.
    Returns actual C/V_eff arrays and supplied parameter metadata; neither
    the grid nor metadata establishes physical ADW derivation or convergence.
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
