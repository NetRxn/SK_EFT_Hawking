"""Unrestricted numerical enclosure of an illustrative regulated scalar ansatz.

The exact adopted V is continuous at zero and even in signed C. Canonical
formulas.py encloses its supplied-input/true-pi threshold and positive root
with finite exact-rational work, final rounding and energy error checks.
There is no fixed magnitude search floor, UV-amplitude cap or flat origin
interval. Refusal is explicit, never a zero-filled unresolved result.

This scalar numerical witness is not a microscopic HS/fermion determinant,
physical tetrad or gravity derivation. TetradField.flat_spacetime adopts its
Lorentzian background; its existing finite-threshold signature property is
legacy model metadata, not a condition for existence of the scalar minimum.
The separate NJL fixed point shares a threshold, not the nonzero root.
"""

from dataclasses import dataclass
from enum import Enum
from numbers import Real
from math import isfinite
import numpy as np
from scipy.optimize import minimize_scalar

from src.core.formulas import (
    adw_effective_potential as _canonical_V_eff,
    adw_critical_coupling as _canonical_G_c,
    adw_curvature_at_origin as _canonical_curv,
    adw_effective_potential_derivative as _canonical_derivative,
    adw_scalar_minimum as _canonical_scalar_minimum,
    adw_validate_scalar_enclosure as _canonical_validate_enclosure,
    _adw_exact as _canonical_exact,
    ADWScalarEnclosure, ADWScalarUnresolved,
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
        """Legacy represented G/G_c diagnostic; not the true-pi branch oracle."""
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
        nontrivial_solution: Certified positive scalar minimum, or None for certified origin
        global_minimum: Canonical certified magnitude-domain scalar minimum
        phase: Adopted label of the certified scalar branch, not derived gravity
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
    scalar_status: str | None = None
    search_diagnostics: dict | None = None
    scalar_enclosure: ADWScalarEnclosure | None = None


def effective_potential(C: float, G: float, Lambda: float, N_f: int) -> float:
    """Continuous numerical scalar ansatz; delegates to canonical formulas.py.

    Physical derivation and native verification are UNCOMPUTED. Numerical
    representation/work failure propagates; no absolute flat guard remains.
    """
    return _canonical_V_eff(C, G, Lambda, N_f)


def effective_potential_derivative(C: float, G: float, Lambda: float,
                                   N_f: int) -> float:
    """Continuous signed scalar derivative; canonical sign-or-error evaluation.

    No absolute flat interval remains. An odd derivative is not a raw-small-
    slope root certificate; use the normalized rational residual/enclosure.
    Microscopic ADW/physical gravity identification remains UNCOMPUTED.
    """
    return _canonical_derivative(C, G, Lambda, N_f)


def critical_coupling(Lambda: float, N_f: int) -> float:
    """Critical coupling G_c = 8pi²/(N_f Λ²). Delegates to canonical formulas.py.

    Lean: critical_coupling_pos
    """
    return _canonical_G_c(Lambda, N_f)


def curvature_at_origin(G: float, Lambda: float, N_f: int) -> float:
    """Legacy floating diagnostic of the continuous-origin curvature coefficient."""
    return _canonical_curv(G, Lambda, N_f)


def _positive_scalar(value, name):
    """Validate supplied arithmetic domain without silent zero/overflow coercion."""
    if isinstance(value, (bool, np.bool_)) or not isinstance(value, Real):
        raise ValueError(f"{name} must be a finite positive real scalar")
    if value <= 0:
        raise ValueError(f"{name} must be positive")
    try:
        represented = float(value)
    except (TypeError, ValueError, OverflowError) as exc:
        raise ValueError(f"{name} is not representable") from exc
    if not isfinite(represented) or represented <= 0:
        raise ValueError(f"{name} is not representable as a positive finite scalar")

def _reported_scalar(value, name):
    """Read a numeric optimizer diagnostic; null plus a tag retains invalidity."""
    if isinstance(value, (bool, np.bool_)) or not isinstance(value, Real):
        raise ValueError(f"optimizer {name} must be a real scalar, not a boolean")
    try:
        represented = float(value)
    except (TypeError, ValueError, OverflowError) as exc:
        raise ValueError(f"optimizer {name} is not representable") from exc
    if not isfinite(represented):
        if value != value or value == represented:  # genuine NaN/Inf, not finite overflow
            return None, "nonfinite"
        raise ValueError(f"optimizer {name} has an unrepresentable finite value")
    if represented != value:
        raise ValueError(f"optimizer {name} would lose its reported value on conversion")
    return represented, "finite"


def solve_gap_equation(params: GapEquationParams, *, atol=0, rtol=1e-10,
                       energy_atol=0, energy_rtol=1e-8,
                       max_work=200000, max_bits=100000) -> GapEquationResult:
    """Consume the canonical unrestricted scalar numerical witness or refuse.

    Exact supplied G/Lambda/N_f and true pi determine the branch. Legacy
    G_c/coupling_ratio are finite compatibility diagnostics, not a decision
    oracle. Scalar globality does not derive the adopted tetrad/gravity.
    No unresolved result is filled with a pre-geometric zero placeholder.
    """
    G, Lambda, N_f = params.G, params.Lambda, params.N_f
    for name, value in (("G", G), ("Lambda", Lambda), ("N_f", N_f)):
        _positive_scalar(value, name)
    try:
        G_c, ratio = params.G_c, params.coupling_ratio
    except (OverflowError, ZeroDivisionError, TypeError) as exc:
        raise ValueError("legacy G_c/ratio diagnostics are not representable") from exc
    _positive_scalar(G_c, "G_c")
    _positive_scalar(ratio, "coupling_ratio")
    certificate = _canonical_scalar_minimum(G, Lambda, N_f, atol=atol, rtol=rtol,
        energy_atol=energy_atol, energy_rtol=energy_rtol,
        max_work=max_work, max_bits=max_bits)
    certificate = _canonical_validate_enclosure(certificate, G, Lambda, N_f,
        atol=atol, rtol=rtol, energy_atol=energy_atol, energy_rtol=energy_rtol,
        max_work=max_work, max_bits=max_bits)
    if type(certificate) is not ADWScalarEnclosure:
        raise ValueError("canonical scalar certificate required")
    expected_inputs = tuple(_canonical_exact(x, name, positive=True) for x, name in
        ((G, "G"), (Lambda, "Lambda"), (N_f, "N_f")))
    if certificate.model != "supplied-parameters-exact-pi" or certificate.inputs != expected_inputs:
        raise ValueError("certificate changed the supplied scalar problem")
    requested = tuple(_canonical_exact(x, name) for x, name in
        ((atol, "atol"), (rtol, "rtol"), (energy_atol, "energy_atol"), (energy_rtol, "energy_rtol")))
    observed = (certificate.requested_atol, certificate.requested_rtol,
                certificate.requested_energy_atol, certificate.requested_energy_rtol)
    if observed != requested or certificate.max_work != max_work or certificate.max_bits != max_bits:
        raise ValueError("certificate changed requested accuracy/resource budgets")
    C, energy = certificate.C, certificate.V_eff
    if any(type(v) is not float or not isfinite(v) for v in (C, energy)):
        raise ValueError("certificate has nonfinite/nonbinary scalar outputs")
    origin = certificate.branch == "origin"
    if origin:
        if (C != 0 or energy != 0 or certificate.r_interval[1] > 1 or
                certificate.magnitude_interval != (0, 0) or certificate.energy_interval != (0, 0)):
            raise ValueError("not a certified origin result")
    elif (certificate.branch != "positive" or C <= 0 or energy >= 0 or
          certificate.r_interval[0] <= 1 or certificate.energy_interval[1] >= 0):
        raise ValueError("not a certified positive scalar result")
    trivial = TetradSolution(0.0, TetradField.zero(), 0.0, origin,
                            PhaseType.PRE_GEOMETRIC, False)
    nontrivial = None
    selected = trivial
    if not origin:
        tetrad = TetradField.flat_spacetime(C)
        nontrivial = TetradSolution(C, tetrad, energy, True,
                                   PhaseType.FULL_TETRAD, tetrad.is_lorentzian)
        selected = nontrivial
    diagnostics = dict(
        search_attempted=not origin, bounds=None, candidate_cutoff=None,
        optimizer_success=None, optimizer_status=None, optimizer_message=None,
        C=C, V_eff=energy, C_validity="finite", V_eff_validity="finite",
        candidate_window="not_applicable" if origin else "unrestricted",
        selected=not origin, stationarity="enclosed_exact_ansatz",
        globality="unrestricted_scalar_ansatz", certificate=certificate.as_dict(),
    )
    return GapEquationResult(params, trivial, nontrivial, selected, selected.phase,
        G_c, ratio, dict(nontrivial_exists=not origin,
                        lorentzian_signature=bool(nontrivial and nontrivial.is_lorentzian),
                        is_global_minimum=True,
                        coupling_above_critical=certificate.r_interval[0] > 1),
        "certified_origin" if origin else "certified_scalar_minimum", diagnostics,
        certificate)


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
    """Sample the continuous scalar potential over C in [0,Lambda].

    This display grid is not the unrestricted optimizer domain.
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


def full_gap_analysis(G: float, Lambda: float, N_f: int, **accuracy) -> GapEquationResult:
    """Delegate the supplied scalar problem and explicit certificate budgets.

    Legacy positional G,Lambda,N_f calls remain. Valid numerical refusal is
    explicit; no physical-gravity or native acceptance is implied.
    """
    params = GapEquationParams(G=G, Lambda=Lambda, N_f=N_f)
    return solve_gap_equation(params, **accuracy)
