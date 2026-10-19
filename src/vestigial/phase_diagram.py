"""Sampled adopted scalar/curvature model; physical gravity remains BUILD.

Mean-field labels retain the chosen curvature convention and scalar branch.
Sampled adjacent-label changes are brackets, not susceptibility-derived or
thermodynamic boundaries. Scalar receipts do not derive metric phases,
Lorentzian signature or EP transport. MC remains its separate unchanged
uncoupled-bosonic-HS route, with no new scalar or physical acceptance."""

from dataclasses import dataclass
import numpy as np
from typing import Optional

from src.vestigial.lattice_model import LatticeParams
from src.vestigial.mean_field import (
    MeanFieldParams, MeanFieldResult, full_mean_field_analysis,
    vestigial_phase_window,
)
from src.core.constants import ADW_4D_FSS, FERMION_BAG
from src.vestigial.monte_carlo import MCParams, MCResult, run_monte_carlo


@dataclass
class PhasePoint:
    """One sampled model label and normalized scalar/proxy values.

    Added fields carry the actual supplied-input receipt and rounding-aware
    intervals. None proxy errors on origin are uncomputed, not zero. Physical
    Lorentzian signature is uncomputed; positivity is only a model diagnostic.
    MC keeps its existing values and defaults these scalar-only fields to None.
    """
    coupling_ratio: float
    phase: str
    tetrad_vev: float
    metric_mag: float
    method: str
    scalar_enclosure: object = None
    scalar_inputs: tuple | None = None
    tetrad_interval: tuple | None = None
    tetrad_error: object = None
    metric_interval: tuple | None = None
    metric_error: object = None
    is_lorentzian: bool | None = None
    physical_signature_status: str = 'uncomputed'
    metric_positive_definite: bool | None = None
    mean_field_result: object = None
    origin_proxy_enclosure: object = None
    origin_metric_interval: tuple | None = None
    origin_metric_error: object = None


@dataclass
class PhaseDiagramResult:
    """Result of a phase diagram scan.

    Attributes:
        points: List of PhasePoint.
        coupling_ratios: Array of G/G_c values scanned.
        tetrad_values: Array of tetrad VEV values.
        metric_values: Array of metric correlator values.
        phases: List of phase labels.
        vestigial_exists: Whether sampled adopted vestigial labels occur.
        vestigial_window: First/last sampled label coordinates, not physical boundaries.
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
    sampled_transition_brackets: list | None = None
    boundary_status: str = "sampled model labels only; physical boundaries uncomputed"


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


def _phase_normalize(value, interval, Lambda, power):
    """Normalize a represented scalar/proxy and its target interval, with rounding.

    None denotes an uncertified curvature proxy, never zero uncertainty.
    """
    from fractions import Fraction
    from math import isfinite
    from src.core.formulas import ADWScalarUnresolved, _adw_exact
    supplied=_adw_exact(value,'normalization value')
    cutoff=_adw_exact(Lambda,'normalization cutoff',positive=True)
    if supplied < 0 or type(power) is not int or power not in (1,2,4):
        raise ValueError('nonnegative value and admitted integer normalization power required')
    scale=cutoff**power
    target=supplied/scale
    try:
        represented=float(target)
    except OverflowError as exc:
        raise ADWScalarUnresolved('normalized scalar overflows binary64') from exc
    if not isfinite(represented) or (target and represented==0):
        raise ADWScalarUnresolved('normalized nonzero scalar is not representable')
    if interval is None:
        return represented, None, None
    if type(interval) is not tuple or len(interval)!=2 or any(type(x) is not Fraction for x in interval) or interval[0]>interval[1]:
        raise ValueError('ordered exact rational interval required')
    bounds=tuple(x/scale for x in interval)
    error=max(abs(Fraction.from_float(represented)-x) for x in bounds)
    return represented, bounds, error


def _phase_transport_equal(value, expected):
    """Compare admitted actual transport without laundering equal-valued types.

    Rational bounds/errors, tuple shapes, bools and None have strict protocols.
    Represented scalar/input numbers retain canonical finite nonboolean Real
    admission, including NumPy floating values; no arbitrary coercion repairs a
    malformed field. This is object binding, not a new model/parser/gate.
    """
    from fractions import Fraction
    from src.core.formulas import _adw_exact
    if expected is None:
        return value is None
    if type(expected) is Fraction:
        return type(value) is Fraction and value==expected
    if type(expected) is bool:
        return type(value) is bool and value is expected
    if type(expected) is tuple:
        return type(value) is tuple and len(value)==len(expected) and all(
            _phase_transport_equal(a,b) for a,b in zip(value,expected))
    if type(expected) is str:
        return type(value) is str and value==expected
    return _adw_exact(value,'transport scalar')==_adw_exact(expected,'expected scalar')


def _phase_point_from_mean_field(result, requested_ratio, G, Lambda, N_f, **accuracy):
    """Bind one actual result to supplied inputs; retain numerical/physical limits."""
    from fractions import Fraction
    from src.core.formulas import adw_validate_scalar_enclosure, _adw_exact
    from src.vestigial.mean_field import (MeanFieldParams,_mean_policy,_mean_lattice,
        _validate_origin_proxy_enclosure)
    cert=result.scalar_enclosure
    scalar_policy,_=_mean_policy(accuracy)
    expected_params=MeanFieldParams(G=G,Lambda=Lambda,N_f=N_f)
    admitted_origin=None
    if result.origin_proxy_enclosure is not None:
        admitted_origin=_validate_origin_proxy_enclosure(result.origin_proxy_enclosure,expected_params,cert,**accuracy)
    adw_validate_scalar_enclosure(cert,G,Lambda,N_f,**scalar_policy)
    # The scan's actual full-analysis entry point has these unchanged defaults.
    if not _phase_transport_equal(_mean_lattice(result.params),_mean_lattice(expected_params)):
        raise ValueError('mean-field scan lattice/temperature metadata mismatch')
    if (not _phase_transport_equal((result.params.G,result.params.Lambda,result.params.N_f),(G,Lambda,N_f)) or
            not _phase_transport_equal(result.C_tetrad,cert.C) or
            not _phase_transport_equal(result.V_eff,cert.V_eff)):
        raise ValueError('mean-field result input/scalar mismatch')
    if result.is_lorentzian is not None or not _phase_transport_equal(result.physical_signature_status,'uncomputed') or type(result.metric_positive_definite) is not bool:
        raise ValueError('physical signature must remain uncomputed; positivity is separate')
    metric_value=_adw_exact(result.G_metric,'adopted metric proxy',positive=True)
    for eigenvalue in result.metric_eigenvalues:
        _adw_exact(eigenvalue,'metric eigenvalue')
    if (len(result.metric_eigenvalues)!=result.params.d or not np.all(np.isfinite(result.metric_eigenvalues)) or
            result.metric_positive_definite!=bool(np.all(result.metric_eigenvalues>0))):
        raise ValueError('metric positivity diagnostic/eigenvalues mismatch')
    origin=None;origin_interval=origin_error=None
    if cert.branch=='positive':
        if any(getattr(result,k) is not None for k in ('origin_proxy_enclosure','origin_proxy_interval','origin_proxy_error')):
            raise ValueError('positive branch cannot carry adopted-origin evidence')
        if any(not _phase_transport_equal(v,result.G_metric) for v in result.metric_eigenvalues):
            raise ValueError('positive metric eigenvalue/source mismatch')
        if not _phase_transport_equal(result.G_metric,float(Fraction.from_float(cert.C)**2)):
            raise ValueError('represented C-squared proxy mismatch')
        if not _phase_transport_equal(result.phase,'full_tetrad') or result.is_vestigial is not False:
            raise ValueError('positive scalar branch/model label mismatch')
        expected=tuple(x*x for x in cert.magnitude_interval)
        if not _phase_transport_equal(result.scalar_metric_interval,expected):
            raise ValueError('positive metric proxy interval mismatch')
        expected_error=max(abs(metric_value-x) for x in expected)
        if type(result.scalar_metric_error) is not Fraction or result.scalar_metric_error!=expected_error:
            raise ValueError('positive metric proxy error mismatch')
    else:
        origin=admitted_origin if admitted_origin is not None else _validate_origin_proxy_enclosure(result.origin_proxy_enclosure,result.params,cert,**accuracy)
        if (not _phase_transport_equal(result.G_metric,origin.values[0]) or
                any(not _phase_transport_equal(v,origin.values[2]) for v in result.metric_eigenvalues) or
                not _phase_transport_equal(result.phase,origin.phase) or
                not _phase_transport_equal(result.origin_proxy_interval,origin.intervals[0]) or
                not _phase_transport_equal(result.origin_proxy_error,origin.errors[0])):
            raise ValueError('adopted-origin result/witness mismatch')
        _,origin_interval,origin_error=_phase_normalize(result.G_metric,origin.intervals[0],Lambda,2)
        if type(result.phase) is not str or result.phase not in ('pre_geometric','vestigial') or result.is_vestigial is not (result.phase=='vestigial'):
            raise ValueError('origin curvature model label mismatch')
        if result.scalar_metric_interval is not None or result.scalar_metric_error is not None:
            raise ValueError('origin curvature proxy has no certified metric interval')
    C,ci,ce=_phase_normalize(cert.C,cert.magnitude_interval,Lambda,1)
    metric,mi,me=_phase_normalize(result.G_metric,result.scalar_metric_interval,Lambda,2)
    return PhasePoint(float(requested_ratio),result.phase,C,metric,'mean_field',
        cert,(G,Lambda,N_f),ci,ce,mi,me,None,'uncomputed',result.metric_positive_definite,
        result,origin,origin_interval,origin_error)


def scan_coupling(
    method: str = "mean_field",
    Lambda: float = 1.0,
    N_f: int = 4,
    coupling_range: tuple[float, float] = ADW_4D_FSS['coupling_range'],
    n_points: int = ADW_4D_FSS['n_couplings'],
    L: int = 4,
    mc_params: Optional[MCParams] = None,
    **accuracy,
) -> PhaseDiagramResult:
    """Scan the original grid with actual receipts; numerical refusals propagate.

    Mean-field labels use the adopted curvature model, not a physical phase
    theorem. Accuracy/resource requests pass unchanged to canonical replay.

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
        from numbers import Integral
        if isinstance(n_points,(bool,np.bool_)) or not isinstance(n_points,Integral) or n_points<1:
            raise ValueError('positive integer n_points required')
        if not np.isfinite(G_c) or G_c<=0 or not np.all(np.isfinite(ratios)) or np.any(ratios<=0):
            raise ValueError('finite positive actual couplings required')
        for index,r in enumerate(ratios):
            G=r*G_c
            try:
                result=full_mean_field_analysis(G=G,Lambda=Lambda,N_f=N_f,**accuracy)
                point=_phase_point_from_mean_field(result,r,G,Lambda,N_f,**accuracy)
            except Exception as exc:
                exc.add_note(f'outer mean-field sample {index}, requested ratio {r}')
                raise
            points.append(point)
            tetrad_values.append(point.tetrad_vev)
            metric_values.append(point.metric_mag)
            phases.append(point.phase)

    elif method == "monte_carlo":
        import warnings
        warnings.warn(
            "phase_diagram method='monte_carlo' uses the uncoupled bosonic HS model "
            "(no inter-site coupling, no fermion determinant). It CANNOT produce "
            "phase transitions. Use the fermion-bag MC via run_vestigial_production.py "
            "for physics-correct results.",
            stacklevel=2,
        )
        if mc_params is None:
            mc_params = MCParams(
                n_thermalize=FERMION_BAG['n_thermalize'],
                n_measure=FERMION_BAG['n_measure'],
                n_skip=FERMION_BAG['n_skip'],
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
        sampled_transition_brackets=[(float(ratios[i-1]),float(ratios[i]),phases[i-1],phases[i])
            for i in range(1,len(phases)) if phases[i]!=phases[i-1]],
    )
