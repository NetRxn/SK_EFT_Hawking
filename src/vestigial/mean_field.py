"""Adopted mean-field proxies with a canonical scalar branch. The adopted Gaussian proxy now carries distinct true-pi numerical bounds. Its physical identification and vestigial gravity remain BUILD; no numerical minimum proves them.

Reference: Volovik, JETP Lett. 119, 330 (2024) — retained literature context.
Reference: Vladimirov-Diakonov, PRD 86, 104019 (2012) — retained literature context."""

from dataclasses import dataclass
import numpy as np
from scipy.optimize import minimize_scalar, brentq
from src.adw.gap_equation import effective_potential, critical_coupling
from src.core.formulas import (adw_curvature_at_origin,
    ADWOriginProxyEnclosure as OriginProxyEnclosure, adw_origin_proxy,
    adw_validate_origin_proxy_enclosure)


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
        C_tetrad: Certified scalar coordinate approximation, not a physical VEV derivation.
        G_metric: Adopted metric proxy; origin curvature model is not physically certified.
        V_eff: Effective potential at the solution.
        phase: Phase classification string.
        is_vestigial: Whether we are in the vestigial phase.
        metric_eigenvalues: Eigenvalues of the mean-field metric.
        is_lorentzian: None because physical signature is uncomputed; positivity is a separate diagnostic.
    """
    params: MeanFieldParams
    C_tetrad: float
    G_metric: float
    V_eff: float
    phase: str
    is_vestigial: bool
    metric_eigenvalues: np.ndarray
    is_lorentzian: bool | None  # None: physical signature is uncomputed
    scalar_enclosure: object = None
    scalar_metric_interval: tuple | None = None
    scalar_metric_error: object = None
    physical_signature_status: str = "uncomputed"
    metric_positive_definite: bool | None = None
    origin_proxy_enclosure: object = None
    origin_proxy_interval: tuple | None = None
    origin_proxy_error: object = None



def _mean_policy(accuracy):
    """Separate scalar requests from explicit adopted-origin numerical requests."""
    from src.core.formulas import _adw_exact
    supplied=dict(accuracy)
    requests=tuple(_adw_exact(supplied.pop(k,default),k) for k,default in
        (("origin_atol",0),("origin_rtol",1e-10)))
    if any(x<0 for x in requests) or sum(requests)<=0:
        raise ValueError('nonnegative origin tolerances with one positive required')
    policy=dict(atol=0,rtol=1e-10,energy_atol=0,energy_rtol=1e-8,max_work=200000,max_bits=100000)
    unknown=set(supplied)-set(policy)
    if unknown:
        raise TypeError('unknown mean-field accuracy keywords: '+','.join(sorted(unknown)))
    policy.update(supplied)
    return policy,requests


def _validate_origin_proxy_enclosure(c,params,certificate,**accuracy):
    """Thin actual-parameter facade; canonical preflight precedes scalar replay."""
    policy,requests=_mean_policy(accuracy)
    return adw_validate_origin_proxy_enclosure(c,params.G,params.Lambda,params.N_f,
        d=params.d,L=params.L,temperature=params.temperature,scalar_enclosure=certificate,
        origin_atol=requests[0],origin_rtol=requests[1],**policy)


def _origin_receipt(params,certificate,origin_enclosure=None,**accuracy):
    policy,requests=_mean_policy(accuracy)
    if origin_enclosure is not None:
        return _validate_origin_proxy_enclosure(origin_enclosure,params,certificate,**accuracy)
    return adw_origin_proxy(params.G,params.Lambda,params.N_f,d=params.d,L=params.L,
        temperature=params.temperature,scalar_enclosure=certificate,
        origin_atol=requests[0],origin_rtol=requests[1],**policy)


def _scalar_receipt(params, certificate=None, **accuracy):
    """Actual scalar policy; distinct origin requests never leak to its facade."""
    from src.core.formulas import adw_scalar_minimum, adw_validate_scalar_enclosure
    policy,_=_mean_policy(accuracy)
    if certificate is None:
        certificate=adw_scalar_minimum(params.G,params.Lambda,params.N_f,**policy)
    return adw_validate_scalar_enclosure(certificate,params.G,params.Lambda,params.N_f,**policy)


def _mean_binary(value, name, *, nonzero=False):
    from src.core.formulas import _adw_binary_midpoint
    return _adw_binary_midpoint((value,value),name,nonzero=nonzero)[0]


def _mean_lattice(params):
    from numbers import Integral
    from src.core.formulas import _adw_exact
    for name in ('d','L'):
        value=getattr(params,name)
        if isinstance(value,(bool,np.bool_)) or not isinstance(value,Integral) or value<=0:
            raise ValueError(name+' must be a positive integer')
    temperature=_adw_exact(params.temperature,'temperature')
    if temperature<0:
        raise ValueError('temperature must be nonnegative')
    return int(params.d),int(params.L),temperature


def _origin_fluctuation(params, *, extensive, scalar_enclosure=None, origin_enclosure=None, **accuracy):
    """True-pi adopted Gaussian proxy with its distinct numerical witness."""
    result=_origin_receipt(params,scalar_enclosure,origin_enclosure,**accuracy)
    return result.values[1 if extensive else 0]


def _scalar_metric(certificate, volume=1):
    from fractions import Fraction
    q=Fraction.from_float(certificate.C)
    return _mean_binary(q*q*volume,'scalar metric proxy',nonzero=certificate.branch=='positive')


def mean_field_gap_equation(params: MeanFieldParams, *, scalar_enclosure=None, **accuracy) -> float:
    """Return the canonical scalar magnitude or propagate explicit refusal.

    This is an adopted scalar coordinate, not a physical tetrad derivation.
    """
    return _scalar_receipt(params,scalar_enclosure,**accuracy).C


def mean_field_metric_correlator(params: MeanFieldParams, *, scalar_enclosure=None, origin_enclosure=None, **accuracy) -> float:
    """Adopted proxy; origin numerical error is distinct from physical error."""
    if origin_enclosure is not None:
        return _origin_fluctuation(params,extensive=False,scalar_enclosure=scalar_enclosure,origin_enclosure=origin_enclosure,**accuracy)
    certificate=_scalar_receipt(params,scalar_enclosure,**accuracy)
    _mean_lattice(params)
    if certificate.branch=='positive':
        if origin_enclosure is not None:raise ValueError('positive scalar has no origin witness')
        return _scalar_metric(certificate)
    return _origin_fluctuation(params,extensive=False,scalar_enclosure=certificate,origin_enclosure=origin_enclosure,**accuracy)


def _total_metric_correlator(params: MeanFieldParams, *, scalar_enclosure=None, origin_enclosure=None, **accuracy) -> float:
    """Extensive adopted proxy, independently rounded with the same receipt."""
    if origin_enclosure is not None:
        return _origin_fluctuation(params,extensive=True,scalar_enclosure=scalar_enclosure,origin_enclosure=origin_enclosure,**accuracy)
    certificate=_scalar_receipt(params,scalar_enclosure,**accuracy)
    d,L,_=_mean_lattice(params)
    if certificate.branch=='positive':
        if origin_enclosure is not None:raise ValueError('positive scalar has no origin witness')
        return _scalar_metric(certificate,L**d)
    return _origin_fluctuation(params,extensive=True,scalar_enclosure=certificate,origin_enclosure=origin_enclosure,**accuracy)


def _classify_phase(C: float, params: MeanFieldParams, *, scalar_enclosure=None, origin_enclosure=None, **accuracy) -> str:
    """Actual scalar branch, then the strict true-pi adopted alpha classifier."""
    from src.core.formulas import _adw_exact
    if origin_enclosure is not None:
        _validate_origin_proxy_enclosure(origin_enclosure,params,scalar_enclosure,**accuracy)
    certificate=_scalar_receipt(params,scalar_enclosure,**accuracy)
    if _adw_exact(C,'C')!=_adw_exact(certificate.C,'returned C'):
        raise ValueError('C does not match the actual scalar receipt')
    if certificate.branch=='positive':
        if origin_enclosure is not None:raise ValueError('positive scalar has no origin witness')
        return 'full_tetrad'
    return _origin_receipt(params,certificate,origin_enclosure,**accuracy).phase


def vestigial_phase_window(Lambda: float, N_f: int, n_points: int=50, **accuracy) -> dict:
    """Original complete adopted-model grid; numerical refusal never skips."""
    from numbers import Integral
    if isinstance(n_points,(bool,np.bool_)) or not isinstance(n_points,Integral) or n_points<1:
        raise ValueError('positive integer n_points required')
    G_c=critical_coupling(Lambda,N_f)
    ratios=np.linspace(0.5,2.0,n_points)
    C_values=[];G_metric_values=[];phases=[];certificates=[];origins=[]
    for index,r in enumerate(ratios):
        params=MeanFieldParams(G=r*G_c,Lambda=Lambda,N_f=N_f)
        try:
            cert=_scalar_receipt(params,**accuracy)
            origin=_origin_receipt(params,cert,**accuracy) if cert.branch=='origin' else None
            metric=mean_field_metric_correlator(params,scalar_enclosure=cert,origin_enclosure=origin,**accuracy)
            phase=_classify_phase(cert.C,params,scalar_enclosure=cert,origin_enclosure=origin,**accuracy)
        except Exception as exc:
            exc.add_note(f'mean-field sample {index}, requested ratio {r}')
            raise
        C_values.append(cert.C);G_metric_values.append(metric);phases.append(phase)
        certificates.append(cert.as_dict());origins.append(None if origin is None else origin.as_dict())
    indices=[i for i,p in enumerate(phases) if p=='vestigial']
    return dict(coupling_ratios=ratios,C_tetrad=np.array(C_values),G_metric=np.array(G_metric_values),
        phases=phases,vestigial_min=ratios[indices[0]] if indices else 0.0,
        vestigial_max=ratios[indices[-1]] if indices else 0.0,vestigial_exists=bool(indices),
        scalar_enclosures=certificates,origin_proxy_enclosures=origins,
        physical_phase_status='uncomputed adopted curvature model')


def full_mean_field_analysis(G: float, Lambda: float, N_f: int=4, **accuracy) -> MeanFieldResult:
    """One scalar solve and one reused origin witness when that branch applies."""
    from fractions import Fraction
    params=MeanFieldParams(G=G,Lambda=Lambda,N_f=N_f)
    cert=_scalar_receipt(params,**accuracy)
    origin=_origin_receipt(params,cert,**accuracy) if cert.branch=='origin' else None
    metric=mean_field_metric_correlator(params,scalar_enclosure=cert,origin_enclosure=origin,**accuracy)
    phase=_classify_phase(cert.C,params,scalar_enclosure=cert,origin_enclosure=origin,**accuracy)
    d,_,_=_mean_lattice(params)
    if cert.branch=='positive':
        metric_eigs=np.array([metric]*d)
        interval=tuple(x*x for x in cert.magnitude_interval)
        metric_error=max(abs(Fraction.from_float(metric)-x) for x in interval)
    else:
        metric_eigs=np.array([origin.values[2]]*d)
        interval=metric_error=None  # no scalar-positive or physical certificate invented
    return MeanFieldResult(params,cert.C,metric,cert.V_eff,phase,phase=='vestigial',metric_eigs,
        None,cert,interval,metric_error,'uncomputed',bool(np.all(metric_eigs>0)),origin,
        None if origin is None else origin.intervals[0],None if origin is None else origin.errors[0])
