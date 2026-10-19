"""UNRUN independent-reference and actual transport controls for adopted origin proxy.

References use separate high-precision pi/Gaussian integration, with refinement.
No numerical, physical or native acceptance follows from authored source.
"""
from dataclasses import replace
from fractions import Fraction as Q
from copy import deepcopy
import json
import math
import pytest
import numpy as np
import mpmath as mp
from src.core import formulas as f
from src.vestigial import mean_field as mf
from src.vestigial import phase_diagram as pd
from src.core import visualizations as viz


def mq(q):
    return mp.mpf(q.numerator)/q.denominator


def independent_gaussian(params,dps):
    """Normalized one-dimensional Gaussian integrals, not production intervals."""
    with mp.workdps(dps):
        G,Lambda,Nf,T=(mq(f._adw_exact(v,k)) for v,k in
            ((params.G,'G'),(params.Lambda,'Lambda'),(params.N_f,'Nf'),(params.temperature,'T')))
        delta=mq(Q.from_float(1e-30));alpha=mq(Q.from_float(.3))
        b=Nf*Lambda**2/8
        kappa=1/G-b/mp.pi**2
        teff=max(T,Lambda/(4*mp.pi))
        W=mp.mpf(int(params.L))**int(params.d)
        a=W*(kappa+delta)/(2*teff)
        # Substitute y=sqrt(a)*x to keep both integrals O(1).
        denominator=mp.quad(lambda y:mp.exp(-y*y),[-mp.inf,0,mp.inf])
        numerator=mp.quad(lambda y:y*y*mp.exp(-y*y),[-mp.inf,0,mp.inf])
        variance=numerator/(a*denominator)
        site=int(params.d)**2*variance
        phase='vestigial' if mp.pi**2<(1+alpha)*b*G else 'pre_geometric'
        return dict(kappa=+kappa,teff=+teff,values=(+site,+(W*site),+(site/int(params.d))),phase=phase)


def actual_origin(params,**accuracy):
    scalar=mf._scalar_receipt(params,**accuracy)
    assert scalar.branch=='origin'
    return scalar,mf._origin_receipt(params,scalar,**accuracy)


@pytest.fixture(scope='module')
def nominal_origin():
    params=mf.MeanFieldParams(mf.critical_coupling(1.,4),1.,4)
    scalar,witness=actual_origin(params)
    return params,scalar,witness


class TestIndependentOriginNumerics:
    @pytest.mark.parametrize('cutoff',[Q(1,8),Q(1),Q(8)])
    @pytest.mark.parametrize('temperature',[Q(0),Q(10)])
    def test_actual_bounds_and_rounding_against_refined_gaussian(self,cutoff,temperature):
        params=mf.MeanFieldParams(Q(10)/(cutoff*cutoff),cutoff,4,d=2,L=8,temperature=temperature*cutoff)
        scalar,c=actual_origin(params)
        first=independent_gaussian(params,100)
        second=independent_gaussian(params,180)
        with mp.workdps(180):
            assert abs(first['kappa']-second['kappa'])<=mp.mpf('1e-70')*abs(second['kappa'])
            assert mq(c.raw_curvature_interval[0])<=second['kappa']<=mq(c.raw_curvature_interval[1])
            assert mq(c.curvature_interval[0])<=second['kappa']<=mq(c.curvature_interval[1])
            assert mq(c.temperature_interval[0])<=second['teff']<=mq(c.temperature_interval[1])
            for index,(bounds,value,error,expected) in enumerate(zip(c.intervals,c.values,c.errors,second['values'])):
                assert abs(first['values'][index]-expected)<=mp.mpf('1e-70')*abs(expected)
                assert mq(bounds[0])<=expected<=mq(bounds[1])
                assert abs(mp.mpf(value)-expected)<=mq(error)
                assert error==max(abs(Q.from_float(value)-x) for x in bounds)
                assert error<=c.requests[0]+c.requests[1]*abs(Q.from_float(value))
                assert value>0
        assert c.phase==second['phase']
        assert c.delta==Q.from_float(1e-30) and c.alpha==Q.from_float(.3)
        assert c.volume==8**2
        assert mf._validate_origin_proxy_enclosure(c,params,scalar) is c

    def test_actual_nominal_machine_reference_refines_without_fake_equality(self,nominal_origin):
        params,scalar,c=nominal_origin
        assert scalar.inputs[0]==Q.from_float(float(params.G))
        expected=independent_gaussian(params,180)
        with mp.workdps(180):
            assert expected['kappa']>0  # actual supplied binary G, not symbolic Gc
            assert mq(c.curvature_interval[0])<=expected['kappa']<=mq(c.curvature_interval[1])
        assert c.phase=='vestigial' and c.terms>4
        assert c.branch_evidence=='verified matching scalar origin; kappa>=0 intersection'
        result=mf.full_mean_field_analysis(params.G,1.,4)
        assert result.G_metric>0 and result.origin_proxy_error>=0
        assert result.scalar_metric_interval is None and result.scalar_metric_error is None
        assert result.is_lorentzian is None and result.physical_signature_status=='uncomputed'

    def test_zero_temperature_and_dominant_temperature_are_distinct_adopted_models(self):
        low=mf.MeanFieldParams(1.,1.,4,temperature=0.)
        high=mf.MeanFieldParams(1.,1.,4,temperature=10.)
        _,a=actual_origin(low);_,b=actual_origin(high)
        assert a.temperature_interval[0]>0
        assert b.temperature_interval==(Q(10),Q(10))
        assert all(y>x for x,y in zip(a.values,b.values))
        assert b.inputs[3]==Q(10)

    def test_gaussian_trace_and_extensive_factors_are_enclosed_not_float_identities(self):
        p=mf.MeanFieldParams(1.,1.,4,d=3,L=5)
        scalar,c=actual_origin(p)
        assert c.lattice==(3,5) and c.volume==125
        assert c.intervals[1]==tuple(125*x for x in c.intervals[0])
        assert c.intervals[2]==tuple(x/3 for x in c.intervals[0])
        assert mf.mean_field_metric_correlator(p,scalar_enclosure=scalar,origin_enclosure=c)==c.values[0]
        assert mf._total_metric_correlator(p,scalar_enclosure=scalar,origin_enclosure=c)==c.values[1]

    def test_strict_alpha_boundary_uses_two_sided_true_pi_sign(self):
        with mp.workdps(160):
            alpha=mq(Q.from_float(.3))
            crossing=2*mp.pi**2/(1+alpha)
            scale=10**40
            lower=Q(int(mp.floor(crossing*scale)),scale)
            upper=Q(int(mp.ceil(crossing*scale)),scale)
        p=mf.MeanFieldParams(lower,Q(1),4);_,a=actual_origin(p)
        q=mf.MeanFieldParams(upper,Q(1),4);_,b=actual_origin(q)
        assert a.phase=='pre_geometric' and a.pi_interval[0]**2>=a.threshold
        assert b.phase=='vestigial' and b.pi_interval[1]**2<b.threshold
        assert a.inputs[0]==lower and b.inputs[0]==upper

    def test_original_hundred_rows_and_nominal_one_are_not_moved_or_skipped(self):
        result=mf.vestigial_phase_window(1.,4,n_points=100)
        expected=list(np.linspace(.5,2.,100))
        assert list(result['coupling_ratios'])==expected
        assert len(result['scalar_enclosures'])==len(result['origin_proxy_enclosures'])==100
        assert expected[33]==1.0
        for scalar,origin,phase,metric in zip(result['scalar_enclosures'],result['origin_proxy_enclosures'],result['phases'],result['G_metric']):
            if scalar['branch']=='origin':
                assert origin is not None and origin['phase']==phase
                assert origin['values'][0]==float(metric)>0
            else:
                assert origin is None and phase=='full_tetrad'
        assert result['origin_proxy_enclosures'][33] is not None

    def test_external_origin_tolerance_does_not_change_scalar_requests(self):
        p=mf.MeanFieldParams(1.,1.,4)
        scalar,c=actual_origin(p,rtol=1e-9,energy_rtol=1e-7,origin_rtol=1e-12,origin_atol=Q(0))
        assert scalar.requested_rtol==Q.from_float(1e-9)
        assert scalar.requested_energy_rtol==Q.from_float(1e-7)
        assert c.requests==(Q(0),Q.from_float(1e-12))
        assert c.max_work==scalar.max_work==200000
        data=pd.scan_coupling(coupling_range=(.5,.5),n_points=1,origin_rtol=1e-12)
        assert data.points[0].origin_proxy_enclosure.requests==(Q(0),Q.from_float(1e-12))

    @pytest.mark.parametrize('options',[dict(origin_rtol=True),dict(origin_atol=False),dict(origin_rtol=-1),
        dict(origin_rtol=float('inf')),dict(origin_atol=0,origin_rtol=0),dict(origin_atol=-1)])
    def test_invalid_origin_policy_refuses_on_origin_and_positive(self,options):
        for G in (1.,40.):
            with pytest.raises(ValueError):mf.full_mean_field_analysis(G,1.,4,**options)

    @pytest.mark.parametrize('options',[dict(max_work=1),dict(max_bits=8),
        dict(origin_rtol=Q(1,10**100),max_work=1000)])
    def test_finite_or_unattainable_policy_refuses_not_zero(self,options):
        with pytest.raises(f.ADWScalarUnresolved):mf.full_mean_field_analysis(1.,1.,4,**options)

    @pytest.mark.parametrize('kind',['underflow','overflow'])
    def test_origin_positive_representation_failure_is_explicit(self,kind):
        if kind=='underflow':
            cutoff=Q(10**400);p=mf.MeanFieldParams(1/(cutoff*cutoff),cutoff,4)
        else:
            p=mf.MeanFieldParams(1.,1.,4,temperature=Q(10**400))
        scalar=mf._scalar_receipt(p)
        assert scalar.branch=='origin'
        with pytest.raises(f.ADWScalarUnresolved):mf._origin_receipt(p,scalar)

    def test_positive_scalar_never_carries_origin_proxy(self):
        result=mf.full_mean_field_analysis(40.,1.,4,origin_rtol=1e-12)
        assert result.scalar_enclosure.branch=='positive'
        assert result.origin_proxy_enclosure is result.origin_proxy_interval is result.origin_proxy_error is None
        assert result.scalar_metric_interval is not None


class TestOriginWitnessPolicyAndSemantics:
    @pytest.mark.parametrize('kind',['requests_false_zero','inputs_false_temperature','pi','raw_curvature',
        'intersection','temperature','interval','interval_bool','values_bool','output','error',
        'phase','threshold','delta','alpha','volume','lattice','model','branch_evidence','terms','work','bits'])
    def test_actual_witness_semantic_or_type_corruption_refuses(self,nominal_origin,kind):
        p,scalar,c=nominal_origin
        if kind=='requests_false_zero':bad=replace(c,requests=(False,c.requests[1]))
        elif kind=='inputs_false_temperature':bad=replace(c,inputs=(*c.inputs[:3],False))
        elif kind=='pi':bad=replace(c,pi_interval=(Q(3),Q(4)))
        elif kind=='raw_curvature':bad=replace(c,raw_curvature_interval=(Q(0),Q(0)))
        elif kind=='intersection':bad=replace(c,curvature_interval=(Q(0),Q(0)))
        elif kind=='temperature':bad=replace(c,temperature_interval=(Q(1),Q(1)))
        elif kind=='interval':bad=replace(c,intervals=((Q(0),Q(0)),*c.intervals[1:]))
        elif kind=='interval_bool':bad=replace(c,intervals=((False,c.intervals[0][1]),*c.intervals[1:]))
        elif kind=='values_bool':bad=replace(c,values=(True,*c.values[1:]))
        elif kind=='output':bad=replace(c,values=(2*c.values[0],*c.values[1:]))
        elif kind=='error':bad=replace(c,errors=(Q(0),*c.errors[1:]))
        elif kind=='phase':bad=replace(c,phase='pre_geometric')
        elif kind=='threshold':bad=replace(c,threshold=c.threshold+1)
        elif kind=='delta':bad=replace(c,delta=Q(1,10**30))  # decimal differs from adopted binary64
        elif kind=='alpha':bad=replace(c,alpha=Q(3,10))
        elif kind=='volume':bad=replace(c,volume=c.volume+1)
        elif kind=='lattice':bad=replace(c,lattice=(4,64))
        elif kind=='model':bad=replace(c,model='physical-susceptibility')
        elif kind=='branch_evidence':bad=replace(c,branch_evidence='unverified floor')
        elif kind=='terms':bad=replace(c,terms=c.max_work+1)
        elif kind=='work':bad=replace(c,max_work=c.max_work+1)
        else:bad=replace(c,max_bits=c.max_bits+1)
        with pytest.raises(ValueError):mf._validate_origin_proxy_enclosure(bad,p,scalar)

    @pytest.mark.parametrize('kind',['work','bits','request'])
    def test_external_policy_refusal_precedes_expensive_origin_recompute(self,nominal_origin,monkeypatch,kind):
        p,scalar,c=nominal_origin
        def forbidden(*a,**kw):raise AssertionError('expensive origin replay reached')
        monkeypatch.setattr(f,'_adw_origin_at_terms',forbidden)
        bad=(replace(c,max_work=c.max_work+1) if kind=='work' else
            replace(c,max_bits=c.max_bits+1) if kind=='bits' else replace(c,requests=(Q(0),Q(1,10))))
        with pytest.raises(ValueError):mf._validate_origin_proxy_enclosure(bad,p,scalar)

    @pytest.mark.parametrize('field',['G','Lambda','N_f','temperature','L'])
    def test_receipt_cannot_change_actual_problem(self,nominal_origin,field):
        p,scalar,c=nominal_origin
        values=dict(G=p.G,Lambda=p.Lambda,N_f=p.N_f,temperature=p.temperature,L=p.L)
        values[field]=values[field]+1
        other=mf.MeanFieldParams(**values)
        with pytest.raises(ValueError):mf._validate_origin_proxy_enclosure(c,other,scalar)

    def test_serialized_snapshot_is_output_only_and_uses_existing_codec(self,nominal_origin):
        _,_,c=nominal_origin
        data=c.as_dict();encoded=json.dumps(data,allow_nan=False)
        assert 'adopted-origin-gaussian-exact-pi' in encoded
        assert data['inputs'][3]==dict(numerator='0',denominator='1')
        assert data['delta']!=dict(numerator='1',denominator='1000000000000000000000000000000')
        assert type(data['requests'][0]['numerator']) is str
        # An output dict is not an admitted in-memory witness.
        with pytest.raises(ValueError):mf._validate_origin_proxy_enclosure(data,*nominal_origin[:2])


@pytest.fixture(scope='module')
def actual_outer_origin_grid():
    data=pd.scan_coupling(Lambda=1.,N_f=4,coupling_range=(.3,3.),n_points=60)
    assert data.points[0].scalar_enclosure.branch=='origin'
    assert data.points[0].origin_proxy_enclosure is data.points[0].mean_field_result.origin_proxy_enclosure
    return data


class TestActualOriginTransport:
    @pytest.mark.parametrize('poison',['missing','alias','normalized_error_bool','normalized_interval_bool',
        'source_error_bool','source_interval_list','witness_zero_request_bool','witness_temperature_bool',
        'source_phase','source_volume','scalar_positive_fields','physical_false'])
    def test_new_fields_rejected_by_actual_fig42(self,actual_outer_origin_grid,monkeypatch,poison):
        data=deepcopy(actual_outer_origin_grid);p=data.points[0];result=p.mean_field_result
        if poison=='missing':p.origin_proxy_enclosure=None
        elif poison=='alias':p.origin_proxy_enclosure=replace(p.origin_proxy_enclosure)
        elif poison=='normalized_error_bool':p.origin_metric_error=False
        elif poison=='normalized_interval_bool':p.origin_metric_interval=(False,p.origin_metric_interval[1])
        elif poison=='source_error_bool':result.origin_proxy_error=False
        elif poison=='source_interval_list':result.origin_proxy_interval=list(result.origin_proxy_interval)
        elif poison=='witness_zero_request_bool':result.origin_proxy_enclosure=replace(result.origin_proxy_enclosure,requests=(False,result.origin_proxy_enclosure.requests[1]))
        elif poison=='witness_temperature_bool':result.origin_proxy_enclosure=replace(result.origin_proxy_enclosure,inputs=(*result.origin_proxy_enclosure.inputs[:3],False))
        elif poison=='source_phase':result.phase='full_tetrad'
        elif poison=='source_volume':result.params.L=64
        elif poison=='scalar_positive_fields':result.scalar_metric_interval=result.origin_proxy_interval
        else:result.is_lorentzian=False
        monkeypatch.setattr(pd,'scan_coupling',lambda **kw:data)
        with pytest.raises(ValueError) as exc:viz.fig_vestigial_phase_diagram()
        assert any('vestigial figure row 0' in s for s in exc.value.__notes__)

    def test_actual_figure_emits_distinct_numeric_origin_error_and_physical_unknown(self,actual_outer_origin_grid,monkeypatch):
        data=deepcopy(actual_outer_origin_grid)
        monkeypatch.setattr(pd,'scan_coupling',lambda **kw:data)
        figure=viz.fig_vestigial_phase_diagram();rows=figure.layout.meta['rows']
        assert len(rows)==60 and len(figure.data[0].x)==60
        for row,p in zip(rows,data.points):
            assert row['is_lorentzian'] is None
            if p.scalar_enclosure.branch=='origin':
                assert row['metric_error'] is None
                assert row['adopted_origin_proxy']['model']=='adopted-origin-gaussian-exact-pi'
                e=row['adopted_origin_metric_error'];bound=Q(int(e['numerator']),int(e['denominator']))
                assert bound==p.origin_metric_error>=0
                assert row['adopted_origin_metric_interval'] is not None
            else:
                assert row['adopted_origin_proxy'] is row['adopted_origin_metric_error'] is None
        json.dumps(figure.to_dict()['layout']['meta'],allow_nan=False)

    @pytest.mark.parametrize('name',['d','L','temperature'])
    def test_actual_scan_binder_rejects_changed_default_lattice(self,actual_outer_origin_grid,name):
        p=deepcopy(actual_outer_origin_grid.points[0]);setattr(p.mean_field_result.params,name,99)
        with pytest.raises(ValueError):pd._phase_point_from_mean_field(p.mean_field_result,p.coupling_ratio,*p.scalar_inputs)

    def test_normalized_origin_error_includes_final_rounding(self,actual_outer_origin_grid):
        for p in actual_outer_origin_grid.points:
            if p.origin_proxy_enclosure is None:continue
            cutoff=f._adw_exact(p.scalar_inputs[1],'cutoff')
            original=p.origin_proxy_enclosure.intervals[0]
            assert p.origin_metric_interval==tuple(x/cutoff**2 for x in original)
            assert p.origin_metric_error==max(abs(Q.from_float(float(p.metric_mag))-x) for x in p.origin_metric_interval)


class TestCanonicalOriginOwnershipAndPreflight:
    def test_actual_canonical_type_provider_and_domain_primitive_facade(self,nominal_origin,monkeypatch):
        params,scalar,c=nominal_origin
        assert type(c) is f.ADWOriginProxyEnclosure is mf.OriginProxyEnclosure
        assert f.adw_origin_proxy.__module__==f.__name__
        assert f.adw_validate_origin_proxy_enclosure.__module__==f.__name__
        original=f.adw_origin_proxy;calls=[]
        def actual(*args,**kwargs):
            calls.append((args,kwargs.copy()))
            return original(*args,**kwargs)
        monkeypatch.setattr(mf,'adw_origin_proxy',actual)
        from_domain=mf._origin_receipt(params,scalar)
        assert len(calls)==1
        args,kwargs=calls[0]
        assert args==(params.G,params.Lambda,params.N_f)
        assert kwargs['d']==params.d and kwargs['L']==params.L and kwargs['temperature']==params.temperature
        assert kwargs['scalar_enclosure'] is scalar
        assert from_domain.values==c.values and from_domain.intervals==c.intervals
        assert f.adw_validate_origin_proxy_enclosure(from_domain,*args,
            scalar_enclosure=scalar,d=params.d,L=params.L,temperature=params.temperature) is from_domain

    @pytest.mark.parametrize('field',['model','phase','branch_evidence'])
    def test_unknown_model_phase_evidence_refuses_before_any_replay(self,nominal_origin,monkeypatch,field):
        p,scalar,c=nominal_origin
        bad=replace(c,**{field:'not-the-adopted-contract'})
        def forbidden(*a,**kw):raise AssertionError('scalar or pi replay reached before admission')
        for name in ('adw_scalar_minimum','adw_validate_scalar_enclosure','_adw_pi_bounds','_adw_origin_at_terms'):
            monkeypatch.setattr(f,name,forbidden)
        with pytest.raises(ValueError):
            f.adw_validate_origin_proxy_enclosure(bad,p.G,p.Lambda,p.N_f,scalar_enclosure=scalar)

    @pytest.mark.parametrize('field',['inputs','requests','pi_interval','raw_curvature_interval',
        'curvature_interval','temperature_interval','lattice','volume','terms','max_work','max_bits',
        'work_used','delta','alpha','threshold','intervals','errors'])
    def test_all_incoming_exact_payload_sizes_refuse_before_any_replay(self,nominal_origin,monkeypatch,field):
        p,scalar,c=nominal_origin
        # Correct types/shapes; size exceeds the trusted EXTERNAL bit cap.
        huge=1<<(c.max_bits+1)
        if field in ('inputs','requests','pi_interval','raw_curvature_interval','curvature_interval','temperature_interval'):
            row=getattr(c,field);bad=replace(c,**{field:(Q(huge),*row[1:])})
        elif field=='lattice':bad=replace(c,lattice=(huge,c.lattice[1]))
        elif field=='intervals':bad=replace(c,intervals=((Q(huge),c.intervals[0][1]),*c.intervals[1:]))
        elif field=='errors':bad=replace(c,errors=(Q(huge),*c.errors[1:]))
        elif field in ('delta','alpha','threshold'):bad=replace(c,**{field:Q(huge)})
        else:bad=replace(c,**{field:huge})
        def forbidden(*a,**kw):raise AssertionError('scalar or pi replay reached before payload admission')
        for name in ('adw_scalar_minimum','adw_validate_scalar_enclosure','_adw_pi_bounds','_adw_origin_at_terms'):
            monkeypatch.setattr(f,name,forbidden)
        with pytest.raises(f.ADWScalarUnresolved):
            f.adw_validate_origin_proxy_enclosure(bad,p.G,p.Lambda,p.N_f,
                scalar_enclosure=scalar,max_bits=c.max_bits,max_work=c.max_work)

    def test_paired_valid_fraction_zero_payload_and_matching_numpy_inputs(self,nominal_origin):
        p,scalar,c=nominal_origin
        assert type(c.requests[0]) is Q and c.requests[0]==0
        assert type(c.inputs[3]) is Q and c.inputs[3]==0
        assert f.adw_validate_origin_proxy_enclosure(c,np.float64(p.G),np.float64(p.Lambda),
            np.int64(p.N_f),d=np.int64(p.d),L=np.int64(p.L),temperature=np.float64(0),
            scalar_enclosure=scalar) is c

    @pytest.mark.parametrize('route',['receipt','validator','metric','total','classifier','phase','figure'])
    def test_real_consumer_routes_preflight_bad_model_before_any_scalar(self,actual_outer_origin_grid,monkeypatch,route):
        data=deepcopy(actual_outer_origin_grid);point=data.points[0];result=point.mean_field_result
        params=result.params;scalar=result.scalar_enclosure
        bad=replace(result.origin_proxy_enclosure,model='physical-susceptibility')
        result.origin_proxy_enclosure=bad
        def forbidden(*a,**kw):raise AssertionError('consumer replay occurred before canonical model admission')
        for name in ('adw_scalar_minimum','adw_validate_scalar_enclosure','_adw_pi_bounds','_adw_origin_at_terms'):
            monkeypatch.setattr(f,name,forbidden)
        monkeypatch.setattr(mf,'_scalar_receipt',forbidden)
        if route=='figure':monkeypatch.setattr(pd,'scan_coupling',lambda **kw:data)
        with pytest.raises(ValueError):
            if route=='receipt':mf._origin_receipt(params,scalar,bad)
            elif route=='validator':mf._validate_origin_proxy_enclosure(bad,params,scalar)
            elif route=='metric':mf.mean_field_metric_correlator(params,scalar_enclosure=scalar,origin_enclosure=bad)
            elif route=='total':mf._total_metric_correlator(params,scalar_enclosure=scalar,origin_enclosure=bad)
            elif route=='classifier':mf._classify_phase(scalar.C,params,scalar_enclosure=scalar,origin_enclosure=bad)
            elif route=='phase':pd._phase_point_from_mean_field(result,point.coupling_ratio,*point.scalar_inputs)
            else:viz.fig_vestigial_phase_diagram()


@pytest.fixture(scope='module',params=[1.,1e-40])
def actual_positive_eigen_result(request):
    cutoff=request.param;G=2.*mf.critical_coupling(cutoff,4)
    result=mf.full_mean_field_analysis(G,cutoff,4)
    assert result.scalar_enclosure.branch=='positive'
    assert result.G_metric>0
    return result


class TestRealPositiveEigenvalueBinding:
    def test_matching_numpy_positive_and_tiny_values_are_admitted(self,actual_positive_eigen_result):
        source=deepcopy(actual_positive_eigen_result)
        source.metric_eigenvalues=np.array([source.G_metric]*source.params.d,dtype=np.float64)
        point=pd._phase_point_from_mean_field(source,2.,source.params.G,source.params.Lambda,source.params.N_f)
        assert point.mean_field_result is source and point.phase=='full_tetrad'
        assert point.origin_proxy_enclosure is point.origin_metric_interval is point.origin_metric_error is None
        assert source.is_lorentzian is None and source.physical_signature_status=='uncomputed'
        assert all(type(x) is np.float64 for x in source.metric_eigenvalues)

    @pytest.mark.parametrize('poison',['all_positive_rescaled','single_positive_entry'])
    def test_actual_positive_binder_refuses_changed_eigenvalues(self,actual_positive_eigen_result,poison):
        source=deepcopy(actual_positive_eigen_result)
        if poison=='all_positive_rescaled':source.metric_eigenvalues=source.metric_eigenvalues*2.
        else:source.metric_eigenvalues[0]*=2.
        assert np.all(np.isfinite(source.metric_eigenvalues)) and np.all(source.metric_eigenvalues>0)
        assert source.metric_positive_definite is True
        with pytest.raises(ValueError,match='positive metric eigenvalue/source mismatch'):
            pd._phase_point_from_mean_field(source,2.,source.params.G,source.params.Lambda,source.params.N_f)

    @pytest.mark.parametrize('poison',['all_positive_rescaled','single_positive_entry'])
    def test_actual_fig42_refuses_genuine_positive_source_eigenvalue_poison(self,actual_outer_origin_grid,monkeypatch,poison):
        data=deepcopy(actual_outer_origin_grid)
        index,point=next((i,p) for i,p in enumerate(data.points) if p.scalar_enclosure.branch=='positive')
        source=point.mean_field_result
        if poison=='all_positive_rescaled':source.metric_eigenvalues=source.metric_eigenvalues*2.
        else:source.metric_eigenvalues[-1]*=2.
        assert source.metric_positive_definite is True and np.all(source.metric_eigenvalues>0)
        monkeypatch.setattr(pd,'scan_coupling',lambda **kw:data)
        with pytest.raises(ValueError,match='positive metric eigenvalue/source mismatch') as exc:
            viz.fig_vestigial_phase_diagram()
        assert any(f'vestigial figure row {index}' in note for note in exc.value.__notes__)


class TestExternalPhaseOriginPolicy:
    def test_actual_external_phase_inputs_refuse_before_scalar_replay(self,actual_outer_origin_grid,monkeypatch):
        point=deepcopy(actual_outer_origin_grid.points[0]);result=point.mean_field_result
        def forbidden(*a,**kw):raise AssertionError('external input mismatch reached scalar/pi replay')
        for name in ('adw_scalar_minimum','adw_validate_scalar_enclosure','_adw_pi_bounds','_adw_origin_at_terms'):
            monkeypatch.setattr(f,name,forbidden)
        with pytest.raises(ValueError,match='actual-parameter/lattice mismatch'):
            pd._phase_point_from_mean_field(result,point.coupling_ratio,
                point.scalar_inputs[0]*2,point.scalar_inputs[1],point.scalar_inputs[2])
