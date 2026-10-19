"""Outer scalar assurance SOURCE; real numerics vs controlled transport distinguished.

Requires the accepted canonical M1r2 and downstream proposals; UNRUN at authoring.
No mocked result is an independent numerical or physical correctness witness.
"""
from dataclasses import replace
from fractions import Fraction as Q
import json
from pathlib import Path
import numpy as np
import pytest
from src.core.formulas import ADWScalarUnresolved, adw_scalar_minimum
from src.adw.gap_equation import critical_coupling
from src.vestigial.phase_diagram import scan_coupling, _phase_normalize, _phase_point_from_mean_field
from src.vestigial.mean_field import full_mean_field_analysis
from src.core import visualizations as viz


class TestExactNormalization:
    @pytest.mark.parametrize('power',[1,2,4])
    def test_independent_rational_rounding_bound(self,power):
        interval=(Q(1,12),Q(1,9))
        value,bounds,error=_phase_normalize(.1,interval,3.,power)
        assert bounds==(interval[0]/3**power,interval[1]/3**power)
        assert value==float(Q.from_float(.1)/3**power)
        assert error==max(abs(Q.from_float(value)-x) for x in bounds)
        # The target interval need not contain the rounded representation.
        point=(Q(1,10),Q(1,10))
        value,bounds,error=_phase_normalize(.1,point,3.,power)
        assert error==abs(Q.from_float(value)-Q(1,10)/3**power)>0

    def test_unknown_proxy_uncertainty_remains_none(self):
        value,interval,error=_phase_normalize(.1,None,3.,2)
        assert value==float(Q.from_float(.1)/9)
        assert interval is None and error is None

    @pytest.mark.parametrize('value,cutoff,power',[(1e-300,1e100,2),(1e300,1e-100,2)])
    def test_no_normalized_nonzero_collapse(self,value,cutoff,power):
        with pytest.raises(ADWScalarUnresolved):_phase_normalize(value,None,cutoff,power)

    @pytest.mark.parametrize('value,cutoff,power',[(True,1,1),(1,False,1),(-1,1,1),(1,0,1),(1,float('nan'),1),(1,1,3)])
    def test_invalid_normalization_refuses(self,value,cutoff,power):
        with pytest.raises(ValueError):_phase_normalize(value,None,cutoff,power)


class TestActualScan:
    @pytest.mark.parametrize('cutoff',[.125,1.,8.])
    def test_real_positive_metric_interval_scaling(self,cutoff):
        data=scan_coupling(Lambda=cutoff,N_f=4,coupling_range=(2.,2.),n_points=1)
        point=data.points[0];cert=point.scalar_enclosure;scale=Q.from_float(cutoff)
        assert point.scalar_inputs==(2.*critical_coupling(cutoff,4),cutoff,4)
        assert cert.branch=='positive' and point.mean_field_result.scalar_enclosure is cert
        assert point.tetrad_interval==tuple(x/scale for x in cert.magnitude_interval)
        assert point.metric_interval==tuple(x*x/scale**2 for x in cert.magnitude_interval)
        assert point.metric_error==max(abs(Q.from_float(point.metric_mag)-x) for x in point.metric_interval)
        assert point.tetrad_error==max(abs(Q.from_float(point.tetrad_vev)-x) for x in point.tetrad_interval)
        assert point.is_lorentzian is None and point.physical_signature_status=='uncomputed'
        assert point.metric_positive_definite is True

    def test_real_tiny_positive_root_is_not_old_floor(self):
        data=scan_coupling(Lambda=1e-12,N_f=4,coupling_range=(1.01,1.01),n_points=1)
        p=data.points[0]
        assert p.scalar_enclosure.branch=='positive' and 0<p.scalar_enclosure.C<1e-12
        assert p.phase=='full_tetrad' and p.metric_mag>0

    def test_real_origin_keeps_unknown_proxy_error(self):
        p=scan_coupling(coupling_range=(.5,.5),n_points=1).points[0]
        assert p.scalar_enclosure.branch=='origin'
        assert p.tetrad_vev==0 and p.tetrad_error==0
        assert p.metric_interval is None and p.metric_error is None
        assert p.is_lorentzian is None

    def test_actual_receipt_generated_once_per_row(self,monkeypatch):
        from src.core import formulas as canonical
        original=canonical.adw_scalar_minimum;calls=[]
        def spy(*a,**k):calls.append((a,k));return original(*a,**k)
        monkeypatch.setattr(canonical,'adw_scalar_minimum',spy)
        result=scan_coupling(coupling_range=(.3,3.),n_points=7)
        assert len(calls)==len(result.points)==7
        assert list(result.coupling_ratios)==list(np.linspace(.3,3.,7))
        expected=[(float(result.coupling_ratios[i-1]),float(result.coupling_ratios[i]),result.phases[i-1],result.phases[i]) for i in range(1,7) if result.phases[i]!=result.phases[i-1]]
        assert result.sampled_transition_brackets==expected

    def test_actual_failure_identity_and_no_skipping(self,monkeypatch):
        # Controlled transport failure; not a synthetic numerical oracle.
        from src.vestigial import phase_diagram as pd
        original=pd.full_mean_field_analysis;calls=[];failure=ADWScalarUnresolved('controlled refusal')
        def spy(*a,**k):
            calls.append(k['G'])
            if len(calls)==3:raise failure
            return original(*a,**k)
        monkeypatch.setattr(pd,'full_mean_field_analysis',spy)
        with pytest.raises(ADWScalarUnresolved) as exc:pd.scan_coupling(n_points=10)
        assert exc.value is failure and len(calls)==3
        assert any('sample 2' in s for s in failure.__notes__)

    @pytest.mark.parametrize('attribute,value',[('is_lorentzian',False),('physical_signature_status','verified'),('scalar_metric_error',Q(0)),('phase','vestigial'),('G_metric',0.),('metric_positive_definite',False)])
    def test_actual_result_poison_rejected(self,attribute,value):
        G=2*critical_coupling(1.,4);result=full_mean_field_analysis(G,1.,4)
        setattr(result,attribute,value)
        with pytest.raises(ValueError):_phase_point_from_mean_field(result,2.,G,1.,4)

    def test_actual_changed_input_refuses(self):
        G=2*critical_coupling(1.,4);result=full_mean_field_analysis(G,1.,4)
        with pytest.raises(ValueError):_phase_point_from_mean_field(result,2.,G*2,1.,4)

    def test_explicit_nominalcritical_proxy_refusal(self):
        # Default true-pi refinement now succeeds; explicit finite limits still refuse.
        G=critical_coupling(1.,4);cert=adw_scalar_minimum(G,1.,4)
        assert cert.branch=='origin'
        result=full_mean_field_analysis(G,1.,4)
        assert result.origin_proxy_enclosure.inputs[:3]==cert.inputs
        assert result.origin_proxy_enclosure.curvature_interval[0]>=0
        assert result.origin_proxy_error>=0 and result.G_metric>0
        assert result.scalar_metric_interval is None and result.scalar_metric_error is None
        assert result.is_lorentzian is None and result.phase=='vestigial'
        with pytest.raises(ADWScalarUnresolved):full_mean_field_analysis(G,1.,4,max_work=1)


    def test_actual_external_accuracy_is_preserved(self):
        result=scan_coupling(coupling_range=(2.,3.),n_points=2,rtol=1e-9,energy_rtol=1e-7)
        for p in result.points:
            assert p.scalar_enclosure.requested_rtol==Q.from_float(1e-9)
            assert p.scalar_enclosure.requested_energy_rtol==Q.from_float(1e-7)
            assert p.scalar_enclosure.max_work==200000 and p.scalar_enclosure.max_bits==100000

    def test_real_budget_refusal_is_not_a_zero_row(self):
        with pytest.raises(ADWScalarUnresolved):
            scan_coupling(coupling_range=(2.,3.),n_points=2,max_work=1)


class TestActualFigureConsumers:
    def test_real_gl_full_population_and_independent_scaled_errors(self):
        fig=viz.fig_gl_phase_diagram();meta=fig.layout.meta
        assert len(meta['rows'])==60 and len(fig.data)==4
        assert list(fig.data[0].x)==list(np.linspace(.5,5.,60))
        for row,y4,y3,y2 in zip(meta['rows'],fig.data[1].y,fig.data[2].y,fig.data[3].y):
            cert=row['scalar_enclosure'];v=cert['V_eff']
            assert [y4,y3,y2]==[float(n*Q.from_float(v)) for n in (4,3,2)]
            for n,y in [(4,y4),(3,y3),(2,y2)]:
                item=row['energies'][str(n)]
                bounds=[Q(int(x['numerator']),int(x['denominator'])) for x in item['interval']]
                e=item['absolute_error'];error=Q(int(e['numerator']),int(e['denominator']))
                assert error==max(abs(Q.from_float(y)-x) for x in bounds)
        assert meta['physical_phase_status']=='uncomputed'
        assert 'scalar' in fig.layout.title.text and 'quartic' in fig.layout.annotations[-1].text
        # Actual dict serialization route; metadata itself is JSON-safe.
        json.dumps(fig.to_dict()['layout']['meta'],allow_nan=False)

    def test_real_vestigial_full_population_and_unknown_not_zero(self):
        fig=viz.fig_vestigial_phase_diagram();meta=fig.layout.meta
        assert len(meta['rows'])==60 and len(fig.data)==3
        assert list(fig.data[0].x)==list(np.linspace(.3,3.,60))
        assert meta['physical_signature_status']=='uncomputed'
        origins=[row for row in meta['rows'] if row['scalar_enclosure']['branch']=='origin']
        assert origins and all(row['metric_error'] is None for row in origins)
        assert all(row['is_lorentzian'] is None for row in meta['rows'])
        assert 'proxy/Λ²' in fig.layout.yaxis.title.text
        json.dumps(fig.to_dict()['layout']['meta'],allow_nan=False)

    @pytest.mark.parametrize('poison',['missing','energy','error','brackets','grid','request','inputs'])
    def test_gl_actual_consumer_rejects_poison(self,monkeypatch,poison):
        from src.adw import ginzburg_landau as gl
        result=gl.compute_phase_diagram(1.,4,n_points=60)
        if poison=='missing':result.scalar_enclosures=result.scalar_enclosures[:-1]
        if poison=='energy':result.free_energies_B[-1]=0.
        if poison=='error':result.scalar_energy_errors[4][-1]=Q(-1)
        if poison=='brackets':result.sampled_transition_brackets=[]
        if poison=='grid':result.coupling_ratios[0]=.1
        if poison=='request':result.scalar_enclosures[-1]=replace(result.scalar_enclosures[-1],requested_rtol=Q(1))
        if poison=='inputs':
            c=result.scalar_enclosures[-1]
            result.scalar_enclosures[-1]=replace(c,inputs=(2*c.inputs[0],*c.inputs[1:]))
        monkeypatch.setattr(gl,'compute_phase_diagram',lambda **k:result)
        with pytest.raises(ValueError):viz.fig_gl_phase_diagram()

    @pytest.mark.parametrize('poison',['missing','error','physical','arrays','grid'])
    def test_vestigial_actual_consumer_rejects_poison(self,monkeypatch,poison):
        from src.vestigial import phase_diagram as pd
        result=pd.scan_coupling(Lambda=1.,N_f=4,coupling_range=(.3,3.),n_points=60)
        if poison=='missing':result.points=result.points[:-1]
        if poison=='error':result.points[-1].tetrad_error=Q(-1)
        if poison=='physical':result.points[-1].is_lorentzian=True
        if poison=='arrays':result.metric_values[-1]=0.
        if poison=='grid':result.coupling_ratios[0]=.1
        monkeypatch.setattr(pd,'scan_coupling',lambda **k:result)
        with pytest.raises(ValueError):viz.fig_vestigial_phase_diagram()

    @pytest.mark.parametrize('name',['fig_gl_phase_diagram','fig_vestigial_phase_diagram'])
    def test_actual_producer_failure_propagates_without_figure(self,monkeypatch,name):
        # Transport only: real entrypoint, controlled upstream refusal, no render.
        from src.adw import ginzburg_landau as gl
        from src.vestigial import phase_diagram as pd
        failure=ADWScalarUnresolved('controlled upstream refusal')
        def refuse(**k):raise failure
        monkeypatch.setattr(gl if name=='fig_gl_phase_diagram' else pd,'compute_phase_diagram' if name=='fig_gl_phase_diagram' else 'scan_coupling',refuse)
        with pytest.raises(ADWScalarUnresolved) as exc:getattr(viz,name)()
        assert exc.value is failure


@pytest.fixture(scope='module')
def _outer_genuine_origin_grid():
    """Real source-generated receipts, not hand-built or synthetic scalar proofs."""
    data=scan_coupling(Lambda=1.,N_f=4,coupling_range=(.3,3.),n_points=60)
    assert data.points[0].scalar_enclosure.branch=='origin'
    assert type(data.points[0].tetrad_error) is Q and data.points[0].tetrad_error==0
    assert data.points[0].metric_error is None
    return data


class TestStrictOuterOriginTransport:
    @pytest.mark.parametrize('poison',[
        'error_false','error_int','error_float','endpoint_bool','endpoint_int',
        'endpoint_float','interval_list','positivity_int_one','positivity_int_zero',
        'positivity_numpy_bool','array_bool','array_numpy_bool','point_bool',
        'input_tuple_bool','source_lambda_bool','unknown_metric_error_zero'])
    def test_real_origin_equal_value_poison_rejected(self,monkeypatch,_outer_genuine_origin_grid,poison):
        # Actual Fig42, real origin receipt, controlled transport corruption ONLY.
        from copy import deepcopy
        from src.vestigial import phase_diagram as pd
        data=deepcopy(_outer_genuine_origin_grid);p=data.points[0]
        assert type(p.tetrad_error) is Q and p.tetrad_error==0
        assert p.tetrad_interval==(Q(0),Q(0)) and p.metric_positive_definite is True
        if poison=='error_false':p.tetrad_error=False
        if poison=='error_int':p.tetrad_error=0
        if poison=='error_float':p.tetrad_error=0.
        if poison=='endpoint_bool':p.tetrad_interval=(False,Q(0))
        if poison=='endpoint_int':p.tetrad_interval=(0,Q(0))
        if poison=='endpoint_float':p.tetrad_interval=(0.,Q(0))
        if poison=='interval_list':p.tetrad_interval=[Q(0),Q(0)]
        if poison=='positivity_int_one':p.metric_positive_definite=1
        if poison=='positivity_int_zero':p.metric_positive_definite=0
        if poison=='positivity_numpy_bool':p.metric_positive_definite=np.bool_(True)
        if poison in ('array_bool','array_numpy_bool'):
            data.tetrad_values=list(data.tetrad_values)
            data.tetrad_values[0]=False if poison=='array_bool' else np.bool_(False)
        if poison=='point_bool':p.tetrad_vev=False
        if poison=='input_tuple_bool':p.scalar_inputs=(p.scalar_inputs[0],True,p.scalar_inputs[2])
        if poison=='source_lambda_bool':p.mean_field_result.params.Lambda=True
        if poison=='unknown_metric_error_zero':p.metric_error=Q(0)
        monkeypatch.setattr(pd,'scan_coupling',lambda **k:data)
        with pytest.raises(ValueError) as caught:viz.fig_vestigial_phase_diagram()
        assert any('vestigial figure row 0' in s for s in caught.value.__notes__)

    def test_genuine_origin_fraction_zero_none_and_numpy_array_pass(self,monkeypatch,_outer_genuine_origin_grid):
        from copy import deepcopy
        from src.vestigial import phase_diagram as pd
        data=deepcopy(_outer_genuine_origin_grid)
        data.points[0].tetrad_vev=np.float64(0.)
        data.tetrad_values=list(data.tetrad_values);data.tetrad_values[0]=np.float32(0.)
        monkeypatch.setattr(pd,'scan_coupling',lambda **k:data)
        fig=viz.fig_vestigial_phase_diagram();row=fig.layout.meta['rows'][0]
        assert len(fig.layout.meta['rows'])==60
        assert row['tetrad_error']=={'numerator':'0','denominator':'1'}
        assert row['metric_error'] is None and row['metric_interval'] is None
        assert row['is_lorentzian'] is None and row['metric_positive_definite'] is True
        assert len(fig.data[0].x)==60 and len(fig.data[0].y)==60

    @pytest.mark.parametrize('branch_ratio',[.5,2.])
    def test_actual_binder_refuses_boolean_lambda_metadata(self,branch_ratio):
        G=branch_ratio*critical_coupling(1.,4)
        result=full_mean_field_analysis(G,1.,4)
        result.params.Lambda=True
        with pytest.raises(ValueError):_phase_point_from_mean_field(result,branch_ratio,G,1.,4)

    @pytest.mark.parametrize('field',['C_tetrad','V_eff','G_metric'])
    def test_actual_binder_accepts_matching_numpy_real(self,field):
        G=2.*critical_coupling(1.,4);result=full_mean_field_analysis(G,1.,4)
        setattr(result,field,np.float64(getattr(result,field)))
        p=_phase_point_from_mean_field(result,2.,G,1.,4)
        assert p.scalar_enclosure is result.scalar_enclosure and p.phase=='full_tetrad'

    @pytest.mark.parametrize('value,expected',[(1.,1.),(np.float64(1.),1.),(np.float32(1.),1.),(1e-300,1e-300),(np.float64(1e-300),1e-300)])
    def test_admitted_typed_one_and_tiny_scalar_transport(self,value,expected):
        # Numeric display admission only; not a synthetic C=1 root claim.
        from src.vestigial.phase_diagram import _phase_transport_equal
        assert _phase_transport_equal(value,expected)
        assert not _phase_transport_equal(value,Q.from_float(expected))
        with pytest.raises(ValueError):_phase_transport_equal(True,expected)

    def test_strict_zero_unknown_boolean_protocols(self):
        from src.vestigial.phase_diagram import _phase_transport_equal
        assert _phase_transport_equal(Q(0),Q(0))
        assert _phase_transport_equal(None,None)
        assert _phase_transport_equal(True,True)
        for value in (False,0,0.):assert not _phase_transport_equal(value,Q(0))
        assert not _phase_transport_equal(1,True)
        assert not _phase_transport_equal(Q(0),None)

    def test_existing_decimal_codec_large_integer_without_limit_change(self):
        # Existing canonical encoder; no global conversion-limit mutation.
        import sys
        from src.core.formulas import _adw_decimal
        before=sys.get_int_max_str_digits()
        assert _adw_decimal(10**5000)=='1'+'0'*5000
        assert _adw_decimal(-(10**5000))=='-'+'1'+'0'*5000
        assert sys.get_int_max_str_digits()==before


class TestOriginalNotebookPopulationsAfterDistanceRepair:
    def test_complete_eighty_and_fifty_rows_preserve_last_endpoint(self):
        from src.adw.gap_equation import critical_coupling
        ratios=np.linspace(.3,2.5,80)
        results=[full_mean_field_analysis(G=float(r)*critical_coupling(1.,4),Lambda=1.,N_f=4) for r in ratios]
        assert len(results)==80 and ratios[-1]==2.5
        assert all(r.scalar_enclosure.max_bits==100000 and r.scalar_enclosure.max_work==200000 for r in results)
        data=scan_coupling(Lambda=1.,N_f=4,coupling_range=(.3,2.5),n_points=50)
        assert len(data.points)==50 and data.coupling_ratios[-1]==2.5
        assert list(data.coupling_ratios)==list(np.linspace(.3,2.5,50))
