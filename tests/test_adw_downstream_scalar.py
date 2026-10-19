"""UNRUN proposed downstream scalar tests; no physical/native acceptance.

Real numerical calls depend on the separately reviewed canonical prototype.
Transport spies do not replace these actual mathematical controls.
"""
from fractions import Fraction as Q
from dataclasses import replace
import math
import pytest
import numpy as np
import mpmath as mp
from src.core import formulas as f
from src.vestigial import mean_field as mf
from src.adw import ginzburg_landau as gl
from src.adw import hubbard_stratonovich as hs


def m(q):
    return mp.mpf(q.numerator)/q.denominator


class TestActualDownstreamScalar:
    @pytest.mark.parametrize('cutoff',[1.0,1e-12])
    def test_mean_field_has_no_amplitude_floor_or_cap(self,cutoff):
        # r is about12.16: actual root is aboveLambda even for tinyLambda.
        G=240.0/(cutoff*cutoff)
        direct=f.adw_scalar_minimum(G,cutoff,4)
        result=mf.full_mean_field_analysis(G,cutoff,4)
        assert result.C_tetrad>cutoff
        assert result.C_tetrad==direct.C
        assert result.phase=='full_tetrad'
        assert result.scalar_enclosure==direct
        assert result.V_eff==direct.V_eff
        assert result.physical_signature_status=='uncomputed'
        assert result.is_lorentzian is None
        assert result.metric_positive_definite is True
        q=Q.from_float(float(result.metric_eigenvalues[0]))
        assert max(abs(q-x) for x in result.scalar_metric_interval)==result.scalar_metric_error

    def test_nearcritical_meanfield_below_old_relative_floor(self):
        with mp.workdps(180):
            G=Q(int(mp.ceil((2*mp.pi**2)*10**40)),10**40)
        p=mf.MeanFieldParams(G=G,Lambda=1.0,N_f=4)
        result=mf.full_mean_field_analysis(G,1.0,4,rtol=1e-8)
        assert 0<result.C_tetrad<1e-6
        assert result.phase=='full_tetrad'
        assert mf._classify_phase(result.C_tetrad,p,scalar_enclosure=result.scalar_enclosure,rtol=1e-8)=='full_tetrad'
        assert result.scalar_enclosure.energy_interval[1]<0

    def test_all_three_meanfield_consumers_share_positive_branch_below_old_floor(self):
        cutoff=1e-12;p=mf.MeanFieldParams(240.0/cutoff**2,cutoff,4)
        cert=f.adw_scalar_minimum(p.G,p.Lambda,p.N_f)
        assert 0<cert.C<1e-10
        assert mf.mean_field_gap_equation(p,scalar_enclosure=cert)==cert.C
        metric=mf.mean_field_metric_correlator(p,scalar_enclosure=cert)
        total=mf._total_metric_correlator(p,scalar_enclosure=cert)
        assert metric>0 and total==pytest.approx(metric*p.L**p.d,rel=1e-14)
        assert mf._classify_phase(cert.C,p,scalar_enclosure=cert)=='full_tetrad'

    def test_full_meanfield_calls_actual_generator_once(self,monkeypatch):
        original=f.adw_scalar_minimum;calls=[]
        def observed(*a,**kw):
            calls.append((a,kw));return original(*a,**kw)
        monkeypatch.setattr(f,'adw_scalar_minimum',observed)
        result=mf.full_mean_field_analysis(40.0,1.0,4)
        assert len(calls)==1
        assert result.scalar_enclosure.inputs==(Q(40),Q(1),Q(4))

    def test_supplied_receipt_rejects_changed_parameters(self):
        p=mf.MeanFieldParams(G=40.0,Lambda=1.0,N_f=4)
        cert=f.adw_scalar_minimum(p.G,p.Lambda,p.N_f)
        p.G=80.0
        with pytest.raises(ValueError):mf.mean_field_gap_equation(p,scalar_enclosure=cert)

    def test_scalar_origin_and_adopted_curvature_model_remain_distinct(self):
        result=mf.full_mean_field_analysis(0.001,1.0,4)
        assert result.C_tetrad==result.V_eff==0
        assert result.scalar_enclosure.branch=='origin'
        assert result.phase=='pre_geometric'
        assert result.scalar_metric_interval is None  # no physical fluctuation certificate

    def test_unresolved_origin_fluctuation_is_not_an_abs_curvature_phase(self,monkeypatch):
        # Historical refusal is repaired: a poisoned legacy subtraction is unused.
        p=mf.MeanFieldParams(1.0,1.0,4);cert=f.adw_scalar_minimum(p.G,p.Lambda,p.N_f)
        assert cert.branch=='origin'
        monkeypatch.setattr(mf,'adw_curvature_at_origin',lambda *a:0.0)
        origin=mf._origin_receipt(p,cert)
        assert origin.curvature_interval[0]>0
        assert mf.mean_field_metric_correlator(p,scalar_enclosure=cert,origin_enclosure=origin)>0
        assert mf._classify_phase(0.0,p,scalar_enclosure=cert,origin_enclosure=origin)=='pre_geometric'
        assert cert.branch=='origin'  # physical proxy refusal did not alter scalar proof

    @pytest.mark.parametrize('n',[0,1,2,3,4,7])
    def test_GL_polynomial_minimum_matches_independent_complete_square(self,n):
        # F=n*(-8)*C²+n²*C⁴ has value-16 at C²=4/n.
        actual=gl._gl_minimized_free_energy(Q(-8),Q(1),n)
        if n==0:
            assert actual==0
        else:
            assert actual==-16
            assert gl._gl_free_energy(-8,1,math.sqrt(4/n),n)==pytest.approx(-16,rel=1e-14)
            if n>1:assert actual!=pytest.approx(-16/n)

    @pytest.mark.parametrize('alpha,beta,n,expected',[(2,1,4,0),(0,1,4,0),(2,0,4,0),(0,0,4,0),(-2,-1,0,0)])
    def test_GL_origin_flat_and_n0_domains(self,alpha,beta,n,expected):
        assert gl._gl_minimized_free_energy(alpha,beta,n)==expected

    @pytest.mark.parametrize('alpha,beta',[(-1,0),(-1,-1),(0,-1),(2,-1)])
    def test_GL_unbounded_is_not_zero_or_numerical_refusal(self,alpha,beta):
        with pytest.raises(gl.GLUnboundedBelow):gl._gl_minimized_free_energy(alpha,beta,3)

    @pytest.mark.parametrize('n',[-1,True,False,1.5,Q(3,2)])
    def test_GL_invalid_direction_count_refuses(self,n):
        with pytest.raises(ValueError):gl._gl_minimized_free_energy(-2,1,n)
        with pytest.raises(ValueError):gl._full_cw_free_energy(40,1,4,n)

    @pytest.mark.parametrize('name',['alpha','beta_eff'])
    @pytest.mark.parametrize('bad',[True,float('nan'),float('inf')])
    def test_nonfinite_or_boolean_GL_coefficient_refuses_even_at_n0(self,name,bad):
        values=dict(alpha=-2,beta_eff=1,n_condensed=0);values[name]=bad
        with pytest.raises(ValueError):gl._gl_minimized_free_energy(**values)

    @pytest.mark.parametrize('n',[2,3,4])
    def test_actual_full_scalar_energy_and_error_scale_with_positive_n(self,n):
        cert=f.adw_scalar_minimum(240.0,1.0,4)
        record=gl._full_cw_minimum(240.0,1.0,4,n,scalar_enclosure=cert)
        assert record.scalar_enclosure is cert
        assert record.energy_interval==(n*(cert.energy_interval[0]-cert.energy_gap_upper),n*cert.energy_interval[1])
        assert abs(Q.from_float(record.free_energy)-n*Q.from_float(cert.V_eff))<=record.energy_error
        assert record.free_energy<0

    def test_GL_supplied_receipt_cannot_change_the_problem(self):
        cert=f.adw_scalar_minimum(40.0,1.0,4)
        with pytest.raises(ValueError):gl._full_cw_minimum(80.0,1.0,4,3,scalar_enclosure=cert)

    def test_n0_does_not_invoke_scalar_generator(self,monkeypatch):
        def blocked(*a,**kw):raise AssertionError('n0 must be constantzero')
        monkeypatch.setattr(f,'adw_scalar_minimum',blocked)
        record=gl._full_cw_minimum(40,1,4,0)
        assert record.free_energy==0 and record.scalar_enclosure is None

    def test_tiny_negative_energy_branch_not_absolute_floor(self):
        cutoff=1e-6;G=40.0/cutoff**2
        phases=gl.classify_gl_phases(gl.compute_gl_coefficients(G,cutoff,4))
        ground=[p for p in phases if p.is_ground_state]
        assert len(ground)==1 and ground[0].phase_type==gl.GLPhaseType.B_PHASE
        assert -1e-15<ground[0].free_energy<0
        assert ground[0].scalar_enclosure.branch=='positive'
        assert ground[0].scalar_energy_interval[1]<0

    def test_actual_GL_classification_one_generation_and_shared_receipt(self,monkeypatch):
        original=f.adw_scalar_minimum;calls=[]
        def observed(*a,**kw):calls.append(a);return original(*a,**kw)
        monkeypatch.setattr(f,'adw_scalar_minimum',observed)
        phases=gl.classify_gl_phases(gl.compute_gl_coefficients(40,1,4))
        assert len(calls)==1
        cert=phases[0].scalar_enclosure
        assert all(p.scalar_enclosure is cert for p in phases)
        assert [p.free_energy for p in phases[:3]]==sorted(p.free_energy for p in phases[:3])

    def test_GL_sampled_diagram_retains_actual_receipts_and_nominal_boundary_scope(self):
        diagram=gl.compute_phase_diagram(1.0,4,n_points=3)
        assert len(diagram.scalar_enclosures)==3
        assert diagram.boundary_status.startswith('nominal_reference_only')
        assert diagram.sampled_transition_brackets
        for i,cert in enumerate(diagram.scalar_enclosures):
            assert cert.inputs[0]==Q.from_float(float(diagram.coupling_ratios[i]*gl.critical_coupling(1,4)))
            assert Q.from_float(float(diagram.free_energies_B[i]))<=0
            assert diagram.scalar_energy_errors[4][i]>=0

    def test_meanfield_window_preserves_each_certificate(self):
        result=mf.vestigial_phase_window(1.0,4,n_points=3)
        assert len(result['scalar_enclosures'])==len(result['coupling_ratios'])==3
        for C,snapshot in zip(result['C_tetrad'],result['scalar_enclosures']):
            assert C==snapshot['C']
        assert result['physical_phase_status'].startswith('uncomputed')

    def test_polynomial_value_is_not_its_unbounded_minimum(self):
        assert gl._gl_free_energy(0,-1,1,2)==-4
        with pytest.raises(gl.GLUnboundedBelow):gl._gl_minimized_free_energy(0,-1,2)

    @pytest.mark.parametrize('C',[0.0,1e-16,0.5])
    def test_HS_continuous_scalar_split_has_independent_value_backing(self,C):
        result=hs.fermion_effective_action(hs.TetradField.flat_spacetime(C),4,1.0,40.0)
        if C==0:
            assert result['V_tree']==result['V_1loop']==result['V_eff']==0
            return
        assert result['V_1loop']<0  # no old absolute near-origin loop guard
        c=Q.from_float(result['C'])
        with mp.workdps(180):
            exact=m(c)**2/80-4/(16*mp.pi**2)*(m(c)**2-m(c)**4*mp.log1p(1/m(c)**2))
            lo,hi=result['value_intervals']['V_eff']
            assert m(lo)<=exact<=m(hi)
            assert abs(mp.mpf(result['V_eff'])-exact)<=m(result['rounding_errors']['V_eff'])
        assert result['split_discrepancy']<=result['split_discrepancy_bound']

    def test_HS_cancellation_does_not_reconstruct_total_from_rounded_columns(self):
        result=hs.fermion_effective_action(hs.TetradField.flat_spacetime(1e-10),4,1.0,float(2*np.pi**2))
        c=Q.from_float(result['C']);G=Q.from_float(result['G'])
        with mp.workdps(180):
            expected=m(c)**2/(2*m(G))-4/(16*mp.pi**2)*(m(c)**2-m(c)**4*mp.log1p(1/m(c)**2))
            assert abs(mp.mpf(result['V_eff'])-expected)<=m(result['rounding_errors']['V_eff'])
        assert result['V_eff']!=0
        assert result['split_discrepancy']<=result['split_discrepancy_bound']

    def test_HS_singular_nonzero_is_actual_scalar_zero(self):
        e=hs.TetradField(np.diag([1.0,1.0,1.0,0.0]))
        result=hs.fermion_effective_action(e,4,1.0,40.0)
        assert result['matrix_determinant_exact']==0
        assert result['C']==result['V_eff']==0

    def test_HS_exact_determinant_permutation_sign_is_real(self):
        e=hs.TetradField(np.array([[0.,3.,0.,0.],[2.,0.,0.,0.],[0.,0.,4.,0.],[0.,0.,0.,5.]]))
        result=hs.fermion_effective_action(e,4,1.0,40.0)
        assert result['matrix_determinant_exact']==-120
        assert result['C']>0

    @pytest.mark.parametrize('name,bad',[('G',0),('G',True),('Lambda',0),('N_f',float('inf'))])
    def test_HS_invalid_parameters_are_not_tree_or_loop_zero(self,name,bad):
        values=dict(N_f=4,Lambda=1.0,G=40.0);values[name]=bad
        with pytest.raises(ValueError):hs.fermion_effective_action(hs.TetradField.zero(),**values)

    def test_HS_nonsingular_determinant_collapse_refuses_not_origin(self):
        with pytest.raises(f.ADWScalarUnresolved):
            hs.fermion_effective_action(hs.TetradField.flat_spacetime(1e-100),4,1.0,40.0)

    @pytest.mark.parametrize('route',['meanfield','GL','HS'])
    def test_actual_failures_propagate_without_zero_fallback(self,monkeypatch,route):
        expected=f.ADWScalarUnresolved('controlled resource refusal')
        def raises(*a,**kw):raise expected
        if route=='HS':
            monkeypatch.setattr(f,'_adw_pi_bounds',raises)
            call=lambda:hs.fermion_effective_action(hs.TetradField.flat_spacetime(.5),4,1,40)
        elif route=='GL':
            monkeypatch.setattr(f,'adw_scalar_minimum',raises)
            call=lambda:gl._full_cw_free_energy(40,1,4,4)
        else:
            monkeypatch.setattr(f,'adw_scalar_minimum',raises)
            call=lambda:mf.mean_field_gap_equation(mf.MeanFieldParams(40,1,4))
        with pytest.raises(f.ADWScalarUnresolved) as caught:call()
        assert caught.value is expected
