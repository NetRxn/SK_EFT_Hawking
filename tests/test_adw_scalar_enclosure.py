"""UNRUN proposed independent-reference tests of actual canonical entrypoints.

High-precision positive-kernel integration/reference refinement is an oracle,
not the production series copied as expected output. Reference precision and
budgets are engineering proposals requiring actual isolated runtime review.
"""
import json
from dataclasses import FrozenInstanceError, replace
from fractions import Fraction
import math
import pytest
import mpmath as mp

from src.core import formulas as f
from src.adw import gap_equation as ge


def mq(value):
    return mp.mpf(value.numerator)/value.denominator


def independent_j(z):
    """O(1) positive-kernel integral, including large-z scaling."""
    z = mq(z) if isinstance(z, Fraction) else mp.mpf(z)
    if z >= 1:
        return mp.quad(lambda t: t*t/(1+t/z)**2, [0, 1])/(z*z)
    # Independently integrate the positive deficit 1-J, normalized before scaling.
    # t=z*exp(u) resolves the tiny-z boundary layer; no production series or
    # analytic logarithmic closed form is used as an oracle.
    kernel=lambda u: mp.exp(u)*(1+2*mp.exp(u))/(1+mp.exp(u))**2
    deficit=z*mp.quad(kernel,[-mp.inf,0,mp.log(1/z)])
    return 1-deficit


def independent_root(r):
    """Independent high-precision integral bisection, not production J/solver."""
    left, right = mp.mpf(0), mp.mpf(1)
    while independent_j(right) > 1/r:
        right *= 2
    for _ in range(700):
        middle = (left+right)/2
        if independent_j(middle) > 1/r:
            left = middle
        else:
            right = middle
    return (left+right)/2


def independent_value(c, G, cutoff, species):
    return c*c/(2*G)-species/(16*mp.pi**2)*(cutoff**2*c*c-c**4*mp.log1p(cutoff**2/c**2))


class TestActualADWEnclosures:
    @pytest.mark.parametrize("z", [Fraction(1, 10**80), Fraction(1, 8), Fraction(1), Fraction(2), Fraction(10**80)])
    def test_actual_kernel_interval_contains_independent_positive_integral(self, z):
        # r=1 gives f=1-J. Reference refinement must agree before use.
        terms = 1 if z >= 10**40 else 80
        flo, fhi = f.adw_scalar_residual_enclosure(z, Fraction(1), terms=terms)
        with mp.workdps(220):
            first = independent_j(z)
        with mp.workdps(300):
            second = independent_j(z)
            assert abs(first-second) <= mp.mpf('1e-200')*abs(second)
            assert mq(1-fhi) <= second <= mq(1-flo)
            assert 0 < second < 1

    def test_midpoint_zero_containing_enclosure_uses_distance_not_guessed_sign(self):
        # Choose exact rational r making the *finite* J enclosure centered on1/r
        # at initial midpoint z=2. This does not assert the exact J is rational.
        flo, fhi = f.adw_scalar_residual_enclosure(Fraction(2), Fraction(1), terms=4)
        jlo, jhi = 1-fhi, 1-flo
        r = 2/(jlo+jhi)
        result = f.adw_scalar_minimum_ratio(r)
        assert any(step[-1] == 'distance' for step in result.trace)
        with mp.workdps(180):
            root = independent_root(mq(r))
            assert mq(result.z_interval[0]) <= root <= mq(result.z_interval[1])

    @pytest.mark.parametrize("r", [Fraction(1, 2), Fraction(1)])
    def test_exact_ratio_subcritical_and_critical_origin(self, r):
        result = f.adw_scalar_minimum_ratio(r)
        assert result.branch == 'origin'
        assert result.C == result.V_eff == 0
        assert result.r_interval == (r, r)
        assert result.model == 'exact-ratio'

    def test_strong_coupling_unrestricted_root_not_old_cutoff(self):
        result = f.adw_scalar_minimum_ratio(Fraction(12))
        assert result.branch == 'positive'
        # Independent exact positive-integral bracket: 1<z*(12)<2.
        assert result.z_interval[0] > 1
        assert result.z_interval[1] < 2
        assert result.C > 1
        assert f.adw_validate_scalar_enclosure_ratio(result,Fraction(12)) is result
        with pytest.raises(ValueError):
            f.adw_validate_scalar_enclosure(result,Fraction(12),1,4)
        with mp.workdps(180):
            root = independent_root(mp.mpf(12))
            assert mq(result.z_interval[0]) <= root <= mq(result.z_interval[1])
            assert abs(mp.mpf(result.C)-mp.sqrt(root)) <= mq(result.returned_magnitude_error)

    def test_actual_supplied_parameters_true_pi_not_nominal_G_over_Gc(self):
        G = ge.critical_coupling(1.0, 4)
        result = f.adw_scalar_minimum(G, 1.0, 4)
        assert result.model == 'supplied-parameters-exact-pi'
        assert result.inputs[0] == Fraction.from_float(float(G))
        with mp.workdps(180):
            exact_ratio = mq(result.inputs[0])*4/(8*mp.pi**2)
            assert mq(result.r_interval[0]) <= exact_ratio <= mq(result.r_interval[1])
            assert result.branch == ('positive' if exact_ratio > 1 else 'origin')
        exact_one = f.adw_scalar_minimum_ratio(Fraction(1))
        assert exact_one.branch == 'origin'  # a distinct target, no float equality premise

    def test_nearcritical_minimum_below_old_search_floor(self):
        with mp.workdps(180):
            scale = 10**40
            G = Fraction(int(mp.ceil((8*mp.pi**2/4)*scale)), scale)
        result = f.adw_scalar_minimum(G, Fraction(1), Fraction(4), rtol=1e-8)
        assert result.branch == 'positive'
        assert 0 < result.C < 1e-6
        assert result.energy_interval[1] < 0
        f.adw_validate_scalar_enclosure(result, G, 1, 4, rtol=1e-8)
        with mp.workdps(220):
            r = mq(G)*4/(8*mp.pi**2)
            z = independent_root(r)
            assert mq(result.z_interval[0]) <= z <= mq(result.z_interval[1])

    @pytest.mark.parametrize("cutoff", [Fraction(1, 10**20), Fraction(1), Fraction(10**20)])
    def test_scaling_even_potential_odd_derivative_and_energy(self, cutoff):
        # Preserve same *exact supplied* dimensionless ratio by scaling G exactly.
        G = Fraction(160)/(cutoff*cutoff)
        result = f.adw_scalar_minimum(G, cutoff, Fraction(3, 2))
        f.adw_validate_scalar_enclosure(result, G, cutoff, Fraction(3, 2))
        c = Fraction(3, 10)*cutoff
        vp = f.adw_effective_potential(c, G, cutoff, Fraction(3, 2))
        vm = f.adw_effective_potential(-c, G, cutoff, Fraction(3, 2))
        dp = f.adw_effective_potential_derivative(c, G, cutoff, Fraction(3, 2))
        dm = f.adw_effective_potential_derivative(-c, G, cutoff, Fraction(3, 2))
        assert vp == vm and dp == -dm
        assert vp != 0  # no old absolute C guard, even at tiny cutoff
        with mp.workdps(180):
            expected = independent_value(mq(c), mq(G), mq(cutoff), mp.mpf('1.5'))
            assert abs(mp.mpf(vp)-expected) <= abs(expected)*mp.mpf(2)**-39
            z = independent_root(mq(G)*mp.mpf('1.5')*mq(cutoff)**2/(8*mp.pi**2))
            cstar = mq(cutoff)*mp.sqrt(z)
            optimum = independent_value(cstar, mq(G), mq(cutoff), mp.mpf('1.5'))
            at_returned = independent_value(mp.mpf(result.C), mq(G), mq(cutoff), mp.mpf('1.5'))
            assert mq(result.energy_interval[0]) <= at_returned <= mq(result.energy_interval[1])
            assert 0 <= at_returned-optimum <= mq(result.energy_gap_upper)
            assert abs(mp.mpf(result.V_eff)-optimum) <= mq(result.energy_rounding_error+result.energy_gap_upper)

    def test_closed_cutoff_trichotomy_is_not_unrestricted_cap(self):
        # Independent positive integral at z=1 defines the crossing.
        with mp.workdps(180):
            crossing = 1/independent_j(Fraction(1))
            below = Fraction(int(mp.floor(crossing*10**12)), 10**12)
            above = Fraction(int(mp.ceil(crossing*10**12)), 10**12)
        low = f.adw_scalar_minimum_ratio(below, rtol=1e-15, energy_rtol=1e-12)
        high = f.adw_scalar_minimum_ratio(above, rtol=1e-15, energy_rtol=1e-12)
        assert low.z_interval[1] < 1 < high.z_interval[0]
        # Equality at exact irrational crossing is a mathematical endpoint;
        # no rational approximation is called exact equality here.
        assert f.adw_scalar_residual_enclosure(Fraction(1), below, terms=80)[0] > 0
        assert f.adw_scalar_residual_enclosure(Fraction(1), above, terms=80)[1] < 0

    def test_actual_wrapper_preserves_selected_identity_and_receipt(self):
        result = ge.full_gap_analysis(240.0, 1.0, 4)
        assert result.scalar_status == 'certified_scalar_minimum'
        assert result.global_minimum is result.nontrivial_solution
        assert result.nontrivial_solution.C > 1
        assert result.nontrivial_solution.C == result.scalar_enclosure.C
        assert result.search_diagnostics['certificate'] == result.scalar_enclosure.as_dict()
        assert result.phase is result.nontrivial_solution.phase
        assert result.search_diagnostics['globality'] == 'unrestricted_scalar_ansatz'


class TestCertificateRefusalAndTransport:
    @pytest.fixture
    def actual(self):
        return f.adw_scalar_minimum(40.0, 1.0, 4)

    def test_actual_serialized_roundtrip_semantic_replay(self, actual):
        record = json.loads(json.dumps(actual.as_dict(), allow_nan=False))
        parsed = f.adw_scalar_enclosure_from_dict(record)
        assert parsed == actual
        assert f.adw_validate_scalar_enclosure(parsed, 40.0, 1.0, 4) is parsed
        with pytest.raises(FrozenInstanceError):
            actual.C = 0.0

    @pytest.mark.parametrize('kind', ['initial', 'trace', 'pi', 'ratio', 'magnitude', 'energy',
        'energy_gap', 'rounding', 'tolerance', 'missing_input', 'different_model', 'bool_C'])
    def test_real_semantic_verifier_rejects_corruption(self, actual, kind):
        if kind == 'initial':
            corrupt = replace(actual, initial_z_interval=(Fraction(0), Fraction(1, 100)))
        elif kind == 'trace':
            rows = list(actual.trace); row = list(rows[0]); row[4] += 1; rows[0] = tuple(row)
            corrupt = replace(actual, trace=tuple(rows))
        elif kind == 'pi':
            corrupt = replace(actual, pi_interval=(Fraction(3), Fraction(3)))
        elif kind == 'ratio':
            corrupt = replace(actual, r_interval=(Fraction(2), Fraction(2)))
        elif kind == 'magnitude':
            corrupt = replace(actual, magnitude_interval=(Fraction(0), Fraction(0)))
        elif kind == 'energy':
            corrupt = replace(actual, energy_interval=(Fraction(0), Fraction(0)))
        elif kind == 'energy_gap':
            corrupt = replace(actual, energy_gap_upper=Fraction(0))
        elif kind == 'rounding':
            corrupt = replace(actual, returned_magnitude_error=Fraction(0))
        elif kind == 'tolerance':
            corrupt = replace(actual, requested_rtol=Fraction(0))
        elif kind == 'missing_input':
            corrupt = replace(actual, inputs=actual.inputs[:2])
        elif kind == 'different_model':
            corrupt = replace(actual, model='exact-ratio')
        else:
            corrupt = replace(actual, C=True)
        with pytest.raises(ValueError):
            f.adw_validate_scalar_enclosure(corrupt, 40.0, 1.0, 4)

    @pytest.mark.parametrize('kind', ['top_duplicate', 'nested_duplicate', 'nonfinite', 'oversize'])
    def test_actual_text_boundary_refuses_before_dict_loses_evidence(self, actual, kind):
        text = json.dumps(actual.as_dict(), allow_nan=False)
        if kind == 'top_duplicate':
            text = '{"model":"forged",'+text[1:]
        elif kind == 'nested_duplicate':
            text = text.replace('"numerator":', '"numerator":"0","numerator":', 1)
        elif kind == 'nonfinite':
            text = text.replace('"C":', '"C":NaN,"ignored":', 1)
        else:
            with pytest.raises(ValueError):
                f.adw_scalar_enclosure_from_json(text, max_text_bytes=10)
            return
        with pytest.raises(ValueError):
            f.adw_scalar_enclosure_from_json(text)

    @pytest.mark.parametrize('kind', ['work', 'bits', 'accuracy'])
    def test_external_policy_precedes_any_expensive_replay(self, actual, monkeypatch, kind):
        def forbidden(*args, **kwargs):
            raise AssertionError('expensive replay reached before external policy refusal')
        monkeypatch.setattr(f, '_adw_pi_bounds', forbidden)
        if kind == 'work':
            corrupt = replace(actual, max_work=200001)
        elif kind == 'bits':
            corrupt = replace(actual, max_bits=100001)
        else:
            corrupt = replace(actual, requested_rtol=Fraction(1,100))
        with pytest.raises(ValueError):
            f.adw_validate_scalar_enclosure(corrupt,40.0,1.0,4,
                atol=0,rtol=1e-10,energy_atol=0,energy_rtol=1e-8,
                max_work=200000,max_bits=100000)

    @pytest.mark.parametrize('kind', ['missing', 'extra', 'unreduced', 'signedzero', 'boolbudget', 'budgetraise', 'hugeinteger'])
    def test_untrusted_json_parser_refuses(self, actual, kind):
        record = actual.as_dict()
        if kind == 'missing':
            record.pop('trace')
        elif kind == 'extra':
            record['verified'] = True
        elif kind == 'unreduced':
            record['inputs'][0] = {'numerator':'80','denominator':'2'}
        elif kind == 'signedzero':
            record['requested_atol'] = {'numerator':'-0','denominator':'1'}
        elif kind == 'boolbudget':
            record['max_work'] = True
        elif kind == 'budgetraise':
            record['max_work'] = 200001
        else:
            record['inputs'][0]['numerator'] = '9'*100001
        with pytest.raises((ValueError, f.ADWScalarUnresolved)):
            f.adw_scalar_enclosure_from_dict(record)

    @pytest.mark.parametrize('name', ['G', 'Lambda', 'N_f'])
    @pytest.mark.parametrize('bad', [True, False, 0, -1, float('nan'), float('inf'), 1j, [], [1]])
    def test_actual_scalar_domain(self, name, bad):
        values = dict(G=40, Lambda=1, N_f=4); values[name] = bad
        with pytest.raises(ValueError):
            f.adw_scalar_minimum(**values)

    @pytest.mark.parametrize('options', [dict(rtol=True), dict(atol=False),
        dict(rtol=-1), dict(rtol=float('inf')), dict(atol=0,rtol=0),
        dict(energy_atol=0,energy_rtol=0), dict(max_work=True), dict(max_bits=0)])
    def test_malformed_requested_accuracy_or_budget_refuses(self, options):
        with pytest.raises(ValueError):
            f.adw_scalar_minimum(40,1,4,**options)

    @pytest.mark.parametrize('options', [dict(max_work=1), dict(max_bits=8),
        dict(rtol=Fraction(1,10**100), energy_rtol=Fraction(1,10**100), max_work=2000)])
    def test_finite_work_or_unattainable_accuracy_refuses_not_midpoint(self, options):
        with pytest.raises(f.ADWScalarUnresolved):
            f.adw_scalar_minimum(40, 1, 4, **options)

    def test_true_pi_threshold_uncertainty_exhaustion_not_zero(self):
        with mp.workdps(180):
            G = Fraction(int(mp.ceil((8*mp.pi**2/4)*10**100)), 10**100)
        with pytest.raises(f.ADWScalarUnresolved):
            f.adw_scalar_minimum(G, 1, 4, max_work=100)

    @pytest.mark.parametrize('cutoff', [Fraction(1,10**320), Fraction(10**200)])
    def test_valid_input_unrepresentable_returned_energy_or_magnitude_refuses(self, cutoff):
        # Ratio remains finite, but requested binary64 output need not exist.
        G = Fraction(40)/(cutoff*cutoff)
        with pytest.raises(f.ADWScalarUnresolved):
            f.adw_scalar_minimum(G, cutoff, 4)

    @pytest.mark.parametrize('route', ['wrapper', 'producer'])
    @pytest.mark.parametrize('kind', ['work', 'bits', 'accuracy'])
    def test_real_memory_routes_reject_untrusted_policy_before_replay(self, monkeypatch, route, kind):
        # Obtain an actual matching receipt BEFORE placing the replay sentinel.
        G = 40.0 if route == 'wrapper' else float(0.1*ge.critical_coupling(1.0,4))
        result = ge.full_gap_analysis(G,1.0,4)
        actual = result.scalar_enclosure
        corrupt = (replace(actual,max_work=200001) if kind == 'work' else
                   replace(actual,max_bits=100001) if kind == 'bits' else
                   replace(actual,requested_rtol=Fraction(1,100)))
        def forbidden(*args, **kwargs):
            raise AssertionError('untrusted policy reached expensive replay')
        if route == 'wrapper':
            monkeypatch.setattr(ge,'_canonical_scalar_minimum',lambda *a,**kw:corrupt)
            monkeypatch.setattr(f,'_adw_pi_bounds',forbidden)
            with pytest.raises(ValueError):
                ge.full_gap_analysis(G,1.0,4)
        else:
            import src.core.visualizations as viz
            # Synchronize the receipt snapshot; it cannot authorize its policy.
            result.scalar_enclosure = corrupt
            result.search_diagnostics['certificate'] = corrupt.as_dict()
            monkeypatch.setattr(ge,'full_gap_analysis',lambda *a,**kw:result)
            monkeypatch.setattr(f,'adw_validate_scalar_enclosure',forbidden)
            with pytest.raises(ValueError,match='altered accuracy/resource'):
                viz.fig_adw_phase_diagram()

    def test_verifier_has_own_meter_not_generation_counter(self, actual):
        # The telemetry is plausible in range but cannot grant replay work.
        corrupt = replace(actual,max_work=1,work_used=1)
        with pytest.raises(f.ADWScalarUnresolved):
            f.adw_validate_scalar_enclosure(corrupt,40.0,1.0,4,max_work=1)

    def test_fraction_inputs_never_silently_collapse(self):
        assert f._adw_exact(Fraction(1,10**400), 'x', positive=True) == Fraction(1,10**400)
        with pytest.raises(ValueError):
            f._adw_exact(Fraction(-1,10**400), 'x', positive=True)
        assert f._adw_exact(-0.0, 'C') == 0
        smallest = float.fromhex('0x0.0000000000001p-1022')
        assert f._adw_exact(smallest, 'x', positive=True) == Fraction(1,2**1074)


class TestFig29ProducerM1Transport:
    """UNRUN actual wrapper/producer transport, NOT numerical proof.

    Only the canonical generation and semantic replay seams are controlled.
    The real wrapper creates its real solution objects, phases, identity,
    diagnostics and success flags, then the real unchanged-grid producer reads
    them. Synthetic receipts here never establish scalar correctness; the
    original independent integral/replay tests above remain unmodified.
    """

    @staticmethod
    def install(monkeypatch, positive_C=0.25, poison=None, target='positive'):
        import src.core.visualizations as viz
        audit = dict(results=[], mutated=[], wrapper_replays=[], producer_replays=[])
        original = ge.full_gap_analysis

        def controlled(G, Lambda, N_f, **policy):
            # This diagnostic split is a fixture choice ONLY; production true-pi
            # classification and all real numerical controls remain separate.
            origin = G/ge.critical_coupling(Lambda,N_f) <= 1
            C, energy = (0.0,0.0) if origin else (positive_C,-1.0)
            qC, qE = Fraction.from_float(C), Fraction.from_float(energy)
            z = qC*qC
            zero = Fraction(0)
            return f.ADWScalarEnclosure(
                model='supplied-parameters-exact-pi', branch='origin' if origin else 'positive',
                inputs=tuple(f._adw_exact(v,n,positive=True) for v,n in
                    ((G,'G'),(Lambda,'Lambda'),(N_f,'N_f'))),
                pi_interval=(Fraction(3),Fraction(4)),
                r_interval=(Fraction(1,2),Fraction(1,2)) if origin else (Fraction(2),Fraction(2)),
                z_interval=(z,z), initial_z_interval=(zero,zero) if origin else (zero,Fraction(2)),
                trace=(), magnitude_interval=(qC,qC), C=C, returned_magnitude_error=zero,
                requested_atol=f._adw_exact(policy['atol'],'atol'),
                requested_rtol=f._adw_exact(policy['rtol'],'rtol'),
                requested_energy_atol=f._adw_exact(policy['energy_atol'],'energy_atol'),
                requested_energy_rtol=f._adw_exact(policy['energy_rtol'],'energy_rtol'),
                residual_interval=(zero,zero), energy_interval=(qE,qE), V_eff=energy,
                energy_rounding_error=zero, energy_gap_upper=zero,
                work_used=1, terms=4, max_work=policy['max_work'], max_bits=policy['max_bits'])

        def wrapper_replay(cert,*args,**kwargs):
            audit['wrapper_replays'].append(cert)
            return cert

        def producer_replay(cert,*args,**kwargs):
            audit['producer_replays'].append(cert)
            return cert

        def actual_result(**kwargs):
            result = original(**kwargs)
            audit['results'].append(result)
            if poison is not None and result.scalar_enclosure.branch == target and not audit['mutated']:
                poison(result)
                audit['mutated'].append(len(audit['results'])-1)
            return result

        monkeypatch.setattr(ge,'_canonical_scalar_minimum',controlled)
        monkeypatch.setattr(ge,'_canonical_validate_enclosure',wrapper_replay)
        monkeypatch.setattr(f,'adw_validate_scalar_enclosure',producer_replay)
        monkeypatch.setattr(ge,'full_gap_analysis',actual_result)
        return viz, audit

    @classmethod
    def refuses(cls, monkeypatch, poison, *, target='positive', positive_C=0.25):
        viz, audit = cls.install(monkeypatch,positive_C,poison,target)
        with pytest.raises(ValueError,match=r'Fig29 row \d+'):
            viz.fig_adw_phase_diagram()
        assert len(audit['mutated']) == 1
        assert audit['mutated'][0] == len(audit['results'])-1
        assert len(audit['results']) < 100  # no partial figure returned
        assert len(audit['wrapper_replays']) == len(audit['producer_replays']) == len(audit['results'])

    @pytest.mark.parametrize('positive_C', [0.25,1.0,1e-12])
    def test_complete_real_wrapper_producer_origin_positive_and_tiny_signature_false(self, monkeypatch,positive_C):
        viz, audit = self.install(monkeypatch,positive_C)
        data = viz.fig_adw_phase_diagram().to_dict()
        rows = data['layout']['meta']['paper5_scalar_scan']['rows']
        assert len(rows) == len(audit['results']) == 100
        assert len(audit['wrapper_replays']) == len(audit['producer_replays']) == 100
        origin = [r for r in audit['results'] if r.scalar_status == 'certified_origin']
        positive = [r for r in audit['results'] if r.scalar_status == 'certified_scalar_minimum']
        assert origin and positive
        for result in origin:
            assert result.global_minimum is result.trivial_solution
            assert result.trivial_solution.C == result.trivial_solution.V_eff == 0.0
            assert result.success_criteria == dict(nontrivial_exists=False,lorentzian_signature=False,
                is_global_minimum=True,coupling_above_critical=False)
        for result in positive:
            assert result.global_minimum is result.nontrivial_solution
            assert result.trivial_solution is not result.global_minimum
            assert result.trivial_solution.is_minimum is False
            assert result.trivial_solution.C == result.trivial_solution.V_eff == 0.0
            assert result.trivial_solution.phase is ge.PhaseType.PRE_GEOMETRIC
            assert result.nontrivial_solution.C == positive_C
            signature = positive_C != 1e-12
            assert bool(result.nontrivial_solution.is_lorentzian) is signature
            assert result.success_criteria == dict(nontrivial_exists=True,lorentzian_signature=signature,
                is_global_minimum=True,coupling_above_critical=True)
        assert [row['C'] for row in rows] == list(data['data'][0]['y'])
        assert any(row['status'] == 'certified_scalar_minimum' and row['C'] == positive_C for row in rows)

    @pytest.mark.parametrize('target',['origin','positive'])
    @pytest.mark.parametrize('key', ['search_attempted','bounds','candidate_cutoff','optimizer_success',
        'optimizer_status','optimizer_message','C','V_eff','C_validity','V_eff_validity',
        'candidate_window','selected','stationarity','globality','certificate'])
    def test_each_required_diagnostic_missing_including_none_fields(self,monkeypatch,target,key):
        self.refuses(monkeypatch,lambda result: result.search_diagnostics.pop(key),target=target)

    @pytest.mark.parametrize('target',['origin','positive'])
    @pytest.mark.parametrize('kind',['absent','none','list','bool'])
    def test_success_dictionary_itself_required(self,monkeypatch,target,kind):
        def poison(result):
            if kind == 'absent':
                del result.success_criteria
            else:
                result.success_criteria = {'none':None,'list':[],'bool':True}[kind]
        self.refuses(monkeypatch,poison,target=target)

    @pytest.mark.parametrize('target',['origin','positive'])
    @pytest.mark.parametrize('key',['nontrivial_exists','lorentzian_signature','is_global_minimum','coupling_above_critical'])
    def test_each_success_key_required(self,monkeypatch,target,key):
        self.refuses(monkeypatch,lambda result: result.success_criteria.pop(key),target=target)

    @pytest.mark.parametrize('target',['origin','positive'])
    @pytest.mark.parametrize('key',['nontrivial_exists','lorentzian_signature','is_global_minimum','coupling_above_critical'])
    def test_each_success_boolean_semantics(self,monkeypatch,target,key):
        def poison(result):
            result.success_criteria[key] = not result.success_criteria[key]
        self.refuses(monkeypatch,poison,target=target)

    @pytest.mark.parametrize('target',['origin','positive'])
    @pytest.mark.parametrize('key',['nontrivial_exists','lorentzian_signature','is_global_minimum','coupling_above_critical'])
    @pytest.mark.parametrize('bad',[0,1,'True',None])
    def test_each_success_value_requires_actual_bool(self,monkeypatch,target,key,bad):
        def poison(result):
            result.success_criteria[key] = bad
        self.refuses(monkeypatch,poison,target=target)

    @pytest.mark.parametrize('kind',['C_nonzero','C_bool','C_nan','V_nonzero','V_bool','V_nan',
        'phase','minimum_true','minimum_int_zero','minimum_none','alias','absent'])
    def test_positive_unused_trivial_is_zero_distinct_and_unselected(self,monkeypatch,kind):
        def poison(result):
            trivial = result.trivial_solution
            if kind == 'alias': result.trivial_solution = result.nontrivial_solution
            elif kind == 'absent': result.trivial_solution = None
            elif kind == 'phase': trivial.phase = ge.PhaseType.FULL_TETRAD
            elif kind == 'minimum_true': trivial.is_minimum = True
            elif kind == 'minimum_int_zero': trivial.is_minimum = 0
            elif kind == 'minimum_none': trivial.is_minimum = None
            elif kind.startswith('C_'): trivial.C = {'C_nonzero':0.1,'C_bool':False,'C_nan':float('nan')}[kind]
            else: trivial.V_eff = {'V_nonzero':0.1,'V_bool':False,'V_nan':float('nan')}[kind]
        self.refuses(monkeypatch,poison)

    @pytest.mark.parametrize('key',['C','V_eff'])
    @pytest.mark.parametrize('bad',[True,False,float('nan'),float('inf')])
    def test_positive_diagnostics_finite_and_nonboolean_even_at_C_one(self,monkeypatch,key,bad):
        def poison(result): result.search_diagnostics[key] = bad
        # Genuine typed C=1.0 is allowed; True must not compare as its mirror.
        self.refuses(monkeypatch,poison,positive_C=1.0)

    @pytest.mark.parametrize('target',['origin','positive'])
    @pytest.mark.parametrize('kind',['work_float','bits_float','used_float','terms_float',
        'C_int','V_int','inputs_tuple','trace_tuple','missing','extra','fraction_numerator_int'])
    def test_actual_dict_snapshot_mirror_preserves_types_and_shape(self,monkeypatch,target,kind):
        def poison(result):
            snapshot = result.search_diagnostics['certificate']
            names = {'work_float':'max_work','bits_float':'max_bits','used_float':'work_used','terms_float':'terms'}
            if kind in names: snapshot[names[kind]] = float(snapshot[names[kind]])
            elif kind == 'C_int': snapshot['C'] = int(snapshot['C'])
            elif kind == 'V_int': snapshot['V_eff'] = int(snapshot['V_eff'])
            elif kind == 'inputs_tuple': snapshot['inputs'] = tuple(snapshot['inputs'])
            elif kind == 'trace_tuple': snapshot['trace'] = tuple(snapshot['trace'])
            elif kind == 'missing': snapshot.pop('trace')
            elif kind == 'extra': snapshot['verified'] = True
            else: snapshot['inputs'][0]['numerator'] = int(snapshot['inputs'][0]['numerator'])
        self.refuses(monkeypatch,poison,target=target,positive_C=1.0)

    def test_tiny_positive_false_legacy_signature_cannot_be_flipped_true(self,monkeypatch):
        def poison(result): result.success_criteria['lorentzian_signature'] = True
        self.refuses(monkeypatch,poison,positive_C=1e-12)


class TestActualTinyScalarLegacyMetadata:
    def test_real_numeric_tiny_positive_is_valid_despite_false_legacy_signature(self):
        # Real canonical generation/replay, no mocked semantic verifier. This
        # checks scaled positive numerical output, not a physical signature.
        cutoff = Fraction(1,10**12)
        G = Fraction(40)/(cutoff*cutoff)
        result = ge.full_gap_analysis(G,cutoff,4)
        assert result.scalar_enclosure.branch == 'positive'
        assert 0 < result.nontrivial_solution.C < float(cutoff)
        assert result.nontrivial_solution.is_lorentzian is False
        assert result.success_criteria['lorentzian_signature'] is False
        assert result.success_criteria['is_global_minimum'] is True
        assert f.adw_validate_scalar_enclosure(result.scalar_enclosure,G,cutoff,4) is result.scalar_enclosure


class TestActualDyadicDistanceRepair:
    @pytest.mark.parametrize("a,b,distance",[
        (Fraction(0),Fraction(1),Fraction(1,16)),
        (Fraction(0),Fraction(1),Fraction(1,4)-Fraction(1,10**30)),
        (Fraction(1,3),Fraction(10,7),Fraction(1,21)),
        (Fraction(10**20),Fraction(10**20+1),Fraction(1,11)),
        (Fraction(1,10**40),Fraction(2,10**40),Fraction(1,10**42)),
    ])
    def test_exact_outward_enclosure_and_strict_progress(self,a,b,distance):
        u=(a+b)/2;lo,hi=f._adw_distance_bracket(a,b,u,distance,f._ADWWork(200000,100000))
        assert a<=lo<=u-distance<=u+distance<=hi<=b
        assert hi-lo<5*(b-a)/8
        # Independent floor/ceil characterization, no replicated helper formula.
        mesh=Fraction(1,16*(b-a).denominator)
        assert u-distance-lo<mesh and hi-(u+distance)<mesh
        assert lo.denominator<=16*(b-a).denominator
        assert hi.denominator<=16*(b-a).denominator

    @pytest.mark.parametrize("bad",[False,0,0.,Fraction(0),Fraction(-1),Fraction(1,4)])
    def test_invalid_or_noncontracting_distance_is_refused(self,bad):
        with pytest.raises(ValueError):
            f._adw_distance_bracket(Fraction(0),Fraction(1),Fraction(1,2),bad,f._ADWWork(200000,100000))

    @pytest.mark.parametrize("kind",["incoming","grid","product","work"])
    def test_external_size_and_work_admission_is_not_relaxed(self,kind):
        a,b,u,d=Fraction(0),Fraction(1),Fraction(1,2),Fraction(1,8)
        work=f._ADWWork(200000,64)
        if kind=="incoming":d=Fraction(1,2**1000)
        if kind=="grid":a=Fraction(0);b=Fraction(1,2**61);u=b/2;d=b/8
        if kind=="product":a=Fraction(2**60);b=a+1;u=(a+b)/2;d=Fraction(1,8)
        if kind=="work":work=f._ADWWork(1,100000)
        with pytest.raises(f.ADWScalarUnresolved):f._adw_distance_bracket(a,b,u,d,work)

    def test_real_former_80_row_endpoint_replays_under_unchanged_caps(self):
        G=49.34802200544679
        cert=f.adw_scalar_minimum(G,1.,4)
        assert cert.inputs[0]==Fraction(3472558336175019,70368744177664)
        assert cert.branch=="positive" and any(t[-1]=="distance" for t in cert.trace)
        assert cert.max_work==200000 and cert.max_bits==100000
        assert f.adw_validate_scalar_enclosure(cert,G,1.,4) is cert
        for step in cert.trace:
            for endpoint in step[1:4]:
                assert endpoint.denominator & (endpoint.denominator-1)==0
        assert cert.returned_magnitude_error<=cert.requested_rtol*Fraction.from_float(cert.C)
        assert cert.energy_rounding_error+cert.energy_gap_upper<=cert.requested_energy_rtol*abs(Fraction.from_float(cert.V_eff))

    def test_numpy_integral_components_remain_exact_python_integers(self):
        import numpy as np
        for value in (np.int8(4),np.int64(4),np.uint64(2**63+1)):
            exact=f._adw_exact(value,"input")
            assert type(exact.numerator) is int and type(exact.denominator) is int
            assert exact==int(value)
            f._ADWWork(100,1000).take(exact)


class TestM1NestedExactRationalAdmission:
    @pytest.mark.parametrize("kind",["signed_numerator","signed_pair","unsigned_numerator","unsigned_pair","signed_large","unsigned_large"])
    def test_real_public_generator_snapshot_and_replay_preserve_exact_value(self,kind):
        import numpy as np
        values={"signed_numerator":Fraction(np.int64(1)),
                "signed_pair":Fraction(np.int64(4),np.int64(2)),
                "unsigned_numerator":Fraction(np.uint64(1)),
                "unsigned_pair":Fraction(np.uint64(6),np.uint64(4)),
                "signed_large":Fraction(np.int64(2**62+1)),
                "unsigned_large":Fraction(np.uint64(2**63+1),np.uint64(3))}
        value=values[kind];expected=Fraction(int(value.numerator),int(value.denominator))
        normalized=f._adw_exact(value,"input",positive=True)
        assert normalized==expected
        assert type(normalized.numerator) is type(normalized.denominator) is int
        if "large" in kind:assert normalized!=Fraction.from_float(float(normalized))
        cert=f.adw_scalar_minimum_ratio(value)
        assert cert.inputs[0]==expected
        assert f.adw_validate_scalar_enclosure_ratio(cert,value) is cert
        parsed=f.adw_scalar_enclosure_from_dict(cert.as_dict())
        assert f.adw_validate_scalar_enclosure_ratio(parsed,value) is parsed
        def canonical(payload):
            if type(payload) is Fraction:
                assert type(payload.numerator) is type(payload.denominator) is int
            elif type(payload) is tuple:
                for x in payload:canonical(x)
        for field in cert.__dataclass_fields__:canonical(getattr(cert,field))

    @pytest.mark.parametrize("negative",[-1,-4])
    def test_real_public_negative_nested_fraction_refuses_by_domain(self,negative):
        import numpy as np
        value=Fraction(np.int64(negative),np.int64(2))
        with pytest.raises(ValueError,match="positive"):
            f.adw_scalar_minimum_ratio(value)

    def test_real_scalar_and_origin_requests_normalize_without_float_conversion(self):
        import numpy as np
        q=lambda n,d=1:Fraction(np.int64(n),np.int64(d))
        kwargs=dict(atol=q(0),rtol=q(1,10**10),energy_atol=q(0),energy_rtol=q(1,10**8))
        cert=f.adw_scalar_minimum(q(2),q(1),q(4),**kwargs)
        assert cert.branch=="origin" and cert.inputs==(Fraction(2),Fraction(1),Fraction(4))
        assert cert.requested_rtol==Fraction(1,10**10)
        assert f.adw_validate_scalar_enclosure(cert,q(2),q(1),q(4),**kwargs) is cert
        origin=f.adw_origin_proxy(q(2),q(1),q(4),scalar_enclosure=cert,
            origin_atol=q(0),origin_rtol=q(1,10**10),**kwargs)
        assert origin.requests==(Fraction(0),Fraction(1,10**10))
        assert f.adw_validate_origin_proxy_enclosure(origin,q(2),q(1),q(4),scalar_enclosure=cert,
            origin_atol=q(0),origin_rtol=q(1,10**10),**kwargs) is origin
        for value in (*cert.inputs,*origin.inputs,*origin.requests):
            assert type(value.numerator) is type(value.denominator) is int

    @pytest.mark.parametrize("field",["inputs","z_interval","requested_atol","energy_gap_upper"])
    def test_noncanonical_equal_value_scalar_witness_refuses_before_replay(self,field,monkeypatch):
        import numpy as np
        c=f.adw_scalar_minimum_ratio(Fraction(1))
        if field=="inputs":bad=replace(c,inputs=(Fraction(np.int64(1)),*c.inputs[1:]))
        elif field=="z_interval":bad=replace(c,z_interval=(Fraction(np.int64(0)),Fraction(0)))
        else:bad=replace(c,**{field:Fraction(np.int64(0))})
        def forbidden(*a,**kw):raise AssertionError("noncanonical witness reached pi/replay")
        monkeypatch.setattr(f,"_adw_pi_bounds",forbidden)
        with pytest.raises(ValueError,match="canonical Python-integer Fraction"):
            f.adw_validate_scalar_enclosure_ratio(bad,Fraction(1))

    @pytest.mark.parametrize("field",["inputs","requests","errors"])
    def test_noncanonical_origin_witness_refuses_before_scalar_or_pi(self,field,monkeypatch):
        import numpy as np
        scalar=f.adw_scalar_minimum(1.,1.,4)
        origin=f.adw_origin_proxy(1.,1.,4,scalar_enclosure=scalar)
        old=getattr(origin,field);bad=replace(origin,**{field:(Fraction(np.int64(int(old[0].numerator)),np.int64(int(old[0].denominator))),*old[1:])}) if field!="errors" else replace(origin,errors=(Fraction(np.int64(0)),*old[1:]))
        # The errors corruption is intentionally numerically false too; preflight
        # must reject its noncanonical representation before any arithmetic.
        def forbidden(*a,**kw):raise AssertionError("noncanonical origin reached expensive replay")
        for name in ("adw_scalar_minimum","adw_validate_scalar_enclosure","_adw_pi_bounds","_adw_origin_at_terms"):
            monkeypatch.setattr(f,name,forbidden)
        with pytest.raises(ValueError,match="canonical Python-integer Fraction"):
            f.adw_validate_origin_proxy_enclosure(bad,1.,1.,4,scalar_enclosure=scalar)


class TestM1PreArithmeticWitnessAdmission:
    @pytest.mark.parametrize("field",["pi_interval","r_interval","z_interval"])
    @pytest.mark.parametrize("unsigned",[False,True])
    def test_actual_numpy_overflow_payload_rejected_before_comparison(self,field,unsigned,monkeypatch):
        import numpy as np
        c=f.adw_scalar_minimum_ratio(Fraction(1))
        dtype=np.uint64 if unsigned else np.int64
        largest=2**64-1 if unsigned else 2**63-1
        payload=Fraction(dtype(largest),dtype(largest-1))
        bad=replace(c,**{field:(payload,payload)})
        def forbidden(*a,**kw):raise AssertionError("noncanonical interval reached pi/replay")
        monkeypatch.setattr(f,"_adw_pi_bounds",forbidden)
        with np.errstate(over="raise"):
            with pytest.raises(ValueError,match="canonical Python-integer Fraction"):
                f.adw_validate_scalar_enclosure_ratio(bad,Fraction(1))


def test_supplied_parameter_facade_above_cutoff_with_independent_integral_bracket():
    """Actual supplied-G route is unrestricted; this is not a Fig29 row."""
    G, cutoff, species = 240.0, 1.0, 4
    result = f.adw_scalar_minimum(G, cutoff, species)
    assert result.model == 'supplied-parameters-exact-pi'
    assert result.inputs == (Fraction(G), Fraction(cutoff), Fraction(species))
    assert result.z_interval[0] > 1 and result.z_interval[1] < 2
    assert result.C > cutoff
    assert f.adw_validate_scalar_enclosure(result, G, cutoff, species) is result
    with mp.workdps(180):
        ratio = mp.mpf(G)*species/(8*mp.pi**2)
        assert independent_j(Fraction(1)) > 1/ratio > independent_j(Fraction(2))
        energy = independent_value(mp.mpf(result.C), mp.mpf(G), mp.mpf(cutoff), mp.mpf(species))
        assert mq(result.energy_interval[0]) <= energy <= mq(result.energy_interval[1])
