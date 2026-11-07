"""Exact bounded jet controls and separately admitted COMPLETE one-site control."""
from fractions import Fraction as F
import pytest
from src.vestigial import original_coefficients as o
from src.core import formulas as f

@pytest.fixture(autouse=True)
def bounded_work(request):
    if request.node.name == 'test_original_full_small_carrier_direct_vs_auxiliary':
        yield
    else:
        with o.ExactBudget(1_000_000,512*1024**2) as cost:
            yield
        import resource
        rss=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        assert rss<=512*1024**2
        print('SCALAR_PRODUCTS', request.node.name, cost.products, 'PROCESS_PEAK_RSS_BYTES',rss)


def p(x): return o.Polynomial.scalar(x)

def test_n16_metric_sewing_geometric_action_and_anchor_support():
    reg = o.OriginalRegulator(convention='metric_M')
    x0 = (0, 0, 1, 0)
    y0 = (0, 1, 1, 0)
    x1, y1 = (1, 0, 1, 0), (1, 1, 1, 0)
    result = f.original_metric_sewing_support(reg, x0, 1)
    cases = result['cases']
    assert result['core'] == (x0, y0, x1, y1)
    assert len(result['spectator_edges']) == 6
    assert set(result['spectator_anchors']) == {
        (site, 1) for site in reg.sites if site not in result['core']
    }
    assert tuple(s['multiplicities'] for s in cases['diagonal']['supports']) == (
        (((2, x0, (0, 1)), 1), ((2, y1, (0, 1)), 1)),
        (((2, y0, (0, 1)), 1), ((2, x1, (0, 1)), 1)),
    )
    forward, = cases['mixed_fg']['supports']
    reverse, = cases['mixed_gf']['supports']
    assert forward['multiplicities'] == (((2, x0, (0, 1)), 2), ((2, y0, (0, 1)), 2))
    assert reverse['multiplicities'] == (((2, x1, (0, 1)), 2), ((2, y1, (0, 1)), 2))
    assert forward['exponential_weight'] == reverse['exponential_weight'] == F(1, 4)
    assert len(forward['anchors']) == 28
    translation = dict(result['anchor_translation'])
    assert set(translation) == set(translation.values()) == set(reg.link_order)
    assert {translation[a] for a in forward['anchors']} == set(reverse['anchors'])
    for s in (*cases['diagonal']['supports'], forward, reverse):
        channels = s['curvature_channels']
        assert len(channels) == 2
        first, second = (set(a for _, anchors in c for a in anchors) for c in channels)
        assert len(first) == len(second) == 4 and first.isdisjoint(second)
        assert all(axis in (2, 3) for _, axis in first | second)
        for channel in channels:
            assert {order for order, _ in channel} == {
                (2, 3, 0, 1), (2, 3, 1, 0), (3, 2, 0, 1), (3, 2, 1, 0),
            }


@pytest.mark.parametrize('convention, axis, x0', (
    ('metric_M', 1, (0, 0, 1, 0)),
    ('source_C', 1, (1, 0, 0, 0)),
))
def test_n16_metric_sewing_literal_temporal_and_spatial_support(convention, axis, x0):
    reg = o.OriginalRegulator(convention=convention)
    t = reg.temporal_axis
    result = f.original_metric_sewing_support(reg, x0, axis)
    x0, y0, x1, y1 = result['core']
    cases = result['cases']
    for key, unfilled in (('temporal_x', (y0, y1)), ('temporal_y', (x0, x1))):
        assert dict(cases[key]['holes']) == {site: 2 for site in unfilled}
        assert cases[key]['supports'] == ()
    temporal, = cases['temporal_mixed']['supports']
    spatial, = cases['spatial_mixed']['supports']
    assert temporal['multiplicities'] == spatial['multiplicities'] == ()
    assert temporal['exponential_weight'] == spatial['exponential_weight'] == 1
    assert set(spatial['anchors']) == {(site, axis) for site in reg.sites}
    assert set(temporal['anchors']) - set(spatial['anchors']) == {
        (site, t) for site in (x0, y0, x1, y1)
    }
    assert all(not s['curvature_channels'] for s in (temporal, spatial))


def test_n16_metric_sewing_support_rejects_other_geometry():
    x = (0, 0, 0, 0)
    for reg, root, axis in (
        (o.OriginalRegulator((2, 2, 2, 1)), x, 0),
        (o.OriginalRegulator(boundary_signs=(-1, 1, 1, 1)), x, 0),
        (o.OriginalRegulator(word='printed'), x, 0),
        (o.OriginalRegulator(temporal_axis=0), x, 1),
        (o.OriginalRegulator(), x, 3),
        (o.OriginalRegulator(), (0, 0, 0, 1), 0),
    ):
        with pytest.raises(ValueError):
            f.original_metric_sewing_support(reg, root, axis)


def test_singular_first_mixed_repeated_minors():
    z = o.SparseMatrix(2, ())
    a = o.SparseMatrix(2, (((0,0),1),))
    b = o.SparseMatrix(2, (((1,1),1),))
    m = o.SparseMatrix(2, (((1,1),3),))
    assert o.determinant_jet(m, (a,)).at((0,)) == p(3)
    assert o.determinant_jet(z, (a,b)).at((0,1)) == p(1)
    ident = o.SparseMatrix(2, (((0,0),1),((1,1),1)))
    assert o.determinant_jet(z, (ident,)).at((0,0)) == p(2)
    assert o.determinant_jet(o.SparseMatrix(1,()), (o.SparseMatrix(1,(((0,0),1),)),)).at((0,0)) == p(0)
    assert o.complementary_insertion(m, (0,), (0,)) == p(3)
    # Two sorted bars then two sorted psis supply a minus at n=2.
    assert o.complementary_insertion(z,(0,1),(0,1)) == p(-1)


def test_exact_gaussian_haar_and_sigma_independence():
    for v in (F(2),F(3)):
        assert f.original_gaussian_moment((3,),v)==0
        assert f.original_gaussian_moment((4,2),v)==3*v**3
        assert f.original_scaled_hermite(2,v)==((0,-v),(2,F(1)))
        assert o.hermite_gaussian_contraction((2,), (2,), v)==2
        assert o.hermite_gaussian_contraction((0,), (4,), v)==3*v*v
        assert o.hermite_gaussian_contraction((3,), (3,), v)==6
        # Independent polynomial expansion, not formula-to-itself.
        assert o.hermite_gaussian_contraction((2,), (4,),v)==12*v
    assert f.original_quaternion_haar_moment((2,0,0,0))==F(1,4)
    assert f.original_quaternion_haar_moment((4,0,0,0))==F(1,8)
    assert f.original_quaternion_haar_moment((2,2,0,0))==F(1,24)
    q=lambda axis,ch,k:o.Symbol('q',((0,0,0,0),axis,ch,k))
    assert o.haar_polynomial(o.Polynomial((((q(0,'L',1),)*2+(q(0,'R',1),)*2,1),)))==p(F(1,16))
    assert o.haar_polynomial(o.Polynomial((((q(0,'L',1),q(1,'L',1)),1),)))==p(0)


def test_raw_contacts_acceleration_and_denominator():
    J=o.RawJet
    # O=2+3t+5s+7t²/2+11ts+13s²/2, S analog; measure moves too.
    a=J.from_slots((2,3,5,7,11,13)); b=J.from_slots((17,19,23,29,31,37))
    assert (a*b).slots()==(34,89,131,291,413,525)
    x=J.from_slots((0,2,3,5,7,11))
    ex=o.exponential_jet(x, p(1))
    assert ex.slots()==tuple(map(p,(1,2,3,9,13,20)))
    out=o.insertion_action_measure_jet(a,x,b, p(1))
    assert out == a*ex*b
    n=J.from_slots((2,3,5,7,11,13)); den=J.from_slots((4,2,3,5,7,11))
    r=o.normalize_jet(n,den,o.NonzeroZCertificate(o.QComplex(4)))
    assert r.at(())==o.QComplex(F(1,2))
    assert r.at((0,))==o.QComplex(F(1,2))
    assert r.at((0,1))==o.QComplex(F(17,16))
    # Frame acceleration is not truncated by Grassmann/source derivative count.
    frames=f.original_diagonal_frame_jets()
    assert frames[0].at((0,1))==p(1)
    assert frames[1].at((0,0))==p(1)
    assert frames[2].at((1,1))==p(1)
    assert frames[3].at((0,1))==p(2)


def test_W_derivative_and_all_jet_contacts():
    h=o.Polynomial.variable(o.Symbol('h',(0,)))
    for v in (F(2),F(3)):
        w=h*h+p(2)
        first,second=f.original_auxiliary_insertion_weights(w,(o.Symbol('h',(0,)),),v)
        assert first[0]==h*w*F(1,v)-h*2
        assert second[0,0]==(h*h*F(1,v*v)-p(F(1,v)))*w-h*h*F(4,v)+p(2)
        assert second[0,0] != (h*h*F(1,v*v)-p(F(1,v)))*w


def test_source_family_grading_and_unknown_refusals():
    s=o.GeneratorLinkSupport((),(),())
    # Odd literal metric order IS permitted by weighted saturation.
    g=o.GradedTerm(2,(0,0),(0,1),('literal_metric',),s,F(1))
    assert g.saturates(1,inserted_degree=2)
    assert not g.saturates(1)
    assert o.literal_source_supported(4,0,1,2)
    assert not o.literal_source_supported(4,1,1,0)
    with pytest.raises(ValueError,match='UNKNOWN'):
        o.normalize_jet(o.RawJet.constant(o.QComplex(1)),o.Unknown('full Z not computed'),None)
    with pytest.raises(ValueError,match='nonzero'):
        o.NonzeroZCertificate(o.QComplex(0))
    with pytest.raises(ValueError,match='Hessian'):
        o.legendre_local(((0,0),(0,0)), (0,1))
    assert o.legendre_local(((2,0),(0,3)), (0,1)) == ((o.QComplex(F(1,2)),o.QComplex()),(o.QComplex(),o.QComplex(F(1,3))))


def test_exact_budget_no_partial_complete_result():
    with pytest.raises(o.BudgetExceeded,match='incomplete'):
        with o.ExactBudget(0,512*1024**2):
            o.determinant_jet(o.SparseMatrix(1,(((0,0),1),)),())
    with pytest.raises(o.BudgetExceeded,match='storage'):
        o.ExactBudget(100,1).check_storage((p(1),))


def test_original_full_small_carrier_direct_vs_auxiliary():
    # This COMPLETE scientific test requires ROOT runtime admission. No skip or
    # environment bypass; bounded allocation selects other named tests explicitly.
    with o.ExactBudget(250_000_000,2*1024**3) as budget:
        result=f.original_one_site_complete_control(budget=budget)
    assert result['complete']
    assert result['quartic_slots']==3876 and result['center_allowed']==740
    assert result['words']==('printed','closed') and result['variances']==(F(2),F(3))
    assert result['query_count']==23504*4
    # Expected accepted polynomial is a regression ORACLE only in this test.
    # The production coefficients were independently generated from original
    # coframe, exterior, determinant, Gaussian and Haar arithmetic.
    origin=(0,0,0,0)
    j=tuple(o.Polynomial.variable(o.Symbol('J',(origin,mu,a))) for mu in range(4) for a in range(4))
    g2=o.Polynomial.variable(o.Symbol('g2',()))
    rows=tuple(sum((j[4*mu+a]*j[4*mu+a] for a in range(4)),p(0)) for mu in range(4))
    expected=g2*g2*96+sum((r*r*F(25,128) for r in rows),p(0))
    from itertools import combinations
    for mu,nu in combinations(range(4),2):
        dot=sum((j[4*mu+a]*j[4*nu+a] for a in range(4)),p(0))
        expected+=rows[mu]*rows[nu]*F(13,32)+dot*dot*F(1,16)
    for word, report in result['reports'].items():
        assert report['direct']==report['auxiliary'][F(2)]==report['auxiliary'][F(3)]==expected
        assert report['interacting_denominator']==p(96)
        assert report['nonzero_quartics']==172
        assert len(report['T_first'])==16 and len(report['T_second'])==136
        assert len(report['H_first'])==10 and len(report['H_second'])==55
        assert report['frame_direct']==report['frame_auxiliary'][F(2)]==report['frame_auxiliary'][F(3)]


def test_prehaar_frame_metric_current_contacts():
    reg=o.OriginalRegulator((2,1,1,1))
    x,y=reg.sites
    # Exact original endpoint bilinear and local phase charge, then frame path.
    links={anchor:f.original_spin4_link((0,1,0,0),(0,0,1,0)) for anchor in reg.link_order}
    t=o.assemble_coframe(reg,f.original_coframe_blocks(reg,(x,0,3),links)).to_exterior(reg)
    charges={x:F(0),y:F(1)}
    current=o.exterior_phase_derivative(t,reg,charges)
    assert current != o.ExteriorPolynomial()
    scalar=o.RawJet.from_slots(tuple(p(v) for v in (1,2,3,5,7,11)))
    tj=o.RawJet.constant(t)*scalar
    cj=o.apply_linear_map_jet(tj,lambda v:o.exterior_phase_derivative(v,reg,charges))
    assert cj.at((0,1))==current*p(7)
    coframes={(x,mu,a):tj for mu in range(4) for a in range(4)}
    metric=f.original_literal_metric(coframes,x,0,1)
    assert metric.at((0,1))==(t*t)*p(4*(2*7+2*2*3))
    assert o.apply_linear_map_jet(metric,lambda v:o.exterior_phase_derivative(v,reg,charges)).at((0,1))==o.exterior_phase_derivative(metric.at((0,1)),reg,charges)


def test_literal_metric_joint_polynomial_repeated_factors():
    j=tuple(o.Symbol('J',(i,)) for i in range(16))
    h=tuple(o.Symbol('H',(i,)) for i in range(10))
    # A complete formal quartic seed tests generic H and raw factors without
    # asserting this formal seed is an averaged original one-site coefficient.
    seed=o.Polynomial((((j[0],)*4,1),((j[0],j[0],j[4],j[4]),1)))
    joint=o.literal_metric_source_polynomial(seed,j,h)
    assert dict(joint.terms)[tuple(sorted((h[0],h[0])))]==o.QComplex(12)
    # Offdiagonal H01 occurs once: dJ0 dJ4 on J0²J4² gives 4J0J4.
    assert dict(joint.terms)[tuple(sorted((j[0],j[4],h[1])))]==o.QComplex(4)
    assert dict(joint.terms)[tuple(sorted((h[1],h[1])))]==o.QComplex(2)


def test_weight_full_degree_compensation_without_local8():
    x=o.Symbol('X',(0,)); X=o.Polynomial.variable(x)
    # Independent tiny EXACT Hermite algebra fixture; original full carrier is
    # the separate full scientific control. No substitution for that target.
    for v in (F(2),F(3)):
        w=o.hermite_weight(X*X*F(2,3),(x,),v,4)
        h=o.Symbol('h',(0,)); aux=o.Polynomial.variable(h)
        # Evaluate every polynomial coefficient through independently expanded
        # centered Gaussian moments against the true polynomial determinant seed.
        product=w*(aux*aux*aux*aux)
        value=sum((c.real*f.original_gaussian_moment((len(k),),v) for k,c in product.terms),F(0))
        assert value==F(16,3)
    with pytest.raises(ValueError,match='zero X-constant'):
        o.hermite_weight(p(1),(x,),F(2),4)


def test_original_zero_coupling_normalization_refusal():
    # Original V=1 has four fermion pairs, so literal zero M determinant is0.
    zero=o.determinant_jet(o.SparseMatrix(4,()),())
    assert zero.at(())==p(0)
    with pytest.raises(ValueError,match='nonzero'):
        o.normalize_jet(zero,zero,None)
    with pytest.raises(ValueError,match='nonzero'):
        o.logarithmic_response(zero,None)


def test_graded_coefficient_and_complete_raw_weight_schedule():
    # Metadata-only full raw roster: no original coefficients/Haar/control run.
    from itertools import combinations,permutations
    quadratic={(4*mu+a,4*nu+b):p(1) for mu,nu in combinations(range(4),2) for a in range(4) for b in range(4) if a!=b}
    quartic=tuple((tuple(4*mu+a for mu,a in enumerate(order)),F(o.epsilon(order))) for order in permutations(range(4)))
    for v in (F(2),F(3)):
        terms=o.one_site_weight_terms(quadratic,quartic,v)
        assert len(terms)==4029
        assert sum(1 for term in terms for _ in o.gaussian_compatible_queries(term))==23504
        assert sum(term.origin=='compensation' for term in terms)==16
    assert len(o.multiindices(16,4))==3876
    assert sum(o.direction_center_even(k) for k in o.multiindices(16,4))==740
    assert sum(not o.direction_center_even(k) for k in o.multiindices(16,4))==3136


def test_actual_original_frame_phase_action_pullback():
    reg=o.OriginalRegulator((2,1,1,1)); x,y=reg.sites
    choices=((F(3,5),F(4,5),0,0),(F(5,13),0,F(12,13),0),(0,0,0,1),(F(8,17),F(9,17),F(12,17),0))
    links={anchor:f.original_spin4_link(choices[i%4],choices[(i+1)%4]) for i,anchor in enumerate(reg.link_order)}
    zero=o.RawJet.constant(p(0)); ident=o.RawJet.constant(p(1))
    frame={(site,mu,nu):(ident if mu==nu and mu<2 else zero) for site in reg.sites for mu in range(4) for nu in range(4)}
    for site in reg.sites:
        frame[site,0,0]=o.RawJet.from_slots(tuple(p(v) for v in (1,2,0,3,0,0)))
    phase={x:zero,y:o.RawJet.from_slots(tuple(p(v) for v in (0,0,1,0,0,0)))}
    charges={x:0,y:1}
    jet=f.original_frame_source_jet(reg,links,frame=frame,phase=phase,g2=1,metric_sources={(x,0,0):1},insertion=lambda t:f.original_literal_metric(t,x,0,0))
    assert jet.action.at(()) != o.ExteriorPolynomial()
    assert jet.action.at((1,)) == o.exterior_phase_derivative(jet.action.at(()),reg,charges)
    assert jet.action.at((0,1)) == o.exterior_phase_derivative(jet.action.at((0,)),reg,charges)
    assert jet.insertion.at((0,0)) == jet.insertion.at(())*p(2*3+2*2**2)
    assert jet.measure.at((0,1))==p(0)
    assert any(term.t_degree==2 and term.coupling_powers==(0,1) for key,terms in jet.grading.entries for term in terms if term.contact_labels==('action',))
    assert any(term.t_degree==2 and term.coupling_powers==(0,0) and term.source_powers==(0,1) for key,terms in jet.grading.entries for term in terms if term.contact_labels==('literal_metric',))


def test_generic_coefficient_request_preserves_coupling_roster():
    g1,g2=o.Symbol('g1',()),o.Symbol('g2',())
    cert=o.SupportCertificate('bounded exact polynomial fixture',(),o.SourceFamilyGrading(()),True,(),())
    request=o.CoefficientRequest(((0,2),),(),'unit',cert)
    poly=o.Polynomial((((g1,),2),((g2,g2),3),((),5)))
    assert o.extract_requested_coefficients(poly,request)==o.Polynomial((((g2,g2),3),))


def test_accelerated_singular_three_by_three_and_jet_immutability():
    m=o.SparseMatrix(3,(((1,1),2),((2,2),3)))
    identity=o.SparseMatrix(3,tuple(((i,i),1) for i in range(3)))
    acceleration=o.SparseMatrix(3,(((0,0),5),))
    jet=o.determinant_jet(m,(identity,),{(0,0):acceleration})
    # det(diag(0,2,3)+t I)=6t+5t²+t³. Matrix acceleration adds5*6.
    assert jet.at((0,))==p(6)
    assert jet.at((0,0))==p(40)
    labels=[0,1]; index=[0]
    value=o.RawJet(labels,(((),p(2)),(index,p(3))))
    labels[0]=8; index[0]=1
    assert value.labels==(0,1) and value.at((0,))==p(3)
    with pytest.raises(TypeError,match='immutable'):
        o.RawJet((0,),(((),[1]),))
    with pytest.raises(ValueError,match='C2'):
        value.at((0,0,0))


def test_factored_weight_and_request_metadata_freeze():
    labels=[0,1]; directions=[0,0]
    term=o.FactoredWeightTerm(labels,F(2),frame_directions=directions)
    labels[0]=9;directions[0]=3
    assert term.eta==(0,1) and term.frame_directions==(0,0)
    roster=[[o.Symbol('J',(0,))]]; coupling=[[0,2]]
    cert=o.SupportCertificate('unit',roster,o.SourceFamilyGrading(()),True,[],[])
    request=o.CoefficientRequest(coupling,roster,'unit',cert)
    roster[0].clear();coupling[0][1]=4
    assert request.coupling_powers==((0,2),)
    assert request.source_multiindices==cert.source_multiindices==((o.Symbol('J',(0,)),),)


@pytest.mark.parametrize('operation', ['integrated', 'derivative', 'haar', 'raw_scalar'])
def test_r2_scalar_product_counter_covers_actual_operations(operation, monkeypatch):
    observed=[]
    mul=o.QComplex.__mul__
    def record(self, other):
        observed.append((self,other))
        return mul(self,other)
    monkeypatch.setattr(o.QComplex,'__mul__',record)
    monkeypatch.setattr(o.QComplex,'__rmul__',record)
    q=o.Symbol('q',((0,0,0,0),0,'L',0)); j=o.Symbol('J',(0,))
    with o.ExactBudget(10000,512*1024**2) as budget:
        if operation=='integrated':
            v=o.integrated_polynomial_product(o.Polynomial((((q,q),2),)),o.Polynomial((((q,q),2),)))
            assert v==o.QComplex(F(1,2))
        elif operation=='derivative':
            assert o.polynomial_derivative(o.Polynomial((((j,j),3),)),j)==o.Polynomial((((j,),6),))
        elif operation=='haar':
            assert o.haar_polynomial(o.Polynomial((((q,q),2),)))==p(F(1,2))
        else:
            (o.RawJet.constant(o.QComplex(2))*o.RawJet.constant(o.QComplex(3))).slots()
    assert budget.products>=len(observed)>0


@pytest.mark.parametrize('operation', ['input', 'stream', 'temporary', 'rational_kernel'])
def test_r2_integer_height_refusal_covers_streams_and_temporaries(operation):
    with pytest.raises(o.BudgetExceeded,match='height'):
        with o.ExactBudget(10000,512*1024**2,integer_bit_limit=8):
            if operation=='input':o.QComplex(2**20)
            elif operation=='stream':o.integrated_polynomial_product(p(2**20),p(1))
            elif operation=='temporary':o.QComplex(F(200,201))*o.QComplex(F(201,200))
            else:f.original_gaussian_moment((12,),F(3))


def test_r2_certificate_rejects_mutable_or_untyped_grading():
    with pytest.raises((TypeError,ValueError),match='grading'):
        o.SupportCertificate('unit',(),[],True,(),())
    with pytest.raises((TypeError,ValueError),match='support'):
        o.GradedTerm(0,(0,0),(0,0),('measure',),[],F(1))


def test_r2_nonzero_raw_source_requires_actual_summand_grading():
    labels=(0,1); zero=o.ExteriorPolynomial()
    with pytest.raises((TypeError,ValueError),match='grading'):
        o.SourceJet(labels,o.SourceFamilyGrading(tuple((k,()) for k in o.RawJet.constant(zero).indices())),
                    o.RawJet.constant(zero),o.RawJet.constant(o.ExteriorPolynomial(((255,p(1)),))),o.RawJet.constant(p(1)))



def _r2_matched_top_source():
    reg=o.OriginalRegulator((1,1,1,1)); labels=(0,1)
    zero=o.ExteriorPolynomial(); top=o.ExteriorPolynomial(((255,p(1)),))
    entries=[]
    for k in o.RawJet.constant(zero,labels).indices():
        terms=() if k else (
            o.GradedTerm(4,(0,0),(0,0),('insertion',),o.GeneratorLinkSupport(reg.generator_order,reg.link_order,reg.sites),F(1),o.QComplex(1),255,()),
            o.GradedTerm(0,(0,0),(0,0),('measure',),o.GeneratorLinkSupport((),(),()),F(1),o.QComplex(1),None,()))
        entries.append((k,terms))
    grade=o.SourceFamilyGrading(tuple(entries))
    return reg,o.SourceJet(labels,grade,o.RawJet.constant(zero),o.RawJet.constant(top),o.RawJet.constant(p(1)))


@pytest.mark.parametrize('defect',['roster','grading','generator','insertion_id'])
def test_r2_contract_refuses_unrelated_complete_certificate(defect):
    reg,source=_r2_matched_top_source()
    roster=() if defect!='roster' else ((o.Symbol('H',(0,0)),),)
    grade=source.grading if defect!='grading' else o.SourceFamilyGrading(())
    generators=reg.generator_order if defect!='generator' else ()
    certificate=o.SupportCertificate('complete matched fixture',roster,grade,True,generators,reg.link_order)
    request=o.CoefficientRequest(None,(),'another insertion' if defect=='insertion_id' else 'unit',certificate)
    with pytest.raises(ValueError,match='support|grading|carrier|insertion'):
        o.contract_original(reg,source,request,o.ExactBudget(1000,512*1024**2))


def test_r2_matched_full_support_and_exact_requested_scope():
    reg,source=_r2_matched_top_source()
    certificate=o.SupportCertificate('matched complete fixture',(),source.grading,True,reg.generator_order,reg.link_order)
    result=o.contract_original(reg,source,o.CoefficientRequest(None,(),'unit',certificate),o.ExactBudget(1000,512*1024**2))
    assert result.support==certificate and result.support.complete
    assert dict(result.N)[()]==p(1)


def test_r2_haar_bucketing_preserves_correlated_links_and_sign():
    q=lambda mu,k:o.Symbol('q',((0,0,0,0),mu,'L',k))
    a=o.Polynomial((((q(0,0),q(0,1)),o.QComplex(2,3)),((q(0,0),q(1,0)),5)))
    b=o.Polynomial((((q(0,0),q(0,1)),o.QComplex(7,-2)),((q(0,0),q(1,0)),11)))
    expanded=o._scalar_value(o.haar_polynomial(a*b))
    assert o.integrated_polynomial_product(a,b)==expanded
    assert o.integrated_polynomial_product(a,b,-1)==-expanded


def test_r2_raw_rational_temporary_height_is_checked():
    with pytest.raises(o.BudgetExceeded,match='height'):
        with o.ExactBudget(10000,512*1024**2,integer_bit_limit=8):
            o.RawJet.constant(F(200,201))*o.RawJet.constant(F(201,200))


def test_r2_raw_rational_sum_temporary_height_is_checked():
    with pytest.raises(o.BudgetExceeded,match='height'):
        with o.ExactBudget(10000,512*1024**2,integer_bit_limit=8):
            o.RawJet.constant(F(200,201))+o.RawJet.constant(F(201,200))



def test_r2_rational_kernel_billing_and_unreduced_height():
    with o.ExactBudget(1000,512*1024**2) as budget:
        before=budget.products
        assert o.count_hermite_contraction((0,0),(0,0,0,0),F(3))==36
        assert budget.products>before
    # The scaled Hermite inverse has a temporary v*v even for zero W.
    with pytest.raises(o.BudgetExceeded,match='height'):
        with o.ExactBudget(10000,512*1024**2,integer_bit_limit=8):
            f.original_auxiliary_insertion_weights(p(0),(o.Symbol('h',(0,)),),F(200,201))



def test_r2_storage_admission_checks_fraction_payload():
    with pytest.raises(o.BudgetExceeded,match='height'):
        o.ExactBudget(1000,512*1024**2,integer_bit_limit=8).check_storage((F(2**20,3),))


def test_r2_source_roster_rejects_non_source_and_noncanonical_monomials():
    grade=o.SourceFamilyGrading(())
    for roster in (((o.Symbol('g2',()),),), ((o.Symbol('J',(1,)),o.Symbol('J',(0,))),)):
        with pytest.raises((TypeError,ValueError),match='source roster'):
            o.SupportCertificate('unit',roster,grade,True,(),())



def test_r2_central_primitive_counter_has_no_double_billing():
    j=o.Polynomial.variable(o.Symbol('J',(0,)))
    with o.ExactBudget(10000,512*1024**2) as budget:
        assert (j+p(2))*(j+p(3))==j*j+j*5+p(6)
    # Use separately constructed inputs to isolate the FOUR coefficient products.
    a=j+p(2);b=j+p(3)
    with o.ExactBudget(10000,512*1024**2) as budget:
        result=a*b
    assert budget.products==4 and result==o.Polynomial((((o.Symbol('J',(0,)),)*2,1),((o.Symbol('J',(0,)),),5),((),6)))
    scalar=o.RawJet.from_slots(tuple(o.QComplex(i) for i in (1,2,3,4,5,6)))
    with o.ExactBudget(10000,512*1024**2) as budget:
        result=scalar*scalar
    assert budget.products==17
    assert result.slots()==tuple(o.QComplex(i) for i in (1,4,6,16,22,30))



@pytest.mark.parametrize('order',(0,1))
def test_r2_certificate_derivative_scope_is_not_silently_expanded(order):
    from dataclasses import replace
    reg,full=_r2_matched_top_source()
    grade=o.SourceFamilyGrading(tuple((k,v) for k,v in full.grading.entries if len(k)<=order))
    source=replace(full,order=order,grading=grade,action=o.RawJet(full.labels,tuple((k,o.ExteriorPolynomial()) for k in full.action.indices())))
    cert=o.SupportCertificate('exact lower-order scope',(),grade,True,reg.generator_order,reg.link_order)
    result=o.contract_original(reg,source,o.CoefficientRequest(None,(),'unit',cert),o.ExactBudget(1000,512*1024**2))
    assert tuple(k for k,v in result.N)==tuple(k for k in full.action.indices() if len(k)<=order)


def test_r2_source_derivative_scope_refuses_hidden_nonzero_contacts():
    from dataclasses import replace
    reg,full=_r2_matched_top_source()
    grade=o.SourceFamilyGrading(tuple((k,v) for k,v in full.grading.entries if not k))
    action=o.RawJet((0,1),(((),o.ExteriorPolynomial()),((0,0),o.ExteriorPolynomial(((255,p(1)),)))))
    with pytest.raises(ValueError,match='grading|scope'):
        replace(full,order=0,grading=grade,action=action)



def test_r2_grading_cannot_erase_actual_quaternion_anchor_or_source_power():
    empty=o.GeneratorLinkSupport((),(),())
    q=o.Symbol('q',((0,0,0,0),0,'L',0))
    with pytest.raises(ValueError,match='anchor|support'):
        o.GradedTerm(0,(0,0),(0,0),('measure',),empty,F(1),o.QComplex(1),None,(q,))
    j=o.Symbol('J',(0,))
    with pytest.raises(ValueError,match='source|grading'):
        o.GradedTerm(0,(0,0),(0,0),('measure',),empty,F(1),o.QComplex(1),None,(j,))


@pytest.mark.parametrize('bits', (8, 1024))
def test_r3_raw_rational_accumulation_observes_unreduced_height(bits):
    n = 127 if bits == 8 else 2**1023 - 1
    a = o.RawJet((0,), (((), F(1)), ((0,), F(1))))
    b = o.RawJet((0,), (((), F(n, 6)), ((0,), F(-n, 10))))
    with pytest.raises(o.BudgetExceeded, match='height'):
        with o.ExactBudget(10000, 512*1024**2, integer_bit_limit=bits):
            a * b
    with o.ExactBudget(10000, 512*1024**2, integer_bit_limit=bits + 8) as budget:
        result = a * b
    assert result.slots() == (F(n, 6), F(n, 15), F(-n, 5))
    assert budget.products == 7
    assert budget.peak_integer_bits > bits


def test_r3_raw_rational_mixed_cancellation_is_not_a_height_certificate():
    a = o.RawJet.from_slots(tuple(map(F, (1, 1, -1, -200, -200, 200))))
    b = o.RawJet.from_slots(tuple(map(F, (1, 200, 200, -200, 200, 200))))
    with pytest.raises(o.BudgetExceeded, match='height'):
        with o.ExactBudget(10000, 512*1024**2, integer_bit_limit=8):
            a * b
    with o.ExactBudget(10000, 512*1024**2, integer_bit_limit=9) as budget:
        result = a * b
    assert result.slots() == tuple(map(F, (1, 201, 199, 0, 0, 0)))
    assert budget.products == 17 and budget.peak_integer_bits == 9


def _r3_two_site_phase_fixture():
    reg = o.OriginalRegulator((2, 1, 1, 1))
    x, y = reg.sites
    indices = {g: i for i, g in enumerate(reg.generator_order)}
    mask = (1 << indices[x, 'bar', 0]) | (1 << indices[y, 'psi', 0])
    return reg, x, y, mask, o.ExteriorPolynomial(((mask, p(1)),))


@pytest.mark.parametrize('bits', (8, 1024))
def test_r3_phase_charge_accumulation_observes_unreduced_height(bits):
    reg, x, y, mask, poly = _r3_two_site_phase_fixture()
    n = 127 if bits == 8 else 2**1023 - 1
    charges = {x: F(n, 10), y: F(n, 6)}
    with pytest.raises(o.BudgetExceeded, match='height'):
        with o.ExactBudget(10000, 512*1024**2, integer_bit_limit=bits):
            o.exterior_phase_derivative(poly, reg, charges)
    with o.ExactBudget(10000, 512*1024**2, integer_bit_limit=bits + 8) as budget:
        result = o.exterior_phase_derivative(poly, reg, charges)
    assert result == o.ExteriorPolynomial(((mask, p(o.QComplex(0, F(n, 15)))),))
    assert budget.products == 1 and budget.peak_integer_bits > bits


def test_r3_phase_cancellation_cannot_hide_oversized_charge_inputs():
    reg, x, y, _, poly = _r3_two_site_phase_fixture()
    charges = {x: 2**20, y: 2**20}
    with pytest.raises(o.BudgetExceeded, match='height'):
        with o.ExactBudget(10000, 512*1024**2, integer_bit_limit=8):
            o.exterior_phase_derivative(poly, reg, charges)
    with o.ExactBudget(10000, 512*1024**2, integer_bit_limit=32):
        assert o.exterior_phase_derivative(poly, reg, charges).terms == ()


def _r3_actual_coframe():
    reg = o.OriginalRegulator((1, 1, 1, 1))
    unit = f.original_spin4_link((0, 0, 0, 1), (0, 0, 0, 1))
    links = {anchor: unit for anchor in reg.link_order}
    alpha = reg.sites[0], 0, 3
    coframe = o.assemble_coframe(reg, f.original_coframe_blocks(reg, alpha, links)).to_exterior(reg)
    return reg, coframe


def _r3_graded_source(reg, action, insertion=None, measure=None, cancelled_body=False):
    """Independent exact supplied-family fixture, retaining pre-collection terms."""
    one = o.ExteriorPolynomial(((0, p(1)),))
    insertion = o.RawJet.constant(one, action.labels) if insertion is None else insertion
    measure = o.RawJet.constant(p(1), action.labels) if measure is None else measure
    grading = []
    empty_support = o.GeneratorLinkSupport((), (), ())
    for k in action.indices():
        terms = []
        for role, jet in (('action', action), ('insertion', insertion)):
            for mask, coefficient in jet.at(k).terms:
                generators = tuple(g for i, g in enumerate(reg.generator_order) if mask >> i & 1)
                for monomial, value in coefficient.terms:
                    anchors = tuple(sorted(set((s.index[0], s.index[1]) for s in monomial if s.family == 'q')))
                    support = o.GeneratorLinkSupport(generators, anchors, tuple(sorted(set(g[0] for g in generators))))
                    cp = tuple(sum(s.family == family for s in monomial) for family in ('g1', 'g2'))
                    sp = tuple(sum(s.family == family for s in monomial) for family in ('J', 'H'))
                    terms.append(o.GradedTerm(mask.bit_count() // 2, cp, sp, (role,), support, F(1), value, mask, monomial))
        if cancelled_body and not k:
            terms.extend(o.GradedTerm(0, (0, 0), (0, 0), ('action',), empty_support, F(1), o.QComplex(sign), 0, ()) for sign in (1, -1))
        for monomial, value in measure.at(k).terms:
            terms.append(o.GradedTerm(0, (0, 0), (0, 0), ('measure',), empty_support, F(1), value, None, monomial))
        grading.append((k, tuple(terms)))
    return o.SourceJet(action.labels, o.SourceFamilyGrading(tuple(grading)), action, insertion, measure)


def _r3_contract(reg, source):
    certificate = o.SupportCertificate('actual positive-degree source family', (), source.grading, True, reg.generator_order, reg.link_order)
    request = o.CoefficientRequest(None, (), 'unit', certificate)
    return o.contract_original(reg, source, request, o.ExactBudget(100000, 512*1024**2))


@pytest.mark.parametrize('index', ((), (0,), (1,), (0, 0), (0, 1), (1, 1)))
def test_r3_every_action_jet_slot_must_have_zero_scalar_body(index):
    reg, coframe = _r3_actual_coframe()
    base = o.RawJet.constant(coframe)
    values = {k: base.at(k) for k in base.indices()}
    values[index] = values[index] + o.ExteriorPolynomial(((0, p(1)),))
    action = o.RawJet(base.labels, tuple(values.items()))
    with pytest.raises(ValueError, match='body|positive|nilpotent'):
        source = _r3_graded_source(reg, action)
        _r3_contract(reg, source)


def test_r3_formal_source_action_body_is_not_grassmann_nilpotent():
    reg, coframe = _r3_actual_coframe()
    j = o.Polynomial.variable(o.Symbol('J', (0,)))
    action = o.RawJet.constant(coframe + o.ExteriorPolynomial(((0, j),)))
    with pytest.raises(ValueError, match='body|positive|nilpotent'):
        _r3_contract(reg, _r3_graded_source(reg, action))


def test_r3_actual_original_acceleration_keeps_unit_insertion_and_measure():
    reg, coframe = _r3_actual_coframe()
    zero = o.ExteriorPolynomial()
    action = o.RawJet.from_slots((coframe, coframe, zero, coframe * 2, zero, zero))
    # Independent last-nonzero power and analytical (1+t+t²)^4 derivatives.
    fourth = coframe * coframe * coframe * coframe
    assert fourth.terms == ((255, p(24)),)
    result = _r3_contract(reg, _r3_graded_source(reg, action))
    assert tuple(dict(result.N)[k] for k in ((), (0,), (0, 0))) == tuple(map(p, (1, 4, 20)))


def test_r3_cancelled_body_preserves_raw_provenance_and_valid_action():
    reg, coframe = _r3_actual_coframe()
    source = _r3_graded_source(reg, o.RawJet.constant(coframe), cancelled_body=True)
    assert sum(term.exterior_mask == 0 and term.contact_labels == ('action',) for term in dict(source.grading.entries)[()]) == 2
    assert all(mask != 0 for mask, _ in source.action.at(()).terms)
    result = _r3_contract(reg, source)
    assert dict(result.N)[()] == p(1)


def test_r3_scalar_measure_motion_keeps_all_action_contacts():
    reg, coframe = _r3_actual_coframe()
    zero = o.ExteriorPolynomial()
    action = o.RawJet.from_slots((coframe, coframe, zero, coframe * 2, zero, zero))
    measure = o.RawJet.from_slots(tuple(map(p, (3, 1, 0, 0, 0, 0))))
    result = _r3_contract(reg, _r3_graded_source(reg, action, measure=measure))
    # (1+t+t²)^4 * (3+t): raw value,first,second are 3,13,68.
    assert tuple(dict(result.N)[k] for k in ((), (0,), (0, 0))) == tuple(map(p, (3, 13, 68)))


@pytest.mark.parametrize('right_q0,right_q3', ((F(3, 5), F(4, 5)), (F(0), F(1))))
def test_n16_polar_coframes_match_both_original_anchors(right_q0, right_q3):
    # Unequal radii detect interchanging gamma and D at y; the second case
    # is singular in the right chirality and must agree without an inverse.
    reg = o.OriginalRegulator((2, 1, 1, 1))
    x, y = reg.sites
    links = {
        (x, 0): f.original_spin4_link((1, 0, 0, 0), (right_q0, 0, 0, right_q3)),
        (y, 0): f.original_spin4_link((-1, 0, 0, 0), (-right_q0, 0, 0, -right_q3)),
    }
    assert hasattr(f, 'original_polar_edge_coframes'), 'missing original polar coframes'
    left, right = f.original_polar_edge_coframes(reg, 0)
    values = {('L',): 2, ('R',): 2 * right_q0}
    radii = {symbol: values[symbol.index] for coframe in left + right
             for _, polynomial in coframe.terms for key, _ in polynomial.terms
             for symbol in key}
    for site, coframes in zip((x, y), (left, right), strict=True):
        for internal, coframe in enumerate(coframes):
            expected = o.assemble_coframe(
                reg, f.original_coframe_blocks(reg, (site, 0, internal), links),
            ).to_exterior(reg)
            evaluated = o.ExteriorPolynomial(tuple(
                (mask, p(value.evaluate(radii))) for mask, value in coframe.terms
            ))
            assert evaluated == expected


def test_n16_direct_edge_full_local_rosters_and_orientation():
    # The accepted manual coefficient proof supplies regression values only.
    # This is a bounded local-edge control, without the auxiliary or N16 action.
    assert hasattr(f, 'original_direct_polar_edge'), 'missing original direct edge kernel'
    with o.ExactBudget(1_000_000, 512 * 1024**2) as budget:
        edge = f.original_direct_polar_edge(o.OriginalRegulator(), 0, budget=budget)
    q = o.QComplex
    assert edge.labels == tuple((chi, kind) for chi in ('L', 'R') for kind in ('n', 'b', 'p'))
    assert edge.radial_moments == (F(1), F(2), F(5), F(14), F(42))
    assert edge.fourth_top == q(F(1125, 4))
    g = ((-2, 0, 0), (0, 0, 1), (0, 1, 0))
    expected_pairing = tuple(tuple(q(g[a % 3][b % 3] if a // 3 == b // 3 else 0)
                                   for b in range(6)) for a in range(6))
    assert edge.local_pairing == expected_pairing
    c = ((1, 0, 0), (0, 0, -2), (0, -2, 0))
    test = ((4, 0, 0), (0, 0, -2), (0, -2, 0))
    for cubic, literal, scale in (
        (edge.cubic_x, edge.cubic_x_tests, F(45, 4)),
        (edge.cubic_mixed, edge.cubic_mixed_tests, F(12)),
    ):
        for table, expected in ((cubic, c), (literal, test)):
            assert len(table) == 6 and all(len(row) == 6 for row in table)
            assert table == tuple(tuple(q(scale * expected[a % 3][b % 3]
                                          if a // 3 != b // 3 else 0)
                                        for b in range(6)) for a in range(6))
    assert budget.products > 0 and 0 < budget.peak_scalar_records <= 55_000


def test_n16_direct_edge_budget_refuses_before_returning_any_result():
    assert hasattr(f, 'original_direct_polar_edge'), 'missing original direct edge kernel'
    reg = o.OriginalRegulator()
    with o.ExactBudget(100, 1) as budget:
        with pytest.raises(o.BudgetExceeded, match='storage budget'):
            f.original_direct_polar_edge(reg, 0, budget=budget)
        assert budget.products == 0
    with o.ExactBudget(1, 512 * 1024**2) as budget:
        with pytest.raises(o.BudgetExceeded, match='scalar budget'):
            f.original_direct_polar_edge(reg, 0, budget=budget)


def test_n16_edge_does_not_discard_odd_polar_powers_as_haar_zeros():
    assert hasattr(o, '_radial_edge_top_integral'), 'missing original radial projector'
    top = (1 << 16) - 1
    with pytest.raises(ValueError, match='odd radial'):
        o._radial_edge_top_integral(
            {(top << 8) | 0x11: o.QComplex(1)}, {0: o.QComplex(1)}, 2, (F(1), F(2)),
        )


def test_n16_edge_coalesced_map_refuses_an_unreserved_slot():
    assert hasattr(o, '_edge_wedge_accumulate'), 'missing coalesced wedge'
    q = o.QComplex
    result = {}
    with pytest.raises(o.BudgetExceeded, match='record'):
        o._edge_wedge_accumulate(
            result, {0x110: q(1), 0x210: q(1)}, {0x401: q(1)},
            max_records=1,
        )
    assert len(result) == 1


@pytest.mark.parametrize('field', ('limit', 'storage_limit', 'integer_bit_limit'))
@pytest.mark.parametrize('invalid', (float('nan'), float('inf'), 1000.0, 1000.5, True, 0, -1))
def test_n16_direct_edge_rejects_each_invalid_cap_before_reserving(field, invalid, monkeypatch):
    def unexpected_reservation(*args, **kwargs):
        pytest.fail('invalid cap reached the first reservation')

    monkeypatch.setattr(o, '_reserve_edge_records', unexpected_reservation)
    budget = o.ExactBudget(100, 512 * 1024**2)
    setattr(budget, field, invalid)
    with budget, pytest.raises(ValueError, match=f'{field} must be a positive exact integer'):
        f.original_direct_polar_edge(o.OriginalRegulator(), 0, budget=budget)
    assert budget.products == budget.peak_payload_bytes == 0


def test_n16_polar_real_roster_preserves_legacy_r_conjugation():
    for index in (('L',), ('R',), ('source', 1)):
        legacy = o.Symbol('r', index)
        assert legacy.conjugate() == o.Symbol('r', index, True)
        assert legacy.conjugate().conjugate() == legacy
    x, y = f.original_polar_edge_coframes(o.OriginalRegulator(), 0)
    radial = {symbol for coframe in x + y for _, polynomial in coframe.terms
              for key, _ in polynomial.terms for symbol in key}
    assert {symbol.index for symbol in radial} == {('L',), ('R',)}
    assert len(radial) == 2 and all(symbol.family != 'r' and symbol.conjugate() == symbol
                                    for symbol in radial)
    unrelated = o.Symbol(next(iter(radial)).family, ('source', 1))
    assert unrelated.conjugate().conjugated


def test_n16_pair_visits_are_reported_separately_from_exact_products():
    with o.ExactBudget(1_000_000, 512 * 1024**2) as budget:
        edge = f.original_direct_polar_edge(o.OriginalRegulator(), 0, budget=budget)
    assert hasattr(edge, 'attempted_wedge_pairs'), 'missing attempted pair receipt'
    assert 512 <= edge.attempted_wedge_pairs <= 14_014_976
    assert edge.attempted_wedge_pairs > budget.products > 0

def test_n16_auxiliary_anchor_blocks_at_unequal_and_singular_radii():
    # Evaluate separate h/k blocks against the actual original four-block
    # constructor. Opposite gamma placements differ at unequal radii.
    reg = o.OriginalRegulator((2, 1, 1, 1))
    x, y = reg.sites
    rows = o._auxiliary_polar_rows(reg, mixed=True)
    for q0, q3 in ((F(3, 5), F(4, 5)), (F(0), F(1))):
        links = {
            (x, 0): f.original_spin4_link((1, 0, 0, 0), (q0, 0, 0, q3)),
            (y, 0): f.original_spin4_link((-1, 0, 0, 0), (-q0, 0, 0, -q3)),
        }
        weights = (1, 2, 3, 4, -5, 6, -7, 8)
        values = weights + (2, 2 * q0)
        matrix = [[o.QComplex() for _ in range(8)] for _ in range(8)]
        for i, row in enumerate(rows):
            for j, terms in row:
                for key, coefficient in terms:
                    term = coefficient
                    for power, value in zip(o._auxiliary_polar_powers(key), values, strict=True):
                        term *= value**power
                    matrix[i][j] += term
        expected = o.SparseMatrix(8, tuple(
            (coord, poly * weights[4 * site_index + internal])
            for site_index, site in enumerate((x, y))
            for internal in range(4)
            for coord, poly in o.assemble_coframe(
                reg, f.original_coframe_blocks(reg, (site, 0, internal), links),
            ).entries
        ))
        assert all(expected.at(i, j) == o.Polynomial.scalar(matrix[i][j])
                   for i in range(8) for j in range(8))


@pytest.mark.parametrize('mixed', (False, True))
def test_n16_auxiliary_support_and_actual_signed_roster(mixed):
    rows = o._auxiliary_polar_rows(o.OriginalRegulator(), mixed=mixed)
    expected = {
        (0, 3): (((0, 6), (0, 6), 1), ((0, 7), (0, 7), 1),
                 ((1, 6), (1, 6), 1), ((1, 7), (1, 7), 1)),
        (3, 0): (((2, 4), (2, 4), 1), ((2, 5), (2, 5), 1),
                 ((3, 4), (3, 4), 1), ((3, 5), (3, 5), 1)),
        (1, 5): (((0, 1), (6, 7), -1),),
        (2, 4): (((6, 7), (0, 1), -1),),
        (4, 2): (((2, 3), (4, 5), -1),),
        (5, 1): (((4, 5), (2, 3), -1),),
    }
    actual = {(i, j): o._auxiliary_polar_minor_roster(rows, i, j)
              for i in range(6) for j in range(6)}
    assert {pair: value for pair, value in actual.items() if value} == expected
    assert sum(not value for value in actual.values()) == 30


def test_n16_auxiliary_minor_sign_and_both_layers_are_reserved():
    x, y, z = 1, 16, 256
    q = o.QComplex
    rows = (((0, ((x, q(2)),)), (1, ((y, q(3)),))),
            ((0, ((z, q(5)),)), (1, ((x, q(7)),))))
    with o.ExactBudget(12, 256 * 1024**2) as budget:
        actual = o._auxiliary_polar_determinant(rows, 4, budget)
    assert actual == {x + x: q(14), y + z: q(-15)}
    assert budget.products == 4
    # The terminal step needs one layer of size 2 and a 30-record
    # next-layer reservation, in addition to the fixed 4,096 slots.
    assert budget.peak_scalar_records >= 2 + 30 + 4096
    with o.ExactBudget(1, 256 * 1024**2) as budget:
        with pytest.raises(o.BudgetExceeded, match='scalar budget'):
            o._auxiliary_polar_determinant(rows, 4, budget)
    with o.ExactBudget(10, 1) as budget:
        with pytest.raises(o.BudgetExceeded, match='storage budget'):
            o._auxiliary_polar_determinant(rows, 4, budget)
        assert budget.products == 0


def test_n16_auxiliary_extracts_exact_gaussian_degree_and_checks_radial_parity():
    q = o.QComplex
    def key(*powers):
        return sum(power << (4 * index) for index, power in enumerate(powers))
    target = key(4, 0, 0, 0, 2, 0, 0, 0, 4, 2)
    other = key(2, 0, 0, 0, 4, 0, 0, 0, 4, 2)
    odd_gaussian = key(3, 1, 0, 0, 2, 0, 0, 0, 4, 2)
    polynomial = {target: q(2), other: q(99), odd_gaussian: q(77)}
    radial = {}
    o._auxiliary_polar_project(polynomial, (4, 2), 1, radial, {})
    assert radial == {(4, 2): q(6)}
    assert o._auxiliary_polar_average(radial, (F(1), F(2), F(5)), 16) == q(960)
    with pytest.raises(ValueError, match='odd radial'):
        o._auxiliary_polar_average({(3, 3): q(1)}, (F(1), F(2), F(5)), 16)


@pytest.mark.parametrize('field', ('limit', 'storage_limit', 'integer_bit_limit'))
@pytest.mark.parametrize('bad', (float('nan'), 1.0, True, 0))
def test_n16_auxiliary_refuses_invalid_caps_without_matrix(field, bad, monkeypatch):
    def unexpected(*args, **kwargs):
        pytest.fail('invalid cap reached matrix construction')
    monkeypatch.setattr(o, '_auxiliary_polar_rows', unexpected, raising=False)
    with o.ExactBudget(100, 256 * 1024**2) as budget:
        setattr(budget, field, bad)
        with pytest.raises(ValueError, match='positive exact integer'):
            f.original_auxiliary_polar_edge(o.OriginalRegulator(), 0, budget=budget)
        assert budget.products == 0 and budget.peak_payload_bytes == 0


def test_n16_auxiliary_dual_basis_and_top_degree_projection():
    q = o.QComplex
    labels, pairing = o._auxiliary_polar_basis()
    assert labels == tuple((chi, kind) for chi in ('L', 'R') for kind in ('n', 'b', 'p'))
    literal = tuple(tuple(q(12 if (i, j) == (0, 3) else 0)
                          for j in range(6)) for i in range(6))
    dual = o._auxiliary_polar_dual(literal, pairing)
    assert dual == tuple(tuple(q(3 if (i, j) == (0, 3) else 0)
                               for j in range(6)) for i in range(6))
    top_key = 8 | (4 << 32) | (4 << 36)
    radial = {}
    o._auxiliary_polar_project({top_key: q(1)}, (8, 0), 1, radial, {})
    assert radial == {(4, 4): q(105)}
    moments = o._auxiliary_polar_radial_moments()
    assert moments == (F(1), F(2), F(5), F(14), F(42))
    assert o._auxiliary_polar_average(radial, moments, 384) == q(105 * 25 * 384)


@pytest.mark.parametrize('field', ('fixed_reserve_bytes', 'products'))
def test_n16_auxiliary_refuses_invalid_accounting_state(field):
    with o.ExactBudget(100, 256 * 1024**2) as budget:
        setattr(budget, field, float('nan'))
        with pytest.raises(ValueError, match='accounting state'):
            f.original_auxiliary_polar_edge(o.OriginalRegulator(), 0, budget=budget)
        assert budget.peak_payload_bytes == 0


@pytest.mark.parametrize('route', ('direct', 'auxiliary'))
@pytest.mark.parametrize('field, value', (
    ('fixed_reserve_bytes', 0), ('fixed_reserve_bytes', float('nan')),
    ('products', -1), ('products', float('nan')),
    ('integer_products', -1), ('peak_payload_bytes', float('nan')),
))
def test_n16_shared_budget_rejects_corrupt_accounting_before_reserving(route, field, value, monkeypatch):
    def unexpected(*args, **kwargs):
        pytest.fail('invalid accounting reached reservation')
    monkeypatch.setattr(o, '_reserve_edge_records', unexpected)
    monkeypatch.setattr(o, 'reserve_scalar_records', unexpected)
    producer = getattr(f, f'original_{route}_polar_edge')
    with o.ExactBudget(100, 256 * 1024**2) as budget:
        setattr(budget, field, value)
        with pytest.raises(ValueError, match='accounting state'):
            producer(o.OriginalRegulator(), 0, budget=budget)
