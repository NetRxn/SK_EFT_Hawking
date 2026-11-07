"""Bounded exact Task1 controls; no full W/Haar/partition evaluator."""
from fractions import Fraction as F
from itertools import permutations

import pytest

from src.core.formulas import (
    original_gamma, original_gamma5, original_spin4_link,
    original_coframe_blocks, original_plaquette, original_action_factors,
)
from src.vestigial.original_coefficients import (
    QComplex as Q, Polynomial as P, Symbol, OriginalRegulator,
    ConventionTransport, ExteriorPolynomial, assemble_coframe, assemble_dirac,
    matrix_add, matrix_scale, matrix_multiply, matrix_dagger, identity_matrix,
    epsilon, permutation_sign, structural_certificate, determinant_support,
    local_degree_certificate, recursive_size_bytes, ScalarCost,
)

@pytest.fixture(autouse=True)
def bounded_scalar_work(request):
    # Counts every expanded polynomial coefficient product in each actual test.
    with ScalarCost(limit=1_000_000) as cost:
        yield
    print(f"SCALAR_PRODUCTS {request.node.name} {cost.products}")


ORIGIN = (0, 0, 0, 0)


def exact_links(reg):
    # Rational unit quaternions with noncommuting vector axes and distinct L/R.
    choices = ((F(3, 5), F(4, 5), 0, 0), (F(5, 13), 0, F(12, 13), 0),
               (0, 0, 0, 1), (1, 0, 0, 0))
    return {a: original_spin4_link(choices[i % 4], choices[(i + 1) % 4])
            for i, a in enumerate(reg.link_order)}


def action_value(reg, x, links, frames):
    factors = original_action_factors(reg, x, links)
    out = [P(), P()]
    for term in factors:
        val = term.coefficient
        for alpha in term.components:
            val *= frames[alpha]
        out[0 if term.t_degree == 4 else 1] += val
    return tuple(out)


def test_exact_scalar_polynomial_and_exterior_algebra():
    # Catches float conversion, coordinate aliasing, wedge signs and hidden products.
    z = Q(F(2, 3), F(-3, 7))
    assert z.storage == (2, 3, -3, 7)
    assert z * z.conjugate() == Q(F(277, 441))
    with pytest.raises(TypeError):
        Q(0.1)
    x, y = P.variable(Symbol('h', (0,))), P.variable(Symbol('J', (0,)))
    assert ((x + y) * (x - y)).evaluate({Symbol('h', (0,)): 2, Symbol('J', (0,)): 3}) == Q(-5)
    assert (x - x).terms == ()
    a, b = ExteriorPolynomial.generator(0), ExteriorPolynomial.generator(1)
    assert a * a == ExteriorPolynomial()
    assert a * b == -(b * a)
    assert (a * b).terms == ((3, P.scalar(1)),)
    cost = ScalarCost(limit=3)
    with pytest.raises(ValueError, match='scalar product budget'):
        (x + y).multiply(x + y, cost)
    assert cost.products == 3


def test_original_n16_four_block_support_and_anchor_addition():
    reg = OriginalRegulator()
    blocks = original_coframe_blocks(reg, (ORIGIN, 0, 3))
    assert [b.weight for b in blocks] == [F(1, 4), F(-1, 4), F(-1, 4), F(1, 4)]
    assert blocks[0].anchor == blocks[1].anchor == (ORIGIN, 0)
    assert blocks[2].anchor == blocks[3].anchor == ((1, 0, 0, 0), 0)
    assert [(b.bar_site, b.psi_site) for b in blocks] == [
        (ORIGIN, (1, 0, 0, 0)), ((1, 0, 0, 0), ORIGIN),
        (ORIGIN, (1, 0, 0, 0)), ((1, 0, 0, 0), ORIGIN)]
    a = assemble_coframe(reg, blocks)
    assert len(a.entries) == 16
    assert sum(len(p.terms) for _, p in a.entries) == 64
    # Hand-derived temporal gamma entry with U=q0 I+i q.sigma.
    qf0 = P.variable(Symbol('q', (ORIGIN, 0, 'R', 0)))
    qb0 = P.variable(Symbol('q', ((1, 0, 0, 0), 0, 'R', 0)))
    qf3 = P.variable(Symbol('q', (ORIGIN, 0, 'R', 3)))
    qb3 = P.variable(Symbol('q', ((1, 0, 0, 0), 0, 'R', 3)))
    assert a.at(0, 4 * reg.site_number((1, 0, 0, 0)) + 2) == (qf0 - qb0 - Q(0, 1) * (qf3 + qb3)) * F(1, 4)
    c = structural_certificate(reg)
    assert (c.components, c.block_increments, c.scalar_slot_writes) == (256, 1024, 8192)
    assert (c.coframe_slots, c.coordinate_terms, c.dirac_slots) == (4096, 16384, 512)
    assert c.dirac_row_populations == (8,) * 64
    assert len(reg.generator_order) == 128 and len(reg.link_order) == 64
    assert c.independent_su2_factors == 128
    assert reg.auxiliary_degree_bound == 64


@pytest.mark.parametrize('length,boundary', [(1, 1), (1, -1), (2, 1), (2, -1), (3, -1)])
def test_original_small_torus_boundary_addition(length, boundary):
    reg = OriginalRegulator((length, 1, 1, 1), (boundary, 1, 1, 1))
    links = exact_links(reg)
    x = (length - 1, 0, 0, 0)
    b = original_coframe_blocks(reg, (x, 0, 3), links)
    assert b[0].weight == F(boundary, 4)
    assert b[1].weight == F(-boundary, 4)
    assert b[2].weight == F(-boundary if length == 1 else -1, 4)
    a = assemble_coframe(reg, b)
    # Independent dense addition of all four supplied matrix increments.
    dense = [[P() for _ in range(4 * length)] for _ in range(4 * length)]
    for inc in b:
        for i in range(4):
            for j in range(4):
                dense[4 * reg.site_number(inc.bar_site) + i][4 * reg.site_number(inc.psi_site) + j] += inc.matrix[i][j] * inc.weight
    assert all(a.at(i, j) == dense[i][j] for i in range(4 * length) for j in range(4 * length))
    if length == 1:
        u = links[(ORIGIN, 0)]
        d = matrix_add(matrix_dagger(u), matrix_scale(u, -1))
        want = matrix_scale(matrix_add(matrix_multiply(original_gamma(3), d), matrix_multiply(d, original_gamma(3))), F(boundary, 4))
        assert tuple(tuple(a.at(i, j) for j in range(4)) for i in range(4)) == want
    with pytest.raises(ValueError):
        OriginalRegulator((0, 1, 1, 1))
    with pytest.raises(ValueError):
        OriginalRegulator(boundary_signs=(1, 1, 1, 2))


def test_original_gamma_and_printed_closed_words():
    g, g5, one = [original_gamma(i) for i in range(4)], original_gamma5(), identity_matrix(4)
    for i in range(4):
        assert matrix_dagger(g[i]) == g[i]
        for j in range(4):
            assert matrix_add(matrix_multiply(g[i], g[j]), matrix_multiply(g[j], g[i])) == matrix_scale(one, 2 if i == j else 0)
    assert matrix_multiply(matrix_multiply(matrix_multiply(g[0], g[1]), g[2]), g[3]) == g5
    m = [original_gamma(i, 'metric_M') for i in range(4)]
    assert matrix_multiply(matrix_multiply(matrix_multiply(m[0], m[1]), m[2]), m[3]) == matrix_scale(g5, -1)
    reg = OriginalRegulator((1, 1, 1, 1))
    links = exact_links(reg)
    a, b = links[(ORIGIN, 0)], links[(ORIGIN, 1)]
    printed = matrix_multiply(matrix_multiply(matrix_multiply(a, b), matrix_dagger(a)), matrix_dagger(b))
    closed = matrix_multiply(matrix_multiply(matrix_multiply(matrix_dagger(b), matrix_dagger(a)), b), a)
    assert printed != closed
    assert original_plaquette(reg, ORIGIN, 0, 1, links, 'printed') == printed
    assert original_plaquette(reg, ORIGIN, 0, 1, links, 'closed') == closed


@pytest.mark.parametrize('word', ['printed', 'closed'])
def test_original_complete_convention_dictionary_before_haar(word):
    tr = ConventionTransport('metric_M', 'source_C')
    mr = OriginalRegulator((1, 2, 1, 1), (-1, 1, -1, 1), 'metric_M', word)
    cr = tr.regulator(mr)
    assert cr.extents == (2, 1, 1, 1) and cr.boundary_signs == (1, -1, 1, -1)
    assert cr.temporal_axis == 3 and mr.temporal_axis == 0
    assert tr.couplings(F(2, 3), F(3, 5)) == (F(2, 3), F(-3, 5))
    assert tr.spinor(3) == 3 and tr.chirality('L') == 'L'
    assert tr.metric_pair((0, 2)) == (1, 3)
    assert tr.frame_pair((0, 2)) == (3, 1)
    assert tr.sigma2(F(3)) == 3
    ml = exact_links(mr)
    cl = {tr.anchor(k): v for k, v in ml.items()}
    for x in mr.sites:
        assert tr.reflect_site(mr, x) == cr.reflect_site(tr.site(x))
        assert tr.phase_label(x) == tr.site(x)
        for mu in range(4):
            assert tr.site(mr.step(x, mu)[0]) == cr.step(tr.site(x), tr.axis(mu))[0]
            assert tr.temporal_reflection_anchor(mr, (x, 0)) == (cr.reflected_anchor(tr.anchor((x, 0)))[0], True)
            for internal in range(4):
                ma, ca = (x, mu, internal), tr.composite((x, mu, internal))
                mb = original_coframe_blocks(mr, ma, ml)
                cb = original_coframe_blocks(cr, ca, cl)
                assert [(tr.site(b.bar_site), tr.site(b.psi_site), tr.anchor(b.anchor), b.weight, b.matrix) for b in mb] == [(b.bar_site, b.psi_site, b.anchor, b.weight, b.matrix) for b in cb]
                assert tr.linear_label(ma) == ca and tr.auxiliary_label(ma) == ca
    for p in permutations(range(4)):
        assert epsilon(tuple(tr.axis(i) for i in p)) == -epsilon(p)
    assert tr.berezin_sign(mr) == 1
    # Complete raw action sums, generic commuting T values, both words, before Haar.
    vals_m = {(x, mu, a): int(mu == a) + F((mu + 1) ** (a + 1) + mr.site_number(x), 17)
              for x in mr.sites for mu in range(4) for a in range(4)}
    vals_c = {tr.composite(k): v for k, v in vals_m.items()}
    sm = [P(), P()]
    sc = [P(), P()]
    for x in mr.sites:
        vm, vc = action_value(mr, x, ml, vals_m), action_value(cr, tr.site(x), cl, vals_c)
        sm = [a + b for a, b in zip(sm, vm)]
        sc = [a + b for a, b in zip(sc, vc)]
    assert sm[0] != P()
    assert sm[1] != P()  # unsquared g2 control cannot hide a wrong coupling sign
    assert sc == [sm[0], -sm[1]]
    assert sc[0] * F(2, 3) + sc[1] * F(-3, 5) == sm[0] * F(2, 3) + sm[1] * F(3, 5)
    with pytest.raises(ValueError):
        OriginalRegulator(word='unlabeled')


def test_original_local_degree_certificate_and_adverse_noncentered_frame():
    reg = OriginalRegulator()
    frames = [assemble_coframe(reg, original_coframe_blocks(reg, (ORIGIN, mu, a))).to_exterior(reg)
              for mu in range(4) for a in range(4)]
    cert = local_degree_certificate(reg, ORIGIN, frames)
    assert cert.degree_bound == 8 and not cert.vanishes_above(8) and cert.vanishes_above(9)
    assert cert.minimum_center_generators == 1
    assert reg.auxiliary_degree_bound == 64  # certificate does not change production bound
    # Boolean exterior multiplication on a real centered T proves ninth support empty.
    support = {0}
    # Project onto the eight center generators: <=256 Boolean states, an
    # upper support envelope valid for every neighbor/anchor choice.
    masks = {mask & cert.center_mask for f in frames for mask, _ in f.terms}
    for _ in range(9):
        support = {a | b for a in support for b in masks if not a & b}
    assert not support
    transformed = [frames[0] + frames[1] * F(2, 3)]
    assert local_degree_certificate(reg, ORIGIN, transformed).degree_bound == 8
    foreign = ExteriorPolynomial.generator(8) * ExteriorPolynomial.generator(9)
    with pytest.raises(ValueError, match='center'):
        local_degree_certificate(reg, ORIGIN, transformed + [foreign])
    one = OriginalRegulator((1, 1, 1, 1))
    fs = [assemble_coframe(one, original_coframe_blocks(one, (ORIGIN, mu, a))).to_exterior(one)
          for mu in range(4) for a in range(4)]
    assert local_degree_certificate(one, ORIGIN, fs).degree_bound == 4
    assert one.auxiliary_degree_bound == 4


def test_original_determinant_support_partition_and_reachability():
    reg = OriginalRegulator()
    cert = determinant_support(reg)
    assert cert.block_sizes == (16, 16, 16, 16)
    assert cert.row_sign * cert.column_sign == 1
    assert sorted(cert.row_order) == sorted(cert.column_order) == list(range(64))
    assert cert.layer_populations == (1, 8, 28, 164, 429, 1628, 2856, 9112, 12610, 11408, 8008, 4368, 1820, 560, 120, 16, 1)
    assert cert.total_reachable_masks == 53137 and cert.transitions_per_block == 200076
    assert cert.transitions_all_blocks == 800304
    # Every actual symbolic matrix entry lies inside its declared directed block.
    matrix = assemble_dirac(reg)
    rows = {v: i // 16 for i, v in enumerate(cert.row_order)}
    cols = {v: i // 16 for i, v in enumerate(cert.column_order)}
    assert len(matrix.entries) == 512
    assert all(rows[i] == cols[j] for (i, j), _ in matrix.entries)
    assert permutation_sign(cert.row_order) == cert.row_sign
    with pytest.raises(ValueError, match='bipartite'):
        determinant_support(OriginalRegulator((3, 2, 2, 2)))


def test_recursive_storage_accounting_unique_payloads():
    value = Q(F((1 << 1023) + 1, 3), F(7, 11))
    payload = {0: value, 1: value}
    assert recursive_size_bytes(payload) > recursive_size_bytes({}) + recursive_size_bytes(value)
    assert recursive_size_bytes((value, value)) < recursive_size_bytes((value, Q(F((1 << 1023) + 1, 3), F(7, 11))))


def test_scalar_cost_scope_counts_expanded_coefficients_and_refuses():
    x, y = P.variable(Symbol('h', (1,))), P.variable(Symbol('h', (2,)))
    with ScalarCost(limit=4) as cost:
        result = (x + y) * (x - y)
    assert cost.products == 4 and len(result.terms) == 2
    with ScalarCost(limit=3):
        with pytest.raises(ValueError, match='scalar product budget'):
            (x + y) * (x - y)


def test_complex_source_conjugation_and_real_quaternion_coordinates():
    # A complex J must not silently acquire a reality assumption under dagger.
    j = P.variable(Symbol('J', (ORIGIN, 0, 0)))
    h = P.variable(Symbol('h', (ORIGIN, 0, 0)))
    assert j.conjugate() != j
    assert j.conjugate().conjugate() == j
    assert h.conjugate() == h
    assert j.conjugate().evaluate({Symbol('J', (ORIGIN, 0, 0)): Q(2, 3)}) == Q(2, -3)


def test_regulator_is_immutable_after_caller_mutates_input():
    extents, boundaries = [2, 2, 2, 2], [1, 1, 1, 1]
    reg = OriginalRegulator(extents, boundaries)
    extents[0], boundaries[0] = 99, -1
    assert reg.volume == 16 and reg.boundary_signs == (1, 1, 1, 1)


def test_original_dropped_increment_and_collapsed_anchor_controls():
    reg = OriginalRegulator((1, 1, 1, 1))
    identity_links = {a: identity_matrix(4) for a in reg.link_order}
    blocks = original_coframe_blocks(reg, (ORIGIN, 0, 3), identity_links)
    assert assemble_coframe(reg, blocks).entries == ()
    assert assemble_coframe(reg, blocks[:-1]).entries != ()
    # All four same-slot increments cancel; assigning the last block cannot pass.
    assert assemble_coframe(reg, blocks[-1:]).entries != ()
    n16 = OriginalRegulator()
    full = assemble_coframe(n16, original_coframe_blocks(n16, (ORIGIN, 0, 3)))
    symbols = {symbol for _, value in full.entries for key, _ in value.terms for symbol in key}
    assert {(s.index[0], s.index[1]) for s in symbols} == {(ORIGIN, 0), ((1, 0, 0, 0), 0)}


def test_original_independent_g1_and_unsquared_g2_prehaar_fixture():
    # Nonzero raw g1 determinant and unsquared g2, with no integrated oracle.
    reg = OriginalRegulator((1, 1, 1, 1))
    vals = {(ORIGIN, mu, a): int(mu == a) + F((mu + 1) ** (a + 1), 17)
            for mu in range(4) for a in range(4)}
    s4, s2 = action_value(reg, ORIGIN, exact_links(reg), vals)
    # det(I + Vandermonde/17), derived by independent permutation definition.
    determinant = F(0)
    for perm in permutations(range(4)):
        term = F(permutation_sign(perm))
        for row, col in enumerate(perm):
            term *= vals[ORIGIN, row, col]
        determinant += term
    assert determinant != 0 and s4 == P.scalar(determinant)
    assert s2 != P()


def test_original_action_full_incidence_support_and_eight_anchors():
    from src.vestigial.original_coefficients import factor_support
    reg = OriginalRegulator()
    factors = original_action_factors(reg, ORIGIN, exact_links(reg))
    cosmological = [f for f in factors if f.t_degree == 4]
    curvature = [f for f in factors if f.t_degree == 2]
    assert len(cosmological) == 24 and len(curvature) == 384
    assert len(cosmological) * reg.volume == 384
    assert len(curvature) * reg.volume == 6144
    scope4 = factor_support(reg, cosmological[0])
    scope2 = factor_support(reg, curvature[0])
    assert len(scope4.sites) == 5 and len(scope4.anchors) == 8
    assert len(scope2.sites) == 3 and len(scope2.anchors) == 8
    assert len(scope4.generators) == 40 and len(scope2.generators) == 24
    anchors = set().union(*(set(factor_support(reg, f).anchors) for f in factors))
    assert len(anchors) == 20
    assert all(len(factor_support(reg, f).anchors) == 8 for f in curvature)


@pytest.mark.parametrize('word', ['printed', 'closed'])
def test_original_actual_c3_unsquared_quadratic_coefficient(word):
    # Actual compact-link control from FiniteGrassmannSourceAuxiliary, not g2^4.
    reg = OriginalRegulator((3, 3, 3, 3), word=word)
    links = {a: identity_matrix(4) for a in reg.link_order}
    links[ORIGIN, 0] = original_spin4_link((0, 0, 0, 1), (1, 0, 0, 0))
    target = tuple(sorted(((ORIGIN, 2, 0), (ORIGIN, 3, 1))))
    coefficient = sum((f.coefficient for f in original_action_factors(reg, ORIGIN, links)
                       if tuple(sorted(f.components)) == target), P())
    assert coefficient == P.scalar(-2)


def test_original_reflection_matrix_and_legacy_quaternion_map():
    from src.vestigial.original_coefficients import legacy_quaternion_to_c
    c, m = OriginalRegulator(), OriginalRegulator(convention='metric_M')
    assert c.reflection_matrix == original_gamma(3)
    assert m.reflection_matrix == original_gamma(0, 'metric_M') == c.reflection_matrix
    old = (F(3, 5), F(4, 5), 0, 0)
    mapped = legacy_quaternion_to_c(old)
    assert mapped == (F(3, 5), F(-4, 5), 0, 0)
    # Old minus-i matrix, hand written, agrees with canonical coordinate map.
    u = original_spin4_link(mapped, (1, 0, 0, 0))
    assert u[0][1] == P.scalar(Q(0, F(-4, 5)))
    assert u[1][0] == P.scalar(Q(0, F(-4, 5)))


def test_original_berezin_output_order_on_supplied_permutation_matrix():
    from src.vestigial.original_coefficients import SparseMatrix
    reg = OriginalRegulator((1, 1, 1, 1))
    # Pure four-pair algebra control; no original action/W or group integral.
    matrix = SparseMatrix(4, tuple(((i, j), P.scalar(i + 1)) for i, j in enumerate((2, 0, 3, 1))))
    form = matrix.to_exterior(reg)
    coefficient = ExteriorPolynomial(((0, P.scalar(1)),))
    # The top coefficient of exp(bar M psi) is the fourth power /4!.
    for _ in range(4):
        coefficient = coefficient * form
    assert dict(coefficient.terms)[255] * F(1, 24) == P.scalar(-24)
    assert reg.generator_order == tuple((ORIGIN, kind, i) for kind, i in
        (('bar', 0), ('bar', 1), ('psi', 0), ('psi', 1),
         ('bar', 2), ('bar', 3), ('psi', 2), ('psi', 3)))


def test_original_explicit_cut_is_independent_of_unreflected_convention():
    c3 = OriginalRegulator((1, 1, 1, 1))
    p0 = OriginalRegulator((1, 1, 1, 1), temporal_axis=0)
    assert c3.temporal_axis == 3 and p0.temporal_axis == 0
    assert c3.gamma == p0.gamma and c3.gamma5 == p0.gamma5
    assert p0.reflection_matrix == original_gamma(0)
    links = exact_links(c3)
    for mu in range(4):
        for a in range(4):
            assert original_coframe_blocks(c3, (ORIGIN, mu, a), links) == original_coframe_blocks(p0, (ORIGIN, mu, a), links)
    assert original_action_factors(c3, ORIGIN, links) == original_action_factors(p0, ORIGIN, links)
    # Dictionary transports the chosen world cut, not a hardwired convention default.
    tr = ConventionTransport('source_C', 'metric_M')
    assert tr.regulator(p0).temporal_axis == 1
    assert tr.regulator(c3).temporal_axis == 0
    with pytest.raises(ValueError, match='temporal'):
        OriginalRegulator(temporal_axis=4)
    with pytest.raises(ValueError, match='temporal'):
        OriginalRegulator(temporal_axis=True)


def test_r2_actual_original_coframe_last_power_and_first_zero():
    reg = OriginalRegulator((1, 1, 1, 1))
    u = original_spin4_link((0, 0, 0, 1), (0, 0, 0, 1))
    links = {anchor: u for anchor in reg.link_order}
    frame = assemble_coframe(reg, original_coframe_blocks(reg, (ORIGIN, 0, 3), links)).to_exterior(reg)
    cert = local_degree_certificate(reg, ORIGIN, [frame])
    p = ExteriorPolynomial(((0, P.scalar(1)),))
    for _ in range(4):
        p = p * frame
    assert p.terms == ((255, P.scalar(24)),)
    assert cert.degree_bound == 4
    assert not cert.vanishes_above(4)
    assert cert.vanishes_above(5)
    assert (p * frame).terms == ()
    assert not cert.production_authorized and reg.auxiliary_degree_bound == 4
    n16 = OriginalRegulator()
    nf = assemble_coframe(n16, original_coframe_blocks(n16, (ORIGIN, 0, 3))).to_exterior(n16)
    nc = local_degree_certificate(n16, ORIGIN, [nf])
    assert nc.degree_bound == 8 and not nc.vanishes_above(8) and nc.vanishes_above(9)
    assert n16.auxiliary_degree_bound == 64 and not nc.production_authorized


def test_r2_sparse_matrix_canonical_duplicate_add_cancel_and_mutation():
    from src.vestigial.original_coefficients import SparseMatrix
    reg = OriginalRegulator((1, 1, 1, 1))
    coordinate = [0, 0]
    entries = [[coordinate, P.scalar(1)], [[0, 0], P.scalar(2)], [[1, 1], 3], [[1, 1], -3]]
    matrix = SparseMatrix(4, entries)
    assert matrix.at(0, 0) == P.scalar(3)
    assert matrix.at(1, 1) == P()
    assert matrix.entries == (((0, 0), P.scalar(3)),)
    assert matrix.to_exterior(reg).terms == ((5, P.scalar(3)),)
    coordinate[0] = 3
    entries.clear()
    assert matrix.at(0, 0) == P.scalar(3)
    assert matrix.to_exterior(reg).terms == ((5, P.scalar(3)),)
    assert hash(matrix)
    assert SparseMatrix(0, []).entries == ()


@pytest.mark.parametrize('size,entries', [(-1, ()), (True, ()), (1.0, ()),
    (4, (((-1, 0), 1),)), (4, (((4, 0), 1),)), (4, (((True, 0), 1),)),
    (4, (((0, 1.0), 1),)), (4, (((0,), 1),)), (4, (((0, 0), 'bad'),))])
def test_r2_sparse_matrix_invalid_domains(size, entries):
    from src.vestigial.original_coefficients import SparseMatrix
    with pytest.raises((ValueError, TypeError)):
        SparseMatrix(size, entries)


def test_r2_deeply_frozen_symbol_and_public_factor_labels():
    from src.vestigial.original_coefficients import BlockIncrement, ActionFactor, GeneratorLinkSupport
    nested = [[0, 0, 0, 0], 1, 'L', 0]
    symbol = Symbol('q', nested)
    polynomial = P.variable(symbol)
    before = hash(symbol)
    nested[0][0] = 7
    nested.clear()
    assert symbol.index == (ORIGIN, 1, 'L', 0) and hash(symbol) == before
    assert polynomial.evaluate({symbol: 2}) == Q(2)
    alpha, anchor = [[0, 0, 0, 0], 0, 3], [[0, 0, 0, 0], 0]
    dense = [list(row) for row in identity_matrix(4)]
    inc = BlockIncrement(alpha, [0]*4, [0]*4, anchor, F(1, 4), dense)
    factor = ActionFactor(2, [alpha, alpha], P.scalar(1), [anchor])
    support = GeneratorLinkSupport([[ORIGIN, 'bar', 0]], [anchor], [[0]*4])
    alpha[0][0] = 9
    anchor[0][0] = 9
    dense[0][0] = P.scalar(2)
    assert inc.alpha == (ORIGIN, 0, 3) and inc.anchor == (ORIGIN, 0)
    assert inc.matrix == identity_matrix(4)
    assert factor.components == ((ORIGIN, 0, 3),)*2
    assert factor.anchors == support.anchors == ((ORIGIN, 0),)
    assert hash(factor) and hash(support) and hash(inc)
    with pytest.raises((ValueError, TypeError)):
        Symbol('q', ({'mutable': 1},))


@pytest.mark.parametrize('bad', [((1,), (2, 3)), ((1, 2), (3,)), ((), ()), ((1,), ())])
def test_r2_dense_matrix_ragged_and_zero_width_refusal(bad):
    for call in (lambda: matrix_dagger(bad),
                 lambda: matrix_multiply(((1, 1),), bad),
                 lambda: matrix_multiply(bad, ((1,),)),
                 lambda: matrix_add(bad, bad)):
        with pytest.raises(ValueError):
            call()


def test_r2_dense_rectangular_and_intentional_empty_behavior():
    a, b = ((1, 2, 3), (4, 5, 6)), ((7, 8), (9, 10), (11, 12))
    assert matrix_multiply(a, b) == ((P.scalar(58), P.scalar(64)), (P.scalar(139), P.scalar(154)))
    assert matrix_dagger(((Q(1, 2), Q(3, -4)),)) == ((P.scalar(Q(1, -2)),), (P.scalar(Q(3, 4)),))
    assert matrix_multiply((), ()) == matrix_dagger(()) == matrix_add((), ()) == ()
    with pytest.raises(ValueError):
        matrix_multiply((), ((1,),))


@pytest.mark.parametrize('bad_shape', [(4, 5), (5, 4), (3, 4), (4, 3)])
def test_r2_supplied_spin4_links_must_be_exact_four_by_four(bad_shape):
    reg = OriginalRegulator((1, 1, 1, 1))
    rows, cols = bad_shape
    links = {a: tuple(tuple(int(i == j) for j in range(cols)) for i in range(rows)) for a in reg.link_order}
    with pytest.raises(ValueError, match='4'):
        original_coframe_blocks(reg, (ORIGIN, 0, 3), links)
    with pytest.raises(ValueError, match='4'):
        original_plaquette(reg, ORIGIN, 0, 1, links)


def test_r2_quaternion_coordinates_use_actual_real_involution():
    j = P.variable(Symbol('J', (0,)))
    for nonreal in (Q(0, 1), j, P.scalar(Q(1, 2)), P.scalar(1) + j):
        with pytest.raises(ValueError, match='real'):
            original_spin4_link((nonreal, 0, 0, 0), (1, 0, 0, 0))
        with pytest.raises(ValueError, match='real'):
            original_spin4_link((1, 0, 0, 0), (nonreal, 0, 0, 0))
    q = P.variable(Symbol('q', (ORIGIN, 0, 'L', 0)))
    h = P.variable(Symbol('h', (0,)))
    real = j + j.conjugate() + h*q + F(2, 3)
    assert real.conjugate() == real
    ambient = original_spin4_link((real, q, h, F(2, 3)), (1, 0, 0, 0))
    assert len(ambient) == 4  # no new sphere-normalization requirement


def test_r2_actual_n16_coframe_eighth_power_nonzero_ninth_zero():
    reg = OriginalRegulator()
    u = original_spin4_link((0, 0, 0, 1), (0, 0, 0, 1))
    links = {anchor: u for anchor in reg.link_order}
    frame = assemble_coframe(reg, original_coframe_blocks(reg, (ORIGIN, 0, 3), links)).to_exterior(reg)
    p = ExteriorPolynomial(((0, P.scalar(1)),))
    for _ in range(8):
        p = p * frame
    # The two 4x4 hopping blocks are -i gamma3 diag(sigma3,sigma3)/2.
    # Their 8x8 determinant is 1/256; 8!/256=315/2 in the stated top order.
    assert p.terms == ((255 | (255 << 64), P.scalar(F(315, 2))),)
    assert (p * frame).terms == ()
    cert = local_degree_certificate(reg, ORIGIN, [frame])
    assert not cert.vanishes_above(8) and cert.vanishes_above(9)
