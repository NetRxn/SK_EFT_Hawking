"""Candidate bounded nearest bare-T pair, closed four-site pureg2.

Controls/pilot only until independent review. --orbit N is a resumable
individual representative, never a complete-support acceptance assertion.
"""
from time import perf_counter
STARTED = perf_counter()  # Includes subsequent imports, all controls and output.
import argparse
import ast
from collections import Counter
from contextlib import redirect_stdout
from fractions import Fraction as F
from functools import cache
import hashlib
import io
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
OLD = HERE.parents[1] / '2026-10-17-publication-substance-construction'
sys.path.insert(0, str(OLD))
ROW_CAP, PRODUCT_CAP = 120000, 3000000
TOP = (1 << 32) - 1
Q = {195: -6, 85: -3, 153: -3, 102: -3, 170: -3, 60: -6}
E = (0, 0, 1, -1)
Z8 = F(1252309350145403, 2123366400)
# Existing reviewed uniform fixed-basis source convention, also consumed in
# source_jet_reweight.py. This is a source j jet, with h=2sqrt(2)j.
LOGZ_JJ = F(954400425849600, 113846304558673)


def wall_guard():
    if perf_counter() - STARTED >= 180:
        raise RuntimeError('whole-process 180-second cap')


def charge(nearest, indices):
    return sum(-E[nearest.TERMS[i][2][1]] - E[nearest.TERMS[i][2][2]] for i in indices)


def machinery():
    # Import the unchanged enumerator and local tensor without their diagnostic
    # stdout. Extract only unchanged imports/function definitions from the
    # archived private-pair module, avoiding its unrelated 33-word top-level run.
    with redirect_stdout(io.StringIO()):
        import l1_nearest_classes as nearest
        import l1_transverse_top as transverse
        import l1_direct_a_haar as haar
        tree = ast.parse((OLD / 'l1_equal_time_private_pairs.py').read_text())
        namespace = {}
        selected = [n for n in tree.body if isinstance(n, (ast.Import, ast.ImportFrom, ast.FunctionDef))]
        exec(compile(ast.Module(body=selected, type_ignores=[]),
                     str(OLD / 'l1_equal_time_private_pairs.py'), 'exec'), namespace)
    return nearest, transverse, haar, namespace


def source_tensor(transverse, haar):
    mean = {}
    for mask, polynomial in transverse.G.items():
        z = tuple(sum(F(int(getattr(c, k))) * transverse.haar_moment(e[:4]) *
                      transverse.haar_moment(e[4:]) for e, c in polynomial.items()) for k in ('x', 'y'))
        if any(z):
            mean[mask] = z
    trace = {m: (F(int(c.const().x)), F(int(c.const().y))) for m, c in transverse.trace.items()}
    assert mean == trace == {m: (F(8 * c), F(0)) for m, c in Q.items()}
    assert transverse.top(transverse.wedge(transverse.trace, transverse.trace)) == 27
    # transverse.top divides by256; Q=trace/8 gives top(Q Q)=108.
    # The source interface's closed ordering is B† A† B A. The forward
    # commutator A B A† B† is a separate control, not silently relabeled.
    commutators = (
        haar.qproduct(haar.adj(haar.B), haar.adj(haar.A), haar.B, haar.A)[1:],
        haar.qproduct(haar.A, haar.B, haar.adj(haar.A), haar.adj(haar.B))[1:],
    )

    @cache
    def moment(components, exponents, which, order=0):
        polynomial = haar.R.one
        for c in components:
            polynomial *= commutators[order][c]
        for q, power in zip(haar.A if which == 0 else haar.B, exponents, strict=True):
            polynomial *= q ** power
        return haar.integral(polynomial)[0]

    zero = (0,) * 4
    assert all(moment((i, j), zero, 0) == (F(2, 9) if i == j else 0)
               for i in range(3) for j in range(3))
    tensor = {}
    for i in range(6):
        for j in range(6):
            left = tuple(k % 3 for k in (i, j) if k < 3)
            right = tuple(k % 3 for k in (i, j) if k >= 3)
            values = {}
            for mask, polynomial in transverse.G.items():
                real = imag = F(0)
                for exponents, coefficient in polynomial.items():
                    first = moment(left, exponents[:4], 0) * moment(right, exponents[4:], 0)
                    second = moment(left, exponents[:4], 1) * moment(right, exponents[4:], 1)
                    forward_first = moment(left, exponents[:4], 0, 1) * moment(right, exponents[4:], 0, 1)
                    forward_second = moment(left, exponents[:4], 1, 1) * moment(right, exponents[4:], 1, 1)
                    assert first == forward_first and second == forward_second
                    # Both physical collapsed-source diagonal contributions.
                    weight = (first + second) / 16
                    assert first == second
                    real += int(coefficient.x) * weight
                    imag += int(coefficient.y) * weight
                if real or imag:
                    values[mask] = (real, imag)
            expected = {m: (F(49, 216) * c, F(0)) for m, c in Q.items()} if i == j else {}
            assert values == expected, (i, j, values)
            tensor[i, j] = values
    print('SOURCE_CONTROL Q', sorted(Q.items()), 'Q_squared_top', 108,
          'tensor_slot_supports', sorted(Counter(map(len, tensor.values())).items()),
          'diagonal_factor', '49/216', 'independence_poison_ratio', '48/49',
          'closed_order', 'Bdag_Adag_B_A', 'forward_order_control', 'PASS', flush=True)


def support_control(nearest):
    assert len(nearest.out) == len(set(nearest.out)) == 128
    for indices in nearest.out:
        word = [nearest.TERMS[i][2] for i in indices]
        counts = Counter(word)
        assert sorted(counts.values()) == [2, 2, 2]
        active = 0 if (0, 2) in nearest.links(indices) else 1
        unused = active ^ 1
        assert all((active, d) in nearest.links(indices) for d in (2, 3))
        assert all((unused, d) not in nearest.links(indices) for d in (2, 3))
        frames, planes = Counter(), {}
        for x, k, l, u, v in counts:
            m, n = [d for d in range(4) if d not in (k, l)]
            frames.update(((u, m), (u, m), (v, n), (v, n)))
            planes[x, k, l] = Counter(((x, k), (nearest.forward(x, k), l),
                                      (nearest.forward(x, l), k), (x, l)))
        assert sorted(frames.values()) == [2] * 6
        use = frames.copy()
        use.update(((active, 2), (active, 3)))
        for edges in planes.values():
            use.update(edges)
        history = []
        while planes:
            for plane, edges in sorted(planes.items()):
                if any(n == 1 and use[z] == 1 for z, n in edges.items()):
                    use.subtract(edges)
                    del planes[plane]
                    history.append(plane)
                    break
            else:
                break
        assert len(history) == 2 and set(planes) == {(active, 2, 3)}
        # Scalar Q commutator contraction is independent of every transport.
        assert all((active, d) not in frames for d in (2, 3))
    assert len(nearest.orbits) == 32
    print('SUPPORT_CONTROL unordered_words', 128, 'orbits', 32,
          'three_squared_terms', 128, 'private_erasure_two_planes', 128,
          'six_distinct_paired_transports', 128, flush=True)


class Guard:
    def __init__(self, product_offset=0):
        self.products = 0
        self.product_offset = product_offset
        self.peak_rows = 0
        self.stages = []
        self.factory_calls = self.factory_products = 0
        self.final_calls = self.final_products = 0

    def join(self, left, right, wedge, name):
        wall_guard()
        products = len(left) * len(right)
        # Conservative proof before allocation: at most one output key per
        # candidate. This intentionally stricter admission is sufficient here.
        if products > ROW_CAP or self.product_offset + self.products + products > PRODUCT_CAP:
            raise RuntimeError(('preallocation cap', name, products, self.products))
        self.products += products
        result = wedge(left, right)
        assert len(result) <= products <= ROW_CAP
        self.peak_rows = max(self.peak_rows, len(left), len(right), len(result))
        if name == 'factory':
            self.factory_calls += 1
            self.factory_products += products
        else:
            self.final_calls += 1
            self.final_products += products
            self.stages.append((name, len(left), len(right), products, len(result)))
        return result


def representative(nearest, ns, orbit_index, product_offset=0):
    wall_guard()
    indices = sorted(nearest.orbits)[orbit_index]
    word = [nearest.TERMS[i][2] for i in indices]
    active = 0 if (0, 2) in nearest.links(indices) else 1
    labels = sorted(set(word))
    central = next(t for t in labels if t[:3] == (active, 2, 3))
    remote = [t for t in labels if t != central]
    guard = Guard(product_offset)
    original_wedge = ns['wedge']
    # The unchanged archived factories resolve their globals from ns. Guard
    # every actual wedge call BEFORE frame_pair/square allocate new factors.
    # Their original exact caches remain active; reused values incur no new
    # factory calls. Restore the binding before the final explicit joins.
    ns['wedge'] = lambda a, b: guard.join(a, b, original_wedge, 'factory')
    try:
        factors = [ns['square'](t) for t in remote]
        local = ns['square'](central)
    finally:
        ns['wedge'] = original_wedge
    assert all(c.is_ground for factor in factors + [local] for c in factor.values())
    source0 = {m: ns['R'](c) for m, c in Q.items()}
    source1 = {m << 8: ns['R'](c) for m, c in Q.items()}
    guard.peak_rows = max(guard.peak_rows, *map(len, factors + [local]))
    sources = guard.join(source0, source1, ns['wedge'], 'Q0_Q1')
    pair = guard.join(*factors, ns['wedge'], 'remote_square_pair')
    rest = guard.join(sources, pair, ns['wedge'], 'source_remote_pair')
    # Exact complement lookup closes all32 original generators. Each lookup is
    # charged conservatively as a product, including missing complements.
    assert product_offset + guard.products + len(local) <= PRODUCT_CAP
    guard.products += len(local)
    guard.final_products += len(local)
    raw = ns['R'].zero
    for mask, coefficient in local.items():
        complement = TOP ^ mask
        if complement in rest:
            raw += coefficient * rest[complement] * ns['wedge_sign'](mask, complement)
    assert raw.is_ground and raw.const().y == 0
    denominator = 8 ** 6 * 4 ** 12 * 2 ** 3
    value = F(int(raw.const().x), denominator) * F(196, 27)
    orbit = {nearest.transform(indices, dx, swap) for dx in (0, 1) for swap in (0, 1)}
    print('REPRESENTATIVE', orbit_index, 'orbit_size', len(orbit), 'word', word,
          'square_rows', [len(f) for f in factors] + [len(local)],
          'stages', guard.stages, 'peak_rows', guard.peak_rows,
          'candidate_products', guard.products, 'raw_integer', int(raw.const().x),
          'factory_calls', guard.factory_calls, 'factory_products', guard.factory_products,
          'final_wedge_calls', guard.final_calls, 'final_products_with_lookup', guard.final_products,
          'denominator', denominator, 'raw_g2_6', str(value),
          'naive_independence_poison', str(value * F(48, 49)), flush=True)
    return {'indices': indices, 'orbit': orbit, 'raw': value,
            'products': guard.products, 'peak_rows': guard.peak_rows}


def complete_target(nearest, ns):
    """Prospective complete run; requires independent source/math acceptance."""
    seen = set()
    raw = raw_j = raw_jj = F(0)
    charges = Counter()
    products = peak = 0
    for index in range(32):
        wall_guard()
        record = representative(nearest, ns, index, products)
        assert not seen & record['orbit']
        seen.update(record['orbit'])
        raw += len(record['orbit']) * record['raw']
        # Evaluate actual charges for EVERY word: transverse exchange may flipq.
        for indices in record['orbit']:
            q = charge(nearest, indices)
            charges[q] += 1
            raw_j += q * record['raw']
            raw_jj += q * q * record['raw']
        products += record['products']
        peak = max(peak, record['peak_rows'])
        assert products <= PRODUCT_CAP and peak <= ROW_CAP
    assert seen == set(nearest.out) and len(seen) == 128
    assert raw_j == 0
    # This is a normalized fixed-bare pair jet; covariance interpretation also
    # requires the one-point/source-jet subtraction to be proved zero.
    pair_jj = raw_jj / Z8 - (raw / Z8) * LOGZ_JJ
    print('FULL_NEAREST_PAIR zero_source_raw_g2_6', str(raw),
          'normalized_pair_times_g2_squared', str(raw / Z8),
          'raw_j', str(raw_j), 'raw_jj', str(raw_jj),
          'normalized_pair_jj_times_g2_squared', str(pair_jj),
          'normalized_pair_hh_times_g2_squared', str(pair_jj / 8),
          'charges', sorted(charges.items()), 'words', len(seen), 'orbits', 32,
          'candidate_products_total', products, 'peak_rows', peak, flush=True)
    wall_guard()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    choice = parser.add_mutually_exclusive_group(required=True)
    choice.add_argument('--controls', action='store_true')
    choice.add_argument('--pilot', action='store_true')
    choice.add_argument('--orbit', type=int, choices=range(32))
    choice.add_argument('--all', action='store_true', help='prospective reviewed complete128-word target')
    args = parser.parse_args()
    print('CAPS', ROW_CAP, PRODUCT_CAP, flush=True)
    for name in ('l1_nearest_classes.py', 'l1_transverse_top.py',
                 'l1_direct_a_haar.py', 'l1_equal_time_private_pairs.py'):
        print('SOURCE_SHA256', name, hashlib.sha256((OLD / name).read_bytes()).hexdigest(), flush=True)
    nearest, transverse, haar, ns = machinery()
    source_tensor(transverse, haar)
    support_control(nearest)
    if args.all:
        complete_target(nearest, ns)
    elif not args.controls:
        representative(nearest, ns, 0 if args.pilot else args.orbit)
    wall_guard()
    print('ELAPSED_SECONDS', round(perf_counter() - STARTED, 6), flush=True)


if __name__ == '__main__':
    main()
