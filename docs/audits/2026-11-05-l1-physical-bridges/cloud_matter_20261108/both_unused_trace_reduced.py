"""Prospective22-word reduction; SOURCE/math gates required before --all.

Only exact SAME4/TWO2 templates, actual occurrence groups, full commutator
fourth moments and original multiplicity factorials are used.
"""
from time import perf_counter
STARTED = perf_counter()
import argparse
from collections import Counter
from fractions import Fraction as F
import hashlib
from itertools import product
from math import factorial, prod
from pathlib import Path
import resource
import signal
import both_unused_trace as I
import both_unused_trace_anchor_control as A
import nearest_trace as N

ROW_CAP, PRODUCT_CAP, WHOLE_SECONDS, CASE_SECONDS = 120000, 3000000, 60, 30
PAIRINGS = (((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2)))
GUARDS = []
SCALAR_CHARGE = 0


def timeout(signum=None, frame=None):
    raise TimeoutError('whole-process60-second cap')


def budget():
    return SCALAR_CHARGE + sum(g.products for g in GUARDS)


def install_tracking():
    original = N.Guard
    class Tracked(original):
        def __init__(self, *args, **kwargs):
            super().__init__(*args, **kwargs)
            GUARDS.append(self)

        def join(self, left, right, wedge, name):
            if budget() + len(left) * len(right) > PRODUCT_CAP:
                raise RuntimeError('aggregate exterior/scalar product cap')
            return super().join(left, right, wedge, name)
    N.Guard = Tracked


def plans(S, orbits):
    result = {}
    census = Counter()
    for ii in set().union(*(orbit for _, orbit in orbits)):
        word = tuple(S.TERMS[i][2] for i in ii)
        slots = Counter(t[0] for t in word)
        assert sorted(slots.values()) == [2, 4] and set(slots) == {1, 2}
        private = next(x for x, n in slots.items() if n == 2)
        center = private ^ 3
        private_terms = tuple(t for t in word if t[0] == private)
        central = tuple(t for t in word if t[0] == center)
        assert private_terms == ((private, 0, 1, private, private),) * 2
        assert all(t[1:3] == (2, 3) for t in central) and len(central) == 4
        frame_edges = set()
        for x, k, l, u, v in word:
            mu, nu = (d for d in range(4) if d not in (k, l))
            frame_edges.update(((u, mu), (v, nu)))
        # A private plane's singleton edge is absent from every frame and
        # central collapsed curvature; conditionally its holonomy is Haar.
        private_edges = ((private, 0), (S.forward(private, 0), 1),
                         (S.forward(private, 1), 0), (private, 1))
        private_singletons = [e for e in private_edges if private_edges.count(e) == 1
                              and e not in frame_edges and e not in ((center, 2), (center, 3))]
        assert (private, 0) in private_singletons and (private, 1) in private_singletons
        templates = []
        for axis, slot in ((0, 3), (1, 4)):
            anchors = tuple(t[slot] for t in central)
            counts = Counter(anchors)
            assert set(anchors) <= {center, S.forward(center, axis)}
            assert sorted(counts.values()) in ([4], [2, 2])
            if len(counts) == 1:
                allowed = PAIRINGS
            else:
                groups = tuple(sorted(tuple(i for i, a in enumerate(anchors) if a == origin)
                                      for origin in sorted(counts)))
                assert len(groups) == 2 and all(len(g) == 2 for g in groups)
                assert groups in PAIRINGS
                allowed = (groups,)
            templates.append(allowed)
        central_factorial = prod(factorial(n) for n in Counter(central).values())
        assert central_factorial in (1, 4, 24)
        assert N.charge(S, ii) == 0
        result[ii] = (private, central, tuple(templates), central_factorial)
        census[tuple(map(len, templates)), central_factorial] += 1
    assert len(result) == 22
    print('ALL22_OCCURRENCE_TEMPLATE_CONTROL', sorted(census.items()),
          'private_singleton_erasure', 22, 'actual_central_occurrences', 4, flush=True)
    return result


def private_controls(ns):
    values = {}
    guard = N.Guard()
    old = ns['wedge']
    ns['wedge'] = lambda a, b: guard.join(a, b, old, 'factory')
    try:
        for site in (1, 2):
            polynomial = ns['square']((site, 0, 1, site, site))
            coefficient = polynomial[255 << (8 * site)]
            assert coefficient.is_ground and coefficient.const().y == 0
            # Private curvature2 cancels its action2!, exactly once.
            values[site] = F(int(coefficient.const().x), 8 ** 2 * 4 ** 4)
    finally:
        ns['wedge'] = old
    assert values == {1: F(18), 2: F(18)}
    print('PRIVATE_PAIR_CONTROLS', {x: str(v) for x, v in values.items()}, flush=True)
    return values


def evaluate(plan, private_values, curvature):
    global SCALAR_CHARGE
    started = perf_counter()
    private, central, templates, central_factorial = plan
    integer_sum = queries = 0
    for first, second in product(*templates):
        for i, j, k, l in product(range(4), repeat=4):
            if perf_counter() - started >= CASE_SECONDS:
                raise TimeoutError('one-case30-second cap')
            # Each curvature coefficient has at most two chiral terms; four
            # factors therefore use <=16 scalar term products. Charge this
            # conservative count even for zero entries or exact cache hits.
            if budget() + 16 > PRODUCT_CAP:
                raise RuntimeError('aggregate exterior/scalar product cap')
            SCALAR_CHARGE += 16
            a, b = [0] * 4, [0] * 4
            for value, block in zip((i, j), first):
                for position in block:
                    a[position] = value
            for value, block in zip((k, l), second):
                for position in block:
                    b[position] = value
            integer_sum += curvature.curv_moment(tuple(sorted(zip(a, b))))
            queries += 1
    value = private_values[private] * F(108, 32 ** 2 * central_factorial) * F(integer_sum, 2025)
    print('REDUCED_WORD', 'central_occurrences', central, 'permitted_pairings', templates,
          'central_multiplicity_factorial', central_factorial, 'curvature_queries', queries,
          'curvature_integer_sum', integer_sum, 'raw_g2_6_one_word', str(value),
          'seconds', perf_counter() - started, flush=True)
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    choice = parser.add_mutually_exclusive_group(required=True)
    choice.add_argument('--controls', action='store_true')
    choice.add_argument('--pilot', action='store_true')
    choice.add_argument('--all', action='store_true', help='prospective reviewed22-word subfamily only')
    args = parser.parse_args()
    signal.signal(signal.SIGALRM, timeout)
    signal.setitimer(signal.ITIMER_REAL, max(.001, WHOLE_SECONDS-(perf_counter()-STARTED)))
    try:
        print('CAPS', ROW_CAP, PRODUCT_CAP, WHOLE_SECONDS, CASE_SECONDS, flush=True)
        for name in ('both_unused_trace_anchor_control.py', 'both_unused_trace_fourth_control.py'):
            print('SOURCE_SHA256', name, hashlib.sha256((Path(__file__).parent/name).read_bytes()).hexdigest(), flush=True)
        S, orbits = I.inventory()
        prepared = plans(S, orbits)  # All22 provenance/matching before target.
        install_tracking()
        A.main()  # Fresh SAME4, identity, gauge-invariant Q and all100 TWO2 controls.
        _, _, _, ns = N.machinery()
        private_values = private_controls(ns)
        import l1_normalization_opposed_fourth as curvature
        assert max(map(len, curvature.L.values())) == 2
        if args.pilot:
            indices = next(ii for ii in prepared if tuple(S.TERMS[i][2] for i in ii) == I.PILOT)
            value = evaluate(prepared[indices], private_values, curvature)
            assert value == F(1161, 5)  # Independently derived one-word anchor only.
        elif args.all:
            total = F(0)
            seen = set()
            for index, (ii, orbit) in enumerate(orbits):
                assert not seen & orbit
                seen.update(orbit)
                value = evaluate(prepared[ii], private_values, curvature)
                total += len(orbit) * value
                print('SELECTED_ORBIT', index, 'words', len(orbit), 'raw_contribution', str(len(orbit)*value), flush=True)
            assert seen == set(prepared) and len(seen) == 22
            pair = total/N.Z8
            print('PARTIAL_BOTH_UNUSED_DIAGONAL', 'selected_words', 22, 'full_words', 310,
                  'raw_g2_6_subcontribution', str(total), 'normalized_pair_subcontribution_g2_squared', str(pair),
                  'raw_selected_numerator_j', '0', 'raw_selected_numerator_jj', '0',
                  'normalized_pair_subcontribution_jj_g2_squared', str(-pair*N.LOGZ_JJ),
                  'normalized_pair_subcontribution_hh_g2_squared', str(-pair*N.LOGZ_JJ/8), flush=True)
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        if not isinstance(rss, (int, float)) or rss <= 0:
            raise RuntimeError('SELF maxRSS unavailable; resource gate fails closed')
        print('RESOURCE_SUMMARY', 'total_candidate_products_with_scalar_upper_charge', budget(),
              'exterior_products', sum(g.products for g in GUARDS), 'scalar_upper_charge', SCALAR_CHARGE,
              'peak_rows', max((g.peak_rows for g in GUARDS), default=0), 'maxrss_kib', rss,
              'seconds', perf_counter()-STARTED, flush=True)


if __name__ == '__main__':
    main()
