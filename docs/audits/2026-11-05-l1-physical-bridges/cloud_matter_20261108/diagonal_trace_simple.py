"""Guarded128-word sub-contribution to bare diagonal T0 T3, not full310."""
from time import perf_counter
STARTED = perf_counter()
import argparse
from collections import Counter
from contextlib import redirect_stdout
from fractions import Fraction as F
import hashlib
import io
from itertools import product
from math import factorial, prod
from pathlib import Path
import nearest_trace as base

ROW_CAP, PRODUCT_CAP, WHOLE_SECONDS = 120000, 3000000, 180
assert (base.ROW_CAP, base.PRODUCT_CAP) == (ROW_CAP, PRODUCT_CAP)
NEAREST_SHA256 = 'b51f77f8f7cdd1ee27285ef59aeb0915cc736d5a88cc938500c43cce8f1b72b8'


def wall_guard():
    if perf_counter() - STARTED >= WHOLE_SECONDS:
        raise RuntimeError('whole-process180-second cap')


class Guard(base.Guard):
    def join(self, *args, **kwargs):
        wall_guard()
        return super().join(*args, **kwargs)


def images(diagonal, indices):
    return {diagonal.transform(indices, dx, world_swap, transverse_swap)
            for dx, world_swap, transverse_swap in product((0, 3), (0, 1), (0, 1))}


def support_control(diagonal):
    all_words = set(diagonal.out)
    assert len(diagonal.out) == len(all_words) == 310
    partitions = Counter(tuple(sorted(Counter(ii).values())) for ii in all_words)
    assert partitions == {(1, 1, 1, 1, 1, 1): 128, (1, 1, 1, 1, 2): 34,
                          (2, 2, 2): 140, (2, 4): 8}
    ordered = sum(factorial(6) // prod(factorial(n) for n in Counter(ii).values()) for ii in all_words)
    assert ordered == 117120
    # Independent ordered-state DP, rather than reweighting the same multiset
    # enumerator. Historical92160 belongs to odd-link H23 cross sources.
    import l1_interacting_support as support
    halves = support.half(3)
    dp_even = support.match(halves, 0, (4, 8, 8, 4))[0]
    cross_parity = support.link(0, 2) ^ support.link(0, 3) ^ support.link(3, 2) ^ support.link(3, 3)
    dp_cross = support.match(halves, cross_parity, (4, 8, 8, 4))[0]
    assert ordered == dp_even == 117120 and dp_cross == 92160
    selected = {ii for ii in all_words if sorted(Counter(ii).values()) == [2, 2, 2]
                and tuple(sum((x, a) in diagonal.links(ii) for a in (2, 3)) for x in (0, 3))
                in ((2, 0), (0, 2))}
    assert len(selected) == 128 and len(all_words - selected) == 182
    assert not selected & (all_words - selected)
    orbits = {}
    for ii in selected:
        orbit = images(diagonal, ii)
        assert orbit <= selected
        orbits[min(orbit)] = orbit
        word = [diagonal.TERMS[i][2] for i in ii]
        active = 0 if (0, 2) in diagonal.links(ii) else 3
        unused = active ^ 3
        assert all((active, d) in diagonal.links(ii) for d in (2, 3))
        assert all((unused, d) not in diagonal.links(ii) for d in (2, 3))
        frames, planes = Counter(), {}
        for x, k, l, u, v in set(word):
            m, n = [d for d in range(4) if d not in (k, l)]
            frames.update(((u, m), (u, m), (v, n), (v, n)))
            planes[x, k, l] = Counter(((x, k), (diagonal.forward(x, k), l),
                                      (diagonal.forward(x, l), k), (x, l)))
        assert sorted(frames.values()) == [2] * 6
        assert all((active, d) not in frames for d in (2, 3))
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
    seen = set()
    for representative, orbit in sorted(orbits.items()):
        assert not seen & orbit and representative == min(orbit)
        seen.update(orbit)
    assert seen == selected and len(orbits) == 20
    assert Counter(map(len, orbits.values())) == {4: 8, 8: 12}
    charges = Counter(base.charge(diagonal, ii) for ii in selected)
    assert charges == {0: 64, -4: 32, 4: 32}
    print('SUPPORT_CONTROL full_words', 310, 'full_ordered', ordered,
          'independent_DP_even_source', dp_even, 'independent_DP_H23_cross_source', dp_cross,
          'multiplicity_partitions', sorted(partitions.items()), 'selected_words', len(selected),
          'unselected_words', 182, 'selected_ordered', 128 * 90,
          'orbits', 20, 'orbit_sizes', sorted(Counter(map(len, orbits.values())).items()),
          'charges', sorted(charges.items()), 'all_selected_private_erasure', 128, flush=True)
    return selected, sorted(orbits.items())


def representative(diagonal, ns, orbit_index, orbits, product_offset=0):
    wall_guard()
    indices, orbit = orbits[orbit_index]
    word = [diagonal.TERMS[i][2] for i in indices]
    active = 0 if (0, 2) in diagonal.links(indices) else 3
    labels = sorted(set(word))
    center = next(t for t in labels if t[:3] == (active, 2, 3))
    remote = [t for t in labels if t != center]
    guard = Guard(product_offset)
    original_wedge = ns['wedge']
    ns['wedge'] = lambda a, b: guard.join(a, b, original_wedge, 'factory')
    try:
        factors = [ns['square'](t) for t in remote]
        local = ns['square'](center)
    finally:
        ns['wedge'] = original_wedge
    assert all(c.is_ground for p in factors + [local] for c in p.values())
    guard.peak_rows = max(guard.peak_rows, *map(len, factors + [local]))
    sources = guard.join({m: ns['R'](c) for m, c in base.Q.items()},
                         {m << 24: ns['R'](c) for m, c in base.Q.items()}, original_wedge, 'Q0_Q3')
    remote_pair = guard.join(*factors, original_wedge, 'remote_square_pair')
    rest = guard.join(sources, remote_pair, original_wedge, 'source_remote_pair')
    if product_offset + guard.products + len(local) > PRODUCT_CAP:
        raise RuntimeError('final complement lookup product cap')
    guard.products += len(local)
    guard.final_products += len(local)
    raw = ns['R'].zero
    for mask, coefficient in local.items():
        complement = base.TOP ^ mask
        if complement in rest:
            raw += coefficient * rest[complement] * ns['wedge_sign'](mask, complement)
    assert raw.is_ground and raw.const().y == 0
    denominator = 8 ** 6 * 4 ** 12 * 2 ** 3
    value = F(int(raw.const().x), denominator) * F(196, 27)
    print('SELECTED_REPRESENTATIVE', orbit_index, 'orbit_size', len(orbit), 'word', word,
          'square_rows', [len(p) for p in factors] + [len(local)], 'stages', guard.stages,
          'factory_calls', guard.factory_calls, 'factory_products', guard.factory_products,
          'final_products_with_lookup', guard.final_products, 'combined_products', guard.products,
          'peak_rows', guard.peak_rows, 'raw_integer', int(raw.const().x),
          'denominator', denominator, 'raw_g2_6_subcontribution_per_word', str(value), flush=True)
    wall_guard()
    return {'orbit': orbit, 'raw': value, 'products': guard.products, 'peak': guard.peak_rows}


def selected_target(diagonal, ns, selected, orbits):
    seen = set()
    raw = raw_j = raw_jj = F(0)
    products = peak = 0
    for index in range(len(orbits)):
        record = representative(diagonal, ns, index, orbits, products)
        assert not seen & record['orbit']
        seen.update(record['orbit'])
        raw += len(record['orbit']) * record['raw']
        for indices in record['orbit']:
            q = base.charge(diagonal, indices)
            raw_j += q * record['raw']
            raw_jj += q * q * record['raw']
        products += record['products']
        peak = max(peak, record['peak'])
    assert seen == selected and len(seen) == 128 and raw_j == 0
    pair_jj = raw_jj / base.Z8 - (raw / base.Z8) * base.LOGZ_JJ
    print('PARTIAL_DIAGONAL_T_PAIR selected_words', 128, 'full_necessary_words', 310,
          'omitted_words', 182, 'raw_g2_6_subcontribution', str(raw),
          'normalized_pair_subcontribution_times_g2_squared', str(raw / base.Z8),
          'selected_numerator_j', str(raw_j), 'selected_numerator_jj', str(raw_jj),
          'normalized_pair_subcontribution_jj_times_g2_squared', str(pair_jj),
          'normalized_pair_subcontribution_hh_times_g2_squared', str(pair_jj / 8),
          'combined_products_total', products, 'peak_rows', peak, flush=True)
    wall_guard()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--controls', action='store_true')
    group.add_argument('--pilot', action='store_true')
    group.add_argument('--orbit', type=int, choices=range(20))
    group.add_argument('--all', action='store_true', help='prospective reviewed128-word SUBFAMILY only')
    args = parser.parse_args()
    print('CAPS rows', ROW_CAP, 'combined_products', PRODUCT_CAP, 'whole_seconds', WHOLE_SECONDS, flush=True)
    assert hashlib.sha256((Path(__file__).parent / 'nearest_trace.py').read_bytes()).hexdigest() == NEAREST_SHA256
    print('SOURCE_SHA256 nearest_trace.py', NEAREST_SHA256, flush=True)
    for name in ('l1_diagonal_classes.py', 'l1_equal_time_private_pairs.py', 'l1_transverse_top.py'):
        print('SOURCE_SHA256', name, hashlib.sha256((base.OLD / name).read_bytes()).hexdigest(), flush=True)
    _, transverse, haar, ns = base.machinery()
    base.source_tensor(transverse, haar)
    with redirect_stdout(io.StringIO()):
        import l1_diagonal_classes as diagonal
    selected, orbits = support_control(diagonal)
    if args.all:
        selected_target(diagonal, ns, selected, orbits)
    elif not args.controls:
        representative(diagonal, ns, 0 if args.pilot else args.orbit, orbits)
    wall_guard()
    print('ELAPSED_SECONDS', round(perf_counter() - STARTED, 6), flush=True)


if __name__ == '__main__':
    main()
