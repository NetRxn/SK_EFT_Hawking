"""New-factorization control only: projected single-link fourth tensor.

Does not join both active axes or compute any action-word coefficient.
"""
from time import perf_counter
STARTED = perf_counter()
from collections import Counter
from itertools import combinations_with_replacement, product
import resource
import nearest_trace as N


def main():
    _, _, haar, ns = N.machinery()
    from l1_normalization_opposed_fourth import nodes, vec_moment
    from l1_reduced_wedge_reference import wedge_sign
    from fractions import Fraction as F
    comm = haar.qproduct(haar.adj(haar.B), haar.adj(haar.A), haar.B, haar.A)
    assert haar.integral(comm[1] ** 4)[0] == vec_moment((0, 0, 0, 0)) == F(8, 75)
    assert haar.integral(comm[1] ** 2 * comm[2] ** 2)[0] == vec_moment((0, 0, 1, 1)) == F(8, 225)
    assert F(8, 75) != 3 * F(2, 9) ** 2
    # Test axis0 at actual center2 and actual source endpoint3.
    site, axis, remote = 2, 0, 3
    quartets = tuple(combinations_with_replacement(range(4), 4))
    out = {q: {} for q in quartets}
    guard = N.Guard()
    Q = {m << (8 * remote): ns['R'](c) for m, c in N.Q.items()}
    remote_mask = 255 << (8 * remote)
    for left, right, weight in nodes():
        if perf_counter() - STARTED >= 55:
            raise TimeoutError('55-second whole control cap')
        U = ns['diag'](ns['quat'](left), ns['quat'](right))
        Ud = ns['diag'](ns['quat'](ns['adj'](left)), ns['quat'](ns['adj'](right)))
        frames = [ns['add'](ns['bilinear'](g * Ud, site, remote),
                            ns['scale'](ns['bilinear'](U * g, remote, site), -1)) for g in ns['gamma']]
        pairs = {(a, b): guard.join(frames[a], frames[b], ns['wedge'], 'frame_pair')
                 for a in range(4) for b in range(a, 4)}
        for a, b, c, d in quartets:
            fourth = guard.join(pairs[a, b], pairs[c, d], ns['wedge'], 'fourth')
            projected = guard.join(fourth, Q, ns['wedge'], 'Q_projection')
            local = {mask ^ remote_mask: coefficient for mask, coefficient in projected.items()
                     if mask & remote_mask == remote_mask}
            assert all((mask >> (8 * site)).bit_count() == 4 and mask >> (8 * site) < 256 for mask in local)
            out[a, b, c, d] = ns['add'](out[a, b, c, d], ns['scale'](local, weight))
    local_Q = {m << (8 * site): c for m, c in N.Q.items()}
    reductions = {}
    for quartet, polynomial in out.items():
        a, b, c, d = quartet
        contractions = int(a == b and c == d) + int(a == c and b == d) + int(a == d and b == c)
        expected = {mask: ns['R'](12288 * contractions * coefficient) for mask, coefficient in local_Q.items()} if contractions else {}
        assert polynomial == expected, quartet
        if polynomial:
            assert set(polynomial) == set(local_Q)
            ratios = set()
            for mask, coefficient in polynomial.items():
                assert coefficient.is_ground and coefficient.const().y == 0
                ratios.add(F(int(coefficient.const().x), local_Q[mask]))
            reductions[quartet] = tuple(map(str, sorted(ratios)))
    print('PROJECTED_Q_RATIOS', reductions, flush=True)
    print('PROJECTED_FOURTH_CONTROL', 'center', site, 'axis', axis, 'source_endpoint', remote,
          'quartets', len(quartets), 'support_histogram', sorted(Counter(map(len, out.values())).items()),
          'normalization', '96*8^4 per physical frame quartet',
          'products', guard.products, 'peak_rows', guard.peak_rows,
          'comm_fourth_same', '8/75', 'comm_fourth_distinct', '8/225',
          'maxrss_kib', resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
          'seconds', perf_counter() - STARTED, flush=True)
    print('No action-word top contraction or subfamily sum evaluated.', flush=True)
    return out, guard


if __name__ == '__main__':
    main()
