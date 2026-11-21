"""Pointwise same-link and independent2+2 anchor quartets; no word sum."""
from time import perf_counter
STARTED = perf_counter()
from fractions import Fraction as F
from itertools import combinations_with_replacement, product
from collections import Counter
import resource
import both_unused_trace_fourth_control as K
import nearest_trace as N


def main():
    cubature, kernel_guard = K.main()
    _, _, _, ns = N.machinery()
    guard = N.Guard(product_offset=kernel_guard.products)
    wedge = ns['wedge']
    # Exact invariant decomposition:Q=3 B_L B_R -6(detbarL detpsiR
    # +detbarR detpsiL). Every factor is invariant under its determinant-one
    # chiral spinor change of variables, including barred inverse actions.
    BL = {17: ns['R'](1), 34: ns['R'](1)}
    BR = {68: ns['R'](1), 136: ns['R'](1)}
    Qcheck = ns['scale'](guard.join(BL, BR, wedge, 'Q_invariant'), 3)
    Qcheck = ns['add'](Qcheck, {195: ns['R'](-6), 60: ns['R'](-6)})
    assert Qcheck == {m: ns['R'](c) for m, c in N.Q.items()}
    site, remote = 2, 3
    Qremote = {m << 24: ns['R'](c) for m, c in N.Q.items()}
    Qlocal = {m << 16: c for m, c in N.Q.items()}
    remote_mask = 255 << 24

    def project(first, second, name):
        p = guard.join(first, second, wedge, name)
        p = guard.join(p, Qremote, wedge, name + '_Q')
        return {m ^ remote_mask: c for m, c in p.items() if m & remote_mask == remote_mask}

    frames = [ns['add'](ns['bilinear'](g, site, remote),
                         ns['scale'](ns['bilinear'](g, remote, site), -1)) for g in ns['gamma']]
    pairs = {(a, b): guard.join(frames[a], frames[b], wedge, 'identity_pair')
             for a in range(4) for b in range(a, 4)}
    for a, b, c, d in combinations_with_replacement(range(4), 4):
        p = project(pairs[a, b], pairs[c, d], 'identity_fourth')
        assert ns['scale'](p, 96 * 16) == cubature[a, b, c, d]
    # At U=I the incoming frame is the negative of this outgoing frame;
    # its fourth tensor is identical. The pointwise gauge proof then uses
    # the invariant Qremote decomposition above to remove arbitrary U.
    ns['wedge'] = lambda a, b: guard.join(a, b, wedge, 'factory')
    try:
        outgoing = ns['frame_pair'](site, 0, site)
        incoming = ns['frame_pair'](site, 0, remote)
    finally:
        ns['wedge'] = wedge
    indices = tuple(combinations_with_replacement(range(4), 2))
    mixed = {}
    for (a, b), (c, d) in product(indices, repeat=2):
        p = project(outgoing[a][b], incoming[c][d], 'mixed_2plus2')
        mixed[a, b, c, d] = p
    def ratio(q):
        if not mixed[q]:
            return F(0)
        values = {F(int(c.const().x), Qlocal[m] * 8 ** 2 * 4 ** 4)
                  for m, c in mixed[q].items()}
        assert all(c.is_ground and c.const().y == 0 for c in mixed[q].values())
        assert len(values) == 1
        return values.pop()
    A, B = ratio((0, 0, 1, 1)), ratio((0, 1, 0, 1))
    for (a, b, c, d), p in mixed.items():
        coefficient = A * int(a == b and c == d) + B * (int(a == c and b == d) + int(a == d and b == c))
        assert all(c.is_ground and c.const().y == 0 for c in p.values())
        actual = {m: F(int(c.const().x), 8 ** 2 * 4 ** 4) for m, c in p.items()}
        expected = {m: coefficient * c for m, c in Qlocal.items()} if coefficient else {}
        assert actual == expected, (a, b, c, d)
    print('ANCHOR_QUARTET_CONTROL', 'Q_chiral_invariant_decomposition', 'PASS',
          'same_link_identity_vs_cubature_quartets', 35, 'mixed_anchor_2plus2_tensors', 100,
          'mixed_A_delta_ab_delta_cd', str(A), 'mixed_B_cross_deltas', str(B),
          'mixed_support_histogram', sorted(Counter(map(len, mixed.values())).items()),
          'combined_exterior_products', kernel_guard.products + guard.products,
          'peak_rows', max(kernel_guard.peak_rows, guard.peak_rows),
          'seconds', perf_counter() - STARTED,
          'maxrss_kib', resource.getrusage(resource.RUSAGE_SELF).ru_maxrss, flush=True)
    print('No action-word scalar or22-word sum evaluated by this control.', flush=True)
    if perf_counter() - STARTED >= 60:
        raise TimeoutError('whole-control60-second cap')


if __name__ == '__main__':
    main()
