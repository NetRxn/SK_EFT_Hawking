"""Exact two-face contraction at specified protected coordinate-pair probes."""
from collections import Counter
from fractions import Fraction
from functools import cache
from itertools import product
from math import factorial

from l1_direct_b_haar import add, scale
from l1_extended_mixed_center_census import EVEN, curvature_boundary, orbits, swap_patterns
from l1_extended_mixed_center_gamma import COMPONENTS, gamma_tensor
from l1_extended_mixed_curvature_core import PAIRS, PAIR_INDEX, face_vector
from l1_normalization_uniform_mixed_edge import unit
from l1_extended_mixed_frame_join import remote_center
from l1_extended_mixed_frame_moment import SCALE
from l1_extended_opposed_source import summed_fourth
from l1_extended_overlap_strip import HAAR
from l1_extended_protected_center import protected_center
from l1_extended_two_mixed_centers import contract, remap


@cache
def slice_rows(face, links, probes, free):
    rows = {}
    orientations = [(p,) if p[0] == p[1] else (p, p[::-1]) for p in probes]
    for components in COMPONENTS:
        (ca, ia), (cb, ib) = (divmod(label, 3) for label in components)
        row = Counter()
        for choices in product(*orientations):
            if any(a // 4 != ca or b // 4 != cb for a, b in choices):
                continue
            left = {edge: (unit(a % 4),) * 2 for edge, (a, _) in zip(links, choices)}
            right = {edge: (unit(b % 4),) * 2 for edge, (_, b) in zip(links, choices)}
            for u, v in product(range(4), repeat=2):
                left[free], right[free] = (unit(u),) * 2, (unit(v),) * 2
                weight = face_vector(face, left, ca, ia) * face_vector(face, right, cb, ib)
                if weight:
                    key = tuple(sorted((4*ca + u, 4*cb + v)))
                    row[PAIR_INDEX[key]] += weight
        row = {i: value for i, value in row.items() if value}
        if row:
            rows[components] = row
    return rows


def curvature_join(first, last):
    result = {}
    for a, b in product(first, last):
        value = sum(u * weight * last[b].get(j, 0)
                    for i, u in first[a].items() for j, weight in HAAR[PAIRS[i]])
        if value:
            result[a, b] = value
    return result


def coefficient(pattern, faces, protected, probes, common):
    free, = {e for edges in faces.values() for e in edges} - protected
    site, = {f[0] for f in faces}
    first, last = pattern[EVEN.index(site)]
    axis, = set(first) & set(last)
    a, b = sorted(set(first) ^ set(last))
    ordered = []
    for exclusive in (a, b):
        # The residual face that uses this frame direction is the one
        # whose curvature plane excludes it.
        face, = [f for f in faces if exclusive not in f[1:]]
        links = tuple(sorted(faces[face] - {free}))
        ordered.append(slice_rows(face, links, tuple(probes[e] for e in links), free))
    channels = curvature_join(*ordered)
    core = add(*(scale(gamma_tensor(probes[site, a], probes[site, b], c, d, common), weight)
                 for (c, d), weight in channels.items()))
    terms = {site: remap(core, (site, site ^ (1 << a), site ^ (1 << axis), site ^ (1 << b)))}
    divisor = 48 * SCALE**4 * 4**4 * 96**2 * 8**4 * factorial(2)**2

    for x, pairs in zip(EVEN, pattern, strict=True):
        if x == site:
            continue
        p, q = pairs
        protected_axes = [i for i in sorted(set(p) | set(q)) if (x ^ (1 << i), i) in probes]
        if protected_axes:
            assert p == q and tuple(protected_axes) == p
            local = protected_center(tuple(probes[x ^ (1 << i), i] for i in p))
            axes = p
            divisor *= 48 * SCALE**4 * 4**8 * factorial(4)
        else:
            local, axes = remote_center(pairs)
            divisor *= 96**4 * 8**8
            for pair in set(pairs):
                divisor *= 48 * factorial(2 * pairs.count(pair))
        terms[x] = remap(local, (x, *(x ^ (1 << i) for i in axes)))
    if not core:
        return len(channels), 0, Fraction(0)
    raw = contract(terms)
    assert raw == contract(dict(enumerate(reversed(tuple(terms.values())))))
    assert raw.is_ground and not raw.const().y
    return len(channels), len(core), Fraction(int(raw.const().x), divisor)


def main():
    common = summed_fourth(1)
    for pattern, multiplicity in orbits(swap_patterns()):
        faces, protected = curvature_boundary(pattern)
        if len(faces) != 2:
            continue
        links = {e for edges in faces.values() for e in edges} & protected
        assert len(links) == 6
        for (x, _, _), edges in faces.items():
            frame_links = edges & links
            local = {edge for edge in frame_links if edge[0] == x}
            assert len(local) == 1
            pure_sites = {y ^ (1 << axis) for y, axis in frame_links - local}
            pure_site, = pure_sites
            assert len(frame_links - local) == 2 and pure_site in EVEN
            a, b = pattern[EVEN.index(pure_site)]
            assert a == b
        for pair in ((0, 0), (0, 4)):
            probes = dict.fromkeys(links, pair)
            print("orbit", multiplicity, "probe", pair,
                  "channels, core entries, coefficient", coefficient(
                      pattern, faces, protected, probes, common), flush=True)


if __name__ == "__main__":
    main()
