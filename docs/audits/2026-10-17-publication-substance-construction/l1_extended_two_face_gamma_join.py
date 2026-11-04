"""Exact two-face contraction at specified protected coordinate-pair probes."""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from fractions import Fraction
from functools import cache
from itertools import product
from math import factorial

from l1_direct_b_haar import R, add, scale
from l1_extended_mixed_center_census import EVEN, curvature_boundary, orbits, swap_patterns
from l1_extended_mixed_center_gamma import COMPONENTS, gamma_tensor
from l1_extended_mixed_curvature_core import PAIRS, PAIR_INDEX, face_tensor, face_vector
from l1_normalization_uniform_mixed_edge import unit
from l1_extended_mixed_frame_join import remote_center
from l1_extended_mixed_frame_moment import SCALE
from l1_extended_opposed_source import summed_fourth
from l1_extended_overlap_strip import HAAR
from l1_extended_protected_center import protected_center
from l1_extended_two_mixed_centers import contract, contract_boundary, remap
from l1_reduced_wedge_reference import wedge_sign


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

    coupled = {site}
    for x, pairs in zip(EVEN, pattern, strict=True):
        if x == site:
            continue
        p, q = pairs
        protected_axes = [i for i in sorted(set(p) | set(q)) if (x ^ (1 << i), i) in probes]
        if protected_axes:
            coupled.add(x)
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
    keep, environment = remote_environment(pattern, coupled)
    boundary = contract_boundary({x: terms[x] for x in coupled}, keep)
    closed = R.zero
    for mask, value in boundary.items():
        opposite = keep ^ mask
        if opposite in environment:
            closed += value * environment[opposite] * wedge_sign(mask, opposite)
    assert raw == closed
    assert raw.is_ground and not raw.const().y
    return len(channels), len(core), Fraction(int(raw.const().x), divisor)


def pure_links(face, edges, protected):
    local, = (e for e in edges & protected if e[0] == face[0])
    pure = tuple(sorted((edges & protected) - {local}, key=lambda e: e[1]))
    assert len(pure) == 2
    site, = {x ^ (1 << axis) for x, axis in pure}
    return pure, local, site


@cache
def pure_table():
    table = {}
    for i, j in product(range(len(PAIRS)), repeat=2):
        poly = protected_center((PAIRS[i], PAIRS[j]))
        if poly:
            assert all(value.is_ground for value in poly.values())
            table[i, j] = {m: (int(v.const().x), int(v.const().y)) for m, v in poly.items()}
    return table


def fuse_face(face, pure, local, free, table):
    out = {}
    for components in COMPONENTS:
        boundary = defaultdict(dict)
        for (a, b, probe, live), weight in face_tensor(
                face, (*pure, local, free), {}, components).items():
            if (a, b) not in table:
                continue
            row = boundary[probe, live]
            for mask, (re, im) in table[a, b].items():
                old_re, old_im = row.get(mask, (0, 0))
                row[mask] = old_re + weight*re, old_im + weight*im
        for key, row in boundary.items():
            reduced = {m: value for m, value in row.items() if any(value)}
            if reduced:
                out[components, *key] = reduced
    return out


def check_fusion(face, pure, local, free, table, pair):
    index = PAIR_INDEX[pair]
    if (index, index) not in table:
        return
    row = table[index, index]
    fused = fuse_face(face, pure, local, free, {(index, index): row})
    reference = slice_rows(face, (*pure, local), (pair,) * 3, free)
    expected = {(components, index, live): {m: (weight*r, weight*i)
                                           for m, (r, i) in row.items()}
                for components, values in reference.items() for live, weight in values.items()}
    assert {key: poly for key, poly in fused.items() if key[1] == index} == expected


def remote_environment(pattern, coupled):
    terms = {}
    open_sites = {x ^ (1 << a) for x in coupled
                  for pair in pattern[EVEN.index(x)] for a in pair}
    keep = sum(255 << (8*x) for x in open_sites)
    for x, pairs in zip(EVEN, pattern, strict=True):
        if x not in coupled:
            local, axes = remote_center(pairs)
            terms[x] = remap(local, (x, *(x ^ (1 << i) for i in axes)))
    return keep, contract_boundary(terms, keep)


def fuse_all():
    table = pure_table()
    for pattern, multiplicity in orbits(swap_patterns()):
        faces, protected = curvature_boundary(pattern)
        if len(faces) != 2:
            continue
        free, = {e for edges in faces.values() for e in edges} - protected
        mixed, = {face[0] for face in faces}
        coupled = {mixed}
        for face, edges in sorted(faces.items()):
            pure, local, site = pure_links(face, edges, protected)
            coupled.add(site)
            assert len(set(pattern[EVEN.index(site)])) == 1
            for pair in ((0, 0), (0, 4)):
                check_fusion(face, pure, local, free, table, pair)
            fused = fuse_face(face, pure, local, free, table)
            print("orbit", multiplicity, "face", face, "fused rows", len(fused),
                  "exterior entries", sum(map(len, fused.values())), flush=True)
        assert len(coupled) == 3
        keep, environment = remote_environment(pattern, coupled)
        print("orbit", multiplicity, "open passive sites", keep.bit_count() // 8,
              "remote environment entries", len(environment), flush=True)


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
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--fuse-pure-centers", action="store_true")
    if parser.parse_args().fuse_pure_centers:
        fuse_all()
    else:
        main()
