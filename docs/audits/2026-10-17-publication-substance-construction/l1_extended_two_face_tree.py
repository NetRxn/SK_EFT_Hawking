"""Exact tree-gauge normalization for free-link two-face cores."""
from argparse import ArgumentParser
from fractions import Fraction
from functools import cache
from itertools import product
from math import factorial

from l1_direct_b_haar import add, scale, wedge
from l1_extended_four_face_gauge_join import IDENTITY, PROBE_CLASSES, indexed_mixed_dual, mixed_rows
from l1_extended_mixed_center_census import (
    EVEN, curvature_boundary, orbits, swap_patterns, words_with_mixed_count,
)
from l1_extended_mixed_center_gamma import COMPONENTS, face_channels, gamma_block, opposite_center, opposite_source
from l1_extended_mixed_curvature_core import PAIRS, face_tensor
from l1_extended_mixed_frame_moment import SCALE, frame_edge
from l1_extended_opposed_source import summed_fourth
from l1_extended_protected_center import protected_center, summed_protected_source
from l1_extended_two_face_gamma_join import remote_environment
from l1_extended_two_mixed_centers import remap
from l1_reduced_wedge_reference import wedge_sign


@cache
def upper_tensor(pure, positions, probe, source, removed):
    if pure:
        tensor = summed_protected_source if source else protected_center
        return tensor((probe, None) if positions == (1, 2) else (None, probe))
    live, fixed = positions
    probes = tuple(probe if i == live else None for i in (1, 2, 3))
    if source:
        slots = (removed,) if removed is not None else (1, 3)
        return add(*(opposite_source(slot, probes, fixed=(fixed,)) for slot in slots))
    return opposite_center(probes, fixed=(fixed,))


def upper_links(face, edges, protected):
    x, k, l = face
    center = x ^ (1 << k) ^ (1 << l)
    upper = tuple(sorted(((y, a) for y, a in edges & protected
                          if y ^ (1 << a) == center), key=lambda edge: edge[1]))
    assert len(upper) == 2
    return center, upper


def upper_factor(pattern, face, edges, protected, reverse, source=False, omitted=None,
                 probe_classes=False):
    center, upper = upper_links(face, edges, protected)
    if reverse:
        upper = upper[::-1]
    planes = pattern[EVEN.index(center)]
    p, q = planes
    if p == q:
        directions = p
    else:
        a, b = sorted(set(p) ^ set(q))
        common, = set(p) & set(q)
        directions = (a, common, b)
    removed = None
    if omitted is not None:
        assert source and omitted[0] == center and p != q
        plane = tuple(a for a in range(4) if a not in omitted[1:])
        assert plane in planes
        removed = 1 if directions[0] in plane else 3
    positions = tuple(directions.index(a) + 1 for _, a in upper)
    sites = tuple(center ^ (1 << a) for a in directions)
    fixed = dict.fromkeys(edges - {upper[0]}, IDENTITY)
    rows = {}
    multiplicities = dict(PROBE_CLASSES) if probe_classes else dict.fromkeys(PAIRS, 1)
    for components in COMPONENTS:
        terms = face_tensor(face, upper[:1], fixed, components)
        poly = add(*(scale(upper_tensor(p == q, positions, PAIRS[i], source, removed),
                            weight * multiplicities[PAIRS[i]])
                     for (i,), weight in terms.items() if PAIRS[i] in multiplicities))
        if poly:
            assert all(mask & 255 == 255 for mask in poly)
            rows[components] = remap({m >> 8: v for m, v in poly.items()}, sites)
    degree = sum(2 * sum(a in plane for plane in planes) for _, a in upper)
    divisor = SCALE**4 * 4**degree * 96**((8-degree)//2) * 8**(8-degree)
    divisor *= 48 * factorial(4) if p == q else 48**2 * factorial(2)**2
    if source:
        adjustment = -2 * (factorial(4) // factorial(2) if p == q else 48 * factorial(2))
        rows = {key: scale(poly, adjustment) for key, poly in rows.items()}
    return center, sites, rows, divisor


@cache
def fixed_frame_pair(components):
    rows = []
    for (a, b), weight in face_channels(components).items():
        first = fixed_second_frame(a)
        second = remap(fixed_second_frame(b), (0, 2))
        rows.append(scale(wedge(first, second), weight))
    return add(*rows)


@cache
def fixed_second_frame(labels):
    return frame_edge(labels, 0, None)


@cache
def disjoint_base(first, last):
    joined = wedge(fixed_frame_pair(first), remap(fixed_frame_pair(last), (0, 3, 4)))
    return {mask: value for mask, value in joined.items() if mask & 255 == 255}


def check_disjoint_tree(faces, protected, reverse):
    links = set.union(*faces.values())
    live = {upper_links(face, edges, protected)[1][int(reverse)]
            for face, edges in faces.items()}
    tree = links - live
    vertices = {v for x, axis in links for v in (x, x ^ (1 << axis))}
    reached = {min(vertices)}
    for _ in tree:
        for x, axis in tree:
            y = x ^ (1 << axis)
            if x in reached or y in reached:
                reached.update((x, y))
    assert len(live) == 2 and len(tree) == 6 and len(vertices) == 7
    assert reached == vertices


def close_upper(left, right, dual):
    """Pair exterior products with the sparse dual using exact integers."""
    real = imag = 0
    for a, value in left.items():
        r, i = int(value.const().x), int(value.const().y)
        if len(right) <= len(dual):
            pairs = ((b, other, dual.get(a | b)) for b, other in right.items() if not a & b)
        else:
            pairs = ((mask ^ a, right.get(mask ^ a), weight)
                     for mask, weight in dual.items() if mask & a == a)
        for b, other, weight in pairs:
            if other is None or weight is None:
                continue
            s, j = int(other.const().x), int(other.const().y)
            u, v = weight
            sign = wedge_sign(a, b)
            real += sign * ((r*s - i*j)*u - (r*j + i*s)*v)
            imag += sign * ((r*s - i*j)*v + (r*j + i*s)*u)
    return real, imag


def close_channels(base, base_sites, keep, env, upper_sites, terms):
    """Reuse one environment index and release each dual row after contraction."""
    dual = indexed_mixed_dual(keep, env, upper_sites)
    channels = set().union(*(set(product(left, right)) for left, right in terms))
    totals = [[0, 0] for _ in terms]
    for key in sorted(channels):
        row = dual(mixed_rows(base, base_sites, (key,))[key])
        x, y = key
        for (left, right), subtotal in zip(terms, totals, strict=True):
            if x in left and y in right:
                re, im = close_upper(left[x], right[y], row)
                subtotal[0] += re
                subtotal[1] += im
    assert all(im == 0 for _, im in totals)
    return tuple(re for re, _ in totals)


def coefficient(pattern, faces, protected, base, reverse=False, source=False, omitted=None,
                probe_classes=False):
    assert not (source and omitted is not None)
    site, = {f[0] for f in faces}
    p, q = pattern[EVEN.index(site)]
    if set(p) & set(q):
        common, = set(p) & set(q)
        a, b = sorted(set(p) ^ set(q))
        directions = (a, common, b)
        ordered = [next(f for f in faces if axis not in f[1:]) for axis in (a, b)]
        base_divisor = SCALE**4 * 4**4 * 96**2 * 8**4 * factorial(2)**2
    else:
        directions = p + q
        ordered = [(site, *q), (site, *p)]
        assert set(ordered) == set(faces)
        check_disjoint_tree(faces, protected, reverse)
        base = disjoint_base
        base_divisor = SCALE**8 * 4**8 * factorial(2)**2
    def upper(side, *, source=False, omitted=None):
        face = ordered[side]
        return upper_factor(pattern, face, faces[face], protected, reverse, source, omitted,
                            probe_classes=probe_classes and side == 0)

    left, right = upper(0), upper(1)
    coupled = {site, left[0], right[0]}
    assert len(coupled) == 3
    assert omitted is None or omitted[0] != site
    remote_omission = omitted if omitted is not None and omitted[0] not in coupled else None
    keep, env = remote_environment(pattern, coupled, only_face=remote_omission)
    if omitted is not None and remote_omission is None:
        if omitted[0] == left[0]:
            left = upper(0, source=True, omitted=omitted)
        else:
            assert omitted[0] == right[0]
            right = upper(1, source=True, omitted=omitted)
    sites = tuple(site ^ (1 << i) for i in directions)
    changed = None
    if source:
        changed = [upper(side, source=True)[2] for side in (0, 1)]
    upper_sites = set(left[1]) | set(right[1])
    terms = [(left[2], right[2])]
    if changed is not None:
        terms.extend(((changed[0], right[2]), (left[2], changed[1])))
    total, *upper_terms = close_channels(base, sites, keep, env, upper_sites, terms)
    divisor = left[3] * right[3] * base_divisor
    for x, (p, q) in zip(EVEN, pattern, strict=True):
        if x not in coupled:
            divisor *= 96**4 * 8**8
            divisor *= 48 * factorial(4) if p == q else 48**2 * factorial(2)**2
    normal = Fraction(total, divisor * (6 if omitted is not None else 1))
    if changed is None:
        return normal
    source_keep, source_env = remote_environment(pattern, coupled, source=True)
    assert source_keep == keep
    remote, = close_channels(base, sites, keep, source_env, upper_sites, terms[:1])
    return normal, Fraction(remote, 6 * divisor), Fraction(sum(upper_terms), 6 * divisor)


def replay_four_face_deletions(reverse, probe_classes):
    from l1_extended_one_face_gauge_join import check_removals

    base = cache(gamma_block(None, None, summed_fourth(1)))
    total = Fraction()
    count = population = 0
    for pattern, multiplicity in orbits(words_with_mixed_count(3)):
        faces, protected = curvature_boundary(pattern)
        if len(faces) != 4:
            continue
        check_removals(pattern)
        subtotal = Fraction()
        for omitted in faces:
            rest, protection = curvature_boundary(pattern, omitted=omitted)
            assert protection == protected and len(rest) == 2
            assert len(set.union(*rest.values()) - protected) == 1
            value = coefficient(pattern, rest, protected, base, reverse, omitted=omitted,
                                probe_classes=probe_classes)
            print("orbit", count, "removed face", omitted, "source", value, flush=True)
            subtotal += value
        total += 2 * multiplicity * subtotal
        count += 1
        population += multiplicity
    assert (count, population) == (10, 1920)
    print("four-face deletion subtotal, both checkerboards", total, flush=True)


def main(control, reverse, source, orbit, all_protected, probe_classes):
    words = swap_patterns() if control else words_with_mixed_count(3)
    base = disjoint_base if all_protected else cache(gamma_block(None, None, summed_fourth(1)))
    total = Fraction()
    count = population = eligible = 0
    remote = upper = Fraction()
    for pattern, multiplicity in orbits(words):
        faces, protected = curvature_boundary(pattern)
        if len(faces) != 2 or len(set.union(*faces.values()) - protected) != (0 if all_protected else 1):
            continue
        index = eligible
        eligible += 1
        if orbit is not None and index != orbit:
            continue
        result = coefficient(pattern, faces, protected, base, reverse, source,
                             probe_classes=probe_classes)
        if source:
            result, remote_row, upper_row = result
            remote += 2 * multiplicity * remote_row
            upper += 2 * multiplicity * upper_row
            print("source orbit", index, multiplicity, remote_row, upper_row, flush=True)
        print(index, multiplicity, result, flush=True)
        total += 2 * multiplicity * result
        count += 1
        population += multiplicity
    if control:
        expected_count, expected_population = 3, 576
    elif all_protected:
        expected_count, expected_population = 23, 3744
    else:
        expected_count, expected_population = 80, 15072
    assert eligible == expected_count
    if orbit is None:
        assert (count, population) == (expected_count, expected_population)
    else:
        assert count == 1
    print("candidate normalization, both checkerboards", total, flush=True)
    if source:
        print("candidate retained source, both checkerboards", remote, upper, flush=True)
    if control:
        expected = (Fraction(8997242104792619384765625, 72057594037927936)
                    / (3 if orbit is not None else 1))
        assert total == expected, f"tree control differs from fused control by {total - expected}"


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--control", action="store_true", help="compare to the corrected fused subtotal (default)")
    mode.add_argument("--candidate", action="store_true", help="emit provisional three-mixed orbit values")
    mode.add_argument("--candidate-source", action="store_true", help="emit provisional three-mixed retained-source values")
    mode.add_argument("--control-source", action="store_true", help="replay the two-mixed retained-source controls")
    mode.add_argument("--four-face-deleted-source", action="store_true")
    parser.add_argument("--reverse-upper", action="store_true")
    parser.add_argument("--orbit", type=int, help="evaluate a single numbered orbit")
    parser.add_argument("--all-protected", action="store_true",
                        help="select the 23 all-protected three-mixed orbits")
    parser.add_argument("--probe-classes", action="store_true", help="weight one live link by its probe classes")
    args = parser.parse_args()
    if args.all_protected and not (args.candidate or args.candidate_source):
        parser.error("--all-protected requires --candidate or --candidate-source")
    if args.four_face_deleted_source:
        if args.orbit is not None:
            parser.error("--orbit is unavailable for the four-face deletion replay")
        replay_four_face_deletions(args.reverse_upper, args.probe_classes)
    else:
        main(not (args.candidate or args.candidate_source), args.reverse_upper,
             args.control_source or args.candidate_source, args.orbit, args.all_protected,
             args.probe_classes)
