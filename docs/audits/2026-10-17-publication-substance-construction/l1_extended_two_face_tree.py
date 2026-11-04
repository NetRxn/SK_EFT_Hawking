"""Exact tree-gauge normalization for free-link two-face cores."""
from argparse import ArgumentParser
from fractions import Fraction
from functools import cache
from itertools import product
from math import factorial

from l1_direct_b_haar import add, scale, wedge
from l1_extended_four_face_gauge_join import IDENTITY, dot, dual_mixed, mixed_rows
from l1_extended_mixed_center_census import (
    EVEN, curvature_boundary, orbits, swap_patterns, words_with_mixed_count,
)
from l1_extended_mixed_center_gamma import COMPONENTS, gamma_block, opposite_center, opposite_source
from l1_extended_mixed_curvature_core import PAIRS, face_tensor
from l1_extended_mixed_frame_moment import SCALE
from l1_extended_opposed_source import summed_fourth
from l1_extended_protected_center import protected_center, summed_protected_source
from l1_extended_two_face_gamma_join import remote_environment
from l1_extended_two_mixed_centers import remap


@cache
def upper_tensor(pure, positions, probe, source):
    if pure:
        tensor = summed_protected_source if source else protected_center
        return tensor((probe, None) if positions == (1, 2) else (None, probe))
    live, fixed = positions
    probes = tuple(probe if i == live else None for i in (1, 2, 3))
    if source:
        return add(*(opposite_source(removed, probes, fixed=(fixed,)) for removed in (1, 3)))
    return opposite_center(probes, fixed=(fixed,))


def upper_factor(pattern, face, edges, protected, reverse, source=False):
    x, k, l = face
    center = x ^ (1 << k) ^ (1 << l)
    upper = tuple(sorted(((y, a) for y, a in edges & protected
                          if y ^ (1 << a) == center), key=lambda edge: edge[1]))
    assert len(upper) == 2
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
    positions = tuple(directions.index(a) + 1 for _, a in upper)
    sites = tuple(center ^ (1 << a) for a in directions)
    fixed = dict.fromkeys(edges - {upper[0]}, IDENTITY)
    rows = {}
    for components in COMPONENTS:
        terms = face_tensor(face, upper[:1], fixed, components)
        poly = add(*(scale(upper_tensor(p == q, positions, PAIRS[i], source), weight)
                     for (i,), weight in terms.items()))
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


def coefficient(pattern, faces, protected, base, reverse=False, source=False):
    site, = {f[0] for f in faces}
    p, q = pattern[EVEN.index(site)]
    common, = set(p) & set(q)
    a, b = sorted(set(p) ^ set(q))
    ordered = [next(f for f in faces if axis not in f[1:]) for axis in (a, b)]
    left, right = [upper_factor(pattern, face, faces[face], protected, reverse) for face in ordered]
    coupled = {site, left[0], right[0]}
    assert len(coupled) == 3
    keep, env = remote_environment(pattern, coupled)
    sites = tuple(site ^ (1 << i) for i in (a, common, b))
    changed = None
    if source:
        changed = [upper_factor(pattern, face, faces[face], protected, reverse, source=True)[2]
                   for face in ordered]
    channels = tuple(product(set(left[2]) | (changed[0].keys() if changed else set()),
                             set(right[2]) | (changed[1].keys() if changed else set())))
    first = mixed_rows(base, sites, channels)
    upper_sites = set(left[1]) | set(right[1])
    dual = dual_mixed(keep, env, first, upper_sites)

    def close(lhs, rhs, boundary):
        total = imag = 0
        for x, y in product(lhs, rhs):
            row = wedge(lhs[x], rhs[y])
            values = {m: (int(v.const().x), int(v.const().y)) for m, v in row.items()}
            re, im = dot(boundary[x, y], values)
            total += re
            imag += im
        assert imag == 0
        return total

    total = close(left[2], right[2], dual)
    divisor = left[3] * right[3] * SCALE**4 * 4**4 * 96**2 * 8**4 * factorial(2)**2
    for x, (p, q) in zip(EVEN, pattern, strict=True):
        if x not in coupled:
            divisor *= 96**4 * 8**8
            divisor *= 48 * factorial(4) if p == q else 48**2 * factorial(2)**2
    normal = Fraction(total, divisor)
    if changed is None:
        return normal
    source_keep, source_env = remote_environment(pattern, coupled, source=True)
    assert source_keep == keep
    remote_dual = dual_mixed(keep, source_env, first, upper_sites)
    remote = close(left[2], right[2], remote_dual)
    # A source pair replaces two of the four slots at exactly one upper center.
    upper = close(changed[0], right[2], dual) + close(left[2], changed[1], dual)
    return normal, Fraction(remote, 6 * divisor), Fraction(upper, 6 * divisor)


def main(control, reverse, source, orbit):
    words = swap_patterns() if control else words_with_mixed_count(3)
    base = cache(gamma_block(None, None, summed_fourth(1)))
    total = Fraction()
    count = population = eligible = 0
    remote = upper = Fraction()
    for pattern, multiplicity in orbits(words):
        faces, protected = curvature_boundary(pattern)
        if len(faces) != 2 or len(set.union(*faces.values()) - protected) != 1:
            continue
        index = eligible
        eligible += 1
        if orbit is not None and index != orbit:
            continue
        result = coefficient(pattern, faces, protected, base, reverse, source)
        if source:
            result, remote_row, upper_row = result
            remote += 2 * multiplicity * remote_row
            upper += 2 * multiplicity * upper_row
            print("source orbit", index, multiplicity, remote_row, upper_row, flush=True)
        print(index, multiplicity, result, flush=True)
        total += 2 * multiplicity * result
        count += 1
        population += multiplicity
    expected_count, expected_population = (3, 576) if control else (80, 15072)
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
    parser.add_argument("--reverse-upper", action="store_true")
    parser.add_argument("--orbit", type=int, help="evaluate a single numbered orbit")
    args = parser.parse_args()
    main(not (args.candidate or args.candidate_source), args.reverse_upper,
         args.control_source or args.candidate_source, args.orbit)
