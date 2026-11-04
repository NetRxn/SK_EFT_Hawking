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
from l1_extended_mixed_center_gamma import COMPONENTS, gamma_block, opposite_center
from l1_extended_mixed_curvature_core import PAIRS, face_tensor
from l1_extended_mixed_frame_moment import SCALE
from l1_extended_opposed_source import summed_fourth
from l1_extended_protected_center import protected_center
from l1_extended_two_face_gamma_join import pure_links, remote_environment
from l1_extended_two_mixed_centers import remap


@cache
def upper_tensor(pure, positions, probe):
    if pure:
        return protected_center((probe, None) if positions == (1, 2) else (None, probe))
    live, fixed = positions
    probes = tuple(probe if i == live else None for i in (1, 2, 3))
    return opposite_center(probes, fixed=(fixed,))


def upper_factor(pattern, face, edges, protected, reverse):
    upper, _, center = pure_links(face, edges, protected)
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
        poly = add(*(scale(upper_tensor(p == q, positions, PAIRS[i]), weight)
                     for (i,), weight in terms.items()))
        if poly:
            assert all(mask & 255 == 255 for mask in poly)
            rows[components] = remap({m >> 8: v for m, v in poly.items()}, sites)
    degree = sum(2 * sum(a in plane for plane in planes) for _, a in upper)
    divisor = SCALE**4 * 4**degree * 96**((8-degree)//2) * 8**(8-degree)
    divisor *= 48 * factorial(4) if p == q else 48**2 * factorial(2)**2
    return center, sites, rows, divisor


def coefficient(pattern, faces, protected, base, reverse=False):
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
    channels = tuple(product(left[2], right[2]))
    first = mixed_rows(base, sites, channels)
    dual = dual_mixed(keep, env, first, set(left[1]) | set(right[1]))
    total = imag = 0
    for x, y in channels:
        row = wedge(left[2][x], right[2][y])
        values = {m: (int(v.const().x), int(v.const().y)) for m, v in row.items()}
        re, im = dot(dual[x, y], values)
        total += re
        imag += im
    assert imag == 0
    divisor = left[3] * right[3] * SCALE**4 * 4**4 * 96**2 * 8**4 * factorial(2)**2
    for x, (p, q) in zip(EVEN, pattern, strict=True):
        if x not in coupled:
            divisor *= 96**4 * 8**8
            divisor *= 48 * factorial(4) if p == q else 48**2 * factorial(2)**2
    return Fraction(total, divisor)


def main(control, reverse):
    words = swap_patterns() if control else words_with_mixed_count(3)
    base = cache(gamma_block(None, None, summed_fourth(1)))
    total = Fraction()
    count = population = 0
    for pattern, multiplicity in orbits(words):
        faces, protected = curvature_boundary(pattern)
        if len(faces) != 2 or len(set.union(*faces.values()) - protected) != 1:
            continue
        result = coefficient(pattern, faces, protected, base, reverse)
        print(count, multiplicity, result, flush=True)
        total += 2 * multiplicity * result
        count += 1
        population += multiplicity
    assert (count, population) == ((3, 576) if control else (80, 15072))
    print("candidate normalization, both checkerboards", total, flush=True)
    if control:
        expected = Fraction(8998309550740190185546875, 72057594037927936)
        assert total == expected, f"tree control differs from fused control by {total - expected}"


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--control", action="store_true", help="compare to the established fused subtotal (default)")
    mode.add_argument("--candidate", action="store_true", help="emit provisional three-mixed orbit values")
    parser.add_argument("--reverse-upper", action="store_true")
    args = parser.parse_args()
    main(not args.candidate, args.reverse_upper)
