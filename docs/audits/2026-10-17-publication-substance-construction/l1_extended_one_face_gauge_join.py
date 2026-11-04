"""Exact normalization and source numerator for supported one-face cores."""
from argparse import ArgumentParser
from collections import Counter
from fractions import Fraction
from functools import cache
from itertools import combinations, product
from math import factorial

from l1_direct_b_haar import R, add, scale, wedge
from l1_extended_four_face_gauge_join import IDENTITY, dot, dual_mixed, mixed_rows
from l1_extended_mixed_center_census import (
    AXES, EVEN, curvature_boundary, disjoint_center, orbits, source_total, tensors,
    words_with_mixed_count,
)
from l1_extended_mixed_center_gamma import COMPONENTS, face_channels
from l1_extended_mixed_curvature_core import PAIRS, face_tensor
from l1_extended_mixed_frame_moment import SCALE, anchored, frame_edge
from l1_extended_opposed import staged_center
from l1_extended_opposed_source import summed_fourth
from l1_extended_protected_center import protected_center, summed_protected_source
from l1_extended_two_face_gamma_join import remote_environment
from l1_extended_two_face_tree import upper_factor
from l1_extended_two_mixed_centers import (
    mixed_center, remap, second_channels, second_sum, source_only,
)
from l1_reduced_wedge_reference import wedge_sign


@cache
def integrated_pair():
    return second_sum(0)


@cache
def live_pair(probe):
    first = {g: frame_edge(g, 0, probe) for g in integrated_pair()}
    last = {g: remap(frame_edge(g, 0, None), (0, 2)) for g in integrated_pair()}
    return add(*(scale(wedge(first[tuple(sorted(a))], last[b]), weight)
                 for a, b, weight in second_channels()))


@cache
def residual_pair(components):
    second = integrated_pair()
    return add(*(scale(wedge(remap(second[a], (0, 3)), remap(second[b], (0, 4))), weight)
                 for (a, b), weight in face_channels(components).items()))


@cache
def source_frame(probe):
    terms = []
    for endpoint, gamma in product(range(2), range(4)):
        first = anchored(0, (), probe, gamma if endpoint == 0 else None)
        last = anchored(1, (), (), gamma if endpoint == 1 else None)
        terms.append(wedge(first, last))
    return add(*terms)


@cache
def local_mixed(source=False):
    # Canonical square. Fix both upper links and the second base link.
    face = (0, 0, 1)
    live = (0, 0)
    fixed = dict.fromkeys(((0, 1), (1, 1), (2, 0)), IDENTITY)
    rows = []
    for components in COMPONENTS:
        second = residual_pair(components)
        for (probe,), weight in face_tensor(face, (live,), fixed, components).items():
            pair = PAIRS[probe]
            first = (wedge(source_frame(pair), remap(source_frame(None), (0, 2)))
                     if source else live_pair(pair))
            exterior = wedge(first, second)
            rows.append(scale({m: v for m, v in exterior.items() if m & 255 == 255}, weight))
    return add(*rows)


@cache
def local_pure(source=False):
    if source:
        return summed_protected_source((None, None))
    return protected_center((None, None))


def coefficient(pattern, face, edges, source=False, *, both=False):
    x, k, l = face
    opposite = x ^ (1 << k) ^ (1 << l)
    first, last = pattern[EVEN.index(x)]
    assert not set(first) & set(last) and (k, l) in (first, last)
    surviving, = {first, last} - {(k, l)}
    assert pattern[EVEN.index(opposite)] == ((k, l),) * 2
    sites = (x, *(x ^ (1 << a) for a in (k, l, *surviving)))
    assert edges == {(x, k), (x, l), (x ^ (1 << k), l), (x ^ (1 << l), k)}
    pure_sites = (opposite, sites[2], sites[1])
    mixed = remap(local_mixed(), sites)
    pure = remap(local_pure(), pure_sites)
    active = (255 << (8*x)) | (255 << (8*opposite))
    keep, environment = remote_environment(pattern, {x, opposite})

    def close(left, right, env):
        raw = R.zero
        for mask, value in wedge(left, right).items():
            boundary = mask ^ active
            target = keep ^ boundary
            if target in env:
                raw += value * env[target] * wedge_sign(boundary, target)
        assert raw.is_ground and not raw.const().y
        return int(raw.const().x)

    raw = close(mixed, pure, environment)
    if source or both:
        source_keep, source_environment = remote_environment(pattern, {x, opposite}, source=True)
        assert source_keep == keep
        source_raw = (close(mixed, pure, source_environment)
                      - 24 * close(mixed, remap(local_pure(True), pure_sites), environment)
                      - 96 * factorial(2) * close(remap(local_mixed(True), sites), pure, environment))
    # Four protected frame edges use two directed Haar scales each.
    divisor = (SCALE**4 * 4**4 * 96**2 * 8**4 * 48 * factorial(2)**2)
    divisor *= 48 * SCALE**4 * 4**8 * factorial(4)
    for y, (p, q) in zip(EVEN, pattern, strict=True):
        if y not in (x, opposite):
            divisor *= 96**4 * 8**8
            divisor *= 48 * factorial(4) if p == q else 48**2 * factorial(2)**2
    if both:
        return Fraction(raw, divisor), Fraction(source_raw, 6 * divisor)
    return Fraction(source_raw, 6 * divisor) if source else Fraction(raw, divisor)


def deleted_face_coefficient(pattern, face, normal, shared, disjoint):
    assert not curvature_boundary(pattern, omitted=face)[0]
    frame_scale = 96**4 * 8**8
    pure = sum(a == b for a, b in pattern)
    divisor = (48 * frame_scale * factorial(4))**pure
    divisor *= (48**2 * frame_scale * factorial(2)**2)**(len(pattern) - pure)
    raw = source_total(pattern, tensors(pattern, normal, shared, disjoint), only_faces={face})
    return Fraction(raw, 6 * divisor)


def check_removals(pattern, *, expected_count=11):
    def edge(x, axis):
        return min(x, x ^ (1 << axis)), axis

    def support(x, frame):
        k, l = (a for a in AXES if a not in frame)
        curvature = {edge(x, k), edge(x, l), edge(x ^ (1 << k), l), edge(x ^ (1 << l), k)}
        return curvature ^ {edge(x, a) for a in frame}

    # The original word has even multiplicities. Each quadratic source
    # adds even site degree and even parity on its own geometric link.
    slots = [(x, plane) for x, pairs in zip(EVEN, pattern, strict=True)
             for plane in pairs for _ in range(2)]
    survivors = set()
    for (x, first), (y, second) in combinations(slots, 2):
        degree = Counter(x ^ (1 << a) for a in first)
        degree.update(y ^ (1 << a) for a in second)
        if all(n % 2 == 0 for n in degree.values()) and support(x, first) == support(y, second):
            survivors.add(((x, first), (y, second)))
    expected = {(slot, slot) for slot in slots}
    assert survivors == expected and len(survivors) == expected_count


def check_source_trace():
    baseline = scale(add(source_only(0), source_only(1)), SCALE**2 * 4**2)
    for start in (0, 4):
        trace = add(*(source_frame((j, j)) for j in range(start, start + 4)))
        assert scale(trace, 96 * 8**2) == baseline


@cache
def deleted_base_row(components):
    source = source_frame(None)
    pair = wedge(source, remap(source, (0, 2)))
    return {mask: value for mask, value in wedge(pair, residual_pair(components)).items()
            if mask & 255 == 255}


def surviving_face_coefficient(pattern, face, edges, protected):
    x, k, l = face
    a, b = (i for i in AXES if i not in (k, l))
    assert set(pattern[EVEN.index(x)]) == {(k, l), (a, b)}
    center, upper_sites, upper, upper_divisor = upper_factor(
        pattern, face, edges, protected, False)
    coupled = {x, center}
    keep, environment = remote_environment(pattern, coupled)
    sites = tuple(x ^ (1 << i) for i in (k, l, a, b))
    base = mixed_rows(deleted_base_row, sites, ((key,) for key in upper))
    dual = dual_mixed(keep, environment, base, upper_sites)
    total = imag = 0
    for key, row in upper.items():
        values = {m: (int(v.const().x), int(v.const().y)) for m, v in row.items()}
        re, im = dot(dual[key,], values)
        total += re
        imag += im
    assert imag == 0
    divisor = upper_divisor * SCALE**4 * 4**4 * 96**2 * 8**4 * factorial(2)
    for y, (p, q) in zip(EVEN, pattern, strict=True):
        if y not in coupled:
            divisor *= 96**4 * 8**8
            divisor *= 48 * factorial(4) if p == q else 48**2 * factorial(2)**2
    return Fraction(-2 * total, 6 * divisor)


def replay_surviving_faces():
    total = Fraction()
    count = population = 0
    for pattern, multiplicity in orbits(words_with_mixed_count(3)):
        faces, protected = curvature_boundary(pattern)
        if len(faces) != 2 or not set.union(*faces.values()) <= protected:
            continue
        check_removals(pattern)
        contribution = Fraction()
        for omitted in faces:
            rest, protection = curvature_boundary(pattern, omitted=omitted)
            assert protection == protected and len(rest) == 1
            (face, edges), = rest.items()
            assert face[0] == omitted[0] and edges <= protection
            contribution += surviving_face_coefficient(pattern, face, edges, protection)
        print("orbit", count, "multiplicity", multiplicity, "surviving-face source", contribution, flush=True)
        total += 2 * multiplicity * contribution
        count += 1
        population += multiplicity
    assert (count, population) == (23, 3744)
    print("all-protected deletion subtotal, both checkerboards", total, flush=True)


def main(deleted_face=False, retained_face=False):
    if retained_face:
        check_source_trace()
    if deleted_face:
        fourth = summed_fourth(1)
        normal, _ = staged_center(summed_fourth(0), fourth)
        shared = mixed_center(fourth)
        disjoint = disjoint_center()
    label = "normalization"
    if deleted_face:
        label = "deleted-face source"
    elif retained_face:
        label = "retained-face source"
    total = Fraction()
    population = 0
    count = 0
    for pattern, multiplicity in orbits(words_with_mixed_count(3)):
        faces, protected = curvature_boundary(pattern)
        if len(faces) != 1:
            continue
        (face, edges), = faces.items()
        assert edges <= protected
        check_removals(pattern)
        if deleted_face:
            value = deleted_face_coefficient(pattern, face, normal, shared, disjoint)
        else:
            value = coefficient(pattern, face, edges, retained_face)
        print("orbit", count, "multiplicity", multiplicity, label, value, flush=True)
        total += 2 * multiplicity * value
        population += multiplicity
        count += 1
    assert (count, population) == (13, 2208)
    print(f"one-face {label}, both checkerboards", total)


def four_mixed_pure_upper():
    words = {pattern for pattern in words_with_mixed_count(4)
             if sum(not set(a) & set(b) for a, b in pattern) == 1}
    selected = []
    one_face_count = 0
    for pattern, multiplicity in orbits(words):
        faces, protected = curvature_boundary(pattern)
        if len(faces) != 1:
            continue
        index = one_face_count
        one_face_count += 1
        (face, edges), = faces.items()
        x, k, l = face
        first, second = pattern[EVEN.index(x)]
        opposite = x ^ (1 << k) ^ (1 << l)
        assert edges <= protected and not set(first) & set(second) and (k, l) in (first, second)
        if pattern[EVEN.index(opposite)] != ((k, l),) * 2:
            continue
        assert all(set(a) & set(b) for y, (a, b) in zip(EVEN, pattern, strict=True) if y not in (x, opposite))
        assert multiplicity == 192 and sum(a == b for a, b in pattern) == 4
        check_removals(pattern, expected_count=12)
        omissions = {(y, *(axis for axis in AXES if axis not in plane))
                     for y, planes in zip(EVEN, pattern, strict=True) for plane in set(planes)}
        assert len(omissions) == 12 and face in omissions
        for omitted in omissions:
            assert curvature_boundary(pattern, omitted=omitted) == (
                {} if omitted == face else faces, protected,
            )
        selected.append((index, multiplicity, pattern, face, edges))
    assert one_face_count == 44 and [row[0] for row in selected] == [3, 4, 13, 14, 15, 16]
    print("four-mixed one-face pure-upper coverage", len(selected), "orbits,",
          sum(row[1] for row in selected), "words per checkerboard", flush=True)
    fourth = summed_fourth(1)
    normal, _ = staged_center(summed_fourth(0), fourth)
    shared = mixed_center(fourth)
    disjoint = disjoint_center()
    totals = [Fraction() for _ in range(3)]
    for index, multiplicity, pattern, face, edges in selected:
        norm, retained = coefficient(pattern, face, edges, both=True)
        deleted = deleted_face_coefficient(pattern, face, normal, shared, disjoint)
        print("four-mixed one-face pure-upper orbit", index, "multiplicity", multiplicity,
              "normalization", norm, "retained source", retained, "deleted source", deleted, flush=True)
        for i, value in enumerate((norm, retained, deleted)):
            totals[i] += 2 * multiplicity * value
    print("four-mixed one-face pure-upper both checkerboards normalization/retained/deleted",
          *totals, flush=True)
    print("four-mixed one-face pure-upper fixed-shear numerator", sum(totals[1:]), flush=True)


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--deleted-face-source", action="store_true")
    mode.add_argument("--retained-face-source", action="store_true")
    mode.add_argument("--surviving-face-source", action="store_true")
    mode.add_argument("--four-mixed-pure-upper", action="store_true")
    args = parser.parse_args()
    if args.four_mixed_pure_upper:
        four_mixed_pure_upper()
    elif args.surviving_face_source:
        replay_surviving_faces()
    else:
        main(args.deleted_face_source, args.retained_face_source)
