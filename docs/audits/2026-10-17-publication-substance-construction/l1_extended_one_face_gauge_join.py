"""Exact normalization and source numerator for supported one-face cores."""
from argparse import ArgumentParser
from collections import Counter
from fractions import Fraction
from functools import cache
from itertools import combinations, product
from math import factorial

from l1_direct_b_haar import R, add, scale, wedge
from l1_extended_four_face_gauge_join import IDENTITY, PROBE_CLASSES, dot, dual_mixed, indexed_mixed_dual, mixed_rows
from l1_extended_mixed_center_census import (
    AXES, EVEN, curvature_boundary, disjoint_center, disjoint_pair, orbits, source_total,
    summed_source_tensor, tensors, words_with_mixed_count,
)
from l1_extended_mixed_center_gamma import COMPONENTS, face_channels, opposite_source_edge
from l1_extended_mixed_curvature_core import PAIRS, face_tensor
from l1_extended_mixed_frame_moment import SCALE, anchored, frame_edge
from l1_extended_opposed import staged_center
from l1_extended_opposed_source import summed_fourth
from l1_extended_protected_center import protected_center, summed_protected_source
from l1_extended_two_face_gamma_join import remote_environment, remote_source_replacements
from l1_extended_two_face_tree import close_upper, upper_factor, upper_links
from l1_extended_two_mixed_centers import (
    contract_boundary, mixed_center, remap, second_channels, second_sum, source_only,
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


def coefficient(pattern, face, edges, source=False, *, both=False, environment_builder=remote_environment):
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
    keep, environment = environment_builder(pattern, {x, opposite})

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
        source_keep, source_environment = environment_builder(pattern, {x, opposite}, source=True)
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


def four_mixed_pure_upper(disjoint_count=1):
    expected = {1: (44, [3, 4, 13, 14, 15, 16]), 2: (13, [1, 2, 3, 4, 5, 6, 7])}
    expected_count, expected_indices = expected[disjoint_count]
    label = ("four-mixed one-face pure-upper" if disjoint_count == 1
             else "four-mixed one-face pure-upper d2")
    words = {pattern for pattern in words_with_mixed_count(4)
             if sum(not set(a) & set(b) for a, b in pattern) == disjoint_count}
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
        remote_disjoint = sum(not set(a) & set(b) for y, (a, b) in zip(EVEN, pattern, strict=True)
                              if y not in (x, opposite))
        assert remote_disjoint == disjoint_count - 1
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
    assert one_face_count == expected_count and [row[0] for row in selected] == expected_indices
    print(label, "coverage", len(selected), "orbits,",
          sum(row[1] for row in selected), "words per checkerboard", flush=True)
    fourth = summed_fourth(1)
    normal, _ = staged_center(summed_fourth(0), fourth)
    shared = mixed_center(fourth)
    disjoint = disjoint_center()
    def disjoint_environment(pattern, coupled, *, source=False):
        # The disjoint center's four second moments use the same total
        # 96^4 * 8^8 frame scale as the overlapping center's 2+4+2 moments.
        open_sites = {x ^ (1 << axis) for x in coupled
                      for plane in pattern[EVEN.index(x)] for axis in plane}
        keep = sum(255 << (8 * x) for x in open_sites)
        terms = {x: row for x, row in tensors(pattern, normal, shared, disjoint).items()
                 if x not in coupled}
        if not source:
            return keep, contract_boundary(terms, keep)
        replacements = list(remote_source_replacements(pattern, terms, coupled))
        disjoint_center_site, = (x for x in terms
                                 if not set.intersection(*map(set, pattern[EVEN.index(x)])))
        assert len(replacements) == 9
        assert sum(row[disjoint_center_site] is not terms[disjoint_center_site] and weight == -192
                   for row, weight in replacements) == 2
        return keep, add(*(scale(contract_boundary(row, keep), weight) for row, weight in replacements))

    environment = disjoint_environment if disjoint_count == 2 else remote_environment
    totals = [Fraction() for _ in range(3)]
    for index, multiplicity, pattern, face, edges in selected:
        norm, retained = coefficient(pattern, face, edges, both=True, environment_builder=environment)
        deleted = deleted_face_coefficient(pattern, face, normal, shared, disjoint)
        print(label, "orbit", index, "multiplicity", multiplicity,
              "normalization", norm, "retained source", retained, "deleted source", deleted, flush=True)
        for i, value in enumerate((norm, retained, deleted)):
            totals[i] += 2 * multiplicity * value
    print(label, "both checkerboards normalization/retained/deleted",
          *totals, flush=True)
    print(label, "fixed-shear numerator", sum(totals[1:]), flush=True)


@cache
def overlap_base_row(components, source=False):
    if source:
        edge = source_frame(None)
        peeled = wedge(edge, remap(edge, (0, 2)))
    else:
        peeled = live_pair(None)
    return {mask: value for mask, value in wedge(peeled, residual_pair(components)).items()
            if mask & 255 == 255}


@cache
def disjoint_upper_pair(probe, source=False):
    if source:
        plain = remap(add(source_only(0), source_only(1)), (0, 2))
        return wedge(opposite_source_edge(1, (probe,)), plain)
    protected = {labels: frame_edge(labels, 1, probe) for labels in integrated_pair()}
    plain = integrated_pair()
    return add(*(scale(wedge(protected[tuple(sorted(a))], remap(plain[b], (0, 2))), weight)
                 for a, b, weight in second_channels()))


def disjoint_upper_row(first, second):
    return {mask: value for mask, value in wedge(first, remap(second, (0, 3, 4))).items()
            if mask & 255 == 255}


@cache
def disjoint_upper_tensor(probe, source):
    live = disjoint_upper_pair(probe)
    fixed = disjoint_upper_pair(None)
    if not source:
        return disjoint_upper_row(live, fixed)
    return add(disjoint_upper_row(disjoint_upper_pair(probe, True), fixed),
               disjoint_upper_row(live, disjoint_upper_pair(None, True)))


def disjoint_upper_factor(pattern, face, edges, protected, reverse, source=False, *, probe_classes):
    upper, links = upper_links(face, edges, protected)
    if reverse:
        links = links[::-1]
    planes = pattern[EVEN.index(upper)]
    assert not set(planes[0]) & set(planes[1])
    axes = []
    for _, axis in links:
        plane, = (plane for plane in planes if axis in plane)
        other, = set(plane) - {axis}
        axes.extend((axis, other))
    assert set(axes) == set(AXES)
    sites = tuple(upper ^ (1 << axis) for axis in axes)
    fixed = dict.fromkeys(edges - {links[0]}, IDENTITY)
    multiplicities = dict(PROBE_CLASSES) if probe_classes else dict.fromkeys(PAIRS, 1)
    rows = {}
    for components in COMPONENTS:
        terms = face_tensor(face, links[:1], fixed, components)
        local = add(*(scale(disjoint_upper_tensor(PAIRS[i], source),
                            weight * multiplicities[PAIRS[i]])
                      for (i,), weight in terms.items() if PAIRS[i] in multiplicities))
        if local:
            adjustment = -192 if source else 1
            rows[components] = remap({mask >> 8: adjustment * value
                                      for mask, value in local.items()}, sites)
    divisor = SCALE**4 * 4**4 * 96**2 * 8**4 * 48**2 * factorial(2)**2
    return upper, sites, rows, divisor


def check_disjoint_upper_traces():
    ratio, remainder = divmod(SCALE**2 * 4**2, 96 * 8**2)
    assert not remainder and ratio == 96
    source_pair = add(source_only(0), source_only(1))
    source_pair = wedge(source_pair, remap(source_pair, (0, 2)))
    for start in (0, 4):
        diagonal = [(i, i) for i in range(start, start + 4)]
        traced = add(*(disjoint_upper_pair(probe) for probe in diagonal))
        source = add(*(disjoint_upper_pair(probe, True) for probe in diagonal))
        assert traced == scale(disjoint_pair(), ratio)
        assert source == scale(source_pair, ratio)
        assert disjoint_upper_row(traced, traced) == scale(disjoint_center(), ratio**2)
        assert disjoint_upper_row(source, traced) == scale(summed_source_tensor(4), ratio**2)
        assert disjoint_upper_row(traced, source) == scale(summed_source_tensor(5), ratio**2)
    print("disjoint-upper two-chirality action and source traces passed", flush=True)


def overlap_upper_coefficient(pattern, face, edges, protected, *, factor=upper_factor):
    x, k, l = face
    base_axes = (k, l, *(a for a in AXES if a not in (k, l)))
    base_sites = tuple(x ^ (1 << a) for a in base_axes)
    upper, upper_sites, ordinary, upper_divisor = factor(
        pattern, face, edges, protected, False, probe_classes=True,
    )
    _, _, changed, source_divisor = factor(
        pattern, face, edges, protected, False, source=True, probe_classes=True,
    )
    assert source_divisor == upper_divisor
    coupled = {x, upper}
    keep, environment = remote_environment(pattern, coupled)
    source_keep, source_environment = remote_environment(pattern, coupled, source=True)
    assert source_keep == keep
    dual = indexed_mixed_dual(keep, environment, set(upper_sites))
    source_dual = indexed_mixed_dual(keep, source_environment, set(upper_sites))
    totals = [[0, 0] for _ in range(4)]
    unit = {0: R.one}
    for components in sorted(ordinary.keys() | changed.keys()):
        key = (components,)
        row = mixed_rows(overlap_base_row, base_sites, (key,))[key]
        source_row = mixed_rows(lambda c: overlap_base_row(c, True), base_sites, (key,))[key]
        boundary = dual(row)
        upper_row = ordinary.get(components, {})
        terms = (
            close_upper(upper_row, unit, boundary),
            close_upper(upper_row, unit, source_dual(row)),
            close_upper(changed.get(components, {}), unit, boundary),
            close_upper(upper_row, unit, dual(source_row)),
        )
        for subtotal, (re, im) in zip(totals, terms, strict=True):
            subtotal[0] += re
            subtotal[1] += im
    assert all(im == 0 for _, im in totals)
    norm, remote, upper_source, base_source = (re for re, _ in totals)
    # The fixed base edges carry the peeled plane; its complementary
    # frame pair is unprobed and still weighted by the residual face.
    divisor = upper_divisor * 48 * SCALE**4 * 4**4 * 96**2 * 8**4 * factorial(2)**2
    for y, (first, second) in zip(EVEN, pattern, strict=True):
        if y not in coupled:
            divisor *= 96**4 * 8**8
            divisor *= 48 * factorial(4) if first == second else 48**2 * factorial(2)**2
    return Fraction(norm, divisor), Fraction(remote + upper_source - 192 * base_source, 6 * divisor)


def four_mixed_overlap_upper(orbit=None, *, disjoint_upper=False):
    disjoint_count = 2 if disjoint_upper else 1
    words = {pattern for pattern in words_with_mixed_count(4)
             if sum(not set(a) & set(b) for a, b in pattern) == disjoint_count}
    selected = []
    incidence = Counter()
    one_face_count = 0
    for pattern, multiplicity in orbits(words):
        faces, protected = curvature_boundary(pattern)
        if len(faces) != 1:
            continue
        index = one_face_count
        one_face_count += 1
        (face, edges), = faces.items()
        x, k, l = face
        upper = x ^ (1 << k) ^ (1 << l)
        base_planes = pattern[EVEN.index(x)]
        first, last = pattern[EVEN.index(upper)]
        assert edges <= protected and not set.intersection(*map(set, base_planes))
        assert (k, l) in base_planes
        if first == last:
            assert first == (k, l)
            continue
        common = set(first) & set(last)
        assert len(common) == (0 if disjoint_upper else 1)
        assert {k, l} <= set(first) | set(last)
        if disjoint_upper:
            assert all(len(set(plane) & {k, l}) == 1 for plane in (first, last))
        assert all(set(a) & set(b) for y, (a, b) in zip(EVEN, pattern, strict=True)
                   if y not in (x, upper))
        assert sum(a == b for a, b in pattern) == 4
        check_removals(pattern, expected_count=12)
        for y, planes in zip(EVEN, pattern, strict=True):
            for plane in set(planes):
                omitted = (y, *(axis for axis in AXES if axis not in plane))
                assert curvature_boundary(pattern, omitted=omitted) == (
                    {} if omitted == face else faces, protected,
                )
        incidence[len(common & {k, l})] += 1
        selected.append((index, multiplicity, pattern, face, edges, protected))
    if disjoint_upper:
        assert one_face_count == 13 and incidence == {0: 6}
        assert [(i, n) for i, n, *_ in selected] == [
            (0, 96), (8, 192), (9, 192), (10, 192), (11, 96), (12, 192),
        ]
        upper_type = "disjoint-upper"
        factor = disjoint_upper_factor
    else:
        assert one_face_count == 44 and incidence == {0: 23, 1: 15}
        assert all(n == 192 for _, n, *_ in selected)
        upper_type = "overlap-upper"
        factor = upper_factor
    if orbit is not None:
        selected = [row for row in selected if row[0] == orbit]
        if not selected:
            raise ValueError(f"one-face orbit {orbit} has no supported {upper_type} in this stratum")
    label = f"four-mixed one-face {upper_type}"
    if orbit is not None:
        label += f" selected {orbit}"
    print(label, "coverage", len(selected), "orbits,",
          sum(row[1] for row in selected), "words per checkerboard", flush=True)
    fourth = summed_fourth(1)
    normal, _ = staged_center(summed_fourth(0), fourth)
    shared = mixed_center(fourth)
    disjoint = disjoint_center()
    totals = [Fraction() for _ in range(3)]
    for index, multiplicity, pattern, face, edges, protected in selected:
        norm, retained = overlap_upper_coefficient(pattern, face, edges, protected, factor=factor)
        if index == 0 and not disjoint_upper:
            assert norm == Fraction(20210328503647055859375, 9007199254740992)
            assert retained == Fraction(-211023361946496119203125, 18014398509481984)
        deleted = deleted_face_coefficient(pattern, face, normal, shared, disjoint)
        print(label, "orbit", index, "multiplicity", multiplicity,
              "normalization", norm, "retained source", retained, "deleted source", deleted, flush=True)
        for i, value in enumerate((norm, retained, deleted)):
            totals[i] += 2 * multiplicity * value
    print(label, "both checkerboards normalization/retained/deleted", *totals, flush=True)
    print(label, "fixed-shear numerator", sum(totals[1:]), flush=True)


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--deleted-face-source", action="store_true")
    mode.add_argument("--retained-face-source", action="store_true")
    mode.add_argument("--surviving-face-source", action="store_true")
    mode.add_argument("--four-mixed-pure-upper", action="store_true")
    mode.add_argument("--four-mixed-pure-upper-d2", action="store_true")
    mode.add_argument("--four-mixed-overlap-upper", action="store_true")
    mode.add_argument("--four-mixed-disjoint-upper", action="store_true")
    mode.add_argument("--upper-trace-controls", action="store_true")
    parser.add_argument("--overlap-orbit", type=int,
                        help="select one orbit by its one-disjoint one-face census ID")
    parser.add_argument("--disjoint-upper-orbit", type=int,
                        help="select one orbit by its two-disjoint one-face census ID")
    args = parser.parse_args()
    if args.overlap_orbit is not None and not args.four_mixed_overlap_upper:
        parser.error("--overlap-orbit requires --four-mixed-overlap-upper")
    if args.disjoint_upper_orbit is not None and not args.four_mixed_disjoint_upper:
        parser.error("--disjoint-upper-orbit requires --four-mixed-disjoint-upper")
    if args.upper_trace_controls:
        check_disjoint_upper_traces()
    elif args.four_mixed_disjoint_upper:
        four_mixed_overlap_upper(args.disjoint_upper_orbit, disjoint_upper=True)
    elif args.four_mixed_overlap_upper:
        four_mixed_overlap_upper(args.overlap_orbit)
    elif args.four_mixed_pure_upper or args.four_mixed_pure_upper_d2:
        four_mixed_pure_upper(2 if args.four_mixed_pure_upper_d2 else 1)
    elif args.surviving_face_source:
        replay_surviving_faces()
    else:
        main(args.deleted_face_source, args.retained_face_source)
