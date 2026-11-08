"""Exact tree-gauge normalization for free-link two-face cores."""
from argparse import ArgumentParser
from collections import Counter
from fractions import Fraction
from functools import cache
from itertools import product
from math import factorial

from l1_direct_b_haar import add, scale, wedge
from l1_extended_four_face_gauge_join import IDENTITY, PROBE_CLASSES, indexed_mixed_dual, mixed_rows
from l1_extended_mixed_center_census import (
    AXES, EVEN, curvature_boundary, disjoint_center, orbits, swap_patterns, tensors,
    words_with_mixed_count,
)
from l1_extended_mixed_center_gamma import COMPONENTS, face_channels, gamma_block, opposite_center, opposite_source
from l1_extended_mixed_curvature_core import PAIRS, face_tensor
from l1_extended_mixed_frame_moment import SCALE, frame_edge
from l1_extended_opposed import staged_center
from l1_extended_opposed_source import summed_fourth
from l1_extended_protected_center import protected_center, summed_protected_source
from l1_extended_two_face_gamma_join import remote_environment, remote_source_replacements
from l1_extended_two_mixed_centers import contract_boundary, mixed_center, remap
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
                probe_classes=False, *, environment=remote_environment, close=close_channels,
                upper_builder=upper_factor):
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
        return upper_builder(pattern, face, faces[face], protected, reverse, source, omitted,
                            probe_classes=probe_classes and side == 0)

    left, right = upper(0), upper(1)
    coupled = {site, left[0], right[0]}
    assert len(coupled) == 3
    assert omitted is None or omitted[0] != site
    remote_omission = omitted if omitted is not None and omitted[0] not in coupled else None
    keep, env = environment(pattern, coupled, only_face=remote_omission)
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
    total, *upper_terms = close(base, sites, keep, env, upper_sites, terms)
    divisor = left[3] * right[3] * base_divisor
    for x, (p, q) in zip(EVEN, pattern, strict=True):
        if x not in coupled:
            divisor *= 96**4 * 8**8
            divisor *= 48 * factorial(4) if p == q else 48**2 * factorial(2)**2
    normal = Fraction(total, divisor * (6 if omitted is not None else 1))
    if changed is None:
        return normal
    source_keep, source_env = environment(pattern, coupled, source=True)
    assert source_keep == keep
    remote, = close(base, sites, keep, source_env, upper_sites, terms[:1])
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


def main(control, reverse, source, orbit, all_protected, probe_classes, orbit_range=None):
    expected_count, expected_population = ((3, 576) if control else
                                           (23, 3744) if all_protected else (80, 15072))
    start, stop = orbit_range or ((orbit, orbit + 1) if orbit is not None else (0, expected_count))
    if not 0 <= start < stop <= expected_count:
        raise ValueError(f"orbit interval [{start}, {stop}) exceeds the {expected_count} eligible orbits")
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
        if not start <= index < stop:
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
    assert eligible == expected_count and count == stop - start
    if (start, stop) == (0, expected_count):
        assert population == expected_population
        scope = "both checkerboards"
    else:
        scope = f"both checkerboards, orbit interval [{start}, {stop})"
    print("candidate normalization", scope, total, flush=True)
    if source:
        print("candidate retained source", scope, remote, upper, flush=True)
    if control:
        expected = Fraction(8997242104792619384765625, 72057594037927936)
        assert expected_count * total == count * expected, (total, count, expected)
        if source:
            assert expected_count * remote == count * Fraction(-909034756435048095703125, 2251799813685248)
            assert expected_count * upper == count * Fraction(-5907501623989865478515625, 36028797018963968)


def four_mixed_overlap_base(reverse, probe_classes, orbit=None, orbit_range=None, *,
                            component_remotes=False, compare_component_remotes=False,
                            family="overlap-base", census_only=False):
    from l1_extended_one_face_gauge_join import (
        check_removals, deleted_face_coefficient, disjoint_upper_factor, surviving_face_coefficient,
    )
    from l1_two_face_remote_components import ComponentRemotes

    all_protected_remaining = family == "all-protected-disjoint-base-remaining"
    all_protected = family == "all-protected-disjoint-base" or all_protected_remaining
    expected = {
        "overlap-base": 160,
        "all-protected-disjoint-base": 35,
        "all-protected-disjoint-base-remaining": 32,
    }.get(family, 25)
    start, stop = orbit_range or ((orbit, orbit + 1) if orbit is not None else (0, expected))
    if not 0 <= start < stop <= expected:
        raise ValueError(f"orbit interval [{start}, {stop}) exceeds the {expected} eligible orbits")
    eligible = []
    kinds = Counter()
    disjoint_remote_count = 0
    for pattern, multiplicity in orbits(words_with_mixed_count(4)):
        faces, protected = curvature_boundary(pattern)
        if len(faces) != 2 or len({face[0] for face in faces}) != 1:
            continue
        links = set.union(*faces.values())
        free = links - protected
        if len(free) != (0 if all_protected else 1):
            continue
        site, = {face[0] for face in faces}
        first, last = pattern[EVEN.index(site)]
        if bool(set(first) & set(last)) == all_protected:
            continue
        uppers = [upper_links(face, edges, protected) for face, edges in faces.items()]
        upper_planes = [pattern[EVEN.index(center)] for center, _ in uppers]
        disjoint_uppers = [
            (planes, incoming) for planes, (_, incoming) in zip(upper_planes, uppers, strict=True)
            if not set.intersection(*map(set, planes))
        ]
        same_plane_uppers = sum(
            tuple(sorted(axis for _, axis in incoming)) in planes
            for planes, incoming in disjoint_uppers
        )
        orbit_family = "overlap-base"
        if all_protected:
            assert not same_plane_uppers
            orbit_family = family
        elif disjoint_uppers:
            orbit_family = "same-plane-disjoint-upper" if same_plane_uppers else "split-disjoint-upper"
        if orbit_family != family:
            continue
        if family == "same-plane-disjoint-upper":
            assert len(disjoint_uppers) == same_plane_uppers == 1
        assert first != last
        assert set.intersection(*faces.values()) == free
        assert {tuple(a for a in AXES if a not in face[1:]) for face in faces} == {first, last}
        coupled = {site, *(center for center, _ in uppers)}
        assert len(coupled) == 3 and sum(a == b for a, b in pattern) == 4
        if all_protected:
            check_disjoint_tree(faces, protected, reverse)
        else:
            tree = links - {upper[reverse] for _, upper in uppers}
            vertices = {y for x, a in links for y in (x, x ^ (1 << a))}
            reached = {site}
            for _ in tree:
                for x, a in tree:
                    y = x ^ (1 << a)
                    if x in reached or y in reached:
                        reached.update((x, y))
            assert len(tree) == len(vertices) - 1 and reached == vertices
        remote_disjoint = sum(not set(a) & set(b) for x, (a, b) in zip(EVEN, pattern, strict=True)
                              if x not in coupled)
        if all_protected:
            has_disjoint = bool(disjoint_uppers or remote_disjoint)
            if has_disjoint != all_protected_remaining:
                continue
            assert remote_disjoint in (0, 1, 3)
        else:
            assert remote_disjoint in (0, 1)
        disjoint_remote_count += remote_disjoint
        kinds[len(disjoint_uppers), sum(a != b for a, b in upper_planes), remote_disjoint] += 1
        eligible.append((pattern, multiplicity, faces, protected, remote_disjoint))
    assert len(eligible) == expected
    if family == "overlap-base":
        assert sum(row[1] for row in eligible) == 30624
        assert {m: sum(kinds[0, m, d] for d in (0, 1)) for m in range(3)} == {2: 93, 1: 64, 0: 3}
        assert disjoint_remote_count == 1
    elif all_protected_remaining:
        assert sum(row[1] for row in eligible) == 4896 and disjoint_remote_count == 22
        assert kinds == {
            (1, 2, 0): 13, (1, 1, 0): 1, (0, 2, 1): 7,
            (2, 2, 1): 7, (0, 0, 1): 2, (0, 0, 3): 2,
        }
    elif all_protected:
        assert sum(row[1] for row in eligible) == 6720 and not disjoint_remote_count
        assert kinds == {(0, 2, 0): 26, (0, 1, 0): 9}
    else:
        assert all(row[1] == 192 for row in eligible) and not disjoint_remote_count
        if family == "split-disjoint-upper":
            assert kinds == {(1, 2, 0): 19, (1, 1, 0): 5, (2, 2, 0): 1}
        else:
            assert kinds == {(1, 2, 0): 22, (1, 1, 0): 3}

    selected = eligible[start:stop]
    label = f"four-mixed two-face {family} [{start}, {stop})"
    print(label, "coverage", len(selected), "orbits,",
          sum(row[1] for row in selected), "words per checkerboard", flush=True)

    def check_deletions(pattern, faces, protected):
        check_removals(pattern, expected_count=12)
        omissions = {(x, *(axis for axis in AXES if axis not in plane))
                     for x, planes in zip(EVEN, pattern, strict=True) for plane in set(planes)}
        assert len(omissions) == 12 and faces.keys() <= omissions
        for omitted in omissions:
            expected_faces = faces
            if omitted in faces:
                expected_faces = ({face: edges for face, edges in faces.items() if face != omitted}
                                  if all_protected else {})
            assert curvature_boundary(pattern, omitted=omitted) == (expected_faces, protected)

    if census_only:
        for pattern, _, faces, protected, _ in selected:
            check_deletions(pattern, faces, protected)
        print(label, "geometry and omission census passed", flush=True)
        return

    def build_upper(pattern, face, edges, protected, reverse, source=False, omitted=None, *,
                    probe_classes=False):
        center, incoming = upper_links(face, edges, protected)
        first, second = pattern[EVEN.index(center)]
        if set(first) & set(second):
            return upper_factor(pattern, face, edges, protected, reverse, source, omitted,
                                probe_classes=probe_classes)
        assert family != "overlap-base" and omitted is None
        same_plane = tuple(sorted(axis for _, axis in incoming)) in (first, second)
        assert same_plane == (family == "same-plane-disjoint-upper")
        return disjoint_upper_factor(pattern, face, edges, protected, reverse, source,
                                     probe_classes=probe_classes, same_plane=same_plane)
    remotes = ComponentRemotes() if component_remotes or compare_component_remotes else None
    if compare_component_remotes:
        if any(row[-1] for row in selected):
            raise ValueError("component map control excludes the disjoint remote fallback")
        for index, (pattern, _, faces, protected, _) in enumerate(selected, start):
            coupled = {face[0] for face in faces}
            coupled.update(upper_links(face, edges, protected)[0] for face, edges in faces.items())
            keep, normal, source = remotes.maps(pattern, coupled)
            assert (keep, normal) == remote_environment(pattern, coupled)
            assert (keep, source) == remote_environment(pattern, coupled, source=True)
            print("component remote maps exact", index, len(normal), len(source),
                  remotes.component_rows.cache_info(), flush=True)
        return
    fourth = summed_fourth(1)
    base = cache(gamma_block(None, None, fourth))
    normal, _ = staged_center(summed_fourth(0), fourth)
    shared = mixed_center(fourth)
    disjoint = disjoint_center()

    def disjoint_environment(pattern, coupled, *, source=False, only_face=None):
        assert only_face is None
        sites = {x ^ (1 << a) for x in coupled for plane in pattern[EVEN.index(x)] for a in plane}
        keep = sum(255 << (8 * x) for x in sites)
        terms = {x: row for x, row in tensors(pattern, normal, shared, disjoint).items()
                 if x not in coupled}
        if not source:
            return keep, contract_boundary(terms, keep)
        replacements = list(remote_source_replacements(pattern, terms, coupled))
        assert len(replacements) == sum(len(set(pattern[EVEN.index(x)])) for x in terms)
        for x in terms:
            if not set.intersection(*map(set, pattern[EVEN.index(x)])):
                assert sum(row[x] is not terms[x] and weight == -192
                           for row, weight in replacements) == 2
        return keep, add(*(scale(contract_boundary(row, keep), weight) for row, weight in replacements))

    totals = [Fraction() for _ in range(4)]
    for index, (pattern, multiplicity, faces, protected, remote_disjoint) in enumerate(selected, start):
        check_deletions(pattern, faces, protected)
        environment = disjoint_environment if remote_disjoint else (
            remotes.environment if remotes is not None else remote_environment
        )
        norm, remote, upper = coefficient(pattern, faces, protected, base, reverse, source=True,
                                          probe_classes=probe_classes, environment=environment,
                                          upper_builder=build_upper)
        if all_protected:
            # Each of the two base deletions leaves the other original face.
            deleted = sum(surviving_face_coefficient(
                pattern, face, edges, protected, factor=build_upper,
                environment=disjoint_environment if all_protected_remaining else remote_environment,
            ) for face, edges in faces.items())
        else:
            deleted = sum(deleted_face_coefficient(pattern, face, normal, shared, disjoint)
                          for face in faces)
        print(label, "orbit", index, "multiplicity", multiplicity, "normalization", norm,
              "remote source", remote, "upper source", upper, "deleted source", deleted, flush=True)
        for i, value in enumerate((norm, remote, upper, deleted)):
            totals[i] += 2 * multiplicity * value
    print(label, "both checkerboards normalization/remote/upper/deleted", *totals, flush=True)
    print(label, "fixed-shear numerator", sum(totals[1:]), flush=True)


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--control", action="store_true", help="compare to the corrected fused subtotal (default)")
    mode.add_argument("--candidate", action="store_true", help="emit provisional three-mixed orbit values")
    mode.add_argument("--candidate-source", action="store_true", help="emit provisional three-mixed retained-source values")
    mode.add_argument("--control-source", action="store_true", help="replay the two-mixed retained-source controls")
    mode.add_argument("--four-face-deleted-source", action="store_true")
    mode.add_argument("--four-mixed-overlap-base", action="store_true")
    mode.add_argument("--four-mixed-split-disjoint-upper", action="store_true")
    mode.add_argument("--four-mixed-same-plane-disjoint-upper", action="store_true")
    mode.add_argument("--four-mixed-all-protected-disjoint-base", action="store_true")
    mode.add_argument("--four-mixed-all-protected-disjoint-base-remaining", action="store_true")
    parser.add_argument("--census-only", action="store_true",
                        help="check four-mixed geometry and omissions without evaluating tensors")
    parser.add_argument("--reverse-upper", action="store_true")
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument("--orbit", type=int, help="evaluate a single numbered orbit")
    selection.add_argument("--orbit-range", type=int, nargs=2, metavar=("START", "STOP"),
                           help="evaluate a half-open interval of numbered orbits")
    parser.add_argument("--all-protected", action="store_true",
                        help="select the 23 all-protected three-mixed orbits")
    parser.add_argument("--probe-classes", action="store_true", help="weight one live link by its probe classes")
    remote_mode = parser.add_mutually_exclusive_group()
    remote_mode.add_argument("--component-remotes", action="store_true",
                             help="reuse exact remote component maps for the four-mixed overlap-base route")
    remote_mode.add_argument("--compare-component-remotes", action="store_true",
                             help="compare only exact remote maps with the existing evaluator")
    args = parser.parse_args()
    if args.all_protected and not (args.candidate or args.candidate_source):
        parser.error("--all-protected requires --candidate or --candidate-source")
    if (args.component_remotes or args.compare_component_remotes) and not args.four_mixed_overlap_base:
        parser.error("remote component modes require --four-mixed-overlap-base")
    if args.compare_component_remotes and args.orbit is None and args.orbit_range is None:
        parser.error("--compare-component-remotes requires an explicit orbit selection")
    family = next((name for selected, name in (
        (args.four_mixed_overlap_base, "overlap-base"),
        (args.four_mixed_all_protected_disjoint_base, "all-protected-disjoint-base"),
        (args.four_mixed_all_protected_disjoint_base_remaining, "all-protected-disjoint-base-remaining"),
        (args.four_mixed_split_disjoint_upper, "split-disjoint-upper"),
        (args.four_mixed_same_plane_disjoint_upper, "same-plane-disjoint-upper"),
    ) if selected), None)
    if args.census_only and family is None:
        parser.error("--census-only requires a four-mixed two-face mode")
    if args.census_only and (args.component_remotes or args.compare_component_remotes):
        parser.error("--census-only does not evaluate remote components")
    if family is not None:
        four_mixed_overlap_base(
            args.reverse_upper, args.probe_classes, args.orbit, args.orbit_range,
            component_remotes=args.component_remotes,
            compare_component_remotes=args.compare_component_remotes,
            family=family,
            census_only=args.census_only,
        )
    elif args.four_face_deleted_source:
        if args.orbit is not None or args.orbit_range is not None:
            parser.error("orbit selection is unavailable for the four-face deletion replay")
        replay_four_face_deletions(args.reverse_upper, args.probe_classes)
    else:
        main(not (args.candidate or args.candidate_source), args.reverse_upper,
             args.control_source or args.candidate_source, args.orbit, args.all_protected,
             args.probe_classes, args.orbit_range)
