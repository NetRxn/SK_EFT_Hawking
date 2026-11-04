"""Exact normalization for the five three-face cores with three mixed centers."""
from argparse import ArgumentParser
from collections import defaultdict
from fractions import Fraction
from functools import cache
from itertools import product
from math import factorial

from l1_direct_b_haar import add, scale, wedge
from l1_extended_four_face_gauge_join import IDENTITY, dual_mixed, mixed_rows
from l1_extended_mixed_center_census import AXES, EVEN, curvature_boundary, orbits, words_with_mixed_count
from l1_extended_mixed_center_gamma import COMPONENTS, gamma_block
from l1_extended_mixed_curvature_core import PAIRS, face_tensor
from l1_extended_mixed_frame_moment import SCALE
from l1_extended_one_face_gauge_join import check_removals, live_pair, source_frame
from l1_extended_opposed_source import summed_fourth
from l1_extended_protected_center import protected_center, summed_protected_source
from l1_extended_two_face_gamma_join import remote_environment
from l1_extended_two_face_tree import close_upper, fixed_frame_pair, upper_factor
from l1_extended_two_mixed_centers import remap


def geometry(faces, protected, reverse):
    upper = defaultdict(list)
    live = set()
    for face, edges in faces.items():
        x, k, l = face
        center = x ^ (1 << k) ^ (1 << l)
        choices = sorted((y, a) for y, a in edges & protected if y ^ (1 << a) == center)
        edge = choices[-1] if reverse else choices[0]
        live.add(edge)
        upper[center].append((edge[1], face, edge))
    links = set.union(*faces.values())
    tree = links - live
    reached = {min(tree)[0]}
    for _ in tree:
        for x, a in tree:
            y = x ^ (1 << a)
            if x in reached or y in reached:
                reached.update((x, y))
    assert len(tree) == 7 and len(reached) == 8
    assert sorted(map(len, upper.values())) == [1, 2]
    assert all(len(edges & live) == 1 for edges in faces.values())
    return upper, tree


def upper_probes(face, edges, live, tree):
    fixed = dict.fromkeys(edges & tree, IDENTITY)
    rows = {}
    for components in COMPONENTS:
        terms = face_tensor(face, (live,), fixed, components)
        if terms:
            ((index,), weight), = terms.items()
            rows[components] = PAIRS[index], weight
    return rows


@cache
def disjoint_row(components, source=False):
    if source:
        edge = source_frame(None)
        peeled = wedge(edge, remap(edge, (0, 2)))
    else:
        peeled = live_pair(None)
    residual = remap(fixed_frame_pair(components), (0, 3, 4))
    return {mask >> 8: value for mask, value in wedge(peeled, residual).items()
            if mask & 255 == 255}


@cache
def pure_row(first, last, source=False):
    tensor = summed_protected_source if source else protected_center
    return {mask >> 8: value for mask, value in tensor((first, last)).items()
            if mask & 255 == 255}


def coefficient(pattern, faces, protected, base, reverse, source=False):
    upper, tree = geometry(faces, protected, reverse)
    (shared, shared_items), = [(x, sorted(items)) for x, items in upper.items() if len(items) == 2]
    (single, single_items), = [(x, items) for x, items in upper.items() if len(items) == 1]
    singles = [face for face in faces if sum(other[0] == face[0] for other in faces) == 1]
    disjoint_face, = singles
    disjoint, k, l = disjoint_face
    p, q = pattern[EVEN.index(disjoint)]
    assert not set(p) & set(q)
    survivor, = {p, q} - {(k, l)}
    disjoint_sites = tuple(disjoint ^ (1 << a) for a in (k, l, *survivor))
    overlapping, = {face[0] for face in faces} - {disjoint}
    p, q = pattern[EVEN.index(overlapping)]
    common, = set(p) & set(q)
    a, b = sorted(set(p) ^ set(q))
    overlap_sites = tuple(overlapping ^ (1 << i) for i in (a, common, b))
    ordered = [next(f for f in faces if f[0] == overlapping and i not in f[1:])
               for i in (a, b)]

    shared_sites = tuple(shared ^ (1 << axis) for axis, _, _ in shared_items)
    shared_faces = tuple(face for _, face, _ in shared_items)
    assert disjoint_face in shared_faces
    side = shared_faces.index(disjoint_face)
    shared_face = shared_faces[1 - side]
    _, single_face, _ = single_items[0]
    assert {shared_face, single_face} == set(ordered)
    assert pattern[EVEN.index(shared)] == (tuple(axis for axis, _, _ in shared_items),) * 2
    assert len(set(pattern[EVEN.index(single)])) == 1
    shared_probes = [upper_probes(face, faces[face], edge, tree) for _, face, edge in shared_items]
    def group_rows(replace_pure=False, replace_disjoint=False):
        grouped = {}
        for key, (probe, weight) in shared_probes[1 - side].items():
            rows = []
            for label, (other, other_weight) in shared_probes[side].items():
                args = (other, probe) if side == 0 else (probe, other)
                pure = remap(pure_row(*args, source=replace_pure), shared_sites)
                local = remap(disjoint_row(label, source=replace_disjoint), disjoint_sites)
                rows.append(scale(wedge(pure, local), weight * other_weight))
            grouped[key] = add(*rows)
        return grouped

    grouped = group_rows()
    _, single_sites, single_rows, single_divisor = upper_factor(
        pattern, single_face, faces[single_face], protected, reverse)
    coupled = {shared, single, disjoint, overlapping}
    keep, env = remote_environment(pattern, coupled)
    shared_first = ordered[0] == shared_face
    changed_single = {}
    if source:
        _, _, changed_single, _ = upper_factor(
            pattern, single_face, faces[single_face], protected, reverse, source=True)
    single_keys = single_rows.keys() | changed_single.keys()
    channels = tuple(product(grouped, single_keys) if shared_first else product(single_keys, grouped))
    first = mixed_rows(base, overlap_sites, channels)
    sites = set(shared_sites) | set(disjoint_sites) | set(single_sites)
    dual = dual_mixed(keep, env, first, sites)

    def close(grouped_rows, singles, boundary):
        left, right = (grouped_rows, singles) if shared_first else (singles, grouped_rows)
        real = imag = 0
        for x, y in product(left, right):
            re, im = close_upper(left[x], right[y], boundary[x, y])
            real += re
            imag += im
        assert imag == 0
        return real

    real = close(grouped, single_rows, dual)
    divisor = single_divisor * 48 * SCALE**4 * 4**8 * factorial(4)
    divisor *= 48 * SCALE**8 * 4**8 * factorial(2)**2
    divisor *= SCALE**4 * 4**4 * 96**2 * 8**4 * factorial(2)**2
    for x, (p, q) in zip(EVEN, pattern, strict=True):
        if x not in coupled:
            divisor *= 96**4 * 8**8
            divisor *= 48 * factorial(4) if p == q else 48**2 * factorial(2)**2
    normal = Fraction(real, divisor)
    if not source:
        return normal
    source_keep, source_env = remote_environment(pattern, coupled, source=True)
    assert source_keep == keep
    remote_dual = dual_mixed(keep, source_env, first, sites)
    remote = close(grouped, single_rows, remote_dual)
    upper_term = (close(grouped, changed_single, dual)
                  - 24 * close(group_rows(replace_pure=True), single_rows, dual))
    disjoint_term = -192 * close(group_rows(replace_disjoint=True), single_rows, dual)
    return normal, tuple(Fraction(term, 6 * divisor) for term in (remote, upper_term, disjoint_term))


def main(reverse, source):
    base = cache(gamma_block(None, None, summed_fourth(1)))
    total = Fraction()
    count = population = 0
    subtotals = [Fraction() for _ in range(3)]
    for pattern, multiplicity in orbits(words_with_mixed_count(3)):
        faces, protected = curvature_boundary(pattern)
        if len(faces) != 3:
            continue
        if source:
            check_removals(pattern)
            retained = 0
            for x, planes in zip(EVEN, pattern, strict=True):
                for plane in set(planes):
                    omitted = (x, *(axis for axis in AXES if axis not in plane))
                    if omitted in faces:
                        continue
                    assert curvature_boundary(pattern, omitted=omitted) == (faces, protected)
                    retained += 1
            assert retained == 8
        result = coefficient(pattern, faces, protected, base, reverse, source)
        if source:
            result, terms = result
            print("source orbit", count, "remote, upper, base", *terms, flush=True)
            for i, term in enumerate(terms):
                subtotals[i] += 2 * multiplicity * term
        print("orbit", count, "multiplicity", multiplicity, "normalization", result, flush=True)
        total += 2 * multiplicity * result
        count += 1
        population += multiplicity
    assert (count, population) == (5, 960)
    print("three-face normalization, both checkerboards", total, flush=True)
    if source:
        print("three-face retained source, both checkerboards", *subtotals, flush=True)


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--reverse-upper", action="store_true")
    parser.add_argument("--source", action="store_true")
    args = parser.parse_args()
    main(args.reverse_upper, args.source)
