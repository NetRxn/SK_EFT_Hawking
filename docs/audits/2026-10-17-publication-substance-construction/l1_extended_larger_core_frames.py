"""Directed frame routing and local tensors for the larger three-mixed cores."""
from argparse import ArgumentParser
from collections import Counter
from fractions import Fraction
from functools import cache, lru_cache
from itertools import combinations, product
from math import factorial, prod

from l1_direct_b_haar import add, scale, wedge
from l1_extended_four_face_gauge_join import IDENTITY, larger_core_tree
from l1_extended_mixed_center_census import AXES, EVEN, curvature_boundary, orbits, words_with_mixed_count
from l1_extended_mixed_center_gamma import (
    COMPONENTS, contract_gamma, contract_gamma_products, face_channels,
    gamma_block, gamma_products, peeled_channels,
)
from l1_extended_mixed_curvature_core import PAIRS as PROBE_PAIRS, PAIR_INDEX, face_tensor
from l1_extended_mixed_frame_join import join_factors
from l1_extended_mixed_frame_moment import SCALE, anchored, frame_edge_moments, source_edge_moments
from l1_extended_one_face_gauge_join import check_removals
from l1_extended_opposed import close_second_frame, staged_center
from l1_extended_opposed_source import PAIRS, summed_fourth
from l1_extended_two_mixed_centers import contract, remap
from l1_normalization_opposed_fourth import tuples


def layout(pattern, faces, protected, minimize_keys=False):
    cost = tree_key_cost(faces) if minimize_keys else None
    _, tree, live = larger_core_tree(faces, protected, cost=cost)
    core_links = set.union(*faces.values())
    slots = {}
    routed = Counter()
    for center, planes in zip(EVEN, pattern, strict=True):
        directions = sorted(set.union(*(set(p) for p in planes)))
        slots[center] = {}
        for axis in directions:
            anchors = ((center, axis), (center ^ (1 << axis), axis))
            states = tuple(edge if edge in live else None if edge in tree else ()
                           for edge in anchors)
            slots[center][axis] = states
            routed.update(edge for edge, state in zip(anchors, states, strict=True) if state != ())
    assert routed == Counter(core_links & protected)
    return slots, tree, live


@cache
def edge_table(degree, moments, slot):
    labels = tuples if degree == 4 else PAIRS
    return {g: remap(frame_edge_moments(g, moments), (0, slot)) for g in labels}


@cache
def source_edge_table(moments, slot):
    return {labels: remap(add(*(source_edge_moments(labels, moments, endpoint)
                               for endpoint in range(2))), (0, slot))
            for labels in PAIRS}


@cache
def source_only_table(moments, slot):
    terms = []
    for endpoint, gamma in product(range(2), range(4)):
        terms.append(wedge(*(anchored(anchor, (), moments[anchor],
                                     gamma if endpoint == anchor else None)
                            for anchor in range(2))))
    return remap(add(*terms), (0, slot))


def source_center_tensor(planes, directions, moments, removed):
    channels = peeled_channels()
    if planes[0] == planes[1]:
        first, second = (source_edge_table(m, i) for i, m in enumerate(moments, 1))
        boundary = {b: add(*(scale(first[a], weight) for (a, key), weight in channels.items()
                             if key == b))
                    for b in PAIRS}
        return scale(close_second_frame(boundary, second), -24)

    removed_slot = 0 if directions[0] in removed else 2
    survivor = 2 - removed_slot
    common = source_edge_table(moments[1], 2)
    other = edge_table(2, moments[survivor], survivor + 1)
    source = source_only_table(moments[removed_slot], removed_slot + 1)
    retained = add(*(scale(wedge(common[a], other[b]), weight)
                     for (a, b), weight in channels.items()))
    return {mask: -192 * value for mask, value in wedge(retained, source).items()
            if mask & 255 == 255}


def center_tensor(center, planes, slots, components, probes, removed=None, products=None):
    first, last = planes
    if first == last:
        directions = first
    else:
        common, = set(first) & set(last)
        a, b = sorted(set(first) ^ set(last))
        directions = (a, common, b)
    moments = [tuple(probes[state] if state else state for state in slots[axis])
               for axis in directions]
    degrees = [2 * sum(axis in p for p in planes) for axis in directions]
    divisor = SCALE**(2 * len(directions)) * 4**sum(degrees)
    if removed is not None:
        assert removed in planes and not components
        curvature_scale = 48 * factorial(4) if first == last else 48**2 * factorial(2)**2
        return directions, source_center_tensor(planes, directions, moments, removed), divisor * curvature_scale

    tensors = [edge_table(d, m, i) for i, (d, m) in enumerate(zip(degrees, moments, strict=True), 1)]
    if first == last:
        k, l = (axis for axis in AXES if axis not in first)
        assert (center, k, l) not in components
        result, _ = staged_center(*tensors)
        return directions, result, divisor * 48 * factorial(4)

    # Curvature components belong to the face complementary to the
    # exclusive frame axis, independent of which directed link is live.
    weights = []
    for exclusive in (directions[0], directions[2]):
        plane, = [p for p in planes if exclusive in p]
        k, l = (axis for axis in AXES if axis not in plane)
        labels = components.get((center, k, l))
        weights.append(peeled_channels() if labels is None else face_channels(labels))
        if labels is None:
            divisor *= 48
    if products is None:
        result = contract_gamma(*tensors, *weights)
    else:
        result = contract_gamma_products(products(tuple(moments)), *weights)
    return directions, result, divisor * factorial(2)**2


def probe_slice(faces, tree, live):
    probes = {}
    components = {}
    for face, edges in faces.items():
        active = tuple(sorted(edges & live))
        fixed = dict.fromkeys(edges & tree, IDENTITY)
        assert active
        pairs = ((1, 1),) + ((0, 0),) * (len(active) - 1)
        key = tuple(PAIR_INDEX[pair] for pair in pairs)
        rows = {labels: value for labels in COMPONENTS
                if (value := face_tensor(face, active, fixed, labels).get(key, 0))}
        assert rows == {(0, 0): 1}
        components[face] = (0, 0)
        probes.update(zip(active, pairs, strict=True))
    assert probes.keys() == live
    return components, probes


def contract_slice(pattern, slots, components, probes, replacement=None):
    divisor = 1
    terms = {}
    for center, planes in zip(EVEN, pattern, strict=True):
        removed = replacement[1] if replacement is not None and center == replacement[0] else None
        based = {face: labels for face, labels in components.items() if face[0] == center}
        directions, local, denominator = center_tensor(center, planes, slots[center], based, probes, removed)
        terms[center] = remap(local, (center, *(center ^ (1 << axis) for axis in directions)))
        divisor *= denominator
    result = contract(terms)
    assert result.is_ground and not result.const().y
    return Fraction(int(result.const().x), divisor * (6 if replacement is not None else 1))


def face_factor(face, edges, tree, live, selection=None):
    active = tuple(sorted(edges & live))
    fixed = dict.fromkeys(edges & tree, IDENTITY)
    rows = {}
    for labels in COMPONENTS:
        for keys, value in face_tensor(face, active, fixed, labels).items():
            key = (labels, *keys)
            if selection is None or key == selection:
                rows[key] = {0: (value, 0)}
    assert rows
    return (face, *active), rows


def face_factors(faces, tree, live, selection=None):
    return [face_factor(face, edges, tree, live, None if selection is None else selection[face])
            for face, edges in faces.items()]


def projected_keys(center, factor):
    axes, rows = factor
    owners = [axes[0][0], *(x if x in EVEN else x ^ (1 << a) for x, a in axes[1:])]
    indices = tuple(i for i, owner in enumerate(owners) if owner == center)
    if not indices:
        return (), {()}
    return tuple(axes[i] for i in indices), {tuple(row[i] for i in indices) for row in rows}


def tree_key_cost(faces):
    @cache
    def projection_sizes(face, active):
        edges = faces[face]
        factor = face_factor(face, edges, edges - active, active)
        return tuple(len(projected_keys(center, factor)[1]) for center in EVEN)

    def score(tree, live):
        assert not tree & live
        by_face = [projection_sizes(face, frozenset(edges & live)) for face, edges in faces.items()]
        sizes = tuple(prod(column) for column in zip(*by_face, strict=True))
        return max(sizes), sum(sizes)

    return score


def grouped_projection_keys(projections):
    groups = []
    for axes, keys in projections:
        indices = tuple(i for i, axis in enumerate(axes) if len(axis) == 2)
        by_probe = {}
        for key in sorted(keys):
            by_probe.setdefault(tuple(key[i] for i in indices), []).append(key)
        groups.append(by_probe.values())
    for group in product(*groups):
        for projected in product(*group):
            yield tuple(value for key in projected for value in key)


def center_factor(center, planes, slots, faces, removed=None):
    projections = [projected_keys(center, factor) for factor in faces]
    axes = tuple(axis for keys, _ in projections for axis in keys)
    rows = {}
    divisor = None
    @lru_cache(maxsize=1)
    def products(moments):
        return gamma_products(*(edge_table(degree, moment, i)
                                for i, (degree, moment) in enumerate(
                                    zip((2, 4, 2), moments, strict=True), 1)))

    for key in grouped_projection_keys(projections):
        components = {axis: value for axis, value in zip(axes, key, strict=True) if len(axis) == 3}
        probes = {axis: PROBE_PAIRS[value] for axis, value in zip(axes, key, strict=True)
                  if len(axis) == 2}
        directions, local, scale_factor = center_tensor(center, planes, slots, components, probes, removed, products)
        assert divisor is None or divisor == scale_factor
        divisor = scale_factor
        if local:
            assert all(mask & 255 == 255 and value.is_ground for mask, value in local.items())
            mapped = remap({mask >> 8: value for mask, value in local.items()},
                           tuple(center ^ (1 << i) for i in directions))
            rows[key] = {mask: (int(value.const().x), int(value.const().y))
                         for mask, value in mapped.items()}
    assert divisor is not None
    return (axes, rows), divisor


def close_factors(factors):
    while len(factors) > 1:
        def score(pair):
            a, b = (factors[i] for i in pair)
            return (not bool(set(a[0]) & set(b[0])),
                    sum(map(len, a[1].values())) * sum(map(len, b[1].values())))

        i, j = min(combinations(range(len(factors)), 2), key=score)
        merged = join_factors(factors[i], factors[j], match_labels=True)
        if not merged[1]:
            return 0
        factors.pop(j)
        factors[i] = merged
    axes, rows = factors[0]
    assert not axes
    mask = sum(255 << (8 * (x ^ 1)) for x in EVEN)
    assert rows.keys() == {()} and rows[()].keys() == {mask}
    real, imag = rows[()][mask]
    assert imag == 0
    return real


def contract_factors(pattern, slots, faces, tree, live, selection=None, retained=None,
                     replacement=None):
    assert retained is None or replacement is None
    curvature = face_factors(faces, tree, live, selection)
    factors = list(curvature)
    divisors = {}
    for center, planes in zip(EVEN, pattern, strict=True):
        removed = replacement[1] if replacement is not None and center == replacement[0] else None
        factor, denominator = center_factor(center, planes, slots[center], curvature, removed)
        factors.append(factor)
        divisors[center] = denominator
    occurrences = Counter(key for axes, _ in factors for key in axes)
    assert set(occurrences.values()) == {2}
    divisor = prod(divisors.values())
    normal = Fraction(close_factors(list(factors)), divisor * (6 if replacement is not None else 1))
    if retained is None:
        return normal

    source_total = 0
    for center, plane in retained:
        position = EVEN.index(center)
        factor, denominator = center_factor(center, pattern[position], slots[center], curvature, plane)
        assert denominator == divisors[center]
        changed = list(factors)
        index = len(curvature) + position
        assert changed[index][0] == factor[0]
        changed[index] = factor
        value = close_factors(changed)
        source_total += value
        print("retained source", center, plane, Fraction(value, 6 * divisor), flush=True)
    return normal, Fraction(source_total, 6 * divisor)


def retained_planes(pattern, faces, protected):
    check_removals(pattern)
    retained = []
    for center, planes in zip(EVEN, pattern, strict=True):
        for plane in sorted(set(planes)):
            omitted = (center, *(a for a in AXES if a not in plane))
            if omitted in faces:
                continue
            assert curvature_boundary(pattern, omitted=omitted) == (faces, protected)
            retained.append((center, plane))
    assert len(retained) == 11 - len(faces)
    return retained



def verify_source_tensors():
    from l1_extended_mixed_center_gamma import opposite_source
    from l1_extended_protected_center import summed_protected_source

    live = (1, 0)
    probes = {live: (0, 0)}
    pure_slots = {0: ((), live), 1: ((), None)}
    _, actual, _ = center_tensor(0, ((0, 1),) * 2, pure_slots, {}, probes, (0, 1))
    assert actual and actual == scale(summed_protected_source(((0, 0), None)), -24)
    mixed_slots = {0: ((), live), 1: ((), ()), 2: ((), None)}
    for plane, removed in (((0, 1), 1), ((1, 2), 3)):
        _, actual, _ = center_tensor(0, ((0, 1), (1, 2)), mixed_slots, {}, probes, plane)
        reference = opposite_source(removed, ((0, 0), None, None), fixed=(3,))
        assert actual and scale(actual, 4) == scale(reference, -192)
    print("pure and both mixed source replacements match established tensors", flush=True)


def verify_local_tensors():
    pure_slots = {0: ((), ()), 1: ((), ())}
    directions, tensor, divisor = center_tensor(0, ((0, 1), (0, 1)), pure_slots, {}, {})
    reference, _ = staged_center(summed_fourth(0), summed_fourth(1))
    assert directions == (0, 1) and tensor and scale(tensor, 16) == reference
    assert 16 * divisor == 48 * 96**4 * 8**8 * factorial(4)

    mixed_slots = {0: (None, ()), 1: ((), ()), 2: (None, ())}
    components = {(0, 2, 3): (0, 0), (0, 0, 3): (4, 4)}
    directions, tensor, divisor = center_tensor(0, ((0, 1), (1, 2)), mixed_slots, components, {})
    reference = gamma_block(None, None, summed_fourth(1))((0, 0), (4, 4))
    assert directions == (0, 1, 2) and tensor and scale(tensor, 4) == reference
    assert 4 * divisor == SCALE**4 * 4**4 * 96**2 * 8**4 * factorial(2)**2
    print("pure and mixed local tensors agree with the established replays", flush=True)


def replay_six_deletions(first_slice, deletion_index):
    total = Fraction()
    count = 0
    for pattern, multiplicity in orbits(words_with_mixed_count(3)):
        faces, protected = curvature_boundary(pattern)
        if len(faces) != 6:
            continue
        assert multiplicity == 192
        check_removals(pattern)
        for index, omitted in enumerate(faces):
            if deletion_index is not None and index != deletion_index:
                continue
            rest, protection = curvature_boundary(pattern, omitted=omitted)
            assert len(rest) == 4 and protection == protected
            assert omitted[0] not in {f[0] for f in rest}
            assert len(set.union(*rest.values()) - protection) == 2
            slots, tree, live = layout(pattern, rest, protection, minimize_keys=True)
            center, k, l = omitted
            plane = tuple(a for a in AXES if a not in (k, l))
            replacement = center, plane
            print("six-face deletion", index, omitted, "projected keys",
                  tree_key_cost(rest)(tree, live), flush=True)
            selection = None
            if first_slice:
                components, probes = probe_slice(rest, tree, live)
                selection = {face: (components[face], *(PAIR_INDEX[probes[e]] for e in sorted(edges & live)))
                             for face, edges in rest.items()}
            value = contract_factors(pattern, slots, rest, tree, live, selection, replacement=replacement)
            if first_slice:
                direct = contract_slice(pattern, slots, components, probes, replacement)
                assert value == direct
                print("fixed-probe six-face deletion control", value, flush=True)
            else:
                print("six-face deletion source", index, value, flush=True)
                total += 2 * multiplicity * value
            count += 1
    assert count == (6 if deletion_index is None else 1)
    if not first_slice:
        label = "six-face deletion subtotal" if deletion_index is None else "selected six-face deletion"
        print(label, "both checkerboards", total, flush=True)


def main(first_slice=False, full_orbit=None, tree_costs=False, source=False):
    counts = Counter()
    completed_full = False
    for pattern, multiplicity in orbits(words_with_mixed_count(3)):
        faces, protected = curvature_boundary(pattern)
        if len(faces) not in (4, 6):
            continue
        run_full = full_orbit == sum(counts.values())
        slots, tree, live = layout(pattern, faces, protected, minimize_keys=run_full or tree_costs)
        if tree_costs:
            score = tree_key_cost(faces)
            _, baseline_tree, baseline_live = larger_core_tree(faces, protected)
            baseline = score(baseline_tree, baseline_live)
            optimized = score(tree, live)
            assert optimized <= baseline
            if not counts:
                assert (baseline, optimized) == ((199584, 205189), (69696, 70213))
            print("projected keys", len(faces), baseline, optimized, flush=True)
        retained = retained_planes(pattern, faces, protected)
        components, probes = probe_slice(faces, tree, live)
        if first_slice and not counts:
            direct = contract_slice(pattern, slots, components, probes)
            print("first four-face probe slice", direct, flush=True)
            selected = {face: (components[face], *(PAIR_INDEX[probes[e]] for e in sorted(edges & live)))
                        for face, edges in faces.items()}
            assert contract_factors(pattern, slots, faces, tree, live, selected) == direct
            print("fixed-probe factor join agrees", flush=True)
        if run_full:
            score = tree_key_cost(faces)
            print("full orbit", full_orbit, "projected keys", score(tree, live), flush=True)
            result = contract_factors(pattern, slots, faces, tree, live,
                                      retained=retained if source else None)
            if source:
                result, numerator = result
                print("full orbit", full_orbit, "retained numerator", numerator, flush=True)
            print("full orbit", full_orbit, "normalization", result, flush=True)
            completed_full = True
        for center, planes in zip(EVEN, pattern, strict=True):
            if any(state != () for states in slots[center].values() for state in states):
                if planes[0] != planes[1]:
                    assert len(set(planes[0]) & set(planes[1])) == 1
                else:
                    assert not any(face[0] == center for face in faces)
        counts[len(faces)] += 1
        print("core", len(faces), "multiplicity", multiplicity,
              "fixed", len(tree), "live", len(live), flush=True)
    assert counts == {4: 10, 6: 1}
    assert full_orbit is None or completed_full


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--local-controls", action="store_true")
    parser.add_argument("--source-controls", action="store_true")
    parser.add_argument("--first-slice", action="store_true")
    full = parser.add_mutually_exclusive_group()
    full.add_argument("--full-first", dest="full_orbit", action="store_const", const=0)
    full.add_argument("--full-orbit", type=int, choices=range(11))
    parser.add_argument("--tree-costs", action="store_true")
    parser.add_argument("--retained-source", action="store_true")
    parser.add_argument("--six-deletions", action="store_true")
    parser.add_argument("--deletion-index", type=int, choices=range(6))
    args = parser.parse_args()
    if args.deletion_index is not None and not args.six_deletions:
        parser.error("--deletion-index requires --six-deletions")
    if args.six_deletions:
        if args.full_orbit is not None or args.retained_source or args.tree_costs or args.local_controls or args.source_controls:
            parser.error("--six-deletions is separate from original-core replays")
        replay_six_deletions(args.first_slice, args.deletion_index)
        raise SystemExit
    if args.retained_source and args.full_orbit is None:
        parser.error("--retained-source requires --full-orbit or --full-first")
    main(args.first_slice, args.full_orbit, args.tree_costs, args.retained_source)
    if args.local_controls:
        verify_local_tensors()
    if args.source_controls:
        verify_source_tensors()
