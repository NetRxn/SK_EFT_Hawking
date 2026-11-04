"""Directed frame routing and local tensors for the larger three-mixed cores."""
from argparse import ArgumentParser
from collections import Counter
from fractions import Fraction
from functools import cache
from math import factorial

from l1_direct_b_haar import scale
from l1_extended_four_face_gauge_join import IDENTITY, larger_core_tree
from l1_extended_mixed_center_census import AXES, EVEN, curvature_boundary, orbits, words_with_mixed_count
from l1_extended_mixed_center_gamma import COMPONENTS, contract_gamma, face_channels, gamma_block, peeled_channels
from l1_extended_mixed_curvature_core import PAIR_INDEX, face_tensor
from l1_extended_mixed_frame_moment import SCALE, frame_edge_moments
from l1_extended_opposed import staged_center
from l1_extended_opposed_source import PAIRS, summed_fourth
from l1_extended_two_mixed_centers import contract, remap
from l1_normalization_opposed_fourth import tuples


def layout(pattern, faces, protected):
    _, tree, live = larger_core_tree(faces, protected)
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


def center_tensor(center, planes, slots, components, probes):
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
    tensors = [edge_table(d, m, i) for i, (d, m) in enumerate(zip(degrees, moments, strict=True), 1)]
    divisor = SCALE**(2 * len(directions)) * 4**sum(degrees)
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
    return directions, contract_gamma(*tensors, *weights), divisor * factorial(2)**2


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


def contract_slice(pattern, slots, components, probes):
    divisor = 1
    terms = {}
    for center, planes in zip(EVEN, pattern, strict=True):
        directions, local, denominator = center_tensor(center, planes, slots[center], components, probes)
        terms[center] = remap(local, (center, *(center ^ (1 << axis) for axis in directions)))
        divisor *= denominator
    result = contract(terms)
    assert result.is_ground and not result.const().y
    return Fraction(int(result.const().x), divisor)


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


def main(first_slice=False):
    counts = Counter()
    for pattern, multiplicity in orbits(words_with_mixed_count(3)):
        faces, protected = curvature_boundary(pattern)
        if len(faces) not in (4, 6):
            continue
        slots, tree, live = layout(pattern, faces, protected)
        components, probes = probe_slice(faces, tree, live)
        if first_slice and not counts:
            print("first four-face probe slice", contract_slice(pattern, slots, components, probes), flush=True)
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


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--local-controls", action="store_true")
    parser.add_argument("--first-slice", action="store_true")
    args = parser.parse_args()
    main(args.first_slice)
    if args.local_controls:
        verify_local_tensors()
