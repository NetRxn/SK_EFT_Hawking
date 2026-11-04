"""Gamma-summed local tensor for a pure center with two protected edges."""
from argparse import ArgumentParser
from collections import Counter
from functools import cache
from itertools import combinations_with_replacement, product

from l1_direct_b_haar import add, scale
from l1_extended_mixed_frame_moment import SCALE, frame_edge, source_edge
from l1_extended_opposed import close_second_frame, stage_first_frame, staged_center
from l1_extended_opposed_source import PAIRS as GAMMA_PAIRS, modified_center, source_frames, summed_fourth
from l1_extended_two_mixed_centers import remap
from l1_normalization_opposed_fourth import tuples


@cache
def edge_table(anchor, probe):
    return {labels: frame_edge(labels, anchor, probe) for labels in tuples}


@cache
def first_boundary(anchor, probe):
    return stage_first_frame(edge_table(anchor, probe))


@cache
def second_frame(anchor, probe):
    return {labels: remap(poly, (0, 2))
            for labels, poly in edge_table(anchor, probe).items()}


def protected_center(probes, anchors=(1, 1)):
    """Retain one coordinate-pair probe on each frame edge."""
    boundary = first_boundary(anchors[0], probes[0])
    second = second_frame(anchors[1], probes[1])
    return close_second_frame(boundary, second)


@cache
def source_table(probe, endpoint):
    return {labels: source_edge(labels, 1, probe, endpoint) for labels in GAMMA_PAIRS}


def protected_source_center(probes, endpoints):
    """One unsigned quadratic source per axis, with both probes open."""
    first, second = (source_table(probe, endpoint)
                     for probe, endpoint in zip(probes, endpoints, strict=True))
    return modified_center(first, {labels: remap(poly, (0, 2))
                                   for labels, poly in second.items()})


def check_source_center():
    reference = [[source_frames(direction, anchor) for anchor in (0, 1)]
                 for direction in (0, 1)]
    for endpoints in ((0, 0), (0, 1), (1, 1)):
        expected = modified_center(*({labels: add(*(maps[endpoint][labels] for maps in edge))
                                     for labels in GAMMA_PAIRS}
                                    for edge, endpoint in zip(reference, endpoints, strict=True)))
        diagonal = tuple((i, i) for i in range(4))
        actual = add(*(protected_source_center(probes, endpoints)
                       for probes in product(diagonal, repeat=2)))
        assert actual
        assert all(tuple(((mask >> shift) & 255).bit_count() for shift in (0, 8, 16))
                   == (8, 4, 4) for mask in actual)
        assert scale(actual, (96**2 * 2**4)**2) == scale(expected, SCALE**4)
        print("source endpoints", endpoints, "norm-control entries", len(actual), flush=True)


def main(all_probes):
    baseline, _ = staged_center(summed_fourth(0), summed_fourth(1))
    # Each probe's chiral unit-norm sum independently recovers the
    # unprobed tensor, after translating the unit-coordinate scale.
    for chiralities in ((0, 0), (0, 1), (1, 1)):
        diagonal = [tuple((i, i) for i in range(4*c, 4*c+4)) for c in chiralities]
        total = add(*(protected_center(probes) for probes in product(*diagonal)))
        assert scale(total, 96**4 * 2**8) == scale(baseline, SCALE**4)
        print("chiralities", chiralities, "norm contraction entries", len(total), flush=True)
    for probes in (((0, 4), (0, 4)), ((0, 1), (0, 1)), ((1, 1), (2, 2))):
        result = protected_center(probes)
        print("probes", probes, "entries", len(result), flush=True)

    if all_probes:
        pairs = tuple(combinations_with_replacement(range(8), 2))
        counts = Counter()
        for probes in product(pairs, repeat=2):
            poly = protected_center(probes)
            if poly:
                counts["live rows"] += 1
                counts["exterior entries"] += len(poly)
        print("complete probe table", dict(counts), flush=True)


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--all-probes", action="store_true")
    modes.add_argument("--source-controls", action="store_true")
    args = parser.parse_args()
    if args.source_controls:
        check_source_center()
    else:
        main(args.all_probes)
