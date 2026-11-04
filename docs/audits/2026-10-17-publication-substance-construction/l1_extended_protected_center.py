"""Gamma-summed local tensor for a pure center with two protected edges."""
from argparse import ArgumentParser
from collections import Counter
from functools import cache
from itertools import combinations_with_replacement, product

from l1_direct_b_haar import add, scale
from l1_extended_mixed_frame_moment import SCALE, frame_edge
from l1_extended_opposed import close_second_frame, stage_first_frame, staged_center
from l1_extended_opposed_source import summed_fourth
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
    parser.add_argument("--all-probes", action="store_true")
    main(parser.parse_args().all_probes)
