"""Structural support for transverse source pairs on the periodic 2^4 torus.

Count 30-action words with two copies of one center-plane label at
each of fifteen sites. Multiplicities in the census count label
multisets before choosing directed anchors or ordering action vertices.
"""

from collections import Counter
from functools import cache
from itertools import combinations, product

from l1_extended_anchor_census import anchor_multiplicity

AXES = (0, 1, 2, 3)
SITES = tuple(range(16))
FRAME_PAIRS = tuple(combinations(AXES, 2))


def source_endpoints(offset, first_axis, second_axis):
    return Counter((0, 1 << first_axis, offset, offset ^ (1 << second_axis)))


def count_side(senders, demand):
    """Count two distinct outgoing frame directions per sender."""
    choices = [
        tuple((site ^ (1 << a), site ^ (1 << b)) for a, b in FRAME_PAIRS)
        for site in senders
    ]

    @cache
    def search(index, remaining):
        if index == len(choices):
            return int(not any(remaining))
        count = 0
        for first, second in choices[index]:
            if remaining[first] and remaining[second]:
                updated = list(remaining)
                updated[first] -= 1
                updated[second] -= 1
                count += search(index + 1, tuple(updated))
        return count

    return search(0, demand)


def count_words(offset, first_axis, second_axis, omitted):
    endpoints = source_endpoints(offset, first_axis, second_axis)
    # Divide each site's Grassmann degree by two. A pair of action
    # vertices supplies two units at its center and one at each neighbor.
    targets = tuple(4 - endpoints[site] - 2 * (site != omitted) for site in SITES)
    count = 1
    for parity in (0, 1):
        senders = tuple(site for site in SITES
                        if site != omitted and site.bit_count() % 2 == parity)
        demand = tuple(need if site.bit_count() % 2 != parity else 0
                       for site, need in enumerate(targets))
        if min(demand) < 0 or sum(demand) != 2 * len(senders):
            return 0
        count *= count_side(senders, demand)
    return count


def verify_witness(frame_pairs, offset):
    word = []
    frame_edges = set()
    for site, frame in sorted(frame_pairs.items()):
        curvature = tuple(axis for axis in AXES if axis not in frame)
        word.extend([(site, *curvature)] * 2)
        for axis in frame:
            frame_edges.add((min(site, site ^ (1 << axis)), axis))
    degrees, anchors = anchor_multiplicity(word, 16, 4)
    endpoints = source_endpoints(offset, 2, 2)
    assert len(word) == 30
    assert all(degrees[site] + 2 * endpoints[site] == 8 for site in SITES)
    # Curvature link degrees are even. Each populated undirected frame
    # edge supplies one parity constraint on its directed anchor choices.
    assert anchors == 2 ** (60 - len(frame_edges))
    return anchors


def swap_site(site):
    return (site & 12) | ((site & 1) << 1) | ((site & 2) >> 1)


def main():
    witness = {site: (0, 1) for site in SITES if site}
    witness.update({6: (0, 2), 7: (0, 3), 8: (0, 3), 14: (1, 2)})
    swap_axis = (1, 0, 2, 3)
    rotated = {
        swap_site(site): tuple(sorted(swap_axis[a] for a in frame))
        for site, frame in witness.items()
    }
    anchors = verify_witness(witness, 1)
    assert verify_witness(rotated, 2) == anchors
    print("Verified witness and axis exchange. Parity-accepted anchor assignments:", anchors)

    for first_axis, second_axis in product((2, 3), repeat=2):
        counts = [count_words(1, first_axis, second_axis, site) for site in SITES]
        swapped = [count_words(2, first_axis, second_axis, swap_site(site))
                   for site in SITES]
        assert counts == swapped
        assert sum(counts) > 0
        print("Offsets 1 and 2, ordered source axes", (first_axis, second_axis),
              "word multisets per offset", sum(counts), "by omitted center", counts)
    print("Structural census only. Signed exterior and Haar contractions are separate.")


if __name__ == "__main__":
    main()
