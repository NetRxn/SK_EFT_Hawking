"""Frame-edge tensors with a retained curvature coordinate pair."""
from collections import Counter
from functools import cache
from itertools import combinations, combinations_with_replacement, product

from l1_direct_b_haar import R, add, haar_moment, scale, wedge
from l1_extended_opposed_source import action_frame, summed_fourth
from l1_extended_two_mixed_centers import second_sum
from l1_normalization_uniform_mixed_edge import unit

SCALE = 192
ZERO = (0,) * 4


@cache
def basis(anchor, coordinate):
    q = unit(coordinate % 4)
    return action_frame(0, anchor, *((q, ZERO) if coordinate < 4 else (ZERO, q)))


@cache
def moment(indices):
    counts = Counter(indices)
    value = SCALE
    for start in (0, 4):
        value *= haar_moment(tuple(counts[i] for i in range(start, start + 4)))
    assert value.denominator == 1
    return int(value)


@cache
def anchor_terms(anchor, labels):
    """Raw exterior polynomials grouped by quaternion monomial."""
    out = {}
    for coordinates in product(range(8), repeat=len(labels)):
        counts = Counter(coordinates)
        if sum(n % 2 for n in counts.values()) > 2:
            continue
        poly = {0: R.one}
        for label, coordinate in zip(labels, coordinates, strict=True):
            poly = wedge(poly, basis(anchor, coordinate)[label])
            if not poly:
                break
        if poly:
            key = tuple(sorted(coordinates))
            out[key] = add(out.get(key, {}), poly)
    return {key: poly for key, poly in out.items() if poly}


@cache
def anchored(anchor, labels, probe):
    """One directed link, with the probe retained in its moment weight."""
    return add(*(scale(poly, weight) for key, poly in anchor_terms(anchor, labels).items()
                 if (weight := moment(tuple(sorted((*key, *probe)))))))


def frame_edge(labels, protected_anchor, probe):
    """Return the joint tensor at scale 192² times the raw frame convention."""
    terms = []
    # A quadratic probe leaves even frame count on each directed link.
    for n in range(0, len(labels) + 1, 2):
        for left in combinations(range(len(labels)), n):
            a = tuple(labels[i] for i in left)
            b = tuple(labels[i] for i in range(len(labels)) if i not in left)
            terms.append(wedge(anchored(0, a, probe if protected_anchor == 0 else ()),
                               anchored(1, b, probe if protected_anchor == 1 else ())))
    return add(*terms)


def check_core_degrees():
    from l1_extended_mixed_center_census import EVEN, curvature_boundary, orbits, swap_patterns

    for pattern, _ in orbits(swap_patterns()):
        faces, protected = curvature_boundary(pattern)
        if not faces:
            continue
        degree = Counter(link for edges in faces.values() for link in edges if link in protected)
        assert set(degree.values()) == {1}
        assert all((x ^ (1 << axis), axis) not in degree for x, axis in degree)
        frame_degrees = Counter()
        for x, axis in degree:
            center = x if x in EVEN else x ^ (1 << axis)
            frame_degrees[2 * sum(axis in pair for pair in pattern[EVEN.index(center)])] += 1
        assert frame_degrees == ({2: 2, 4: 4} if len(faces) == 2 else {2: 4, 4: 4})


def main():
    check_core_degrees()
    assert moment((0,) * 6) == 15 and moment((0, 0, 1, 1, 2, 2)) == 1
    assert moment((0, 0, 0, 0, 4, 4)) == 6
    fourth = summed_fourth(0)
    second = second_sum(0)
    for degree, reference in ((2, second), (4, fourth)):
        nonzero = Counter()
        for labels, unprobed in reference.items():
            reference_scale = 96**(degree // 2) * 2**degree
            for anchor in (0, 1):
                table = {probe: frame_edge(labels, anchor, probe)
                         for probe in combinations_with_replacement(range(8), 2)}
                for probe, poly in table.items():
                    nonzero[anchor, "mixed" if probe[0] // 4 != probe[1] // 4 else "same"] += len(poly)
                # Summing q_i² in either chirality inserts one.
                for chirality in (0, 1):
                    result = add(*(table[i, i] for i in range(4*chirality, 4*chirality + 4)))
                    assert scale(result, reference_scale) == scale(unprobed, SCALE**2)
        print("frame degree", degree, "nonzero boundary entries", dict(sorted(nonzero.items())),
              flush=True)



if __name__ == "__main__":
    main()
