"""Exact protected-square local factors for the paired k=3 offset stratum."""

from functools import cache
from itertools import combinations, product
from math import prod

from l1_direct_b_haar import R, add, scale, wedge
from l1_extended_mixed_center_gamma import COMPONENTS
from l1_extended_mixed_curvature_core import PAIRS, face_tensor, face_vector
from l1_extended_mixed_frame_moment import SCALE, frame_edge_moments
from l1_extended_offset_witness import coframe, local_edge
from l1_extended_opposed_source import action_frame
from l1_extended_two_mixed_centers import remap
from l1_normalization_opposed_fourth import nodes
from l1_normalization_uniform_mixed_edge import unit


def square_factor(face, live, fixed):
    """Integer scalar rows indexed by face component pair and live probe."""
    return {
        (labels, PAIRS[i]): weight
        for labels in COMPONENTS
        for (i,), weight in face_tensor(face, (live,), fixed, labels).items()
    }


@cache
def identity_moment(anchor, labels):
    result = {0: R.one}
    for center, gamma in labels:
        factor = add(
            *(coframe(center, anchor, coordinate, gamma) for coordinate in (0, 4))
        )
        result = wedge(result, factor)
    return scale(result, SCALE)


@cache
def fixed_action_edge(labels, centers, fixed_anchor):
    """One fixed directed anchor, opposite directed anchor integrated."""
    from l1_extended_offset_witness import directed_moment

    if len(labels) == 1:
        center = centers[0]
        moments = tuple(
            None if (anchor ^ center) == fixed_anchor else () for anchor in (0, 1)
        )
        row = frame_edge_moments(labels[0], moments)
        return remap(row, (1, 0)) if center else row
    slots = tuple(
        (center, gamma)
        for center, pair in zip(centers, labels, strict=True)
        for gamma in pair
    )
    factors = []
    for n in range(0, len(slots) + 1, 2):
        for selected in combinations(range(len(slots)), n):
            chunks = (
                tuple(slots[i] for i in selected),
                tuple(slots[i] for i in range(len(slots)) if i not in selected),
            )
            factors.append(
                wedge(
                    *(
                        (
                            identity_moment
                            if anchor == fixed_anchor
                            else directed_moment
                        )(anchor, chunk)
                        for anchor, chunk in enumerate(chunks)
                    )
                )
            )
    return add(*factors)


@cache
def probed_action_edge(labels, center, physical_anchor, probe):
    moments = tuple(
        probe if (anchor ^ center) == physical_anchor else () for anchor in (0, 1)
    )
    row = frame_edge_moments(labels, moments)
    return remap(row, (1, 0)) if center else row


def square_control(face, live, fixed):
    rows = square_factor(face, live, fixed)
    assert len(rows) == 21
    assert {p for _, p in rows} == {
        (a, b) for a in (1, 2, 3, 5, 6, 7) for b in (1, 2, 3, 5, 6, 7) if a <= b
    }
    for left, right in product(range(4), repeat=2):
        coordinates = {**fixed, live: (unit(left), unit(right))}
        q = unit(left) + unit(right)
        for labels in COMPONENTS:
            expected = prod(
                face_vector(face, coordinates, *divmod(label, 3)) for label in labels
            )
            actual = sum(
                w * q[a] * q[b] for (c, (a, b)), w in rows.items() if c == labels
            )
            assert actual == expected


def cubature(anchor, labels, fixed):
    result = []
    rule = [((2, 0, 0, 0), (2, 0, 0, 0), 96)] if fixed else nodes()
    for left, right, weight in rule:
        row = {0: R.one}
        for center, gamma in labels:
            value = action_frame(0, anchor ^ center, left, right)[gamma]
            if center:
                value = scale(remap(value, (1, 0)), -1)
            row = wedge(row, value)
        result.append(scale(row, weight))
    return add(*result)


def cubature_edge(labels, centers, fixed_anchor):
    slots = tuple(
        (center, gamma)
        for center, pair in zip(centers, labels, strict=True)
        for gamma in pair
    )
    rows = []
    for n in range(0, len(slots) + 1, 2):
        for selected in combinations(range(len(slots)), n):
            chunks = (
                tuple(slots[i] for i in selected),
                tuple(slots[i] for i in range(len(slots)) if i not in selected),
            )
            rows.append(
                wedge(
                    *(cubature(a, c, a == fixed_anchor) for a, c in enumerate(chunks))
                )
            )
    return add(*rows)


def check_local_moments():
    for labels, centers in [
        (((0, 0),), (0,)),
        (((0, 0),), (1,)),
        (((0, 0), (0, 0)), (0, 1)),
        (((0, 1), (0, 1)), (0, 1)),
    ]:
        d = 2 * len(labels)
        ratio, rem = divmod(96**2 * 8**d, SCALE**2 * 4**d)
        assert not rem
        for fixed_anchor in (0, 1):
            exact = fixed_action_edge(labels, centers, fixed_anchor)
            assert scale(exact, ratio) == cubature_edge(labels, centers, fixed_anchor)
    for center, physical_anchor in product((0, 1), repeat=2):
        baseline = local_edge(((0, 0),), (center,))
        for start in (0, 4):
            assert (
                add(
                    *(
                        probed_action_edge((0, 0), center, physical_anchor, (i, i))
                        for i in range(start, start + 4)
                    )
                )
                == baseline
            )
    print(
        "oriented fixed-edge cubature and live-probe trace controls passed", flush=True
    )
