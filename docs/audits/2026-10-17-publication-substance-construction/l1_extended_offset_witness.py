"""Exact selected 30-action coefficient at offset 1 on the periodic 2^4 torus.

The two source insertions are directed axis-2 terms based at 0 and 1.
The output sums frame anchors, gamma labels and curvature channels for
one paired action word. The full offset ensemble requires other words.
"""

from argparse import ArgumentParser
from collections import Counter, defaultdict
from fractions import Fraction
from functools import cache
from itertools import combinations, combinations_with_replacement, product
from math import comb, prod
from time import perf_counter

from l1_direct_b_haar import R, add, scale, wedge
from l1_extended_four_face_gauge_join import IDENTITY
from l1_extended_mixed_center_gamma import face_channels, peeled_channels
from l1_extended_mixed_curvature_core import conditional
from l1_extended_mixed_frame_join import join_factors
from l1_extended_mixed_frame_moment import SCALE, anchored, basis, frame_edge_moments, moment
from l1_extended_offset_pair_census import AXES, SITES, verify_witness
from l1_extended_two_mixed_centers import remap

FRAME_PLANES = {site: (0, 1) for site in SITES if site}
FRAME_PLANES.update({6: (0, 2), 7: (0, 3), 8: (0, 3), 14: (1, 2)})
SOURCE_LINKS = ((0, 2), (1, 2))
FIXED_SOURCE = SOURCE_LINKS[1]
FIXED_GAMMAS = ((0, 0), (1, 1))
DIAGONAL = tuple((i, i) for i in range(6))
EDGE_LABELS = defaultdict(list)
for center, axes in FRAME_PLANES.items():
    for axis in axes:
        end = center ^ (1 << axis)
        EDGE_LABELS[min(center, end), max(center, end), axis].append((center, axis))
EXCLUSIVE = {label for labels in EDGE_LABELS.values() if len(labels) == 1 for label in labels}


def residual_core():
    assert verify_witness(FRAME_PLANES, 1) == 2**40
    assert len(EDGE_LABELS) == 20
    assert all((min(x, x ^ (1 << a)), max(x, x ^ (1 << a)), a) not in EDGE_LABELS
               for x, a in SOURCE_LINKS)
    protected = {(y, a) for x, end, a in EDGE_LABELS for y in (x, end)} | set(SOURCE_LINKS)
    faces = {}
    for center, axes in FRAME_PLANES.items():
        k, l = (axis for axis in AXES if axis not in axes)
        faces[center, k, l] = {(center, k), (center ^ (1 << k), l),
                               (center ^ (1 << l), k), (center, l)}
    while True:
        counts = Counter(edge for edges in faces.values() for edge in edges)
        private = next((face for face, edges in faces.items()
                        if any(counts[e] == 1 and e not in protected for e in edges)), None)
        if private is None:
            break
        del faces[private]
    assert tuple(faces) == tuple((center, 2, 3) for center in (1, 5, 9, 13))
    assert set.union(*faces.values()) & protected == {FIXED_SOURCE}
    return faces


CORE = residual_core()
BASES = tuple(face[0] for face in CORE)
DIVISOR = (SCALE**2)**len(EDGE_LABELS) * 4**60 * (SCALE * 4**2)**2
DIVISOR *= 48**(len(FRAME_PLANES) - len(CORE)) * 2**len(FRAME_PLANES)


def direct_core(labels):
    return conditional(CORE, {FIXED_SOURCE}, {FIXED_SOURCE: IDENTITY},
                       dict(zip(CORE, labels, strict=True)))


def core_branches():
    # After the protected source link is gauge-fixed, the core has an
    # independent scalar term plus the same-chirality matching correction.
    yield Fraction(1, 256), dict.fromkeys(BASES, DIAGONAL)
    for chirality in range(2):
        indices = range(3 * chirality, 3 * chirality + 3)
        diagonal = tuple((i, i) for i in indices)
        yield Fraction(-1, 559872), dict.fromkeys(BASES, diagonal)
        for pair in combinations_with_replacement(indices, 2):
            weight = Fraction(2 if pair[0] == pair[1] else 1, 279936)
            yield weight, {1: (pair,), 5: (pair,), 9: diagonal, 13: diagonal}


@cache
def coframe(center, anchor, coordinate, gamma):
    row = basis(anchor ^ center, coordinate)[gamma]
    # Exchanging endpoint slots of one coframe crosses two odd generators.
    return scale(remap(row, (1, 0)), -1) if center else row


@cache
def directed_moment(anchor, labels):
    terms = []
    for coordinates in product(range(8), repeat=len(labels)):
        weight = moment(tuple(sorted(coordinates)))
        if not weight:
            continue
        row = {0: R.one}
        for (center, gamma), coordinate in zip(labels, coordinates, strict=True):
            row = wedge(row, coframe(center, anchor, coordinate, gamma))
        if row:
            terms.append(scale(row, weight))
    return add(*terms)


@cache
def local_edge(labels, centers):
    if len(labels) == 1:
        row = frame_edge_moments(labels[0], ((), ()))
        return remap(row, (1, 0)) if centers[0] else row
    slots = tuple((center, gamma) for center, pair in zip(centers, labels, strict=True)
                  for gamma in pair)
    terms = []
    # Haar requires even total degree on each directed anchor. An anchor
    # may take one coframe from each endpoint center.
    for count in (0, 2, 4):
        for indices in combinations(range(4), count):
            left = tuple(slots[i] for i in indices)
            right = tuple(slots[i] for i in range(4) if i not in indices)
            terms.append(wedge(directed_moment(0, left), directed_moment(1, right)))
    return add(*terms)


def gaussian(poly):
    assert all(v.is_ground for v in poly.values())
    return {mask: (int(value.const().x), int(value.const().y)) for mask, value in poly.items()}


def center_weights(labels):
    if labels is None:
        return peeled_channels()
    weights = Counter()
    for label in labels:
        weights.update(face_channels(label))
    return {key: value for key, value in weights.items() if value}


def prepare(core_labels, restrictions):
    choices, factors = {}, []
    for center, axes in FRAME_PLANES.items():
        keys = tuple((center, axis) for axis in axes)
        weights = center_weights(core_labels[center] if center in BASES else None)
        rows = {labels: {0: (weight, 0)} for labels, weight in weights.items()
                if (center not in restrictions or restrictions[center] == labels)
                and all(labels[i][0] == labels[i][1]
                        for i, key in enumerate(keys) if key in EXCLUSIVE)}
        if not rows:
            return None
        choices[center] = rows
        factors.append((keys, rows, {}))
    for (low, high, _), keys in sorted(EDGE_LABELS.items()):
        domains = []
        for center, axis in keys:
            index = FRAME_PLANES[center].index(axis)
            domains.append(sorted({labels[index] for labels in choices[center]}))
        rows = {}
        for labels in product(*domains):
            row = local_edge(labels, tuple(int(center == high) for center, _ in keys))
            if row:
                rows[labels] = gaussian(remap(row, (low, high)))
        if not rows:
            return None
        degree = 2 * len(keys)
        factors.append((tuple(keys), rows, {low: degree, high: degree}))
    # U(1,2)=I is a one-link tree gauge, with no additional Haar volume.
    # The fixed and integrated directed source rows use the same raw scale.
    for link in SOURCE_LINKS:
        site, axis = link
        end = site ^ (1 << axis)
        probe = None if link == FIXED_SOURCE else ()
        row = add(*(anchored(0, (), probe, gamma) for gamma in range(4)))
        factors.append(((), {(): gaussian(remap(row, (site, end)))}, {site: 2, end: 2}))
    assert len(factors) == 37
    return factors


def compatible_pairs(left, right):
    axes, left_rows, _ = left
    other, right_rows, _ = right
    shared = tuple(label for label in axes if label in other)
    a = tuple(axes.index(label) for label in shared)
    b = tuple(other.index(label) for label in shared)
    counts = Counter()
    for key, row in right_rows.items():
        counts[tuple(key[i] for i in b)] += len(row)
    return sum(len(row) * counts[tuple(key[i] for i in a)] for key, row in left_rows.items())


def eliminate(factors, row_cap=120_000, pair_cap=3_000_000):
    if factors is None:
        return 0, 0, 0
    peak = steps = 0
    while len(factors) > 1:
        candidates = []
        for i, j in combinations(range(len(factors)), 2):
            left, right = factors[i], factors[j]
            labels, other = set(left[0]), set(right[0])
            if not labels & other and not left[2].keys() & right[2].keys():
                continue
            degrees = Counter(left[2])
            degrees.update(right[2])
            assert all(degree <= 8 for degree in degrees.values())
            open_degrees = {site: degree for site, degree in degrees.items() if degree < 8}
            bound = prod(4 if label in EXCLUSIVE else 10 for label in labels ^ other)
            bound *= prod(comb(8, degree) for degree in open_degrees.values())
            candidates.append((bound, i, j, degrees, open_degrees))
        _, i, j, degrees, open_degrees = min(candidates)
        left, right = factors[i], factors[j]
        pairs = compatible_pairs(left, right)
        if pairs > pair_cap:
            raise RuntimeError(f"join {steps}: {pairs} compatible pairs exceed cap {pair_cap}")
        keys, rows = join_factors(left[:2], right[:2], match_labels=True)
        if not rows:
            return 0, peak, steps
        closed = sum(255 << (8 * site) for site, degree in degrees.items() if degree == 8)
        if closed:
            assert all(mask & closed == closed for row in rows.values() for mask in row)
            rows = {key: {mask ^ closed: value for mask, value in row.items()}
                    for key, row in rows.items()}
        size = sum(map(len, rows.values()))
        if size > row_cap:
            raise RuntimeError(f"join {steps}: {size} rows exceed cap {row_cap}")
        peak = max(peak, size)
        steps += 1
        factors[i] = keys, rows, open_degrees
        factors.pop(j)
    keys, rows, degrees = factors[0]
    assert not keys and not degrees and set(rows) == {()} and set(rows[()]) == {0}
    real, imag = rows[()][0]
    assert not imag
    return real, peak, steps


def value(core_labels, restrictions):
    raw, peak, steps = eliminate(prepare(core_labels, restrictions))
    return Fraction(raw, DIVISOR), peak, steps


def controls():
    fixed = dict.fromkeys(FRAME_PLANES, FIXED_GAMMAS)
    exact_core = dict.fromkeys(BASES, ((2, 2),))
    weight = direct_core(((2, 2),) * 4)
    assert weight == Fraction(365, 93312)
    result, peak, steps = value(exact_core, fixed)
    assert result * weight == Fraction(79646312375, 10625324586456701730816)
    print("fixed-label control", result * weight, "peak", peak, "joins", steps, flush=True)

    free = 2
    restricted = {x: labels for x, labels in fixed.items() if x != free}
    subtotal, peak, steps = value(exact_core, restricted)
    explicit = sum(value(exact_core, restricted | {free: labels})[0]
                   for labels in peeled_channels())
    assert subtotal == explicit == Fraction(53024805225, 2305843009213693952)
    print("one-center explicit-sum control", subtotal, "peak", peak, "joins", steps, flush=True)

    restricted = {x: labels for x, labels in fixed.items() if x not in (1, 5)}
    domain = ((2, 2), (0, 1), (5, 5))
    allowed = {1: domain, 5: domain, 9: ((2, 2),), 13: ((2, 2),)}
    explicit = Fraction()
    for a, b in product(domain, repeat=2):
        weight = direct_core((a, b, (2, 2), (2, 2)))
        if weight:
            explicit += weight * value(allowed | {1: (a,), 5: (b,)}, restricted)[0]
    subtotal = Fraction()
    for weight, branch in core_branches():
        selected = {x: tuple(label for label in branch[x] if label in allowed[x]) for x in BASES}
        if all(selected.values()):
            subtotal += weight * value(selected, restricted)[0]
    assert subtotal == explicit == Fraction(636515871775, 1328165573307087716352)
    print("linked-center direct-core control", subtotal, flush=True)


def main(controls_only):
    controls()
    if controls_only:
        return
    total = Fraction()
    branches = list(core_branches())
    assert len(branches) == 15
    for index, (weight, core_labels) in enumerate(branches):
        start = perf_counter()
        coefficient, peak, steps = value(core_labels, {})
        contribution = weight * coefficient
        total += contribution
        print("branch", index, "weight", weight, "coefficient", contribution,
              "peak rows", peak, "joins", steps, "seconds", round(perf_counter() - start, 3), flush=True)
    assert total == Fraction(2028966652060713225, 1099511627776)
    print("selected offset-1 word coefficient before g2^30", total, flush=True)


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--controls-only", action="store_true")
    main(parser.parse_args().controls_only)
