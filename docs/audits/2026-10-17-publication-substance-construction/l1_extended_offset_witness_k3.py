"""Exact paired words with three frame-plane changes at offset 1.

This replay sums all twelve words in the declared paired subfamily.
Other action words remain outside the result.
"""

from argparse import ArgumentParser
from collections import Counter, defaultdict, namedtuple
from fractions import Fraction
from itertools import combinations, product
from time import perf_counter

import l1_extended_offset_witness as witness
from l1_direct_b_haar import add
from l1_extended_anchor_census import anchor_multiplicity
from l1_extended_four_face_gauge_join import IDENTITY
from l1_extended_offset_pair_census import AXES, FRAME_PAIRS, SITES, source_endpoints
from l1_extended_offset_square import (
    check_local_moments,
    fixed_action_edge,
    probed_action_edge,
    square_control,
    square_factor,
)
from l1_extended_offset_witness_k2 import (
    eliminate_components,
    free_branches,
    joint_source,
    protected_branches,
)
from l1_extended_two_mixed_centers import remap

SQUARE = ("square", "component")
PROBE = ("square", "probe")
BASE = (0, 1)
ALTERNATIVES = tuple(pair for pair in FRAME_PAIRS if pair != BASE)
Geometry = namedtuple(
    "Geometry",
    "frame edges sources fixed_source square live fixed_square fixed_edges "
    "joined_source linked other free_tori divisor",
)
WORD_TYPES = {
    (2, 2, (4, 4)): 4,
    (2, 2, (1, 4)): 4,
    (2, 3, (1, 4)): 2,
    (2, 3, (1, 4, 4)): 2,
}


def census(first_axis, second_axis):
    sources = ((0, first_axis), (1, second_axis))
    ends = source_endpoints(1, first_axis, second_axis)
    for omitted in SITES:
        senders = tuple(x for x in SITES if x != omitted)
        demand = Counter({x: 4 - ends[x] - 2 * (x != omitted) for x in SITES})
        for chosen in combinations(senders, 3):
            incoming = Counter(
                x ^ (1 << axis) for x in senders if x not in chosen for axis in BASE
            )
            if any(incoming[x] > demand[x] for x in SITES):
                continue
            for planes in product(ALTERNATIVES, repeat=3):
                changes = tuple(zip(chosen, planes, strict=True))
                added = Counter(x ^ (1 << axis) for x, pair in changes for axis in pair)
                if incoming + added == demand:
                    yield (
                        omitted,
                        changes,
                        dict.fromkeys(senders, BASE) | dict(changes),
                        sources,
                    )


def geometry(frame, sources):
    edges = defaultdict(list)
    faces = {}
    for x, axes in sorted(frame.items()):
        for a in axes:
            y = x ^ (1 << a)
            edges[min(x, y), max(x, y), a].append((x, a))
        k, l = (a for a in AXES if a not in axes)
        faces[x, k, l] = {(x, k), (x ^ (1 << k), l), (x ^ (1 << l), k), (x, l)}
    word = [f for f in faces for _ in range(2)]
    degree, anchors = anchor_multiplicity(word, 16, 4)
    ends = source_endpoints(1, *(a for _, a in sources))
    assert len(word) == 30 and anchors == 2 ** (60 - len(edges))
    assert all(degree[x] + 2 * ends[x] == 8 for x in SITES)
    protected = {(site, a) for x, y, a in edges for site in (x, y)} | set(sources)
    while True:
        counts = Counter(e for row in faces.values() for e in row)
        private = next(
            (
                f
                for f, row in faces.items()
                if any(counts[e] == 1 and e not in protected for e in row)
            ),
            None,
        )
        if private is None:
            break
        del faces[private]
    (linked_source,) = set(sources) & set.union(*faces.values())
    square = next((f for f, row in faces.items() if row <= protected), None)
    live = None
    fixed_square = {}
    if square is not None:
        x, k, l = square
        live = x, k
        lo, hi = sorted((x, x ^ (1 << k)))
        assert len(edges[lo, hi, k]) == 1
        fixed_square = dict.fromkeys(faces[square] - {live}, IDENTITY)
    torus_faces = {f: row for f, row in faces.items() if f != square}
    tori = [
        {f: row for f, row in torus_faces.items() if f[0] & 3 == column}
        for column in sorted({f[0] & 3 for f in torus_faces})
    ]
    assert all(len(t) == 4 and all(f[1:] == (2, 3) for f in t) for t in tori)
    (protected_torus,) = [
        t for t in tori if any(linked_source in row for row in t.values())
    ]
    free_tori = [t for t in tori if t is not protected_torus]
    assert len(free_tori) <= 1
    a, d = linked_source
    linked = (a, a ^ (1 << d))
    other = tuple(f[0] for f in protected_torus if f[0] not in linked)
    assert len(other) == 2
    assert set.union(*(row for t in tori for row in t.values())) & protected == {
        linked_source
    }
    # Identity gauge for these directed links is allowed on a forest.
    parent = {}

    def root(x):
        while x in parent:
            x = parent[x]
        return x

    for x, a in set(fixed_square) | {linked_source}:
        left, right = root(x), root(x ^ (1 << a))
        assert left != right
        parent[left] = right
    fixed_edges = {}
    for x, a in fixed_square:
        y = x ^ (1 << a)
        fixed_edges[min(x, y), max(x, y), a] = int(x > y)
    joined_source = {}
    for source in sources:
        x, a = source
        y = x ^ (1 << a)
        key = min(x, y), max(x, y), a
        if key in edges:
            assert (
                source != linked_source
                and len(edges[key]) == 1
                and key not in fixed_edges
            )
            joined_source[key] = int(x != edges[key][0][0])
    assert len(joined_source) <= 1
    divisor = (
        (witness.SCALE**2) ** len(edges)
        * 4**64
        * witness.SCALE ** (2 - len(joined_source))
    )
    divisor *= 48 ** (15 - len(faces)) * 2**15
    return Geometry(
        frame,
        edges,
        sources,
        linked_source,
        square,
        live,
        fixed_square,
        fixed_edges,
        joined_source,
        linked,
        other,
        free_tori,
        divisor,
    )


def prepare(geom, core, restrict=None):
    (
        frame,
        edges,
        sources,
        fixed_source,
        square,
        live,
        fixed_square,
        fixed_edges,
        joined_source,
        _,
        _,
        _,
        divisor,
    ) = geom
    restrict = {} if restrict is None else restrict
    if square is None:
        square_rows = {}
        live_edge = None
    else:
        square_rows = square_factor(square, live, fixed_square)
        x, a = live
        y = x ^ (1 << a)
        live_edge = min(x, y), max(x, y), a
    changed = set(fixed_edges) | set(joined_source)
    if live_edge is not None:
        changed.add(live_edge)
    exclusive = {
        label
        for edge, labels in edges.items()
        if len(labels) == 1 and edge not in changed
        for label in labels
    }
    factors = []
    choices = {}
    for x, axes in sorted(frame.items()):
        keys = tuple((x, a) for a in axes)
        at_square = square is not None and x == square[0]
        domains = sorted({label for label, _ in square_rows}) if at_square else (None,)
        rows = {}
        for comp in domains:
            weights = witness.center_weights((comp,) if at_square else core.get(x))
            for gamma, weight in weights.items():
                if x in restrict and gamma != restrict[x]:
                    continue
                if any(
                    gamma[i][0] != gamma[i][1]
                    for i, key in enumerate(keys)
                    if key in exclusive
                ):
                    continue
                rows[gamma + ((comp,) if at_square else ())] = {0: (weight, 0)}
        if not rows:
            return None
        choices[x] = rows
        factors.append((keys + ((SQUARE,) if at_square else ()), rows, {}))
    for edge, keys in sorted(edges.items()):
        lo, hi, a = edge
        centers = tuple(int(x == hi) for x, _ in keys)
        domains = [
            sorted({row[frame[x].index(axis)] for row in choices[x]})
            for x, axis in keys
        ]
        rows = {}
        for gamma in product(*domains):
            if edge == live_edge:
                for probe in sorted({p for _, p in square_rows}):
                    row = probed_action_edge(
                        gamma[0], centers[0], int(live[0] == hi), probe
                    )
                    if row:
                        rows[gamma + (probe,)] = witness.gaussian(remap(row, (lo, hi)))
                continue
            if edge in fixed_edges:
                row = fixed_action_edge(gamma, centers, fixed_edges[edge])
            elif edge in joined_source:
                row = joint_source(gamma[0], joined_source[edge])
                if centers[0]:
                    row = remap(row, (1, 0))
            else:
                row = witness.local_edge(gamma, centers)
            if row:
                rows[gamma] = witness.gaussian(remap(row, (lo, hi)))
        if not rows:
            return None
        degree = 2 * (len(keys) + int(edge in joined_source))
        factors.append(
            (
                tuple(keys) + ((PROBE,) if edge == live_edge else ()),
                rows,
                {lo: degree, hi: degree},
            )
        )
    if square_rows:
        factors.append(
            (
                (SQUARE, PROBE),
                {key: {0: (weight, 0)} for key, weight in square_rows.items()},
                {},
            )
        )
    for x, a in sources:
        y = x ^ (1 << a)
        if (min(x, y), max(x, y), a) in joined_source:
            continue
        probe = None if (x, a) == fixed_source else ()
        row = add(*(witness.anchored(0, (), probe, gamma) for gamma in range(4)))
        factors.append(((), {(): witness.gaussian(remap(row, (x, y)))}, {x: 2, y: 2}))
    assert Counter(
        {x: sum(f[2].get(x, 0) for f in factors) for x in SITES}
    ) == dict.fromkeys(SITES, 8)
    assert set(Counter(k for f in factors for k in f[0]).values()) == {2}
    return factors, divisor, exclusive


def contraction(geom, core, restrict=None):
    prepared = prepare(geom, core, restrict)
    if prepared is None:
        return Fraction(), 0
    factors, divisor, exclusive = prepared
    raw, peak = eliminate_components(factors, exclusive)
    return Fraction(raw, divisor), peak


def solve(geom):
    branches = product(
        protected_branches(geom.linked, geom.other),
        *(free_branches(t) for t in geom.free_tori),
    )
    total = Fraction()
    peak = 0
    count = 0
    for row in branches:
        weight = Fraction(1)
        domains = {}
        for w, d in row:
            weight *= w
            domains.update(d)
        value, rows = contraction(geom, domains)
        total += weight * value
        peak = max(peak, rows)
        count += 1
    assert count == 15 * 3 ** len(geom.free_tori)
    return total, peak


def data():
    rows = []
    kinds = Counter()
    for a, b in ((2, 2), (2, 3)):
        for omitted, changes, frames, sources in census(a, b):
            geom = geometry(frames, sources)
            square = geom.square
            sizes = tuple(
                sorted(
                    ([1] if square is not None else [])
                    + [4] * (1 + len(geom.free_tori))
                )
            )
            kinds[a, b, sizes] += 1
            rows.append(((a, b, omitted, changes), geom))
    assert kinds == WORD_TYPES

    def flip_site(x):
        return (x & 3) | ((x & 4) << 1) | ((x & 8) >> 1)

    def flip_axis(a):
        return 5 - a if a in (2, 3) else a

    for a, b in ((2, 2), (2, 3)):
        rotated = {
            (
                flip_site(omitted),
                tuple(
                    sorted(
                        (flip_site(x), tuple(sorted(flip_axis(i) for i in pair)))
                        for x, pair in changes
                    )
                ),
            )
            for _, _, omitted, changes in (
                label for label, _ in rows if label[:2] == (a, b)
            )
        }
        assert rotated == {
            (h, c) for h, c, _, _ in census(flip_axis(a), flip_axis(b))
        }
    return rows


def controls(rows):
    old = geometry(witness.FRAME_PLANES, witness.SOURCE_LINKS)
    value, _ = contraction(
        old,
        dict.fromkeys(witness.BASES, ((2, 2),)),
        dict.fromkeys(witness.FRAME_PLANES, witness.FIXED_GAMMAS),
    )
    assert value * Fraction(365, 93312) == Fraction(
        79646312375, 10625324586456701730816
    )
    assert len(rows) == 12
    print(
        "generic no-square fixed-label control and complete k3 geometry census pass",
        flush=True,
    )
    check_local_moments()
    squares = [geom for _, geom in rows if geom.square is not None]
    assert len(squares) == 8
    for geom in squares:
        square_control(geom.square, geom.live, geom.fixed_square)
    print("all eight live square factors match direct quaternion controls", flush=True)
    square = squares[0]
    restricted = dict.fromkeys(square.frame, witness.FIXED_GAMMAS)
    scalar_core = dict.fromkeys(square.linked + square.other, ((2, 2),))
    local, peak = contraction(square, scalar_core, restricted)
    assert local == Fraction(102985502126335, 3541774862152233910272)
    print("fixed-gamma square control", local, "peak", peak, flush=True)


def main():
    ap = ArgumentParser(description=__doc__)
    modes = ap.add_mutually_exclusive_group()
    modes.add_argument("--word", type=int, choices=range(12))
    modes.add_argument("--controls-only", action="store_true")
    args = ap.parse_args()
    rows = data()
    controls(rows)
    if args.controls_only:
        return
    selected = range(len(rows)) if args.word is None else (args.word,)
    totals = Counter()
    for i in selected:
        label, geom = rows[i]
        t = perf_counter()
        value, peak = solve(geom)
        kind = label[:2], geom.square is not None, len(geom.free_tori)
        expected = {
            ((2, 2), False, 1): Fraction(15856502831317631804805, 281474976710656),
            ((2, 2), True, 0): Fraction(162048281191263238005, 4398046511104),
            ((2, 3), True, 0): Fraction(1379328468900739359525, 281474976710656),
            ((2, 3), True, 1): Fraction(11034837982644552391725, 2251799813685248),
        }
        assert value == expected[kind], (i, kind, value)
        totals[label[:2]] += value
        print(
            "word",
            i,
            label,
            "unsigned axis coefficient",
            value,
            "peak",
            peak,
            "seconds",
            round(perf_counter() - t, 3),
            flush=True,
        )
    if args.word is None:
        same, mixed = totals[2, 2], totals[2, 3]
        shear = 2 * (same - mixed)
        assert same == Fraction(26227592827558479037125, 70368744177664)
        assert mixed == Fraction(22069465733850467267925, 1125899906842624)
        assert shear == Fraction(397572019507085197326075, 562949953421312)
        print(
            "same",
            same,
            "unsigned mixed",
            mixed,
            "fixed-origin shear before g2^30",
            shear,
            flush=True,
        )


if __name__ == "__main__":
    main()
