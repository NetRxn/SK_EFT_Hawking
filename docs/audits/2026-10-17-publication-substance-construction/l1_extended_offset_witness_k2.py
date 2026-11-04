"""Exact six-word subfamily with two frame-plane changes at offset 1.

The source origins are fixed at 0 and 1. The final shear combines the
same-axis and mixed-axis terms, using transverse axis exchange.
This replay covers the declared paired-word subfamily.
"""

from argparse import ArgumentParser
from collections import Counter, defaultdict
from fractions import Fraction
from functools import cache
from itertools import combinations, product
from math import comb, prod
from time import perf_counter

import l1_extended_offset_witness as witness
from l1_direct_b_haar import add, scale
from l1_extended_anchor_census import anchor_multiplicity
from l1_extended_four_face_gauge_join import IDENTITY
from l1_extended_mixed_curvature_core import conditional
from l1_extended_mixed_frame_join import preceding_parity
from l1_extended_mixed_frame_moment import source_edge_moments
from l1_extended_offset_pair_census import AXES, FRAME_PAIRS, SITES, source_endpoints
from l1_extended_two_mixed_centers import remap, source_edge

ROW_CAP = 120_000
PAIR_CAP = 3_000_000

BASE = (0, 1)
ALT = tuple(p for p in FRAME_PAIRS if p != BASE)
EXPECTED = {
    (2, 2): [
        (0, ((4, (1, 2)), (6, (0, 2)))),
        (1, ((5, (1, 2)), (7, (0, 2)))),
        (4, ((0, (1, 2)), (2, (0, 2)))),
        (5, ((1, (1, 2)), (3, (0, 2)))),
    ],
    (2, 3): [(0, ((6, (0, 2)), (8, (1, 3)))), (1, ((5, (1, 2)), (11, (0, 3))))],
}


def enumerate_words(source_axes):
    found = []
    endpoints = source_endpoints(1, *source_axes)
    for omitted in SITES:
        senders = tuple(x for x in SITES if x != omitted)
        demand = tuple(4 - endpoints[x] - 2 * (x != omitted) for x in SITES)
        for x, y in combinations(senders, 2):
            incoming = Counter(
                s ^ (1 << a) for s in senders if s not in (x, y) for a in BASE
            )
            deficits = Counter({s: need - incoming[s] for s, need in enumerate(demand)})
            if min(deficits.values()) < 0:
                continue
            for a, b in product(ALT, repeat=2):
                modified = Counter(
                    (x ^ (1 << a[0]), x ^ (1 << a[1]), y ^ (1 << b[0]), y ^ (1 << b[1]))
                )
                if deficits == modified:
                    found.append((omitted, ((x, a), (y, b))))
    assert found == EXPECTED[source_axes]
    return found


def geometry(omitted, changes, source_axes):
    frame = {x: BASE for x in SITES if x != omitted} | dict(changes)
    edges = defaultdict(list)
    for x, axes in frame.items():
        for a in axes:
            y = x ^ (1 << a)
            edges[min(x, y), max(x, y), a].append((x, a))
    sources = tuple(zip((0, 1), source_axes, strict=True))
    degrees = Counter()
    for (x, y, _), keys in edges.items():
        degrees[x] += 2 * len(keys)
        degrees[y] += 2 * len(keys)
    for x, a in sources:
        degrees[x] += 2
        degrees[x ^ (1 << a)] += 2
    assert degrees == dict.fromkeys(SITES, 8)
    word = [
        (x, *(a for a in AXES if a not in plane))
        for x, plane in frame.items()
        for _ in range(2)
    ]
    action_degree, anchors = anchor_multiplicity(word, 16, 4)
    endpoints = source_endpoints(1, *source_axes)
    assert all(action_degree[x] + 2 * endpoints[x] == 8 for x in SITES)
    assert anchors == 2 ** (60 - len(edges))
    protected = {(y, a) for x, end, a in edges for y in (x, end)} | set(sources)
    faces = {}
    for x, axes in frame.items():
        k, l = (a for a in AXES if a not in axes)
        faces[x, k, l] = {(x, k), (x ^ (1 << k), l), (x ^ (1 << l), k), (x, l)}
    while True:
        counts = Counter(e for ee in faces.values() for e in ee)
        peel = next(
            (
                f
                for f, ee in faces.items()
                if any(counts[e] == 1 and e not in protected for e in ee)
            ),
            None,
        )
        if peel is None:
            break
        del faces[peel]
    assert len(faces) == 8 and all(f[1:] == (2, 3) for f in faces)
    (fixed,) = set.union(*faces.values()) & protected
    assert fixed in sources
    linked = (fixed[0], fixed[0] ^ (1 << fixed[1]))
    assert set(linked) <= {f[0] for f in faces}
    components = [
        {f: ee for f, ee in faces.items() if f[0] & 3 == c}
        for c in sorted({f[0] & 3 for f in faces})
    ]
    assert len(components) == 2 and all(len(c) == 4 for c in components)
    connected, free = sorted(
        components, key=lambda c: not any(fixed in ee for ee in c.values())
    )
    assert not set.union(*connected.values()) & set.union(*free.values())
    other = tuple(f[0] for f in connected if f[0] not in linked)
    return frame, edges, sources, fixed, faces, connected, free, linked, other


def protected_branches(linked, other):
    relabel = dict(zip(witness.BASES, linked + other, strict=True))
    for weight, domain in witness.core_branches():
        yield weight, {relabel[x]: labels for x, labels in domain.items()}


def free_branches(faces):
    # The independent endpoint rotation averages the linked matching term
    # to 2/3 of the same-chirality diagonal product.
    bases = tuple(f[0] for f in faces)
    yield Fraction(1, 256), dict.fromkeys(bases, witness.DIAGONAL)
    for c in (0, 3):
        diagonals = tuple((i, i) for i in range(c, c + 3))
        yield Fraction(1, 1679616), dict.fromkeys(bases, diagonals)


def direct(core, fixed, labels):
    links = {fixed: IDENTITY} if fixed is not None else {}
    return conditional(core, set(links), links, {f: labels[f[0]] for f in core})


def formula(branches, labels):
    return sum(
        weight
        for weight, domain in branches
        if all(labels[x] in rows for x, rows in domain.items())
    )


def controls(data):
    checked = set()
    for _, geom in data:
        frame, edges, sources, fixed, faces, protected, free, linked, other = geom
        signature = tuple(protected), fixed
        if signature in checked:
            continue
        checked.add(signature)
        for graph, link, branches, order in [
            (protected, fixed, list(protected_branches(linked, other)), linked + other),
            (free, None, list(free_branches(free)), tuple(f[0] for f in free)),
        ]:
            for row in [
                ((0, 0),) * 4,
                ((0, 0), (3, 3), (0, 0), (0, 0)),
                ((0, 1), (0, 1), (0, 0), (0, 0)),
                ((1, 2), (1, 2), (0, 0), (3, 3)),
                ((0, 0), (0, 0), (3, 3), (3, 3)),
            ]:
                labels = dict(zip(order, row, strict=True))
                actual, expected = (
                    direct(graph, link, labels),
                    formula(branches, labels),
                )
                assert actual == expected, (
                    tuple(graph),
                    link,
                    labels,
                    actual,
                    expected,
                )
    print(
        "direct protected/unprotected core controls",
        len(checked),
        "geometries",
        flush=True,
    )
    witness.controls()
    exact_core = dict.fromkeys(witness.BASES, ((2, 2),))
    for free_center in (None, 2):
        fixed = {
            x: witness.FIXED_GAMMAS for x in witness.FRAME_PLANES if x != free_center
        }
        factors = witness.prepare(exact_core, fixed)
        assert (
            eliminate(list(factors), witness.EXCLUSIVE)[0]
            == witness.eliminate(factors)[0]
        )
    left = (((0, 0),), {(0,): {15: (2, 3)}, (1,): {15: (7, -2)}}, {0: 4})
    right = (((0, 0),), {(0,): {240: (-4, 2)}, (1,): {15: (4, 5)}}, {0: 4})
    assert indexed_join(left, right, 255, ROW_CAP, PAIR_CAP) == (
        (),
        {(): {0: (-14, -8)}},
        1,
    )
    first = ((), {(): {15: (19, 0)}}, {0: 4})
    second = ((), {(): {240: (13, 0)}}, {0: 4})
    third = ((), {(): {15 << 8: (23, 0)}}, {1: 4})
    fourth = ((), {(): {240 << 8: (17, 0)}}, {1: 4})
    scalar = ((), {(): {0: (7, 0)}}, {})
    assert (
        eliminate_components([first, second, third, fourth, scalar], set())[0] == 676039
    )
    left_label = (((0, 0),), {(0,): {15: (2, 0)}, (1,): {15: (5, 0)}}, {0: 4})
    right_label = (
        ((0, 0),),
        {(0,): {15 << 8: (3, 0)}, (1,): {15 << 8: (11, 0)}},
        {1: 4},
    )
    assert (
        eliminate_components([left_label, second, right_label, fourth, scalar], set())[
            0
        ]
        == 94367
    )
    print("indexed join and disconnected-component controls passed", flush=True)
    for endpoint in (0, 1):
        reference = source_edge(0, endpoint)
        for labels in ((0, 0), (0, 1)):
            actual = joint_source(labels, endpoint)
            assert scale(actual, 4) == reference[labels]
        labels = (0, 0)
        actual = joint_source(labels, endpoint)
        assert actual
        for start in (0, 4):
            trace = add(
                *(
                    source_edge_moments(labels, ((i, i), ()), endpoint)
                    for i in range(start, start + 4)
                )
            )
            assert trace == actual
    print(
        "joint source-action direct and chiral trace controls pass for both anchors",
        flush=True,
    )


@cache
def joint_source(labels, endpoint):
    return source_edge_moments(labels, ((), ()), endpoint)


def prepare(geom, core_labels):
    frame, edges, sources, fixed, faces, *_ = geom
    shared = {}
    for x, a in sources:
        y = x ^ (1 << a)
        e = (min(x, y), max(x, y), a)
        if e in edges:
            assert (x, a) != fixed and len(edges[e]) == 1
            center, _ = edges[e][0]
            shared[e] = (x, a, int(x != center))
    assert len(shared) == int(sources[0][1] == sources[1][1])
    exclusive = {
        key
        for edge, keys in edges.items()
        if len(keys) == 1 and edge not in shared
        for key in keys
    }
    bases = {f[0] for f in faces}
    factors = []
    choices = {}
    for center, axes in frame.items():
        keys = tuple((center, axis) for axis in axes)
        weights = witness.center_weights(
            core_labels[center] if center in bases else None
        )
        rows = {
            labels: {0: (weight, 0)}
            for labels, weight in weights.items()
            if all(
                labels[i][0] == labels[i][1]
                for i, key in enumerate(keys)
                if key in exclusive
            )
        }
        if not rows:
            return None
        choices[center] = rows
        factors.append((keys, rows, {}))
    for edge, keys in sorted(edges.items()):
        lo, hi, _ = edge
        domains = [
            sorted({labels[frame[c].index(a)] for labels in choices[c]})
            for c, a in keys
        ]
        rows = {}
        for labels in product(*domains):
            centers = tuple(int(c == hi) for c, _ in keys)
            if edge in shared:
                row = joint_source(labels[0], shared[edge][2])
                if centers[0]:
                    row = remap(row, (1, 0))
            else:
                row = witness.local_edge(labels, centers)
            if row:
                rows[labels] = witness.gaussian(remap(row, (lo, hi)))
        if not rows:
            return None
        degree = 2 * (len(keys) + int(edge in shared))
        factors.append((tuple(keys), rows, {lo: degree, hi: degree}))
    for x, a in sources:
        y = x ^ (1 << a)
        if (min(x, y), max(x, y), a) in shared:
            continue
        probe = None if (x, a) == fixed else ()
        row = add(*(witness.anchored(0, (), probe, gamma) for gamma in range(4)))
        factors.append(((), {(): witness.gaussian(remap(row, (x, y)))}, {x: 2, y: 2}))
    assert len(factors) == len(frame) + len(edges) + 2 - len(shared)
    assert Counter(
        {x: sum(f[2].get(x, 0) for f in factors) for x in SITES}
    ) == dict.fromkeys(SITES, 8)
    divisor = (
        (witness.SCALE**2) ** len(edges)
        * 4**64
        * witness.SCALE ** (2 - len(shared))
        * 48**7
        * 2**15
    )
    return factors, divisor, exclusive


def indexed_join(left, right, closed, row_cap, pair_cap):
    """Join exact gamma labels and closing-byte complements before multiplying."""
    axes, lr, _ = left
    other, rr, _ = right
    shared = tuple(label for label in axes if label in other)
    ai = tuple(axes.index(x) for x in shared)
    bi = tuple(other.index(x) for x in shared)
    au = tuple(i for i, x in enumerate(axes) if x not in shared)
    bu = tuple(i for i, x in enumerate(other) if x not in shared)
    out_axes = tuple(axes[i] for i in au) + tuple(other[i] for i in bu)
    table = defaultdict(list)
    for key, row in rr.items():
        label = tuple(key[i] for i in bi)
        tail = tuple(key[i] for i in bu)
        for mask, (r, i) in row.items():
            table[label, mask & closed].append(
                (tail, mask, preceding_parity(mask), r, i)
            )
    count = 0
    result = defaultdict(dict)
    allocated = 0
    for key, row in lr.items():
        label = tuple(key[i] for i in ai)
        tail = tuple(key[i] for i in au)
        for a, (r, i) in row.items():
            for rhs, b, p, s, j in table.get((label, closed ^ (a & closed)), ()):
                if a & b:
                    continue
                count += 1
                if count > pair_cap:
                    raise RuntimeError(
                        f"{count} exact compatible products exceed cap {pair_cap}"
                    )
                dest = tail + rhs
                output = result[dest]
                mask = (a | b) ^ closed
                sign = 1 - 2 * ((a & p).bit_count() & 1)
                if mask not in output:
                    allocated += 1
                    if allocated > row_cap:
                        raise RuntimeError(
                            f"{allocated} live row slots exceed cap {row_cap}"
                        )
                re, im = output.get(mask, (0, 0))
                output[mask] = re + sign * (r * s - i * j), im + sign * (r * j + i * s)
    rows = {k: {m: v for m, v in row.items() if any(v)} for k, row in result.items()}
    return out_axes, {k: row for k, row in rows.items() if row}, count


def choose(factors, exclusive):
    candidates = []
    for i, j in combinations(range(len(factors)), 2):
        a, b = factors[i], factors[j]
        labels, other = set(a[0]), set(b[0])
        if not labels & other and not a[2].keys() & b[2].keys():
            continue
        degrees = Counter(a[2])
        degrees.update(b[2])
        assert all(d <= 8 for d in degrees.values())
        opened = {x: d for x, d in degrees.items() if d < 8}
        bound = prod(4 if label in exclusive else 10 for label in labels ^ other)
        bound *= prod(comb(8, d) for d in opened.values())
        candidates.append((bound, i, j, degrees, opened))
    return min(candidates)


def eliminate(factors, exclusive):
    peak = 0
    while len(factors) > 1:
        _, i, j, degrees, opened = choose(factors, exclusive)
        closed = sum(255 << (8 * x) for x, d in degrees.items() if d == 8)
        keys, rows, _ = indexed_join(factors[i], factors[j], closed, ROW_CAP, PAIR_CAP)
        if not rows:
            return 0, peak
        peak = max(peak, sum(map(len, rows.values())))
        factors[i] = keys, rows, opened
        factors.pop(j)
    keys, rows, degrees = factors[0]
    assert not keys and not degrees and set(rows) == {()} and set(rows[()]) == {0}
    real, imag = rows[()][0]
    assert not imag
    return real, peak


def eliminate_components(factors, exclusive):
    """Multiply scalar outputs of groups disconnected in both labels and sites."""
    pending = list(factors)
    product_value = 1
    peak = 0
    while pending:
        group = [pending.pop()]
        labels = set(group[0][0])
        sites = set(group[0][2])
        while neighbors := [
            i
            for i, f in enumerate(pending)
            if labels.intersection(f[0]) or sites.intersection(f[2])
        ]:
            for i in reversed(neighbors):
                f = pending.pop(i)
                group.append(f)
                labels.update(f[0])
                sites.update(f[2])
        raw, size = eliminate(group, exclusive)
        product_value *= raw
        peak = max(peak, size)
    return product_value, peak


def solve(geom):
    frame, edges, sources, fixed, faces, protected, free, linked, other = geom
    total = Fraction()
    peak = 0
    for n, ((u, a), (v, b)) in enumerate(
        product(protected_branches(linked, other), free_branches(free))
    ):
        prepared = prepare(geom, a | b)
        if prepared is None:
            continue
        factors, divisor, exclusive = prepared
        raw, size = eliminate_components(factors, exclusive)
        total += u * v * Fraction(raw, divisor)
        peak = max(peak, size)
    assert n == 44
    return total, peak


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--controls-only", action="store_true")
    args = parser.parse_args()
    data = [
        ((axes, omitted, changes), geometry(omitted, changes, axes))
        for axes in EXPECTED
        for omitted, changes in enumerate_words(axes)
    ]
    controls(data)
    if args.controls_only:
        return
    subtotal = Counter()
    for key, geom in data:
        t = perf_counter()
        value, peak = solve(geom)
        subtotal[key[0]] += value
        print(
            "word",
            key,
            "unsigned axis coefficient",
            value,
            "peak",
            peak,
            "seconds",
            round(perf_counter() - t, 3),
            flush=True,
        )
    same, mixed = subtotal[(2, 2)], subtotal[(2, 3)]
    shear = 2 * (same - mixed)
    assert same == Fraction(247348708021702592193669, 70368744177664)
    assert mixed == Fraction(16670281986745651878525, 70368744177664)
    assert shear == Fraction(28834803254369617539393, 4398046511104)
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
