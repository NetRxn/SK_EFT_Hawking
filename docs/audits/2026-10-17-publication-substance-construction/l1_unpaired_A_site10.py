"""Replay one signed dominant-B rank-one component across its site-10 selectors."""

import json
import signal
from argparse import ArgumentParser
from collections import Counter, defaultdict
from fractions import Fraction
from functools import lru_cache
from hashlib import sha256
from itertools import combinations, product
from math import comb, prod
from pathlib import Path
from time import monotonic

from l1_extended_offset_witness_k2 import indexed_join
from l1_reduced_wedge_reference import wedge_sign
from l1_unpaired_A_dominant_components import (
    DIGEST,
    QKEYS,
    component_partition,
    digest_rows,
    input_words,
    table_sum,
)
from l1_unpaired_A_group import DIVISOR, environment
from l1_unpaired_B_census import B_BOUNDARY
from l1_unpaired_offset_factors import FRAME_PLANES, SLOTS, gkey, prepare, qkey
from l1_unpaired_signed_slice import (
    CUT_EDGES,
    PRODUCT_CAP,
    ROW_CAP,
    check_grades,
    freeze,
)

MEMBER_DIGEST = "fe6c9dd82e8a4eb6f33f2f0e80b168075333db93bd423a0da4349a7ce44135ea"
ROSTER_DIGEST = "b8bde9d2380ff0fa25a5d2478cd30042c4144d024638729801ddbd5c439e4dae"
JOINT_DIGEST = "a35f2af71cb901a9103614b093e7b56b217b0d2094cb9e2e40db6f145504a02e"
COMPONENT_PINS = {
    (0, 3): (60, (4, 5), MEMBER_DIGEST, JOINT_DIGEST),
    (0, 0): (
        12,
        (4, 1),
        "24649b6ae541a1c09f0ea2a396ba36d8606064827239d72a7b19bd933f26aae8",
        "0353a8533c18ca0b722a788e20e853bccc53cf4cf459f8ae1cfcb2a679ab7707",
    ),
}
TARGET = gkey(1, 1)
DUMMY = qkey((15, 3))


def restricted_transfer(factors, required, restriction):
    factors = list(factors)
    total = Counter()
    for _, _, g in factors:
        total.update(g)

    def prune(f):
        keys, rows, grade = f
        assert sum(grade.values()) % 2 == 0
        # Keep bytes, including the selected partial ones, for wedge signs.
        complete = (
            sum(255 << (8 * x) for x, n in grade.items() if n == total[x]) & restriction
        )

        def allowed(mask):
            return not (mask & restriction & ~required) and (mask & complete) == (
                required & complete
            )

        out = {
            k: {m: v for m, v in row.items() if allowed(m)} for k, row in rows.items()
        }
        return keys, {k: r for k, r in out.items() if r}, grade

    factors = [prune(f) for f in factors]
    if any(not r for _, r, _ in factors):
        return (), {}, {}
    while len(factors) > 1:
        choices = []
        for i, j in combinations(range(len(factors)), 2):
            a, b = factors[i], factors[j]
            ga = Counter(a[2])
            ga.update(b[2])
            assert all(n <= 8 for n in ga.values())
            opened = {x: n for x, n in ga.items() if n < 8}
            cost = 10 ** len(set(a[0]) ^ set(b[0])) * prod(
                comb(8, n) for n in opened.values()
            )
            choices.append((cost, i, j, ga, opened))
        _, i, j, ga, opened = min(choices)
        closed = sum(255 << (8 * x) for x, n in ga.items() if n == 8)
        assert not closed & restriction
        keys, rows, _ = indexed_join(
            factors[i], factors[j], closed, ROW_CAP, PRODUCT_CAP
        )
        factors[i] = prune((keys, rows, opened))
        if not factors[i][1]:
            return (), {}, {}
        factors.pop(j)
    return factors[0]


def site10_transfers(rest, selector):
    fs = [freeze(f, selector) for f in rest]
    left = [f for f in fs if gkey(3, 0) in f[0]]
    right = [f for f in fs if gkey(3, 0) not in f[0]]
    assert len(left) == 2
    degrees = []
    for branch in (left, right):
        d = Counter()
        for _, _, g in branch:
            d.update(g)
        degrees.append(dict(d))
    assert degrees == [{1: 2, 2: 4, 3: 6}, {1: 2, 3: 2, 9: 4, 11: 4}], degrees
    lmask = 255 << (8 * 2)
    rmask = sum(255 << (8 * x) for x in (9, 11))
    full = 255 << (8 * 3)

    @lru_cache(maxsize=18)
    def left_map(mask):
        return restricted_transfer(left, mask, lmask)

    @lru_cache(maxsize=16)
    def right_map(mask):
        keys, rows, grade = restricted_transfer(right, mask, rmask)
        table = defaultdict(list)
        shared = (gkey(3, 3), ("coordinate", 3, 3))
        if rows:
            assert set(keys) == set(shared)
        order = tuple(keys.index(k) for k in shared) if rows else ()
        for k, row in rows.items():
            for m, value in row.items():
                table[tuple(k[i] for i in order), m & full].append((m, value))
        return table

    def query(target):
        lk, lr, _ = left_map(target & lmask)
        rr = right_map(target & rmask)
        if not lr or not rr:
            return None, 0
        shared = (gkey(3, 3), ("coordinate", 3, 3))
        assert set(lk) == set(shared)
        order = tuple(lk.index(k) for k in shared)
        pairs = re = im = 0
        for k, row in lr.items():
            labels = tuple(k[i] for i in order)
            for a, (x, y) in row.items():
                if a & ~(target | full):
                    continue
                for b, (u, v) in rr.get((labels, full ^ (a & full)), ()):
                    if a & b or a | b != target | full:
                        continue
                    pairs += 1
                    if pairs > PRODUCT_CAP:
                        raise RuntimeError("partial transfer complement cap")
                    sign = wedge_sign(a, b)
                    re += sign * (x * u - y * v)
                    im += sign * (x * v + y * u)
        return (re, im) if re or im else None, pairs

    return query


def site10_cut(a):
    check_grades(a, {})
    for _ in range(12):
        choices = []
        domains = [
            {k: len({v[i] for v in rows}) for i, k in enumerate(keys)}
            for keys, rows, _ in a
        ]
        for i, j in combinations(range(len(a)), 2):
            fa, fb = a[i], a[j]
            left_labels, right_labels = set(fa[0]), set(fb[0])
            if not (left_labels & right_labels or fa[2].keys() & fb[2].keys()):
                continue
            if (not fa[2] and gkey(11, 3) in left_labels) or (
                not fb[2] and gkey(11, 3) in right_labels
            ):
                continue
            if left_labels == {DUMMY} and not fa[2] and not ({3, 11} & fb[2].keys()):
                continue
            if right_labels == {DUMMY} and not fb[2] and not ({3, 11} & fa[2].keys()):
                continue
            grade = Counter(fa[2])
            grade.update(fb[2])
            assert all(n <= 8 for n in grade.values())
            opened = {x: n for x, n in grade.items() if n < 8}
            domain = domains[i] | domains[j]
            cost = prod(domain[k] for k in left_labels ^ right_labels) * prod(
                comb(8, n) for n in opened.values()
            )
            choices.append(
                (not any(grade[x] == 8 for x in B_BOUNDARY), cost, i, j, grade, opened)
            )
        _, _, i, j, grade, opened = min(choices)
        closed = sum(255 << (8 * x) for x, n in grade.items() if n == 8)
        if closed == 255 << (8 * 10):
            left, right = a[i], a[j]
            rest = [f for k, f in enumerate(a) if k not in (i, j)]
            return left, right, rest
        keys, rows, _ = indexed_join(a[i], a[j], closed, ROW_CAP, PRODUCT_CAP)
        assert rows
        a[i] = keys, rows, opened
        a.pop(j)
    raise RuntimeError("did not encounter intended site10 cut")


def component_factors(primitive_path, receipt_paths, logs, component=(0, 3)):
    count, shape, member_digest, joint_digest = COMPONENT_PINS[component]
    records = [
        json.loads(line)
        for line in primitive_path.read_text().splitlines()
        if line.strip()
    ]
    (record,) = (row for row in records if row["primitive_sha256"] == DIGEST)
    primitive = tuple((mask, tuple(value)) for mask, value in record["primitive_rows"])
    assert len(primitive) == 208 and digest_rows(primitive) == DIGEST
    words = input_words(sorted(receipt_paths), sorted(logs), primitive)
    assert len(words) == 9216
    selected = None
    for block_id, component_id, c1, c9, c3, c11, groups in component_partition(words):
        if (block_id, component_id) != component:
            continue
        members = sorted(
            index for _, rows in groups for _, _, index in rows if index is not None
        )
        assert selected is None and (len(c3), len(c11)) == shape
        assert len(members) == count and digest_rows(members) == member_digest
        assert sum(len(rows) for _, rows in groups) == count
        selected = c1, table_sum(c3), c9, table_sum(c11)
    assert selected is not None
    c1, c3, c9, c11 = selected
    joint = tuple(
        ((u, v), Fraction(a * b)) for (u, a), (v, b) in product(c3[1], c11[1])
    )
    assert digest_rows(joint) == joint_digest

    factors = prepare()
    centers = dict(zip(sorted(FRAME_PLANES), factors[:15], strict=True))
    edges = dict(zip(sorted(SLOTS), factors[15:-2], strict=True))

    active = {}
    for site, (keys, rows) in zip((1, 3, 9, 11), selected, strict=True):
        assert keys == tuple(k for k in centers[site][0] if k not in QKEYS)
        table = {k: {0: (v, 0)} for k, v in rows}
        if site == 11:
            keys = (*keys, DUMMY)
            table = {(*k, 0): row for k, row in table.items()}
        active[site] = keys, table, {}
    out = [((), {(): dict(primitive)}, B_BOUNDARY), ((DUMMY,), {(0,): {0: (1, 0)}}, {})]
    out.extend(active[x] for x in (3, 11))
    out.extend(
        active.get(x, row)
        for x, row in centers.items()
        if not x & 4 and x not in (3, 11)
    )
    out.extend(row for edge, row in edges.items() if edge not in CUT_EDGES)
    assert len(out) == 20
    return out


def selector_roster(factors):
    domains = [
        {key[keys.index(TARGET)] for key in rows}
        for keys, rows, _ in factors
        if TARGET in keys
    ]
    assert len(domains) == 2
    domain = sorted(set.intersection(*domains))
    assert domain == [(0,), (1,), (2,), (3,)]
    roster = []
    cuts = {}
    for gamma in domain:
        fa, fb, rest = site10_cut(
            [freeze(factor, {TARGET: gamma}) for factor in factors]
        )
        assert set(fa[0]).isdisjoint(fb[0])
        outer, _, boundary = environment(rest)
        assert set(outer) == set(fa[0]) | set(fb[0]) and boundary == {
            1: 4,
            2: 4,
            9: 4,
            11: 4,
        }
        outer = tuple(sorted(outer))
        projections = []
        for keys, rows, _ in rest:
            shared = tuple(k for k in outer if k in keys)
            if shared:
                positions = tuple(keys.index(k) for k in shared)
                projections.append(
                    (
                        shared,
                        {
                            tuple(key[i] for i in positions)
                            for key, row in rows.items()
                            if row
                        },
                    )
                )
        assert Counter(k for keys, _ in projections for k in keys) == Counter(outer)
        candidates = []
        for a, b in product(fa[1], fb[1]):
            selector = dict(zip(fa[0], a, strict=True)) | dict(
                zip(fb[0], b, strict=True)
            )
            if all(
                tuple(selector[k] for k in shared) in rows
                for shared, rows in projections
            ):
                candidates.append(tuple(selector[k] for k in outer))
        assert len(candidates) == len(set(candidates)) == 64
        roster.extend((gamma, outer, values) for values in sorted(candidates))
        cuts[gamma] = fa, fb, rest, boundary
    assert len({values for _, _, values in roster}) == 256
    assert (
        sha256(json.dumps(roster, separators=(",", ":")).encode()).hexdigest()
        == ROSTER_DIGEST
    )
    return roster, cuts


def selector_scalar(fa, fb, rest, boundary, selector):
    closing = 255 << (8 * 10)
    full = sum(255 << (8 * x) for x in boundary)
    right_mask = (255 << (8 * 9)) | (255 << (8 * 11))
    a_rows, b_rows = (
        factor[1][tuple(selector[k] for k in factor[0])] for factor in (fa, fb)
    )
    right_index = defaultdict(list)
    for mask, value in b_rows.items():
        right_index[mask & closing].append((mask, value))

    weights = defaultdict(lambda: [0, 0])
    products = 0
    for a, (x, y) in a_rows.items():
        for b, (u, v) in right_index[closing ^ (a & closing)]:
            if a & b:
                continue
            products += 1
            if products > PRODUCT_CAP:
                raise RuntimeError("site-10 compatible products exceed cap")
            mask = (a | b) ^ closing
            assert not mask & ~full
            complement = full ^ mask
            sign = wedge_sign(a, b) * wedge_sign(mask, complement)
            weights[complement][0] += sign * (x * u - y * v)
            weights[complement][1] += sign * (x * v + y * u)

    query = site10_transfers(rest, selector)
    total = [0, 0]
    nonzero = 0
    for mask in sorted(weights, key=lambda m: (m & right_mask, m)):
        result, _ = query(mask)
        if result:
            nonzero += 1
            x, y = weights[mask]
            u, v = result
            total[0] += x * u - y * v
            total[1] += x * v + y * u
    return total, products, len(weights), nonzero


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("start", type=int)
    parser.add_argument("stop", type=int)
    parser.add_argument("--gamma-slice", type=int, choices=range(4), required=True)
    parser.add_argument("--primitive", type=Path, required=True)
    parser.add_argument("--rows", type=Path, nargs="+", required=True)
    parser.add_argument("--logs", type=Path, nargs="*", default=[])
    parser.add_argument(
        "--component",
        type=int,
        choices=(0, 3),
        default=3,
        help="rank-one component of block 0",
    )
    args = parser.parse_args()
    low = 64 * args.gamma_slice
    if not low <= args.start < args.stop <= low + 64:
        parser.error(f"range must lie within gamma slice [{low}, {low + 64})")
    start = monotonic()
    signal.alarm(120)
    roster, cuts = selector_roster(
        component_factors(args.primitive, args.rows, args.logs, (0, args.component))
    )
    batch = [0, 0]
    for index in range(args.start, args.stop):
        tick = monotonic()
        gamma, keys, values = roster[index]
        assert gamma == (args.gamma_slice,)
        selector = dict(zip(keys, values, strict=True))
        total, products, queries, nonzero = selector_scalar(*cuts[gamma], selector)
        for k, value in enumerate(total):
            batch[k] += value
        print(
            "exact selector",
            index,
            "raw",
            total,
            "scaled",
            tuple(str(Fraction(x, DIVISOR)) for x in total),
            "products",
            products,
            "queries",
            queries,
            "nonzero",
            nonzero,
            "seconds",
            monotonic() - tick,
            flush=True,
        )
    print(
        "terminal range",
        args.start,
        args.stop,
        "roster",
        ROSTER_DIGEST,
        "raw",
        batch,
        "scaled",
        tuple(str(Fraction(x, DIVISOR)) for x in batch),
        "elapsed",
        monotonic() - start,
        flush=True,
    )
    signal.alarm(0)


if __name__ == "__main__":
    main()
