"""Exact zero filter from projected site-13/15 support on B."""

from collections import Counter, defaultdict
from itertools import combinations, product
from math import comb, prod
from time import monotonic
import signal

from l1_extended_offset_witness_k2 import indexed_join
from l1_unpaired_offset_factors import FRAME_PLANES, SLOTS, gkey, prepare, qkey

ROW_CAP = 120_000
PRODUCT_CAP = 300_000
SITES = (13, 15)
UPPER_CENTERS = {12, 13, 14, 15}
UPPER_EDGES = {(8, 2), (10, 2), (12, 0), (12, 1), (14, 0)}


def contract_env(factors):
    while len(factors) > 1:
        choices = []
        for i, j in combinations(range(len(factors)), 2):
            a, b = factors[i], factors[j]
            common = set(a[0]) & set(b[0])
            if not common and not a[2].keys() & b[2].keys():
                continue
            degree = Counter(a[2])
            degree.update(b[2])
            assert all(d <= 8 for d in degree.values())
            opened = {x: d for x, d in degree.items() if d < 8}
            cost = 10 ** len(set(a[0]) ^ set(b[0])) * prod(
                comb(8, d) for d in opened.values()
            )
            choices.append((cost, i, j, degree, opened))
        _, i, j, degree, opened = min(choices)
        closed = sum(255 << (8 * x) for x, d in degree.items() if d == 8)
        a, b = factors[i], factors[j]
        keys, rows, pairs = indexed_join(a, b, closed, ROW_CAP, PRODUCT_CAP)
        print(
            "upper environment join",
            len(factors),
            pairs,
            sum(map(len, rows.values())),
            flush=True,
        )
        assert rows
        factors[i] = (keys, rows, opened)
        factors.pop(j)
    return factors[0]


def values_of(factor, labels, sites):
    axes, rows, degrees = factor
    indexes = tuple(axes.index(k) for k in labels)
    out = defaultdict(set)
    for key, row in rows.items():
        q = tuple(key[i] for i in indexes)
        out[q].update(tuple((mask >> (8 * x)) & 255 for x in sites) for mask in row)
    return out


def upper_support(env, connector):
    # Keep the two shared gamma labels until after exact matching.
    gammas = tuple(gkey(x, 1) for x in SITES)
    exterior = values_of(env, gammas, SITES)
    live = qkey((15, 1))
    joins = values_of(connector, gammas + (live,), SITES)
    support = defaultdict(set)
    products = compatible = 0
    for (g, h, q), masks in joins.items():
        for a, b in exterior[g, h]:
            for c, d in masks:
                products += 1
                if a & c or b & d:
                    continue
                compatible += 1
                if compatible > PRODUCT_CAP:
                    raise RuntimeError("projected compatible products exceed cap")
                pair = (255 ^ (a | c), 255 ^ (b | d))
                assert all(x.bit_count() == 2 for x in pair)
                support[q].add(pair)
    return support, (products, compatible)


def main():
    signal.alarm(75)
    factors = prepare()
    centers = dict(zip(sorted(FRAME_PLANES), factors[: len(FRAME_PLANES)], strict=True))
    edges = dict(zip(sorted(SLOTS), factors[len(FRAME_PLANES) : -2], strict=True))
    start = monotonic()
    env = contract_env(
        [centers[x] for x in sorted(UPPER_CENTERS)]
        + [edges[e] for e in sorted(UPPER_EDGES)]
    )
    assert set(env[0]) == {gkey(x, 1) for x in SITES}
    assert dict(env[2]) == {8: 2, 10: 2, 13: 2, 15: 2}
    assert (len(env[1]), sum(map(len, env[1].values()))) == (16, 3456)
    print("upper environment", len(env[1]), sum(map(len, env[1].values())), flush=True)
    support, count = upper_support(env, edges[(13, 1)])
    sizes = [len(support[q]) for q in range(8)]
    assert count == (1_392_640, 47_872)
    assert sizes == [176, 144, 144, 110, 176, 144, 144, 110]
    print("upper projected products", count, "pairs by q15,1", sizes, flush=True)
    first = values_of(edges[(5, 3)], (qkey((5, 3)), qkey((13, 3))), (13,))
    second = values_of(edges[(7, 3)], (qkey((7, 3)), qkey((15, 3))), (15,))
    by_connect = Counter()
    excluded = set()
    for a, b, c, d, q in product(
        (1, 2, 3, 5, 6, 7), range(8), range(8), range(8), range(8)
    ):
        ok = any((x,) in first[a, b] and (y,) in second[c, d] for x, y in support[q])
        if not ok:
            excluded.add((a, b, c, d, q))
            by_connect[q] += 1
    assert len(excluded) == 12_480
    print(
        "upper projection excluded",
        len(excluded),
        "of",
        6 * 8**4,
        "q cases, covering",
        48 * len(excluded),
        "of",
        1_179_648,
        "full tuples",
        "by q15,1",
        dict(by_connect),
        "seconds",
        monotonic() - start,
        flush=True,
    )
    for sample, expected in (
        ((1, 1, 1, 1, 1), False),
        ((1, 1, 1, 1, 5), False),
        ((1, 1, 1, 5, 1), True),
    ):
        assert (sample in excluded) == expected
        print(
            "known B-zero sample",
            sample,
            "excluded by this projection",
            expected,
            flush=True,
        )
    print(
        "Excluded tuples have zero support for this word. Other tuples are inconclusive.",
        flush=True,
    )


if __name__ == "__main__":
    main()
