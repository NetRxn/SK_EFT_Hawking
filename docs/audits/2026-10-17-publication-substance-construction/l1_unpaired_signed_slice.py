"""Replay the eight exact shards of one guarded unpaired-word slice."""

from collections import Counter
from hashlib import sha256
from itertools import combinations
from math import comb, prod

from l1_extended_offset_witness_k2 import indexed_join
from l1_reduced_wedge_reference import wedge_sign
from l1_unpaired_offset_factors import FRAME_PLANES, SLOTS, prepare, qkey
from l1_unpaired_upper_support import contract_env

CUT_EDGES = {(4, 0), (4, 1), (5, 1), (5, 3), (6, 0), (7, 3),
             (8, 2), (10, 2), (12, 0), (12, 1), (13, 1), (14, 0)}
FIXED = {(5, 1): 5, (5, 3): 5, (7, 1): 1, (7, 3): 5, (13, 3): 1, (15, 3): 1}
VARYING = (15, 1)
A_BOUNDARY = {4: 2, 5: 2, 8: 6, 10: 6}
B_BOUNDARY = {4: 6, 5: 6, 8: 2, 10: 2}
ROW_CAP = 120_000
PRODUCT_CAP = 300_000


def freeze(factor, coordinates):
    keys, rows, degree = factor
    fixed = {i: coordinates[key] for i, key in enumerate(keys) if key in coordinates}
    remaining = tuple(key for key in keys if key not in coordinates)
    selected = {}
    for values, row in rows.items():
        if all(values[i] == coordinate for i, coordinate in fixed.items()):
            index = tuple(value for i, value in enumerate(values) if i not in fixed)
            assert index not in selected
            selected[index] = row
    return remaining, selected, degree


def check_grades(factors, boundary):
    labels = Counter(key for keys, _, _ in factors for key in keys)
    assert all(count == 2 for count in labels.values())
    total = Counter()
    for _, rows, degree in factors:
        total.update(degree)
        assert sum(degree.values()) % 2 == 0
        for row in rows.values():
            for mask in row:
                assert mask.bit_count() == sum(degree.values())
                assert all(((mask >> (8 * site)) & 255).bit_count() == grade
                           for site, grade in degree.items())
    assert all(grade <= 8 for grade in total.values())
    assert {site: grade for site, grade in total.items() if grade < 8} == boundary


def contract(factors, boundary, close_boundary_first=False):
    check_grades(factors, boundary)
    if any(not rows for _, rows, _ in factors):
        return {}, []
    trace = []
    factors = list(factors)
    while len(factors) > 1:
        domains = [{key: len({values[i] for values in rows})
                    for i, key in enumerate(keys)} for keys, rows, _ in factors]
        choices = []
        for i, j in combinations(range(len(factors)), 2):
            left, right = factors[i], factors[j]
            left_keys, right_keys = set(left[0]), set(right[0])
            if not (left_keys & right_keys or left[2].keys() & right[2].keys()):
                continue
            degree = Counter(left[2])
            degree.update(right[2])
            opened = {site: grade for site, grade in degree.items() if grade < 8}
            domain = domains[i] | domains[j]
            cost = prod(domain[key] for key in left_keys ^ right_keys)
            cost *= prod(comb(8, grade) for grade in opened.values())
            priority = close_boundary_first and not any(degree[site] == 8 for site in B_BOUNDARY)
            choices.append((priority, cost, i, j, degree, opened))
        _, _, i, j, degree, opened = min(choices)
        closed_sites = tuple(sorted(site for site, grade in degree.items() if grade == 8))
        closed = sum(255 << (8 * site) for site in closed_sites)
        keys, rows, count = indexed_join(factors[i], factors[j], closed, ROW_CAP, PRODUCT_CAP)
        trace.append((closed_sites, count, sum(map(len, rows.values()))))
        if not rows:
            return {}, trace
        factors[i] = keys, rows, opened
        factors.pop(j)
    keys, rows, degree = factors[0]
    assert not keys and set(rows) == {()} and degree == boundary
    return rows[()], trace


def main():
    left = ((), {(): {0x41: (2, 3)}}, {0: 2})
    right = ((), {(): {0xBE: (5, -2)}}, {0: 6})
    assert wedge_sign(0x41, 0xBE) == -1
    forward = indexed_join(left, right, 255, 100, 100)
    assert forward == indexed_join(right, left, 255, 100, 100)
    assert forward[1] == {(): {0: (-16, -11)}}

    factors = prepare()
    centers = dict(zip(sorted(FRAME_PLANES), factors[:15], strict=True))
    edges = dict(zip(sorted(SLOTS), factors[15:-2], strict=True))
    a = [row for site, row in centers.items() if not site & 4]
    a.extend(row for edge, row in edges.items() if edge not in CUT_EDGES)
    a.extend(factors[-2:])
    b = [row for site, row in centers.items() if site & 4]
    b.extend(row for edge, row in edges.items() if edge in CUT_EDGES)
    assert len(a) == len(b) == 20
    labels_a = {key for keys, _, _ in a for key in keys}
    labels_b = {key for keys, _, _ in b for key in keys}
    assert labels_a & labels_b == {qkey(edge) for edge in (*FIXED, VARYING)}

    upper = contract_env([centers[x] for x in (12, 13, 14, 15)]
                         + [edges[e] for e in ((8, 2), (10, 2), (12, 0), (12, 1), (14, 0))])
    lower = contract_env([centers[x] for x in (4, 6, 7)]
                         + [edges[e] for e in ((4, 0), (4, 1), (6, 0))])
    digests = set()
    for q in range(8):
        coordinates = {qkey(edge): value for edge, value in (FIXED | {VARYING: q}).items()}
        cached = [upper, lower, centers[5]]
        cached.extend(freeze(edges[e], coordinates) for e in ((5, 1), (5, 3), (7, 3), (13, 1)))
        rhs, _ = contract(cached, B_BOUNDARY)
        direct, _ = contract([freeze(factor, coordinates) for factor in b], B_BOUNDARY)
        assert rhs == direct
        if q not in (1, 5):
            assert not rhs
            print("coordinate", q, "both exact B maps empty", flush=True)
            continue
        assert len(rhs) == 24
        digests.add(sha256(repr(sorted(rhs.items())).encode()).hexdigest())
        left_factors = [freeze(factor, coordinates) for factor in a]
        scalar, trace = contract([((), {(): rhs}, B_BOUNDARY), *left_factors], {},
                                 close_boundary_first=True)
        assert not scalar and trace == [((4,), 32, 24), ((5,), 0, 0)]
        print("coordinate", q, "B maps agree (24 rows), closure", trace, flush=True)
    assert len(digests) == 2
    print("complete eight-value slice subtotal: 0")


if __name__ == "__main__":
    main()
