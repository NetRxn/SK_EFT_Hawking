"""Exact bounded A replay for the selected two-word B-map group."""

import argparse
from collections import Counter, defaultdict
from functools import lru_cache
from hashlib import sha256
from itertools import combinations, permutations
import json
from math import comb, prod

from l1_extended_mixed_frame_join import preceding_parity
from l1_extended_offset_witness_k2 import indexed_join
from l1_reduced_wedge_reference import wedge_sign
from l1_unpaired_B_census import B_BOUNDARY, signed_join
from l1_unpaired_offset_factors import DIVISOR, FRAME_PLANES, SLOTS, gkey, prepare, qkey
from l1_unpaired_signed_slice import (
    CUT_EDGES,
    PRODUCT_CAP,
    ROW_CAP,
    check_grades,
    freeze,
)
from l1_unpaired_source_support import CUT
from l1_unpaired_upper_support import contract_env

WORDS = ((1, 7, 1, 5, 7, 4, 5), (1, 7, 1, 6, 7, 4, 6))
OUTER = (qkey((15, 3)), gkey(9, 0), gkey(9, 1), qkey((9, 1)), gkey(3, 3), qkey((3, 3)))


def grouped_factors():
    factors = prepare()
    centers = dict(zip(sorted(FRAME_PLANES), factors[:15], strict=True))
    edges = dict(zip(sorted(SLOTS), factors[15:-2], strict=True))
    upper = contract_env(
        [centers[x] for x in (12, 13, 14, 15)]
        + [edges[e] for e in ((8, 2), (10, 2), (12, 0), (12, 1), (14, 0))]
    )
    lower = contract_env(
        [centers[x] for x in (4, 6, 7)]
        + [edges[e] for e in ((4, 0), (4, 1), (6, 0))]
        + factors[-2:]
    )
    coordinates = [dict(zip(map(qkey, CUT), word, strict=True)) for word in WORDS]
    maps = []
    for fixed in coordinates:
        keys, rows, grade = signed_join(
            [upper, lower, centers[5]]
            + [freeze(edges[e], fixed) for e in ((5, 1), (5, 3), (7, 3), (13, 1))]
        )
        assert not keys and set(rows) == {()} and grade == B_BOUNDARY
        maps.append(rows[()])
    assert maps[0] == maps[1] and len(maps[0]) == 36
    digest = sha256(repr(tuple(sorted(maps[0].items()))).encode()).hexdigest()
    assert digest == "0bd2465037650f26612fbda2d4ce965287900d3927f6b83657ccb5d9a1acb52f"

    changing = tuple(
        sorted(k for k in coordinates[0] if coordinates[0][k] != coordinates[1][k])
    )
    assert changing == (qkey((7, 3)), qkey((15, 3)))
    common = {k: v for k, v in coordinates[0].items() if k not in changing}
    first, second = (freeze(centers[x], common) for x in (3, 11))
    fixed_a = [row for x, row in centers.items() if not x & 4 and x not in (3, 11)]
    fixed_a.extend(row for edge, row in edges.items() if edge not in CUT_EDGES)
    fixed_a = [freeze(factor, common) for factor in fixed_a]
    assert not any(set(changing) & set(keys) for keys, _, _ in fixed_a)
    selector = (
        changing,
        {tuple(c[k] for k in changing): {0: (1, 0)} for c in coordinates},
        {},
    )

    expected = defaultdict(lambda: (0, 0))
    for fixed in coordinates:
        keys, rows, _ = indexed_join(
            freeze(first, fixed), freeze(second, fixed), 0, ROW_CAP, PRODUCT_CAP
        )
        for label, row in rows.items():
            assert set(row) == {0}
            re, im = expected[label]
            expected[label] = re + row[0][0], im + row[0][1]
    names, rows, _ = indexed_join(selector, first, 0, ROW_CAP, PRODUCT_CAP)
    names, rows, _ = indexed_join((names, rows, {}), second, 0, ROW_CAP, PRODUCT_CAP)
    order = tuple(names.index(k) for k in keys)
    assert len(rows) == 41_472
    assert {tuple(k[i] for i in order): row[0] for k, row in rows.items()} == {
        k: value for k, value in expected.items() if any(value)
    }

    def prune(factor):
        keys, rows, grade = factor
        position, key = next((i, k) for i, k in enumerate(keys) if k in changing)
        domain = {c[key] for c in coordinates}
        return keys, {k: row for k, row in rows.items() if k[position] in domain}, grade

    print(
        "equal B map",
        len(maps[0]),
        digest,
        "explicit center sum",
        len(rows),
        flush=True,
    )
    return [
        ((), {(): maps[0]}, B_BOUNDARY),
        selector,
        prune(first),
        prune(second),
        *fixed_a,
    ]


def site11_cut(factors):
    check_grades(factors, {})
    pending = {qkey((7, 3)), qkey((15, 3))}
    # The verified pre-cut path closes sites 8 and 10 before this cut.
    for _ in range(12):
        choices = []
        domains = [
            {k: len({v[i] for v in rows}) for i, k in enumerate(keys)}
            for keys, rows, _ in factors
        ]
        for i, j in combinations(range(len(factors)), 2):
            a, b = factors[i], factors[j]
            left, right = set(a[0]), set(b[0])
            if not (left & right or a[2].keys() & b[2].keys()):
                continue
            if left and left <= pending and not a[2] and not ({3, 11} & b[2].keys()):
                continue
            if right and right <= pending and not b[2] and not ({3, 11} & a[2].keys()):
                continue
            grade = Counter(a[2])
            grade.update(b[2])
            assert all(v <= 8 for v in grade.values())
            opened = {x: v for x, v in grade.items() if v < 8}
            domain = domains[i] | domains[j]
            cost = prod(domain[k] for k in left ^ right) * prod(
                comb(8, d) for d in opened.values()
            )
            choices.append(
                (not any(grade[x] == 8 for x in B_BOUNDARY), cost, i, j, grade, opened)
            )
        _, _, i, j, grade, opened = min(choices)
        closed = sum(255 << (8 * x) for x, d in grade.items() if d == 8)
        keys, rows, _ = indexed_join(
            factors[i], factors[j], closed, ROW_CAP, PRODUCT_CAP
        )
        assert rows
        factors[i] = keys, rows, opened
        factors.pop(j)
    check_grades(factors, {})
    incident = [f for f in factors if 11 in f[2]]
    (scalar,) = [f for f in factors if not f[2] and gkey(11, 3) in f[0]]
    assert len(incident) == 3
    rest = [f for f in factors if f is not scalar and 11 not in f[2]]
    assert len(rest) == 4
    return incident, scalar, rest


def prefix_roster(incident, scalar, rest):
    """Exclude unsupported outer keys using paired site-2/9/11 bytes."""
    left, e33, e91 = sorted(incident, key=lambda f: -f[2].get(11, 0))
    if 3 not in e33[2]:
        e33, e91 = e91, e33
    c = scalar
    assert left[2] == {0: 4, 1: 2, 9: 4, 2: 2, 11: 4}
    assert e33[2] == {3: 2, 11: 2} and e91[2] == {9: 2, 11: 2}
    assert [f[2][2] for f in rest if 2 in f[2]] == [6]
    assert [f[2][9] for f in rest if 9 in f[2]] == [2]
    env2 = next(f for f in rest if 2 in f[2])
    env9 = next(f for f in rest if 9 in f[2])

    def byte(m, x):
        return m >> (8 * x) & 255

    masks2 = {255 ^ byte(m, 2) for row in env2[1].values() for m in row}
    masks9 = defaultdict(set)
    ix = [env9[0].index(k) for k in (gkey(9, 0), gkey(9, 1), qkey((9, 1)))]
    for key, row in env9[1].items():
        masks9[tuple(key[i] for i in ix)].update(255 ^ byte(m, 9) for m in row)

    def transfer(f, inner, outer):
        inn = [f[0].index(k) for k in inner]
        out = [f[0].index(k) for k in outer]
        idx = defaultdict(dict)
        for key, row in f[1].items():
            idx[tuple(key[i] for i in inn)][tuple(key[i] for i in out)] = row
        return idx

    left_rows = transfer(left, (gkey(11, 0),), (gkey(9, 0),))
    edge_rows = transfer(e91, (gkey(11, 1), qkey((11, 1))), (gkey(9, 1), qkey((9, 1))))
    third_rows = transfer(e33, (gkey(11, 3), qkey((11, 3))), (gkey(3, 3), qkey((3, 3))))
    all_keys = set()
    projected = set()
    memo = {}
    for key in c[1]:
        k = dict(zip(c[0], key, strict=True))
        q153 = k[qkey((15, 3))]
        left_inner = (k[gkey(11, 0)],)
        edge_inner = k[gkey(11, 1)], k[qkey((11, 1))]
        third_inner = k[gkey(11, 3)], k[qkey((11, 3))]
        for (g90,), lrows in left_rows[left_inner].items():
            for (g91, q91), erows in edge_rows[edge_inner].items():
                mkey = (left_inner, edge_inner, g90, g91, q91)
                if mkey not in memo:
                    er = {(byte(m, 9), byte(m, 11)) for m in erows}
                    allowed = masks9[g90, g91, q91]
                    # Joint necessary support retains shared site9/11 bytes and same L row for site2.
                    lr = {
                        (byte(m, 9), byte(m, 11)) for m in lrows if byte(m, 2) in masks2
                    }
                    memo[mkey] = {
                        255 ^ (a11 | b11)
                        for a9, a11 in lr
                        for b9, b11 in er
                        if not (a9 & b9 or a11 & b11) and a9 | b9 in allowed
                    }
                possible = memo[mkey]
                for (g33, q33), trows in third_rows[third_inner].items():
                    block = (q153, g90, g91, q91, g33, q33)
                    all_keys.add(block)
                    if any(byte(m, 11) in possible for m in trows):
                        projected.add(block)
    digest = sha256(repr(tuple(sorted(projected))).encode()).hexdigest()
    assert digest == "cfeec1137c5b5417171a9e01c263d9a498430927f494478b86b33c1319e8d406"
    counts = Counter(key[:4] for key in projected)
    assert len(all_keys) == 6144 and len(projected) == 2304
    assert len(counts) == 144 and set(counts.values()) == {16}
    return sorted(projected)


def environment(factors):
    """Index each factor by external labels and bytes it must supply alone."""
    incidence = Counter(k for keys, _, _ in factors for k in keys)
    degree = Counter()
    for _, _, d in factors:
        degree.update(d)
    outer = tuple(sorted(k for k, n in incidence.items() if n == 1))
    opened = {x: n for x, n in degree.items() if n < 8}
    outer_set = set(outer)
    indexes = []
    forced_by_factor = [
        tuple(x for x, d in grade.items() if d == degree[x]) for _, _, grade in factors
    ]
    for (keys, rows, d), forced in zip(factors, forced_by_factor, strict=True):
        fixed = sum(255 << (8 * x) for x in forced)
        external = tuple(k for k in keys if k in outer_set)
        ii = tuple(keys.index(k) for k in external)
        tab = defaultdict(list)
        for key, row in rows.items():
            by_mask = defaultdict(dict)
            for m, v in row.items():
                by_mask[m & fixed][m] = v
            for m, sub in by_mask.items():
                tab[tuple(key[i] for i in ii), m].append(
                    (dict(zip(keys, key, strict=True)), sub)
                )
        indexes.append((external, fixed, tab))

    @lru_cache(maxsize=ROW_CAP)
    def query(values, mask):
        known = dict(zip(outer, values, strict=True))
        remaining = mask
        for x, n in degree.items():
            if n == 8:
                remaining |= 255 << (8 * x)
        choices = [
            tab.get((tuple(known[k] for k in external), remaining & fixed), ())
            for external, fixed, tab in indexes
        ]
        if not all(choices):
            return None
        order = sorted(range(len(choices)), key=lambda i: len(choices[i]))
        result = [0, 0]

        def visit(depth, known, used, re, im):
            i = order[depth]
            for other, row in choices[i]:
                if any(known[k] != v for k, v in other.items() if k in known):
                    continue
                if depth + 1 == len(order):
                    comp = remaining ^ used
                    candidates = ((comp, row[comp]),) if comp in row else ()
                else:
                    candidates = row.items()
                for m, (r, t) in candidates:
                    if m & used or m & ~remaining:
                        continue
                    sign = wedge_sign(used, m)
                    v, w = sign * (re * r - im * t), sign * (re * t + im * r)
                    if depth + 1 == len(order):
                        result[0] += v
                        result[1] += w
                    else:
                        visit(depth + 1, known | other, used | m, v, w)

        visit(0, known, 0, 1, 0)
        return tuple(result) if any(result) else None

    return outer, query, opened


def fixture():
    a = (("ext", "int"), {(1, 4): {0x41: (2, 3)}, (1, 5): {0x41: (0, 4)}}, {0: 2})
    b = (("int",), {(4,): {0xBE: (5, -2)}, (6,): {0xBE: (7, 8)}}, {0: 6})
    keys, q, d = environment([a, b])
    assert keys == ("ext",) and d == {}
    sign = wedge_sign(0x41, 0xBE)
    assert q((1,), 0) == (sign * 16, sign * 11) and q((2,), 0) is None
    print("signed environment fixture passed", flush=True)


def prefix_scalar(incident, scalar, env, selector):
    """Contract one disjoint outer-label block without materializing either side."""

    def selected(labels):
        return all(
            k not in labels or labels[k] == v
            for k, v in zip(OUTER[: len(selector)], selector, strict=True)
        )

    def score(order):
        a, b, _ = order
        return (
            -len(set(a[0]) & set(b[0])),
            sum(map(len, a[1].values())) * sum(map(len, b[1].values())),
        )

    left, middle, right = min(permutations(incident), key=score)
    akeys, bkeys, ckeys = left[0], middle[0], right[0]
    shared_ab = tuple(k for k in bkeys if k in akeys)
    shared_c = tuple(k for k in ckeys if k in akeys or k in bkeys)
    scalar_match = tuple(
        k for k in scalar[0] if k in set(akeys) | set(bkeys) | set(ckeys)
    )
    scalar_index = defaultdict(list)
    for key, row in scalar[1].items():
        assert set(row) == {0}
        labels = dict(zip(scalar[0], key, strict=True))
        if selected(labels):
            scalar_index[tuple(labels[k] for k in scalar_match)].append(
                (labels, row[0])
            )

    incidence = Counter(k for keys, _, _ in [*incident, scalar] for k in keys)
    outer, query, boundary = env
    assert set(outer) == {k for k, n in incidence.items() if n == 1} == set(OUTER)
    grade = Counter()
    for _, _, degrees in incident:
        grade.update(degrees)
    assert grade[11] == 8 and all(d <= 8 for d in grade.values())
    closed = sum(255 << (8 * x) for x, d in grade.items() if d == 8)
    assert set(boundary) == {x for x, d in grade.items() if d < 8}
    assert all(boundary[x] + grade[x] == 8 for x in boundary)
    full = sum(255 << (8 * x) for x in boundary)

    def index(factor, shared, retain_mask):
        keys, rows, _ = factor
        table = defaultdict(list)
        for values, row in rows.items():
            labels = dict(zip(keys, values, strict=True))
            if selected(labels):
                match = tuple(labels[k] for k in shared)
                for mask, value in row.items():
                    table[match, mask & closed if retain_mask else 0].append(
                        (labels, mask, preceding_parity(mask), value)
                    )
        return table

    middle_index = index(middle, shared_ab, False)
    right_index = index(right, shared_c, True)
    total_re = total_im = scanned = matched = 0
    for key, row in left[1].items():
        av = dict(zip(akeys, key, strict=True))
        if not selected(av):
            continue
        match_ab = tuple(av[k] for k in shared_ab)
        for a, (ar, ai) in row.items():
            for bv, b, bp, (br, bi) in middle_index.get((match_ab, 0), ()):
                if a & b:
                    continue
                ab = a | b
                prior = av | bv
                match_c = tuple(prior[k] for k in shared_c)
                for cv, c, cp, (cr, ci) in right_index.get(
                    (match_c, closed ^ (ab & closed)), ()
                ):
                    if ab & c:
                        continue
                    labels = prior | cv
                    mask = (ab | c) ^ closed
                    complement = full ^ mask
                    for sv, (sr, si) in scalar_index.get(
                        tuple(labels[k] for k in scalar_match), ()
                    ):
                        scanned += 1
                        if scanned > PRODUCT_CAP:
                            return "scan-cap", scanned, matched, None, None
                        merged = labels | sv
                        target = query(tuple(merged[k] for k in outer), complement)
                        if target is None:
                            continue
                        matched += 1
                        if matched > PRODUCT_CAP:
                            return "match-cap", scanned, matched, None, None
                        sign = 1 - 2 * (
                            (
                                (a & bp).bit_count()
                                + (ab & cp).bit_count()
                                + (mask & preceding_parity(complement)).bit_count()
                            )
                            & 1
                        )
                        re, im = ar * br - ai * bi, ar * bi + ai * br
                        re, im = re * cr - im * ci, re * ci + im * cr
                        re, im = re * sr - im * si, re * si + im * sr
                        er, ei = target
                        total_re += sign * (re * er - im * ei)
                        total_im += sign * (re * ei + im * er)
    return "exact", scanned, matched, total_re, total_im


def multiple_masks_fixture():
    """Both masks of a left label must use the same middle-join key."""
    left_middle = ("test", "left-middle")
    right_scalar = ("test", "right-scalar")
    shift = 8 * 11
    first = (
        (left_middle,),
        {(7,): {0x0F << shift: (2, 0), 0x33 << shift: (3, 0)}},
        {11: 4},
    )
    middle = (
        (left_middle,),
        {(7,): {0x30 << shift: (5, 0), 0x0C << shift: (7, 0)}},
        {11: 2},
    )
    right = ((right_scalar,), {(9,): {0xC0 << shift: (11, 0)}}, {11: 2})
    selector = (5, (0, 0), (1,), 5, (0,), 0)
    scalar = ((*OUTER, right_scalar), {(*selector, 9): {0: (1, 0)}}, {})
    env = environment([(OUTER, {selector: {0: (1, 0)}}, {})])
    expected = 11 * (10 * wedge_sign(0x0F, 0x30) + 21 * wedge_sign(0x33, 0x0C))
    assert prefix_scalar((first, middle, right), scalar, env, selector) == (
        "exact",
        2,
        2,
        expected,
        0,
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("start", type=int)
    parser.add_argument("stop", type=int)
    parser.add_argument(
        "--leaf", type=int, help="run only this local leaf index for a single prefix"
    )
    args = parser.parse_args()
    if not 0 <= args.start < args.stop <= 144:
        parser.error("expected 0 <= start < stop <= 144")
    if args.leaf is not None and (
        args.stop != args.start + 1 or not 0 <= args.leaf < 16
    ):
        parser.error("--leaf requires one prefix and an index from 0 through 15")
    fixture()
    multiple_masks_fixture()
    incident, scalar, rest = site11_cut(grouped_factors())
    leaves = prefix_roster(incident, scalar, rest)
    env = environment(rest)
    print("roster", len(leaves), "leaves, 16 per prefix, divisor", DIVISOR, flush=True)
    for idx in range(args.start, args.stop):
        offset = idx * 16
        indices = [args.leaf] if args.leaf is not None else range(16)
        for leaf_idx in indices:
            key = leaves[offset + leaf_idx]
            status, scanned, matched, re, im = prefix_scalar(incident, scalar, env, key)
            print(
                json.dumps(
                    dict(
                        id=idx,
                        leaf=leaf_idx,
                        key=key,
                        status=status,
                        scanned=scanned,
                        matches=matched,
                        numerator_real=re,
                        numerator_imag=im,
                    )
                ),
                flush=True,
            )


if __name__ == "__main__":
    main()
