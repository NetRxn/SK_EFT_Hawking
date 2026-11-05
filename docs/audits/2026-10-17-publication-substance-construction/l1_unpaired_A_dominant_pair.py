"""Replay the guarded dominant-B pair at support indices 4776 and 17672."""

import argparse
from collections import Counter
from fractions import Fraction
from hashlib import sha256
import json

from l1_unpaired_A_group import projected_outer_keys, site11_cut
from l1_unpaired_A_pairwise import pairwise_leaf
from l1_unpaired_B_census import BEvaluator, B_BOUNDARY, exact_primitive
from l1_unpaired_offset_factors import DIVISOR, prepare, qkey
from l1_unpaired_signed_slice import CUT_EDGES, freeze
from l1_unpaired_source_support import CUT

WORDS = ((1, 2, 5, 2, 6, 1, 7), (2, 1, 5, 2, 6, 1, 7))
EXACT_B = (
    "f0d4bd83cdbda198f7052ebf732a87b4a8bd98b098c23e9b877911e7cc22aa16",
    "aceaad96c1c178c7643b4ce6a8aac2d3ac3a46ca4ff42403f6c311138d5683cb",
)
PRIMITIVE_B = "2300ae45fae9964a814091804bfc5e81817b8d972c7b40b927e0c73e984df0e4"
ROSTER = "489f340dc12c5e1935e05b842b46325bb2573a14fa575066835b76b6e2b94cf4"


def dominant_pair():
    evaluator = BEvaluator(prepare())
    exact = []
    for word, digest in zip(WORDS, EXACT_B, strict=True):
        status, rows = evaluator.evaluate(word)
        assert status == "B-nonzero" and rows == evaluator.direct(word)
        result = exact_primitive(rows)
        assert sha256(repr(result[0]).encode()).hexdigest() == digest
        exact.append(result)

    _, primitive, scale = exact[1]
    assert len(primitive) == 208 and exact[0][1:] == (primitive, -scale)
    assert sha256(repr(primitive).encode()).hexdigest() == PRIMITIVE_B
    coordinates = [dict(zip(map(qkey, CUT), word, strict=True)) for word in WORDS]
    changing = {k for k, v in coordinates[0].items() if coordinates[1][k] != v}
    retained = (qkey((7, 3)), qkey((15, 3)))
    assert changing == set(map(qkey, CUT[:2]))
    assert all(coordinates[0][k] == coordinates[1][k] for k in retained)
    fixed = {
        k: v for k, v in coordinates[0].items() if k not in changing | set(retained)
    }
    a_centers = {x: f for x, f in evaluator.centers.items() if not x & 4}
    a_edges = [f for e, f in evaluator.edges.items() if e not in CUT_EDGES]
    assert [x for x, f in a_centers.items() if changing & set(f[0])] == [1]
    assert all(not (changing & set(f[0])) for f in a_edges)

    weighted = Counter()
    center_keys = None
    for coord, sign in zip(coordinates, (-1, 1), strict=True):
        names, rows, degree = freeze(a_centers[1], coord)
        assert not degree and (center_keys is None or names == center_keys)
        center_keys = names
        assert all(set(row) == {0} and row[0][1] == 0 for row in rows.values())
        weighted.update({key: sign * row[0][0] for key, row in rows.items()})
    center1 = center_keys, {key: {0: (v, 0)} for key, v in weighted.items() if v}, {}
    assert Counter(row[0][0] for row in center1[1].values()) == {4: 12, -4: 12}

    def retain_selector(factor):
        names, rows, degree = freeze(factor, fixed)
        ((position, label),) = [(i, k) for i, k in enumerate(names) if k in retained]
        return (
            names,
            {k: v for k, v in rows.items() if k[position] == coordinates[0][label]},
            degree,
        )

    selector = retained, {tuple(coordinates[0][k] for k in retained): {0: (1, 0)}}, {}
    factors = [((), {(): dict(primitive)}, B_BOUNDARY), selector]
    factors.extend(retain_selector(a_centers[x]) for x in (3, 11))
    factors.extend(
        center1 if x == 1 else freeze(f, fixed)
        for x, f in a_centers.items()
        if x not in (3, 11)
    )
    factors.extend(a_edges)
    assert len(factors) == 20
    return factors, scale


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("start", type=int)
    parser.add_argument("stop", type=int)
    args = parser.parse_args()
    if not 0 <= args.start < args.stop <= 72:
        parser.error("expected 0 <= start < stop <= 72")

    factors, scale = dominant_pair()
    incident, scalar, rest = site11_cut(factors)
    all_keys, projected = projected_outer_keys(incident, scalar, rest)
    assert len(all_keys) == 3072
    leaves = sorted(projected)
    assert len(leaves) == 1152 and set(Counter(k[:4] for k in leaves).values()) == {16}
    assert sha256(repr(tuple(leaves)).encode()).hexdigest() == ROSTER
    print(
        "dominant pair",
        WORDS,
        "leaves",
        len(leaves),
        "scale",
        scale,
        "divisor",
        DIVISOR,
        flush=True,
    )
    total_re = total_im = failures = 0
    for i in range(16 * args.start, 16 * args.stop):
        key = leaves[i]
        row = dict(index=i, id=i // 16, leaf=i % 16, key=key)
        try:
            re, im, pairs = pairwise_leaf(incident, scalar, rest, key)
        except RuntimeError as error:
            row.update(status="join-cap", detail=str(error))
            failures += 1
        else:
            total_re += re
            total_im += im
            row.update(
                status="exact", numerator_real=re, numerator_imag=im, pairs=pairs
            )
        print(json.dumps(row), flush=True)
    print(
        "available subtotal",
        Fraction(total_re * scale, DIVISOR),
        Fraction(total_im * scale, DIVISOR),
        flush=True,
    )
    if failures:
        raise SystemExit(2)


if __name__ == "__main__":
    main()
