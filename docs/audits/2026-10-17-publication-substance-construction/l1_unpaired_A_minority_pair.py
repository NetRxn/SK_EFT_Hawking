"""Replay one exact same-B minority pair differing only at q151."""

import argparse
from collections import Counter
from fractions import Fraction
from hashlib import sha256
import json

from l1_unpaired_A_group import projected_outer_keys, site11_cut
from l1_unpaired_A_pairwise import pairwise_leaf
from l1_unpaired_B_census import B_BOUNDARY, BEvaluator, exact_primitive
from l1_unpaired_offset_factors import DIVISOR, prepare, qkey
from l1_unpaired_signed_slice import CUT_EDGES, freeze
from l1_unpaired_source_support import CUT

MINORITY = frozenset(
    (
        "ca2595302d1af707369c0351c4bcd3e969de471d4675e128486e9792ac1e08ec",
        "9feca1434834c83837f644c1975c480bcb110c9f060e7dd783de7fe4c83eefcc",
        "36908a28dcbcb8586b800dcba8e814f10dbed0ee09a517240a1d4afb46b90408",
        "cb82bec729d271d49339fbc6c75f3d8d6debaf137758b819b63605084ff1fa7a",
        "f88b526d099b8a0233536103d9c7c46954afafdfc2e23b5d6eaddcfc9fc59e02",
        "39c8163e16292027ba85d28ee5ab608ffe6b0e82b1dee9de8ebfb15143922d12",
    )
)


def assemble(words, exact_digest):
    assert len(words) == 2 and all(len(w) == len(CUT) for w in words)
    assert words[0][:5] + words[0][6:] == words[1][:5] + words[1][6:]
    assert {w[5] for w in words} == {0, 4}
    evaluator = BEvaluator(prepare())
    maps = []
    for word in words:
        status, rows = evaluator.evaluate(word)
        assert status == "B-nonzero" and rows == evaluator.direct(word)
        maps.append(rows)
    assert maps[0] == maps[1] and len(maps[0]) in (36, 72, 162)
    exact, primitive, scale = exact_primitive(maps[0])
    assert sha256(repr(exact).encode()).hexdigest() == exact_digest
    primitive_digest = sha256(repr(primitive).encode()).hexdigest()
    assert primitive_digest in MINORITY

    coords = [dict(zip(map(qkey, CUT), word, strict=True)) for word in words]
    differing = {k for k, v in coords[0].items() if coords[1][k] != v}
    assert differing == {qkey((15, 1))}
    retained = (qkey((7, 3)), qkey((15, 3)))
    fixed = {k: v for k, v in coords[0].items() if k not in differing | set(retained)}
    centers = {x: f for x, f in evaluator.centers.items() if not x & 4}
    edges = [f for e, f in evaluator.edges.items() if e not in CUT_EDGES]
    assert [x for x, f in centers.items() if differing & set(f[0])] == [11]
    assert all(not set(coords[0]) & set(f[0]) for f in edges)
    c11 = Counter()
    c11_keys = None
    for coord in coords:
        keys, rows, grade = freeze(
            centers[11], fixed | {k: coord[k] for k in differing}
        )
        assert not grade and (c11_keys is None or c11_keys == keys)
        c11_keys = keys
        assert all(set(row) == {0} and row[0][1] == 0 for row in rows.values())
        c11.update({key: row[0][0] for key, row in rows.items()})
    c11_factor = c11_keys, {k: {0: (v, 0)} for k, v in c11.items() if v}, {}

    def retain(factor):
        names, rows, degree = factor
        ((i, label),) = [(i, k) for i, k in enumerate(names) if k in retained]
        return (
            names,
            {k: row for k, row in rows.items() if k[i] == coords[0][label]},
            degree,
        )

    c11_factor = retain(c11_factor)
    assert len(c11_factor[1]) == 288
    factors = [
        ((), {(): dict(primitive)}, B_BOUNDARY),
        (retained, {tuple(coords[0][k] for k in retained): {0: (1, 0)}}, {}),
    ]
    factors.extend([retain(freeze(centers[3], fixed)), c11_factor])
    factors.extend(freeze(f, fixed) for x, f in centers.items() if x not in (3, 11))
    factors.extend(edges)
    print(
        "equal B maps",
        len(exact),
        exact_digest,
        primitive_digest,
        "scale",
        scale,
        "C11",
        len(c11_factor[1]),
        flush=True,
    )
    return factors, scale


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--first", type=int, nargs=7, required=True)
    parser.add_argument("--second", type=int, nargs=7, required=True)
    parser.add_argument("--exact-b-sha256", required=True)
    parser.add_argument(
        "--roster-sha256", help="verify a previously measured support roster"
    )
    parser.add_argument("start", type=int, help="first projected leaf")
    parser.add_argument(
        "stop", type=int, help="exclusive end, equal to start for roster census only"
    )
    args = parser.parse_args()
    words = tuple(map(tuple, (args.first, args.second)))
    print(
        "minority pair", words, "requested range", (args.start, args.stop), flush=True
    )
    factors, scale = assemble(words, args.exact_b_sha256)
    incident, scalar, rest = site11_cut(factors)
    outer, projected = projected_outer_keys(incident, scalar, rest)
    leaves = sorted(projected)
    roster_digest = sha256(repr(tuple(leaves)).encode()).hexdigest()
    if args.roster_sha256 is not None:
        assert roster_digest == args.roster_sha256
    if not 0 <= args.start <= args.stop <= len(leaves):
        parser.error("expected 0 <= start <= stop <= number of projected leaves")
    print(
        "roster", len(outer), len(leaves), roster_digest, "divisor", DIVISOR, flush=True
    )
    total_re = total_im = exact = 0
    for index in range(args.start, args.stop):
        key = leaves[index]
        try:
            re, im, pairs = pairwise_leaf(incident, scalar, rest, key)
        except RuntimeError as error:
            record = dict(index=index, key=key, status="join-cap", detail=str(error))
        else:
            exact += 1
            total_re += re
            total_im += im
            record = dict(
                index=index,
                key=key,
                status="exact",
                numerator_real=re,
                numerator_imag=im,
                pairs=pairs,
            )
        print(json.dumps(record), flush=True)
    print(
        "range",
        args.start,
        args.stop,
        "exact",
        exact,
        "available subtotal",
        Fraction(total_re * scale, DIVISOR),
        Fraction(total_im * scale, DIVISOR),
        flush=True,
    )
    if exact != args.stop - args.start:
        raise SystemExit(2)


if __name__ == "__main__":
    main()
