"""Replay selected A-group leaves using two independently closed factor maps."""

import argparse
from collections import Counter
from itertools import combinations
import json
from math import comb, prod
from time import monotonic

from l1_extended_offset_witness_k2 import indexed_join
from l1_unpaired_A_group import (
    DIVISOR,
    OUTER,
    environment,
    grouped_factors,
    prefix_roster,
    prefix_scalar,
    site11_cut,
)
from l1_unpaired_signed_slice import PRODUCT_CAP, ROW_CAP, freeze


def materialize(factors):
    """Close internal labels and full site volumes, leaving the exterior boundary."""
    factors = list(factors)
    while len(factors) > 1:
        choices = []
        for i, j in combinations(range(len(factors)), 2):
            left, right = factors[i], factors[j]
            axes = set(left[0]) ^ set(right[0])
            grade = Counter(left[2])
            grade.update(right[2])
            assert all(n <= 8 for n in grade.values())
            opened = {x: n for x, n in grade.items() if n < 8}
            cost = prod(comb(8, n) for n in opened.values()) * 10 ** len(axes)
            choices.append((cost, i, j, grade, opened))
        _, i, j, grade, opened = min(choices)
        closed = sum(255 << (8 * x) for x, n in grade.items() if n == 8)
        keys, rows, _ = indexed_join(
            factors[i], factors[j], closed, ROW_CAP, PRODUCT_CAP
        )
        factors[i] = keys, rows, opened
        factors.pop(j)
    return factors[0]


def pairwise_leaf(incident, scalar, rest, labels):
    fixed = dict(zip(OUTER, labels, strict=True))
    left = materialize(freeze(f, fixed) for f in [*incident, scalar])
    right = materialize(freeze(f, fixed) for f in rest)
    assert not left[0] and not right[0]
    assert left[1].keys() <= {()} and right[1].keys() <= {()}
    assert left[2].keys() == right[2].keys()
    assert all(left[2][x] + right[2][x] == 8 for x in left[2])
    full = sum(255 << (8 * x) for x in left[2])
    rhs = right[1].get((), {})
    total_re = total_im = pairs = 0
    for mask, (re, im) in left[1].get((), {}).items():
        complement = full ^ mask
        if complement not in rhs:
            continue
        other_re, other_im = rhs[complement]
        pairs += 1
        if pairs > PRODUCT_CAP:
            raise RuntimeError("final complement products exceed cap")
        inversions = sum(
            (complement & ((1 << i) - 1)).bit_count()
            for i in range(mask.bit_length())
            if mask >> i & 1
        )
        sign = (-1) ** inversions
        total_re += sign * (re * other_re - im * other_im)
        total_im += sign * (re * other_im + im * other_re)
    return total_re, total_im, pairs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("start", type=int, help="first four-label prefix")
    parser.add_argument("stop", type=int, help="exclusive final four-label prefix")
    parser.add_argument(
        "--cross-check",
        action="store_true",
        help="compare each raw result with the query replay",
    )
    args = parser.parse_args()
    if not 0 <= args.start < args.stop <= 144:
        parser.error("expected 0 <= start < stop <= 144")

    incident, scalar, rest = site11_cut(grouped_factors())
    leaves = prefix_roster(incident, scalar, rest)
    oracle = environment(rest) if args.cross_check else None
    print("roster", len(leaves), "leaves, 16 per prefix, divisor", DIVISOR, flush=True)
    failures = 0
    for i in range(16 * args.start, 16 * args.stop):
        key = leaves[i]
        start = monotonic()
        row = dict(index=i, id=i // 16, leaf=i % 16, key=key)
        try:
            re, im, pairs = pairwise_leaf(incident, scalar, rest, key)
        except RuntimeError as error:
            row.update(status="join-cap", detail=str(error))
            failures += 1
        else:
            if oracle is not None:
                status, _, _, expected_re, expected_im = prefix_scalar(
                    incident, scalar, oracle, key
                )
                assert status == "exact" and (re, im) == (expected_re, expected_im), (
                    i,
                    key,
                )
            row.update(
                status="exact", numerator_real=re, numerator_imag=im, pairs=pairs
            )
        row.update(seconds=round(monotonic() - start, 3))
        print(json.dumps(row), flush=True)
    if failures:
        raise SystemExit(2)


if __name__ == "__main__":
    main()
