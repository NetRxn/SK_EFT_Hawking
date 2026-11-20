"""Exact B-side maps and low-prefix roster for the selected unpaired word."""

from ast import literal_eval
from collections import Counter
from functools import lru_cache
from itertools import combinations, product
from math import comb, gcd, prod
import re

from l1_extended_offset_witness_k2 import indexed_join
from l1_unpaired_offset_factors import FRAME_PLANES, SLOTS, gkey, qkey
from l1_unpaired_signed_slice import PRODUCT_CAP, ROW_CAP, freeze
from l1_unpaired_source_support import ALL, CUT, NONSCALE, surviving_tuples
from l1_unpaired_upper_support import contract_env

B_BOUNDARY = {0: 2, 1: 2, 8: 2, 10: 2}
LOW_BOUNDARY = {0: 2, 1: 2, 5: 6, 15: 2}
RIGHT_BOUNDARY = {5: 2, 8: 2, 10: 2, 15: 6}
LOW_EDGES = ((5, 1), (7, 1), (7, 3), (15, 3))
LOW_PREFIXES = frozenset(product(NONSCALE, ALL, ALL, ALL))
LOW_ROW = re.compile(r"^low (\([^)]*\)) (exact zero|nonzero low map|support empty) candidates (\d+)(?: |$)")


def signed_join(factors):
    """Join open factors, preserving Gaussian signs and exact-empty status.

    A cap from indexed_join propagates as RuntimeError.
    """
    factors = list(factors)
    if any(not rows for _, rows, _ in factors):
        return (), {}, {}
    while len(factors) > 1:
        choices = []
        for i, j in combinations(range(len(factors)), 2):
            left, right = factors[i], factors[j]
            left_keys, right_keys = set(left[0]), set(right[0])
            if not (left_keys & right_keys or left[2].keys() & right[2].keys()):
                continue
            grade = Counter(left[2])
            grade.update(right[2])
            assert all(d <= 8 for d in grade.values())
            opened = {site: d for site, d in grade.items() if d < 8}
            cost = 10**len(left_keys ^ right_keys) * prod(comb(8, d) for d in opened.values())
            choices.append((cost, i, j, grade, opened))
        _, i, j, grade, opened = min(choices)
        closed = sum(255 << (8 * site) for site, d in grade.items() if d == 8)
        keys, rows, _ = indexed_join(factors[i], factors[j], closed, ROW_CAP, PRODUCT_CAP)
        if not rows:
            return (), {}, {}
        factors[i] = keys, rows, opened
        factors.pop(j)
    return factors[0]


def low_prefix(word):
    return tuple(word[i] for i in (0, 2, 3, 6))


def read_low_roster(receipt_paths):
    """Read exact terminal low-prefix rows from completed replay receipts."""
    roster = {}
    for path in receipt_paths:
        for line in path.read_text().splitlines():
            if not line.startswith("low "):
                continue
            match = LOW_ROW.match(line)
            if not match:
                raise ValueError(f"unresolved or invalid low-prefix receipt: {line}")
            prefix_text, state, count_text = match.groups()
            prefix, count = literal_eval(prefix_text), int(count_text)
            if prefix not in LOW_PREFIXES or prefix in roster:
                raise ValueError(f"unexpected or duplicate low prefix: {prefix}")
            if state == "support empty" and count:
                raise ValueError(f"nonempty candidate count for support-empty prefix: {prefix}")
            roster[prefix] = state, count
    if roster.keys() != LOW_PREFIXES:
        raise ValueError("low-prefix roster does not cover the guarded domain")
    assert Counter(state for state, _ in roster.values()) == {
        "nonzero low map": 816, "exact zero": 1436, "support empty": 820,
    }
    return roster


def indexed_roster(factors, low_roster):
    """Validate low-prefix counts, then index retained tuples in replay order."""
    counts = Counter()
    retained = []
    for word in surviving_tuples(factors):
        prefix = low_prefix(word)
        counts[prefix] += 1
        if low_roster[prefix][0] == "nonzero low map":
            retained.append(word)
    if any(counts[prefix] != count for prefix, (_, count) in low_roster.items()):
        raise ValueError("low-prefix candidate counts do not match projected support")
    assert sum(counts.values()) == 124_416 and len(retained) == len(set(retained)) == 77_472
    return tuple(retained)


def exact_primitive(rows):
    """Return canonical exact rows, primitive rows, and signed integer scale."""
    exact = tuple(sorted(rows.items()))
    scale = 0
    for _, (re, im) in exact:
        scale = gcd(scale, gcd(re, im))
    assert scale
    if next(value for value in exact[0][1] if value) < 0:
        scale = -scale
    return exact, tuple((mask, (re // scale, im // scale)) for mask, (re, im) in exact), scale


class BEvaluator:
    """Evaluate selected B maps with bounded low and right caches."""

    def __init__(self, factors):
        self.centers = dict(zip(sorted(FRAME_PLANES), factors[:15], strict=True))
        self.edges = dict(zip(sorted(SLOTS), factors[15:-2], strict=True))
        self.upper = contract_env([self.centers[x] for x in (12, 13, 14, 15)]
                                  + [self.edges[e] for e in ((8, 2), (10, 2), (12, 0), (12, 1), (14, 0))])
        self.lower = contract_env([self.centers[x] for x in (4, 6, 7)]
                                  + [self.edges[e] for e in ((4, 0), (4, 1), (6, 0))]
                                  + factors[-2:])
        assert self.lower[2] == {0: 2, 1: 2, 5: 4, 7: 4}

    @lru_cache(maxsize=16)
    def low(self, prefix):
        coordinates = dict(zip(map(qkey, LOW_EDGES), prefix, strict=True))
        result = signed_join([self.lower, freeze(self.edges[5, 1], coordinates),
                              freeze(self.edges[7, 3], coordinates)])
        if result[1]:
            assert result[0] == (gkey(5, 1),) and result[2] == LOW_BOUNDARY
        return result

    @lru_cache(maxsize=8)
    def high(self, q151):
        return signed_join([self.upper, freeze(self.edges[13, 1], {qkey((15, 1)): q151})])

    @lru_cache(maxsize=48)
    def middle(self, q53, q133):
        coordinates = {qkey((5, 3)): q53, qkey((13, 3)): q133}
        return signed_join([self.centers[5], freeze(self.edges[5, 3], coordinates)])

    @lru_cache(maxsize=24)
    def right(self, q53, q133, q151):
        result = signed_join([self.high(q151), self.middle(q53, q133)])
        if result[1]:
            assert result[0] == (gkey(5, 1),) and result[2] == RIGHT_BOUNDARY
        return result

    @staticmethod
    def boundary_map(result):
        keys, rows, grade = result
        if not rows:
            return {}
        assert not keys and grade == B_BOUNDARY and rows.keys() == {()}
        return rows[()]

    def direct(self, word):
        coordinates = dict(zip(map(qkey, CUT), word, strict=True))
        factors = [self.upper, self.lower, self.centers[5]]
        factors.extend(freeze(self.edges[e], coordinates)
                       for e in ((5, 1), (5, 3), (7, 3), (13, 1)))
        return self.boundary_map(signed_join(factors))

    def evaluate(self, word):
        """Return an exact status and map, or a cap status and its diagnostic."""
        try:
            low = self.low(low_prefix(word))
            right = self.right(word[1], word[4], word[5])
            rows = self.boundary_map(signed_join([low, right]))
        except RuntimeError as error:
            return "B-cap", str(error)
        return ("B-nonzero" if rows else "B-zero"), rows
