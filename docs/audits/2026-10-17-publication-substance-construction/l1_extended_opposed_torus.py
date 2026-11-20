"""Exact four-face curvature channels for the constant opposed layer patterns."""
from collections import Counter
from fractions import Fraction
from functools import cache, partial
from itertools import product
from math import factorial, prod

from l1_direct_b_haar import add, haar_moment
from l1_extended_opposed import L, curvature, staged_center
from l1_extended_opposed_source import PAIRS, close, modified_center, source_frames, summed_fourth

CHARACTERS = ((1,), (-1, 4), (1, -12, 16))
SCALE = 720
CHANNELS = tuple((a, b) for a, b in product(range(3), repeat=2) if a + b <= 2)


@cache
def character_moment(spin, counts):
    return sum(c * haar_moment((2*k, *counts))
               for k, c in enumerate(CHARACTERS[spin]))


@cache
def moment(channel, pairs):
    total = Fraction()
    for term in product(*(L[p] for p in pairs)):
        counts = Counter(i for i, _ in term)
        total += (character_moment(channel[0], tuple(counts[i] for i in range(3)))
                  * character_moment(channel[1], tuple(counts[i] for i in range(3, 6)))
                  * prod(v for _, v in term))
    total *= SCALE
    assert total.denominator == 1
    if channel == (0, 0):
        assert total == (SCALE // 48) * curvature(pairs)
    return int(total)


def main():
    first, second = (summed_fourth(direction) for direction in range(2))
    centers = {channel: staged_center(first, second, partial(moment, channel))[0]
               for channel in CHANNELS}
    sources = [[source_frames(direction, anchor) for anchor in range(2)]
               for direction in range(2)]
    denominator = SCALE * 96**4 * 8**8
    torus_weight = {c: Fraction(1, prod(2*j + 1 for j in c)**4) for c in CHANNELS}
    layer = {(a, b): Fraction(close(centers[a], centers[b]),
                              denominator**2 * factorial(4)**2)
             for a, b in product(CHANNELS, repeat=2)}
    trivial = (0, 0)
    independent_norm = layer[trivial, trivial]**4
    assert independent_norm == Fraction(9982511481025756988525390625, 295147905179352825856)
    normalization = sum(torus_weight[a] * torus_weight[b] * value**4
                        for (a, b), value in layer.items())
    print("constant-pattern normalization", normalization, flush=True)
    numerator = {}
    for u, v in product(range(2), repeat=2):
        first_source, second_source = (
            {p: add(*(maps[endpoint][p] for maps in tables)) for p in PAIRS}
            for tables, endpoint in zip(sources, (u, v), strict=True))
        subtotal = Fraction()
        for a in CHANNELS:
            if sum(a) > 1:
                continue
            changed = modified_center(first_source, second_source, partial(moment, a))
            for b in CHANNELS:
                # Four layers, two affected centers, two ordered sources.
                changed_layer = Fraction(-16 * close(changed, centers[b]),
                                         denominator**2 * factorial(2) * factorial(4))
                contribution = layer[a, b]**3 * changed_layer
                if a == b == trivial:
                    assert contribution == Fraction(
                        -151675751259254608154296875, 576460752303423488)
                subtotal += torus_weight[a] * torus_weight[b] * contribution
        numerator[(u << 2) | (v << 3)] = subtotal
    print("constant-pattern numerator by offset", numerator)
    print("constant-pattern numerator", sum(numerator.values()))
    print("constant-pattern trivial-channel normalization", independent_norm)
    print("homogeneous opposed normalization", 6 * (14 * independent_norm + 2 * normalization))
    independent_numerator = Fraction(-151675751259254608154296875, 144115188075855872)
    print("homogeneous opposed numerator", 14 * independent_numerator + 2 * sum(numerator.values()))


if __name__ == "__main__":
    main()
