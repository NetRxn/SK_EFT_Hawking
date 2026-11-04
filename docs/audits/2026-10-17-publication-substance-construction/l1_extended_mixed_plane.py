"""Mixed-plane fourth-power sector with peelable curvature links on 2^4."""
from collections import Counter, defaultdict
from fractions import Fraction
from functools import cache
from itertools import combinations, product
from math import factorial, prod

from l1_direct_b_haar import add
from l1_extended_opposed import staged_center
from l1_extended_opposed_source import PAIRS as GAMMA_PAIRS, modified_center, source_frames, summed_fourth
from l1_reduced_wedge_reference import wedge_sign

AXES = tuple(range(4))
PAIRS = tuple(combinations(AXES, 2))
EVEN = tuple(x for x in range(16) if x.bit_count() % 2 == 0)


def patterns():
    degree = Counter()
    chosen = {}

    def visit(i):
        if i == len(EVEN):
            yield dict(chosen)
            return
        x = EVEN[i]
        for a, b in PAIRS:
            y, z = x ^ (1 << a), x ^ (1 << b)
            if degree[y] == 2 or degree[z] == 2:
                continue
            chosen[x] = (a, b)
            degree[y] += 1
            degree[z] += 1
            yield from visit(i + 1)
            degree[y] -= 1
            degree[z] -= 1

    yield from visit(0)


def peelable(pattern):
    faces = {}
    protected = {(site, a) for x, axes in pattern.items() for a in axes
                 for site in (x, x ^ (1 << a))}
    for x, frame in pattern.items():
        k, l = (a for a in AXES if a not in frame)
        faces[x] = ((x, k), (x ^ (1 << k), l), (x ^ (1 << l), k), (x, l))
    while faces:
        counts = Counter(e for face in faces.values() for e in face)
        x = next((x for x, face in faces.items() if any(counts[e] == 1 and e not in protected for e in face)), None)
        if x is None:
            return False
        del faces[x]
    return True


def cycles(pattern):
    incidence = defaultdict(list)
    for x, axes in pattern.items():
        for a in axes:
            incidence[x ^ (1 << a)].append((x, a))
    remaining = set(pattern)
    while remaining:
        start = min(remaining)
        x = start
        incoming, _ = pattern[x]
        cycle = []
        while x in remaining:
            remaining.remove(x)
            outgoing = next(a for a in pattern[x] if a != incoming)
            cycle.append((pattern[x], incoming))
            y = x ^ (1 << outgoing)
            x, incoming = next((z, a) for z, a in incidence[y] if z != x)
        assert x == start and incoming == cycle[0][1]
        yield cycle


def center_transfers(poly):
    transfers = [defaultdict(dict), defaultdict(dict)]
    for mask, value in poly.items():
        assert mask >> 24 == 0 and mask & 255 == 255 and value.is_ground
        a, b = (mask >> 8) & 255, (mask >> 16) & 255
        assert a.bit_count() == b.bit_count() == 4 and not value.const().y
        for transfer, incoming, outgoing in ((transfers[0], a, b), (transfers[1], b, a)):
            transfer[255 ^ incoming][outgoing] = (
                wedge_sign(255 ^ incoming, incoming) * int(value.const().x))
    return transfers


def trace(matrices):
    total = 0
    for initial in matrices[0]:
        row = {initial: 1}
        for matrix in matrices:
            next_row = Counter()
            for a, c in row.items():
                for b, v in matrix.get(a, {}).items():
                    next_row[b] += c * v
            row = next_row
        total += row[initial]
    return total


def source_transfers():
    tables = [[source_frames(direction, anchor) for anchor in range(2)]
              for direction in range(2)]
    result = {}
    for u, v in product(range(2), repeat=2):
        a, b = ({p: add(*(maps[endpoint][p] for maps in per_edge)) for p in GAMMA_PAIRS}
                for per_edge, endpoint in zip(tables, (u, v), strict=True))
        result[(u << 2) | (v << 3)] = center_transfers(modified_center(a, b))
    return result


def main():
    poly, _ = staged_center(summed_fourth(0), summed_fourth(1))
    transfers = center_transfers(poly)
    source = source_transfers()

    @cache
    def cycle_value(orientations, changed=-1, offset=0):
        matrices = [(source[offset] if i == changed else transfers)[orient]
                    for i, orient in enumerate(orientations)]
        return trace(matrices)
    denominator = 48 * 96**4 * 8**8 * factorial(4)
    # One opposite-center layer from the homogeneous replay.
    homogeneous_layer = cycle_value((0, 1))
    assert Fraction(homogeneous_layer, denominator**2)**4 == Fraction(
        9982511481025756988525390625, 295147905179352825856)
    for offset in source:
        changed = sum(cycle_value((0, 1), j, offset) for j in range(2))
        assert Fraction(-96 * changed * homogeneous_layer**3, denominator**8) == Fraction(
            -151675751259254608154296875, 576460752303423488)
    counts = Counter()
    total = 0
    numerator = Counter()
    for pattern in patterns():
        independent = peelable(pattern)
        counts[independent] += 1
        if independent:
            components = list(cycles(pattern))
            orders = [tuple(axes.index(incoming) for axes, incoming in cycle)
                      for cycle in components]
            factors = list(map(cycle_value, orders))
            total += prod(factors)
            for i, cycle in enumerate(components):
                other = prod(factors[:i] + factors[i+1:])
                for j, (axes, _) in enumerate(cycle):
                    if axes == (2, 3):
                        for offset in source:
                            numerator[offset] += other * cycle_value(orders[i], j, offset)
    assert sum(counts.values()) == 2970
    print("patterns by curvature peelability", dict(counts))
    print("peelable fourth-power normalization, both checkerboards",
          Fraction(2 * total, denominator**8))
    # Two checkerboards, two source orders, opposite axis signs,
    # and a surviving 2! at the modified center in place of 4!.
    values = {offset: Fraction(-48 * value, denominator**8)
              for offset, value in sorted(numerator.items())}
    print("peelable fourth-power numerator by offset", values)
    print("peelable fourth-power numerator", sum(values.values()))


if __name__ == "__main__":
    main()
