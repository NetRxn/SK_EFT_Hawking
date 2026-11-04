"""Two-source replacements of the disjoint opposed 16-site normalization word."""
from collections import Counter
from fractions import Fraction
from itertools import combinations_with_replacement, product
from math import factorial

from l1_direct_b_haar import R, add, bilinear, diag, gamma, scale, wedge
from l1_extended_opposed import center, curvature, geometry
from l1_normalization_disjoint_sector import adj, quat
from l1_normalization_opposed_fourth import nodes


def frame(direction, reverse, left, right):
    x, y = 0, 1 << direction
    if reverse:
        x, y = y, x
    u = diag(quat(left), quat(right))
    ud = diag(quat(adj(left)), quat(adj(right)))
    return [add(bilinear(g * ud, x, y), scale(bilinear(u * g, y, x), -1))
            for g in gamma]


PAIRS = tuple(combinations_with_replacement(range(4), 2))


def source_frames(direction):
    second = {pair: {} for pair in PAIRS}
    shared = {pair: {} for pair in PAIRS}
    reverse_source = {}
    for left, right, weight in nodes():
        t = frame(direction, False, left, right)
        reverse_t = frame(direction, True, left, right)
        g = add(*(wedge(v, v) for v in t))
        reverse_source = add(reverse_source,
                             scale(add(*(wedge(v, v) for v in reverse_t)), weight))
        for a, b in PAIRS:
            pair = wedge(t[a], t[b])
            second[a, b] = add(second[a, b], scale(pair, weight))
            shared[a, b] = add(shared[a, b], scale(wedge(pair, g), weight))
    # Both maps use 96² times Haar and 8⁴ times physical frame degree.
    return ({p: scale(v, 96) for p, v in shared.items()},
            {p: wedge(v, reverse_source) for p, v in second.items()})


def modified_center(a, b):
    out = {}
    for i, j, k, l in product(range(4), repeat=4):
        weight = curvature(tuple(sorted(((i, k), (j, l)))))
        if weight:
            out = add(out, scale(wedge(a[tuple(sorted((i, j)))],
                                       b[tuple(sorted((k, l)))]), weight))
    return {mask: value for mask, value in out.items() if mask & 255 == 255}


def close(left, right):
    top = (1 << 32) - 1
    opposite = {sum(((mask >> (8*x)) & 255) << (8*(x ^ 3))
                    for x in range(4)): value for mask, value in right.items()}
    result = wedge(left, opposite).get(top, R.zero)
    assert result.is_ground and not result.const().y
    return int(result.const().x)


def check_source_support(active):
    # Degrees count bilinears, not individual Grassmann generators.
    edges = tuple((x, bit) for x, bit in product(range(16), (4, 8)))
    for x, y in combinations_with_replacement(active, 2):
        if x != y:
            # Each removed center leaves an odd independent curvature moment.
            continue
        deficit = Counter({x: 4, x ^ 4: 2, x ^ 8: 2})
        matched = set()
        for (a, u), (b, v) in product(edges, repeat=2):
            degrees = Counter((a, a ^ u, b, b ^ v))
            if {site: 2 * n for site, n in degrees.items()} == deficit:
                matched.add(((a, u), (b, v)))
        expected = {order for a, b in product((x, x ^ 4), (x, x ^ 8))
                    for order in (((a, 4), (b, 8)), ((b, 8), (a, 4)))}
        assert matched == expected


def main():
    active = geometry()
    check_source_support(active)
    normal, denominator = center()
    baseline = Fraction(close(normal, normal), denominator**2 * factorial(4)**2)
    assert baseline == Fraction(61875, 262144)
    maps = [source_frames(direction) for direction in range(2)]
    # Removed vertices have the same center. One source must occupy
    # each outgoing frame edge. Each can use either directed anchor.
    modified_denominator = 48 * 96**4 * 8**8
    weight = len(active) * baseline**3
    total = Fraction()
    for first, second in product(range(2), repeat=2):
        row = modified_center(maps[0][first], maps[1][second])
        # Opposite signs of D's two axes, and two source orderings.
        value = Fraction(-2 * close(row, normal),
                         modified_denominator * denominator * factorial(2) * factorial(4))
        offset = (first << 2) | (second << 3)
        print("offset", offset, "center terms", len(row),
              "layer coefficient", value, "lattice coefficient", weight * value)
        total += value
    print("two-source selected-word contribution", weight * total)


if __name__ == "__main__":
    main()
