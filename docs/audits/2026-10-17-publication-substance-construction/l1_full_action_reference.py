from collections import Counter
from functools import cache
from itertools import permutations, product

from sympy import I, ImmutableMatrix, diag, eye, simplify, sqrt, symbols, zeros

LENGTH = 5
ORIGIN = (0, 0, 0, 0)
DIRECTIONS = range(4)
SITES = tuple(product(range(LENGTH), repeat=4))
ORDERS = tuple(permutations(DIRECTIONS))
g1, g2 = symbols("g1 g2")
identity = ImmutableMatrix(eye(4))
pauli = [ImmutableMatrix([[0, 1], [1, 0]]),
         ImmutableMatrix([[0, -I], [I, 0]]), ImmutableMatrix(diag(1, -1))]
gamma = [ImmutableMatrix(zeros(2).row_join(-I * p).col_join((I * p).row_join(zeros(2))))
         for p in pauli]
gamma.append(ImmutableMatrix(zeros(2).row_join(eye(2)).col_join(eye(2).row_join(zeros(2)))))
gamma5 = ImmutableMatrix(diag(1, 1, -1, -1))
y_link = ImmutableMatrix(diag(I * pauli[0], eye(2)))
rotation = ImmutableMatrix(diag((eye(2) + I * pauli[2]) / sqrt(2), eye(2)))


def step(site, mu, n=1):
    return tuple((v + n) % LENGTH if j == mu else v for j, v in enumerate(site))


local = ((ORIGIN, 2), (ORIGIN, 3), (step(ORIGIN, 2), 4), (step(ORIGIN, 3), 4))
canonical = tuple(sorted(local))


def inversion_sign(values):
    return (-1) ** sum(a > b for j, a in enumerate(values) for b in values[j + 1:])


def extract_bits(left, right):
    indices = tuple(canonical.index(v) for v in (*left, *right))
    if len(set(indices)) != 4:
        return 0
    mask = 0
    sign = 1
    for index in indices:
        sign *= (-1) ** ((mask >> (index + 1)).bit_count())
        mask |= 1 << index
    return sign


def extract_reverse(left, right):
    # Independently remove target generators in reverse canonical order.
    word = list((*left, *right))
    sign = 1
    for generator in reversed(canonical):
        if generator not in word:
            return 0
        at = word.index(generator)
        sign *= (-1) ** (len(word) - at - 1)
        del word[at]
    return sign


@cache
def gauge(site, gauge_site):
    return rotation if site == gauge_site else identity


@cache
def link(site, mu, gauge_site, poison):
    bare = y_link if (site, mu) == (step(ORIGIN, 0), 1) else identity
    endpoint_missing = poison == "omit_endpoint" or (
        poison == "omit_single_endpoint" and (site, mu) == (ORIGIN, 0)
    )
    end = identity if endpoint_missing else gauge(step(site, mu), gauge_site)
    return ImmutableMatrix((end * bare * gauge(site, gauge_site).H).applyfunc(simplify))


@cache
def frame(site, mu, gauge_site, poison):
    forward, backward = step(site, mu), step(site, mu, -1)
    blocks = ((site, forward, 0, 1), (forward, site, 1, -1),
              (site, backward, 2, -1), (backward, site, 3, 1))
    out = {}
    for bars, psi, j, sign in blocks:
        # The target quotient is applied to each original block after recording it.
        for a in canonical[:2]:
            if a[0] != bars:
                continue
            for b in canonical[2:]:
                if b[0] != psi:
                    continue
                f = link(site, mu, gauge_site, poison)
                back = link(backward, mu, gauge_site, poison)
                values = []
                for gamma_a in gamma:
                    matrices = (gamma_a * f.H, f * gamma_a, gamma_a * back, back.H * gamma_a)
                    mat = gauge(bars, gauge_site).H * matrices[j] * gauge(psi, gauge_site)
                    values.append(simplify(sign * mat[a[1], b[1] - 4] / 4))
                out[(a, b)] = out.get((a, b), zeros(4)) + sum(
                    (c * mat for c, mat in zip(values, gamma)), zeros(4))
    return {word: mat for word, mat in out.items() if mat != zeros(4)}


def coefficient(ordering, gauge_site, extract, poison=None):
    stats = Counter()
    total = 0
    for x in SITES:
        stats["bases"] += 1
        # S4 is a sum of four degree-two T factors. The target extractor is homogeneous degree four.
        stats["g1_degree8_excluded"] += 1
        for k, l, mu, nu in ORDERS:
            stats["world_tuples"] += 1
            left = frame(x, mu, gauge_site, poison)
            right = frame(x, nu, gauge_site, poison)
            terms = [(a, b, extract(wa, wb)) for wa, a in left.items() for wb, b in right.items()]
            if not any(sign for _, _, sign in terms):
                continue
            stats["surviving_world_tuples"] += 1
            factors = [link(x, k, gauge_site, poison),
                       link(step(x, k), l, gauge_site, poison),
                       link(step(x, l), k, gauge_site, poison).H,
                       link(x, l, gauge_site, poison).H]
            if ordering == "closed":
                factors.reverse()
            plaquette = identity
            for factor in factors:
                plaquette *= factor
            for a, b, sign in terms:
                if sign:
                    divisor = 1 if poison == "drop_action_quarter" else 4
                    chirality = -gamma5 if poison == "flip_gamma5" else gamma5
                    total += (sign * inversion_sign((k, l, mu, nu))
                              * (plaquette * a * b * chirality).trace() / divisor)
                    stats["nonzero_wedges"] += 1
    assert len(SITES) * len(DIRECTIONS) == 2500
    assert stats["bases"] == stats["g1_degree8_excluded"] == 625
    assert stats["world_tuples"] == 15000
    return simplify(g1 * 0 + g2 * total), stats


def main():
    orientation = inversion_sign(tuple(canonical.index(v) for v in local))
    print("local to lexicographic sign", orientation)
    records = {}
    for order in ("literal", "closed"):
        for transformed in (False, True):
            gauge_site = ORIGIN if transformed else None
            val, stats = coefficient(order, gauge_site, extract_bits)
            second, second_stats = coefficient(order, gauge_site, extract_reverse)
            assert (val, stats) == (second, second_stats)
            records[order, transformed] = orientation * val
            print(order, transformed, "global", val, "local", orientation * val, dict(stats))
    assert records == {("literal", False): I*g2/2, ("literal", True): -I*g2/2,
                       ("closed", False): I*g2/2, ("closed", True): I*g2/2}
    for order in ("literal", "closed"):
        print(order, "residual", simplify(records[order, True] - records[order, False]))
    for poison in ("omit_endpoint", "drop_action_quarter", "flip_gamma5"):
        val, _ = coefficient("closed", ORIGIN, extract_bits, poison)
        detected = orientation * val != records["closed", True]
        print("poison", poison, "local", orientation * val, "detected", detected)
        if poison != "omit_endpoint":
            assert detected
    print("poison old order in closed", records["literal", True])

    # Move the nontrivial gauge factor to the end of the positive first link.
    # Omit just that link's endpoint factor while retaining every other one.
    endpoint = step(ORIGIN, 0)
    expected = {
        ("literal", None): g2 / 2,
        ("closed", None): I * g2 / 2,
        ("closed", "omit_single_endpoint"): sqrt(2) * (1 + I) * g2 / 4,
    }
    for (order, poison), want in expected.items():
        val, stats = coefficient(order, endpoint, extract_bits, poison)
        second, second_stats = coefficient(order, endpoint, extract_reverse, poison)
        assert (val, stats) == (second, second_stats)
        assert simplify(orientation * val - want) == 0
        print("endpoint control", order, poison, "global", val,
              "local", orientation * val, dict(stats))
    poisoned = expected["closed", "omit_single_endpoint"]
    assert simplify(poisoned - records["closed", False]) != 0
    restored, _ = coefficient("closed", endpoint, extract_bits)
    assert orientation * restored == records["closed", False]
    print("single endpoint omission detected; unpoisoned repeat PASS")


if __name__ == "__main__":
    main()
