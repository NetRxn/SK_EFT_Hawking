"""Exact local D² top coefficient with both independent source links weighted."""
from functools import cache
from fractions import Fraction as F
from itertools import combinations_with_replacement, product

from l1_equal_time_source_weights import G, T, square, coeff, weighted
from l1_direct_b_haar import haar_moment
from l1_reduced_wedge_reference import wedge_sign

PAIRS = tuple(combinations_with_replacement(range(8), 2))


def powers(indices):
    return tuple(indices.count(i) for i in range(8))


def avg(exponents):
    return haar_moment(exponents[:4]) * haar_moment(exponents[4:])


@cache
def weighted_G(indices):
    """Raw 16G coefficients integrated with a degree-two weight."""
    weight = powers(indices)
    result = {}
    for mask, polynomial in G.items():
        real = imag = F(0)
        for exponent, coefficient in polynomial.items():
            moment = avg(tuple(a + b for a, b in zip(exponent, weight, strict=True)))
            real += int(coefficient.x) * moment
            imag += int(coefficient.y) * moment
        if real or imag:
            result[mask] = (real, imag)
    return result


@cache
def kernel(a, b):
    A, B = weighted_G(a), weighted_G(b)
    real = imag = F(0)
    for mask, (r, i) in A.items():
        complement = T ^ mask
        if complement not in B:
            continue
        u, v = B[complement]
        sign = wedge_sign(mask, complement)
        real += sign * (r * u - i * v)
        imag += sign * (r * v + i * u)
    assert imag == 0
    ea, eb = powers(a), powers(b)
    # Square terms use exact single-link fourth tensors; the cross term is
    # the signed product of two independent weighted G polynomials.
    return coeff(square, ea) * avg(eb) + coeff(square, eb) * avg(ea) - real / 128


if __name__ == "__main__":
    values = {(a, b): kernel(a, b) for a, b in product(PAIRS, repeat=2)}
    assert all(value == values[b, a] for (a, b), value in values.items())
    for a in PAIRS:
        for offset in (0, 4):
            assert sum(values[a, (i, i)] for i in range(offset, offset + 4)) == weighted(powers(a))
    print("2+2 joint kernel nonzero", sum(bool(value) for value in values.values()), "/", len(values))
    samples = {
        ((0, 0), (0, 0)): F(15, 16), ((0, 0), (1, 1)): F(5, 4),
        ((0, 1), (0, 1)): F(0), ((1, 2), (1, 2)): F(0), ((1, 1), (5, 5)): F(67, 48),
    }
    for indices, expected in samples.items():
        assert values[indices] == expected
        print(indices, expected)
