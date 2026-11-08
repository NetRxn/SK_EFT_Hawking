"""Exact fixed-link checkerboard and internal chirality determinant control."""
from itertools import product

from sympy import Matrix, diag, zeros

from l1_direct_b_haar import gamma
from l1_normalization_disjoint_sector import quat


def matrix():
    result = zeros(64)
    units = tuple(tuple(int(a == b) for a in range(4)) for b in range(4))
    for site, axis in product(range(16), range(4)):
        neighbor = site ^ (1 << axis)
        for anchor in (site, neighbor):
            link = diag(quat(units[(anchor + axis) % 4]),
                        quat(units[(anchor // 2 + 3 * axis) % 4]))
            weight = 1 + (11 * site + 7 * axis + 3 * anchor) % 17
            block = weight * gamma[axis] * link.adjoint() if anchor == site else (
                -weight * gamma[axis] * link
            )
            for a, b in product(range(4), repeat=2):
                result[4 * site + a, 4 * neighbor + b] += block[a, b]
                result[4 * neighbor + b, 4 * site + a] -= block[a, b].conjugate()
    return result


def indices(parity, chirality):
    return [4 * site + spin for site in range(16)
            if site.bit_count() % 2 == parity
            for spin in range(2 * chirality, 2 * chirality + 2)]


if __name__ == "__main__":
    original = matrix()
    even = [indices(0, chirality) for chirality in (0, 1)]
    odd = [indices(1, chirality) for chirality in (0, 1)]
    order = even[0] + odd[1] + even[1] + odd[0]
    first = original.extract(even[0], odd[1])
    second = original.extract(even[1], odd[0])
    zero = zeros(16)
    expected = diag(Matrix.vstack(Matrix.hstack(zero, first), Matrix.hstack(-first.adjoint(), zero)),
                    Matrix.vstack(Matrix.hstack(zero, second), Matrix.hstack(-second.adjoint(), zero)))
    assert original.extract(order, order) == expected
    direct = original.det(method="domain-ge")
    factored = first.det(method="domain-ge") * second.det(method="domain-ge")
    assert direct == factored * factored.conjugate() and direct > 0
    print("Exact 64 by 64 determinant matches the two chiral block norms")
