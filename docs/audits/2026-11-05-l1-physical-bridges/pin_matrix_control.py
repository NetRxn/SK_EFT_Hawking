"""Exact small Gaussian-integer matrix control; imports no project evaluator."""
from itertools import permutations
import json


def matmul(a, b):
    return [[sum(x * y for x, y in zip(row, col)) for col in zip(*b)] for row in a]


def block(a, b, c, d):
    return [x + y for x, y in zip(a, b)] + [x + y for x, y in zip(c, d)]


def scale(c, a):
    return [[c * x for x in row] for row in a]


def determinant(a):
    value = 0
    for p in permutations(range(len(a))):
        term = (-1) ** sum(p[i] > p[j] for i in range(len(p)) for j in range(i + 1, len(p)))
        for i, j in enumerate(p):
            term *= a[i][j]
        value += term
    return value


if __name__ == '__main__':
    z = [[0, 0], [0, 0]]
    eye = [[1, 0], [0, 1]]
    pauli = [[[0, 1], [1, 0]], [[0, -1j], [1j, 0]], [[1, 0], [0, -1]]]
    gamma = [block(z, scale(-1j, p), scale(1j, p), z) for p in pauli]
    gamma.append(block(z, eye, eye, z))
    gamma5 = block(eye, z, z, scale(-1, eye))
    r = gamma[3]
    ident = block(eye, z, z, eye)
    assert matmul(r, r) == ident
    assert determinant(r) == 1
    for i, g in enumerate(gamma):
        assert matmul(matmul(r, g), r) == scale(1 if i == 3 else -1, g)
    assert matmul(matmul(r, gamma5), r) == scale(-1, gamma5)
    for k in range(4):
        e = [[int(i * 2 + j == k) for j in range(2)] for i in range(2)]
        assert matmul(matmul(r, block(e, z, z, z)), r) == block(z, z, z, e)
        assert matmul(matmul(r, block(z, z, z, e)), r) == block(e, z, z, z)
    cases = 0
    for sites in range(1, 65):
        for insertions in range(3):
            for m in range(sites + 1):
                n = 2 * sites - 2 * m - insertions
                if n >= 0 and (m + n) % 2 == 0:
                    assert m % 2 == insertions % 2
                    cases += 1
    print(json.dumps({'matrix_control': 'passed', 'R_determinant': 1,
                      'internal_vector_signs': [-1, -1, -1, 1],
                      'chiral_swap_basis_checks': 8,
                      'finite_degree_parity_cases': cases,
                      'scope': 'tiny exact matrix and parity controls; no Haar contraction or denominator calculation'}))
