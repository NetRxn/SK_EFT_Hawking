from collections import defaultdict
from fractions import Fraction
from functools import lru_cache

from sympy import I, Matrix, diag, eye, zeros
from sympy.polys.domains import ZZ_I

ZERO = ZZ_I.zero
TOP = (1 << 16) - 1


@lru_cache(None)
def wedge_sign(left, right):
    crossings = 0
    while left:
        bit = left & -left
        crossings += (right & (bit - 1)).bit_count()
        left ^= bit
    return (-1) ** crossings


def add(*polynomials):
    result = defaultdict(lambda: ZERO)
    for polynomial in polynomials:
        for mask, coefficient in polynomial.items():
            result[mask] += coefficient
    return {mask: coefficient for mask, coefficient in result.items() if coefficient}


def scale(polynomial, factor):
    return {mask: coefficient * factor for mask, coefficient in polynomial.items()}


def wedge(left, right):
    result = defaultdict(lambda: ZERO)
    for lhs, first in left.items():
        for rhs, second in right.items():
            if not lhs & rhs:
                result[lhs | rhs] += first * second * wedge_sign(lhs, rhs)
    return {mask: coefficient for mask, coefficient in result.items() if coefficient}


def bilinear(matrix, bar_site, psi_site, ordering):
    result = {}
    for i in range(4):
        for j in range(4):
            coefficient = ZZ_I.from_sympy(matrix[i, j])
            if coefficient:
                left = 1 << ordering[8 * bar_site + i]
                right = 1 << ordering[8 * psi_site + 4 + j]
                result[left | right] = coefficient * wedge_sign(left, right)
    return result


def probe(r, s, ordering=tuple(range(16)), multiplier=1, coupled=True):
    pauli = [Matrix([[0, 1], [1, 0]]), Matrix([[0, -I], [I, 0]]), diag(1, -1)]
    gamma = [zeros(2).row_join(-I * p).col_join((I * p).row_join(zeros(2))) for p in pauli]
    gamma.append(zeros(2).row_join(eye(2)).col_join(eye(2).row_join(zeros(2))))
    embeddings = [diag(p, zeros(2)) for p in pauli] + [diag(zeros(2), p) for p in pauli]
    c = diag(r, r, s, s)
    products = [(g * c, c * g) for g in gamma]
    transport = [
        [scale(add(bilinear(a, 0, 1, ordering), scale(bilinear(b, 1, 0, ordering), -1)),
               multiplier if coupled else 0) for a, b in site_products]
        for site_products in [products, [(b, a) for a, b in products]]
    ]

    def site_response(site, t):
        axial = [[bilinear(g * p + p * g, site, site, ordering) for p in embeddings] for g in gamma]
        k = [[scale(add(*(wedge(a, b) for a, b in zip(row, column))), -1)
              for column in axial] for row in axial]
        norm = add(*(wedge(v, v) for v in t))
        trace = add(*(k[j][j] for j in range(4)))
        return add(wedge(norm, trace), scale(add(*(
            wedge(wedge(t[j], t[m]), k[j][m]) for j in range(4) for m in range(4)
        )), -1))

    # T was scaled by four and K by sixteen, so each R is scaled by 256.
    left, right = (site_response(site, t) for site, t in enumerate(transport))
    result = wedge(left, right).get(TOP, ZERO)
    assert result.y == 0, result
    return Fraction(int(result.x), 256 ** 2)


def main():
    f10, f11 = probe(1, 0), probe(1, 1)
    assert (f10, f11) == (Fraction(135, 32), Fraction(27, 2))
    assert probe(0, 1) == f10
    assert probe(-1, 1) == f11
    assert probe(0, 0) == 0
    swapped = (1, 0, *range(2, 16))
    assert probe(1, 0, swapped) == -f10
    assert probe(1, 1, swapped) == -f11
    assert probe(1, 0, multiplier=2) == 16 * f10
    assert probe(1, 1, coupled=False) == 0
    assert probe(2, 3) == f10 * (2**4 + 3**4) + (f11 - 2*f10) * 2**2 * 3**2
    u, v = f10, f11 - 2*f10
    haar_avg = 10*u + 4*v
    db = Fraction(64, 9) * haar_avg
    assert haar_avg == Fraction(999, 16) and db == 444
    print(f'F(1,0)={f10}; F(1,1)={f11}; u={u}; v={v}; Haar average={haar_avg}; D_B={db}')
    print('PASS: chirality swap, chiral sign, C=0, odd orientation, longitudinal T rescaling, coupling removal, off-probe quartic.')


if __name__ == '__main__':
    main()
