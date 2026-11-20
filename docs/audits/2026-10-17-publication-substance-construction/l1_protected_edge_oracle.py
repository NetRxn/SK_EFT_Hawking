"""Direct 16-bit exterior/quaternion oracle for a protected intersite frame."""

from collections import Counter, defaultdict
from fractions import Fraction
from functools import cache
from itertools import product
from math import prod
from sympy import I, Matrix, diag, eye, zeros

from l1_extended_mixed_frame_moment import frame_edge

P = (Matrix([[0, 1], [1, 0]]), Matrix([[0, -I], [I, 0]]), diag(1, -1))
G = tuple(zeros(2).row_join(-I * p).col_join((I * p).row_join(zeros(2))) for p in P)
G += (zeros(2).row_join(eye(2)).col_join(eye(2).row_join(zeros(2))),)
Q = (eye(2), *(-I * p for p in P))


def put(matrix, left, right, coefficient=1):
    result = {}
    for a, b in product(range(4), repeat=2):
        z = matrix[a, b] * coefficient
        if not z:
            continue
        first, second = 8 * left + a, 8 * right + 4 + b
        re, im = map(int, z.as_real_imag())
        s = -1 if first > second else 1
        result[(1 << first) | (1 << second)] = (s * re, s * im)
    return result


@cache
def basis(label, port):
    anchor, j = divmod(port, 8)
    chirality, q = divmod(j, 4)
    U = diag(Q[q], zeros(2)) if chirality == 0 else diag(zeros(2), Q[q])
    Ud = U.adjoint()
    g = G[label]
    if anchor == 0:
        return put(g * Ud, 0, 1) | put(U * g, 1, 0, -1)
    return put(Ud * g, 1, 0) | put(g * U, 0, 1, -1)


@cache
def sign(a, b):
    # Count inversions directly without borrowing the production sign routine.
    return (-1) ** sum(
        (b & ((1 << i) - 1)).bit_count() for i in range(16) if a >> i & 1
    )


def wedge(a, b):
    real, imag = Counter(), Counter()
    for u, (r, i) in a.items():
        for v, (s, j) in b.items():
            if u & v:
                continue
            w = sign(u, v)
            real[u | v] += w * (r * s - i * j)
            imag[u | v] += w * (r * j + i * s)
    return {m: (r, imag[m]) for m, r in real.items() if r or imag[m]}


@cache
def pair(a, b, i, j):
    return wedge(basis(a, i), basis(b, j))


@cache
def sphere(powers):
    if any(n % 2 for n in powers):
        return Fraction()
    return Fraction(
        prod(prod(range(1, n, 2)) for n in powers), prod(range(4, 4 + sum(powers), 2))
    )


@cache
def weight(coords, probe):
    powers = Counter(coords)
    if probe is None:
        if any(powers[i] for i in (9, 10, 11, 13, 14, 15)):
            return 0
        groups = (0, 4)
    else:
        powers.update(8 + i for i in probe)
        groups = (0, 4, 8, 12)
    value = 192**2 * prod(
        sphere(tuple(powers[s + j] for j in range(4))) for s in groups
    )
    assert value.denominator == 1
    return int(value)


def reference(labels, probe):
    a, b, c, d = labels
    out = defaultdict(lambda: [0, 0])
    live = 0
    for coords in product(range(16), repeat=4):
        w = weight(tuple(sorted(coords)), probe)
        if not w:
            continue
        live += 1
        i, j, k, l = coords
        for mask, (r, s) in wedge(pair(a, b, i, j), pair(c, d, k, l)).items():
            out[mask][0] += w * r
            out[mask][1] += w * s
    return {m: tuple(z) for m, z in out.items() if any(z)}, live


if __name__ == "__main__":
    cases = (((0, 0, 1, 1), (0, 4)), ((0, 1, 2, 3), (1, 2)), ((0, 0, 1, 1), None))
    for labels, probe in cases:
        actual, live = reference(labels, probe)
        expected = {}
        for m, c in frame_edge(labels, 1, probe).items():
            if c:
                assert c.is_ground
                z = c.const()
                expected[m] = (int(z.x), int(z.y))
        assert actual == expected, (labels, probe, len(actual), len(expected))
        if probe == (1, 2):
            assert not actual
        else:
            assert actual
        signed = tuple(
            sum(s * v > 0 for z in actual.values() for v in z) for s in (1, -1)
        )
        assert not actual or all(signed)
        print(
            labels,
            probe,
            "live coordinates",
            live,
            "map entries",
            len(actual),
            "signed components",
            signed,
            flush=True,
        )
