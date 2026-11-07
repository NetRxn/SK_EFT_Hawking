"""Check the transverse pair formula by exact coordinate Haar moments."""
from itertools import product

from l1_normalization_uniform_mixed_edge import mul, qadj, unit


def direct(x, y, z, t):
    result = [[0] * 3 for _ in range(3)]
    for a, b in product(range(4), repeat=2):
        first = mul(mul(qadj(unit(a)), x), mul(unit(b), y))
        second = mul(mul(qadj(unit(b)), z), mul(unit(a), t))
        for i, j in product(range(3), repeat=2):
            result[i][j] += first[i + 1] * second[j + 1]
    return result


if __name__ == "__main__":
    nonzero = 0
    for labels in product(range(4), repeat=4):
        x, y, z, t = map(unit, labels)
        observed = direct(x, y, z, t)
        for i, j in product(range(3), repeat=2):
            expected = -4 * mul(z, x)[0] * mul(mul(y, unit(i + 1)), t)[j + 1]
            assert observed[i][j] == expected, (labels, i, j)
            nonzero += bool(expected)
    assert nonzero == 144
    print("2,304 exact components matched, including 144 nonzero components")
