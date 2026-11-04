"""Bound the signed curvature numerator for exact modular reconstruction."""
from sys import argv


def numerator_bound(path):
    column_weight = 0
    with open(path) as rows:
        for row in rows:
            first, second, _, real, imag = map(int, row.split())
            assert imag == 0
            column_weight += abs(real) * (1 if first == second else 2)
    return column_weight**2 * 48**8 * 4**4


if __name__ == "__main__":
    bound = numerator_bound(argv[1])
    print(f"Absolute numerator bound {bound}")
    print(f"Require modulus product > {2 * bound}")
