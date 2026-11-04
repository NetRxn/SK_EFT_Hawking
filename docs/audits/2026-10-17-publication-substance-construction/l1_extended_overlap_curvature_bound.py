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


PRIMES = (
    65521, 65519, 65497, 65479, 65449, 65447, 65437, 65423, 65419,
    65413, 65407, 65393, 65381, 65371, 65357, 65353, 65327,
)
CHECK_PRIME = 65323


def reconstruct(residues, bound, check_residue):
    """Recover the signed numerator and check an unused modulus."""
    modulus = 1
    value = 0
    for prime, residue in zip(PRIMES, residues, strict=True):
        digit = (residue - value) * pow(modulus, -1, prime) % prime
        value += digit * modulus
        modulus *= prime
    assert modulus > 2 * bound
    if value > modulus // 2:
        value -= modulus
    assert abs(value) <= bound
    assert value % CHECK_PRIME == check_residue
    return value


if __name__ == "__main__":
    bound = numerator_bound(argv[1])
    print(f"Absolute numerator bound {bound}")
    print(f"Require modulus product > {2 * bound}")
