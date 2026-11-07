"""Bound the signed curvature numerator for exact modular reconstruction."""
from math import gcd
from sys import argv


def column_norms(path):
    divisor = maximum = column_weight = 0
    with open(path) as rows:
        for row in rows:
            first, second, _, real, imag = map(int, row.split())
            assert imag == 0
            magnitude = abs(real)
            divisor = gcd(divisor, magnitude)
            maximum = max(maximum, magnitude)
            column_weight += magnitude * (1 if first == second else 2)
    assert divisor > 0
    return divisor, maximum, column_weight


def numerator_bound(path):
    _, _, column_weight = column_norms(path)
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
    divisor, maximum, column_weight = column_norms(argv[1])
    scaled_bound = (column_weight // divisor)**2 * 48**8 * 4**4
    print(f"Common divisor {divisor}, scaled maximum {maximum // divisor}")
    print(f"Scaled numerator bound {scaled_bound} ({scaled_bound.bit_length()} bits)")
