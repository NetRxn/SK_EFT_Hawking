"""Check global chirality symmetry of the exact exterior column."""
from sys import argv


def flip_key(key):
    flipped = 0
    place = 1
    for _ in range(8):
        key, label = divmod(key, 6)
        flipped += ((label + 3) % 6) * place
        place *= 6
    assert key == 0
    return flipped


if __name__ == "__main__":
    rows = {}
    with open(argv[1]) as stream:
        for line in stream:
            a, b, key, real, imag = map(int, line.split())
            assert imag == 0 and real
            rows[a, b, key] = real
    assert len(rows) == 2_321_664
    for (a, b, key), coefficient in rows.items():
        first, second = sorted((a ^ 4, b ^ 4))
        assert rows[first, second, flip_key(key)] == coefficient
    print(f"Global chirality flip matches all {len(rows):,} coefficients")
