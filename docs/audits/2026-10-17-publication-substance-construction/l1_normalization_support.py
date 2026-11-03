"""Enumerate the degree-eight pure-g2 normalization support."""
from collections import Counter, defaultdict
from itertools import combinations_with_replacement
from math import factorial, prod

from l1_interacting_support import TERMS, forward, half, match


def normalization_support():
    halves = defaultdict(list)
    for indices in combinations_with_replacement(range(len(TERMS)), 4):
        parity = 0
        counts = [0] * 4
        for index in indices:
            mask, degree, _ = TERMS[index]
            parity ^= mask
            counts = [a + b for a, b in zip(counts, degree)]
        if max(counts) <= 8:
            halves[parity, tuple(counts)].append(indices)

    for (parity, counts), prefixes in halves.items():
        suffixes = halves.get((parity, tuple(8 - n for n in counts)), ())
        for prefix in prefixes:
            for suffix in suffixes:
                if prefix[-1] <= suffix[0]:
                    yield prefix + suffix


def translated_support(indices):
    lookup = {label: index for index, (_, _, label) in enumerate(TERMS)}
    labels = [TERMS[index][2] for index in indices]
    return {
        tuple(sorted(lookup[x ^ shift, k, l, u ^ shift, v ^ shift]
                     for x, k, l, u, v in labels))
        for shift in range(4)
    }


def link_degrees(indices):
    """Count polynomial degree before parity reduction, including self-links."""
    degrees = Counter()
    for index in indices:
        x, k, l, u, v = TERMS[index][2]
        mu, nu = (axis for axis in range(4) if axis not in (k, l))
        degrees.update(((x, k), (forward(x, k), l), (forward(x, l), k),
                        (x, l), (u, mu), (v, nu)))
    assert sum(degrees.values()) == 48
    assert all(degree % 2 == 0 for degree in degrees.values())
    return degrees


if __name__ == "__main__":
    profiles = Counter()
    ordered = 0
    support = set(normalization_support())
    orbits = Counter()
    maximum_degrees = Counter()
    for indices in sorted(support):
        orbit = translated_support(indices)
        assert orbit <= support
        if indices == min(orbit):
            orbits[len(orbit)] += 1
            maximum_degrees[max(link_degrees(indices).values())] += 1
        multiplicities = Counter(indices).values()
        profiles[tuple(sorted(multiplicities, reverse=True))] += 1
        ordered += factorial(8) // prod(map(factorial, multiplicities))
    assert ordered == match(half(4), 0, (8,) * 4)[0]
    for profile, count in sorted(profiles.items()):
        print(profile, count)
    assert sum(size * count for size, count in orbits.items()) == len(support)
    print("translation orbit sizes", sorted(orbits.items()))
    print("maximum per-link degree by orbit", sorted(maximum_degrees.items()))
    print("multisets", sum(profiles.values()), "ordered", ordered)
