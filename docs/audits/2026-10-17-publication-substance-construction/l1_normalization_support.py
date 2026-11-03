"""Enumerate the degree-eight pure-g2 normalization support."""
from collections import Counter, defaultdict
from itertools import combinations, combinations_with_replacement, product
from math import factorial, lcm, prod

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


def world_axis_orbit(indices):
    """Images under translations and swaps of equal-extent axes."""
    lookup = {label: index for index, (_, _, label) in enumerate(TERMS)}
    labels = [TERMS[index][2] for index in indices]
    orbit = set()
    for swap_extended, swap_transverse, shift in product(range(2), range(2), range(4)):
        axes = (swap_extended, 1 - swap_extended,
                2 + swap_transverse, 3 - swap_transverse)

        def site(x):
            return (((x >> 1) | ((x & 1) << 1)) if swap_extended else x) ^ shift

        image = []
        for x, k, l, u, v in labels:
            mu, nu = (axis for axis in range(4) if axis not in (k, l))
            if axes[mu] > axes[nu]:
                u, v = v, u
            first, second = sorted((axes[k], axes[l]))
            image.append(lookup[site(x), first, second, site(u), site(v)])
        orbit.add(tuple(sorted(image)))
    return orbit


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


def extended_link_trees():
    links = [(site, axis) for site in range(4) for axis in range(2)]
    for tree in combinations(links, 3):
        components = [{site} for site in range(4)]
        for site, axis in tree:
            left = next(group for group in components if site in group)
            right = next(group for group in components if forward(site, axis) in group)
            if left != right:
                left.update(right)
                components.remove(right)
        if len(components) == 1:
            yield tree


def haar_scale(degree):
    """Common denominator for normalized Spin(4) moments on a single link."""
    def sphere_scale(n):
        return prod(range(4, 4 + n, 2))

    return lcm(*(sphere_scale(left) * sphere_scale(degree - left)
                 for left in range(0, degree + 1, 2)))


if __name__ == "__main__":
    profiles = Counter()
    ordered = 0
    support = set(normalization_support())
    orbits = Counter()
    maximum_degrees = Counter()
    denominator_scale = 1
    tree_degrees = Counter()
    trees = tuple(extended_link_trees())
    for indices in sorted(support):
        multiplicities = Counter(indices).values()
        orbit = translated_support(indices)
        assert orbit <= support
        if indices == min(orbit):
            orbits[len(orbit)] += 1
            incidence = link_degrees(indices)
            degrees = incidence.values()
            remaining_degree = 48 - max(sum(incidence[link] for link in tree)
                                        for tree in trees)
            tree_degrees[remaining_degree] += 1
            maximum_degrees[max(degrees)] += 1
            weight_scale = prod(map(factorial, multiplicities))
            denominator_scale = lcm(denominator_scale,
                                    weight_scale * prod(map(haar_scale, degrees)))
        profiles[tuple(sorted(multiplicities, reverse=True))] += 1
        ordered += factorial(8) // prod(map(factorial, multiplicities))
    assert ordered == match(half(4), 0, (8,) * 4)[0]
    for profile, count in sorted(profiles.items()):
        print(profile, count)
    assert sum(size * count for size, count in orbits.items()) == len(support)
    print("translation orbit sizes", sorted(orbits.items()))
    print("maximum per-link degree by orbit", sorted(maximum_degrees.items()))
    print("multisets", sum(profiles.values()), "ordered", ordered)
    print("candidate tree reduction", len(trees), sorted(tree_degrees.items()))
    print("common denominator including factorials", denominator_scale)
    unassigned = support.copy()
    axis_orbits = Counter()
    while unassigned:
        orbit = world_axis_orbit(min(unassigned))
        assert orbit <= unassigned
        unassigned.difference_update(orbit)
        axis_orbits[len(orbit)] += 1
    print("world-axis orbit sizes", sorted(axis_orbits.items()))
