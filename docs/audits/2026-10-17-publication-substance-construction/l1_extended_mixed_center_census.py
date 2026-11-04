"""Balanced checkerboard words with exactly two centers split 2+2."""
from collections import Counter, defaultdict
from fractions import Fraction
from functools import cache
from itertools import permutations, product
from math import factorial

from l1_extended_mixed_plane import AXES, EVEN, PAIRS, patterns
from l1_extended_opposed import staged_center
from l1_direct_b_haar import add
from l1_extended_opposed_source import modified_center, summed_fourth
from l1_extended_two_mixed_centers import (
    contract, mixed_center, mixed_source_center, remap, source_edge, word,
)


def swap_patterns():
    seen = set()
    for base in patterns():
        changes = defaultdict(list)
        for x, original in base.items():
            for other in PAIRS:
                if original == other:
                    continue
                removed = tuple(x ^ (1 << a) for a in original if a not in other)
                added = tuple(x ^ (1 << a) for a in other if a not in original)
                changes[removed, added].append((x, other))
        for (removed, added), forward in changes.items():
            for (x, a), (y, b) in product(forward, changes.get((added, removed), ())):
                if x >= y:
                    continue
                seen.add(tuple(tuple(sorted((pair, {x: a, y: b}[z])))
                               if z in (x, y) else (pair, pair)
                               for z, pair in base.items()))
    return seen


def site_permutation(axes, shift):
    return tuple(sum(((x >> i) & 1) << axes[i] for i in AXES) ^ shift
                 for x in range(16))


def orbits(words):
    transforms = [(site_permutation(axes, shift),
                   {p: tuple(sorted(axes[a] for a in p)) for p in PAIRS})
                  for axes, shift in product(permutations(AXES), EVEN)]
    pending = set(words)
    while pending:
        representative = min(pending)
        images = set()
        for sites, planes in transforms:
            image = sorted((sites[x], tuple(sorted(map(planes.__getitem__, pairs))))
                           for x, pairs in zip(EVEN, representative, strict=True))
            images.add(tuple(pairs for _, pairs in image))
        assert images <= pending
        pending.difference_update(images)
        yield representative, len(images)


def curvature_boundary(pattern, omitted=None):
    protected = set()
    faces = {}
    for x, pairs in zip(EVEN, pattern, strict=True):
        for frame in set(pairs):
            for a in frame:
                protected.update(((x, a), (x ^ (1 << a), a)))
            k, l = (a for a in AXES if a not in frame)
            if (x, k, l) == omitted:
                continue
            faces[x, k, l] = {(x, k), (x ^ (1 << k), l), (x ^ (1 << l), k), (x, l)}
    while faces:
        counts = Counter(link for face in faces.values() for link in face)
        private = next((x for x, face in faces.items()
                        if any(counts[e] == 1 and e not in protected for e in face)), None)
        if private is None:
            return faces, protected
        del faces[private]
    return faces, protected


def curvature_core(pattern):
    return len(curvature_boundary(pattern)[0])


def tensors(pattern, normal, shared):
    result = {}
    for x, (first, second) in zip(EVEN, pattern, strict=True):
        common = set(first) & set(second)
        if first == second:
            poly, axes = normal, first
        else:
            assert len(common) == 1
            a, b = sorted(set(first) ^ set(second))
            poly, axes = shared, (a, next(iter(common)), b)
        result[x] = remap(poly, (x, *(x ^ (1 << a) for a in axes)))
    return result


@cache
def summed_source_tensor(removed_local_site):
    if removed_local_site == 0:
        return add(*(modified_center(source_edge(0, u), source_edge(1, v))
                     for u, v in product(range(2), repeat=2)))
    return add(*(mixed_source_center(removed_local_site, u, v)
                 for u, v in product(range(2), repeat=2)))


def source_total(pattern, original, only_faces=None):
    # Sum over all six choices of shear axes. Axis permutations in
    # an orbit make the contribution to any fixed choice one sixth.
    total = 0
    for x, (first, second) in zip(EVEN, pattern, strict=True):
        if first == second:
            axes = first
            variants = [(0, factorial(4) // factorial(2), first)]
        else:
            common, = set(first) & set(second)
            a, b = sorted(set(first) ^ set(second))
            axes = (a, common, b)
            variants = [(1, 48 * factorial(2), (a, common)),
                        (3, 48 * factorial(2), (b, common))]
        sites = (x, *(x ^ (1 << a) for a in axes))
        for local, adjustment, frame in variants:
            k, l = (axis for axis in AXES if axis not in frame)
            if only_faces is not None and (x, k, l) not in only_faces:
                continue
            terms = dict(original)
            terms[x] = remap(summed_source_tensor(local), sites)
            raw = contract(terms)
            assert raw.is_ground and not raw.const().y
            total -= 2 * adjustment * int(raw.const().x)
    return total


def main():
    patterns = swap_patterns()
    selected = defaultdict(list)
    for x, n, pair in word():
        selected[x].extend([pair] * (n // 2))
    selected = tuple(tuple(sorted(selected[x])) for x in EVEN)
    assert selected in patterns
    fourth = summed_fourth(1)
    normal, _ = staged_center(summed_fourth(0), fourth)
    shared = mixed_center(fourth)
    frame_scale = 96**4 * 8**8
    denominator = (48 * frame_scale * factorial(4))**6
    denominator *= (48**2 * frame_scale * factorial(2)**2)**2
    control = contract(tensors(selected, normal, shared))
    assert control.is_ground and not control.const().y
    assert Fraction(int(control.const().x), denominator) == Fraction(
        123512167576473721435546875, 9223372036854775808)
    total = numerator = 0
    counts = Counter()
    populations = Counter()
    for representative, multiplicity in orbits(patterns):
        core = curvature_core(representative)
        counts[core] += 1
        populations[core] += multiplicity
        if core == 0:
            terms = tensors(representative, normal, shared)
            raw = contract(terms)
            assert raw.is_ground and not raw.const().y
            total += multiplicity * int(raw.const().x)
            numerator += multiplicity * source_total(representative, terms)
    assert sum(populations.values()) == len(patterns)
    print("one-checkerboard orbit counts by curvature core size", dict(sorted(counts.items())))
    print("one-checkerboard word counts by curvature core size", dict(sorted(populations.items())))
    print("peelable two-mixed-center normalization, both checkerboards",
          Fraction(2 * total, denominator))
    print("peelable two-mixed-center numerator, both checkerboards",
          Fraction(2 * numerator, 6 * denominator))


if __name__ == "__main__":
    main()
