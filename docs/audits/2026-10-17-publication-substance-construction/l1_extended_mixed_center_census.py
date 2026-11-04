"""Balanced checkerboard words with even plane multiplicities."""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from fractions import Fraction
from functools import cache
from itertools import combinations_with_replacement, permutations, product
from math import factorial

from l1_extended_mixed_plane import AXES, EVEN, PAIRS, patterns
from l1_extended_opposed import staged_center
from l1_direct_b_haar import add, scale, wedge
from l1_extended_opposed_source import modified_center, summed_fourth
from l1_extended_two_mixed_centers import (
    contract, mixed_center, mixed_source_center, remap, second_channels, second_sum, source_edge, source_only, word,
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


def tensors(pattern, normal, shared, disjoint=None):
    result = {}
    for x, (first, second) in zip(EVEN, pattern, strict=True):
        common = set(first) & set(second)
        if first == second:
            poly, axes = normal, first
        elif not common:
            assert disjoint is not None
            poly, axes = disjoint, first + second
        else:
            a, b = sorted(set(first) ^ set(second))
            poly, axes = shared, (a, next(iter(common)), b)
        result[x] = remap(poly, (x, *(x ^ (1 << a) for a in axes)))
    return result


@cache
def summed_source_tensor(removed_local_site):
    if removed_local_site == 0:
        return add(*(modified_center(source_edge(0, u), source_edge(1, v))
                     for u, v in product(range(2), repeat=2)))
    if removed_local_site in (4, 5):
        g = add(source_only(0), source_only(1))
        sources = wedge(g, remap(g, (0, 2)))
        survivor = remap(disjoint_pair(), (0, 3, 4))
        joined = wedge(sources, survivor)
        if removed_local_site == 5:
            joined = remap(joined, (0, 3, 4, 1, 2))
        return {m: c for m, c in joined.items() if m & 255 == 255}
    return add(*(mixed_source_center(removed_local_site, u, v)
                 for u, v in product(range(2), repeat=2)))


def source_variants(first, second):
    if first == second:
        return first, [(0, factorial(4) // factorial(2), first)]
    common_axes = set(first) & set(second)
    if not common_axes:
        adjustment = 48 * factorial(2)
        return first + second, [(4, adjustment, first), (5, adjustment, second)]
    common, = common_axes
    a, b = sorted(set(first) ^ set(second))
    return (a, common, b), [(1, 48 * factorial(2), (a, common)),
                            (3, 48 * factorial(2), (b, common))]


def source_total(pattern, original, only_faces=None):
    # Sum over all six choices of shear axes. Axis permutations in
    # an orbit make the contribution to any fixed choice one sixth.
    total = 0
    for x, (first, second) in zip(EVEN, pattern, strict=True):
        axes, variants = source_variants(first, second)
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


def half_words(centers):
    passive = tuple(x ^ 1 for x in EVEN)
    options = {}
    for x in centers:
        rows = []
        for first, second in combinations_with_replacement(PAIRS, 2):
            incidence = Counter(x ^ (1 << a) for pair in (first, second) for a in pair)
            rows.append((tuple(incidence[y] for y in passive), (first, second)))
        options[x] = rows

    for rows in product(*(options[x] for x in centers)):
        degree = tuple(sum(column) for column in zip(*(row for row, _ in rows)))
        if max(degree) <= 4:
            word = tuple(pair for _, pair in rows)
            yield degree, sum(a != b for a, b in word), word


def words_with_mixed_count(count):
    left = defaultdict(list)
    for degree, mixed, word in half_words(EVEN[:4]):
        if mixed <= count:
            left[degree, mixed].append(word)
    for degree, mixed, word in half_words(EVEN[4:]):
        key = tuple(4 - n for n in degree), count - mixed
        for prefix in left.get(key, ()):
            yield prefix + word


def even_center_counts():
    def half(centers):
        support = defaultdict(Counter)
        for degree, mixed, _ in half_words(centers):
            support[degree][mixed] += 1
        return support

    left, right = half(EVEN[:4]), half(EVEN[4:])
    result = Counter()
    for degree, counts in left.items():
        other = tuple(4 - n for n in degree)
        for a, b in product(counts, right.get(other, ())):
            result[a + b] += counts[a] * right[other][b]
    assert result[0] == 2970 and result[1] == 0 and result[2] == len(swap_patterns())
    return dict(sorted(result.items()))


@cache
def disjoint_pair():
    second = second_sum(0)
    return add(*(scale(wedge(second[tuple(sorted(a))], remap(second[b], (0, 2))), w)
                 for a, b, w in second_channels()))


def disjoint_center():
    # Temporary sites 1,2 and 3,4 carry the two disjoint frame pairs.
    pair = disjoint_pair()
    return {m: c for m, c in wedge(pair, remap(pair, (0, 3, 4))).items() if m & 255 == 255}


def three_mixed(source=False):
    words = set(words_with_mixed_count(3))
    assert len(words) == 41760
    fourth = summed_fourth(1)
    normal, _ = staged_center(summed_fourth(0), fourth)
    shared = mixed_center(fourth)
    disjoint = disjoint_center()
    frame_scale = 96**4 * 8**8
    denominator = (48 * frame_scale * factorial(4))**5
    denominator *= (48**2 * frame_scale * factorial(2)**2)**3
    counts = Counter()
    populations = Counter()
    totals = Counter()
    numerators = Counter()
    for representative, multiplicity in orbits(words):
        core = curvature_core(representative)
        disjoint_count = sum(not (set(a) & set(b)) for a, b in representative)
        key = core, disjoint_count
        counts[key] += 1
        populations[key] += multiplicity
        if core == 0:
            terms = tensors(representative, normal, shared, disjoint)
            raw = contract(terms)
            assert raw.is_ground and not raw.const().y
            totals[disjoint_count] += multiplicity * int(raw.const().x)
            if source:
                numerators[disjoint_count] += multiplicity * source_total(representative, terms)
    assert sum(populations.values()) == len(words)
    print("orbit counts by (core size, disjoint centers)", dict(sorted(counts.items())))
    print("word counts by (core size, disjoint centers)", dict(sorted(populations.items())))
    print("peelable normalization by disjoint centers, both checkerboards",
          {k: str(Fraction(2 * v, denominator)) for k, v in sorted(totals.items())})

    if source:
        print("peelable numerator by disjoint centers, both checkerboards",
              {k: str(Fraction(2 * v, 6 * denominator)) for k, v in sorted(numerators.items())})


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
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--even-center-census", action="store_true")
    parser.add_argument("--three-mixed-normalization", action="store_true")
    parser.add_argument("--three-mixed-source", action="store_true")
    args = parser.parse_args()
    if args.three_mixed_normalization or args.three_mixed_source:
        three_mixed(args.three_mixed_source)
    elif args.even_center_census:
        print("balanced words by mixed-center count", even_center_counts())
    else:
        main()
