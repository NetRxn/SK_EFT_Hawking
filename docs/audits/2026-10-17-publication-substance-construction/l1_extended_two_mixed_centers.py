"""Exact fourth-power checkerboard word with two mixed-plane centers."""
from collections import Counter
from fractions import Fraction
from functools import cache
from itertools import permutations, product
from math import factorial

from l1_direct_b_haar import R, add, scale, wedge
from l1_extended_mixed_plane import EVEN
from l1_extended_opposed import curvature, staged_center
from l1_extended_opposed_source import PAIRS, action_frame, frame, modified_center, source_frames, summed_fourth
from l1_normalization_opposed_fourth import nodes


def second_sum(direction):
    result = {pair: {} for pair in PAIRS}
    for left, right, weight in nodes():
        for anchor in (0, 1):
            frame = action_frame(direction, anchor, left, right)
            for a, b in PAIRS:
                result[a, b] = add(result[a, b], scale(wedge(frame[a], frame[b]), weight))
    return result


def remap(poly, sites):
    return {sum(((m >> (8*i)) & 255) << (8*x) for i, x in enumerate(sites)): c
            for m, c in poly.items()}


def second_channels():
    for a, b, c, d in product(range(4), repeat=4):
        weight = curvature(tuple(sorted(((a, c), (b, d)))))
        if weight:
            yield (a, b), tuple(sorted((c, d))), weight


def mixed_center(common):
    # Use temporary odd sites 1, 2, 3 for axes 0, 2, 3.
    other = {k: remap(v, (0, 1)) for k, v in second_sum(0).items()}
    last = {k: remap(v, (0, 3)) for k, v in second_sum(0).items()}
    channels = tuple(second_channels())
    out = {}
    for (a, b), u, weight in channels:
        for (c, d), v, second_weight in channels:
            exterior = wedge(wedge(other[u], common[tuple(sorted((a, b, c, d)))]), last[v])
            saturated = {m: w for m, w in exterior.items() if m & 255 == 255}
            out = add(out, scale(saturated, weight * second_weight))
    return out


def word():
    return [(x, n, frame) for x in EVEN for n, frame in (
        ((2, (0, 2)), (2, (2, 3))) if x in (0, 9) else ((4, (2, 3)),))]


def orbit_size():
    images = set()
    for axes, translation in product(permutations(range(4)), range(16)):
        image = []
        for x, n, frame in word():
            site = sum(((x >> a) & 1) << axes[a] for a in range(4)) ^ translation
            image.append((site, n, tuple(sorted(axes[a] for a in frame))))
        images.add(tuple(sorted(image)))
    return len(images)


def check_word():
    faces = {}
    protected = set()
    degree = Counter()
    for x, n, frame in word():
        for a in frame:
            y = x ^ (1 << a)
            protected.update(((x, a), (y, a)))
            degree[y] += n
        k, l = (a for a in range(4) if a not in frame)
        faces[x, k, l] = {(x, k), (x ^ (1 << k), l), (x ^ (1 << l), k), (x, l)}
    assert len(degree) == 8 and set(degree.values()) == {8}
    while faces:
        counts = Counter(e for edges in faces.values() for e in edges)
        private = next(x for x, edges in faces.items()
                       if any(counts[e] == 1 and e not in protected for e in edges))
        del faces[private]


def contract(terms):
    # Drop each fully saturated site after its final incident tensor.
    incident = {x: sum(255 << (8*i) for i in range(16)
                       if any(m & (255 << (8*i)) for m in row))
                for x, row in terms.items()}

    @cache
    def remaining_sites(todo):
        mask = 0
        for x in todo:
            mask |= incident[x]
        return mask

    state = {0: R.one}
    todo = tuple(terms)
    while todo:
        x = min(todo, key=lambda x: ((remaining_sites(todo) ^ remaining_sites(
            tuple(y for y in todo if y != x))).bit_count() * -1, x))
        todo = tuple(y for y in todo if y != x)
        closed = incident[x] & ~remaining_sites(todo)
        joined = wedge(state, terms[x])
        state = {m ^ closed: value for m, value in joined.items() if m & closed == closed}
    return state.get(0, R.zero)


@cache
def source_edge(direction, endpoint):
    a, b = (source_frames(direction, anchor)[endpoint] for anchor in (0, 1))
    return {pair: add(a[pair], b[pair]) for pair in PAIRS}


@cache
def source_only(endpoint):
    return add(*(scale(add(*(wedge(t, t) for t in frame(0, bool(endpoint), left, right))), weight)
                 for left, right, weight in nodes()))


def mixed_source_center(removed_site, common_endpoint, other_endpoint):
    # Of the two noncommon local sites 1 and 3, one carries the
    # remaining action frame and the other a source on its own edge.
    survivor = 4 - removed_site
    second = second_sum(0)
    common = source_edge(1, common_endpoint)
    out = {}
    for pair, other, weight in second_channels():
        # The second curvature tensor is symmetric under exchanging its
        # frame axes (both factors reverse sign).
        out = add(out, scale(wedge(remap(second[other], (0, survivor)),
                                   common[tuple(sorted(pair))]), weight))
    g = remap(source_only(other_endpoint), (0, removed_site))
    return {m: c for m, c in wedge(out, g).items() if m & 255 == 255}


def numerator(terms, denominator, baseline_axes):
    values = Counter()
    removed_site = 3 if baseline_axes else 1
    for common, other in product(range(2), repeat=2):
        mixed = mixed_source_center(removed_site, common, other)
        normal = modified_center(source_edge(0, common), source_edge(1, other)) if baseline_axes else {}
        for x in EVEN:
            changed = dict(terms)
            if x in (0, 9):
                changed[x] = remap(mixed, (x, x ^ 1, x ^ 4, x ^ 8))
                adjustment = 48 * factorial(2)
            elif baseline_axes:
                changed[x] = remap(normal, (x, x ^ 4, x ^ 8))
                adjustment = factorial(4) // factorial(2)
            else:
                continue
            raw = contract(changed)
            assert raw.is_ground and not raw.const().y
            # Opposite shear signs and two ordered source assignments.
            values[common, other] += Fraction(-2 * adjustment * int(raw.const().x), denominator)
    return values


def main():
    check_word()
    common = summed_fourth(1)
    normal, _ = staged_center(summed_fourth(0), common)
    frame_scale = 96**4 * 8**8
    normal_scale = 48 * frame_scale * factorial(4)
    control = contract({x: remap(normal, (x, x ^ 4, x ^ 8)) for x in EVEN})
    assert control.is_ground and not control.const().y
    assert Fraction(int(control.const().x), normal_scale**8) == Fraction(
        9982511481025756988525390625, 295147905179352825856)
    mixed = mixed_center(common)
    terms = {x: remap(mixed, (x, x ^ 1, x ^ 4, x ^ 8)) if x in (0, 9)
             else remap(normal, (x, x ^ 4, x ^ 8)) for x in EVEN}
    raw = contract(terms)
    assert raw.is_ground and not raw.const().y
    denominator = normal_scale**6
    denominator *= (48**2 * frame_scale * factorial(2)**2)**2
    print("mixed center terms", len(mixed))
    coefficient = Fraction(int(raw.const().x), denominator)
    print("two mixed centers coefficient", coefficient)
    size = orbit_size()
    print("axis-permutation and translation orbit", size, size * coefficient, flush=True)
    baseline = numerator(terms, denominator, True)
    secondary = numerator(terms, denominator, False)
    print("baseline-plane source by endpoint", dict(baseline))
    print("secondary-plane source by endpoint", dict(secondary))
    # A specified unordered frame pair occurs in one sixth of each
    # orbit role. The baseline and secondary pairs are distinct.
    assert size % 6 == 0
    print("orbit source numerator", (size // 6) * (sum(baseline.values()) + sum(secondary.values())))


if __name__ == "__main__":
    main()
