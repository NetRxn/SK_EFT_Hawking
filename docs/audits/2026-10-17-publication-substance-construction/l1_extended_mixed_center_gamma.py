"""Local gamma sum at a mixed center with two residual faces."""
from argparse import ArgumentParser
from collections import Counter
from functools import cache
from itertools import combinations_with_replacement, product

from l1_direct_b_haar import add, scale, wedge
from l1_extended_mixed_frame_moment import SCALE, anchored, frame_edge, source_edge as probed_source_edge
from l1_extended_opposed_source import PAIRS, summed_fourth
from l1_extended_two_mixed_centers import (
    mixed_center, mixed_source_center, remap, second_channels, second_sum,
    source_edge, source_only,
)
from l1_normalization_opposed_fourth import L, tuples

COMPONENTS = tuple(combinations_with_replacement(range(6), 2))


@cache
def face_channels(components):
    """Ordered gamma occurrences grouped by the two symmetric frame pairs."""
    weights = Counter()
    for a, b, c, d in product(range(4), repeat=4):
        for i, u in L[a, c]:
            for j, v in L[b, d]:
                if tuple(sorted((i, j))) == components:
                    weights[tuple(sorted((a, b))), tuple(sorted((c, d)))] += u * v
    return {key: value for key, value in weights.items() if value}


@cache
def probed_edge(probe, endpoint):
    return {pair: remap(frame_edge(pair, 0, probe), (0, endpoint)) for pair in PAIRS}


def contract_gamma(first, common, last, first_weights, last_weights):
    terms = []
    for (a, u), weight in first_weights.items():
        for (b, v), second_weight in last_weights.items():
            mid = common[tuple(sorted(a + b))]
            if first[u] and mid and last[v]:
                exterior = wedge(wedge(first[u], mid), last[v])
                saturated = {m: c for m, c in exterior.items() if m & 255 == 255}
                terms.append(scale(saturated, weight * second_weight))
    return add(*terms)


def gamma_tensor(first_probe, last_probe, first_components, last_components, common):
    return contract_gamma(probed_edge(first_probe, 1), common, probed_edge(last_probe, 3),
                          face_channels(first_components), face_channels(last_components))


def gamma_products(first, common, last):
    """Cache exterior products for one set of directed frame moments."""
    @cache
    def left_product(u, labels):
        return wedge(first[u], common[labels])

    @cache
    def exterior(u, labels, v):
        return {mask: value for mask, value in wedge(left_product(u, labels), last[v]).items()
                if mask & 255 == 255}

    return exterior


def contract_gamma_products(exterior, first_weights, last_weights):
    return add(*(scale(exterior(u, tuple(sorted(a + b)), v), weight * other)
                 for (a, u), weight in first_weights.items()
                 for (b, v), other in last_weights.items()))


def gamma_block(first_probe, last_probe, common):
    """Share exterior products across component rows for one probe pair."""
    exterior = gamma_products(probed_edge(first_probe, 1), common, probed_edge(last_probe, 3))

    def components(first_components, last_components):
        return contract_gamma_products(exterior, face_channels(first_components),
                                       face_channels(last_components))

    return components


@cache
def peeled_channels():
    weights = Counter()
    for a, b, weight in second_channels():
        weights[tuple(sorted(a)), b] += weight
    return dict(weights)


def opposite_center(probes, *, fixed=()):
    """Axes are exclusive, common, exclusive. Fixed slots are one-based."""
    assert all(probes[i - 1] is None for i in fixed)
    first, common, last = (
        opposite_edge(i, (probe,) if probe is not None or i in fixed else None)
        for i, probe in enumerate(probes, start=1)
    )
    weights = peeled_channels()
    return contract_gamma(first, common, last, weights, weights)


@cache
def opposite_edge(site, probes):
    labels = tuples if site == 2 else PAIRS
    if probes is None:
        if site == 2:
            return summed_fourth(1)
        table = second_sum(0)
    else:
        table = {g: add(*(frame_edge(g, 1, probe) for probe in probes)) for g in labels}
    return {g: remap(poly, (0, site)) for g, poly in table.items()}


@cache
def opposite_source_edge(site, probes):
    if site == 2:
        if probes is None:
            return {g: add(*(source_edge(1, endpoint)[g] for endpoint in range(2)))
                    for g in PAIRS}
        return {g: remap(add(*(probed_source_edge(g, 1, probe, endpoint)
                               for probe in probes for endpoint in range(2))), (0, site))
                for g in PAIRS}

    if probes is None:
        return remap(add(source_only(0), source_only(1)), (0, site))
    terms = []
    for probe, endpoint, gamma in product(probes, range(2), range(4)):
        first = anchored(0, (), (), gamma if endpoint == 0 else None)
        last = anchored(1, (), probe, gamma if endpoint == 1 else None)
        terms.append(wedge(first, last))
    return remap(add(*terms), (0, site))


def opposite_source(removed, probes, *, fixed=()):
    """Replace the plane containing the given exclusive slot by a source pair."""
    assert removed in (1, 3) and all(probes[i - 1] is None for i in fixed)
    slots = tuple((p,) if p is not None or i in fixed else None
                  for i, p in enumerate(probes, 1))
    return opposite_source_tensor(removed, slots)


def opposite_source_tensor(removed, slots):
    survivor = 4 - removed
    common = opposite_source_edge(2, slots[1])
    other = opposite_edge(survivor, slots[survivor - 1])
    source = opposite_source_edge(removed, slots[removed - 1])
    retained = add(*(scale(wedge(common[a], other[b]), weight)
                     for (a, b), weight in peeled_channels().items()))
    return {mask: value for mask, value in wedge(retained, source).items()
            if mask & 255 == 255}


def verify_opposite_source():
    for removed, protected in product((1, 3), ((1, 3), (1, 2), (2, 3))):
        reference = add(*(mixed_source_center(removed, a, b)
                          for a, b in product(range(2), repeat=2)))
        degree = sum(4 if i == 2 else 2 for i in protected)
        raw_scale = 96**(degree // 2) * 8**degree
        probe_scale = SCALE**(2 * len(protected)) * 4**degree
        for chirality in (0, 1):
            diagonal = tuple((i, i) for i in range(4 * chirality, 4 * chirality + 4))
            slots = tuple(diagonal if i in protected else None for i in (1, 2, 3))
            trace = opposite_source_tensor(removed, slots)
            assert scale(trace, raw_scale) == scale(reference, probe_scale)
        live, fixed = protected
        probes = tuple((0, 0) if i == live else None for i in (1, 2, 3))
        row = opposite_source(removed, probes, fixed=(fixed,))
        assert row and all(tuple(((mask >> (8*i)) & 255).bit_count() for i in range(4))
                           == (8, 2, 4, 2) for mask in row)
        print("removed slot", removed, "protected slots", protected,
              "both chiral source traces passed", flush=True)


def verify_opposite_geometry():
    from l1_extended_mixed_center_census import (
        EVEN, curvature_boundary, orbits, words_with_mixed_count,
    )
    from l1_extended_two_face_gamma_join import pure_links

    count = Counter()
    for pattern, _ in orbits(words_with_mixed_count(3)):
        faces, protected = curvature_boundary(pattern)
        links = set().union(*faces.values())
        if len(faces) != 2 or len(links - protected) != 1:
            continue
        base, = {face[0] for face in faces}
        live = set()
        for face, edges in faces.items():
            upper, _, center = pure_links(face, edges, protected)
            live.add(upper[0])
            planes = pattern[EVEN.index(center)]
            degrees = tuple(sorted(2 * sum(a in p for p in planes) for _, a in upper))
            count[degrees] += 1
        tree = links - live
        reached = {base}
        for _ in tree:
            for x, a in tree:
                y = x ^ (1 << a)
                if x in reached or y in reached:
                    reached.update((x, y))
        vertices = {y for x, a in links for y in (x, x ^ (1 << a))}
        assert len(live) == 2 and len(tree) == 5 and len(vertices) == 6
        assert reached == vertices
    assert count == {(2, 2): 104, (2, 4): 44, (4, 4): 12}
    print("80 spanning tree checks passed, role counts", dict(count), flush=True)


def verify_opposite():
    verify_opposite_geometry()
    weights = peeled_channels()
    reference = mixed_center(opposite_edge(2, None))
    for protected in ((1, 3), (1, 2), (2, 3)):
        for chirality in (0, 1):
            diagonal = tuple((i, i) for i in range(4 * chirality, 4 * chirality + 4))
            first, common, last = (
                opposite_edge(site, diagonal if site in protected else None)
                for site in (1, 2, 3)
            )
            value = contract_gamma(first, common, last, weights, weights)
            degree = sum(4 if i == 2 else 2 for i in protected)
            raw_scale = 96**(degree // 2) * 8**degree
            probe_scale = SCALE**(2 * len(protected)) * 4**degree
            assert scale(value, raw_scale) == scale(reference, probe_scale)
        row = opposite_center(tuple((0, 0) if site in protected else None for site in (1, 2, 3)))
        assert row
        assert all(tuple(((mask >> (8 * i)) & 255).bit_count() for i in range(4))
                   == (8, 2, 4, 2) for mask in row)
        live, fixed = protected
        probes = tuple((0, 0) if site == live else None for site in (1, 2, 3))
        fixed_row = opposite_center(probes, fixed=(fixed,))
        assert fixed_row
        assert all(mask & 255 == 255 for mask in fixed_row)
        print("protected slots", protected, "exact trace match, live and fixed row entries",
              len(row), len(fixed_row), flush=True)


def verify_norm(common):
    reference = mixed_center(common)
    # Independent Haar on each face selects identical components and
    # contributes 48 * E[q_i²] = 12 for each selected diagonal.
    weights = Counter()
    for i in range(6):
        for pair, value in face_channels((i, i)).items():
            weights[pair] += 12 * value
    for chirality in (0, 1):
        probes = [(i, i) for i in range(4*chirality, 4*chirality + 4)]
        first, last = ({pair: add(*(probed_edge(probe, endpoint)[pair] for probe in probes))
                        for pair in PAIRS} for endpoint in (1, 3))
        result = contract_gamma(first, common, last, weights, weights)
        assert scale(result, (96 * 2**2)**2) == scale(reference, SCALE**4)
        print("independent-Haar norm control", chirality, len(result), flush=True)


def verify_core_roles():
    from l1_extended_mixed_center_census import EVEN, curvature_boundary, orbits, swap_patterns

    for pattern, _ in orbits(swap_patterns()):
        faces, protected = curvature_boundary(pattern)
        if not faces:
            continue
        core_links = {edge for links in faces.values() for edge in links}
        based = Counter(x for x, _, _ in faces)
        for x, count in based.items():
            first, last = pattern[EVEN.index(x)]
            assert count == 2 and len(set(first) & set(last)) == 1
            for axis in set(first) ^ set(last):
                assert (x, axis) in core_links & protected
                assert (x ^ (1 << axis), axis) not in core_links
            shared, = set(first) & set(last)
            assert not core_links & {(x, shared), (x ^ (1 << shared), shared)}


def main():
    verify_core_roles()
    common = summed_fourth(1)
    verify_norm(common)
    for probes in (((0, 0), (0, 0)), ((0, 4), (0, 4))):
        sizes = [len(gamma_tensor(*probes, a, b, common))
                 for a, b in product(COMPONENTS, repeat=2)]
        print("probes", probes, "live component rows", sum(bool(n) for n in sizes),
              "exterior entries", sum(sizes), flush=True)


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--opposite-center", action="store_true")
    mode.add_argument("--opposite-source", action="store_true")
    args = parser.parse_args()
    if args.opposite_source:
        verify_opposite_source()
    elif args.opposite_center:
        verify_opposite()
    else:
        main()
