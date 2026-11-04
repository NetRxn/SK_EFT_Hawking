"""Local gamma sum at a mixed center with two residual faces."""
from collections import Counter
from functools import cache
from itertools import combinations_with_replacement, product

from l1_direct_b_haar import add, scale, wedge
from l1_extended_mixed_frame_moment import SCALE, frame_edge
from l1_extended_opposed_source import PAIRS, summed_fourth
from l1_extended_two_mixed_centers import mixed_center, remap, second_sum
from l1_normalization_opposed_fourth import L

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


def gamma_block(first_probe, last_probe, common):
    """Share exterior products across component rows for one probe pair."""
    first = probed_edge(first_probe, 1)
    last = probed_edge(last_probe, 3)

    @cache
    def left_product(u, labels):
        return wedge(first[u], common[labels])

    @cache
    def exterior(u, labels, v):
        return {mask: value for mask, value in wedge(left_product(u, labels), last[v]).items()
                if mask & 255 == 255}

    def components(first_components, last_components):
        return add(*(scale(exterior(u, tuple(sorted(a + b)), v), weight * other)
                     for (a, u), weight in face_channels(first_components).items()
                     for (b, v), other in face_channels(last_components).items()))

    return components


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
    main()
