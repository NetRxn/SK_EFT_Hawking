"""Necessary source-supported cut condition for the selected unpaired word."""

from collections import defaultdict
from itertools import combinations, product

from l1_unpaired_offset_factors import FRAME_PLANES, SLOTS, SOURCES, gkey, prepare, qkey
from l1_unpaired_signed_slice import CUT_EDGES, FIXED, VARYING
from l1_unpaired_upper_support import contract_env, upper_support, values_of

ALL = tuple(range(8))
NONSCALE = (1, 2, 3, 5, 6, 7)
CUT = ((5, 1), (5, 3), (7, 1), (7, 3), (13, 3), (15, 1), (15, 3))
DOMAINS = (NONSCALE, NONSCALE, ALL, ALL, ALL, ALL, ALL)


def cut_domains(half, labels):
    domains = {label: set(ALL) for label in labels}
    for keys, rows, _ in half:
        for i, key in enumerate(keys):
            if key in domains:
                observed = {row[i] for row in rows}
                assert observed <= set(ALL)
                domains[key].intersection_update(observed)
    return domains


def projected_counts(factors):
    """Yield each guarded coordinate tuple and its necessary support count."""
    centers = dict(zip(sorted(FRAME_PLANES), factors[:15], strict=True))
    edges = dict(zip(sorted(SLOTS), factors[15:-2], strict=True))
    sources = dict(zip(SOURCES, factors[-2:], strict=True))
    a = [f for site, f in centers.items() if not site & 4]
    a.extend(f for edge, f in edges.items() if edge not in CUT_EDGES)
    a.extend(sources.values())
    b = [f for site, f in centers.items() if site & 4]
    b.extend(f for edge, f in edges.items() if edge in CUT_EDGES)
    assert len(a) == len(b) == 20
    labels = tuple(map(qkey, CUT))
    assert {k for keys, _, _ in a for k in keys} & {k for keys, _, _ in b for k in keys} == set(labels)
    domains_a, domains_b = (cut_domains(half, labels) for half in (a, b))
    assert tuple(tuple(sorted(domains_a[k] & domains_b[k])) for k in labels) == DOMAINS
    for site, source in ((4, (0, 2)), (5, (1, 2))):
        assert [f for f in a if site in f[2]] == [sources[source]]
        assert sources[source][0] == ()

    upper = contract_env([centers[x] for x in (12, 13, 14, 15)]
                         + [edges[e] for e in ((8, 2), (10, 2), (12, 0), (12, 1), (14, 0))])
    lower = contract_env([centers[x] for x in (4, 6, 7)]
                         + [edges[e] for e in ((4, 0), (4, 1), (6, 0))]
                         + list(sources.values()))
    assert lower[2] == {0: 2, 1: 2, 5: 4, 7: 4}
    assert len(lower[1]) == 4 and sum(map(len, lower[1].values())) == 5040

    gamma7 = gkey(7, 3)
    gamma51, gamma53 = gkey(5, 1), gkey(5, 3)
    base = values_of(lower, (gamma7,), (5, 7))
    incoming = values_of(edges[5, 1], (labels[0], labels[2], gamma51), (5, 7))
    side = values_of(edges[5, 3], (labels[1], labels[4], gamma53), (5, 13))
    outgoing = values_of(edges[7, 3], (labels[3], labels[6], gamma7), (7, 15))
    high, _ = upper_support(upper, edges[13, 1])
    assert set(high) == set(ALL)

    # Site 5's center constrains the gamma pair; retain that relation.
    center_gammas = defaultdict(set)
    indexes = tuple(centers[5][0].index(g) for g in (gamma51, gamma53))
    for row in centers[5][1]:
        u, v = (row[i] for i in indexes)
        center_gammas[u].add(v)
    lower_index = {}
    for q51, q71 in product(NONSCALE, ALL):
        masks = defaultdict(set)
        for u, side_gammas in center_gammas.items():
            for m5, m7 in incoming[q51, q71, u]:
                for (g,), rows in base.items():
                    for b5, b7 in rows:
                        if not (m5 & b5 or m7 & b7):
                            masks[g, 255 ^ (m7 | b7)].update(
                                (v, 255 ^ (m5 | b5)) for v in side_gammas)
        lower_index[q51, q71] = masks

    side_index = {}
    for q53, q133 in product(NONSCALE, ALL):
        masks = defaultdict(set)
        for v in set().union(*center_gammas.values()):
            for m5, m13 in side[q53, q133, v]:
                masks[v, m5].add(m13)
        side_index[q53, q133] = masks
    outgoing_index = defaultdict(list)
    for (q73, q153, g), rows in outgoing.items():
        outgoing_index[q73, q153].extend((g, m7, m15) for m7, m15 in rows)

    two_bits = tuple((1 << i) | (1 << j) for i, j in combinations(range(8), 2))
    pair_codes = {pair: i for i, pair in enumerate(product(two_bits, repeat=2))}
    high_bits = {q: sum(1 << pair_codes[pair] for pair in high[q]) for q in ALL}
    for q51, q71, q73, q153 in product(NONSCALE, ALL, ALL, ALL):
        low = lower_index[q51, q71]
        reachable = {(v, m5, m15) for g, m7, m15 in outgoing_index[q73, q153]
                     for v, m5 in low[g, m7]}
        for q53, q133 in product(NONSCALE, ALL):
            side_masks = side_index[q53, q133]
            pairs = {(m13, m15) for v, m5, m15 in reachable for m13 in side_masks[v, m5]}
            bits = sum(1 << pair_codes[pair] for pair in pairs)
            for q151 in ALL:
                yield (q51, q53, q71, q73, q133, q151, q153), (bits & high_bits[q151]).bit_count()


def surviving_tuples(factors):
    """Yield support survivors in deterministic order, in CUT coordinate order."""
    for word, count in projected_counts(factors):
        if count:
            yield word


def main():
    controls = {(1, 1, 1, 1, 1, 1, 1), (1, 1, 1, 1, 1, 5, 1),
                (1, 1, 1, 1, 1, 1, 5), (5, 1, 1, 1, 1, 1, 1)}
    fiber = [tuple((FIXED | {VARYING: q})[edge] for edge in CUT) for q in ALL]
    checked = {}
    tested = survivors = 0
    for word, count in projected_counts(prepare()):
        tested += 1
        survivors += bool(count)
        if word in controls or word in fiber:
            checked[word] = count
    assert tested == 1_179_648 and survivors == 124_416
    assert all(checked[word] == 0 for word in controls)
    fiber_counts = [checked[word] for word in fiber]
    assert fiber_counts == [96, 0, 0, 96, 96, 0, 0, 96]
    print("source-supported cut survivors", survivors, "excluded", tested - survivors)
    print("known-zero controls excluded", len(controls), "signed fiber support", fiber_counts)


if __name__ == "__main__":
    main()
