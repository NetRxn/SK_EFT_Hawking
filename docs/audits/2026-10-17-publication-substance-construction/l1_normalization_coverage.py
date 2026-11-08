"""Check the disjoint support partition underlying the exact normalization."""
from collections import Counter

from l1_normalization_shared_transport import TERMS, component_multisets
from l1_normalization_six_transport import sixth
from l1_normalization_six_mixed_chain import classify as mixed_chain
from l1_normalization_transport_cycle import pattern
from l1_normalization_paired_curvature import classify as private_curvature
from l1_normalization_correlated_cases import classify as correlated
from l1_normalization_diagonal_mixed import case_for


def sector(parts):
    word = tuple(index for part in parts for index in part)
    labels = [TERMS[index][2] for index in word]
    size = max(map(len, parts))
    if size <= 4:
        return "small components"
    if size == 6 and sixth(max(parts, key=len)):
        return "pure chain"
    if size == 6 and mixed_chain(max(parts, key=len)) is not None:
        return "mixed chain"
    if pattern(word) is not None:
        return "transport cycle increment"
    if all(label[1:3] == (0, 1) for label in labels):
        return "all local"
    if private_curvature(word) is not None:
        return "private repeated" if len(set(word)) == 4 else "private paired"
    if correlated(word) is not None:
        return "correlated six" if size == 6 else "correlated eight"
    if all(label[1:3] == (2, 3) for label in labels):
        assert sorted(Counter(label[0] for label in labels).values()) == [1, 1, 3, 3]
        return "odd commutator"
    if all(k < 2 and l >= 2 for _, k, l, _, _ in labels):
        if len({(x, k) for x, k, _, _, _ in labels}) == 8:
            return "mixed cycle"
        centers = {x: k for x, k, _, _, _ in labels}
        assert (len(set(word)) == 4 and len(centers) == 4
                and len({l for _, _, l, _, _ in labels}) == 1
                and centers[0] == centers[3] != centers[1] == centers[2])
        return "checkerboard"
    if case_for(word) is not None:
        return "diagonal mixed"
    assert size == 8 and len(set(word)) == 8
    sources = {x for x, k, l, _, _ in labels if (k, l) == (0, 1)}
    commutators = {x for x, k, l, _, _ in labels if (k, l) == (2, 3)}
    assert len(sources) == len(commutators) == 2
    a, b = sorted(sources)
    assert a ^ b == 3
    assert commutators == sources or commutators.isdisjoint(sources)
    mixed = [(x, k, l) for x, k, l, _, _ in labels if k < 2 and l >= 2]
    assert {(x, k) for x, k, _ in mixed} == {
        (x, k) for x in set(range(4)) - sources for k in range(2)
    }
    same = len({(x, l) for x, _, l in mixed}) == 2
    return ("X" if commutators == sources else "Y") + ("1" if same else "2")


if __name__ == "__main__":
    counts = Counter(map(sector, component_multisets()))
    for name, count in sorted(counts.items()):
        print(name, count)
    assert sum(counts.values()) == 6451
