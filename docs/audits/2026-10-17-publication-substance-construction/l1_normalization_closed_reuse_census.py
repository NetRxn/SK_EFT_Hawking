"""Count closed-order reuse while retaining conditional singleton incidence."""

from collections import Counter

from l1_normalization_coverage import TERMS, component_multisets, sector
from l1_normalization_shared_transport import forward


def reusable(word):
    """Peel private curvature and keep any link retained in a conditional tensor."""
    incidence = Counter()
    plaquettes = {}
    for index in word:
        x, k, l, u, v = TERMS[index][2]
        m, n = (axis for axis in range(4) if axis not in (k, l))
        incidence.update(((u, m), (v, n)))
        plaquettes[x, k, l] = Counter((
            (x, k), (forward(x, k), l), (forward(x, l), k), (x, l),
        ))
    for ports in plaquettes.values():
        incidence.update(ports)

    while plaquettes:
        for key, ports in sorted(plaquettes.items()):
            unique = any(ports[z] == incidence[z] == 1 for z in ports)
            commutator = len(ports) == 2 and all(
                ports[z] == incidence[z] == 2 for z in ports
            )
            if unique or commutator:
                incidence.subtract(plaquettes.pop(key))
                break
        else:
            for key, ports in sorted(plaquettes.items()):
                x, k, l = key
                if k < 2 <= l and ports[x, k] == incidence[x, k] == 2:
                    del plaquettes[key]
                    # The average still depends on both transverse links.
                    incidence[x, k] -= 2
                    break
            else:
                return False
    return True


def cross_weight(word):
    slices = [0, 0]
    polarization = (0, 0, 1, -1)
    for index in word:
        x, k, l, _, _ = TERMS[index][2]
        slices[x & 1] -= polarization[k] + polarization[l]
    return slices[0] * slices[1]


if __name__ == "__main__":
    counts = Counter()
    for parts in component_multisets():
        word = tuple(index for part in parts for index in part)
        counts[reusable(word), sector(parts), bool(cross_weight(word))] += 1
    for label, count in sorted(counts.items()):
        print(label, count)
    reused = sum(n for (reuse, _, _), n in counts.items() if reuse)
    weighted = sum(n for (reuse, _, weight), n in counts.items() if reuse and weight)
    assert (reused, weighted) == (5718, 1812)
    assert sum(counts.values()) == 6451
    print("reusable normalization and cross support", reused, weighted)
