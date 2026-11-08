"""Count normalization words killed by independent odd curvature moments."""
from collections import Counter

from l1_normalization_support import TERMS, normalization_support


def odd_commutator_words():
    for indices in normalization_support():
        labels = [TERMS[index][2] for index in indices]
        if all(label[1:3] == (2, 3) for label in labels):
            counts = Counter(label[0] for label in labels)
            if any(count % 2 for count in counts.values()):
                yield indices, tuple(sorted(counts.values()))


if __name__ == "__main__":
    population = Counter(profile for _, profile in odd_commutator_words())
    assert population == {(1, 1, 3, 3): 800}
    print("odd independent curvature words", dict(population))
