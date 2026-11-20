"""Replay the extended-plane occurrence moment in the two private sectors."""
from collections import Counter
from fractions import Fraction
from math import factorial, prod
import sys

import l1_normalization_paired_paths as paired
import l1_normalization_private_paths as repeated
from l1_normalization_coverage import TERMS, component_multisets, sector


def moment(kind):
    kernel = {"private paired": paired, "private repeated": repeated}[kind]
    weighted_counts = Counter()
    words = 0
    for parts in component_multisets():
        if sector(parts) != kind:
            continue
        word = tuple(index for part in parts for index in part)
        count = sum(TERMS[index][2][1:3] == (0, 1) for index in word)
        if not count:
            continue
        words += 1
        plan = kernel.canonical(kernel.plan_for(word))
        haar = kernel.classify(word).count("Haar")
        # The repeated kernel already includes its multiplicity factorial.
        divisor = 1 if kernel is repeated else prod(
            factorial(n) for n in Counter(word).values()
        )
        weighted_counts[plan, haar, divisor] += count

    total = sum(
        count * kernel.scalar(plan)[0] * 2**haar
        * Fraction(16, 9)**(4 - haar) / divisor
        for (plan, haar, divisor), count in weighted_counts.items()
    )
    return words, total


if __name__ == "__main__":
    print(*moment(sys.argv[1]))
