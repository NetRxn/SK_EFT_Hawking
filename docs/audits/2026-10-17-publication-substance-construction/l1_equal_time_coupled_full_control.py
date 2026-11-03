"""Run all 40 coupled words without a symmetry reduction."""
from collections import Counter
from fractions import Fraction

from l1_equal_time_coupled import solve
from l1_equal_time_structural import (
    frame_links, incidence, reduce_source_dependence, same_site_quadratic_support,
)


def main():
    outcomes = Counter()
    for word in same_site_quadratic_support():
        _, removed = reduce_source_dependence(word)
        if removed:
            continue
        frames = frame_links(word)
        planes = {term[:3] for term in word}
        for x, axis in ((1, 0), (2, 1)):
            key = x, axis
            assert not frames[key]
            assert {plane for plane in planes if key in incidence(*plane)} == {
                (x, axis, 2), (x, axis, 3)
            }
            assert all(incidence(x, axis, j).count(key) == 2 for j in (2, 3))
        value = solve(word)
        outcomes[value] += 1
        print('word', word, 'value', value, flush=True)
    assert sum(outcomes.values()) == 40
    subtotal = sum(value * count for value, count in outcomes.items())
    assert subtotal == Fraction(-23063, 32)
    print('all coupled exact', sorted(outcomes.items()), 'subtotal', subtotal)


if __name__ == '__main__':
    main()
