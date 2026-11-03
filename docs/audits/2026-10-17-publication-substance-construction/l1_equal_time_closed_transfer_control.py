"""Verify the finite equal-time transfer under plaquette-order reversal."""
from collections import Counter
from fractions import Fraction
from itertools import product

from l1_equal_time_coupled import TYPES, local_center, projected_curvature
from l1_equal_time_structural import (
    frame_links,
    incidence,
    reduce_source_dependence,
    same_site_quadratic_support,
)


def main():
    changes = sum(
        projected_curvature(a, b, r, ch, p)
        != projected_curvature(a, b, r, ch, p, closed=True)
        for a, b, r, ch, p in product(range(4), range(4), range(4), range(2), range(1, 4))
    )
    assert changes == 48
    for site, source_type in product((1, 2), TYPES):
        literal = local_center(site, source_type)
        closed = local_center(site, source_type, closed=True)
        assert literal == closed
        count = sum(sum(bool(real or imag) for real, imag in row.values())
                    for row in closed.values())
        assert count == (104 if source_type[0] % 4 == 0 else 96)
        print("reduced center", site, source_type, count)

    cases = Counter()
    source_links = {(0, 2), (0, 3)}
    for word in same_site_quadratic_support():
        source_degrees, removed = reduce_source_dependence(word)
        if not removed:
            assert source_degrees == (2, 2)
            cases["coupled"] += 1
            continue
        assert source_degrees == (0, 0)
        remaining = Counter(term[:3] for term in word if term[:3] not in removed)
        if not remaining:
            cases["private Haar only"] += 1
            continue
        ((plane, multiplicity),) = remaining.items()
        assert plane[1:] == (2, 3) and multiplicity == 2
        assert set(incidence(*plane)).isdisjoint(source_links | frame_links(word).keys())
        cases["private Haar and isolated commutator"] += 1
    assert cases == {
        "coupled": 40,
        "private Haar only": 41,
        "private Haar and isolated commutator": 104,
    }
    # The 145 privately reduced words reuse the prior exact contraction.
    # Run l1_equal_time_coupled_full_control.py --closed for the 40-word subtotal.
    print("raw order changes", changes, "with equal reduced tensors")
    print("transfer populations", dict(cases))
    print("closed same-site coefficient", Fraction(318843) - Fraction(23063, 32))


if __name__ == "__main__":
    main()
