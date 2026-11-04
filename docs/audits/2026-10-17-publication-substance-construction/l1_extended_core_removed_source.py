"""Source terms that delete a residual curvature face and restore peeling."""
from argparse import ArgumentParser
from collections import Counter
from fractions import Fraction
from math import factorial

from l1_extended_mixed_center_census import (
    curvature_boundary, disjoint_center, orbits, source_total, swap_patterns, tensors,
    words_with_mixed_count,
)
from l1_extended_one_face_gauge_join import check_removals
from l1_extended_opposed import staged_center
from l1_extended_opposed_source import summed_fourth
from l1_extended_two_mixed_centers import mixed_center


def main(three_mixed=False):
    common = summed_fourth(1)
    normal, _ = staged_center(summed_fourth(0), common)
    mixed = mixed_center(common)
    frame_scale = 96**4 * 8**8
    mixed_count = 3 if three_mixed else 2
    divisor = (48 * frame_scale * factorial(4))**(8 - mixed_count)
    divisor *= (48**2 * frame_scale * factorial(2)**2)**mixed_count
    disjoint = disjoint_center() if three_mixed else None
    patterns = words_with_mixed_count(3) if three_mixed else swap_patterns()
    population = Counter()
    retained = Counter()
    total = Counter()
    count = Counter()
    for pattern, multiplicity in orbits(patterns):
        faces, protected = curvature_boundary(pattern)
        if not faces:
            continue
        if three_mixed:
            if len(faces) != 2:
                continue
            check_removals(pattern)
            if set.union(*faces.values()) <= protected:
                assert all(len(curvature_boundary(pattern, omitted=f)[0]) == 1 for f in faces)
                retained["orbits"] += 1
                retained["words"] += multiplicity
                continue
        for face in faces:
            rest, remaining_protected = curvature_boundary(pattern, omitted=face)
            assert not rest and remaining_protected == protected
        raw = source_total(pattern, tensors(pattern, normal, mixed, disjoint), only_faces=faces)
        contribution = Fraction(2 * multiplicity * raw, 6 * divisor)
        count[len(faces)] += 1
        population[len(faces)] += multiplicity
        total[len(faces)] += contribution
        print("core faces", len(faces), "multiplicity", multiplicity,
              "weighted source contribution", contribution, flush=True)
    if three_mixed:
        assert count == {2: 80} and population == {2: 15072}
        assert retained == {"orbits": 23, "words": 3744}
        print("three-mixed orbit and word counts", dict(count), dict(population), dict(retained))
    else:
        assert count == {2: 3, 4: 3}
    print("source subtotal by deleted core-face family", dict(sorted(total.items())))


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--two-face-deleted-source", action="store_true")
    main(parser.parse_args().two_face_deleted_source)
