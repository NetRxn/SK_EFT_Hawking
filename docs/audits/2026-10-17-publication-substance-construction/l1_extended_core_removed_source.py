"""Source terms that delete a residual curvature face and restore peeling."""
from collections import Counter
from fractions import Fraction
from math import factorial

from l1_extended_mixed_center_census import (
    curvature_boundary, orbits, source_total, swap_patterns, tensors,
)
from l1_extended_opposed import staged_center
from l1_extended_opposed_source import summed_fourth
from l1_extended_two_mixed_centers import mixed_center


def main():
    common = summed_fourth(1)
    normal, _ = staged_center(summed_fourth(0), common)
    mixed = mixed_center(common)
    frame_scale = 96**4 * 8**8
    divisor = (48 * frame_scale * factorial(4))**6
    divisor *= (48**2 * frame_scale * factorial(2)**2)**2
    total = Counter()
    count = Counter()
    for pattern, multiplicity in orbits(swap_patterns()):
        faces, protected = curvature_boundary(pattern)
        if not faces:
            continue
        for face in faces:
            rest, remaining_protected = curvature_boundary(pattern, omitted=face)
            assert not rest and remaining_protected == protected
        raw = source_total(pattern, tensors(pattern, normal, mixed), only_faces=faces)
        contribution = Fraction(2 * multiplicity * raw, 6 * divisor)
        count[len(faces)] += 1
        total[len(faces)] += contribution
        print("core faces", len(faces), "multiplicity", multiplicity,
              "weighted source contribution", contribution, flush=True)
    assert count == {2: 3, 4: 3}
    print("source subtotal by deleted core-face family", dict(sorted(total.items())))


if __name__ == "__main__":
    main()
