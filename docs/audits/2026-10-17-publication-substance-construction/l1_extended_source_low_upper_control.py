"""Check the complete lower half-tensor reuse for the selected source family."""
from fractions import Fraction

from l1_extended_overlap_lower_halves import complement_project, fixed_pair, half_columns
from l1_extended_source_low_upper import low_upper_complements
from l1_extended_source_separated import twice_signed_lower_complements


if __name__ == "__main__":
    fixed = fixed_pair()
    baseline = half_columns(complement_project(fixed))
    separated = half_columns(complement_project(fixed, twice_signed_lower_complements()))
    for site in (2, 3):
        unshared = half_columns(complement_project(fixed, low_upper_complements(site, False)))
        shared = half_columns(complement_project(fixed, low_upper_complements(site, True)))
        for position, (base, sep, a, c) in enumerate(zip(
            baseline, separated, unshared, shared, strict=True
        )):
            assert base.keys() == sep.keys() == a.keys() == c.keys()
            for key in base:
                assert all(
                    2 * u == s and 2 * v == 5 * s - 6 * b
                    for b, s, u, v in zip(base[key], sep[key], a[key], c[key], strict=True)
                ), (site, position, key)
            print(f"Site {site}, half {position}: {len(base):,} exact coefficient matches")

    same = Fraction(-60445514255728976151, 9903520314283042199192993792)
    separated_sum = Fraction(-45709102752653698569, 4951760157141521099596496896)
    shared_sum = (5 * separated_sum - 3 * same) / 2
    print("Shared lower–upper subtotal", shared_sum)
    print("All selected source replacements", same + 2 * separated_sum + shared_sum)
