"""Write both lower half-column inputs for the exact C++ join."""
from argparse import ArgumentParser
from pathlib import Path

from l1_extended_overlap_lower_halves import complement_project, fixed_pair, half_columns


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--separated-half", type=int, choices=(0, 1))
    args = parser.parse_args()
    output = args.output
    output.mkdir(parents=True, exist_ok=True)
    original = fixed_pair()
    halves = half_columns(complement_project(original))
    if args.separated_half is not None:
        from l1_extended_source_separated import twice_signed_lower_complements

        changed = half_columns(complement_project(original, twice_signed_lower_complements()))
        halves[args.separated_half] = changed[args.separated_half]
    for index, half in enumerate(halves):
        with (output / f"half{index}.rows").open("w") as stream:
            for key, value in sorted(half.items()):
                print(*key, *value, file=stream)
