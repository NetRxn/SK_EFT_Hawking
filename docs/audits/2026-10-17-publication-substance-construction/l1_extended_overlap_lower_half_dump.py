"""Write both lower half-column inputs for the exact C++ join."""
from pathlib import Path
from sys import argv

from l1_extended_overlap_lower_halves import complement_project, fixed_pair, half_columns


if __name__ == "__main__":
    output = Path(argv[1])
    output.mkdir(parents=True, exist_ok=True)
    for index, half in enumerate(half_columns(complement_project(fixed_pair()))):
        with (output / f"half{index}.rows").open("w") as stream:
            for key, value in sorted(half.items()):
                print(*key, *value, file=stream)
