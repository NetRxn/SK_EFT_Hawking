"""Rebuild and replay the exact diagonal composite numerator in either ordering."""

from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction
from functools import cache
from pathlib import Path
import os
import re
import subprocess
import sys

import l1_mixed_center_contract as center
import l1_residual_sparse_sources as residual
import l1_shift_group_contract as shifted


AUDIT = Path(__file__).resolve().parent
SLICE = re.compile(r"^slice ([0-9 ]+)$", re.MULTILINE)
EXACT = re.compile(
    r"\bexact(?: slice (\d+ \d+ \d+ \d+))? "
    r"scaled Gaussian \((-?\d+),(-?\d+)\)/5308416$",
    re.MULTILINE,
)
ZERO = (Fraction(0), Fraction(0))


def compile_evaluators(output, closed):
    files = (
        "l1_sparse_center_dual", "l1_sparse_center_parity_dual",
        "l1_sparse_center_mixed_dual", "l1_sparse_center_mixed_parity_dual",
        "l1_sparse_center_shift_dual", "l1_sparse_center_shift_parity",
        "l1_residual_batched",
    )
    flag = ["-DL1_CLOSED_ORDER"] if closed else []
    for name in files:
        subprocess.run(
            [os.environ.get("CXX", "c++"), "-std=c++20", "-O3", *flag,
             str(AUDIT / f"{name}.cpp"), "-o", str(output / name)],
            check=True,
        )


def validate_projection_receipt(receipt, row, base_same):
    matches = EXACT.findall(receipt)
    if len(matches) != 1:
        raise ValueError(f"Expected one exact projection receipt for {row}")
    index, real, imaginary = matches[0]
    if base_same:
        if index or (int(real), int(imaginary)) != (0, 0):
            raise ValueError(f"Expected unindexed exact zero for {row}")
    elif index.split() != row:
        raise ValueError(f"Projection receipt index {index!r} differs from {row}")


def project(output, key, stem, suffix, expected, pool):
    parity = stem + ("_parity" if suffix else "_parity_dual")
    parity_output = subprocess.check_output(
        [str(output / parity), *suffix], text=True,
    )
    slices = [row.split() for row in SLICE.findall(parity_output)]
    assert len(slices) == expected
    assert len({tuple(row) for row in slices}) == expected
    (output / f"{key}.slices").write_text(parity_output)

    def evaluate(row):
        receipt = subprocess.check_output(
            [str(output / (stem + "_dual")), *row, *suffix], text=True,
        )
        validate_projection_receipt(receipt, row, base_same=key == "same")
        return receipt

    path = output / f"{key}.out"
    with path.open("w") as stream:
        for receipt in pool.map(evaluate, slices):
            stream.write(receipt)
    result = list(center.read(path))
    if "mixed" not in key:
        assert not result
    else:
        assert len(result) == 24
    print(key, len(slices), "slices", len(result), "nonzero", flush=True)
    return result


def replay(output, closed):
    compile_evaluators(output, closed)
    tensors = {}
    with ThreadPoolExecutor(3) as pool:
        for family, stem, size in (
            ("same", "l1_sparse_center", 320),
            ("mixed", "l1_sparse_center_mixed", 608),
        ):
            tensors[family, 0] = project(output, family, stem, [], size, pool)
            for shift in range(1, 4):
                key = f"{family}_{shift}"
                suffix = [str(shift), str(int(family == "mixed"))]
                tensors[family, shift] = project(
                    output, key, "l1_sparse_center_shift", suffix, size, pool,
                )

    @cache
    def load(family, shift):
        return tensors[family, shift]

    shifted_total = list(ZERO)
    for (family, left, right), count in sorted(shifted.groups.items()):
        value, _ = shifted.contract(family, left, right, load)
        assert value == shifted.contract(family, right, left, load)[0]
        for i in range(2):
            shifted_total[i] += count * value[i]
    assert shifted_total == [Fraction(25, 1536), 0]
    print("shifted subtotal", tuple(shifted_total), flush=True)

    data = {}
    for code, family in enumerate(("same", "mixed")):
        path = output / f"residual_{family}.out"
        with path.open("w") as stream:
            subprocess.run(
                [str(output / "l1_residual_batched"), str(code)],
                stdout=stream, check=True,
            )
        data[family] = residual.read(family, path)
    table = residual.source_table(closed)
    links, den = residual.adjacency(table)
    residual_total = list(ZERO)
    for (family, left, right), count in sorted(residual.residual.items()):
        a, b = data[family][left], data[family][right]
        value, _ = residual.contract(a, b, links, den)
        assert value == residual.contract(b, a, links, den)[0]
        print("residual", family, left, right, count, value, flush=True)
        for i in range(2):
            residual_total[i] += count * value[i]
    print("residual subtotal", tuple(residual_total), flush=True)
    total = tuple(x + y for x, y in zip(shifted_total, residual_total))
    expected = Fraction(-1171, 1024) if closed else Fraction(-3113, 27648)
    assert total == (expected, 0)
    print("diagonal numerator coefficient", total, flush=True)


if __name__ == "__main__":
    if len(sys.argv) != 3 or sys.argv[2] not in {"closed", "literal"}:
        raise SystemExit("usage: l1_closed_composite_diagonal_replay.py OUTPUT closed|literal")
    destination = Path(sys.argv[1]).resolve()
    destination.mkdir(parents=True, exist_ok=True)
    replay(destination, sys.argv[2] == "closed")
