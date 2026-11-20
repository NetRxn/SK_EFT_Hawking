"""Compare two overlap rows to reviewed raw integers using an odd-prime join."""
from fractions import Fraction
from hashlib import file_digest
from pathlib import Path
from signal import alarm
from sys import argv
from time import perf_counter

import numpy as np

from l1_extended_overlap_run_orbits import temporal_parity
from l1_extended_overlap_schedule_orbits import selected
from l1_extended_overlap_scheduler import (
    EXTERIOR_FACTOR, assignments, exterior, indices, jobs, left, right,
)
from l1_extended_overlap_sum_orbits import normalized_motif

PRIME = 65537


def check_hash(path, expected):
    with Path(path).open("rb") as stream:
        assert file_digest(stream, "sha256").hexdigest() == expected


def mod_matrix(matrix):
    result = matrix.copy()
    assert result.data.dtype == np.int64
    assert result.nnz * (PRIME - 1) < 2**63
    result.data %= PRIME
    result.sum_duplicates()
    result.data %= PRIME
    result.eliminate_zeros()
    assert result.has_canonical_format
    return result


def mod_join(lmat, rmat, left_column, right_column):
    # Keep the tracked tensor indexing and project independently from the
    # exact kernel. The sparse dot and each block reduction fit signed int64.
    assert lmat.shape == rmat.shape and lmat.shape[1] * (PRIME - 1)**2 < 2**63
    lmat = mod_matrix(lmat)
    rmat = mod_matrix(rmat).T
    a, b = (np.array([digits for digits, _ in c], dtype=np.int16)
            for c in (left_column, right_column))
    s3, s0, s2, s1 = (indices(a, b, i, j)
                      for i, j in ((0, 2), (6, 4), (7, 5), (1, 3)))
    u = (81*s3+s0).ravel()
    v = (81*s2+s1).ravel()
    order = np.argsort(u, kind="stable")
    u, v = u[order], v[order]
    weights = []
    for column in (left_column, right_column):
        split = [divmod(value, EXTERIOR_FACTOR) for _, value in column]
        assert all(rem == 0 and abs(value) <= 3264 for value, rem in split)
        weights.append(np.array([value % PRIME for value, _ in split], dtype=np.int64))
    wa, wb = weights
    assert len(u) * (PRIME - 1) < 2**63
    total = live = 0
    for i in range(0, lmat.shape[0], 128):
        j = min(i+128, lmat.shape[0])
        lo, hi = np.searchsorted(u, [i, j])
        if lo == hi:
            continue
        g = lmat[i:j] @ rmat
        g.data %= PRIME
        values = np.asarray(g[u[lo:hi]-i, v[lo:hi]]).ravel()
        flat = order[lo:hi]
        live += int(np.count_nonzero(values))
        terms = values * wa[flat//len(wb)] % PRIME
        terms = terms * wb[flat%len(wb)] % PRIME
        total = (total + int(terms.sum(dtype=np.int64))) % PRIME
    return total * pow(EXTERIOR_FACTOR, 2, PRIME) % PRIME, len(u), live


def mod_fraction(value):
    return value.numerator * pow(value.denominator, -1, PRIME) % PRIME


def main(column_path, exact_path):
    started = perf_counter()
    alarm(45)
    check_hash(column_path, "3f15a76fc3ae9af4f3340cfc14626feebee2839c0fb25ead9cf2750ee37bf702")
    check_hash(exact_path, "d487deadea8c31337cecc5ac5ffcceaff79a30e3e0422f9b07b7f4ecbe277b32")
    exact = [tuple(map(int, row.split()[:5])) for row in Path(exact_path).read_text().splitlines()]
    assert [row[0] for row in exact] == [0, 1]
    groups = exterior(column_path)
    full = jobs(groups)
    plan = list(selected(full))
    assert len(plan) == 35_084
    assert sum(weight for _, weight in plan) == len(full) == 589_194
    assert sum(weight * len(groups[s, q]) * len(groups[t, r])
               for (_, _, _, s, q, t, r), weight in plan) == 94_748_063_904
    assert sum(temporal_parity(s) and temporal_parity(t)
               for (_, _, _, s, _, t, _), _ in plan) == 770
    print("pinned schedule seconds", perf_counter()-started, flush=True)
    exact_subtotal = residue_subtotal = 0
    for idx, weight, pairs, exact_live, raw in exact:
        tick = perf_counter()
        (a, b, c, s, q, t, r), expected_weight = plan[idx]
        assert weight == expected_weight and temporal_parity(s) and temporal_parity(t)
        residue, count, live = mod_join(
            left(a,b), right(c,assignments(q,r,s[5],t[5]),s[7]), groups[s,q], groups[t,r])
        assert count == pairs and live <= exact_live and residue == raw % PRIME and raw != 0
        print("row weight candidates exact_live modular_live raw residue seconds",
              idx, weight, count, exact_live, live, raw, residue, perf_counter()-tick, flush=True)
        exact_subtotal += weight * raw
        residue_subtotal = (residue_subtotal + weight * residue) % PRIME
    assert residue_subtotal == exact_subtotal % PRIME
    curvature_scale = 48**8 * 4**4
    print("weighted two-row raw subtotal and residue", exact_subtotal, residue_subtotal)
    curvature = Fraction(exact_subtotal, curvature_scale)
    assert mod_fraction(curvature) == residue_subtotal * pow(curvature_scale, -1, PRIME) % PRIME
    print("two-row curvature-only subtotal", curvature, "residue", mod_fraction(curvature))
    normalized = normalized_motif(exact_subtotal)
    scale = normalized_motif(1)
    assert mod_fraction(normalized) == residue_subtotal * mod_fraction(scale) % PRIME
    print("two-row subtotal under full motif scale", normalized, "residue", mod_fraction(normalized))
    print("complete seconds", perf_counter()-started, flush=True)
    alarm(0)


if __name__ == "__main__":
    main(*argv[1:])
