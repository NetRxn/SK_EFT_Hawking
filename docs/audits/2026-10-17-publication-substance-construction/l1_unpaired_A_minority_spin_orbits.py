"""Check fixed-coordinate covariance for exact minority pairs 5/6/7."""

from argparse import ArgumentParser
from collections import Counter, defaultdict
from hashlib import sha256
from itertools import permutations, product
import re
from fractions import Fraction
import json
from pathlib import Path
from sympy import I, Matrix, diag, eye, simplify, sqrt, trace
from l1_direct_b_haar import gamma, pauli
from l1_unpaired_offset_factors import DIVISOR
from l1_unpaired_A_minority_pair import MINORITY

from l1_reduced_wedge_reference import wedge_sign


def mul(a, b):
    return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


def transform(rows, axis, offset):
    out = defaultdict(lambda: [Fraction(0), Fraction(0)])
    for mask, value in rows:
        expansion = {(0, 0): tuple(value)}
        for i in range(mask.bit_length()):
            if not mask >> i & 1:
                continue
            local = i % 8
            if local not in (offset, offset + 1, offset + 4, offset + 5):
                terms = [(i, (1, 0), 0)]
            else:
                bar = local < 4
                if axis == 2:
                    terms = [
                        (i, (1, (1 if local % 2 == 0 else -1) * (1 if bar else -1)), 1)
                    ]
                else:
                    terms = [(i, (1, 0), 1), (i ^ 1, (0, 1 if bar else -1), 1)]
            next_terms = defaultdict(lambda: [0, 0])
            for (old, power), v in expansion.items():
                for j, u, p in terms:
                    b = 1 << j
                    if old & b:
                        continue
                    dest = next_terms[old | b, power + p]
                    sign = wedge_sign(old, b)
                    r, t = mul(v, u)
                    dest[0] += sign * r
                    dest[1] += sign * t
            expansion = next_terms
        for (target, power), (r, t) in expansion.items():
            denom = 2 ** (power // 2)
            out[target, power % 2][0] += Fraction(r, denom)
            out[target, power % 2][1] += Fraction(t, denom)
    return {k: tuple(v) for k, v in out.items() if any(v)}


MANIFEST_SHA = "48d9d1cf6ed7445be86b772602f8ee682966f56d4c6c0c7f301eb9e5938e40c4"
HEX = re.compile(r"\b[0-9a-f]{64}\b")


def sha(path):
    return sha256(path.read_bytes()).hexdigest()


def freeze_json(key):
    return tuple(tuple(v) if isinstance(v, list) else v for v in key)


def proper_rotations():
    for p in permutations(range(3)):
        parity = (-1) ** sum(p[i] > p[j] for i in range(3) for j in range(i + 1, 3))
        # One proper signed lift per unsigned axis permutation suffices.
        signs = (1, 1, parity)
        assert parity * signs[0] * signs[1] * signs[2] == 1
        yield tuple(sign * (i + 1) for i, sign in zip(p, signs, strict=True))


def coordinate(word, left, right):
    values = []
    signs = []
    for x in word:
        if x in (0, 4):
            values.append(x)
            signs.append(1)
        else:
            axis = (left if x < 4 else right)[x % 4 - 1]
            values.append(abs(axis) + (4 if x >= 4 else 0))
            signs.append(1 if axis > 0 else -1)
    assert all(signs[a] * signs[b] == 1 for a, b in ((0, 2), (1, 4), (3, 6)))
    assert signs[5] == 1
    return tuple(values), tuple(signs)


def check_generators(path):
    records = {}
    for line in path.read_text().splitlines():
        row = json.loads(line)
        name = row["primitive_sha256"]
        if name not in MINORITY:
            continue
        rows = tuple((m, tuple(v)) for m, v in row["primitive_rows"])
        assert sha256(repr(rows).encode()).hexdigest() == name
        assert records.setdefault(name, rows) == rows
    assert records.keys() == MINORITY
    for offset, axis in product((0, 2), (0, 2)):
        u = (eye(2) - I * pauli[axis]) / sqrt(2)
        S = diag(u, eye(2)) if offset == 0 else diag(eye(2), u)
        assert simplify(S * S.adjoint()) == eye(4) and simplify(S.det()) == 1
        assert S * diag(1, 1, -1, -1) == diag(1, 1, -1, -1) * S
        rotated = [simplify(S * g * S.adjoint()) for g in gamma]
        R = Matrix([[simplify(trace(a * b) / 4) for b in gamma] for a in rotated])
        assert simplify(R * R.T) == eye(4) and simplify(R.det()) == 1
        assert all(
            simplify(
                a - sum((R[i, j] * b for j, b in enumerate(gamma)), Matrix.zeros(4))
            )
            == Matrix.zeros(4)
            for i, a in enumerate(rotated)
        )
        for rows in records.values():
            expected = {(m, 0): tuple(map(Fraction, v)) for m, v in rows}
            assert transform(rows, axis, offset) == expected
    return records


def evaluated(receipts, manifest):
    parts = defaultdict(list)
    for receipt in receipts:
        id_text, path = receipt.split("=", 1)
        idx = int(id_text)
        path = Path(path)
        parts[idx].append(path)
    results = {}
    for idx, paths in parts.items():
        row = manifest[idx]
        raw = []
        rosters = set()
        for path in paths:
            lines = path.read_text().splitlines()
            (desc,) = [x.split() for x in lines if x.startswith("equal B maps ")]
            assert (int(desc[3]), desc[4], desc[5], int(desc[7]), int(desc[9])) == (
                row["b_rows"],
                row["exact_b_sha256"],
                row["primitive_sha256"],
                row["signed_b_scale"],
                row["center11_rows"],
            )
            (roster,) = [
                x for x in lines if x.startswith(("verified roster ", "roster "))
            ]
            (roster_sha,) = HEX.findall(roster)
            rosters.add(roster_sha)
            raw.extend(json.loads(x) for x in lines if x.startswith("{"))
        assert len(rosters) == 1
        raw.sort(key=lambda r: r["index"])
        assert len(raw) == 2304 and [r["index"] for r in raw] == list(range(2304))
        assert all(r["status"] == "exact" for r in raw)
        keys = tuple(freeze_json(r["key"]) for r in raw)
        assert keys == tuple(sorted(set(keys)))
        assert sha256(repr(keys).encode()).hexdigest() in rosters
        totals = tuple(
            Fraction(sum(r[field] for r in raw) * row["signed_b_scale"], DIVISOR)
            for field in ("numerator_real", "numerator_imag")
        )
        results[idx] = totals, [(p.name, sha(p)) for p in sorted(paths)]
    return results


def main():
    p = ArgumentParser(description=__doc__)
    p.add_argument("--manifest", required=True, type=Path)
    p.add_argument("--primitive", required=True, type=Path)
    p.add_argument("--receipt", action="append", default=[])
    p.add_argument("--output", required=True, type=Path)
    args = p.parse_args()
    assert sha(args.manifest) == MANIFEST_SHA
    check_generators(args.primitive)
    _, *manifest = map(json.loads, args.manifest.read_text().splitlines())
    assert [r["id"] for r in manifest] == list(range(288))
    by_word = {}
    for row in manifest:
        a, b = map(tuple, row["words"])
        assert a[5] == 0 and b[5] == 4 and a[:5] + a[6:] == b[:5] + b[6:]
        assert all(a[i] == a[j] for i, j in ((0, 2), (1, 4), (3, 6)))
        assert a not in by_word
        by_word[a] = row
    observed = evaluated(args.receipt, manifest)
    pending = set(range(len(manifest)))
    bins = Counter()
    overlaps = 0
    represented = 0
    rotations = tuple(proper_rotations())
    with args.output.open("x") as out:
        out.write(
            json.dumps(
                dict(
                    kind="manifest",
                    minority_sha256=MANIFEST_SHA,
                    primitive_sha256=sha(args.primitive),
                    coordinates=576,
                    pairs=288,
                )
            )
            + "\n"
        )
        while pending:
            rep = min(pending)
            base = manifest[rep]
            first, second = map(tuple, base["words"])
            witnesses = {}
            for left, right in product(rotations, repeat=2):
                target, signs = coordinate(first, left, right)
                other, signs_other = coordinate(second, left, right)
                member = by_word[target]
                assert tuple(member["words"][1]) == other and signs == signs_other
                assert all(
                    member[k] == base[k]
                    for k in ("exact_b_sha256", "primitive_sha256", "signed_b_scale")
                )
                witnesses.setdefault(
                    member["id"],
                    dict(id=member["id"], left=left, right=right, signs=signs),
                )
            assert witnesses.keys() <= pending
            pending -= witnesses.keys()
            bins[len(witnesses)] += 1
            tested = sorted(i for i in witnesses if i in observed)
            totals = {observed[i][0] for i in tested}
            assert len(totals) <= 1
            overlaps += max(0, len(tested) - 1)
            represented += bool(tested)
            out.write(
                json.dumps(
                    dict(
                        representative=rep,
                        multiplicity=len(witnesses),
                        members=[witnesses[i] for i in sorted(witnesses)],
                        observed=[
                            dict(
                                id=i,
                                total=list(map(str, observed[i][0])),
                                receipts=observed[i][1],
                            )
                            for i in tested
                        ],
                    )
                )
                + "\n"
            )
    assert bins == {3: 6, 6: 12, 9: 10, 18: 6}
    print(
        "exact orbits",
        sum(bins.values()),
        bins,
        "observed pairs",
        len(observed),
        "observed orbits",
        represented,
        "independent overlap comparisons",
        overlaps,
    )


if __name__ == "__main__":
    main()
