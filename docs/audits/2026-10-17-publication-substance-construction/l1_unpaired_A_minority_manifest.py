"""Build a deterministic exact minority-pair admission manifest from B receipts."""

from argparse import ArgumentParser
from ast import literal_eval
from collections import Counter, defaultdict
from functools import cache
from hashlib import sha256
import json
from pathlib import Path
import re

from l1_unpaired_A_minority_pair import MINORITY
from l1_unpaired_offset_factors import FRAME_PLANES, LIVE, SLOTS, action_centers, qkey
from l1_unpaired_signed_slice import CUT_EDGES, freeze
from l1_unpaired_source_support import CUT

LOG = re.compile(
    r"tuple (\([^)]*\)) nonzero B\+sources rows (\d+) exact digest ([0-9a-f]+) "
    r"primitive digest ([0-9a-f]+) signed integer scale (-?\d+)"
)
QKEYS = tuple(map(qkey, CUT))


def digest(value):
    return sha256(repr(value).encode()).hexdigest()


def primitives(path):
    out = {}
    for line in path.read_text().splitlines():
        row = json.loads(line)
        name = row["primitive_sha256"]
        if name not in MINORITY:
            continue
        rows = tuple((mask, tuple(value)) for mask, value in row["primitive_rows"])
        assert len(rows) in (36, 72, 162) and rows == tuple(sorted(rows))
        assert len({mask for mask, _ in rows}) == len(rows) and digest(rows) == name
        assert out.setdefault(name, rows) == rows
    assert out.keys() == MINORITY
    return out


def verify_inputs(paths, logs, maps):
    entries = {}
    indices = {}

    @cache
    def exact_hash(name, scale):
        return digest(
            tuple((mask, (re * scale, im * scale)) for mask, (re, im) in maps[name])
        )

    def save(path, index, word, count, exact, name, scale):
        assert len(word) == 7 and len(maps[name]) == count and scale
        assert exact_hash(name, scale) == exact
        value = (name, exact, scale, count)
        saved_value, origins = entries.setdefault(word, (value, {}))
        assert saved_value == value
        assert origins.setdefault(path.name, index) == index
        if index is not None:
            assert indices.setdefault(index, word) == word

    for path in paths:
        for line in path.read_text().splitlines()[1:]:
            cols = line.split()
            if len(cols) >= 7 and cols[5] in maps:
                assert cols[2] == "B-nonzero"
                save(
                    path,
                    int(cols[0]),
                    tuple(map(int, cols[1].split(","))),
                    int(cols[3]),
                    cols[4],
                    cols[5],
                    int(cols[6]),
                )
    for path in logs:
        for match in LOG.finditer(path.read_text()):
            if match[4] in maps:
                save(
                    path,
                    None,
                    literal_eval(match[1]),
                    int(match[2]),
                    match[3],
                    match[4],
                    int(match[5]),
                )
    return entries


def pairs(entries):
    centers = dict(zip(sorted(FRAME_PLANES), action_centers(), strict=True))
    q151 = QKEYS[5]
    assert [x for x, (keys, _, _) in centers.items() if not x & 4 and q151 in keys] == [
        11
    ]
    for lo, axis in set(SLOTS) - CUT_EDGES:
        hi = lo ^ (1 << axis)
        assert q151 not in {qkey(e) for e in ((lo, axis), (hi, axis)) if e in LIVE}

    @cache
    def joined_center(q153):
        rows = Counter()
        keys = None
        for q151_value in (0, 4):
            names, values, grade = freeze(
                centers[11], {q151: q151_value, QKEYS[6]: q153}
            )
            assert not grade and len(values) == 144 and (keys is None or keys == names)
            keys = names
            assert all(set(row) == {0} and row[0][1] == 0 for row in values.values())
            rows.update({key: row[0][0] for key, row in values.items()})
        signed = tuple(sorted((key, value) for key, value in rows.items() if value))
        assert len(signed) == 288
        return digest((keys, signed))

    groups = defaultdict(list)
    for word, (identity, origins) in sorted(entries.items()):
        groups[word[:5] + word[6:]].append((word, identity, origins))
    for i, (_, members) in enumerate(sorted(groups.items())):
        (first, identity, first_origins), (second, other, second_origins) = members
        assert first[5] == 0 and second[5] == 4 and identity == other
        primitive, exact, scale, count = identity
        yield {
            "id": i,
            "words": [first, second],
            "primitive_sha256": primitive,
            "exact_b_sha256": exact,
            "signed_b_scale": scale,
            "b_rows": count,
            "center11_sum_sha256": joined_center(first[6]),
            "center11_rows": 288,
            "origins": [sorted(first_origins.items()), sorted(second_origins.items())],
        }


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--primitive", type=Path, required=True)
    parser.add_argument("--rows", type=Path, nargs="+", required=True)
    parser.add_argument("--logs", type=Path, nargs="*", default=[])
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    sources = sorted(
        {args.primitive, *args.rows, *args.logs}, key=lambda path: path.name
    )
    assert len({path.name for path in sources}) == len(sources)
    entries = verify_inputs(args.rows, args.logs, primitives(args.primitive))
    records = list(pairs(entries))
    covered = [word for row in records for word in row["words"]]
    assert (
        len(covered) == len(set(covered)) == len(entries) == 576
        and set(covered) == entries.keys()
    )
    assert len(records) == 288
    header = {
        "kind": "manifest",
        "words": 576,
        "pairs": 288,
        "input_sha256": [(p.name, sha256(p.read_bytes()).hexdigest()) for p in sources],
    }
    with args.output.open("x") as stream:
        for row in [header, *records]:
            stream.write(json.dumps(row) + "\n")
    print(
        "minority verified",
        len(entries),
        len(records),
        Counter(row["b_rows"] for row in records),
        "input hashes",
        len(sources),
    )


if __name__ == "__main__":
    main()
