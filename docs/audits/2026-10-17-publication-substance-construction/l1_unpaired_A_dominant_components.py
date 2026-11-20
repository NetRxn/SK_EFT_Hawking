"""Reconstruct disjoint dominant-B rank-one component receipts."""

from argparse import ArgumentParser
from ast import literal_eval
from collections import Counter, defaultdict
from hashlib import sha256
from functools import cache
import json
from math import gcd
from pathlib import Path
import re

from l1_unpaired_offset_factors import FRAME_PLANES, LIVE, SLOTS, action_centers, qkey
from l1_unpaired_signed_slice import CUT_EDGES, freeze
from l1_unpaired_source_support import CUT

DIGEST = "2300ae45fae9964a814091804bfc5e81817b8d972c7b40b927e0c73e984df0e4"
QKEYS = tuple(map(qkey, CUT))
LOG_PATTERN = re.compile(
    r"tuple (\([^)]*\)) nonzero B\+sources rows 208 exact digest ([0-9a-f]+) "
    r"primitive digest ([0-9a-f]+) signed integer scale (-?\d+)"
)


def digest_rows(rows):
    return sha256(repr(rows).encode()).hexdigest()


def input_words(paths, logs, primitive):
    words = {}
    indexed = {}
    reconstructed = {}

    def save(word, index, exact, scale):
        assert len(word) == 7 and scale
        if scale not in reconstructed:
            reconstructed[scale] = digest_rows(
                tuple((m, (re * scale, im * scale)) for m, (re, im) in primitive)
            )
        assert reconstructed[scale] == exact
        if word in words:
            old, prior = words[word]
            assert old == scale and (index is None or prior is None or index == prior)
            if index is None:
                index = prior
        if index is not None:
            assert indexed.setdefault(index, word) == word
        words[word] = scale, index

    for path in paths:
        for line in path.read_text().splitlines()[1:]:
            cells = line.split()
            if len(cells) < 7 or cells[5] != DIGEST:
                continue
            assert cells[2:4] == ["B-nonzero", "208"]
            save(
                tuple(map(int, cells[1].split(","))),
                int(cells[0]),
                cells[4],
                int(cells[6]),
            )
    for path in logs:
        for match in LOG_PATTERN.finditer(path.read_text()):
            if match[3] == DIGEST:
                save(literal_eval(match[1]), None, match[2], int(match[4]))
    return words


def primitive_center(keys, weighted):
    exact = tuple(sorted((k, v) for k, v in weighted.items() if v))
    assert exact
    scale = gcd(*(abs(v) for _, v in exact))
    scale *= 1 if exact[0][1] > 0 else -1
    return (keys, tuple((k, v // scale) for k, v in exact)), scale


def component_partition(words):
    centers = dict(zip(sorted(FRAME_PLANES), action_centers(), strict=True))
    expected_positions = {1: (0, 1), 3: (2, 3), 9: (4,), 11: (5, 6)}
    actual_positions = {
        x: tuple(i for i, k in enumerate(QKEYS) if k in keys)
        for x, (keys, _, _) in centers.items()
        if not x & 4 and set(keys) & set(QKEYS)
    }
    assert actual_positions == expected_positions
    for lo, axis in set(SLOTS) - CUT_EDGES:
        hi = lo ^ (1 << axis)
        assert not set(QKEYS) & {qkey(e) for e in ((lo, axis), (hi, axis)) if e in LIVE}

    @cache
    def frozen(site, coordinates):
        positions = expected_positions[site]
        fixed = dict(zip((QKEYS[i] for i in positions), coordinates, strict=True))
        keys, rows, grade = freeze(centers[site], fixed)
        assert not grade and all(
            set(row) == {0} and row[0][1] == 0 for row in rows.values()
        )
        return keys, {key: row[0][0] for key, row in rows.items()}

    grouped = defaultdict(list)
    for word, (scale, index) in sorted(words.items()):
        grouped[word[2:]].append((word, scale, index))

    signatures = {}
    blocks = defaultdict(dict)
    for fixed, members in sorted(grouped.items()):
        weighted = Counter()
        keys = None
        for word, weight, _ in members:
            row_keys, rows = frozen(1, word[:2])
            assert keys is None or keys == row_keys
            keys = row_keys
            weighted.update({k: weight * v for k, v in rows.items()})
        c1, scale = primitive_center(keys, weighted)
        remaining = []
        for site, coords in zip(
            (3, 9, 11), (fixed[:2], fixed[2:3], fixed[3:]), strict=True
        ):
            sig, factor = primitive_center(*frozen(site, coords))
            remaining.append(sig)
            scale *= factor
        c3, c9, c11 = remaining
        assert (c3, c11) not in blocks[c1, c9]
        blocks[c1, c9][c3, c11] = scale, fixed
        signatures[fixed] = (c1, c3, c9, c11), members

    for block_index, ((c1, c9), block) in enumerate(sorted(blocks.items())):
        graph = defaultdict(set)
        for c3, c11 in block:
            graph[0, c3].add((1, c11))
            graph[1, c11].add((0, c3))
        unseen = set(graph)
        component_index = 0
        while unseen:
            seen = set()
            stack = [min(unseen)]
            while stack:
                node = stack.pop()
                if node not in seen:
                    seen.add(node)
                    stack.extend(graph[node] - seen)
            unseen -= seen
            left = sorted(sig for side, sig in seen if side == 0)
            right = sorted(sig for side, sig in seen if side == 1)
            first = [block.get((left[0], sig), (0, None))[0] for sig in right]
            g = gcd(*(abs(v) for v in first))
            assert g
            rw = [v // g for v in first]
            pivot = next(i for i, v in enumerate(rw) if v)
            lw = []
            for a in left:
                row = [block.get((a, b), (0, None))[0] for b in right]
                weight, rem = divmod(row[pivot], rw[pivot])
                assert not rem and row == [weight * v for v in rw]
                lw.append(weight)

            c3_tables = list(zip(left, lw, strict=True))
            c11_tables = list(zip(right, rw, strict=True))
            member_groups = sorted(
                (block[a, b][1] for a in left for b in right if (a, b) in block)
            )
            yield (
                block_index,
                component_index,
                c1,
                c9,
                c3_tables,
                c11_tables,
                [(fixed, signatures[fixed][1]) for fixed in member_groups],
            )
            component_index += 1


def table_sum(tables):
    keys = tables[0][0][0]
    out = Counter()
    for (other, rows), scale in tables:
        assert other == keys
        out.update({key: scale * value for key, value in rows})
    return keys, tuple(sorted((k, v) for k, v in out.items() if v))


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--primitive", type=Path, required=True)
    parser.add_argument("--rows", type=Path, nargs="+", required=True)
    parser.add_argument("--logs", type=Path, nargs="*", default=[])
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    with args.primitive.open() as stream:
        records = [json.loads(line) for line in stream if line.strip()]
    representative = next(
        row for row in records if row.get("primitive_sha256") == DIGEST
    )
    primitive = tuple(
        (m, tuple(value)) for m, value in representative["primitive_rows"]
    )
    assert len(primitive) == 208 and primitive == tuple(sorted(primitive))
    assert digest_rows(primitive) == DIGEST
    words = input_words(sorted(args.rows), sorted(args.logs), primitive)
    assert len(words) == 9216
    counts = Counter()
    unique = set()
    fixed_groups = set()
    blocks = set()
    sources = sorted({args.primitive, *args.rows, *args.logs})
    with args.output.open("x") as stream:
        stream.write(
            json.dumps(
                {
                    "kind": "manifest",
                    "primitive": DIGEST,
                    "inputs": [
                        (str(p), sha256(p.read_bytes()).hexdigest()) for p in sources
                    ],
                    "words": len(words),
                }
            )
            + "\n"
        )
        for block, component, c1, c9, c3, c11, groups in component_partition(words):
            members = {word for _, rows in groups for word, _, _ in rows}
            assert not unique & members
            unique |= members
            fixed = {k for k, _ in groups}
            assert not fixed_groups & fixed
            fixed_groups |= fixed
            blocks.add(block)
            counts[len(c3), len(c11)] += 1
            c3_sum, c11_sum = table_sum(c3), table_sum(c11)
            stream.write(
                json.dumps(
                    {
                        "block": block,
                        "component": component,
                        "shape": (len(c3), len(c11)),
                        "centers": [
                            digest_rows(c1),
                            digest_rows(c3_sum),
                            digest_rows(c9),
                            digest_rows(c11_sum),
                        ],
                        "weighted_rows": [len(c3_sum[1]), len(c11_sum[1])],
                        "left_weights": [w for _, w in c3],
                        "right_weights": [w for _, w in c11],
                        "fixed_groups": groups,
                    }
                )
                + "\n"
            )
    assert unique == words.keys() and len(fixed_groups) == 6656 and len(blocks) == 104
    assert counts == {(1, 1): 1248, (1, 5): 416, (4, 1): 312, (4, 5): 104}
    print(
        "coverage",
        len(unique),
        "fixed groups",
        len(fixed_groups),
        "blocks",
        len(blocks),
        "components",
        sum(counts.values()),
        counts,
        flush=True,
    )


if __name__ == "__main__":
    main()
