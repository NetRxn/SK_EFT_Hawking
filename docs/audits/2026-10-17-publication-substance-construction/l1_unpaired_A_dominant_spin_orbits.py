"""Exact Spin-orbit witnesses for the pinned dominant-component census."""

import argparse
import ast
import json
import re
from collections import Counter, defaultdict
from fractions import Fraction
from hashlib import sha256
from itertools import permutations, product
from pathlib import Path

COMPONENT_SHA = "eebf286061137a1354f831fae29ad20223bf74ce43f22aaa90e15a98b5031e75"
PRIMITIVE_FILE_SHA = "aed7a69d63235c07425b3cacf777d085d9fdc8bb856c7405473f6f45c78d66bd"
PRIMITIVE = "2300ae45fae9964a814091804bfc5e81817b8d972c7b40b927e0c73e984df0e4"
ID = (1, 2, 3)
X = (1, 3, -2)
Z = (2, -1, 3)
GENERATORS = ((X, ID), (Z, ID), (ID, X), (ID, Z))


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def wedge_sign(a, b):
    return (-1) ** sum(
        (a >> (i + 1)).bit_count() for i in range(b.bit_length()) if b >> i & 1
    )


def mul(a, b):
    return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


def transform(rows, axis, offset=2):
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


def compose(first, second):
    """Apply first then second."""
    return tuple((1 if x > 0 else -1) * second[abs(x) - 1] for x in first)


def parity(p):
    return (-1) ** sum(x > y for i, x in enumerate(p) for y in p[i + 1 :])


def group():
    proper = {
        tuple(a * s for a, s in zip(p, signs, strict=True))
        for p in permutations((1, 2, 3))
        for signs in product((-1, 1), repeat=3)
        if parity(p) * signs[0] * signs[1] * signs[2] == 1
    }
    assert len(proper) == 24
    assert {compose(a, b) for a in proper for b in proper} == proper
    generated = {ID}
    while (
        larger := generated | {compose(a, b) for a in generated for b in (X, Z)}
    ) != generated:
        generated = larger
    assert generated == proper
    lifts = tuple(p[:2] + (p[2] * parity(p),) for p in permutations((1, 2, 3)))
    assert set(lifts) <= proper
    return tuple(sorted(proper)), lifts


def action(word, left, right):
    values, signs = [], []
    for x in word:
        if x % 4:
            y = (left if x < 4 else right)[x % 4 - 1]
            values.append(abs(y) + 4 * (x // 4))
            signs.append(1 if y > 0 else -1)
        else:
            values.append(x)
            signs.append(1)
    return tuple(values), tuple(signs)


def signed(signs):
    return (-1) ** signs.count(-1)


def partition(witnesses, first, hist):
    remaining = set(witnesses)
    while remaining:
        rep = min(remaining)
        orbit = first(rep)
        assert rep in orbit and orbit.keys() <= remaining
        remaining -= orbit.keys()
        hist[len(orbit)] += 1
        yield rep, orbit


def pilot_receipt(directory, members, words):
    pilot = (0, 3)
    indices = sorted(words[word][1] for word in members[pilot])
    assert len(indices) == 60
    assert sha256(repr(indices).encode()).hexdigest() == (
        "fe6c9dd82e8a4eb6f33f2f0e80b168075333db93bd423a0da4349a7ce44135ea"
    )
    prefix = "l1_transport_rank1_site10_"
    roster_path = directory / (prefix + "selector_roster.out")
    roster = [
        json.loads(line[4:])
        for line in roster_path.read_text().splitlines()
        if line.startswith("row ")
    ]
    roster_digest = sha256(
        json.dumps([r[1:] for r in roster], separators=(",", ":")).encode()
    ).hexdigest()
    assert [r[0] for r in roster] == list(range(256))
    assert (
        roster_digest
        == "b8bde9d2380ff0fa25a5d2478cd30042c4144d024638729801ddbd5c439e4dae"
    )
    single = directory / (prefix + "transfer_scalar.out")
    data = single.read_text()
    coords = ast.literal_eval(re.search(r"^selector census (\{.+?\}) ", data, re.M)[1])
    assert coords == {tuple(k): tuple(v) for k, v in zip(*roster[0][2:], strict=True)}
    assert roster[0][1] == [0]
    scalar = re.search(r"^exact scalar raw (\[.+?\]) DIVISOR (\d+)", data, re.M)
    divisor = int(scalar[2])
    raw = {0: ast.literal_eval(scalar[1])}
    receipts = [roster_path, single]
    ranges = [
        (
            prefix + "selector_batch",
            (
                (1, 8),
                (8, 32),
                (32, 48),
                (48, 64),
                (64, 80),
                (80, 96),
                (160, 176),
                (176, 192),
            ),
        ),
        (
            "l1_transport_site10_port",
            (
                (96, 112),
                (112, 128),
                (128, 144),
                (144, 160),
                (192, 208),
                (208, 224),
                (224, 240),
                (240, 256),
            ),
        ),
    ]
    for name, intervals in ranges:
        for lo, hi in intervals:
            path = directory / f"{name}_{lo}_{hi}.out"
            text = path.read_text()
            matches = re.findall(r"^exact selector (\d+) raw (\[[^]]+\])", text, re.M)
            assert [int(i) for i, _ in matches] == list(range(lo, hi))
            assert all(int(i) not in raw for i, _ in matches)
            raw.update((int(i), ast.literal_eval(v)) for i, v in matches)
            match = re.search(
                rf"^terminal range {lo} {hi} roster {roster_digest} raw (\[[^]]+\])",
                text,
                re.M,
            )
            assert ast.literal_eval(match[1]) == list(
                map(sum, zip(*(raw[i] for i in range(lo, hi))))
            )
            receipts.append(path)
    assert set(raw) == set(range(256))
    total = list(map(sum, zip(*raw.values())))
    assert all(v[1] == 0 for v in raw.values())
    return dict(
        kind="direct_receipt",
        component=pilot,
        scope="complete component",
        roster_sha256=roster_digest,
        selectors=len(raw),
        raw=total,
        divisor=divisor,
        coefficient=[str(Fraction(v, divisor)) for v in total],
        receipts=[[path.name, digest(path)] for path in receipts],
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("components", type=Path)
    parser.add_argument("primitive", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--pilot-receipts", type=Path)
    args = parser.parse_args()
    assert digest(args.components) == COMPONENT_SHA
    assert digest(args.primitive) == PRIMITIVE_FILE_SHA
    (primitive,) = (
        r
        for r in map(json.loads, args.primitive.read_text().splitlines())
        if r["primitive_sha256"] == PRIMITIVE
    )
    B = tuple((m, tuple(v)) for m, v in primitive["primitive_rows"])
    assert len(B) == 208 and sha256(repr(B).encode()).hexdigest() == PRIMITIVE
    expected = {(m, 0): tuple(map(Fraction, v)) for m, v in B}
    for offset, axis in product((0, 2), repeat=2):
        assert transform(B, axis, offset) == expected

    head, *components = map(json.loads, args.components.read_text().splitlines())
    assert head["primitive"] == PRIMITIVE
    assert len(head["inputs"]) == 78
    assert all(digest(Path(path)) == expected for path, expected in head["inputs"])
    words, members = {}, {}
    for row in components:
        comp = row["block"], row["component"]
        assert comp not in members
        members[comp] = set()
        for fixed, group_rows in row["fixed_groups"]:
            for word, weight, index in group_rows:
                word = tuple(word)
                assert word not in words and word[2:] == tuple(fixed)
                words[word] = weight, index, comp
                members[comp].add(word)
    assert len(words) == 9216 and len(members) == 2080
    assert sum(w[0] == w[2] and w[1] == w[4] and w[3] == w[6] for w in words) == 0

    rotations, lifts = group()
    counts = []
    for left, right in GENERATORS:
        flips = 0
        for comp, members_set in members.items():
            moved = set()
            for w in members_set:
                v, signs = action(w, left, right)
                sign = signed(signs)
                assert words[v][0] == sign * words[w][0]
                moved.add(v)
                flips += sign < 0
            target = words[min(moved)][2]
            assert moved == members[target]
        counts.append((9216 - flips, flips))
    assert counts == [(5184, 4032)] * 4

    # Each lift represents one unsigned action. For a fixed image word the
    # product sign is forced by the nonzero signed weight and generator closure.
    def word_orbit(rep):
        found = {}
        for left, right in product(lifts, repeat=2):
            w, signs = action(rep, left, right)
            weight, index, comp = words[w]
            assert weight == signed(signs) * words[rep][0]
            found.setdefault(
                w,
                dict(
                    word=w,
                    scale=weight,
                    source_index=index,
                    component=comp,
                    left=left,
                    right=right,
                    signs=signs,
                ),
            )
        return found

    def component_orbit(rep):
        found = {}
        source = sorted(members[rep])
        for left, right in product(lifts, repeat=2):
            mapped = [action(w, left, right) for w in source]
            target = words[mapped[0][0]][2]
            assert {w for w, _ in mapped} == members[target]
            assert all(
                words[v][0] == signed(signs) * words[w][0]
                for w, (v, signs) in zip(source, mapped, strict=True)
            )
            found.setdefault(
                target,
                dict(
                    component=target,
                    left=left,
                    right=right,
                    word_images=[v for v, _ in mapped],
                    coordinate_signs=[s for _, s in mapped],
                ),
            )
        return found

    word_hist, comp_hist = Counter(), Counter()
    with args.output.open("x") as out:

        def emit(row):
            out.write(json.dumps(row, separators=(",", ":")) + "\n")

        emit(
            dict(
                kind="manifest",
                component_sha256=COMPONENT_SHA,
                primitive_file_sha256=PRIMITIVE_FILE_SHA,
                primitive=PRIMITIVE,
                rotations=rotations,
                generators=GENERATORS,
                generator_positive_negative=counts,
                words=len(words),
                components=len(members),
                inputs=head["inputs"],
                direct_scalars_recorded=bool(args.pilot_receipts),
            )
        )
        if args.pilot_receipts:
            emit(pilot_receipt(args.pilot_receipts, members, words))
        for rep, orbit in partition(words, word_orbit, word_hist):
            emit(
                dict(
                    kind="word_orbit",
                    representative=rep,
                    multiplicity=len(orbit),
                    members=[orbit[k] for k in sorted(orbit)],
                )
            )
        for rep, orbit in partition(members, component_orbit, comp_hist):
            emit(
                dict(
                    kind="component_orbit",
                    representative=rep,
                    multiplicity=len(orbit),
                    representative_words=sorted(members[rep]),
                    members=[orbit[k] for k in sorted(orbit)],
                )
            )
        assert word_hist == {3: 12, 6: 24, 9: 116, 18: 252, 36: 96}
        assert comp_hist == {1: 4, 3: 20, 6: 6, 9: 48, 18: 54, 36: 16}
        emit(
            dict(
                kind="terminal",
                word_orbits=sum(word_hist.values()),
                component_orbits=sum(comp_hist.values()),
                word_hist=sorted(word_hist.items()),
                component_hist=sorted(comp_hist.items()),
            )
        )
    print(
        "manifest",
        digest(args.output),
        "word orbits",
        word_hist,
        "component orbits",
        comp_hist,
    )


if __name__ == "__main__":
    main()
