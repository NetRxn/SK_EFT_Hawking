"""Exact fully peeled k4 words with both remaining source Haar factors.

The census keeps all fifteen paired action vertices and both ordered
source insertions. Every curvature pair peels. Each word therefore has
one contraction branch and up to two joint action/source Haar edges.
"""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from fractions import Fraction
import json
from time import perf_counter

from l1_extended_offset_witness_k3 import Geometry, contraction, prepare
from l1_extended_offset_witness_k4 import data
from l1_extended_offset_witness import SCALE


def geometry(row):
    frame = dict.fromkeys((x for x in range(16) if x != row["omitted"]), (0, 1))
    frame.update((x, tuple(axes)) for x, axes in row["changes"])
    sources = ((0, row["axes"][0]), (1, row["axes"][1]))
    edges = defaultdict(list)
    faces = {}
    for x, axes in sorted(frame.items()):
        for axis in axes:
            y = x ^ (1 << axis)
            edges[min(x, y), max(x, y), axis].append((x, axis))
        a, b = (i for i in range(4) if i not in axes)
        faces[x, a, b] = {(x, a), (x ^ (1 << a), b), (x ^ (1 << b), a), (x, b)}
    protected = set(sources) | {(v, a) for x, y, a in edges for v in (x, y)}
    while faces:
        counts = Counter(edge for boundary in faces.values() for edge in boundary)
        removed = [face for face, boundary in faces.items()
                   if any(counts[e] == 1 and e not in protected for e in boundary)]
        if not removed:
            raise ValueError("word has residual curvature faces")
        for face in removed:
            del faces[face]
    joined = {}
    for x, a in sources:
        y = x ^ (1 << a)
        key = min(x, y), max(x, y), a
        if key in edges:
            assert len(edges[key]) == 1
            joined[key] = int(x != edges[key][0][0])
    assert len(joined) <= 2 and len(frame) == 15
    divisor = (SCALE ** 2) ** len(edges) * 4 ** 64
    divisor *= SCALE ** (2 - len(joined)) * 48 ** 15 * 2 ** 15
    return Geometry(frame, edges, sources, None, None, None, {}, {},
                    joined, (), (), [], divisor)


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--word", type=int)
    args = parser.parse_args()
    manifest, _ = data()
    began = perf_counter()
    candidates = {}
    for row in manifest["rows"]:
        try:
            geom = geometry(row)
        except ValueError:
            continue
        candidates[row["index"]] = (row, geom)
    assert len(candidates) == 86
    if args.word is None:
        for joined in range(3):
            index, (row, geom) = next(
                (i, data) for i, data in candidates.items()
                if len(data[1].joined_source) == joined
            )
            began = perf_counter()
            prepared = prepare(geom, {})
            assert prepared is not None
            factors, divisor, exclusive = prepared
            assert divisor == geom.divisor
            for source in geom.sources:
                x, axis = source
                edge = (min(x, x ^ (1 << axis)), max(x, x ^ (1 << axis)), axis)
                if edge in geom.joined_source:
                    assert not (set(geom.edges[edge]) & exclusive)
            value, peak = contraction(geom, {})
            print(json.dumps({"word": index, "joined": joined, "coefficient":
                  [value.numerator, value.denominator], "peak_rows": peak,
                  "seconds": round(perf_counter() - began, 3)}, sort_keys=True), flush=True)
    else:
        if args.word not in candidates:
            parser.error("word must name one of the 86 fully peeled census entries")
        row, geom = candidates[args.word]
        value, peak = contraction(geom, {})
        print(json.dumps({"word": row, "coefficient": [value.numerator,value.denominator],
                          "peak_rows": peak, "seconds": round(perf_counter() - began, 3)},
                         sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
