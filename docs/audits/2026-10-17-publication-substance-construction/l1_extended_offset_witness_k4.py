"""Census and bounded exact replay of four-deviation paired source words.

Origins are fixed at 0 and 1. The census includes both ordered source
axis classes (2, 2) and (2, 3). Exact replay uses the existing k3
geometry and contraction kernels for the core shapes they support.
Other core shapes remain explicit entries in the complete census.
"""

from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
import json
from time import perf_counter

from l1_extended_offset_witness_k3 import census, geometry, solve


def data():
    rows = []
    geometries = {}
    counts = Counter()
    for axes in ((2, 2), (2, 3)):
        seen = set()
        for omitted, changes, frame, sources in census(*axes, deviations=4):
            identity = (omitted, changes)
            assert identity not in seen
            seen.add(identity)
            row = {
                "index": len(rows),
                "axes": axes,
                "omitted": omitted,
                "changes": changes,
            }
            try:
                geom = geometry(frame, sources)
            except (AssertionError, ValueError, TypeError) as error:
                # The complete census retains shapes the k3 kernel cannot handle.
                row["supported_geometry"] = False
                row["geometry_diagnostic"] = type(error).__name__ + ": " + str(error)
                counts[axes + ("unclassified",)] += 1
            else:
                row["supported_geometry"] = True
                row["square"] = geom.square
                row["free_tori"] = len(geom.free_tori)
                row["divisor"] = geom.divisor
                geometries[row["index"]] = geom
                counts[axes + (geom.square is not None, len(geom.free_tori))] += 1
            rows.append(row)
    assert len(rows) == 272
    assert Counter(tuple(row["axes"]) for row in rows) == {(2, 2): 164, (2, 3): 108}
    manifest = {
        "kind": "paired-k4-census",
        "deviations": 4,
        "origins": [0, 1],
        "rows": rows,
        "classes": [
            [list(key), count]
            for key, count in sorted(counts.items(), key=lambda item: str(item[0]))
        ],
    }
    return manifest, geometries


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--word", type=int)
    args = parser.parse_args()
    started = perf_counter()
    manifest, geometries = data()
    serialized = json.dumps(manifest, sort_keys=True, separators=(",", ":")).encode()
    print(json.dumps({
        "kind": "census",
        "words": len(manifest["rows"]),
        "supported_words": len(geometries),
        "classes": manifest["classes"],
        "manifest_sha256": sha256(serialized).hexdigest(),
        "seconds": round(perf_counter() - started, 3),
    }, sort_keys=True), flush=True)
    if args.word is None:
        print(serialized.decode(), flush=True)
        return
    if args.word not in geometries:
        parser.error("word must name a census entry with supported_geometry=true")
    value, peak = solve(geometries[args.word])
    print(json.dumps({
        "kind": "exact-word",
        "word": manifest["rows"][args.word],
        "manifest_sha256": sha256(serialized).hexdigest(),
        "unsigned_axis_coefficient": [value.numerator, value.denominator],
        "peak_rows": peak,
        "seconds": round(perf_counter() - started, 3),
    }, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
