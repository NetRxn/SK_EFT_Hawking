"""Exact replay of the six paired k4 words with one source-bearing square.

This is a selected finite-lattice coefficient population, not a normalized
physical response. All fifteen paired action vertices and both ordered source
insertions remain. Fourteen curvature pairs peel; the remaining square is
integrated jointly with its action frames and its fixed boundary source.
"""

from argparse import ArgumentParser
from collections import Counter, defaultdict
from hashlib import sha256
import json
from pathlib import Path
import sys
from time import perf_counter

# Resolve the existing scientific kernels beside this audit module.
audit_directory = Path(__file__).resolve().parent
if (audit_directory / "l1_extended_offset_witness_k3.py").is_file():
    sys.path.insert(0, str(audit_directory))
import l1_extended_offset_witness_k2 as k2
import l1_extended_offset_witness_k3 as k3
import l1_extended_offset_witness_k4 as k4
import l1_extended_offset_square as square_kernel
import l1_extended_offset_witness as witness
import l1_extended_mixed_frame_moment as moments
from l1_extended_four_face_gauge_join import IDENTITY

EXPECTED_WORDS = (3, 42, 165, 206, 247, 262)
EXPECTED_MANIFEST_SHA256 = (
    "ada6e3a7bd8b32b238a85f1a8e7070dde1d2846f5fe6bc5184068a0fc9596d5b"
)


def source_hashes():
    """Bind this evaluator and the reused principal scientific kernels."""
    modules = (k2, k3, k4, square_kernel, witness, moments)
    result = {Path(m.__file__).name: sha256(Path(m.__file__).read_bytes()).hexdigest()
              for m in modules}
    result["evaluator"] = sha256(Path(__file__).read_bytes()).hexdigest()
    return result


def geometry(row):
    """Construct only the accepted single-square geometry, without contraction."""
    if row["index"] not in EXPECTED_WORDS:
        raise ValueError("word is outside the six single-square entries")
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
        faces[x, a, b] = {(x, a), (x ^ (1 << a), b),
                          (x ^ (1 << b), a), (x, b)}
    assert len(frame) == 15 and len(row["changes"]) == 4
    endpoints = Counter(v for x, a in sources for v in (x, x ^ (1 << a)))
    incoming = Counter(x ^ (1 << a) for x, axes in frame.items() for a in axes)
    assert all(4 * (x in frame) + 2 * incoming[x] + 2 * endpoints[x] == 8
               for x in range(16))

    protected = set(sources) | {(v, a) for x, y, a in edges for v in (x, y)}
    while faces:
        counts = Counter(e for boundary in faces.values() for e in boundary)
        removed = [f for f, boundary in faces.items()
                   if any(counts[e] == 1 and e not in protected for e in boundary)]
        if not removed:
            break
        for face in removed:
            del faces[face]
    assert len(faces) == 1
    square, = faces
    assert faces[square] <= protected
    x, a, _ = square
    live = x, a
    lo, hi = sorted((x, x ^ (1 << a)))
    live_edge = lo, hi, a
    assert len(edges[live_edge]) == 1
    fixed = dict.fromkeys(faces[square] - {live}, IDENTITY)

    # The three fixed square links form a forest. Normalized Haar forest
    # gauge fixing has unit volume and retains the live square holonomy.
    parent = {}

    def root(site):
        while site in parent:
            site = parent[site]
        return site

    for x, a in fixed:
        left, right = root(x), root(x ^ (1 << a))
        assert left != right
        parent[left] = right
    fixed_edges = {}
    for x, a in fixed:
        y = x ^ (1 << a)
        fixed_edges[min(x, y), max(x, y), a] = int(x > y)

    # The source on the square is fixed jointly, not independently Haar
    # averaged. It has no action frame on its geometric edge.
    fixed_source, = set(sources) & faces[square]
    assert fixed_source in fixed
    x, a = fixed_source
    y = x ^ (1 << a)
    assert (min(x, y), max(x, y), a) not in edges
    joined = {}
    for x, a in sources:
        y = x ^ (1 << a)
        key = min(x, y), max(x, y), a
        if key in edges:
            assert len(edges[key]) == 1
            assert key not in fixed_edges and key != live_edge
            joined[key] = int(x != edges[key][0][0])
    assert len(joined) <= 1

    # E action edges normalize two directed moments each. A joint source
    # shares those moments; each other source supplies one SCALE factor.
    # 64 coframes, fourteen peeled curvature pairs, fifteen 2! factors.
    divisor = witness.SCALE ** (2 * len(edges) + 2 - len(joined))
    divisor *= 4 ** 64 * 48 ** 14 * 2 ** 15
    return k3.Geometry(frame, edges, sources, fixed_source, square, live,
                       fixed, fixed_edges, joined, (), (), [], divisor)


def data():
    manifest, _ = k4.data()
    serialized = json.dumps(manifest, sort_keys=True, separators=(",", ":")).encode()
    manifest_hash = sha256(serialized).hexdigest()
    if manifest_hash != EXPECTED_MANIFEST_SHA256:
        raise ValueError("parent k4 census differs from the reviewed manifest")
    candidates = {i: (manifest["rows"][i], geometry(manifest["rows"][i]))
                  for i in EXPECTED_WORDS}
    assert Counter(tuple(r["axes"]) for r, _ in candidates.values()) == {
        (2, 2): 2, (2, 3): 4,
    }
    return manifest_hash, candidates


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--word", type=int, choices=EXPECTED_WORDS)
    args = parser.parse_args()
    manifest_hash, candidates = data()
    binding = {"manifest_sha256": manifest_hash, "source_sha256": source_hashes(),
               "row_cap": k2.ROW_CAP, "pair_cap": k2.PAIR_CAP}
    if args.word is None:
        print(json.dumps({"kind": "single-square-census", "origins": [0, 1],
                          "valid_words": list(EXPECTED_WORDS),
                          "words": [row for row, _ in candidates.values()],
                          **binding}, sort_keys=True), flush=True)
        return
    row, geom = candidates[args.word]
    began = perf_counter()
    # There is one explicit square, not a protected torus branch sum.
    value, peak = k3.contraction(geom, {})
    raw = value * geom.divisor
    assert raw.denominator == 1
    print(json.dumps({"kind": "exact-word", "replay_geometry": "single-square",
                      "word": row, "coefficient": [value.numerator, value.denominator],
                      "divisor": geom.divisor, "raw_numerator": raw.numerator,
                      "fixed_source": geom.fixed_source, "square": geom.square,
                      "live": geom.live, "joined_edges": sorted(geom.joined_source),
                      "peak_rows": peak, "seconds": round(perf_counter() - began, 3),
                      **binding}, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
