"""Exact replay of thirty paired k4 words with one unprotected curvature torus.

This is a selected finite-lattice coefficient population, not a normalized
physical response. All fifteen paired action vertices and both ordered source
insertions remain. Eleven curvature pairs peel; the four-face free torus uses
the existing exact three-branch tensor, with no gauge fixing.
"""

from argparse import ArgumentParser
from collections import Counter, defaultdict
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
import sys
from time import perf_counter

# Resolve scientific kernels beside this audit module when installed there.
audit_directory = Path(__file__).resolve().parent
if (audit_directory / "l1_extended_offset_witness_k3.py").is_file():
    sys.path.insert(0, str(audit_directory))
import l1_extended_offset_witness_k2 as k2
import l1_extended_offset_witness_k3 as k3
import l1_extended_offset_witness_k4 as k4
import l1_extended_offset_square as square_kernel
import l1_extended_offset_witness as witness
import l1_extended_mixed_frame_moment as moments

EXPECTED_WORDS = (
    1, 14, 17, 23, 40, 53, 56, 65, 84, 88, 96, 123, 127, 135,
    164, 178, 187, 192, 204, 217, 223, 233, 246, 249, 251, 254,
    259, 261, 264, 266,
)
EXPECTED_MANIFEST_SHA256 = (
    "ada6e3a7bd8b32b238a85f1a8e7070dde1d2846f5fe6bc5184068a0fc9596d5b"
)


def source_hashes():
    """Bind this evaluator and the principal reused scientific kernels."""
    modules = (k2, k3, k4, square_kernel, witness, moments)
    result = {Path(m.__file__).name: sha256(Path(m.__file__).read_bytes()).hexdigest()
              for m in modules}
    result["evaluator"] = sha256(Path(__file__).read_bytes()).hexdigest()
    return result


def geometry(row):
    """Construct only the accepted free-torus geometry, without contraction."""
    if row["index"] not in EXPECTED_WORDS:
        raise ValueError("word is outside the thirty free-torus entries")
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
    assert len(faces) == 4 and all(face[1:] == (2, 3) for face in faces)
    assert len({face[0] & 3 for face in faces}) == 1
    assert not (set.union(*faces.values()) & protected)

    # Both original sources remain integrated. An action/source shared edge
    # uses the joint tensor, rather than two independent Haar averages.
    joined = {}
    for x, a in sources:
        y = x ^ (1 << a)
        key = min(x, y), max(x, y), a
        if key in edges:
            assert len(edges[key]) == 1
            joined[key] = int(x != edges[key][0][0])
    assert len(joined) <= 1

    # E action edges normalize two directed moments each. A joint source
    # shares those moments; each other source supplies one SCALE factor.
    # 64 coframes, eleven peeled curvature pairs, fifteen 2! factors.
    divisor = witness.SCALE ** (2 * len(edges) + 2 - len(joined))
    divisor *= 4 ** 64 * 48 ** 11 * 2 ** 15
    return k3.Geometry(frame, edges, sources, None, None, None, {}, {},
                       joined, (), (), [faces], divisor)


def solve(geom, restrict=None):
    """Sum the exact free-core tensor's three branches, retaining sources."""
    assert geom.fixed_source is None and geom.square is None
    assert not (geom.fixed_square or geom.fixed_edges or geom.linked or geom.other)
    assert len(geom.free_tori) == 1
    total = Fraction()
    peak = 0
    count = 0
    for weight, domains in k2.free_branches(geom.free_tori[0]):
        value, rows = k3.contraction(geom, domains, restrict)
        total += weight * value
        peak = max(peak, rows)
        count += 1
    assert count == 3
    return total, peak


def data():
    manifest, _ = k4.data()
    serialized = json.dumps(manifest, sort_keys=True, separators=(",", ":")).encode()
    manifest_hash = sha256(serialized).hexdigest()
    if manifest_hash != EXPECTED_MANIFEST_SHA256:
        raise ValueError("parent k4 census differs from the reviewed manifest")
    candidates = {i: (manifest["rows"][i], geometry(manifest["rows"][i]))
                  for i in EXPECTED_WORDS}
    assert Counter(tuple(row["axes"]) for row, _ in candidates.values()) == {
        (2, 2): 14, (2, 3): 16,
    }
    assert Counter((tuple(row["axes"]), len(geom.joined_source))
                   for row, geom in candidates.values()) == {
        ((2, 2), 0): 2, ((2, 2), 1): 12,
        ((2, 3), 0): 6, ((2, 3), 1): 10,
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
        print(json.dumps({"kind": "free-torus-census", "origins": [0, 1],
                          "valid_words": list(EXPECTED_WORDS),
                          "words": [row for row, _ in candidates.values()],
                          **binding}, sort_keys=True), flush=True)
        return
    row, geom = candidates[args.word]
    began = perf_counter()
    value, peak = solve(geom)
    # The three rational core weights have denominator dividing 1679616.
    branch_denominator_lcm = 1679616
    raw = value * geom.divisor * branch_denominator_lcm
    assert raw.denominator == 1
    print(json.dumps({"kind": "exact-word", "replay_geometry": "free-torus",
                      "word": row, "coefficient": [value.numerator, value.denominator],
                      "divisor": geom.divisor,
                      "branch_denominator_lcm": branch_denominator_lcm,
                      "raw_numerator": raw.numerator, "branches": 3,
                      "fixed_source": None, "joined_edges": sorted(geom.joined_source),
                      "peak_rows": peak, "seconds": round(perf_counter() - began, 3),
                      **binding}, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
