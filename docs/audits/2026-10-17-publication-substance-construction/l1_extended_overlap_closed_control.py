"""Check that Haar projection commutes with the complete lower exterior join."""
from itertools import groupby
from pathlib import Path
from sys import argv

from l1_extended_overlap_strip import HAAR, PAIRS


def raw_offsets(stream):
    offsets = {}
    previous = None
    while True:
        offset = stream.tell()
        line = stream.readline()
        if not line:
            return offsets
        pair = tuple(map(int, line.split(None, 2)[:2]))
        if pair != previous:
            if pair in offsets or pair not in PAIRS:
                raise ValueError(f"invalid raw pair group {pair}")
            offsets[pair] = offset
            previous = pair


def late_projection(stream, offsets, pair):
    result = {}
    for i, weight in HAAR[pair]:
        raw_pair = PAIRS[i]
        if raw_pair not in offsets:
            continue
        stream.seek(offsets[raw_pair])
        for line in stream:
            a, b, key, re, im = map(int, line.split())
            if (a, b) != raw_pair:
                break
            old_re, old_im = result.get(key, (0, 0))
            result[key] = old_re + weight * re, old_im + weight * im
    return {key: value for key, value in result.items() if any(value)}


def compare(raw_path, projected_path):
    seen = set()
    entries = 0
    with raw_path.open("rb") as raw, projected_path.open() as projected:
        offsets = raw_offsets(raw)
        for pair, group in groupby((tuple(map(int, line.split())) for line in projected),
                                   key=lambda row: row[:2]):
            if pair in seen or pair not in PAIRS:
                raise ValueError(f"noncontiguous projected pair {pair}")
            seen.add(pair)
            early = {}
            for _, _, key, re, im in group:
                if key in early:
                    raise ValueError(f"duplicate projected key {pair}, {key}")
                early[key] = re, im
            if early != late_projection(raw, offsets, pair):
                raise AssertionError(f"closed lower column mismatch at {pair}")
            entries += len(early)
        for pair in set(PAIRS) - seen:
            if late_projection(raw, offsets, pair):
                raise AssertionError(f"missing projected pair {pair}")
    return len(seen), entries


if __name__ == "__main__":
    print("matching closed pairs and entries", *compare(Path(argv[1]), Path(argv[2])))
