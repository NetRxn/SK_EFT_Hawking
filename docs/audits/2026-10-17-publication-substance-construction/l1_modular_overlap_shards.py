"""Bounded modular overlap-orbit shards with exact receipt coverage and reduction."""
import argparse
import ast
import json
import os
import sys
from hashlib import sha256
from importlib.util import find_spec
from pathlib import Path
from signal import alarm
from tempfile import NamedTemporaryFile
from time import perf_counter

import numpy
import scipy
import l1_modular_overlap_two as modular
from l1_extended_overlap_run_orbits import temporal_parity
from l1_extended_overlap_schedule_orbits import selected
from l1_extended_overlap_scheduler import assignments, exterior, jobs, left, right
from l1_extended_overlap_sum_orbits import normalized_motif

COLUMN_SHA = "3f15a76fc3ae9af4f3340cfc14626feebee2839c0fb25ead9cf2750ee37bf702"
EXACT_SHARDS = (
    ("00000-00002.rows", 0, 2, "d487deadea8c31337cecc5ac5ffcceaff79a30e3e0422f9b07b7f4ecbe277b32"),
    ("00002-35084.rows", 2, 11, "c0d4aa7fb4885a3be2bd5e3752f44a4d72894197aa9df94e8b6a189777bebbde"),
    ("00011-35084.rows", 11, 66, "a94d6412e0793b1abe95a0c138ef3a1b84406daf1e823c73e89d07e796e8280e"),
    ("00066-35084.rows", 66, 35084, "7f3a9f22590f96a728b01dd49cb7cd822b0affe2b66a38c43d99e6fc5ba41d1d"),
)
PRIME = modular.PRIME
ORBIT_COUNT = 35_084
CANDIDATE_CAP = 4_000_000
ACTIVE_CAP = 32
PARITY_CONTROL = 11
RAW_EXPECTED = 4549345865844500133837056022073964680182394381773293174409658368


def serialized(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def digest(data):
    return sha256(data).hexdigest()


def source_stamp():
    # Bind the local, transitive Python source used to generate coefficients.
    module_dir = Path(__file__).resolve().parent
    pending = [Path(__file__).resolve()]
    hashes = {}
    while pending:
        path = pending.pop()
        if path.name in hashes:
            continue
        data = path.read_bytes()
        hashes[path.name] = digest(data)
        for node in ast.walk(ast.parse(data)):
            names = ([node.module] if isinstance(node, ast.ImportFrom)
                     else [name.name for name in node.names] if isinstance(node, ast.Import)
                     else [])
            for name in names:
                if name and name.startswith("l1_"):
                    expected = module_dir / (name + ".py")
                    loaded = sys.modules.get(name)
                    origin = loaded.__file__ if loaded is not None else find_spec(name).origin
                    actual = Path(origin).resolve(strict=True)
                    if actual != expected:
                        raise ValueError(f"{name} resolved to {actual}, expected {expected}")
                    pending.append(actual)
    return {"local_sources": hashes, "numpy": numpy.__version__, "scipy": scipy.__version__}


def inputs(column_path, exact_dir):
    modular.check_hash(column_path, COLUMN_SHA)
    groups = exterior(column_path)
    full = jobs(groups)
    plan = list(selected(full))
    assert len(plan) == ORBIT_COUNT
    assert sum(weight for _, weight in plan) == len(full) == 589_194
    ledger = []
    for (a, b, c, s, q, t, r), weight in plan:
        count = len(groups[s, q]) * len(groups[t, r])
        active = temporal_parity(s) and temporal_parity(t)
        ledger.append((weight, count, active))
    assert sum(weight * count for weight, count, _ in ledger) == 94_748_063_904
    assert sum(active for _, _, active in ledger) == 770
    assert not ledger[PARITY_CONTROL][2]
    assert max(count for _,count,active in ledger if active) <= CANDIDATE_CAP
    exact = []
    for name, start, stop, sha in EXACT_SHARDS:
        data = (exact_dir / name).read_bytes()
        assert digest(data) == sha
        records = [tuple(map(int, row.split()[:5])) for row in data.splitlines()]
        assert [row[0] for row in records] == list(range(start,stop))
        exact.extend(records)
    assert len(exact) == len(ledger)
    for (idx, weight, count, live, raw), (w, n, active) in zip(exact,ledger,strict=True):
        assert (weight,count) == (w,n) and 0 <= live <= count
        assert active or live == raw == 0
    assert sum(weight * raw for _, weight, _, _, raw in exact) == RAW_EXPECTED
    assert modular.mod_fraction(normalized_motif(RAW_EXPECTED)) == 38375
    stamp = {"prime": PRIME, "column_sha256": COLUMN_SHA, "exact_shards": EXACT_SHARDS,
             "schedule_sha256": digest(serialized(plan)), "sources": source_stamp()}
    return groups, plan, ledger, exact, stamp


def run(groups, plan, ledger, exact, stamp, args):
    start, stop = args.start, args.stop
    assert 0 <= start < stop <= ORBIT_COUNT
    assert sum(active or i == PARITY_CONTROL
               for i, (_, _, active) in enumerate(ledger[start:stop], start)) <= ACTIVE_CAP
    assert not args.output.exists()
    alarm(args.wall_seconds)
    began = perf_counter()
    rows = []
    for idx in range(start,stop):
        weight, count, active = ledger[idx]
        if active or idx == PARITY_CONTROL:
            assert count <= CANDIDATE_CAP
            a,b,c,s,q,t,r = plan[idx][0]
            residue, checked_count, live = modular.mod_join(
                left(a,b), right(c,assignments(q,r,s[5],t[5]),s[7]),groups[s,q],groups[t,r])
            assert checked_count == count
            mode = "joined" if active else "parity-control-joined"
            if not active:
                assert live == residue == 0
        else:
            mode, live, residue = "parity-excluded", 0, 0
        assert 0 <= live <= exact[idx][3] and residue == exact[idx][4] % PRIME
        rows.append([idx, weight, count, mode, live, residue])
    terminal = {"start":start, "stop":stop, "rows":len(rows),
                "row_sha256":digest(serialized(rows)),
                "raw_residue":sum(r[1]*r[5] for r in rows) % PRIME}
    payload = {"stamp_sha256":digest(serialized(stamp)), "rows":rows, "terminal":terminal}
    envelope = {"payload_sha256":digest(serialized(payload)), "payload":payload}
    if source_stamp() != stamp["sources"]:
        raise ValueError("local source changed during replay")
    # Link only a complete, flushed receipt. An existing receipt is immutable.
    with NamedTemporaryFile(dir=args.output.parent, delete=False) as stream:
        temp = Path(stream.name)
        try:
            stream.write(serialized(envelope) + b"\n")
            stream.flush()
            os.fsync(stream.fileno())
            stream.close()
            os.link(temp, args.output)
        finally:
            temp.unlink(missing_ok=True)
    alarm(0)
    print(json.dumps({"range":[start,stop], "seconds":perf_counter()-began, **terminal,
                      "file_sha256":digest(args.output.read_bytes())},sort_keys=True))


def reduce_receipts(ledger, exact, stamp, paths):
    seen, manifest = {}, []
    stamp_hash = digest(serialized(stamp))
    for path in paths:
        data = path.read_bytes()
        envelope = json.loads(data)
        payload = envelope["payload"]
        assert envelope["payload_sha256"] == digest(serialized(payload))
        assert payload["stamp_sha256"] == stamp_hash
        terminal = payload["terminal"]
        rows = payload["rows"]
        start, stop = terminal["start"], terminal["stop"]
        assert 0 <= start < stop <= ORBIT_COUNT
        assert len(rows) == terminal["rows"] == stop-start
        assert [row[0] for row in rows] == list(range(start,stop))
        assert terminal["row_sha256"] == digest(serialized(rows))
        assert terminal["raw_residue"] == sum(r[1]*r[5] for r in rows) % PRIME
        for row in rows:
            idx,weight,count,mode,live,residue = row
            assert idx not in seen
            expected_weight, expected_count, active = ledger[idx]
            expected_mode = ("joined" if active else "parity-control-joined"
                             if idx == PARITY_CONTROL else "parity-excluded")
            assert (weight,count,mode) == (expected_weight,expected_count,expected_mode)
            assert (0 <= live <= exact[idx][3] and residue == exact[idx][4] % PRIME)
            assert active or live == residue == 0
            seen[idx] = row
        manifest.append((start,stop,digest(data)))
    if len(seen) != ORBIT_COUNT:
        missing = set(range(ORBIT_COUNT)) - seen.keys()
        raise ValueError(f"incomplete modular motif: {len(missing)} missing, first {min(missing)}")
    assert sum(r[1] for r in seen.values()) == 589_194
    assert sum(r[1]*r[2] for r in seen.values()) == 94_748_063_904
    assert sum(r[3] == "joined" for r in seen.values()) == 770
    raw_residue = sum(r[1]*r[5] for r in seen.values()) % PRIME
    coefficient = raw_residue * modular.mod_fraction(normalized_motif(1)) % PRIME
    assert raw_residue == RAW_EXPECTED % PRIME and coefficient == 38375
    print(json.dumps({"orbit_count":len(seen), "raw_residue":raw_residue,
                      "motif_residue":coefficient, "terminal_shards":sorted(manifest),
                      "coverage_sha256":digest(serialized(sorted(manifest)))},sort_keys=True))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("column",type=Path)
    parser.add_argument("exact_receipts",type=Path)
    sub = parser.add_subparsers(dest="mode",required=True)
    roster = sub.add_parser("plan")
    roster.add_argument("--joins-per-shard",type=int,default=8)
    replay = sub.add_parser("run")
    replay.add_argument("start",type=int)
    replay.add_argument("stop",type=int)
    replay.add_argument("output",type=Path)
    replay.add_argument("--wall-seconds",type=int,default=300)
    reduce = sub.add_parser("reduce")
    reduce.add_argument("receipts",type=Path,nargs="+")
    args = parser.parse_args()
    if not __debug__:
        parser.error("assertion guards must remain enabled")
    if args.mode == "run" and not 1 <= args.wall_seconds <= 900:
        parser.error("wall limit must be between 1 and 900 seconds")
    groups,plan,ledger,exact,stamp = inputs(args.column,args.exact_receipts)
    if args.mode == "run":
        run(groups,plan,ledger,exact,stamp,args)
    elif args.mode == "reduce":
        reduce_receipts(ledger,exact,stamp,args.receipts)
    else:
        assert 1 <= args.joins_per_shard <= ACTIVE_CAP
        jobs = [(idx,count) for idx,(_,count,active) in enumerate(ledger)
                if active or idx == PARITY_CONTROL]
        starts = [0] + [idx for idx,_ in jobs[args.joins_per_shard::args.joins_per_shard]]
        ends = starts[1:] + [ORBIT_COUNT]
        print(json.dumps({"stamp_sha256":digest(serialized(stamp)), "prime":PRIME,
                          "raw_expected_residue":RAW_EXPECTED%PRIME,
                          "ranges":[[start,stop,sum(start <= idx < stop for idx,_ in jobs),
                                     sum(count for idx,count in jobs if start <= idx < stop)]
                                    for start,stop in zip(starts,ends,strict=True)]}))


if __name__ == "__main__":
    main()
