"""Checkpoint exact B-only maps over a disjoint interval of the guarded roster."""

from argparse import ArgumentParser
from collections import Counter
from fcntl import LOCK_EX, LOCK_NB, flock
from hashlib import sha256
from pathlib import Path
import re
import signal
import sys

from l1_unpaired_B_census import BEvaluator, exact_primitive, indexed_roster, read_low_roster
from l1_unpaired_offset_factors import prepare

HEADER = "index q51,q53,q71,q73,q133,q151,q153 state rows B_exact B_primitive B_scale"
DIGEST = re.compile(r"[0-9a-f]{64}")
CHUNK_NAME = re.compile(r"B_(\d+)_(\d+)\.rows")


def coordinates(word):
    return ",".join(map(str, word))


def atomic_write(path, text):
    scratch = path.with_suffix(".tmp")
    scratch.write_text(text)
    scratch.replace(path)


def exact_row(index, word, state, rows):
    fields = [index, coordinates(word), state]
    if state == "B-nonzero":
        exact, primitive, scale = exact_primitive(rows)
        fields.extend((len(exact), sha256(repr(exact).encode()).hexdigest(),
                       sha256(repr(primitive).encode()).hexdigest(), scale))
    else:
        assert state == "B-zero" and not rows
    return " ".join(map(str, fields))


def read_checkpoint(path, low, high, roster):
    if not path.exists():
        return {}
    header, *lines = path.read_text().splitlines()
    if header != HEADER:
        raise ValueError(f"unrecognized receipt header in {path}")
    exact = {}
    for line in lines:
        index, word, state, *payload = line.split()
        index = int(index)
        if not low <= index < high or index in exact or word != coordinates(roster[index]):
            raise ValueError(f"invalid or duplicate receipt index in {path}: {index}")
        if state == "B-nonzero":
            if (len(payload) != 4 or not 0 < int(payload[0]) <= 28**4
                    or not all(DIGEST.fullmatch(digest) for digest in payload[1:3])
                    or not int(payload[3])):
                raise ValueError(f"invalid nonzero receipt payload in {path}: {index}")
        elif state != "B-zero" or payload:
            raise ValueError(f"receipt is not exact in {path}: {index}")
        exact[index] = line
    return exact


def input_stamp(roster, low_receipts):
    """Bind the ordered roster and exact local Python sources used to derive it."""
    here = Path(__file__).resolve().parent
    sources = {Path(__file__).resolve()}
    for module in tuple(sys.modules.values()):
        filename = getattr(module, "__file__", None)
        if filename:
            source = Path(filename).resolve()
            if source.parent == here and source.suffix == ".py":
                sources.add(source)
    source_rows = [f"python {path.name} {sha256(path.read_bytes()).hexdigest()}"
                   for path in sorted(sources)]
    receipt_rows = [f"low-receipt {digest}" for digest in sorted(
        sha256(path.read_bytes()).hexdigest() for path in low_receipts)]
    roster_digest = sha256("\n".join(map(coordinates, roster)).encode()).hexdigest()
    return "\n".join([f"indexed-roster {roster_digest}", *source_rows, *receipt_rows]) + "\n"


def replay(args):
    factors = prepare()
    roster = indexed_roster(factors, read_low_roster(args.low_receipt))
    stamp = args.receipt_dir / "inputs.sha256"
    inputs = input_stamp(roster, args.low_receipt)
    if stamp.exists():
        if stamp.read_text() != inputs:
            raise ValueError("existing receipts belong to different evaluator inputs")
    else:
        if any(args.receipt_dir.glob("B_*.rows")):
            raise ValueError("existing receipts lack an evaluator input stamp")
        atomic_write(stamp, inputs)

    chunks = [(low, min(low + args.chunk, args.stop))
              for low in range(args.start, args.stop, args.chunk)]
    for path in args.receipt_dir.glob("B_*.rows"):
        match = CHUNK_NAME.fullmatch(path.name)
        if not match:
            raise ValueError(f"unrecognized receipt path: {path}")
        low, high = map(int, match.groups())
        if not 0 <= low < high <= len(roster):
            raise ValueError(f"invalid receipt interval: {path}")
        if low < args.stop and args.start < high and (low, high) not in chunks:
            raise ValueError(f"partially overlapping receipt interval: {path}")

    def path_for(low, high):
        return args.receipt_dir / f"B_{low}_{high}.rows"

    completed = {(low, high): read_checkpoint(path_for(low, high), low, high, roster)
                 for low, high in chunks}

    def save_resume():
        rows = ["start stop exact missing_indices"]
        for (low, high), exact in completed.items():
            missing = ",".join(str(i) for i in range(low, high) if i not in exact) or "-"
            rows.append(f"{low} {high} {len(exact)} {missing}")
        atomic_write(args.receipt_dir / f"resume_{args.start}_{args.stop}.txt", "\n".join(rows) + "\n")

    save_resume()
    evaluator = None
    for (low, high), exact in completed.items():
        if len(exact) == high - low:
            continue
        if evaluator is None:
            evaluator = BEvaluator(factors)
        pending = (i for i in range(low, high) if i not in exact)
        controls = 0
        try:
            for index in sorted(pending, key=lambda i: (tuple(roster[i][k] for k in (1, 4, 5)), i)):
                word = roster[index]
                state, rows = evaluator.evaluate(word)
                if state == "B-cap":
                    print("unresolved cap", index, rows, flush=True)
                    continue
                if controls < 12:
                    assert rows == evaluator.direct(word)
                    controls += 1
                exact[index] = exact_row(index, word, state, rows)
        except TimeoutError:
            print("wall limit reached", flush=True)
            break
        finally:
            text = "\n".join([HEADER, *(exact[i] for i in sorted(exact))]) + "\n"
            atomic_write(path_for(low, high), text)
            save_resume()
            counts = Counter(row.split()[2] for row in exact.values())
            print("checkpoint", low, high, dict(counts), sha256(text.encode()).hexdigest(), flush=True)

    count = sum(map(len, completed.values()))
    print("exact B coverage", count, "of", args.stop - args.start)
    return count == args.stop - args.start


def timeout(*_):
    raise TimeoutError("B replay wall limit reached")


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--low-receipt", action="append", type=Path, required=True)
    parser.add_argument("--receipt-dir", type=Path, required=True)
    parser.add_argument("--start", type=int, required=True)
    parser.add_argument("--stop", type=int, required=True)
    parser.add_argument("--chunk", type=int, default=1024)
    parser.add_argument("--wall-seconds", type=int, default=600)
    args = parser.parse_args()
    if (not 0 <= args.start < args.stop <= 77_472 or not 1 <= args.chunk <= 1024
            or not 1 <= args.wall_seconds <= 600):
        parser.error("invalid half-open interval, chunk size, or wall limit")
    args.receipt_dir.mkdir(parents=True, exist_ok=True)
    with (args.receipt_dir / ".writer.lock").open("a") as lock:
        flock(lock, LOCK_EX | LOCK_NB)
        signal.signal(signal.SIGALRM, timeout)
        signal.alarm(args.wall_seconds)
        try:
            complete = replay(args)
        finally:
            signal.alarm(0)
    raise SystemExit(0 if complete else 2)


if __name__ == "__main__":
    main()
