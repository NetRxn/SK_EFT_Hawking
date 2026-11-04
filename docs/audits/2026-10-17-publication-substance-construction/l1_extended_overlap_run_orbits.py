"""Evaluate an indexed shard of the exact L1 curvature orbit schedule."""
from argparse import ArgumentParser
from time import perf_counter

from l1_extended_overlap_schedule_orbits import selected
from l1_extended_overlap_scheduler import assignments, exterior, jobs, kernel, left, right


def temporal_parity(signature):
    """An unfixed node pairs strips of the same chiral parity."""
    strips = ((0, 2), (6, 4), (7, 5), (1, 3))
    return len({signature[a] ^ signature[b] for a, b in strips}) == 1


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("column_rows")
    parser.add_argument("start", type=int)
    parser.add_argument("stop", type=int)
    args = parser.parse_args()

    groups = exterior(args.column_rows)
    full = jobs(groups)
    plan = list(selected(full))
    assert len(plan) == 35_084
    assert sum(weight for _, weight in plan) == len(full) == 589_194
    assert sum(
        weight * len(groups[s, q]) * len(groups[t, r])
        for (_, _, _, s, q, t, r), weight in plan
    ) == 94_748_063_904
    assert sum(temporal_parity(s) and temporal_parity(t)
               for (_, _, _, s, _, t, _), _ in plan) == 770
    if not 0 <= args.start < args.stop <= len(plan):
        parser.error("require 0 <= start < stop <= 35084")

    for index in range(args.start, args.stop):
        (a, b, c, s, q, t, r), weight = plan[index]
        started = perf_counter()
        if not (temporal_parity(s) and temporal_parity(t)):
            count = len(groups[s, q]) * len(groups[t, r])
            print(index, weight, count, 0, 0, 0.0, flush=True)
            continue
        value, count, live, _ = kernel(
            left(a, b),
            right(c, assignments(q, r, s[5], t[5]), s[7]),
            groups[s, q],
            groups[t, r],
        )
        assert count == len(groups[s, q]) * len(groups[t, r])
        print(index, weight, count, live, value, perf_counter() - started, flush=True)


if __name__ == "__main__":
    main()
