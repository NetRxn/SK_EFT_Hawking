"""Evaluate an indexed shard of the exact L1 curvature orbit schedule."""
from argparse import ArgumentParser
from time import perf_counter

from l1_extended_overlap_schedule_orbits import selected
from l1_extended_overlap_scheduler import assignments, exterior, jobs, kernel, left, right


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
    if not 0 <= args.start < args.stop <= len(plan):
        parser.error("require 0 <= start < stop <= 35084")

    for index in range(args.start, args.stop):
        (a, b, c, s, q, t, r), weight = plan[index]
        started = perf_counter()
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
