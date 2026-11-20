"""Reconcile orbit shards against the plan before summing the exact result."""
from fractions import Fraction
from sys import argv

from l1_extended_overlap_curvature_bound import numerator_bound
from l1_extended_overlap_schedule_orbits import selected
from l1_extended_overlap_scheduler import exterior, jobs


def sum_shards(plan, paths):
    results = {}
    for path in paths:
        with open(path) as stream:
            for line in stream:
                index, weight, pairs, live, value = map(int, line.split()[:5])
                if index not in plan or index in results:
                    raise ValueError(f"unexpected or duplicate orbit index {index}")
                if (weight, pairs) != plan[index] or not 0 <= live <= pairs:
                    raise ValueError(f"invalid coverage at orbit index {index}")
                results[index] = weight * value
    missing = plan.keys() - results.keys()
    if missing:
        raise ValueError(f"{len(missing)} missing orbit indices, first {min(missing)}")
    return sum(results.values())


def normalized_motif(raw):
    curvature = Fraction(raw, 48**8 * 4**4)
    lower_frames = (48 * 4**16)**2
    upper_frames = 8**16 * 4**32 * 2**8
    upper_sheets = Fraction(52489, 10368)**2
    return curvature * upper_sheets / (lower_frames * upper_frames)


if __name__ == "__main__":
    groups = exterior(argv[1])
    plan = {
        index: (weight, len(groups[s, q]) * len(groups[t, r]))
        for index, ((_, _, _, s, q, t, r), weight) in enumerate(selected(jobs(groups)))
    }
    assert len(plan) == 35_084
    assert sum(weight for weight, _ in plan.values()) == 589_194
    assert sum(weight * pairs for weight, pairs in plan.values()) == 94_748_063_904
    raw = sum_shards(plan, argv[2:])
    assert abs(raw) <= numerator_bound(argv[1])
    print("raw numerator", raw)
    print("after curvature normalization", Fraction(raw, 48**8 * 4**4))
    print("normalized finite motif", normalized_motif(raw))
