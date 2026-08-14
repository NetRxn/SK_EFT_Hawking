"""Both-directions tests for `scripts/orchestrate.py` — ADR-012 P10.

⚠️ **THE ORCHESTRATOR'S FAILURE MODE IS NOT CRASHING, IT IS DISPATCHING CONFIDENTLY.** A
planner that routes work to the wrong profile, splits one file across two worktrees, or marks
an unverifiable finding closable produces a plan that reads exactly like a correct one — and
at fan-out speed it does so hundreds of times before anyone reads a diff. Every test here is
about a *plausible* plan being wrong, not about an exception.

Two of these encode defects the first draft actually shipped, both caught by running it
against the live queue rather than by reading it:

  * `(untargeted)` collected 20 findings spanning four lanes into one pseudo-group that
    rendered identically to a real work unit;
  * grouping on the raw `Target:` string put `DriveCalibration.lean:612-641` and
    `…:67-69` in **wt2 and wt3** — two workers, one file, which is the exact collision
    target-grouping exists to prevent.
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

import orchestrate as orch  # noqa: E402


def _f(fid, *, lane="infra", target="src/x.py", severity="major",
       verify=None, status="open", blocked_by=None):
    return {"id": fid, "meta": {"lane": lane, "target": target, "severity": severity,
                                "verify": verify, "status": status,
                                "blocked_by": blocked_by or []}}


# ── the target is a FILE, not a string ────────────────────────────────────────────────

@pytest.mark.parametrize("raw,expected", [
    ("`lean/SKEFTHawking/Control/DriveCalibration.lean:612-641`",
     "lean/SKEFTHawking/Control/DriveCalibration.lean"),
    ("`lean/SKEFTHawking/Control/DriveCalibration.lean:67-69`",
     "lean/SKEFTHawking/Control/DriveCalibration.lean"),
    ("src/core/formulas.py", "src/core/formulas.py"),
    ("- `papers/note/paper_draft.tex:36-38` (abstract): \"the claim\"",
     "papers/note/paper_draft.tex"),
    ("", ""),
    ("a finding with no path at all", ""),
])
def test_target_resolves_to_the_file(raw, expected):
    assert orch.target_file(raw) == expected


def test_two_line_ranges_in_one_file_are_ONE_unit():
    """THE REGRESSION. Grouping on the raw string made these two units, and the planner then
    handed one file to two workers in two worktrees while claiming to prevent exactly that."""
    groups, _ = orch.target_groups([
        _f("a", lane="lean", target="`lean/SKEFTHawking/Control/DriveCalibration.lean:612-641`"),
        _f("b", lane="lean", target="`lean/SKEFTHawking/Control/DriveCalibration.lean:67-69`"),
    ])
    assert len(groups) == 1, f"one file split into {len(groups)} work units: {groups}"
    assert sorted(groups[0]["findings"]) == ["a", "b"]


def test_no_two_dispatched_groups_share_a_file():
    """The property, asserted over the LIVE queue rather than a fixture — a fixture cannot
    show that real targets normalize to distinct files."""
    p = orch.plan()
    files = [g["target"] for g in p["dispatch"]]
    assert len(files) == len(set(files)), f"a file is dispatched twice: {files}"


def test_no_two_lean_groups_share_a_worktree_slot():
    p = orch.plan(lane="lean")
    slots = [g["slot"] for g in p["dispatch"] if g.get("slot")]
    assert len(slots) == len(set(slots)), f"a slot is double-booked: {slots}"


# ── refusals: the part that makes this a guard, not a scheduler ───────────────────────

def test_an_untargeted_finding_is_never_grouped():
    """It rendered as a work unit while spanning four lanes. Nobody can be told where to
    work, so it is a filing defect — not a task."""
    groups, untargeted = orch.target_groups([
        _f("a", target=""), _f("b", target="no path here"), _f("c", target="src/y.py"),
    ])
    assert [g["target"] for g in groups] == ["src/y.py"]
    assert {n["id"] for n in untargeted} == {"a", "b"}


def test_a_finding_with_no_verify_is_planned_but_not_closable():
    """`close_finding` skips verification when none is declared, so closing such a finding
    writes `fixed` with an empty `verified_by` — a record nothing proved."""
    assert orch.closable(_f("a", verify="uv run pytest -q")) is True
    assert orch.closable(_f("b", verify=None)) is False
    assert orch.closable(_f("c", verify="   ")) is False
    groups, _ = orch.target_groups([_f("a", verify="x"), _f("b", verify=None)])
    g = groups[0]
    assert g["closable"] == ["a"] and g["unverifiable"] == ["b"]


def test_an_unrouted_finding_is_not_coerced_into_a_lane():
    """A default lane would hand physics work to an infra worker and read, downstream, like
    routing that succeeded."""
    parts = orch.classify([_f("a", lane=None), _f("b", lane="lean")], {"a", "b"}, set())
    assert [n["id"] for n in parts["unrouted"]] == ["a"]
    assert [n["id"] for n in parts["dispatchable"]] == ["b"]


def test_the_three_buckets_partition_the_open_population():
    """A finding in none of them is work the queue silently forgot."""
    p = orch.plan()
    c = p["counts"]
    assert c["dispatchable"] + c["blocked"] + c["unrouted"] == c["open"]


def test_an_empty_population_raises_rather_than_planning_nothing():
    """A plan with nothing to do is indistinguishable from a queue this tool failed to read
    (guide §2.5)."""
    with pytest.raises(RuntimeError, match="EMPTY"):
        orch.plan.__wrapped__() if hasattr(orch.plan, "__wrapped__") else _empty_plan()


def _empty_plan():
    import build_graph
    orig = build_graph.extract_review_finding_nodes
    build_graph.extract_review_finding_nodes = lambda *a, **k: []
    try:
        return orch.plan()
    finally:
        build_graph.extract_review_finding_nodes = orig


# ── the routing table is not allowed to drift from the validated vocabulary ───────────

def test_every_routable_lane_is_a_lane_the_check_accepts():
    """`LANE_PROFILE`'s keys and `reviews.py`'s validated vocabulary are the same set. A lane
    this router understands but the check rejects would be unroutable-in-practice; a lane the
    check accepts but the router does not would silently join the unrouted pile."""
    # The vocabulary is OWNED by `build_graph`; `reviews.py` imports it from there. Importing
    # it from the check would test a re-export, not the source of truth.
    from build_graph import _LANE_DECL_MAP
    assert set(orch.LANE_PROFILE) == set(_LANE_DECL_MAP), (
        f"router {sorted(orch.LANE_PROFILE)} vs check {sorted(_LANE_DECL_MAP)}")


def test_lane_strength_ranks_every_lane_exactly_once():
    """A lane missing from the order makes `next(...)` raise on a spanning target; a
    duplicate makes the winner depend on tuple order rather than a stated rule."""
    assert sorted(orch.LANE_STRENGTH) == sorted(orch.LANE_PROFILE)
    assert len(orch.LANE_STRENGTH) == len(set(orch.LANE_STRENGTH))


def test_a_spanning_target_gets_the_strongest_profile_not_the_first_alphabetically():
    """The first draft used `sorted(lanes)[0]` and called it 'strongest'. For
    {infra, prose} that yields `infra` by luck; for {prose, research} it yields `prose`,
    also by luck — and for {lean, infra} it would yield `infra`, dropping the build gate."""
    groups, _ = orch.target_groups([
        _f("a", lane="infra", target="src/z.py"),
        _f("b", lane="lean", target="src/z.py"),
    ])
    assert groups[0]["lane"] == "lean", "a Lean finding must not be worked without a build gate"
    assert groups[0]["spans_lanes"] == ["infra", "lean"]


def test_lean_slots_are_read_from_disk_not_hardcoded():
    slots = orch.lean_slots()
    assert slots == sorted(slots)
    for s in slots:
        assert (ROOT / ".claude" / "worktrees" / s).is_dir()
