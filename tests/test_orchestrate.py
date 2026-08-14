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


#: Real repo files. ⚠️ `target_files` now REQUIRES a target to resolve to a file that
#: exists — 10 of 95 live group keys did not, including a bare `paper_draft.tex` and a bare
#: `OnsagerAlgebra.lean` that consumed a worktree slot. Fixtures must therefore name real
#: files, which also means these tests exercise the existence requirement rather than
#: mocking past it.
F1, F2, F3 = "src/core/formulas.py", "src/core/constants.py", "scripts/orchestrate.py"


def _f(fid, *, lane="infra", target=F1, severity="major",
       verify=None, status="open", blocked_by=None):
    return {"id": fid, "meta": {"lane": lane, "target": target, "severity": severity,
                                "verify": verify, "status": status,
                                "blocked_by": blocked_by or []}}


# ── the target is a FILE, not a string ────────────────────────────────────────────────

@pytest.mark.parametrize("raw,expected", [
    (f"`{F1}:612-641`", [F1]),                      # line range stripped
    (f"`{F1}:67-69`", [F1]),                        # …and the SAME file
    (F1, [F1]),
    (f"- `{F1}:36-38` (abstract): \"the claim\"", [F1]),   # prose after the path
    (f"SK_EFT_Hawking/{F1}", [F1]),                 # ⚠️ the repo-prefixed spelling that
                                                    #    shipped as a SECOND group key
    (f"`{F1}`, `{F2}`", [F1, F2]),                  # ⚠️ 56 live findings name >1 file;
                                                    #    the second was silently dropped
    ("", []),
    ("a finding with no path at all", []),
    ("`paper_draft.tex`", []),                      # bare basename: not a file from root
    ("`OnsagerAlgebra.lean`", []),                  # …this one consumed wt3
    ("2.5% drift in a doc", []),                    # a version-like token is not a path
])
def test_target_resolves_to_every_file_it_names_and_only_real_ones(raw, expected):
    assert orch.target_files(raw) == expected


def test_two_line_ranges_in_one_file_are_ONE_unit():
    """THE REGRESSION. Grouping on the raw string made these two units, and the planner then
    handed one file to two workers in two worktrees while claiming to prevent exactly that."""
    groups, _ = orch.target_groups([
        _f("a", lane="lean", target=f"`{F1}:612-641`"),
        _f("b", lane="lean", target=f"`{F1}:67-69`"),
    ])
    assert len(groups) == 1, f"one file split into {len(groups)} work units: {groups}"
    assert sorted(groups[0]["findings"]) == ["a", "b"]


def test_no_two_CONCURRENTLY_DISPATCHED_groups_share_a_file():
    """⚠️ THE PROPERTY MOVED, BECAUSE THE DESIGN WAS WRONG — and the earlier version of
    this test could not fail either way.

    v1 read `[g["target"] for g in dispatch]` and asserted uniqueness: those are dict KEYS,
    distinct by construction, so it asserted a property of `dict`. A reviewer restored the
    raw-string resolver and it stayed green with one file in wt2 and wt3.

    v2 asserted disjointness across ALL groups, which forced transitive merging to be true
    — and that merging produced one unit of 107 findings across four lanes.

    A shared file is a resource conflict, so the real invariant is about what runs AT ONCE:
    no two groups dispatched in the same wave may touch the same file. Groups that overlap
    are still valid tasks; they queue.
    """
    p = orch.plan(slots=50)
    assert len(p["dispatch"]) >= 2, "fewer than two dispatched — the property is vacuous"
    held: dict[str, str] = {}
    for g in p["dispatch"]:
        assert g["files"], f"dispatched group {g['target']!r} carries no files"
        for f in g["files"]:
            assert f not in held, (
                f"{f} is dispatched in both {held[f]!r} and {g['target']!r} — two workers, "
                f"one file, in one wave")
            held[f] = g["target"]


def test_an_overlapping_group_is_QUEUED_not_merged_and_not_dropped():
    """The counterpart: a conflict must cost concurrency, never coherence or coverage.
    Merging cost coherence (a 107-finding unit); dropping would cost coverage."""
    p = orch.plan(slots=50)
    ids_dispatched = {i for g in p["dispatch"] for i in g["findings"]}
    ids_queued = {i for g in p["queued_groups"] for i in g["findings"]}
    assert ids_dispatched and ids_queued, "need both populations to assert the split"
    assert not (ids_dispatched & ids_queued), "a finding is both dispatched and queued"
    # ⚠️ Key on the DEFERRAL REASON, not on "overlaps something dispatched". With the
    # conflict guard disabled this test still passed: groups queued by the CAP happened to
    # overlap a dispatched one, so the population was non-empty for an unrelated reason.
    # The decider is whether the conflict guard is what queued them.
    held = {f for g in p["dispatch"] for f in g["files"]}
    blocked = [g for g in p["queued_groups"] if "held by a dispatched group" in (g.get("deferred") or "")]
    assert blocked, (
        "no group was queued BY THE FILE-CONFLICT GUARD — either the guard never engaged "
        "or its reason string changed and this assertion stopped measuring it")
    for g in blocked:
        assert set(g["files"]) & held, (
            f"{g['target']!r} was deferred for a file conflict but shares no file with any "
            f"dispatched group — the reason and the state disagree")


def test_no_two_lean_groups_share_a_worktree_slot():
    p = orch.plan(lane="lean")
    slots = [g["slot"] for g in p["dispatch"] if g.get("slot")]
    assert len(slots) == len(set(slots)), f"a slot is double-booked: {slots}"


# ── refusals: the part that makes this a guard, not a scheduler ───────────────────────

def test_an_untargeted_finding_is_never_grouped():
    """It rendered as a work unit while spanning four lanes. Nobody can be told where to
    work, so it is a filing defect — not a task."""
    groups, untargeted = orch.target_groups([
        _f("a", target=""), _f("b", target="no path here"), _f("c", target=F2),
    ])
    assert [g["target"] for g in groups] == [F2]
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
        _f("a", lane="infra", target=F3),
        _f("b", lane="lean", target=F3),
    ])
    assert groups[0]["lane"] == "lean", "a Lean finding must not be worked without a build gate"
    assert groups[0]["spans_lanes"] == ["infra", "lean"]


def test_a_bare_directory_is_not_a_usable_lean_slot(tmp_path, monkeypatch):
    """⚠️ BOTH ASSERTIONS IN THE FIRST VERSION WERE TAUTOLOGIES — `sorted(x) == sorted(x)`
    and an `is_dir()` loop over names produced BY `is_dir()`. A reviewer replaced
    `lean_slots` with a hardcoded list, which is what the test's own name forbids, and it
    passed. It was also vacuous on a fresh clone: `.claude/worktrees/` is gitignored, so
    the population is empty there and both assertions hold over nothing.

    The decider is "a Lean worker can build here in isolation" — a git worktree with its
    own Lean tree. A leftover `mkdir wt9` was accepted and had a group assigned to it.
    """
    base = tmp_path / ".claude" / "worktrees"
    (base / "wt9").mkdir(parents=True)                       # bare dir: neither leg
    (base / "wt8" / "lean").mkdir(parents=True)              # lean tree, no worktree
    (base / "wt7" / "lean").mkdir(parents=True)
    (base / "wt7" / ".git").write_text("gitdir: ...")        # both legs
    monkeypatch.setattr(orch, "PROJECT_ROOT", tmp_path)
    assert orch.lean_slots() == ["wt7"], (
        "a directory named wtN is not a slot; planning into one sends a Lean worker "
        "somewhere it cannot build")


def test_registry_writing_lanes_carry_the_one_writer_rule():
    """⚠️ THE GUARANTEE THIS PLANNER ADVERTISES DOES NOT COVER WHAT A FIX WRITES.

    Disjointness is computed over DECLARED targets. On 2026-08-13 wt2 and wt3 were dispatched
    as disjoint — their Lean files were — and both then edited `constants.py` and
    `aristotle_interface.py`, because a substrate repair that changes provenance must. They
    merged cleanly only because the two workers happened to touch different regions.

    Serialising the lane on those files would collapse the fan-out, since nearly every
    substrate fix touches them. So the rule is the one already in force for the ledger — a
    registry has ONE writer — and every dispatched unit in a registry-writing lane must carry
    it, or the worker will not know.
    """
    p = orch.plan(slots=50)
    writing = [g for g in p["dispatch"] if g["lane"] in ("lean", "substrate", "pyrust")]
    if not writing:
        pytest.skip("no registry-writing lane dispatched in this plan")
    for g in writing:
        rule = g.get("registry_rule") or ""
        assert "do NOT edit" in rule, (
            f"{g['target']!r} is a {g['lane']} unit dispatched with no registry rule — the "
            f"worker will edit shared registries and collide with its neighbour")
        for reg in orch.SHARED_REGISTRIES:
            assert reg in rule, f"{reg} missing from the rule handed to {g['target']!r}"
    # And the lanes that do NOT write registries must not be handed an irrelevant instruction.
    for g in p["dispatch"]:
        if g["lane"] in ("prose", "research", "infra"):
            assert g.get("registry_rule") is None, (
                f"{g['lane']} carries a registry rule it has no reason to obey; a rule that "
                f"applies to everything is read as boilerplate and ignored where it matters")
