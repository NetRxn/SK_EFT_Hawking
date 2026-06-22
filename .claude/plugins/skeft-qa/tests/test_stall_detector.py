"""Unit tests for the convergence/stall detector (pure core).
Run: uv run python -m pytest SK_EFT_Hawking/.claude/plugins/skeft-qa/tests/ -v"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))
import stall_detector as sd  # noqa: E402


def _atlas(frontier, unknowns=None, nodes=None):
    return {"frontier": frontier, "unknowns": unknowns or [], "nodes": nodes or [], "summary": {}}


def test_stall_when_residual_static_K_events_and_untouched():
    atlas = _atlas(
        frontier=[{"id": "hyp:A", "frontier_impact": 12, "status": "STATED", "is_apex": False}],
        unknowns=[{"id": "hyp:A", "module": "M.A", "atlas_status": "STATED"},
                  {"id": "hyp:B", "module": "M.B", "atlas_status": "STATED"},
                  {"id": "hyp:C", "module": "M.C", "atlas_status": "STATED"}])
    history = [{"compact_event_id": e, "residual_id": "hyp:A", "status": "STATED"} for e in ("e1", "e2", "e3")]
    sig = sd.compute_stall_signal(atlas, history, commits_by_module={"M.A": 5}, k=3, n=2)
    assert sig["stall"] is True
    assert sig["residual_id"] == "hyp:A" and sig["no_advance_events"] >= 3
    assert sig["untouched_count"] >= 2            # M.B, M.C untouched (only M.A had commits)
    assert sig["matched_rung"].startswith("B")    # untouched available -> toehold-sweep


def test_no_stall_when_status_advanced():
    atlas = _atlas(frontier=[{"id": "hyp:A", "frontier_impact": 9, "status": "PROVED", "is_apex": False}],
                   unknowns=[{"id": "hyp:B", "module": "M.B", "atlas_status": "STATED"}])
    history = [{"compact_event_id": "e1", "residual_id": "hyp:A", "status": "STATED"},
               {"compact_event_id": "e2", "residual_id": "hyp:A", "status": "PROVED"}]   # advanced
    sig = sd.compute_stall_signal(atlas, history, {}, k=3, n=1)
    assert sig["stall"] is False and sig["no_advance_events"] < 3


def test_no_stall_without_history():
    atlas = _atlas(frontier=[{"id": "hyp:A", "frontier_impact": 9, "status": "STATED", "is_apex": False}])
    assert sd.compute_stall_signal(atlas, history=[], commits_by_module={}, k=3, n=1)["stall"] is False


def test_no_frontier_is_not_a_stall():
    assert sd.compute_stall_signal(_atlas(frontier=[]), [], {}, k=3, n=1)["stall"] is False


def test_long_no_advance_escalates_to_arc_trace():
    atlas = _atlas(frontier=[{"id": "hyp:A", "frontier_impact": 12, "status": "STATED", "is_apex": False}],
                   unknowns=[{"id": "hyp:A", "module": "M.A", "atlas_status": "STATED"},
                             {"id": "hyp:B", "module": "M.B", "atlas_status": "STATED"},
                             {"id": "hyp:C", "module": "M.C", "atlas_status": "STATED"}])
    history = [{"compact_event_id": "e%d" % i, "residual_id": "hyp:A", "status": "STATED"} for i in range(6)]
    sig = sd.compute_stall_signal(atlas, history, {}, k=3, n=2)
    assert sig["matched_rung"].startswith("E")    # streak >= 2k -> forensic arc-trace


def test_goal_apex_focuses_non_top_residual():
    atlas = _atlas(frontier=[{"id": "hyp:TOP", "frontier_impact": 12, "status": "STATED", "is_apex": False},
                             {"id": "hyp:APEX", "frontier_impact": 4, "status": "STATED", "is_apex": True}])
    sig = sd.compute_stall_signal(atlas, [], {}, k=3, n=1, goal_apex="hyp:APEX")
    assert sig["residual_id"] == "hyp:APEX" and sig["is_apex"] is True


def test_annotated_atlas_module_stem_matches_commits():
    # the atlas `module` field is annotated ("Foo (Phase X...)"); the detector stems it to match a
    # commits map keyed by the bare module path, so untouched-counting works on real atlas data.
    atlas = _atlas(
        frontier=[{"id": "hyp:R", "frontier_impact": 12, "status": "STATED", "is_apex": False}],
        unknowns=[{"id": "hyp:R", "module": "ResidualMod", "atlas_status": "STATED"},
                  {"id": "hyp:T", "module": "TouchedMod (Phase 5q.B, rewired)", "atlas_status": "STATED"},
                  {"id": "hyp:U", "module": "UntouchedMod (alternate route)", "atlas_status": "STATED"}])
    history = [{"compact_event_id": e, "residual_id": "hyp:R", "status": "STATED"} for e in ("e1", "e2", "e3")]
    sig = sd.compute_stall_signal(atlas, history, {"TouchedMod": 3}, k=3, n=1)
    assert "TouchedMod" not in sig["untouched_modules"]      # stem matched the commit key -> touched
    assert "UntouchedMod" in sig["untouched_modules"]        # no commits -> untouched
    assert sig["untouched_count"] == 1


def test_append_history_idempotent_and_capped():
    h = sd.append_history([], "e1", "hyp:A", "STATED")
    h = sd.append_history(h, "e1", "hyp:A", "STATED")     # same (event, residual) -> no dup
    assert len(h) == 1
    h = sd.append_history(h, "e2", "hyp:A", "STATED")
    assert len(h) == 2 and h[-1]["compact_event_id"] == "e2"
    assert sd.append_history(h, None, "hyp:A", "STATED") == h   # no compact_event -> unchanged
