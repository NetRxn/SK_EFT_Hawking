"""The Loops pane reads harness state and refuses to confuse "nothing" with "nothing known".

⚠️ **THE CENTRAL ASSERTION IN THIS FILE IS THE THREE-VALUED STATE.** `.claude/dev-harness/` is
gitignored and local, so on a fresh clone every source is absent. ADR-012 D20 states the
obligation in as many words: the pane *"must say so rather than render an empty roster as 'no
loops running.'"* An empty list is the correct rendering of exactly one of these situations and
a lie about the other.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

import dashboard_loops as dl  # noqa: E402


@pytest.fixture
def harness(tmp_path, monkeypatch):
    h = tmp_path / "dev-harness"
    (h / "managed").mkdir(parents=True)
    monkeypatch.setattr(dl, "HARNESS", h)
    return h


def _marker(h, session, **over):
    m = {k: f"{k}-value" for k in dl.MARKER_KEYS}
    m["question_guard"] = True
    m.update(over)
    (h / "managed" / f"{session}.json").write_text(json.dumps(m))


# ── The three states ──────────────────────────────────────────────────────────────────

def test_an_absent_harness_is_NO_HARNESS_not_an_empty_roster(tmp_path, monkeypatch):
    monkeypatch.setattr(dl, "HARNESS", tmp_path / "does-not-exist")
    got = dl.armed_loops()
    assert got["state"] == "no-harness"
    assert got["loops"] == []
    assert "not the same as no loops running" in got["note"]


def test_a_present_harness_with_no_marker_is_a_MEASURED_zero(harness):
    got = dl.armed_loops()
    assert got["state"] == "none-armed"
    assert "measured zero" in got["note"]


def test_the_two_empty_states_are_DISTINGUISHABLE(tmp_path, monkeypatch, harness):
    """⚠️ THE WHOLE POINT. Both render an empty list; a caller that keys on `loops` alone
    cannot tell "I know there are none" from "I know nothing", and D20 forbids exactly that."""
    armed = dl.armed_loops()
    monkeypatch.setattr(dl, "HARNESS", tmp_path / "nope")
    absent = dl.armed_loops()
    assert armed["loops"] == absent["loops"] == []
    assert armed["state"] != absent["state"]


def test_an_armed_marker_is_reported_with_its_planning_edges(harness):
    _marker(harness, "sess-1", goal_id="g1", roadmap_path="docs/roadmaps/X.md",
            notebook_path="docs/dev-loops/N.md")
    got = dl.armed_loops()
    assert got["state"] == "armed"
    (loop,) = got["loops"]
    # The load-bearing fields: a running loop -> the artifact that authorized it.
    assert loop["roadmap_path"] == "docs/roadmaps/X.md"
    assert loop["notebook_path"] == "docs/dev-loops/N.md"
    assert loop["missing_keys"] == []


def test_a_DISARMED_marker_is_not_counted_as_running(harness):
    """`*.json.cleared-YYYYMMDD` files are how a goal is disarmed. Counting them would report
    loops that ended weeks ago as live — and on this machine both markers are cleared."""
    (harness / "managed" / "old.json.cleared-20260618").write_text("{}")
    assert dl.armed_loops()["state"] == "none-armed"


def test_a_marker_missing_keys_is_REPORTED_not_silently_blank(harness):
    (harness / "managed" / "sess-2.json").write_text(json.dumps({"goal_id": "g2"}))
    (loop,) = dl.armed_loops()["loops"]
    assert set(loop["missing_keys"]) == set(dl.MARKER_KEYS) - {"goal_id"}


def test_an_unreadable_marker_is_reported_rather_than_skipped(harness):
    (harness / "managed" / "broken.json").write_text("{not json")
    (loop,) = dl.armed_loops()["loops"]
    assert loop["unreadable"] is True


# ── The attribution gap D20 got wrong ─────────────────────────────────────────────────

def test_activity_declares_itself_HARNESS_WIDE(harness):
    """⚠️ D20's table says snapshots and stall history are keyed by `goal_id`. Measured: they
    are keyed by TIMESTAMP, and a snapshot's contents carry no goal id either (`head_sha`,
    `last_message`, `transcript_hwm`, `ts`). Presenting a harness-wide heartbeat as one loop's
    heartbeat would be a fabricated join — silently wrong as soon as two loops exist."""
    act = dl.harness_activity()
    assert act["attribution"] == "harness-wide"
    assert "cannot be attributed" in act["attribution_note"]


def test_a_repeating_residual_is_surfaced_as_the_non_convergence_signal(harness):
    sh = harness / "stall_history"
    sh.mkdir()
    sh.joinpath("20260101T000000.json").write_text(json.dumps([
        {"residual_id": "hyp:stuck", "status": "open"},
        {"residual_id": "hyp:stuck", "status": "open"},
        {"residual_id": "hyp:moved", "status": "open"},
    ]))
    got = dl.harness_activity()["repeating_residuals"]
    assert got == [("hyp:stuck", 2)], "a residual seen once must not be reported as repeating"


def test_blocked_questions_absent_is_UNKNOWN_not_zero(harness):
    got = dl.blocked_question_count()
    assert got["available"] is False and got["count"] is None
    assert "unknown, not zero" in got["note"]


def test_blocked_questions_counts_only_non_empty_lines(harness):
    harness.joinpath("blocked_questions.jsonl").write_text('{"q":1}\n\n{"q":2}\n')
    got = dl.blocked_question_count()
    assert got["available"] is True and got["count"] == 2


# ── Against this machine's real harness ───────────────────────────────────────────────

@pytest.mark.slow
def test_the_live_panel_is_internally_consistent():
    """Non-vacuity: the panel must produce a coherent answer against real state, whatever
    that state is. It asserts NO particular count — a machine with no harness is legitimate."""
    p = dl.loops_panel()
    assert p["armed"]["state"] in ("no-harness", "none-armed", "armed")
    if p["armed"]["state"] == "armed":
        assert p["armed"]["loops"], "state says armed but the roster is empty"
    else:
        assert p["armed"]["note"], "an empty roster with no explanation is the forbidden case"
