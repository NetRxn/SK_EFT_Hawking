"""Unit tests for the skeft-qa dev-harness core (resolver + gate + re-injection).
Run: uv run python -m pytest SK_EFT_Hawking/.claude/plugins/skeft-qa/tests/ -v"""
import json
import sys
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent.parent / "scripts"
sys.path.insert(0, str(SCRIPTS))
import harness_common as hc  # noqa: E402


def _marker(root, sid, m):
    d = Path(root) / ".claude" / "skeft-harness" / "managed"
    d.mkdir(parents=True, exist_ok=True)
    (d / f"{sid}.json").write_text(json.dumps(m))


def test_inert_when_repo_unresolved(monkeypatch):
    monkeypatch.setattr(hc, "repo_root", lambda *a, **k: None)
    assert hc.read_marker({"session_id": "abc"}) is None


def test_inert_when_no_marker(tmp_path, monkeypatch):
    monkeypatch.setattr(hc, "repo_root", lambda *a, **k: tmp_path)
    assert hc.read_marker({"session_id": "abc"}) is None


def test_inert_for_subagent(tmp_path, monkeypatch):
    monkeypatch.setattr(hc, "repo_root", lambda *a, **k: tmp_path)
    _marker(tmp_path, "abc", {"role": "solo"})
    assert hc.read_marker({"session_id": "abc", "agent_id": "sub-1"}) is None


def test_inert_without_session_id(tmp_path, monkeypatch):
    monkeypatch.setattr(hc, "repo_root", lambda *a, **k: tmp_path)
    assert hc.read_marker({}) is None


def test_returns_marker_when_present(tmp_path, monkeypatch):
    monkeypatch.setattr(hc, "repo_root", lambda *a, **k: tmp_path)
    _marker(tmp_path, "abc", {"role": "solo", "goal": "ship W4", "goal_id": "20260617T101500",
                              "jsonl_path": "/x.jsonl", "question_guard": True})
    m = hc.read_marker({"session_id": "abc"})
    assert m and m["role"] == "solo" and m["goal"] == "ship W4" and m["question_guard"] is True
    assert m["goal_id"] == "20260617T101500"   # 8-field marker carries goal_id (spec A.5)


def test_payload_includes_goal_and_heuristics_without_active_issues(tmp_path):
    # active_issues.json absent -> section omitted gracefully, no error.
    payload = hc.build_reorientation_payload({"goal": "ship Wave 4"}, tmp_path)
    assert "ship Wave 4" in payload
    assert "re-read claude.md" in payload.lower()   # case-insensitive: payload has "Re-read CLAUDE.md"
    assert "Decision heuristics" in payload
    assert "Active System-2 issues" not in payload  # absent -> omitted


def test_payload_includes_active_issues_when_present(tmp_path):
    d = tmp_path / ".claude" / "skeft-harness"
    d.mkdir(parents=True, exist_ok=True)
    (d / "active_issues.json").write_text(json.dumps(
        {"issues": [{"summary": "re-polluted roadmap at compaction 3"}]}))
    payload = hc.build_reorientation_payload({"goal": "g"}, tmp_path)
    assert "Active System-2 issues" in payload
    assert "re-polluted roadmap at compaction 3" in payload


def test_payload_repo_none_omits_active_issues(tmp_path):
    payload = hc.build_reorientation_payload({"goal": "g"}, None)
    assert "Active System-2 issues" not in payload and "g" in payload


def test_payload_capped_under_9000_with_full_goal(tmp_path):
    # review C1: an oversized active-issues view must NOT push the payload over the cap;
    # the /goal condition is always kept in full while active-issues is truncated.
    d = tmp_path / ".claude" / "skeft-harness"
    d.mkdir(parents=True, exist_ok=True)
    big = [{"summary": "drift finding " + str(i) + " " + ("x" * 300),
            "tier": "agent-reviewed", "tally": i} for i in range(200)]
    (d / "active_issues.json").write_text(json.dumps({"issues": big}))
    goal = "GOAL: ship Wave 4; validate.py prints 43/43 in the transcript " + ("z" * 3000)
    payload = hc.build_reorientation_payload({"goal": goal}, tmp_path)
    assert len(payload) < 9000                       # hard cap (< the 10k additionalContext limit)
    assert goal in payload                           # the /goal condition is always in full
    assert "Decision heuristics" in payload          # heuristics retained
    # at most the top-8 findings survive (truncated further to fit the cap):
    assert payload.count("- drift finding ") <= 8


def test_find_workspace_resolves_repo_cwd_based(tmp_path):
    # The BLOCKER fix: resolve the repo CWD-BASED (no $CLAUDE_PLUGIN_ROOT). Build a fake
    # workspace: <ws>/.mcp.json + <ws>/SK_EFT_Hawking/ (and <ws> is NOT a git repo).
    ws = tmp_path / "workspace"
    (ws / "SK_EFT_Hawking").mkdir(parents=True)
    (ws / ".mcp.json").write_text("{}")
    repo = (ws / "SK_EFT_Hawking").resolve()
    assert hc.find_workspace(str(ws)) == ws.resolve()
    assert hc.repo_root(str(ws)) == repo                       # from the workspace root
    assert hc.repo_root(str(ws / "SK_EFT_Hawking")) == repo    # from inside the repo
    assert hc.repo_root(str(tmp_path)) is None                 # outside any workspace -> inert
