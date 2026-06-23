"""Unit tests for the skeft-qa dev-harness core (resolver + gate + re-injection).
Run: uv run python -m pytest SK_EFT_Hawking/.claude/plugins/skeft-qa/tests/ -v"""
import json
import sys
import time
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent.parent / "scripts"
sys.path.insert(0, str(SCRIPTS))
import harness_common as hc  # noqa: E402


def _marker(root, sid, m):
    d = Path(root) / ".claude" / "dev-harness" / "managed"
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


def test_payload_baseline_without_coaching(tmp_path):
    # No coaching cache -> the baseline (goal + RE-ANCHOR + re-read + the MANDATED PRE_DECISIONS read)
    # is fully functional; the coaching block is a pure enhancement, never required.
    payload = hc.build_reorientation_payload({"goal": "ship Wave 4", "goal_id": "g1"}, tmp_path)
    assert "ship Wave 4" in payload
    assert "RE-ANCHOR before resuming" in payload                  # always-on re-anchor present
    assert "LIVENESS" in payload and "/goal-end" in payload         # the liveness self-check (don't resume a dead goal)
    assert "re-read claude.md" in payload.lower()
    assert "READ docs/dev-loops/PRE_DECISIONS.md" in payload       # pre-decisions = MANDATORY READ
    assert "Decision heuristics" not in payload                    # Core/heuristics NOT injected anymore
    assert "COACHING BLOCK (" not in payload                       # absent -> omitted (RE_ANCHOR names it, hence "(")


def test_payload_mandates_predecisions_read_not_injected(tmp_path):
    # Pre-decisions are NO LONGER injected (they grow unbounded) — the payload MANDATES reading
    # docs/dev-loops/PRE_DECISIONS.md instead; even when the file exists its body is NOT inlined.
    pd = tmp_path / "docs" / "dev-loops" / "PRE_DECISIONS.md"
    pd.parent.mkdir(parents=True, exist_ok=True)
    pd.write_text("# Pre-Decisions\n\n## Core\n\n### PD-0 — keystone\nscale pre-accepted.\n\n## Full\n\ntail.\n")
    payload = hc.build_reorientation_payload({"goal": "g", "goal_id": "g1"}, tmp_path)
    assert "READ docs/dev-loops/PRE_DECISIONS.md" in payload       # the mandatory read
    assert "scale pre-accepted" not in payload                    # Core body NOT inlined
    assert "PRE-DECISIONS (always-on" not in payload              # the old injected prefix is gone
    assert hc._read_predecisions_core(None) == hc.DECISION_HEURISTICS   # helper kept; fail-soft on None


def test_payload_includes_frontier_when_index_present(tmp_path):
    # the live FRONTIER digest is injected verbatim so a post-compaction turn needs zero Reads
    import notebook_lib as nbl  # noqa: E402
    nbl.op_new(tmp_path)
    idx = tmp_path / "LAB_NOTEBOOK_INDEX.md"
    idx.write_text(idx.read_text().replace(
        "- **NEXT BRICK:** (the single next action — numbered).",
        "- **NEXT BRICK:** ship brick 42."))
    payload = hc.build_reorientation_payload(
        {"goal": "g", "notebook_path": str(idx)}, tmp_path)
    assert "LAB-NOTEBOOK FRONTIER (" in payload and "ship brick 42" in payload


def test_payload_omits_frontier_without_notebook_path(tmp_path):
    payload = hc.build_reorientation_payload({"goal": "g"}, tmp_path)
    assert "LAB-NOTEBOOK FRONTIER (" not in payload  # graceful when no notebook_path (RE_ANCHOR names it)


def test_payload_includes_coaching_block_when_present(tmp_path):
    # the per-goal coaching block (harvest-authored) is injected with a freshness label
    d = tmp_path / ".claude" / "dev-harness" / "coaching"
    d.mkdir(parents=True, exist_ok=True)
    (d / "g1.json").write_text(json.dumps(
        {"authored_ts": time.time(), "text": "close-path: discharge subHomConnecting_openDuality"}))
    payload = hc.build_reorientation_payload({"goal": "g", "goal_id": "g1"}, tmp_path)
    assert "COACHING BLOCK (" in payload
    assert "close-path: discharge subHomConnecting_openDuality" in payload
    assert "authored" in payload and "ago" in payload            # authoring FACTS (timestamp + age), not a verdict


def test_payload_coaching_block_carries_facts_not_a_verdict(tmp_path):
    # The harness surfaces AUTHORING FACTS (timestamp, age, transcript high-water-mark) + a brief
    # process note, and lets the loop judge — it does NOT bake in a staleness verdict (a fixed age
    # threshold would misjudge a fast goal vs a slow one and could add unanticipated failure modes).
    d = tmp_path / ".claude" / "dev-harness" / "coaching"
    d.mkdir(parents=True, exist_ok=True)
    (d / "g1.json").write_text(json.dumps(
        {"authored_ts": time.time() - 10 * 3600, "watermark": 48213, "text": "old close-path"}))
    payload = hc.build_reorientation_payload({"goal": "g", "goal_id": "g1"}, tmp_path)
    assert "~10h ago" in payload                          # the age FACT (a timedelta, not a verdict)
    assert "high-water-mark 48213" in payload             # the fixed transcript reference point
    assert "SUPERSEDED" not in payload                    # NO baked-in staleness verdict
    assert "may predate" in payload.lower()               # the brief process note


def test_write_then_read_coaching_block_roundtrips(tmp_path):
    # the harvest's authoring side (write_coaching_block) pairs with the reader; stamps the facts.
    ok = hc.write_coaching_block(tmp_path, "g1", "close-path X; on-track", watermark=512, now=time.time())
    assert ok is True
    cb = hc._read_coaching_block(tmp_path, "g1", time.time())
    assert cb and cb["text"] == "close-path X; on-track"
    assert "high-water-mark 512" in cb["facts"] and "authored" in cb["facts"]
    assert hc.write_coaching_block(tmp_path, "g1", "   ") is False   # empty text -> no write
    assert hc.write_coaching_block(tmp_path, "", "x") is False        # no goal_id -> no write


def test_payload_repo_none_omits_coaching(tmp_path):
    payload = hc.build_reorientation_payload({"goal": "g", "goal_id": "g1"}, None)
    assert "COACHING BLOCK (" not in payload and "g" in payload    # repo None -> coaching omitted
    assert "RE-ANCHOR before resuming" in payload                  # baseline intact


def test_payload_capped_drops_coaching_keeps_goal(tmp_path):
    # The /goal condition (<=4k) is ALWAYS in full; an oversized coaching block that would push the
    # payload over budget is DROPPED (graceful) — never the goal or the re-anchor.
    d = tmp_path / ".claude" / "dev-harness" / "coaching"
    d.mkdir(parents=True, exist_ok=True)
    (d / "g1.json").write_text(json.dumps({"authored_ts": time.time(), "text": "y" * 6000}))   # huge
    goal = "GOAL: ship Wave 4 " + ("z" * 3900)        # near the 4k goal max
    payload = hc.build_reorientation_payload({"goal": goal, "goal_id": "g1"}, tmp_path)
    assert len(payload) < hc.PAYLOAD_MAX_CHARS         # within the payload budget
    assert goal in payload                            # goal always in full
    assert "RE-ANCHOR before resuming" in payload     # re-anchor never dropped
    assert "COACHING BLOCK (" not in payload          # oversized coaching dropped gracefully


def test_emitted_additionalcontext_under_limit_at_max_goal(tmp_path):
    # END-TO-END: payload + the compose_directive frame must stay under the real 10k platform limit
    # even at the 4k goal max (the _WRAPPER_RESERVE covers the frame + conditional notes).
    import harness_reinject as hr  # noqa: E402
    goal = "GOAL " + ("z" * 3990)
    payload = hc.build_reorientation_payload({"goal": goal, "goal_id": "g1"}, tmp_path)
    ctx = hr.compose_directive("compact", goal, "/roadmap.md", "/nb.md", payload)
    assert len(payload) < hc.PAYLOAD_MAX_CHARS
    assert len(ctx) < hc.ADDITIONAL_CONTEXT_LIMIT


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


# --- Task 2: SessionStart composer (role-agnostic) ---
import harness_reinject as hr  # noqa: E402

_PAYLOAD = "SETTLED GOAL (the /goal condition):\nship W4\n\nDecision heuristics: ... TAKE IT ..."


def test_directive_is_go_signal_and_carries_payload():
    ctx = hr.compose_directive("compact", "ship W4", "/r.md", "/n.md", _PAYLOAD)
    assert "next increment of real work THIS turn" in ctx
    assert "GO signal" in ctx and "SETTLED" in ctx and "/r.md" in ctx and "/n.md" in ctx
    assert _PAYLOAD in ctx                                   # shared payload embedded verbatim
    assert "RE-ANCHOR" in ctx                                # frame points at the payload's re-anchor
    assert "self-check" not in ctx.lower()                   # the separate trailing self-check is gone


def test_directive_is_role_agnostic_and_prescribes_no_coordination():
    # spec §4/§5 review item 2: re-injection is ROLE-AGNOSTIC. compose_directive takes no
    # `role` arg; the SAME settled posture is injected for a solo loop or a team lead, and
    # the harness NEVER prescribes build-vs-delegate-vs-team (the agent's emergent judgment).
    ctx = hr.compose_directive("resume", "ship W4", "/r.md", "/n.md", _PAYLOAD)
    assert "next increment of real work THIS turn" in ctx     # one uniform framing
    assert _PAYLOAD in ctx and "/r.md" in ctx
    # NO role-conditioned coordination prescription in either direction:
    assert "do not start building yourself" not in ctx.lower()
    assert "lead" not in ctx.lower() and "coordinate" not in ctx.lower()


# --- Task 5: /goal-guard toggle ---
import goal_guard_toggle as ggt  # noqa: E402


def test_toggle_sets_question_guard_off_then_on(tmp_path, monkeypatch):
    monkeypatch.setattr(hc, "repo_root", lambda *a, **k: tmp_path)
    _marker(tmp_path, "abc", {"role": "solo", "goal": "g", "question_guard": True})
    assert ggt.set_question_guard(tmp_path, "abc", False) is True   # returns success
    assert hc.read_marker({"session_id": "abc"})["question_guard"] is False
    ggt.set_question_guard(tmp_path, "abc", True)
    assert hc.read_marker({"session_id": "abc"})["question_guard"] is True


def test_toggle_missing_marker_is_failopen(tmp_path):
    # No marker -> returns False (nothing to toggle), never raises.
    assert ggt.set_question_guard(tmp_path, "nope", False) is False


# --- Task 6: PreToolUse(AskUserQuestion) guard ---
import io  # noqa: E402
import json as _json  # noqa: E402
import harness_question_guard as qg  # noqa: E402


def _run_guard(ev, monkeypatch, capsys):
    monkeypatch.setattr("sys.stdin", io.StringIO(_json.dumps(ev)))
    rc = qg.main()
    out = capsys.readouterr().out
    return rc, out


def test_guard_denies_when_active(tmp_path, monkeypatch, capsys):
    monkeypatch.setattr(hc, "repo_root", lambda *a, **k: tmp_path)
    _marker(tmp_path, "abc", {"role": "solo", "goal": "ship W4", "question_guard": True})
    rc, out = _run_guard({"session_id": "abc", "cwd": str(tmp_path), "tool_name": "AskUserQuestion",
                          "tool_input": {"questions": [{"question": "which approach?"}]}}, monkeypatch, capsys)
    j = _json.loads(out)
    hso = j["hookSpecificOutput"]
    assert hso["hookEventName"] == "PreToolUse" and hso["permissionDecision"] == "deny"
    assert hso["permissionDecisionReason"] and "ship W4" in hso["additionalContext"]
    # tier-3: the redirect dispatches the in-time coach (not a static "make the call" deny)
    assert "skeft-qa:coach" in hso["permissionDecisionReason"]
    # contract C — the blocked question is logged:
    log = (tmp_path / ".claude" / "dev-harness" / "blocked_questions.jsonl").read_text()
    assert "which approach?" in log


def test_guard_allows_when_no_marker(tmp_path, monkeypatch, capsys):
    monkeypatch.setattr(hc, "repo_root", lambda *a, **k: tmp_path)
    rc, out = _run_guard({"session_id": "none", "cwd": str(tmp_path), "tool_name": "AskUserQuestion",
                          "tool_input": {"questions": []}}, monkeypatch, capsys)
    assert rc == 0 and out.strip() == ""   # allow (no deny JSON emitted)


def test_guard_allows_for_subagent(tmp_path, monkeypatch, capsys):
    monkeypatch.setattr(hc, "repo_root", lambda *a, **k: tmp_path)
    _marker(tmp_path, "abc", {"role": "solo", "goal": "g", "question_guard": True})
    rc, out = _run_guard({"session_id": "abc", "agent_id": "sub-1", "cwd": str(tmp_path),
                          "tool_name": "AskUserQuestion", "tool_input": {"questions": []}}, monkeypatch, capsys)
    assert rc == 0 and out.strip() == ""   # agent_id present -> inert -> allow


def test_guard_allows_when_question_guard_off(tmp_path, monkeypatch, capsys):
    monkeypatch.setattr(hc, "repo_root", lambda *a, **k: tmp_path)
    _marker(tmp_path, "abc", {"role": "solo", "goal": "g", "question_guard": False})
    rc, out = _run_guard({"session_id": "abc", "cwd": str(tmp_path), "tool_name": "AskUserQuestion",
                          "tool_input": {"questions": [{"question": "x?"}]}}, monkeypatch, capsys)
    assert rc == 0 and out.strip() == ""   # guard off -> allow


def test_guard_fail_open_on_bad_input(monkeypatch, capsys):
    monkeypatch.setattr("sys.stdin", io.StringIO("not json"))
    rc = qg.main()
    assert rc == 0 and capsys.readouterr().out.strip() == ""   # error -> allow


# --- Plan 3 Task 2: watermark + harvest-state + self-abort helpers ---

def test_watermark_advance_atomic_monotonic(tmp_path, monkeypatch):
    monkeypatch.setattr(hc, "repo_root", lambda *a, **k: tmp_path)
    assert hc.read_watermark("s") == 0
    hc.advance_watermark("s", 100); assert hc.read_watermark("s") == 100
    hc.advance_watermark("s", 50);  assert hc.read_watermark("s") == 100   # never goes backward


def test_harvest_state_round_trips_ts_and_cadence(tmp_path, monkeypatch):
    monkeypatch.setattr(hc, "repo_root", lambda *a, **k: tmp_path)
    assert hc.read_harvest_state() == {}            # absent -> {} (first run, drift warning silent)
    hc.write_harvest_state(1_000_000, cadence_hours=6)
    st = hc.read_harvest_state()
    assert st["last_run_ts"] == 1_000_000 and st["cadence_hours"] == 6


def test_any_managed_marker_in_workspace_is_generic_and_failclosed(tmp_path, monkeypatch):
    """Self-abort guard (MAJOR-1): detect a managed marker in ANY workspace repo — leak-safe
    (no private name in code, discovered by iterating) — and FAIL CLOSED when unresolvable."""
    ws = tmp_path / "ws"
    for repo in ("SK_EFT_Hawking", "PrivateRepo"):
        (ws / repo / ".claude" / "dev-harness" / "managed").mkdir(parents=True)
    (ws / ".mcp.json").write_text("{}")
    monkeypatch.setattr(hc, "find_workspace", lambda *a, **k: ws)
    (ws / "PrivateRepo" / ".claude" / "dev-harness" / "managed" / "sid9.json").write_text("{}")
    assert hc.any_managed_marker_in_workspace("sid9") is True   # detected even though NOT this repo
    assert hc.any_managed_marker_in_workspace("nope") is False
    monkeypatch.setattr(hc, "find_workspace", lambda *a, **k: None)
    assert hc.any_managed_marker_in_workspace("sid9") is True   # workspace unresolved -> FAIL-CLOSED


# --- Plan 3 Task 4: SessionStart drift warning (pure helper) ---

def test_drift_note_silent_when_fresh_or_absent():
    assert hr.drift_note(None, 1_000_000.0, None) == ""       # absent harvest_state -> silent
    assert hr.drift_note(0, 1_000_000.0, 0) == ""             # no cadence -> silent
    now = 1_000_000.0
    assert hr.drift_note(now - 3600, now, 6) == ""            # 1h elapsed, cadence 6h (< 2x=12h) -> not overdue


def test_drift_note_warns_past_2x_cadence():
    now = 1_000_000.0
    note = hr.drift_note(now - 18 * 3600, now, 6)             # 18h elapsed, 2x cadence = 12h -> overdue
    assert note and "harvest hasn't run" in note


# --- repo_root() launch-location robustness (regression: the skills originally used a bare
#     `git rev-parse`, which UNRESOLVED at the workspace root — spec §A.3 launch-location-robust).
#     repo_root() must resolve from BOTH a standalone in-repo clone (public-distribution launch)
#     and a workspace-root launch, and stay inert (None) for a foreign git-root (leak-safety). ---

def test_repo_root_standalone_clone_uses_git_root_basename_fallback(monkeypatch, tmp_path):
    """Public-distribution / in-repo launch: a standalone clone of just this repo, no parent
    workspace. find_workspace() returns None, so repo_root() falls back to the cwd git-root —
    accepted ONLY when its basename == REPO_DIR_NAME (spec §A.3 cache-safe/leak-safe fallback)."""
    repo = tmp_path / hc.REPO_DIR_NAME
    repo.mkdir()
    monkeypatch.setattr(hc, "find_workspace", lambda *a, **k: None)
    monkeypatch.setattr(hc, "_git_root", lambda *a, **k: repo)
    assert hc.repo_root(str(repo)) == repo


def test_repo_root_none_on_foreign_git_root(monkeypatch, tmp_path):
    """Leak-safety: if find_workspace() fails AND the cwd git-root is some OTHER repo (basename
    != REPO_DIR_NAME — e.g. the ~/.claude plugin cache, or a sibling repo), repo_root() returns
    None (inert) rather than resolving a foreign repo's marker."""
    monkeypatch.setattr(hc, "find_workspace", lambda *a, **k: None)
    monkeypatch.setattr(hc, "_git_root", lambda *a, **k: tmp_path / "SomeForeignRepo")
    assert hc.repo_root(str(tmp_path)) is None


def test_jsonl_path_reconstructs_deterministically_for_unflushed_first_turn(tmp_path, monkeypatch):
    """Regression (the first-turn empty-glob): on a brand-new session's FIRST turn the <sid>.jsonl is
    not yet flushed to disk, so jsonl_path() must RECONSTRUCT ~/.claude/projects/<cwd-slug>/<sid>.jsonl
    (slug = the cwd with every non-alphanumeric char -> '-', CC's encoding) instead of returning empty
    (which the old `ls …/<sid>.jsonl` glob did). HOME is redirected so the glob step finds nothing,
    exercising the deterministic reconstruction path."""
    monkeypatch.setenv("HOME", str(tmp_path))
    got = hc.jsonl_path("SID-123", start="/Users/x/Programming/Fluid-Based-Physics-Research")
    assert got.endswith("/SID-123.jsonl")
    assert ".claude/projects/" in got
    assert "-Users-x-Programming-Fluid-Based-Physics-Research" in got   # CC slug encoding (non-alnum -> -)


def test_jsonl_path_empty_sid_returns_empty():
    """A missing/empty session id resolves to '' (the skill then STOPs rather than arm a bad marker)."""
    assert hc.jsonl_path("", start="/anything") == ""


# --- v4.1 (RC5): marker teardown — remove_marker, the SessionEnd hook, the /goal-end CLI ---
import harness_session_end as hse  # noqa: E402
import harness_goal_end as hge      # noqa: E402


def test_remove_marker_removes_marker_and_watermark(tmp_path, monkeypatch):
    monkeypatch.setattr(hc, "repo_root", lambda *a, **k: tmp_path)
    _marker(tmp_path, "abc", {"role": "solo", "goal": "g"})
    hc.advance_watermark("abc", 500)                       # also drops a watermark
    assert hc.marker_path(tmp_path, "abc").exists()
    assert hc.remove_marker(tmp_path, "abc") is True       # existed -> removed
    assert not hc.marker_path(tmp_path, "abc").exists()
    assert not hc.watermark_path(tmp_path, "abc").exists()  # watermark torn down too


def test_remove_marker_false_when_absent_and_failopen(tmp_path):
    assert hc.remove_marker(tmp_path, "nope") is False     # nothing to remove
    assert hc.remove_marker(None, "x") is False            # repo unresolved -> False, never raises


def _run_session_end(ev, monkeypatch):
    monkeypatch.setattr("sys.stdin", io.StringIO(_json.dumps(ev)))
    hse.main()


def test_session_end_removes_marker_on_clear(tmp_path, monkeypatch):
    # reason=clear (a /clear that also clears the goal) -> the marker is torn down.
    monkeypatch.setattr(hse, "repo_root", lambda *a, **k: tmp_path)
    _marker(tmp_path, "abc", {"role": "solo", "goal": "g"})
    _run_session_end({"reason": "clear", "session_id": "abc", "cwd": str(tmp_path)}, monkeypatch)
    assert not hc.marker_path(tmp_path, "abc").exists()


def test_session_end_keeps_marker_on_resumable_reasons(tmp_path, monkeypatch):
    # reason != clear: a goal still active when a session ends is restored on --resume (goal.md),
    # so the marker must SURVIVE logout/resume/exit — only /clear means the goal is definitively gone.
    monkeypatch.setattr(hse, "repo_root", lambda *a, **k: tmp_path)
    _marker(tmp_path, "abc", {"role": "solo", "goal": "g"})
    for reason in ("logout", "resume", "prompt_input_exit", "other"):
        _run_session_end({"reason": reason, "session_id": "abc", "cwd": str(tmp_path)}, monkeypatch)
        assert hc.marker_path(tmp_path, "abc").exists(), f"marker wrongly removed on reason={reason}"


def test_session_end_inert_for_subagent(tmp_path, monkeypatch):
    monkeypatch.setattr(hse, "repo_root", lambda *a, **k: tmp_path)
    _marker(tmp_path, "abc", {"role": "solo", "goal": "g"})
    _run_session_end({"reason": "clear", "session_id": "abc", "agent_id": "sub-1",
                      "cwd": str(tmp_path)}, monkeypatch)
    assert hc.marker_path(tmp_path, "abc").exists()        # agent_id present -> inert


def test_session_end_failopen_on_bad_input(monkeypatch):
    monkeypatch.setattr("sys.stdin", io.StringIO("not json"))
    hse.main()                                             # must not raise (fail-open teardown)


def test_goal_end_removes_marker(tmp_path, monkeypatch, capsys):
    monkeypatch.setattr(hge, "repo_root", lambda *a, **k: tmp_path)
    monkeypatch.setattr("sys.argv", ["harness_goal_end.py", "abc"])
    _marker(tmp_path, "abc", {"role": "solo", "goal": "g"})
    hge.main()
    assert not hc.marker_path(tmp_path, "abc").exists()
    assert "marker removed" in capsys.readouterr().out


def test_goal_end_graceful_when_no_marker(tmp_path, monkeypatch, capsys):
    monkeypatch.setattr(hge, "repo_root", lambda *a, **k: tmp_path)
    monkeypatch.setattr("sys.argv", ["harness_goal_end.py", "nope"])
    hge.main()                                             # no marker -> graceful, no raise
    assert "already unmanaged" in capsys.readouterr().out


def test_payload_points_to_goal_dev(tmp_path):
    """RC1 reachability: the SessionStart re-inject names the in-loop dev skill (`goal-dev`),
    so a post-compact loop knows where the dev references live (works for both plugin namespaces)."""
    payload = hc.build_reorientation_payload({"goal": "g"}, tmp_path)
    assert "goal-dev" in payload
