"""Tests for the SLOT-AWARE re-anchor (System-2 finding
`harness-gap-post-compaction-repo-state-probe-slot-blind-in-multi-worktree-goal`, promoted
human-reviewed at /debrief 2026-07-04; build task worktree-slot-aware-reanchor.md).

Covers: probe slot-state resolution + isolation + liveness (repo_state_probe.slot_states /
build_report), the pointer-grade injected anchor (harness_common._live_slot_pointer /
live_head_anchor), and reset_slot ownership stamp + exclusive transfer + cross-goal guard.

Run: uv run python -m pytest SK_EFT_Hawking/.claude/plugins/skeft-qa/tests/test_slot_aware.py -v
"""
import json
import os
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[4]          # SK_EFT_Hawking
PLUGIN_SCRIPTS = Path(__file__).resolve().parent.parent / "scripts"
sys.path.insert(0, str(REPO / "scripts"))
sys.path.insert(0, str(PLUGIN_SCRIPTS))
import repo_state_probe as rsp   # noqa: E402
import harness_common as hc      # noqa: E402
import reset_slot as rs          # noqa: E402


def _git(cwd, *args):
    subprocess.run(["git", "-C", str(cwd), *args], check=True, capture_output=True, text=True)


def _mkrepo(tmp_path, branch="main"):
    """A git repo on `branch` (default `main`) with one seed commit."""
    repo = tmp_path / "SK_EFT_Hawking"
    repo.mkdir(parents=True)
    subprocess.run(["git", "init", "-q", "-b", branch, str(repo)], check=True, capture_output=True)
    _git(repo, "config", "user.email", "t@t")
    _git(repo, "config", "user.name", "t")
    (repo / "README.md").write_text("seed")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "seed")
    return repo


def _base(repo):
    return subprocess.run(["git", "-C", str(repo), "symbolic-ref", "--short", "HEAD"],
                          capture_output=True, text=True).stdout.strip() or "main"


def _add_slot(repo, n, ahead=0, dirty=False):
    """Create worktree slot wtN on branch worktree-wtN off the repo's base branch; optionally give it
    `ahead` commits and a dirty file."""
    slot = repo / ".claude" / "worktrees" / f"wt{n}"
    slot.parent.mkdir(parents=True, exist_ok=True)
    _git(repo, "worktree", "add", "-q", "-b", f"worktree-wt{n}", str(slot), _base(repo))
    for i in range(ahead):
        (slot / f"c{n}_{i}.txt").write_text(str(i))
        _git(slot, "add", "-A")
        _git(slot, "commit", "-q", "-m", f"slot {n} commit {i}")
    if dirty:
        (slot / "wip.txt").write_text("uncommitted")
    return slot


def _marker(repo, sid, **fields):
    mp = repo / ".claude" / "dev-harness" / "managed" / f"{sid}.json"
    mp.parent.mkdir(parents=True, exist_ok=True)
    mp.write_text(json.dumps(fields))
    return mp


# ── slot_states: isolation + liveness ───────────────────────────────────────────
def test_slot_states_liveness(tmp_path):
    repo = _mkrepo(tmp_path)
    _add_slot(repo, 1, ahead=2)          # live via commits
    _add_slot(repo, 2)                    # at main, clean → not live
    _add_slot(repo, 3, dirty=True)        # live via dirty tree
    st = {s["n"]: s for s in rsp.slot_states(repo, {"slots": [1, 2, 3]})}
    assert st[1]["live"] and st[1]["ahead"] == 2
    assert not st[2]["live"] and st[2]["ahead"] == 0
    assert st[3]["live"] and st[3]["dirty"] == 1


def test_slot_states_isolation_owns_only_declared(tmp_path):
    repo = _mkrepo(tmp_path)
    _add_slot(repo, 1, ahead=1)
    _add_slot(repo, 2, ahead=1)          # another goal's busy slot
    got = [s["n"] for s in rsp.slot_states(repo, {"slots": [1]})]
    assert got == [1]                    # wt2 NEVER appears — cross-goal isolation


def test_slot_states_empty_when_no_slots(tmp_path):
    repo = _mkrepo(tmp_path)
    assert rsp.slot_states(repo, {}) == []
    assert rsp.slot_states(repo, {"slots": []}) == []


def test_slot_states_missing_worktree_failopen(tmp_path):
    repo = _mkrepo(tmp_path)
    st = rsp.slot_states(repo, {"slots": [9]})
    assert len(st) == 1 and st[0]["exists"] is False


# ── build_report: surfaces the slot, warns, isolates ────────────────────────────
def test_probe_surfaces_live_slot_and_warns(tmp_path):
    repo = _mkrepo(tmp_path)
    _add_slot(repo, 1, ahead=2, dirty=True)
    out = rsp.build_report(repo, "", "G", {"goal_id": "G", "slots": [1]}, "general")
    assert "OWNED WORKTREE SLOTS" in out
    assert "LIVE WORK IS ON WT1" in out
    assert "RE-ANCHOR HERE" in out
    assert "slot commits since main" in out


def test_probe_no_slots_is_main_only(tmp_path):
    repo = _mkrepo(tmp_path)
    _add_slot(repo, 1, ahead=2)
    out = rsp.build_report(repo, "", "G", {"goal_id": "G"}, "general")
    assert "OWNED WORKTREE SLOTS" not in out
    assert "LIVE WORK IS ON" not in out


def test_probe_isolation_other_slot_absent(tmp_path):
    repo = _mkrepo(tmp_path)
    _add_slot(repo, 1, ahead=1)
    _add_slot(repo, 2, ahead=1)
    out = rsp.build_report(repo, "", "G", {"goal_id": "G", "slots": [1]}, "general")
    assert "wt1:" in out and "wt2:" not in out


# ── injected pointer (harness_common) ───────────────────────────────────────────
def test_live_slot_pointer(tmp_path):
    repo = _mkrepo(tmp_path)
    _add_slot(repo, 2, ahead=3)
    ptr = hc._live_slot_pointer(repo, {"slots": [2]})
    assert "NOT MAIN" in ptr and "wt2" in ptr and "3 ahead" in ptr


def test_live_head_anchor_prepends_slot_pointer(tmp_path):
    repo = _mkrepo(tmp_path)
    _add_slot(repo, 1, dirty=True)
    a = hc.live_head_anchor(repo, {"slots": [1]})
    assert "ACTIVE WORK IS ON A WORKTREE SLOT" in a and "[MAIN]" in a


def test_live_head_anchor_no_slots_unchanged(tmp_path):
    repo = _mkrepo(tmp_path)
    a = hc.live_head_anchor(repo, {})
    assert "ACTIVE WORK IS ON A WORKTREE SLOT" not in a and "LIVE ANCHOR" in a


def test_payload_budget_with_slot_pointer(tmp_path):
    repo = _mkrepo(tmp_path)
    _add_slot(repo, 1, ahead=1)
    payload = hc.build_reorientation_payload({"goal": "g", "goal_id": "G", "slots": [1]}, repo)
    assert len(payload) < hc.PAYLOAD_MAX_CHARS


# ── reset_slot ownership stamp + exclusive transfer + guard ─────────────────────
def test_stamp_ownership_transfers_exclusively(tmp_path, monkeypatch):
    repo = _mkrepo(tmp_path)
    _marker(repo, "sidA", goal_id="A", slots=[1])
    _marker(repo, "sidB", goal_id="B")
    monkeypatch.setenv("CLAUDE_SESSION_ID", "sidB")
    msg = rs._stamp_ownership(repo, 1)
    a = json.loads((repo / ".claude/dev-harness/managed/sidA.json").read_text())
    b = json.loads((repo / ".claude/dev-harness/managed/sidB.json").read_text())
    assert b["slots"] == [1] and a["slots"] == []      # exclusive transfer A→B
    assert "claimed" in msg


def test_stamp_ownership_idempotent(tmp_path, monkeypatch):
    repo = _mkrepo(tmp_path)
    _marker(repo, "sidA", goal_id="A", slots=[1])
    monkeypatch.setenv("CLAUDE_SESSION_ID", "sidA")
    rs._stamp_ownership(repo, 1)
    a = json.loads((repo / ".claude/dev-harness/managed/sidA.json").read_text())
    assert a["slots"] == [1]                            # no duplicate


def test_stamp_ownership_no_marker_skips(tmp_path, monkeypatch):
    repo = _mkrepo(tmp_path)
    monkeypatch.setenv("CLAUDE_SESSION_ID", "nope")
    assert rs._stamp_ownership(repo, 1) == ""           # unmanaged session → no-op


def test_other_owners_detects_cross_goal(tmp_path):
    repo = _mkrepo(tmp_path)
    _marker(repo, "sidA", goal_id="A", slots=[2])
    _marker(repo, "sidB", goal_id="B", slots=[])
    owners = rs._other_owners(repo, 2, "sidB", "B")
    assert len(owners) == 1 and owners[0][1]["goal_id"] == "A"
    # same goal is never a conflict
    assert rs._other_owners(repo, 2, "sidB2", "A") == []


# ── adversarial-review regression tests (2026-07-04) ────────────────────────────
def test_slot_states_nonmain_default_branch(tmp_path):
    """#1: a repo whose base branch is `master` must still detect slot liveness (base resolved,
    not hardcoded `main`)."""
    repo = _mkrepo(tmp_path, branch="master")
    _add_slot(repo, 1, ahead=2)
    st = {s["n"]: s for s in rsp.slot_states(repo, {"slots": [1]})}
    assert st[1]["live"] and st[1]["ahead"] == 2          # would be ahead=None,live=False if hardcoded


def test_live_head_anchor_nonmain_default_branch(tmp_path):
    repo = _mkrepo(tmp_path, branch="master")
    _add_slot(repo, 2, ahead=1)
    assert "wt2" in hc._live_slot_pointer(repo, {"slots": [2]})


def test_slots_bare_string_does_not_misparse(tmp_path):
    """#3: `slots` as a string must fail-open to [], not iterate characters into slots [1,3]."""
    repo = _mkrepo(tmp_path)
    _add_slot(repo, 1, ahead=1)
    assert rsp.slot_states(repo, {"slots": "wt13"}) == []
    assert hc._live_slot_pointer(repo, {"slots": "wt13"}) == ""


def test_reset_refuses_unmerged_commits(tmp_path, monkeypatch):
    """#2: reset must refuse (rc 1) when the slot has commits not on base — via main()."""
    repo = _mkrepo(tmp_path)
    _add_slot(repo, 1, ahead=1)                            # 1 commit not on base
    monkeypatch.setattr(rs, "repo_root", lambda *a, **k: repo)
    monkeypatch.setattr(rs, "_reclone_lake_if_stale", lambda *a, **k: 0)
    monkeypatch.setattr(sys, "argv", ["reset_slot.py", "1"])
    monkeypatch.delenv("CLAUDE_SESSION_ID", raising=False)
    assert rs.main() == 1                                  # refused, no reset
    # the slot commit survives
    ahead = subprocess.run(["git", "-C", str(repo / ".claude/worktrees/wt1"),
                            "rev-list", "--count", f"{_base(repo)}..HEAD"],
                           capture_output=True, text=True).stdout.strip()
    assert ahead == "1"


def test_reset_stamps_ownership_end_to_end(tmp_path, monkeypatch):
    """#5: a clean reset via main() stamps the active goal's marker."""
    repo = _mkrepo(tmp_path)
    _add_slot(repo, 2)                                     # clean, at base
    _marker(repo, "sidX", goal_id="X")
    monkeypatch.setattr(rs, "repo_root", lambda *a, **k: repo)
    monkeypatch.setattr(rs, "_reclone_lake_if_stale", lambda *a, **k: 0)
    monkeypatch.setattr(sys, "argv", ["reset_slot.py", "2"])
    monkeypatch.setenv("CLAUDE_SESSION_ID", "sidX")
    assert rs.main() == 0
    mk = json.loads((repo / ".claude/dev-harness/managed/sidX.json").read_text())
    assert mk["slots"] == [2]


def test_reset_ownership_guard_refuses_then_force(tmp_path, monkeypatch):
    """#5/#6: reclaiming a slot another goal owns is refused without --force, allowed with it."""
    repo = _mkrepo(tmp_path)
    _add_slot(repo, 1)
    _marker(repo, "sidA", goal_id="A", slots=[1])          # goal A owns wt1
    _marker(repo, "sidB", goal_id="B")
    monkeypatch.setattr(rs, "repo_root", lambda *a, **k: repo)
    monkeypatch.setattr(rs, "_reclone_lake_if_stale", lambda *a, **k: 0)
    monkeypatch.setenv("CLAUDE_SESSION_ID", "sidB")
    monkeypatch.setattr(sys, "argv", ["reset_slot.py", "1"])
    assert rs.main() == 1                                   # refused (A owns it)
    monkeypatch.setattr(sys, "argv", ["reset_slot.py", "1", "--force"])
    assert rs.main() == 0                                   # --force reclaims + transfers
    a = json.loads((repo / ".claude/dev-harness/managed/sidA.json").read_text())
    b = json.loads((repo / ".claude/dev-harness/managed/sidB.json").read_text())
    assert a["slots"] == [] and b["slots"] == [1]


def test_stamp_preserves_other_marker_fields(tmp_path, monkeypatch):
    """Transfer must only rewrite `slots`, preserving every other field on the donor marker."""
    repo = _mkrepo(tmp_path)
    _marker(repo, "sidA", goal_id="A", slots=[1], role="lead", notebook_path="/nb", custom="keep")
    _marker(repo, "sidB", goal_id="B")
    monkeypatch.setenv("CLAUDE_SESSION_ID", "sidB")
    rs._stamp_ownership(repo, 1)
    a = json.loads((repo / ".claude/dev-harness/managed/sidA.json").read_text())
    assert a["role"] == "lead" and a["notebook_path"] == "/nb" and a["custom"] == "keep"
    assert a["slots"] == []


def test_other_owners_both_goal_id_absent_is_conflict(tmp_path):
    """#4: two markers with no goal_id (different sessions) must still be treated as a conflict."""
    repo = _mkrepo(tmp_path)
    _marker(repo, "sidA", slots=[2])                       # no goal_id
    owners = rs._other_owners(repo, 2, "sidB", None)       # current also has no goal_id
    assert len(owners) == 1


def test_probe_broken_worktree_failopen_exit0(tmp_path):
    """A dangling slot dir must not crash the probe; main() returns 0 (degraded, never blocks)."""
    repo = _mkrepo(tmp_path)
    slot = repo / ".claude" / "worktrees" / "wt1"
    slot.mkdir(parents=True)
    (slot / ".git").write_text("gitdir: /nonexistent")     # dangling worktree pointer
    _marker(repo, "sidZ", goal_id="Z", mode="general", slots=[1])
    out = rsp.build_report(repo, "", "Z", {"goal_id": "Z", "slots": [1]}, "general")
    assert "wt1" in out                                    # section emitted, no raise
    rc = rsp.main(["--repo", str(repo), "--session-id", "sidZ"])  # reads sidZ.json (slots=[1]) end-to-end
    assert rc == 0
