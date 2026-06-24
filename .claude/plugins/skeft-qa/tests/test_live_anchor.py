"""Tests for the Live-Anchor redesign (spec docs/dev-loops/LIVE_ANCHOR_REDESIGN_SPEC.md):
the repo_state_probe (Move 1), the harness_common payload changes (Move 1/C), the PreCompact
staging hook (Move 3/E), and the tracked-path / mode-gating invariants.

Run: uv run python -m pytest SK_EFT_Hawking/.claude/plugins/skeft-qa/tests/test_live_anchor.py -v
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
import repo_state_probe as rsp  # noqa: E402
import harness_common as hc     # noqa: E402
import harness_precompact as hp  # noqa: E402


def _git(repo, *args):
    subprocess.run(["git", "-C", str(repo), *args], check=True,
                   capture_output=True, text=True)


def _mkrepo(tmp_path, files=None):
    repo = tmp_path / "SK_EFT_Hawking"
    (repo / "scripts").mkdir(parents=True)
    (repo / "lean").mkdir()
    _git(tmp_path, "init", str(repo)) if False else None
    subprocess.run(["git", "init", "-q", str(repo)], check=True, capture_output=True)
    _git(repo, "config", "user.email", "t@t")
    _git(repo, "config", "user.name", "t")
    for rel, content in (files or {"README.md": "x"}).items():
        p = repo / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(content)
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "seed")
    return repo


# ── cascade (§A.2a) ────────────────────────────────────────────────────────────
def test_anchor_cascade_sha_exact(tmp_path):
    repo = _mkrepo(tmp_path)
    head = subprocess.run(["git", "-C", str(repo), "rev-parse", "HEAD"],
                          capture_output=True, text=True).stdout.strip()
    mode, val, label = rsp.resolve_anchor(repo, {"arm_sha": head})
    assert mode == "sha" and val == head and "exact" in label


def test_anchor_cascade_unresolvable_sha_falls_through_to_timestamp(tmp_path):
    repo = _mkrepo(tmp_path)
    mode, val, label = rsp.resolve_anchor(repo, {"arm_sha": "deadbeef", "armed_ts": "1700000000"})
    assert mode == "since" and "unresolvable" in label


def test_anchor_cascade_goalid_timestamp(tmp_path):
    repo = _mkrepo(tmp_path)
    mode, val, label = rsp.resolve_anchor(repo, {"goal_id": "20260101T120000"})
    assert mode == "since" and "2026-01-01 12:00:00" in val


def test_anchor_cascade_lastn_when_no_anchor(tmp_path):
    repo = _mkrepo(tmp_path)
    mode, val, label = rsp.resolve_anchor(repo, {})
    assert mode == "lastn" and "last" in label and "commits" in label


# ── mode gating (principle 8) ───────────────────────────────────────────────────
def test_probe_general_mode_suppresses_lean_sections(tmp_path):
    repo = _mkrepo(tmp_path)
    out = rsp.build_report(repo, "", "GG", {"goal_id": "GG"}, mode_override="general")
    assert "mode=general" in out
    assert "engine inventory" not in out          # atlas inventory is lean-only
    assert "lean_diagnostic_messages" not in out  # live-sorry mandate is lean-only
    assert "repo-wide commits" in out             # general delta is repo-wide, not lean/-scoped


def test_probe_lean_mode_enables_lean_sections(tmp_path):
    repo = _mkrepo(tmp_path, {"lean/atlas_view.json": json.dumps(
        {"nodes": [{"fqn": "X.foo", "module": "X.Foo", "atlas_status": "PROVED", "kernel_pure": True}],
         "frontier": [{"id": "hyp:k", "frontier_impact": 9}]})})
    out = rsp.build_report(repo, "", "GG", {"goal_id": "GG"}, mode_override="lean")
    assert "mode=lean" in out
    assert "engine inventory" in out
    assert "lean_diagnostic_messages" in out
    assert "commits to lean/" in out


def test_probe_unknown_mode_defaults_general(tmp_path):
    repo = _mkrepo(tmp_path)
    out = rsp.build_report(repo, "", "GG", {"goal_id": "GG", "mode": "weird"}, None)
    assert "mode=general" in out and "engine inventory" not in out


# ── launch-independence: __file__ anchoring resolves the real repo ──────────────
def test_default_repo_anchors_on_file_not_cwd(tmp_path, monkeypatch):
    monkeypatch.chdir(tmp_path)                 # cwd is a NON-repo dir (the workspace-parent case)
    assert rsp.default_repo() == REPO           # still resolves SK_EFT_Hawking via __file__, not cwd


# ── M1: the timestamp rung must BOUND the delta, not dump all history ────────────
def test_armed_ts_epoch_uses_at_form_for_bounded_since(tmp_path):
    repo = _mkrepo(tmp_path)
    mode, val, label = rsp.resolve_anchor(repo, {"armed_ts": 1718000000})
    assert mode == "since" and val == "@1718000000"   # @<epoch>, NOT a bare int (git would return ALL)


def test_git_delta_since_at_epoch_parses_not_ignored(tmp_path):
    # The @-form must be HONORED as a date (the bug was a bare int that git silently ignores). An
    # epoch-1 (1970) anchor is before all commits, so --since=@1 returns them all — proving the form
    # parses. (A bare `--since=1` is what M1 fixed; we assert the @-form is what resolve_anchor emits.)
    repo = _mkrepo(tmp_path)
    for i in range(3):
        (repo / f"f{i}.txt").write_text("x")
        _git(repo, "add", "-A"); _git(repo, "commit", "-q", "-m", f"c{i}")
    out, _ = rsp.git_delta(repo, "since", "@1", lean=False)
    assert len(out.strip().splitlines()) >= 4   # seed + 3 commits, all after 1970 → @-epoch honored
    assert rsp.resolve_anchor(repo, {"armed_ts": 1700000000})[1].startswith("@")  # emits @-form


# ── M2: full-module matching — no same-basename namespace collision ──────────────
def test_module_inventory_no_tail_collision():
    atlas = {"nodes": [
        {"fqn": "SKEFTHawking.Basic.a", "module": "SKEFTHawking.Basic",
         "atlas_status": "PROVED", "kernel_pure": True},
        {"fqn": "SKEFTHawking.SymTFT.Basic.b", "module": "SKEFTHawking.SymTFT.Basic",
         "atlas_status": "PROVED", "kernel_pure": True},
    ]}
    inv, _ = rsp.module_inventory(atlas, ["lean/SKEFTHawking/SymTFT/Basic.lean"])
    rows = inv["lean/SKEFTHawking/SymTFT/Basic.lean"]
    assert [r[0] for r in rows] == ["SKEFTHawking.SymTFT.Basic.b"]   # ONLY the matching namespace


# ── multi-marker: resolve THIS session's marker (no cross-read) ─────────────────
def test_resolve_marker_picks_session_specific(tmp_path):
    repo = _mkrepo(tmp_path)
    mgr = repo / ".claude" / "dev-harness" / "managed"
    mgr.mkdir(parents=True)
    (mgr / "sidA.json").write_text(json.dumps({"goal_id": "A", "arm_sha": "aaa"}))
    (mgr / "sidB.json").write_text(json.dumps({"goal_id": "B", "arm_sha": "bbb"}))
    m, src = rsp.resolve_marker(repo, "sidB", "", None)
    assert m["goal_id"] == "B" and "sidB" in src


# ── live_head_anchor (spec 1.10 skip-resilience) ────────────────────────────────
def test_live_head_anchor_returns_line_in_git_repo(tmp_path):
    repo = _mkrepo(tmp_path)
    a = hc.live_head_anchor(repo)
    assert a.startswith("LIVE ANCHOR") and "HEAD=" in a


def test_live_head_anchor_failsoft_non_git(tmp_path):
    assert hc.live_head_anchor(tmp_path) == ""   # not a git repo -> ''
    assert hc.live_head_anchor(None) == ""


# ── RE_ANCHOR / FIRST_ACTION (BLOCKER 1.5, FIRST_ACTION rewire) ─────────────────
def test_re_anchor_drops_drift_phrase_and_points_at_probe():
    assert "always current — the loop" not in hc.RE_ANCHOR
    assert "LAB-NOTEBOOK FRONTIER below" not in hc.RE_ANCHOR
    assert "LIVE REPO-STATE ANCHOR" in hc.RE_ANCHOR


def test_first_action_has_live_anchor_and_settled_forks():
    assert "repo_state_probe.py" in hc.FIRST_ACTION
    assert "SETTLED_FORKS.md" in hc.FIRST_ACTION


# ── PreCompact staging hook (Move 3/E) ──────────────────────────────────────────
def _run_precompact(repo, ev):
    """Drive harness_precompact.main() with a synthetic stdin event."""
    import io
    old = sys.stdin
    sys.stdin = io.StringIO(json.dumps(ev))
    try:
        return hp.main()
    finally:
        sys.stdin = old


def _marker(repo, sid, m):
    d = repo / ".claude" / "dev-harness" / "managed"
    d.mkdir(parents=True, exist_ok=True)
    (d / f"{sid}.json").write_text(json.dumps(m))


def test_precompact_writes_snapshot_and_lean_flag(tmp_path, monkeypatch):
    repo = _mkrepo(tmp_path)
    transcript = repo / "t.jsonl"
    transcript.write_text(json.dumps(
        {"type": "assistant", "message": {"content": [{"type": "text",
         "text": "NEXT BRICK: the substantive last message worth preserving across the boundary."}]}}) + "\n")
    _marker(repo, "sid1", {"goal_id": "G1", "mode": "lean", "jsonl_path": str(transcript)})
    monkeypatch.setattr(hp, "repo_root", lambda *a, **k: repo)
    rc = _run_precompact(repo, {"session_id": "sid1", "cwd": str(repo),
                                "transcript_path": str(transcript)})
    assert rc == 0
    snap = json.loads((repo / ".claude/dev-harness/snapshot_G1.json").read_text())
    assert "substantive last message" in snap["last_message"] and snap["head_sha"]
    assert (repo / ".claude/dev-harness/regen_requested.flag").exists()  # lean -> flag staged


def test_precompact_general_mode_no_flag(tmp_path, monkeypatch):
    repo = _mkrepo(tmp_path)
    transcript = repo / "t.jsonl"
    transcript.write_text(json.dumps(
        {"type": "assistant", "message": {"content": [{"type": "text", "text": "general work message here ok"}]}}) + "\n")
    _marker(repo, "sid2", {"goal_id": "G2", "mode": "general", "jsonl_path": str(transcript)})
    monkeypatch.setattr(hp, "repo_root", lambda *a, **k: repo)
    _run_precompact(repo, {"session_id": "sid2", "cwd": str(repo), "transcript_path": str(transcript)})
    assert (repo / ".claude/dev-harness/snapshot_G2.json").exists()          # snapshot: any goal
    assert not (repo / ".claude/dev-harness/regen_requested.flag").exists()  # NO flag in general


def test_precompact_inert_without_marker(tmp_path, monkeypatch):
    repo = _mkrepo(tmp_path)
    monkeypatch.setattr(hp, "repo_root", lambda *a, **k: repo)
    rc = _run_precompact(repo, {"session_id": "no-such", "cwd": str(repo)})
    assert rc == 0
    assert not (repo / ".claude/dev-harness").exists() or not list(
        (repo / ".claude/dev-harness").glob("snapshot_*.json"))


# ── tracked-path invariant (BLOCKER 1.2 / QI) ───────────────────────────────────
def test_boundary_atlas_target_is_gitignored_not_tracked():
    # The probe prefers the gitignored boundary atlas; it must NEVER read/write the tracked path
    # as the regen target. Assert the boundary path is under the gitignored dev-harness dir.
    src = (REPO / "scripts" / "repo_state_probe.py").read_text()
    assert ".claude/dev-harness/atlas_view.boundary.json" in src or "atlas_view.boundary.json" in src
    # and the gitignore actually ignores dev-harness
    gi = (REPO / ".gitignore").read_text()
    assert ".claude/dev-harness" in gi


def test_atlas_write_boundary_targets_gitignored_only(tmp_path, monkeypatch):
    # B1: `atlas_view.py --write-boundary` writes the GITIGNORED boundary atlas and NEVER the tracked
    # lean/atlas_view.json. Monkeypatch the paths + extraction so the test needs no lean_deps/numpy.
    import atlas_view as av  # repo scripts on sys.path
    tracked = tmp_path / "lean" / "atlas_view.json"
    boundary = tmp_path / ".claude" / "dev-harness" / "atlas_view.boundary.json"
    stub = {"nodes": [], "unknowns": [], "edges": [], "frontier": [], "tracks": {},
            "summary": {"theorem_nodes": 0, "unknown_nodes": 0, "implies_edges": 0,
                        "apex_nodes": 0, "apex_ids": [], "by_kind_status": {}, "by_tier": {}}}
    monkeypatch.setattr(av, "ATLAS_VIEW_PATH", tracked)
    monkeypatch.setattr(av, "BOUNDARY_ATLAS_PATH", boundary)
    monkeypatch.setattr(av, "load_lean_deps_file", lambda: [])
    monkeypatch.setattr(av, "build_atlas", lambda *a, **k: stub)
    rc = av.main(["--write-boundary"])
    assert rc == 0
    assert boundary.exists()              # boundary written
    assert not tracked.exists()           # tracked file NOT touched


def test_payload_budget_with_anchor_and_atlas_at_max_goal(tmp_path):
    # m2: the existing budget tests use a non-git tmp_path, so the always-on HEAD anchor + atlas
    # frontier are absent. Exercise the WORST case: a real git repo (anchor present) + a fixture
    # atlas frontier + the 4k goal max + a huge coaching block.
    repo = _mkrepo(tmp_path, {"lean/atlas_view.json": json.dumps({"frontier": [
        {"id": f"hyp:{i}", "frontier_impact": 9 - i, "tier": "t", "eliminability": "hard", "is_apex": False}
        for i in range(8)], "summary": {"apex_ids": []}, "tracks": {}})})
    d = repo / ".claude" / "dev-harness" / "coaching"
    d.mkdir(parents=True, exist_ok=True)
    (d / "g1.json").write_text(json.dumps({"authored_ts": 1.0, "text": "y" * 6000}))
    goal = "GOAL " + ("z" * 3990)
    import harness_reinject as hr  # noqa: E402
    payload = hc.build_reorientation_payload({"goal": goal, "goal_id": "g1"}, repo)
    ctx = hr.compose_directive("compact", goal, "/r.md", "/nb.md", payload)
    assert hc.live_head_anchor(repo)               # anchor non-empty (real git repo)
    assert len(payload) < hc.PAYLOAD_MAX_CHARS     # payload within budget with anchor+atlas present
    assert len(ctx) < hc.ADDITIONAL_CONTEXT_LIMIT  # emitted ctx under the 10k platform limit
    assert goal in payload                         # goal always full


def test_precompact_never_touches_tracked_atlas(tmp_path, monkeypatch):
    # BEHAVIORAL: the hook stages a flag; it must NEVER write/modify the tracked lean/atlas_view.json
    # (or anything under lean/). Run it and assert the tracked file is byte-identical afterward.
    repo = _mkrepo(tmp_path, {"lean/atlas_view.json": '{"nodes":[],"frontier":[]}'})
    tracked = repo / "lean" / "atlas_view.json"
    before = tracked.read_bytes()
    lean_files_before = sorted(p.name for p in (repo / "lean").iterdir())
    transcript = repo / "t.jsonl"
    transcript.write_text(json.dumps(
        {"type": "assistant", "message": {"content": [{"type": "text", "text": "lean work message here ok"}]}}) + "\n")
    _marker(repo, "sidT", {"goal_id": "GT", "mode": "lean", "jsonl_path": str(transcript)})
    monkeypatch.setattr(hp, "repo_root", lambda *a, **k: repo)
    _run_precompact(repo, {"session_id": "sidT", "cwd": str(repo), "transcript_path": str(transcript)})
    assert tracked.read_bytes() == before                                   # tracked atlas untouched
    assert sorted(p.name for p in (repo / "lean").iterdir()) == lean_files_before  # nothing new under lean/
    assert (repo / ".claude/dev-harness/regen_requested.flag").exists()      # the flag IS staged (dev-harness)
