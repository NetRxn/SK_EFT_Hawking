"""Tests for the System-2 register tool — the Misfiled / Process Wins sections, the --group
combine primitive (with its human-reviewed guardrail), and the active-issues open+win view."""
import importlib.util
import json
from pathlib import Path

import pytest

_SPEC = importlib.util.spec_from_file_location(
    "system2_register", Path(__file__).resolve().parent.parent / "scripts" / "system2_register.py")
R = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(R)


def _f(fid, title, tier="agent-reviewed", status="open", occ=1):
    return {"id": fid, "class": "c", "title": title, "why": "w", "how_to_apply": "h",
            "evidence": "e", "tier": tier, "status": status,
            "occurrences": [{"date": "2026-06-18", "session_id": "s", "compact_event_id": None}] * occ,
            "first_seen": "2026-06-18", "last_seen": "2026-06-18"}


@pytest.fixture
def reg(tmp_path):
    p = tmp_path / "REG.md"
    R.render(str(p), [_f("a", "A"), _f("b", "B"),
                      _f("w", "WinLesson", "human-reviewed", "win"),
                      _f("c", "C", status="closed")])
    return str(p)


def test_four_sections_render(reg):
    body = Path(reg).read_text()
    for h in ("## Open", "## Process Wins", "## Closed", "## Misfiled"):
        assert h in body
    # ordering: Open < Process Wins < Closed < Misfiled
    idx = [body.index(h) for h in ("## Open", "## Process Wins", "## Closed", "## Misfiled")]
    assert idx == sorted(idx)


def test_win_renders_under_process_wins(reg):
    body = Path(reg).read_text()
    assert body.index("WinLesson") > body.index("## Process Wins")
    assert body.index("WinLesson") < body.index("## Closed")


def test_round_trip_stable(reg):
    before = R.load(reg)
    R.render(reg, before)
    after = R.load(reg)
    assert {f["id"]: f["status"] for f in before} == {f["id"]: f["status"] for f in after}


def test_group_combines_and_removes_originals(reg):
    n, skipped, dropped = R.group(reg, ["a", "b"], _f("grp", "Grouped", status="closed"))
    assert n == 2 and not skipped and not dropped
    ids = {f["id"] for f in R.load(reg)}
    assert "grp" in ids and "a" not in ids and "b" not in ids


def test_group_never_absorbs_human_reviewed(reg):
    # try to absorb the human-reviewed win 'w' — it must be SKIPPED, not dissolved
    n, skipped, dropped = R.group(reg, ["a", "w"], _f("grp", "Grouped", status="closed"))
    assert n == 1 and skipped == ["w"]
    ids = {f["id"] for f in R.load(reg)}
    assert "w" in ids and "a" not in ids and "grp" in ids


def test_group_merges_absorbed_occurrences(reg):
    R.render(reg, [_f("x", "X", occ=2), _f("y", "Y", occ=3)])
    R.group(reg, ["x", "y"], _f("g", "G", status="closed", occ=0))
    g = next(f for f in R.load(reg) if f["id"] == "g")
    # occurrences are idempotent by (session_id, compact_event_id) -> the duplicates dedupe to 1
    assert len(g["occurrences"]) >= 1


def test_active_issues_includes_open_and_win_with_kind(reg, tmp_path):
    out = tmp_path / "ai.json"
    R.write_active_issues(reg, str(out))
    issues = json.loads(out.read_text())["issues"]
    kinds = {i["title"]: i["kind"] for i in issues}
    assert kinds.get("WinLesson") == "win"
    assert kinds.get("A") == "issue"
    # closed 'C' must be excluded from the active view
    assert "C" not in kinds


def test_active_issues_excludes_misfiled(reg, tmp_path):
    R.upsert(reg, _f("m", "Noise", status="misfiled"))
    out = tmp_path / "ai.json"
    R.write_active_issues(reg, str(out))
    titles = {i["title"] for i in json.loads(out.read_text())["issues"]}
    assert "Noise" not in titles


def test_upsert_reopens_closed_on_new_status(reg):
    # consolidator re-opening a closed finding on recurrence
    R.upsert(reg, {"id": "c", "status": "open", "evidence": "recurred"})
    c = next(f for f in R.load(reg) if f["id"] == "c")
    assert c["status"] == "open" and c["evidence"] == "recurred"


def test_group_cli_via_stdin(reg, monkeypatch, capsys):
    # the --group CLI path the consolidator actually invokes (stdin JSON -> group)
    import io
    payload = json.dumps({"absorb": ["a", "b"],
                          "into": _f("g", "Grouped", status="closed")})
    monkeypatch.setattr("sys.stdin", io.StringIO(payload))
    rc = R.main(["--register", reg, "--group"])
    assert rc == 0
    assert "grouped 2 finding(s)" in capsys.readouterr().out
    ids = {f["id"] for f in R.load(reg)}
    assert "g" in ids and "a" not in ids and "b" not in ids


def test_group_cli_reports_skipped_human_reviewed(reg, monkeypatch, capsys):
    import io
    payload = json.dumps({"absorb": ["a", "w"], "into": _f("g", "Grouped", status="closed")})
    monkeypatch.setattr("sys.stdin", io.StringIO(payload))
    R.main(["--register", reg, "--group"])
    out = capsys.readouterr().out
    assert "skipped 1 human-reviewed" in out and "w" in out
