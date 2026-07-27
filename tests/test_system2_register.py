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


def test_shard_active_has_open_wins_archive_has_closed_misfiled(reg):
    body = Path(reg).read_text()
    arch = Path(R._archive_path(reg)).read_text()
    # ACTIVE surface = Index + Open + Process Wins (resolved/noise are NOT here)
    assert "## Index" in body and "## Open" in body and "## Process Wins" in body
    assert "## Closed" not in body and "## Misfiled" not in body
    # ARCHIVE = Closed + Misfiled (no Open/Wins)
    assert "## Closed" in arch and "## Misfiled" in arch
    assert "## Open" not in arch and "## Process Wins" not in arch
    # the closed finding 'c' lives in the archive, not the active surface
    assert '"id": "c"' in arch and '"id": "c"' not in body


def test_win_renders_under_process_wins(reg):
    body = Path(reg).read_text()
    # the win's full record sits in the Process Wins section (its id appears only there)
    assert body.index('"id": "w"') > body.index("## Process Wins")


def test_index_lists_only_active_findings(reg):
    head = Path(reg).read_text().split("## Open")[0]   # the index region is above the sections
    assert "| id | tier | status | tally | title |" in head
    for fid in ("a", "b", "w"):
        assert "`%s`" % fid in head
    assert "`c`" not in head    # the closed finding is indexed in the archive, not here


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


def test_active_issues_open_only_excludes_wins(reg, tmp_path):
    # wins are NOT injected (ruling 2026-06-20): the active view is OPEN-ISSUES-ONLY.
    out = tmp_path / "ai.json"
    R.write_active_issues(reg, str(out))
    issues = json.loads(out.read_text())["issues"]
    titles = {i["title"] for i in issues}
    assert "A" in titles and "B" in titles          # open issues included
    assert "WinLesson" not in titles                # process win EXCLUDED from the injected view
    assert "C" not in titles                         # closed excluded
    assert all(i["kind"] == "issue" for i in issues)


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


def test_upsert_clamps_human_reviewed_by_default(reg):
    # DETERMINISTIC block: a harvest-origin upsert must NOT mint human-reviewed (self-promotion vector)
    R.upsert(reg, _f("h", "Harvested", tier="human-reviewed"))
    h = next(f for f in R.load(reg) if f["id"] == "h")
    assert h["tier"] == "agent-reviewed"


def test_upsert_promote_allows_human_reviewed(reg):
    # /debrief (allow_human=True, via --promote) MAY set human-reviewed
    R.upsert(reg, _f("h2", "Promoted", tier="human-reviewed"), allow_human=True)
    h = next(f for f in R.load(reg) if f["id"] == "h2")
    assert h["tier"] == "human-reviewed"


def test_clamp_never_downgrades_existing_human_reviewed(reg):
    # never-downgrade safeguard preserved: a later clamped harvest upsert of the human-reviewed
    # win 'w' keeps it human-reviewed (clamp only blocks RAISING, not existing genuine HR).
    R.upsert(reg, {"id": "w", "status": "win", "evidence": "recurred"})
    w = next(f for f in R.load(reg) if f["id"] == "w")
    assert w["tier"] == "human-reviewed"


def test_upsert_stamps_datetime_first_last_on_new_finding(reg):
    # F30: a new finding without supplied first/last gets an ISO-8601 datetime (not a bare date)
    R.upsert(reg, {"id": "dt", "class": "c", "title": "DT", "tier": "agent-reviewed",
                   "occurrences": [{"session_id": "s", "compact_event_id": None}]})
    f = next(x for x in R.load(reg) if x["id"] == "dt")
    assert "T" in f["first_seen"] and f["first_seen"].endswith("Z")   # datetime
    assert "T" in f["last_seen"] and f["last_seen"].endswith("Z")


def test_upsert_bumps_last_seen_datetime_on_new_occurrence_only(reg):
    R.upsert(reg, {"id": "g2", "class": "c", "title": "G2", "tier": "agent-reviewed",
                   "first_seen": "2026-06-01", "last_seen": "2026-06-01",
                   "occurrences": [{"session_id": "s1", "compact_event_id": None}]})
    # a genuinely-new occurrence -> last_seen bumped to a datetime; first_seen preserved
    R.upsert(reg, {"id": "g2", "occurrences": [{"session_id": "s2", "compact_event_id": None}]})
    f = next(x for x in R.load(reg) if x["id"] == "g2")
    assert "T" in f["last_seen"] and f["last_seen"].endswith("Z")
    assert f["first_seen"] == "2026-06-01" and len(f["occurrences"]) == 2
    # a status/evidence-only edit (no new occurrence) must NOT bump last_seen (close != sighting)
    R.upsert(reg, {"id": "g2", "status": "closed", "evidence": "done"})
    f2 = next(x for x in R.load(reg) if x["id"] == "g2")
    assert f2["last_seen"] == f["last_seen"]   # unchanged


def test_group_clamps_into_tier_by_default(reg):
    # a harvest --group into-record cannot mint human-reviewed either
    R.group(reg, ["a", "b"], _f("g", "G", tier="human-reviewed", status="closed"))
    g = next(f for f in R.load(reg) if f["id"] == "g")
    assert g["tier"] == "agent-reviewed"


def test_upsert_cli_promote_flag(reg, monkeypatch, capsys):
    # the --promote CLI path /debrief uses to set human-reviewed
    import io
    monkeypatch.setattr("sys.stdin", io.StringIO(json.dumps(_f("p", "P", tier="human-reviewed"))))
    R.main(["--register", reg, "--upsert", "--promote"])
    p = next(f for f in R.load(reg) if f["id"] == "p")
    assert p["tier"] == "human-reviewed"
    # without --promote, the same upsert clamps
    monkeypatch.setattr("sys.stdin", io.StringIO(json.dumps(_f("p2", "P2", tier="human-reviewed"))))
    R.main(["--register", reg, "--upsert"])
    p2 = next(f for f in R.load(reg) if f["id"] == "p2")
    assert p2["tier"] == "agent-reviewed"


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


def test_offschema_record_is_healed_on_load(tmp_path):
    """A producer outside the System-2 schema (e.g. a Stage-13 paper-honesty pass) emitted a record
    with NO `class` field and `body` instead of `why`. The register must heal it on read so no
    consumer doing record['class'] KeyErrors and no `why` surface renders empty — without losing the
    explicit id or the original body text."""
    p = tmp_path / "REG.md"
    bad = {"id": "offschema", "tier": "agent-reviewed", "status": "open",
           "title": "off-schema record", "body": "the why text lived in body",
           "how_to_apply": "h", "occurrences": [{"session_id": "s", "compact_event_id": None}],
           "first_seen": "2026-06-30T00:00:00Z", "last_seen": "2026-06-30T00:00:00Z"}
    p.write_text("## Open\n\n### offschema\n\n```json\n" + json.dumps(bad, indent=2) + "\n```\n")
    f = next(x for x in R.load(str(p)) if x.get("id") == "offschema")
    assert f.get("class")                              # never None -> record['class'] is safe
    assert f.get("why") == "the why text lived in body"  # body aliased into why, text preserved
    assert f["id"] == "offschema"                      # explicit id untouched (dedup key stable)
    # idempotent: a well-formed record is unchanged
    good = _f("a", "A")
    assert R._normalize_finding(dict(good)) == good


def test_blank_title_is_healed_from_id_not_left_empty(tmp_path):
    """A producer that omits `title` used to leave it "" forever: the record rendered an empty
    `**...**` header + an empty Index cell, and reached the INJECTED active-issues view as a blank
    line. Heal it from the explicit id (the inverse of `slug`), stripping the class prefix so the
    title does not merely repeat the class — without touching the id (dedup key stays stable)."""
    p = tmp_path / "REG.md"
    bare = {"id": "harness-gap-slot-reset-refuses-cross-goal-reclaim", "class": "harness-gap",
            "tier": "agent-reviewed", "status": "open", "why": "w", "how_to_apply": "h",
            "occurrences": [{"session_id": "s", "compact_event_id": None}]}
    p.write_text("## Open\n\n### x\n\n```json\n" + json.dumps(bare, indent=2) + "\n```\n")
    f = next(x for x in R.load(str(p)) if x["id"] == "harness-gap-slot-reset-refuses-cross-goal-reclaim")
    assert f["title"] == "Slot reset refuses cross goal reclaim"   # class prefix stripped, de-slugged
    assert f["id"] == "harness-gap-slot-reset-refuses-cross-goal-reclaim"   # id untouched
    # a real title is never overwritten by the derived one
    kept = R._normalize_finding({"id": "harness-gap-x", "class": "harness-gap", "title": "Real title"})
    assert kept["title"] == "Real title"
    # fallback when there is no usable id either: first sentence of `why`
    nofid = R._normalize_finding({"class": "c", "why": "The loop re-derived a settled route. Again."})
    assert nofid["title"] == "The loop re-derived a settled route"


def test_active_issues_never_emits_a_blank_title(reg, tmp_path):
    """The injected view is the surface a blank title actually hurts — it renders as an empty line in
    the loop's re-orientation payload. Belt-and-braces: even a record written straight to the file
    with no title at all must come back with something identifying."""
    R.upsert(reg, {"id": "compact-delta-head-hash-lost-across-boundary", "class": "compact-delta",
                   "tier": "agent-reviewed", "status": "open", "why": "w",
                   "occurrences": [{"session_id": "s", "compact_event_id": "s:1"}]})
    out = tmp_path / "ai.json"
    R.write_active_issues(reg, out)
    issues = json.loads(out.read_text())["issues"]
    assert issues and all(i["title"].strip() for i in issues)
    assert any(i["title"] == "Head hash lost across boundary" for i in issues)
