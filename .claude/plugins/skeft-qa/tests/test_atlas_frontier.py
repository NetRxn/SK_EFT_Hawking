"""Atlas-frontier consumption (ADR-005 D-I): the harness reads lean/atlas_view.json and surfaces the
ranked OPEN assumptions for atlas-guided fan-out. Fail-soft is the contract — a missing/unreadable
atlas must degrade to None/'' (never wedge the loop), so the loop falls back to roadmap + notebook."""

import json
import sys
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent.parent / "scripts"
sys.path.insert(0, str(SCRIPTS))
import harness_common as hc  # noqa: E402

_ATLAS = {
    "frontier": [
        {"id": "hyp:a", "frontier_impact": 5, "status": "STATED",
         "tier": "external_boundary", "eliminability": "hard", "is_apex": False},
        {"id": "hyp:b", "frontier_impact": 0, "status": "STATED",
         "tier": "headline", "eliminability": "hard", "is_apex": True},
    ],
    "tracks": {
        "external_boundary": {"open_count": 1, "total_impact": 5, "apex_count": 0, "node_ids": ["hyp:a"]},
        "headline": {"open_count": 1, "total_impact": 0, "apex_count": 1, "node_ids": ["hyp:b"]},
    },
    "summary": {"apex_ids": ["hyp:b"]},
}


def _repo_with_atlas(tmp_path):
    lean = tmp_path / "lean"
    lean.mkdir()
    (lean / "atlas_view.json").write_text(json.dumps(_ATLAS))
    return tmp_path


def test_frontier_from_atlas_reads_ranked(tmp_path):
    d = hc.frontier_from_atlas(_repo_with_atlas(tmp_path), max_items=8)
    assert d is not None
    assert d["apex_ids"] == ["hyp:b"]
    assert [f["id"] for f in d["frontier"]] == ["hyp:a", "hyp:b"]  # preserves ranked order
    assert set(d["tracks"]) == {"external_boundary", "headline"}


def test_frontier_from_atlas_respects_max_items(tmp_path):
    d = hc.frontier_from_atlas(_repo_with_atlas(tmp_path), max_items=1)
    assert len(d["frontier"]) == 1 and d["frontier"][0]["id"] == "hyp:a"


def test_format_atlas_frontier_digest(tmp_path):
    s = hc.format_atlas_frontier(_repo_with_atlas(tmp_path))
    assert "tracks (open by area)" in s
    assert "hyp:a" in s and "[external_boundary/hard]" in s
    assert "hyp:b" in s and "*apex" in s          # apex flagged
    assert s == s.encode("ascii", "strict").decode()  # ASCII-only (rides the payload)


def test_failsoft_when_atlas_absent(tmp_path):
    assert hc.frontier_from_atlas(tmp_path) is None        # no lean/atlas_view.json
    assert hc.frontier_from_atlas(None) is None            # no repo
    assert hc.format_atlas_frontier(tmp_path) == ""        # digest degrades to ''


def test_failsoft_when_atlas_corrupt(tmp_path):
    lean = tmp_path / "lean"
    lean.mkdir()
    (lean / "atlas_view.json").write_text("{ not json")
    assert hc.frontier_from_atlas(tmp_path) is None
    assert hc.format_atlas_frontier(tmp_path) == ""


def test_payload_includes_atlas_frontier_when_present(tmp_path):
    repo = _repo_with_atlas(tmp_path)
    marker = {"goal": "prove X", "goal_id": "g1"}
    payload = hc.build_reorientation_payload(marker, repo)
    assert "ATLAS FRONTIER" in payload and "hyp:a" in payload
    # and degrades cleanly when the atlas is absent (no exception, section simply omitted)
    payload2 = hc.build_reorientation_payload(marker, tmp_path / "no_atlas")
    assert "ATLAS FRONTIER" not in payload2
