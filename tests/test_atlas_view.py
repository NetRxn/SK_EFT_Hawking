"""Tests for the derived proof-atlas view (ADR-005).

Phase 1a covered kind/status classification; these lock in the Phase 2 (D-H) additions:
the open frontier carries its TRACK (`tier`) + `eliminability` + `is_apex`, and rolls up into a
per-track view so "many open phases/waves working separate areas" is navigable. `build_atlas` is a
pure function of its inputs, so we drive it with tiny synthetic registries (no 19 MB lean_deps.json
load, no live HYPOTHESIS_REGISTRY coupling)."""

import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent / "scripts"))
import atlas_view  # noqa: E402

# A kernel-pure proved theorem + one OBSTRUCTION (no-go-named) decl.
_LEAN_DEPS = [
    {"name": "M.thmA", "kind": "theorem", "module": "M", "type": "P",
     "axiom_deps_project": [], "axiom_deps_core": ["propext"], "name_deps_project": []},
    {"name": "M.foo_no_go", "kind": "theorem", "module": "M", "type": "¬ P",
     "axiom_deps_project": [], "axiom_deps_core": ["propext"], "name_deps_project": []},
]
# Two open hypotheses on different tracks; one is a HEADLINE apex, one a high-impact boundary wall.
_HYP = {
    "headline_goal": {"tier": "headline", "eliminability": "hard", "module": "M",
                      "statement": "the apex", "status": "active", "dependent_theorems": []},
    "boundary_wall": {"tier": "external_boundary", "eliminability": "very_hard", "module": "M",
                      "statement": "a wall", "status": "active",
                      "dependent_theorems": ["M.thmA", "M.thmA"]},  # impact = 2
}


def _atlas():
    # axiom_metadata={} (not None) keeps build_atlas from importing the live registries.
    return atlas_view.build_atlas(_LEAN_DEPS, hyp_registry=_HYP, axiom_metadata={})


def test_apex_count_matches_headline_tier():
    a = _atlas()
    assert a["summary"]["apex_nodes"] == 1
    assert a["summary"]["apex_ids"] == ["hyp:headline_goal"]
    apex = [u for u in a["unknowns"] if u["is_apex"]]
    assert [u["id"] for u in apex] == ["hyp:headline_goal"]
    # only headline tier is apex
    assert all(u["is_apex"] == (u["tier"] == "headline") for u in a["unknowns"])


def test_tracks_rollup_groups_by_tier():
    tracks = _atlas()["tracks"]
    assert set(tracks) == {"headline", "external_boundary"}
    assert tracks["headline"]["open_count"] == 1
    assert tracks["headline"]["apex_count"] == 1
    assert tracks["external_boundary"]["apex_count"] == 0
    # total_impact = sum of frontier_impact (reverse dep count) in the track
    assert tracks["external_boundary"]["total_impact"] == 2


def test_frontier_carries_track_axis_and_is_ranked():
    fr = _atlas()["frontier"]
    # every frontier entry carries the workstream axis (the D-H enrichment)
    for f in fr:
        assert {"tier", "eliminability", "is_apex"} <= set(f)
    # ranked by impact desc — the boundary wall (impact 2) outranks the apex (impact 0)
    assert fr[0]["id"] == "hyp:boundary_wall"
    assert fr[0]["frontier_impact"] >= fr[-1]["frontier_impact"]


def test_unclassified_tier_degrades_softly():
    hyp = {"loose": {"eliminability": "open", "module": "M", "status": "active",
                     "statement": "no tier", "dependent_theorems": []}}
    tracks = atlas_view.build_atlas(_LEAN_DEPS, hyp_registry=hyp, axiom_metadata={})["tracks"]
    assert "unclassified" in tracks  # missing tier -> soft bucket, never a hard failure


def test_build_atlas_is_deterministic():
    a, b = _atlas(), _atlas()
    assert a == b
