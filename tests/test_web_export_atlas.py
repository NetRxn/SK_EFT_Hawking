"""Exporter additions for the site atlas: families + frontier_links (schema 0.2.0)."""
import importlib.util
from pathlib import Path

spec = importlib.util.spec_from_file_location(
    "export_web_atlas", Path(__file__).parent.parent / "scripts" / "export_web_atlas.py")
ewa = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ewa)

SYNTH = {
    "nodes": [
        {"fqn": "SKEFTHawking.Alpha.t1", "module": "SKEFTHawking.Alpha.Core",
         "atlas_kind": "TRUE", "atlas_status": "PROVED"},
        {"fqn": "SKEFTHawking.Alpha.t2", "module": "SKEFTHawking.Alpha.Core",
         "atlas_kind": "TRUE", "atlas_status": "PROVED"},
        {"fqn": "SKEFTHawking.Beta.t3", "module": "SKEFTHawking.Beta.Main",
         "atlas_kind": "TRUE", "atlas_status": "PROVED"},
    ],
    "unknowns": [
        {"id": "hyp:h1", "module": "Alpha prose (notes); Beta + junk",
         "dependent_theorems": ["SKEFTHawking.Alpha.t1", "SKEFTHawking.Alpha.t2",
                                 "SKEFTHawking.Beta.t3"]},
        {"id": "hyp:h2", "module": "whatever", "dependent_theorems": []},
        # dependents NOT in the nodes list: 3-part FQN -> namespace fallback;
        # top-level (2-part) FQN carries no family evidence
        {"id": "hyp:h3", "module": "prose",
         "dependent_theorems": ["SKEFTHawking.Gamma.tX",
                                 "SKEFTHawking.top_level_decl"]},
    ],
    "frontier": [
        {"id": "hyp:h1", "frontier_impact": 5, "status": "PLANNED",
         "tier": "headline", "eliminability": "hard", "is_apex": True},
        {"id": "hyp:h2", "frontier_impact": 1, "status": "STATED",
         "tier": "local", "eliminability": "easy", "is_apex": False},
        {"id": "hyp:h3", "frontier_impact": 2, "status": "STATED",
         "tier": "local", "eliminability": "easy", "is_apex": False},
    ],
    "obstructions": [
        {"id": "nogo-1", "fork_id": "f", "nogo_kind": "refutation",
         "false_statement": "X", "backing_theorems": ["SKEFTHawking.Beta.t3"],
         "kernel_pure": True, "registered": True},
        {"id": "nogo-2", "fork_id": "g", "nogo_kind": "refutation",
         "false_statement": "Y", "backing_theorems": [],
         "kernel_pure": True, "registered": False},
    ],
    "summary": {},
}


def test_frontier_family_from_dependents_majority():
    out = ewa.build_site_atlas(SYNTH)
    f = {e["id"]: e for e in out["frontier"]}
    assert f["hyp:h1"]["family"] == "Alpha"      # 2 Alpha vs 1 Beta
    assert f["hyp:h2"]["family"] is None          # no dependents -> null
    assert f["hyp:h3"]["family"] == "Gamma"       # namespace fallback for misses


def test_frontier_links_aggregated_by_family():
    out = ewa.build_site_atlas(SYNTH)
    links = sorted(out["frontier_links"], key=lambda l: (l["id"], l["family"]))
    assert links == [
        {"id": "hyp:h1", "family": "Alpha", "weight": 2},
        {"id": "hyp:h1", "family": "Beta", "weight": 1},
        {"id": "hyp:h3", "family": "Gamma", "weight": 1},
    ]


def test_obstruction_family_from_first_backing_theorem():
    out = ewa.build_site_atlas(SYNTH)
    o = {e["id"]: e for e in out["obstructions"]}
    assert o["nogo-1"]["family"] == "Beta"
    assert o["nogo-2"]["family"] is None


def test_schema_version_bumped():
    assert ewa.SCHEMA_VERSION == "0.2.0"
