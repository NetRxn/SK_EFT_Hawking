"""Unit tests for the pure `canonicalize_link` core — fake index, no graph build,
runs in the default suite. Guards the Tier-2 canonicalization logic."""
from __future__ import annotations

import re
import sys
from pathlib import Path

import pytest

PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT / "scripts"))

from chain_canonicalize import (  # noqa: E402
    canonicalize_link, RESOLVED, SUGGESTED, INVALID, UNRESOLVABLE,
)


class FakeIndex:
    node_ids = {
        "formula:higgs_mass_from_condensate",
        "lean:SKEFTHawking.TetradGapEquation.gap_nontrivial_exists",
        "module:SKEFTHawking.TetradGapEquation",
        "param:EW.M_H_GEV",
        "source:Hawking:1974",
        "hyp:c_minus_equals_8Nf",
    }

    def resolve_lean_short(self, name):
        return ("lean:SKEFTHawking.TetradGapEquation.gap_nontrivial_exists"
                if name.endswith("gap_nontrivial_exists") else None)

    def lean_short_candidates(self, name):
        return ["lean:A.ambig", "lean:B.ambig"] if name.rsplit(".", 1)[-1] == "ambig" else []

    def module_id_for_ref(self, target):
        base = re.sub(r"\s*\([^)]*\)\s*$", "", target)
        base = re.sub(r"_module$", "", base).strip()
        cand = base if base.startswith("SKEFTHawking.") else f"SKEFTHawking.{base}"
        mid = f"module:{cand}"
        return mid if mid in self.node_ids else None

    def constant_param_alias(self, target):
        return None

    def is_constant_ref(self, target):
        return target.split(".")[0] == "EWBG_PARAMS"

    def closest_formula(self, target):
        return "higgs_mass_from_condensate" if target == "higgs_mass_from_condensat" else None

    def normalize_bibkey(self, target):
        m = re.match(r"^([A-Za-z]+)(\d{4})$", target)
        return f"{m.group(1)}:{m.group(2)}" if m else None


IDX = FakeIndex()


def test_formula_resolved():
    r = canonicalize_link("formula", "higgs_mass_from_condensate", IDX)
    assert r.status == RESOLVED and r.target_id == "formula:higgs_mass_from_condensate"


def test_formula_renamed_suggested():
    r = canonicalize_link("formula", "higgs_mass_from_condensat", IDX)
    assert r.status == SUGGESTED and r.suggestions == ["formula:higgs_mass_from_condensate"]


def test_theorem_qualified_resolved():
    r = canonicalize_link("theorem", "TetradGapEquation.gap_nontrivial_exists", IDX)
    assert r.status == RESOLVED


def test_module_ref_resolves_to_module_node():
    r = canonicalize_link("theorem", "TetradGapEquation (module)", IDX)
    assert r.status == RESOLVED and r.target_id == "module:SKEFTHawking.TetradGapEquation"


def test_qualified_module_ref_resolves():
    r = canonicalize_link("theorem", "SKEFTHawking.TetradGapEquation", IDX)
    assert r.status == RESOLVED and r.category == "module-resolved"


def test_ambiguous_short_name_suggested():
    r = canonicalize_link("theorem", "ambig", IDX)
    assert r.status == SUGGESTED and len(r.suggestions) == 2


def test_param_constant_unresolvable():
    r = canonicalize_link("parameter", "EWBG_PARAMS.SM_M_H_GEV", IDX)
    assert r.status == UNRESOLVABLE and r.category == "param-constant"


def test_param_resolved():
    assert canonicalize_link("parameter", "EW.M_H_GEV", IDX).status == RESOLVED


def test_citation_format_suggested():
    r = canonicalize_link("citation", "Hawking1974", IDX)
    assert r.status == SUGGESTED and r.suggestions == ["source:Hawking:1974"]


def test_citation_resolved():
    assert canonicalize_link("citation", "Hawking:1974", IDX).status == RESOLVED


def test_invalid_kind():
    r = canonicalize_link("nonsense", "x", IDX)
    assert r.status == UNRESOLVABLE and r.category == "invalid-kind"


def test_empty_target():
    assert canonicalize_link("formula", "", IDX).status == UNRESOLVABLE


def test_invalid_expression_or_ratio():
    assert canonicalize_link("formula", "109/119", IDX).status == INVALID
    assert canonicalize_link("formula", "delta_diss = (1 + xi^2)^-1", IDX).status == INVALID
    assert canonicalize_link("parameter", "n_theorems = 5229", IDX).status == INVALID


def test_invalid_path_or_dict_access():
    assert canonicalize_link("formula", "docs/counts.json:lean.theorems_total", IDX).status == INVALID
    assert canonicalize_link("parameter", "EXPERIMENTS['Steinhauer']", IDX).status == INVALID


def test_value_annotation_stripped_is_not_invalid():
    # "X (2.4 K)" base is a valid param path -> not auto-rejected as invalid.
    assert canonicalize_link("parameter", "Dean_bilayer_nozzle.T_H_K (2.4 K)", IDX).status != INVALID


@pytest.fixture
def production_module_index(monkeypatch):
    """Keep the real adapter/lookups; supply only their finite index data."""
    import build_graph as bg
    from chain_canonicalize import GraphIndex

    index = GraphIndex.__new__(GraphIndex)
    index._bg = bg
    index.node_ids = {
        "module:SKEFTHawking.Plain",
        "module:SKEFTHawking.Nested.Plain",
        "module:SKEFTHawking.Unique",
        "module:SKEFTHawking.Ambig",
        "module:SKEFTHawking.Named_module",
        "lean:Library.Unique",
        "lean:Left.Ambig", "lean:Right.Ambig",
        "lean:Left.Clash", "lean:Right.Clash",
    }
    monkeypatch.setattr(bg, "_LEAN_SHORT_INDEX", {
        "Unique": ["lean:Library.Unique"],
        "Ambig": ["lean:Left.Ambig", "lean:Right.Ambig"],
        "Clash": ["lean:Left.Clash", "lean:Right.Clash"],
    })
    monkeypatch.setattr(bg, "_LEAN_AMBIGUITY_SEEN", set())
    return index


@pytest.mark.parametrize("kind", ["theorem", "axiom"])
@pytest.mark.parametrize("target,want,status", [
    ("module:SKEFTHawking.Plain", "module:SKEFTHawking.Plain", RESOLVED),
    ("module:SKEFTHawking.Unique", "module:SKEFTHawking.Unique", RESOLVED),
    ("module:SKEFTHawking.Ambig", "module:SKEFTHawking.Ambig", RESOLVED),
    ("module:SKEFTHawking.Named_module", "module:SKEFTHawking.Named_module", RESOLVED),
    ("module:SKEFTHawking.Nested.Plain", "module:SKEFTHawking.Nested.Plain", RESOLVED),
    ("  module:SKEFTHawking.Plain  ", "module:SKEFTHawking.Plain", RESOLVED),
    ("module:SKEFTHawking.Missing", None, UNRESOLVABLE),
    ("module:Foreign.Unique", None, UNRESOLVABLE),
    ("module:Foreign.Ambig", None, UNRESOLVABLE),
    ("module:module:SKEFTHawking.Unique", None, UNRESOLVABLE),
    ("module:module:SKEFTHawking.Ambig", None, UNRESOLVABLE),
    ("module:SKEFTHawking.Plain_module", None, UNRESOLVABLE),
    ("module:SKEFTHawking.Plain (module)", None, UNRESOLVABLE),
    ("module:sk_eft.dark_sector.sfdm_merger_forecast", None, UNRESOLVABLE),
    ("module:docs/counts.tex", None, INVALID),
    ("Plain", "module:SKEFTHawking.Plain", RESOLVED),
    ("Nested.Plain", "module:SKEFTHawking.Nested.Plain", RESOLVED),
    ("SKEFTHawking.Plain", "module:SKEFTHawking.Plain", RESOLVED),
    ("Plain (module)", "module:SKEFTHawking.Plain", RESOLVED),
    ("Plain_module", "module:SKEFTHawking.Plain", RESOLVED),
    ("Nested.Plain_module", "module:SKEFTHawking.Nested.Plain", RESOLVED),
    ("Unique", "lean:Library.Unique", RESOLVED),
    ("Library.Unique", "lean:Library.Unique", RESOLVED),
    ("Ambig", "module:SKEFTHawking.Ambig", RESOLVED),
    ("Clash", None, SUGGESTED),
])
def test_production_module_identity_and_refusal_reach_both_consumers(
        production_module_index, monkeypatch, tmp_path, kind, target, want, status):
    """Catch typed IDs rebound to declarations, suggestions or another module."""
    import json

    index = production_module_index
    bg = index._bg
    typed = target.strip().startswith("module:")
    if typed:
        # Exact typed identity must survive the real shared helper as well.
        assert bg._module_id_for_ref(target, index.node_ids) == want

    result = canonicalize_link(kind, target, index)
    assert result.status == status
    assert result.target_id == want
    if typed:
        assert result.suggestions == []
    elif status == SUGGESTED:
        assert result.suggestions == ["lean:Left.Clash", "lean:Right.Clash"]

    paper = tmp_path / "D1"
    paper.mkdir()
    sentence = "sentence:D1:module_identity:00000000"
    (paper / "claims_review.json").write_text(json.dumps({"sentences": [{
        "id": sentence, "chain_proposed": {"links": [
            {"kind": kind, "target": target},
        ]},
    }]}))
    monkeypatch.setattr(bg, "_iter_paper_dirs", lambda: iter([("D1", paper)]))
    edges = bg.extract_backed_by_edges(index.node_ids | {sentence})
    assert len(edges) == 1
    edge = edges[0]
    assert edge["source"] == sentence and edge["type"] == "BACKED_BY"
    assert edge["meta"]["link_kind"] == kind
    if want is not None:
        assert edge["target"] == want
        assert edge["meta"]["link_state"] == "resolved"
    else:
        assert edge["meta"]["link_state"] == "missing_target"
        assert edge["target"] not in index.node_ids
        if typed:
            assert edge["target"] == target.strip()


@pytest.mark.parametrize("paths,expected", [
    (["papers/D1/claims_review.json"], 1),
    (["lean/SKEFTHawking/WKBConnection.lean"], 1),
    (["lean/lean_deps.json"], 1),
    (["papers/D1/claims_review.json", "lean/lean_deps.json"], 1),
    (["docs/README.md"], 0),
])
def test_chain_check_scope_routes_real_inputs_once(paths, expected):
    """Claims and module-membership edits must reach the existing fresh check."""
    from verify_scope import _plan

    steps, _ = _plan(paths)
    check_argvs = [argv for _, argv in steps
                  if any(a == "--check" and b == "chain_backing_targets_resolve"
                         for a, b in zip(argv, argv[1:]))]
    assert len(check_argvs) == expected
    for argv in check_argvs:
        assert argv[:4] == ["uv", "run", "python", "scripts/validate.py"]
        assert "--no-memo" in argv
