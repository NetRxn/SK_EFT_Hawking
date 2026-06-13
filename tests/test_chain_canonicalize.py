"""Unit tests for the pure `canonicalize_link` core — fake index, no graph build,
runs in the default suite. Guards the Tier-2 canonicalization logic."""
from __future__ import annotations

import re
import sys
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT / "scripts"))

from chain_canonicalize import (  # noqa: E402
    canonicalize_link, RESOLVED, SUGGESTED, UNRESOLVABLE,
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
