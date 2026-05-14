"""
test_bundle_migration.py — Phase 6i Wave 7.1 schema + migration tests
"""
from __future__ import annotations

import json
import sys
from pathlib import Path
import pytest

PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT / "scripts"))

from bundle_migration import parse_mapping, _DEST_BUNDLE_RE
from sentence_state import (
    _VALID_BUNDLE_TARGETS, _VALID_LIFT_ACTIONS, validate_claims_review,
)


# ────────────────────────────────────────────────────────────────────────
# Schema validation tests
# ────────────────────────────────────────────────────────────────────────

def _minimal_claims_review_with(bundle_destination=None, lift_action=None,
                                bundle_section_hint=None):
    """Build a minimal v2 claims_review that satisfies the existing
    required fields, optionally with bundle-aware additions."""
    sentence = {
        "id": "sentence:paper_x:intro:abcd1234",
        "section": "intro",
        "tex_line_start": 1,
        "tex_line_end": 1,
        "quote": "test sentence",
        "type": "qualitative",
        "finding_classes": [],
        "agent_verdict": "PASS",
        "agent_run_id": "test-run-1",
        "tombstone": False,
    }
    if bundle_destination is not None:
        sentence["bundle_destination"] = bundle_destination
    if lift_action is not None:
        sentence["lift_action"] = lift_action
    if bundle_section_hint is not None:
        sentence["bundle_section_hint"] = bundle_section_hint
    return {
        "paper": "paper_x",
        "review_date": "2026-04-29",
        "reviewer_version": "claims-reviewer-v2.0",
        "reviewer_run_id": "test-run-1",
        "sentences": [sentence],
        "summary": {},
    }


class TestSchemaAdditions:
    def test_valid_single_bundle_destination(self):
        cr = _minimal_claims_review_with(bundle_destination="D3")
        errs = validate_claims_review(cr)
        assert not errs, f"unexpected errors: {errs}"

    def test_valid_list_bundle_destination(self):
        cr = _minimal_claims_review_with(bundle_destination=["L1", "D3"])
        errs = validate_claims_review(cr)
        assert not errs, f"unexpected errors: {errs}"

    def test_invalid_bundle_destination(self):
        cr = _minimal_claims_review_with(bundle_destination="X9")
        errs = validate_claims_review(cr)
        assert any("bundle_destination invalid" in e for e in errs)

    def test_invalid_bundle_destination_in_list(self):
        cr = _minimal_claims_review_with(bundle_destination=["D3", "X9"])
        errs = validate_claims_review(cr)
        assert any("bundle_destination[1]" in e for e in errs)

    def test_duplicate_bundle_destinations_in_list(self):
        cr = _minimal_claims_review_with(bundle_destination=["D3", "D3"])
        errs = validate_claims_review(cr)
        assert any("bundle_destination has duplicates" in e for e in errs)

    def test_valid_lift_action_section(self):
        cr = _minimal_claims_review_with(lift_action="Lift-section")
        errs = validate_claims_review(cr)
        assert not errs

    def test_invalid_lift_action(self):
        cr = _minimal_claims_review_with(lift_action="Lift-nope")
        errs = validate_claims_review(cr)
        assert any("lift_action invalid" in e for e in errs)

    def test_bundle_section_hint_must_be_string(self):
        cr = _minimal_claims_review_with(bundle_section_hint=42)
        errs = validate_claims_review(cr)
        assert any("bundle_section_hint must be str" in e for e in errs)

    def test_all_six_lift_actions_valid(self):
        # Every lift_action in the schema must validate.
        for la in _VALID_LIFT_ACTIONS:
            cr = _minimal_claims_review_with(lift_action=la)
            errs = validate_claims_review(cr)
            assert not errs, f"{la}: {errs}"

    def test_all_thirteen_bundles_valid(self):
        # Every bundle in the schema must validate.
        for b in _VALID_BUNDLE_TARGETS:
            cr = _minimal_claims_review_with(bundle_destination=b)
            errs = validate_claims_review(cr)
            assert not errs, f"{b}: {errs}"

    def test_bundle_target_set_size(self):
        # Lock the count: 1 flagship + 5 deep + 3 PRL + 3 infra + 2 expt = 14.
        # I3 added Phase 6n session 4 (commit a72ba68) under Pipeline Invariant #14
        # user-auth — bundle architecture grew from 13 to 14 with I3 (verified-stochastic-
        # calculus-for-Mathlib4 community contribution).
        assert len(_VALID_BUNDLE_TARGETS) == 14

    def test_lift_action_set_size(self):
        # Lock the count: 6 actions per PAPER_DRAFT_MAPPING.md conventions.
        assert len(_VALID_LIFT_ACTIONS) == 6


# ────────────────────────────────────────────────────────────────────────
# Mapping parser tests
# ────────────────────────────────────────────────────────────────────────

class TestMappingParser:
    def test_dest_regex_extracts_d3_section(self):
        m = list(_DEST_BUNDLE_RE.finditer("**D3 §5** + **F §6**"))
        assert len(m) == 2
        assert m[0].group(1) == "D3"
        assert m[1].group(1) == "F"

    def test_dest_regex_extracts_l1_no_hint(self):
        m = list(_DEST_BUNDLE_RE.finditer("**L1** (PRL splash)"))
        assert m[0].group(1) == "L1"

    def test_real_mapping_parses_all_papers(self):
        from bundle_migration import MAPPING_DOC
        text = MAPPING_DOC.read_text()
        assignments = parse_mapping(text)
        # Must parse at least 32 (existing-draft count per PAPER_STRATEGY.md)
        assert len(assignments) >= 32

    def test_real_mapping_every_paper_lifts_to_flagship(self):
        from bundle_migration import MAPPING_DOC
        text = MAPPING_DOC.read_text()
        assignments = parse_mapping(text)
        # Every existing DRAFT also lifts into the flagship F. Sourceless
        # `_lean_only` handles (Phase 6n / 6o research substrate that lifts
        # INTO bundle drafts but doesn't have its own draft) are exempt
        # from this invariant — whether they additionally lift into F is a
        # per-entry substantive question, not a universal requirement.
        # See PAPER_DRAFT_MAPPING.md row notes like "(no standalone draft
        # per Phase 6n research-only scope)" for the architectural rationale.
        for paper, a in assignments.items():
            if paper.endswith('_lean_only'):
                continue
            assert "F" in a["bundle_destinations"], (
                f"{paper} missing F (flagship) assignment"
            )

    def test_real_mapping_lift_letter_papers_have_two_or_more_bundles(self):
        from bundle_migration import MAPPING_DOC
        text = MAPPING_DOC.read_text()
        assignments = parse_mapping(text)
        # Lift-letter sentences land in both the splash and the deep.
        # Combined with the universal F, that's ≥3 bundles.
        for paper, a in assignments.items():
            if a["lift_action"] == "Lift-letter":
                assert len(a["bundle_destinations"]) >= 3, (
                    f"{paper} Lift-letter but only "
                    f"{a['bundle_destinations']}"
                )

    def test_real_mapping_three_l_letters_present(self):
        from bundle_migration import MAPPING_DOC
        text = MAPPING_DOC.read_text()
        assignments = parse_mapping(text)
        bundles_seen = set()
        for a in assignments.values():
            bundles_seen.update(a["bundle_destinations"])
        assert {"L1", "L2", "L3"}.issubset(bundles_seen)

    def test_real_mapping_paper27_directory_correct(self):
        # Wave 7.1 fix: mapping referenced paper27_bh_four_laws but the
        # actual directory is paper27_bh_thermodynamics_four_laws.
        from bundle_migration import MAPPING_DOC
        text = MAPPING_DOC.read_text()
        assignments = parse_mapping(text)
        assert "paper27_bh_thermodynamics_four_laws" in assignments
        assert "paper27_bh_four_laws" not in assignments
