"""D5 both-directions tests for `theorem_census_agrees` — the anti-whack-a-mole guard.

WHY THIS CHECK EXISTS. "Is this declaration compiler-generated?" was answered
independently in SIX places, each found by a different reviewer, one at a time. The
six counted generated declarations as authored, so the instruments AGREED on an inflated
figure — main published 26,103 in both `counts.tex` and `ATLAS_HEATMAP.md`. A prior test
asserted they "agree"; agreement held the whole time, which is why it never fired.

So this check has two legs and BOTH must be able to fail:
  * agreement — a published census that disagrees with the one derivation
  * ownership — a `kind == "theorem"` filter that bypasses the single owner

Both legs are mutation-verified below AND were mutation-verified against the live tree
during authoring. Two authoring failures are pinned as tests here because each made a
leg silently vacuous:
  1. the ownership regex omitted `)` from its character class, so it matched NOTHING
     across 131 files while reporting a clean pass;
  2. an autogen guard was accepted anywhere within +/-2 lines, so removing a guard left
     the nearby `_autogen = ...` assignment matching and the leg could not detect its
     own removal.
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT / "scripts"))
sys.path.insert(0, str(SK_ROOT))

import validate_helpers as _H  # noqa: E402
from validation.checks import lean_substrate as ls  # noqa: E402


class TestTheCensusAgrees:
    def test_the_live_corpus_agrees(self):
        """PRODUCTION-SEEDED. Every published census equals the one derivation."""
        r = ls.check_theorem_census_agrees()
        assert r.passed is True and r.measured is not False, (
            "a published theorem census disagrees with validate_helpers.autogen_index — "
            + "; ".join(d.message or "" for d in r.details if not d.passed))

    def test_an_absent_lean_deps_is_UNMEASURED_not_agreed(self, monkeypatch):
        """THE ONE POLICY: an unreachable population is UNMEASURED, never 'agreed'."""
        monkeypatch.setattr(_H, "load_lean_deps", lambda *a, **k: [])
        r = ls.check_theorem_census_agrees()
        assert r.measured is False and r.passed is False

    def test_a_disagreeing_published_census_FAILS(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT. The divergence this leg exists for is a PARTIAL
        fix: correcting the six sites one at a time left ATLAS_HEATMAP.md at 26,398
        against counts.tex's 22,669 for two commits (78ded271..a1644a76)."""
        # ALL THREE censuses must be present, or the population floor fires first and
        # the disagreement is never reached. Seed a tiny corpus so the canonical value
        # is cheap, then make exactly one census disagree.
        import json as _json
        monkeypatch.setattr(_H, "load_lean_deps",
                            lambda *a, **k: [{"name": "SKEFTHawking.M.thm_a", "kind": "theorem"},
                                             {"name": "SKEFTHawking.M.thm_b", "kind": "theorem"}])
        docs = tmp_path / "docs"
        docs.mkdir()
        (docs / "ATLAS_HEATMAP.md").write_text("_Source: 999999 theorem nodes, 0 open._\n")
        cj = docs / "counts.json"
        cj.write_text(_json.dumps({"lean": {"theorems_total": 2}}))
        lean = tmp_path / "lean"
        lean.mkdir()
        (lean / "atlas_view.json").write_text(_json.dumps({"nodes": [{"fqn": "a"}, {"fqn": "b"}]}))
        monkeypatch.setattr(_H, "DOCS_DIR", docs)
        monkeypatch.setattr(_H, "COUNTS_JSON_PATH", cj)
        monkeypatch.setattr(_H, "PROJECT_ROOT", tmp_path)
        r = ls.check_theorem_census_agrees()
        assert r.passed is False
        assert any("999999" in (d.message or "") for d in r.details), (
            "a published census 999,999 away from the derivation did not fail the check")


class TestOwnershipLegCannotGoVacuous:
    """Both authoring bugs that made this leg pass over everything are pinned here."""

    def test_the_pattern_matches_the_dominant_form(self):
        """AUTHORING BUG 1. The regex omitted `)` from its class, so the dominant
        `d.get('kind') == 'theorem'` form never matched and the leg scanned 131 files
        finding zero. A pattern that cannot see the common case is not a guard."""
        assert ls._THEOREM_FILTER_RE.search("if d.get('kind') == 'theorem':")
        assert ls._THEOREM_FILTER_RE.search('if d["kind"] == "theorem":')
        assert ls._THEOREM_FILTER_RE.search("if rec.get('kind') != 'theorem':")

    def test_a_narrowing_pattern_FAILS_rather_than_passing_quietly(self, monkeypatch):
        """AUTHORING BUG 1, second half. Breaking the pattern took matches 13 -> 5 and
        the leg still passed, because only ZERO was fatal. The population carries a
        down-only floor so a quietly narrowing regex reopens nothing."""
        import re as _re
        monkeypatch.setattr(ls, "_THEOREM_FILTER_RE",
                            _re.compile(r"kind[\"']\s*==\s*[\"']theorem[\"']"))
        r = ls.check_theorem_census_agrees()
        assert r.passed is False and r.measured is False
        assert any("NARROWED" in (d.message or "") for d in r.details)

    def test_a_nearby_autogen_mention_does_not_count_as_a_guard(self, monkeypatch):
        """AUTHORING BUG 2. A +/-2 line window accepted the module's own
        `_autogen = autogen_index(...)` assignment as if it guarded the filter below it,
        so stripping a real guard left the check green. Ownership must be the SAME
        expression."""
        import re as _re
        assert not _re.search(r"lines\[max\(0, i - 2\)", Path(
            ls.__file__).read_text()), (
            "the +/-2 line window is back — the ownership leg cannot detect a guard's "
            "own removal with it in place")
