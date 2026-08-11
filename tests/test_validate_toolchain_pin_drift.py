"""Tests for CHECK paper_toolchain_pin_drift — the structural mirror of
claims-reviewer Class TP (Toolchain Pin drift).

`docs/agents/claims_reviewer.md` defines Class TP as a structural check sourced
from `lean-toolchain` + `lakefile.toml`, and records that Classes TN and HD were
mirrored into validate.py "at zero-agent-cost". TP was not, so it fired only
when the claims-reviewer agent ran (Stage 13). The Mathlib v4.29.1 -> v4.32.0
bump (2026-07-29) staled every bundle draft's provenance sentence in one commit
while Stage 13 was deferred, which is what motivated shipping the mirror.

Unit tests drive the pure scan core with synthetic fixtures (true positive,
third-party exemption, capability-claim classification, live-pin quiet case);
the smoke test runs the check against the live repo and asserts it is advisory
(always passes) and that the live pin parses.
"""
from __future__ import annotations

import sys
from pathlib import Path

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT / "scripts"))

import validate as v
from validate import (
    _tp_live_pins,
    _tp_scan_lines,
    check_paper_toolchain_pin_drift,
)

LIVE_VER = "4.32.0"
LIVE_REV = "81a5d257c8e410db227a6665ed08f64fea08e997"


# ────────────────────────────────────────────────────────────────────────
# Registration
# ────────────────────────────────────────────────────────────────────────

class TestRegistration:
    def test_check_registered(self):
        names = {spec.name for spec in v._CHECKS}
        assert "paper_toolchain_pin_drift" in names

    def test_description_nonempty(self):
        for spec in v._CHECKS:
            if spec.name == "paper_toolchain_pin_drift":
                assert spec.description.strip()


# ────────────────────────────────────────────────────────────────────────
# Pure scan core
# ────────────────────────────────────────────────────────────────────────

class TestScanCore:
    def test_stale_version_is_flagged(self):
        lines = [r"Lean~4 proofs verified by \texttt{lake build} (v4.29.1)."]
        pin, cap = _tp_scan_lines(lines, LIVE_VER, LIVE_REV)
        assert [ln for ln, _ in pin] == [1]
        assert "4.29.1" in pin[0][1]
        assert cap == []

    def test_live_version_is_quiet(self):
        lines = [r"Lean~4 proofs verified by \texttt{lake build} (v4.32.0)."]
        pin, cap = _tp_scan_lines(lines, LIVE_VER, LIVE_REV)
        assert pin == [] and cap == []

    def test_stale_mathlib_rev_flagged_only_in_mathlib_context(self):
        lines = [r"verified against Mathlib commit \texttt{5e932f97}."]
        pin, _ = _tp_scan_lines(lines, LIVE_VER, LIVE_REV)
        assert [found for _, found in pin] == ["5e932f97"]

    def test_hex_without_mathlib_context_is_ignored(self):
        # A bare hex-looking token (e.g. a git SHA of something else, or a hash
        # in a data table) must not be read as a Mathlib pin.
        lines = ["the archived run digest is deadbeef12345678."]
        pin, cap = _tp_scan_lines(lines, LIVE_VER, LIVE_REV)
        assert pin == [] and cap == []

    def test_live_rev_prefix_matches(self):
        # Drafts abbreviate the pin; an 8-char prefix of the live rev is current.
        lines = [r"Mathlib commit \texttt{81a5d257}."]
        pin, cap = _tp_scan_lines(lines, LIVE_VER, LIVE_REV)
        assert pin == [] and cap == []

    def test_aristotle_context_is_exempt(self):
        # Aristotle's sandbox pin is a fact about a third-party service, not a
        # claim about our toolchain — it must stay quiet across our bumps.
        lines = [
            "The Aristotle service runs on a fixed Lean toolchain",
            r"(\texttt{leanprover/lean4:v4.28.0}) with a pinned Mathlib.",
        ]
        pin, cap = _tp_scan_lines(lines, LIVE_VER, LIVE_REV)
        assert pin == [] and cap == []

    def test_exemption_does_not_leak_past_the_context_window(self):
        # Three lines after the Aristotle sentence, a claim about OUR pin is
        # again in scope. This is the real I1 shape.
        lines = [
            "The Aristotle service runs on a fixed Lean toolchain",
            r"(\texttt{leanprover/lean4:v4.28.0}) with a corresponding pinned",
            "Mathlib commit, while the project's local toolchain is",
            r"currently \texttt{leanprover/lean4:v4.29.0} with a separately",
        ]
        pin, _ = _tp_scan_lines(lines, LIVE_VER, LIVE_REV)
        assert [ln for ln, _ in pin] == [4]

    def test_capability_claim_classified_separately(self):
        # "Mathlib vX has no Y" justifies an in-tree build; a bump can flip it.
        lines = ["Mathlib v4.29.1 has no Kunneth theorem for singular homology."]
        pin, cap = _tp_scan_lines(lines, LIVE_VER, LIVE_REV)
        assert pin == []
        assert [ln for ln, _ in cap] == [1]

    def test_capability_needs_both_mathlib_and_verb(self):
        # A bare provenance line naming Mathlib but no have/lack verb stays in
        # the pin bucket, not the capability bucket.
        lines = [r"verified by \texttt{lake build} (v4.29.1, Mathlib)."]
        pin, cap = _tp_scan_lines(lines, LIVE_VER, LIVE_REV)
        assert [ln for ln, _ in pin] == [1]
        assert cap == []


# ────────────────────────────────────────────────────────────────────────
# Live-pin reader
# ────────────────────────────────────────────────────────────────────────

class TestLivePins:
    def test_reads_both_pins(self):
        ver, rev = _tp_live_pins()
        assert ver is not None, "lean-toolchain version not parsed"
        assert rev is not None, "lakefile.toml mathlib rev not parsed"

    def test_version_matches_toolchain_file(self):
        ver, _ = _tp_live_pins()
        raw = (SK_ROOT / "lean" / "lean-toolchain").read_text(encoding="utf-8")
        assert ver in raw

    def test_rev_matches_lakefile_mathlib_stanza(self):
        _, rev = _tp_live_pins()
        raw = (SK_ROOT / "lean" / "lakefile.toml").read_text(encoding="utf-8")
        assert rev in raw


# ────────────────────────────────────────────────────────────────────────
# Smoke
# ────────────────────────────────────────────────────────────────────────

class TestSmoke:
    def test_check_is_advisory_and_passes(self):
        # Advisory by construction: a stale pin in a DRAFT is provenance
        # hygiene, and the remedy (re-verify vs. record-as-verified) is a
        # Stage-13 publication decision. This check reports; it never gates.
        result = check_paper_toolchain_pin_drift()
        assert result.passed is True

    def test_reports_the_live_pin(self):
        result = check_paper_toolchain_pin_drift()
        live = [d for d in result.details if d.name == "live-pin"]
        assert len(live) == 1
        assert "toolchain v" in live[0].message


# ── TODO-D22: a CURRENT PhysLib pin is not drift ──────────────────────────

class TestNonMathlibPinsAreNotDrift:
    """`_tp_live_pins` returns only Mathlib's rev, so a sentence naming Mathlib
    and PhysLib together had the PhysLib hash compared against Mathlib's and a
    correct pin reported stale. D11 and D12 both hit it. Both directions are
    asserted: a live non-Mathlib rev is clean, a genuinely stale hex still flags."""

    # `_tp_live_pins` strips the leading "v" — verified against the live
    # resolver rather than assumed from the lean-toolchain file text.
    LIVE_VER = "4.32.0"
    LIVE_MATHLIB = "81a5d257c8e410db227a6665ed08f64fea08e997"
    LIVE_PHYSLIB = "c48433678e8fb6306ebcd48453300c8e16058a62"

    def test_current_physlib_rev_is_not_reported(self):
        from validate import _tp_scan_lines
        lines = ["Lean toolchain v4.32.0, Mathlib revision 81a5d257 and "
                 "PhysLib revision c4843367."]
        pin, _cap = _tp_scan_lines(lines, self.LIVE_VER, self.LIVE_MATHLIB,
                                   other_revs=frozenset({self.LIVE_PHYSLIB}))
        assert pin == [], f"current PhysLib pin reported as drift: {pin}"

    def test_without_the_fix_the_same_line_would_flag(self):
        """Seeded control: drop the PhysLib rev from the live set and the very
        same line flags again. Proves the test is sensitive to the repair and
        not merely to the line being clean."""
        from validate import _tp_scan_lines
        lines = ["Lean toolchain v4.32.0, Mathlib revision 81a5d257 and "
                 "PhysLib revision c4843367."]
        pin, _cap = _tp_scan_lines(lines, self.LIVE_VER, self.LIVE_MATHLIB)
        assert any("c4843367" in found for _n, found in pin)

    def test_genuinely_stale_hex_still_flags(self):
        from validate import _tp_scan_lines
        lines = ["Mathlib revision deadbeefcafe1234."]
        pin, _cap = _tp_scan_lines(lines, self.LIVE_VER, self.LIVE_MATHLIB,
                                   other_revs=frozenset({self.LIVE_PHYSLIB}))
        assert any("deadbeef" in found for _n, found in pin)

    def test_dep_revs_are_derived_from_the_lakefile(self):
        """Derived, not hand-listed: mathlib and physlib both present."""
        import sys, pathlib
        sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "scripts"))
        from validation.checks.papers_prose import _tp_live_dep_revs
        revs = _tp_live_dep_revs()
        assert "mathlib" in revs and "physlib" in revs
        assert all(len(v) >= 8 for v in revs.values())
