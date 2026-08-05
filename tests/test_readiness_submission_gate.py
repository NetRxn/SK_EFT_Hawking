"""ADR-009 Phase 3, item 1 — the submission gate must be able to FAIL.

WHY THIS FILE EXISTS
--------------------
`readiness_submission_gate` was **inverted** until 2026-08-03. It classified every
paper into green / yellow / red, emitted a per-paper detail reading "N blocked:
...", and then returned `passed=True` unconditionally. The only marker was an
inline `# WARN not FAIL during rollout`, and the only state in which the check
could fail was **zero ReadinessGate nodes** — so it failed when it could not
measure, and passed when it measured RED.

Measured at the moment of the fix: **61 of 64 papers RED, verdict `True`.** This is
the sharpest instance of the systemic pattern in `QA_QI_INFRASTRUCTURE_MAP.md` §7 —
absence of enforcement rendered as success — and it is why 14 bundles carried
`stage13_status: green` with open blockers.

The check had no test of any kind. Per ADR-009 D5, the fix ships with one that
demonstrates BOTH directions: it FIRES on a seeded defect and stays SILENT on
correct data. Both legs run against the pure cores, so they need no graph build.

WHAT WOULD HAVE CAUGHT THE ORIGINAL DEFECT
-------------------------------------------
`test_a_blocked_p1_gate_makes_the_paper_red` plus
`test_verdict_is_false_when_any_paper_is_red`. The first alone would not have: the
original code classified red *correctly* and then ignored the classification. The
defect lived in the last line of the function, not in the logic — which is exactly
why a test asserting only the classification would have passed while the gate was
inert.
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT / "scripts"))

from validation.checks.bundles_readiness import (  # noqa: E402
    classify_readiness,
    partition_readiness,
)


def _gate(paper: str, gate: str, state: str, priority: int = 1) -> dict:
    return {"type": "ReadinessGate",
            "meta": {"paper": paper, "gate": gate, "state": state,
                     "priority": priority, "notes": ""}}


ALL_PASSED = [_gate("D1", f"G{i}", "passed", 1) for i in range(1, 9)] + \
             [_gate("D1", f"G{i}", "passed", 2) for i in range(9, 12)]


class TestClassification:
    def test_all_passed_is_green(self):
        green, yellow, red = partition_readiness(classify_readiness(ALL_PASSED))
        assert (green, yellow, red) == (["D1"], [], [])

    def test_a_blocked_p1_gate_makes_the_paper_red(self):
        gates = ALL_PASSED[:-1] + [_gate("D1", "CitationIntegrity", "blocked", 1)]
        green, yellow, red = partition_readiness(classify_readiness(gates))
        assert red == ["D1"] and green == []

    def test_a_blocked_p2_gate_also_makes_the_paper_red(self):
        """P2 blocked is a blocker too — the docstring's contract, easy to lose."""
        gates = ALL_PASSED[:-1] + [_gate("D1", "FixPropagation", "blocked", 2)]
        _g, _y, red = partition_readiness(classify_readiness(gates))
        assert red == ["D1"]

    def test_p2_advisory_is_yellow_not_red(self):
        """The other direction: advisory must NOT fail, or the gate cries wolf."""
        gates = ALL_PASSED[:-1] + [_gate("D1", "NumericalFreshness", "needs-recheck", 2)]
        green, yellow, red = partition_readiness(classify_readiness(gates))
        assert (yellow, red) == (["D1"], [])

    def test_papers_are_independent(self):
        gates = ALL_PASSED + [_gate("D2", "G1", "blocked", 1)]
        green, _y, red = partition_readiness(classify_readiness(gates))
        assert green == ["D1"] and red == ["D2"]


class TestVerdictFollowsClassification:
    """THE leg that matters. The original defect was not in the classification —
    it was that the verdict ignored it."""

    def _verdict(self, gates, monkeypatch):
        import validation.checks.bundles_readiness as m

        class _FakeBG:
            @staticmethod
            def build_graph_json():
                return {"nodes": gates, "edges": []}

        monkeypatch.setitem(sys.modules, "build_graph", _FakeBG)
        return m.check_readiness_submission_gate()

    def test_verdict_is_true_when_every_paper_is_green(self, monkeypatch):
        """SILENT ON CORRECT DATA — the half a one-directional test omits."""
        r = self._verdict(ALL_PASSED, monkeypatch)
        assert r.passed is True, [(d.name, d.message) for d in r.details]

    def test_verdict_is_false_when_any_paper_is_red(self, monkeypatch):
        """FIRES ON THE SEEDED DEFECT. This is the assertion the check failed for
        its entire existence: 61 of 64 papers red, verdict True."""
        gates = ALL_PASSED[:-1] + [_gate("D1", "CitationIntegrity", "blocked", 1)]
        r = self._verdict(gates, monkeypatch)
        assert r.passed is False, (
            "the submission gate reported PASS with a blocked P1 gate — it is "
            "inverted again (ADR-009 §Deferred item 2)")

    def test_the_failing_paper_carries_a_failing_detail(self, monkeypatch):
        """A red paper must not be reported as a passing detail with a warning
        glyph, which is how the original rendered 61 red papers as advisories."""
        gates = ALL_PASSED[:-1] + [_gate("D1", "CitationIntegrity", "blocked", 1)]
        r = self._verdict(gates, monkeypatch)
        d1 = next(d for d in r.details if d.name == "D1")
        assert d1.passed is False and not d1.warning

    def test_summary_detail_agrees_with_the_verdict(self, monkeypatch):
        """The summary said `True` unconditionally too."""
        gates = ALL_PASSED[:-1] + [_gate("D1", "CitationIntegrity", "blocked", 1)]
        r = self._verdict(gates, monkeypatch)
        assert next(d for d in r.details if d.name == "summary").passed is False


class TestCannotMeasureIsNotPassing:
    def test_zero_gate_nodes_fails(self, monkeypatch):
        import validation.checks.bundles_readiness as m

        class _FakeBG:
            @staticmethod
            def build_graph_json():
                return {"nodes": [], "edges": []}

        monkeypatch.setitem(sys.modules, "build_graph", _FakeBG)
        r = m.check_readiness_submission_gate()
        assert r.passed is False

    def test_unimportable_build_graph_fails(self, monkeypatch):
        """This branch returned passed=True ('skipping') until 2026-08-03, while
        its sibling `readiness_verdicts_agree` already carried the reasoning for
        why that is wrong. A guard that cannot load its dependency reports
        'no problem found'."""
        import builtins
        import validation.checks.bundles_readiness as m
        real = builtins.__import__

        def _boom(name, *a, **k):
            if name == "build_graph":
                raise ImportError("seeded")
            return real(name, *a, **k)

        monkeypatch.delitem(sys.modules, "build_graph", raising=False)
        monkeypatch.setattr(builtins, "__import__", _boom)
        r = m.check_readiness_submission_gate()
        assert r.passed is False
