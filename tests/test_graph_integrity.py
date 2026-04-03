"""
Tests for scripts/graph_integrity.py — Knowledge Graph integrity checker.

Tests structural query results and conflict detection.
"""

import sys
from pathlib import Path

import pytest

# Ensure project root is on sys.path
PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT))
sys.path.insert(0, str(PROJECT_ROOT / "scripts"))

from scripts.graph_integrity import run_integrity_checks


class TestIntegrityReportStructure:
    """Tests that the integrity report has all expected keys and valid types."""

    def test_integrity_report_structure(self):
        """Report has all expected keys: orphan_nodes, broken_chains,
        ungrounded_claims, missing_provenance, summary, conflicts."""
        report = run_integrity_checks()

        # Top-level keys
        expected_keys = {
            'orphan_nodes', 'broken_chains', 'ungrounded_claims',
            'missing_provenance', 'summary', 'conflicts',
        }
        assert expected_keys == set(report.keys()), (
            f"Report keys mismatch. Expected: {expected_keys}, Got: {set(report.keys())}"
        )

        # All issue lists are actually lists
        for key in ('orphan_nodes', 'broken_chains', 'ungrounded_claims',
                     'missing_provenance', 'conflicts'):
            assert isinstance(report[key], list), f"{key} should be a list"

        # Summary has expected sub-keys
        summary = report['summary']
        expected_summary_keys = {
            'total_nodes', 'total_edges', 'total_issues',
            'orphans', 'conflicts', 'ungrounded',
            'broken_chains', 'missing_provenance',
        }
        assert expected_summary_keys == set(summary.keys()), (
            f"Summary keys mismatch. Expected: {expected_summary_keys}, "
            f"Got: {set(summary.keys())}"
        )

        # All summary values are non-negative integers
        for key, val in summary.items():
            assert isinstance(val, int), f"summary[{key}] should be int, got {type(val)}"
            assert val >= 0, f"summary[{key}] should be non-negative"

        # total_issues is the sum of all issue counts
        assert summary['total_issues'] == (
            summary['orphans'] + summary['conflicts'] + summary['ungrounded']
            + summary['broken_chains'] + summary['missing_provenance']
        )


class TestDetectsKnownConflict:
    """Tests that the integrity checker detects conflicts via verification status."""

    def test_detects_known_conflict(self):
        """Conflict detection is consistent: summary count matches conflict list,
        and any conflict entries have the expected fields.

        Note: omega_perp previously had a conflict but it has been resolved.
        This test validates the detection mechanism works structurally.
        """
        report = run_integrity_checks()

        # Summary count must match the conflict list length
        assert report['summary']['conflicts'] == len(report['conflicts'])

        # Verify conflict entries have expected fields (if any exist)
        for conflict in report['conflicts']:
            assert 'id' in conflict
            assert 'type' in conflict
            assert 'name' in conflict
            assert 'detail' in conflict

        # Cross-check: independently count conflict nodes from the graph
        from scripts.build_graph import extract_all_nodes
        nodes = extract_all_nodes()
        expected_conflicts = sum(
            1 for n in nodes if n.get('verification') == 'conflict'
        )
        assert report['summary']['conflicts'] == expected_conflicts, (
            f"Integrity checker found {report['summary']['conflicts']} conflicts "
            f"but graph has {expected_conflicts} conflict nodes"
        )
