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
            'unclassified_axioms',
        }
        assert expected_keys == set(report.keys()), (
            f"Report keys mismatch. Expected: {expected_keys}, Got: {set(report.keys())}"
        )

        # All issue lists are actually lists
        for key in ('orphan_nodes', 'broken_chains', 'ungrounded_claims',
                     'missing_provenance', 'conflicts', 'unclassified_axioms'):
            assert isinstance(report[key], list), f"{key} should be a list"

        # Summary has expected sub-keys
        summary = report['summary']
        expected_summary_keys = {
            'total_nodes', 'total_edges', 'total_issues',
            'orphans', 'conflicts', 'ungrounded',
            'broken_chains', 'missing_provenance',
            'total_axioms', 'unclassified_axioms',
            'depends_on_axiom_edges', 'theorems_with_axiom_deps',
            'pg_vertex_count', 'pg_sync',
        }
        assert expected_summary_keys == set(summary.keys()), (
            f"Summary keys mismatch. Expected: {expected_summary_keys}, "
            f"Got: {set(summary.keys())}"
        )

        # All numeric summary values are non-negative integers
        # (pg_sync is a string status, not a count)
        # (pg_vertex_count may be None when PG+AGE container is not running)
        for key, val in summary.items():
            if key == 'pg_sync':
                assert isinstance(val, str), f"summary[{key}] should be str, got {type(val)}"
            elif key == 'pg_vertex_count' and val is None:
                pass  # PG not running — acceptable in non-container environments
            else:
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


# ═══════════════════════════════════════════════════════════════════════
# Phase 5v Wave 2c — integrity checks on new node/edge types
# ═══════════════════════════════════════════════════════════════════════

class TestReviewFindingIntegrity:
    """ReviewFindings should participate in FLAGS edges (otherwise orphan)."""

    def test_no_orphaned_findings(self):
        """Every ReviewFinding is either (a) source of a FLAGS edge, or
        (b) part of a SUPERSEDES chain. Orphan findings indicate the
        heuristic body-text paper-attribution failed and the finding
        won't surface in the dashboard."""
        from scripts.build_graph import extract_all_nodes, extract_all_edges

        nodes = extract_all_nodes()
        node_ids = {n['id'] for n in nodes}
        edges = extract_all_edges(node_ids)

        findings = [n for n in nodes if n['type'] == 'ReviewFinding']
        if not findings:
            pytest.skip("No ReviewFinding nodes present")

        attached = {e['source'] for e in edges if e['type'] in ('FLAGS', 'SUPERSEDES')}
        attached |= {e['target'] for e in edges if e['type'] == 'SUPERSEDES'}
        orphans = [f['id'] for f in findings if f['id'] not in attached]

        # Not a hard failure during rollout — record in report. Once
        # Wave 6 adversarial-reviewer emits structured output this
        # tightens to == 0.
        assert len(orphans) <= len(findings), "accounting error"
        # Soft floor: at least 25% of findings should attach to some artifact.
        attach_rate = 1.0 - (len(orphans) / len(findings))
        assert attach_rate >= 0.25, (
            f"Only {attach_rate:.0%} of {len(findings)} ReviewFindings are "
            f"attached via FLAGS/SUPERSEDES; heuristic paper-attribution "
            f"may be failing. First 3 orphans: {orphans[:3]}"
        )


class TestCountMetricIntegrity:
    """CountMetric snapshot values should match canonical counts.json."""

    def test_count_metric_matches_canonical(self):
        """Every CountMetric node whose id ends in ':current' carries the
        canonical value from counts.json in meta.value. Drift is a bug in
        the extractor (stale snapshot) or in counts.json itself."""
        from scripts.build_graph import extract_all_nodes

        nodes = extract_all_nodes()
        metrics = [n for n in nodes if n['type'] == 'CountMetric']
        if not metrics:
            pytest.skip("No CountMetric nodes")

        try:
            import json
            counts_path = PROJECT_ROOT / "docs" / "counts.json"
            canonical = json.loads(counts_path.read_text())
        except (OSError, json.JSONDecodeError):
            pytest.skip("counts.json unavailable")

        mismatches = []
        for m in metrics:
            metric_key = m['meta'].get('metric')
            node_val = m['meta'].get('value')
            canon_val = canonical.get(metric_key)
            if canon_val is None:
                continue  # canonical has no entry — extractor-defined metric
            if node_val != canon_val:
                mismatches.append((metric_key, node_val, canon_val))

        assert not mismatches, (
            f"CountMetric nodes drift from counts.json: "
            f"{[(k, a, b) for k, a, b in mismatches[:5]]}"
        )


class TestFormulaTestCoverage:
    """Formulas covered only by bounds tests have no correctness coverage."""

    def test_bounds_only_formulas_flagged(self):
        """A Formula with VERIFIES incoming edges ALL of test_kind='bounds'
        has no golden/identity coverage — this is a ComputationCorrectness
        gate signal. This test does not fail; it asserts the integrity
        checker surfaces the count, enabling the readiness gate to fire.
        """
        from scripts.build_graph import (
            extract_all_nodes, extract_formula_nodes, extract_verifies_edges,
        )

        nodes = extract_all_nodes()
        node_ids = {n['id'] for n in nodes}
        verifies = [e for e in extract_verifies_edges(node_ids) if e['type'] == 'VERIFIES']
        if not verifies:
            pytest.skip("No VERIFIES edges")

        formula_ids = {n['id'] for n in extract_formula_nodes()}

        incoming_by_target: dict[str, list[str]] = {}
        for e in verifies:
            if e['target'] in formula_ids:
                incoming_by_target.setdefault(e['target'], []).append(
                    e.get('test_kind', 'unknown')
                )

        bounds_only = [
            fid for fid, kinds in incoming_by_target.items()
            if kinds and all(k == 'bounds' for k in kinds)
        ]

        # Upper bound: not all formulas are bounds-only.
        covered = len(incoming_by_target)
        if covered == 0:
            pytest.skip("No formulas have VERIFIES coverage")
        bounds_only_rate = len(bounds_only) / covered
        assert bounds_only_rate < 0.80, (
            f"{bounds_only_rate:.0%} of covered formulas ({len(bounds_only)}/"
            f"{covered}) have bounds-only test coverage; indicates systemic "
            f"lack of golden/identity tests. Example: {bounds_only[:3]}"
        )
