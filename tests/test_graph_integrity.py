"""
Tests for scripts/graph_integrity.py — Knowledge Graph integrity checker.

Tests structural query results and conflict detection.

Marked `slow`: `run_integrity_checks` builds the full knowledge
graph via `build_graph.py`, which calls `load_lean_deps()` and
re-runs `lake env lean --run SKEFTHawking/ExtractDeps.lean` if the
cached hash is stale (5-10 min). Default pytest skips this module;
run with `-m slow` to include.
"""

import sys
from pathlib import Path

import pytest

pytestmark = pytest.mark.slow

# Ensure project root is on sys.path
PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT))
sys.path.insert(0, str(PROJECT_ROOT / "scripts"))

from scripts.graph_integrity import run_integrity_checks


class TestIntegrityReportStructure:
    """Tests that the integrity report has all expected keys and valid types."""

    def test_integrity_report_structure(self, graph_integrity_report):
        """Report has all expected keys: legacy (orphan_nodes, broken_chains,
        ungrounded_claims, missing_provenance, summary, conflicts,
        unclassified_axioms) plus Phase 5v Wave 10b sentence/audit/cluster
        + last_modified checks."""
        report = graph_integrity_report

        # Top-level keys (Wave 10b adds 6 new check buckets)
        expected_keys = {
            'orphan_nodes', 'broken_chains', 'ungrounded_claims',
            'missing_provenance', 'summary', 'conflicts',
            'unclassified_axioms',
            # Wave 10b additions
            'sentence_chain_incomplete', 'sentence_id_collisions',
            'audit_event_missing_logged_by', 'audit_event_malformed_actor',
            'claim_cluster_inconsistency', 'last_modified_missing',
            # R-06: orphan paper-claim regression guard (PaperClaim subset of orphans)
            'orphan_claims',
        }
        assert expected_keys == set(report.keys()), (
            f"Report keys mismatch. Expected: {expected_keys}, Got: {set(report.keys())}"
        )

        # All issue lists are actually lists
        for key in ('orphan_nodes', 'orphan_claims', 'broken_chains',
                     'ungrounded_claims',
                     'missing_provenance', 'conflicts', 'unclassified_axioms',
                     'sentence_chain_incomplete', 'sentence_id_collisions',
                     'audit_event_missing_logged_by',
                     'audit_event_malformed_actor',
                     'claim_cluster_inconsistency', 'last_modified_missing'):
            assert isinstance(report[key], list), f"{key} should be a list"

        # Summary has expected sub-keys (Wave 10b adds size summaries
        # for each new check bucket)
        summary = report['summary']
        expected_summary_keys = {
            'total_nodes', 'total_edges', 'total_issues',
            'orphans', 'conflicts', 'ungrounded',
            'broken_chains', 'missing_provenance',
            'total_axioms', 'unclassified_axioms',
            'depends_on_axiom_edges', 'theorems_with_axiom_deps',
            'pg_vertex_count', 'pg_sync',
            # Wave 10b summary additions
            'sentence_chain_incomplete', 'sentence_id_collisions',
            'audit_event_missing_logged_by', 'audit_event_malformed_actor',
            'claim_cluster_inconsistency', 'last_modified_missing',
            # R-06: orphan paper-claim regression guard
            'orphan_claims',
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

        # total_issues is the sum of all issue counts (Phase 5v Wave 10b
        # added 5 categories: sentence_chain_incomplete, sentence_id_collisions,
        # audit_event_missing_logged_by, audit_event_malformed_actor,
        # claim_cluster_inconsistency).
        assert summary['total_issues'] == (
            summary['orphans'] + summary['conflicts'] + summary['ungrounded']
            + summary['broken_chains'] + summary['missing_provenance']
            + summary.get('sentence_chain_incomplete', 0)
            + summary.get('sentence_id_collisions', 0)
            + summary.get('audit_event_missing_logged_by', 0)
            + summary.get('audit_event_malformed_actor', 0)
            + summary.get('claim_cluster_inconsistency', 0)
        )


class TestOrphanClaimGuard:
    """R-06 regression guard: zero orphan paper-claim nodes."""

    def test_no_orphan_paper_claims(self, graph_integrity_report):
        """Every PaperClaim node is CLAIMS-connected to its paper. The pre-R-06
        graph had 128 orphan claims; the CLAIMS-edge extractor now connects every
        discovered claim, so this must stay 0. A non-zero count is a hard fail in
        validate.py --check graph_integrity."""
        report = graph_integrity_report
        assert report['summary']['orphan_claims'] == 0, (
            f"{report['summary']['orphan_claims']} orphan paper-claim(s): "
            f"{[o['id'] for o in report['orphan_claims'][:10]]}"
        )
        # orphan_claims is exactly the PaperClaim subset of orphan_nodes.
        pc_orphans = [o for o in report['orphan_nodes'] if o['type'] == 'PaperClaim']
        assert len(pc_orphans) == report['summary']['orphan_claims']


class TestDetectsKnownConflict:
    """Tests that the integrity checker detects conflicts via verification status."""

    def test_detects_known_conflict(self, all_graph_nodes, graph_integrity_report):
        """Conflict detection is consistent: summary count matches conflict list,
        and any conflict entries have the expected fields.

        Note: omega_perp previously had a conflict but it has been resolved.
        This test validates the detection mechanism works structurally.
        """
        report = graph_integrity_report

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
        nodes = all_graph_nodes
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

    def test_no_orphaned_findings(self, all_graph_nodes, all_graph_node_ids, all_graph_edges):
        """Every ReviewFinding is either (a) source of a FLAGS edge, or
        (b) part of a SUPERSEDES chain. Orphan findings indicate the
        heuristic body-text paper-attribution failed and the finding
        won't surface in the dashboard."""
        from scripts.build_graph import extract_all_nodes, extract_all_edges

        nodes = all_graph_nodes
        node_ids = all_graph_node_ids
        edges = all_graph_edges

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
        # Floor raised 0.25 -> 0.70 on 2026-06-17 after bundle-code attribution
        # landed: bundle-era reviews (D*/L*/I*/F/E*.md) now resolve through the
        # inverted PAPER_DRAFT_MAPPING to their source Paper nodes, lifting the
        # achieved attach-rate from ~46% to ~82%. 0.70 leaves safe margin below
        # the achieved rate while guarding against regression of either the
        # paper-key matcher or the bundle-code matcher. The residual orphans are
        # findings on bundles whose sources are all `_phaseXX_lean_only` dirs
        # with no Paper node (e.g. I2/I3/D7/D8) — intentionally left unattached.
        #
        # ⚠️ **0.70 -> 0.89 on 2026-08-15, AND THIS IS A RE-DERIVATION FROM A CORRECTED
        # INSTRUMENT, NOT AN ACCOMMODATION.** `extract_flags_edges` was taught to call
        # `build_graph.resolve_attribution` — the same resolver the readiness aggregation
        # already used — instead of resolving from the two inferences on its own. Measured
        # over the live corpus of 1749 findings: orphans 208 -> 178, attach-rate
        # **0.881075 -> 0.898228**, FLAGS edges 4987 -> 6227. Nothing was added to the
        # corpus; 30 findings that always declared a resolvable target stopped being
        # invisible to this edge type.
        #
        # The floor is placed at 0.89 DELIBERATELY BETWEEN the two measured values, which
        # 0.70 could not do: a floor beneath the pre-fix rate cannot detect the pre-fix
        # behaviour, so reverting the shared resolver would have left this test green.
        # 0.70 carried eighteen points of headroom, and a ratchet with headroom is not a
        # loose guard, it is no guard. ~0.8 points of margin remain — about fourteen
        # findings — which is a real budget for new review documents and a real alarm if
        # a batch of them lands declaring targets that resolve nowhere.
        attach_rate = 1.0 - (len(orphans) / len(findings))
        assert attach_rate >= 0.89, (
            f"Only {attach_rate:.1%} of {len(findings)} ReviewFindings are "
            f"attached via FLAGS/SUPERSEDES; attribution may be failing. Measured "
            f"0.898228 on 2026-08-15 with both layers sharing "
            f"`build_graph.resolve_attribution`; 0.881075 with the graph layer "
            f"resolving on its own. First 3 orphans: {orphans[:3]}"
        )


class TestCountMetricIntegrity:
    """CountMetric snapshot values should match canonical counts.json."""

    def test_count_metric_matches_canonical(self, all_graph_nodes):
        """Every CountMetric node whose id ends in ':current' carries the
        canonical value from counts.json in meta.value. Drift is a bug in
        the extractor (stale snapshot) or in counts.json itself."""
        from scripts.build_graph import extract_all_nodes

        nodes = all_graph_nodes
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

    def test_bounds_only_formulas_flagged(self, all_graph_nodes, all_graph_node_ids):
        """A Formula with VERIFIES incoming edges ALL of test_kind='bounds'
        has no golden/identity coverage — this is a ComputationCorrectness
        gate signal. This test does not fail; it asserts the integrity
        checker surfaces the count, enabling the readiness gate to fire.
        """
        from scripts.build_graph import (
            extract_all_nodes, extract_formula_nodes, extract_verifies_edges,
        )

        nodes = all_graph_nodes
        node_ids = all_graph_node_ids
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
        # ⚠️ A ZERO-HEADROOM RATCHET, measured AT the live population.
        #
        # This went through two wrong versions. It first asserted
        # `bounds_only_rate < 0.80` against a live 0.101 — 70 points of headroom, an
        # eightfold collapse needed to fire, on a test whose own docstring said "This
        # test does not fail". I replaced that with `0.0 <= rate <= 1.0`, which a
        # reviewer then PROVED unfalsifiable: `bounds_only` is a comprehension over
        # `incoming_by_target`, `covered = len(incoming_by_target)`, and `covered == 0`
        # is already skipped — so the range holds for every possible input. That
        # traded a weak test for a vacuous one, which the house rule forbids:
        # a replacement must be STRONGER than what it replaces.
        #
        # The house idiom is a count frozen at what the corpus actually reaches, and
        # lowered — never raised — when the debt shrinks. 35 of 347 formulas have
        # bounds-only coverage today. If that grows, someone added a formula with no
        # golden/identity test and this fires; if it shrinks, lower the number in the
        # same commit that earns it.
        BOUNDS_ONLY_CEILING = 35

        assert len(bounds_only) <= BOUNDS_ONLY_CEILING, (
            f"{len(bounds_only)} of {covered} covered formulas have bounds-only "
            f"coverage, above the frozen {BOUNDS_ONLY_CEILING}. A formula gained "
            f"VERIFIES edges that are ALL test_kind='bounds' — it has no "
            f"golden/identity coverage. New: {sorted(bounds_only)[:3]}")
        assert len(bounds_only) == BOUNDS_ONLY_CEILING, (
            f"bounds-only coverage FELL to {len(bounds_only)} from "
            f"{BOUNDS_ONLY_CEILING} — good news the ratchet must record. Lower "
            f"BOUNDS_ONLY_CEILING here, in this commit; headroom makes it unfireable.")
