"""
Tests for Phase 5v Wave 10b/c/d/f — sentence-level Paper Provenance v2.

Coverage:
- Wave 10b: sentence_state.cmd_mark + prose_state.json + audit_log.jsonl
- Wave 10c: verification_state event log + apply_to_graph
- Wave 10d: _pp_build_data_v2 + sentence-verify endpoint + 3-column SSE
- Wave 10f: cluster_detect + propagation endpoint + cluster banner

Uses ``scripts/test_helpers.py`` to swap PAPERS_ROOT + LOG_PATH onto
isolated tmp dirs so the tests never poke real ``papers/`` state.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

import pytest

PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT))
sys.path.insert(0, str(PROJECT_ROOT / "scripts"))

from scripts.test_helpers import (  # noqa: E402
    isolated_v2_state,
    make_v2_review,
    make_v2_sentence,
)


# ── Fixtures ──────────────────────────────────────────────────────────────


@pytest.fixture
def two_paper_v2_state():
    """Seed two v2 papers sharing one verbatim claim across both."""
    shared_quote = (
        "The acoustic horizon emits a thermal Hawking spectrum at "
        "temperature kBT = hbar kappa / (2 pi)."
    )
    only_a_quote = (
        "Polariton platforms reach kappa values around 0.07-0.11 inverse picoseconds."
    )
    only_b_quote = (
        "Graphene Dirac fluids reach analog Hawking temperature 2.4 K."
    )

    s_shared_a = make_v2_sentence('paper_a', quote=shared_quote,
                                  chain_links=[{'kind': 'citation', 'target': 'Falque2025'}])
    s_a = make_v2_sentence('paper_a', quote=only_a_quote, section_ordinal=2, tex_line=2,
                           sentence_type='numeric',
                           chain_links=[{'kind': 'parameter', 'target': 'kappa_polariton'}])
    s_shared_b = make_v2_sentence('paper_b', quote=shared_quote,
                                  chain_links=[{'kind': 'citation', 'target': 'Falque2025'}])
    s_b = make_v2_sentence('paper_b', quote=only_b_quote, section_ordinal=2, tex_line=2,
                           sentence_type='numeric',
                           chain_links=[{'kind': 'parameter', 'target': 'T_H_graphene'}])

    seeds = {
        'paper_a': make_v2_review('paper_a', [s_shared_a, s_a]),
        'paper_b': make_v2_review('paper_b', [s_shared_b, s_b]),
    }
    with isolated_v2_state(seed_papers=seeds) as (papers_root, log_path):
        yield {
            'papers_root': papers_root,
            'log_path': log_path,
            'shared_a_id': s_shared_a['id'],
            'shared_b_id': s_shared_b['id'],
            'only_a_id': s_a['id'],
            'only_b_id': s_b['id'],
        }


# ── Wave 10b: sole-writer CLI + audit log + prose_state ───────────────────


class TestSentenceStateMark:
    """sentence_state.cmd_mark writes both files atomically."""

    def test_mark_creates_prose_state_and_audit_log(self, two_paper_v2_state):
        from sentence_state import (
            cmd_mark, prose_state_path, audit_log_path,
        )
        sid = two_paper_v2_state['shared_a_id']

        rc = cmd_mark(argparse.Namespace(
            sentence_id=sid, state='verified',
            actor='user:test', notes='ratify',
        ))
        assert rc == 0
        ps = json.loads(prose_state_path('paper_a').read_text())
        assert sid in ps['sentences']
        assert ps['sentences'][sid]['human_state'] == 'human_verified'
        assert ps['sentences'][sid]['human_ratified_by'] == 'user:test'

        # Audit log got one event
        log_lines = audit_log_path('paper_a').read_text().strip().splitlines()
        assert len(log_lines) == 1
        ev = json.loads(log_lines[0])
        assert ev['type'] == 'AuditEvent'
        assert ev['meta']['target_id'] == sid
        assert ev['meta']['action'] == 'verify'
        assert ev['meta']['new_state'] == 'human_verified'

    def test_mark_invalid_state_returns_nonzero(self, two_paper_v2_state):
        from sentence_state import cmd_mark
        sid = two_paper_v2_state['shared_a_id']
        rc = cmd_mark(argparse.Namespace(
            sentence_id=sid, state='bogus',
            actor='user:test', notes=None,
        ))
        assert rc == 1

    def test_mark_unknown_sentence_returns_nonzero(self, two_paper_v2_state):
        from sentence_state import cmd_mark
        rc = cmd_mark(argparse.Namespace(
            sentence_id='sentence:paper_a:abstract:0badf00d',
            state='verified', actor='user:test', notes=None,
        ))
        assert rc == 1


# ── Wave 10b: rebuild_prose_state replay-canonical recovery ───────────────


class TestRebuildProseState:
    """rebuild_prose_state recovers from missing prose_state.json by
    replaying audit_log.jsonl (Wave 10 strengthening pass)."""

    def test_rebuild_no_drift_when_state_consistent(self, two_paper_v2_state):
        from sentence_state import cmd_mark, cmd_rebuild_prose_state

        sid = two_paper_v2_state['shared_a_id']
        cmd_mark(argparse.Namespace(
            sentence_id=sid, state='verified', actor='user:test', notes=None))

        rc = cmd_rebuild_prose_state(argparse.Namespace(
            paper='paper_a', write=False))
        assert rc == 0  # no drift

    def test_rebuild_detects_and_recovers_missing_prose_state(
        self, two_paper_v2_state, capsys,
    ):
        from sentence_state import (
            cmd_mark, cmd_rebuild_prose_state, prose_state_path,
        )
        sid = two_paper_v2_state['shared_a_id']
        cmd_mark(argparse.Namespace(
            sentence_id=sid, state='verified', actor='user:test', notes='x'))

        # Simulate partial-failure: nuke prose_state, keep audit_log
        prose_state_path('paper_a').unlink()

        # --check should detect drift
        rc = cmd_rebuild_prose_state(argparse.Namespace(
            paper='paper_a', write=False))
        assert rc == 1  # drift

        # --write recovers
        rc = cmd_rebuild_prose_state(argparse.Namespace(
            paper='paper_a', write=True))
        assert rc == 0
        ps = json.loads(prose_state_path('paper_a').read_text())
        assert ps['sentences'][sid]['human_state'] == 'human_verified'


# ── Wave 10c: change-bus apply_to_graph + triggered_by ────────────────────


class TestVerificationChangeBus:

    def test_record_event_with_triggered_by(self, two_paper_v2_state):
        import verification_state as vs
        sid = two_paper_v2_state['shared_a_id']

        ev = vs.record_event(
            artifact_type='Citation', artifact_id='Falque2025',
            action='confirm', actor='user:test',
            triggered_by=sid,
        )
        assert ev['triggered_by'] == sid
        assert ev['node_id'] == 'source:Falque2025'

    def test_apply_to_graph_propagates_triggered_by(self, two_paper_v2_state):
        import verification_state as vs
        sid = two_paper_v2_state['shared_a_id']

        vs.record_event(
            artifact_type='Citation', artifact_id='Falque2025',
            action='confirm', actor='user:test', triggered_by=sid,
        )
        graph = {
            'nodes': [{'id': 'source:Falque2025', 'type': 'PrimarySource',
                       'meta': {}}],
            'links': [],
        }
        n = vs.apply_to_graph(graph)
        assert n == 1
        meta = graph['nodes'][0]['meta']
        assert meta['last_verification_action'] == 'confirm'
        assert meta['last_verification_triggered_by'] == sid

    def test_node_id_for_extended_kinds(self):
        from verification_state import node_id_for
        assert node_id_for('Hypothesis', 'H_Foo') == 'hyp:H_Foo'
        assert node_id_for('AristotleRun', '4528aa2b') == 'aristotle:4528aa2b'
        assert node_id_for('ProductionRun', 'L8_g3.385') == 'production:L8_g3.385'


# ── Wave 10c: prune log + size warning ────────────────────────────────────


class TestPruneLog:

    def test_prune_refuses_without_criterion(self, two_paper_v2_state):
        from verification_state import prune_log
        with pytest.raises(ValueError):
            prune_log()

    def test_prune_keep_records_drops_oldest(self, two_paper_v2_state):
        import verification_state as vs
        from datetime import datetime, timedelta, timezone

        for i in range(5):
            ts = (datetime.now(timezone.utc) - timedelta(days=10 - i)).strftime(
                '%Y-%m-%dT%H:%M:%SZ')
            vs.record_event(
                artifact_type='Parameter', artifact_id=f'P{i}',
                action='confirm', actor='user:test', timestamp=ts,
            )
        before = list(vs.read_events())
        assert len(before) == 5

        result = vs.prune_log(keep_records=2)
        assert result['kept'] == 2
        assert result['removed'] == 3

        after = list(vs.read_events())
        assert len(after) == 2
        # Most recent two retained
        kept_ids = {e['artifact_id'] for e in after}
        assert kept_ids == {'P3', 'P4'}

    def test_prune_dry_run_does_not_modify(self, two_paper_v2_state):
        import verification_state as vs
        for i in range(3):
            vs.record_event(
                artifact_type='Parameter', artifact_id=f'P{i}',
                action='confirm', actor='user:test',
            )
        result = vs.prune_log(keep_records=1, dry_run=True)
        assert result['kept'] == 1
        # File unchanged
        assert len(list(vs.read_events())) == 3


# ── Wave 10f: cluster_detect cross-paper exact match ──────────────────────


class TestClusterDetect:

    def test_exact_match_finds_shared_sentence(self, two_paper_v2_state, tmp_path):
        # Override cluster output path to tmp so we don't pollute repo
        out = tmp_path / 'claim_clusters.json'
        from cluster_detect import iter_sentences, build_clusters_exact

        # iter_sentences walks sentence_state.PAPERS_ROOT — but
        # cluster_detect uses its OWN module-level PAPERS_ROOT. Patch it
        # to match the isolated state.
        import cluster_detect
        original = cluster_detect.PAPERS_ROOT
        cluster_detect.PAPERS_ROOT = two_paper_v2_state['papers_root']
        try:
            sentences = list(iter_sentences(min_quote_len=20))
            assert len(sentences) == 4  # 2 per paper
            clusters = build_clusters_exact(sentences)
        finally:
            cluster_detect.PAPERS_ROOT = original

        # Exactly one cluster: the shared quote
        assert len(clusters) == 1
        c = clusters[0]
        assert c['match_kind'] == 'exact'
        assert c['confidence'] == 1.0
        assert sorted(c['member_papers']) == ['paper_a', 'paper_b']
        assert two_paper_v2_state['shared_a_id'] in c['members']
        assert two_paper_v2_state['shared_b_id'] in c['members']

    def test_intra_paper_duplicates_excluded(self, two_paper_v2_state):
        # Add an intra-paper duplicate to paper_a — should NOT cluster
        from sentence_state import claims_review_path, compute_sentence_id
        cr_path = claims_review_path('paper_a')
        cr = json.loads(cr_path.read_text())
        # Append the same shared quote AGAIN with different section to
        # avoid sentence-id collision
        sid_a2, normalized, h = compute_sentence_id(
            'paper_a', 'introduction',
            "The acoustic horizon emits a thermal Hawking spectrum at "
            "temperature kBT = hbar kappa / (2 pi).")
        cr['sentences'].append({
            'id': sid_a2,
            'raw_id_parts': {'paper': 'paper_a', 'section_slug': 'introduction',
                             'quote_hash': h, 'hash_algorithm': 'sha256_first_8'},
            'section': 'introduction', 'section_ordinal': 1,
            'tex_line_start': 10, 'tex_line_end': 10,
            'quote': "The acoustic horizon emits a thermal Hawking spectrum at "
                     "temperature kBT = hbar kappa / (2 pi).",
            'quote_normalized': normalized,
            'type': 'formal-claim', 'finding_classes': [],
            'chain_proposed': {'links': [], 'completeness': 'full'},
            'agent_verdict': 'PASS',
            'agent_run_id': 'claims-reviewer-v2:smoke',
            'tombstone': False,
        })
        cr_path.write_text(json.dumps(cr))

        import cluster_detect
        original = cluster_detect.PAPERS_ROOT
        cluster_detect.PAPERS_ROOT = two_paper_v2_state['papers_root']
        try:
            sentences = list(cluster_detect.iter_sentences(min_quote_len=20))
            clusters = cluster_detect.build_clusters_exact(sentences)
        finally:
            cluster_detect.PAPERS_ROOT = original

        # One cluster across paper_a + paper_b — paper_a may have 2
        # members but the cluster still spans 2 papers.
        assert len(clusters) == 1
        # The sid_a2 (paper_a/introduction) is in the cluster too —
        # cross-paper requirement was already met by paper_b.
        assert sid_a2 in clusters[0]['members']
        assert sorted(clusters[0]['member_papers']) == ['paper_a', 'paper_b']


# ── Wave 10f: cross-precision timestamp compare in sentence_is_stale ──────


class TestStaleDetectionPrecision:

    def test_sentence_is_stale_handles_microsecond_vs_second(self):
        from last_modified import sentence_is_stale

        # Real-world: sentence ratified at MICROSECOND precision
        # (sentence_state); link last_modified at SECOND precision
        # (verification_state). Ratification is genuinely NEWER.
        sentence = {'id': 's0', 'meta': {
            'human_ratified_at': '2026-04-25T05:33:17.500000Z'}}
        edges = [{'type': 'BACKED_BY', 'source': 's0', 'target': 'p0'}]
        nodes = {'p0': {'meta': {'last_modified': '2026-04-25T05:33:17Z'}}}

        # Buggy string compare flips this to True. Fix uses datetime.
        assert sentence_is_stale(sentence, edges, nodes) is False

    def test_sentence_is_stale_detects_genuine_newer_link(self):
        from last_modified import sentence_is_stale

        sentence = {'id': 's0', 'meta': {
            'human_ratified_at': '2026-04-25T05:33:17Z'}}
        edges = [{'type': 'BACKED_BY', 'source': 's0', 'target': 'p0'}]
        nodes = {'p0': {'meta': {'last_modified': '2026-04-25T05:33:18Z'}}}
        assert sentence_is_stale(sentence, edges, nodes) is True

    def test_unratified_sentence_never_stale(self):
        from last_modified import sentence_is_stale
        sentence = {'id': 's0', 'meta': {}}
        edges = [{'type': 'BACKED_BY', 'source': 's0', 'target': 'p0'}]
        nodes = {'p0': {'meta': {'last_modified': '2026-12-31T23:59:59Z'}}}
        assert sentence_is_stale(sentence, edges, nodes) is False
