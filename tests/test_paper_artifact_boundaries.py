"""Production paper readers/writer seams, with dummy roots and read sentinels.

These cases distinguish the prior child-symlink defect; they do not claim
hostile-race confinement or database capability from fixtures.
"""
from __future__ import annotations

import argparse
import builtins
import io
import json
import os
import sys
import subprocess
import textwrap
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from src.core.paper_artifacts import paper_artifact_path


def test_dummy_server_actual_audit_retains_lexical_identity(tmp_path):
    """The real child hook refuses renamed escapes without poisoning pytest."""
    helper = ROOT / 'tests' / 'e2e' / 'dummy_paper_server.py'
    program = textwrap.dedent('''
        import json, os, runpy, sys
        from pathlib import Path
        root = Path(sys.argv[1]).resolve()
        project = root / 'fake_project'
        disposable = root / 'disposable'
        papers = disposable / 'papers'
        papers.mkdir(parents=True)
        corpus = project / 'papers'
        corpus.mkdir(parents=True)
        ordinary = papers / 'prose_state.json'
        ordinary.write_text('allowed')
        linked = papers / 'claims_review.json'
        linked.symlink_to(ordinary)
        outside = disposable / 'outside_claims.json'
        outside.write_text('outside')
        escaped_dir = papers / 'escaping'
        escaped_dir.mkdir()
        escaped = escaped_dir / 'claims_review.json'
        escaped.symlink_to(outside)
        origin = corpus / 'claims_review.json'
        origin.symlink_to(ordinary)
        dir_fd = os.open(papers, os.O_RDONLY)
        record = {'violations': []}
        evidence = root / 'refused.json'
        def save():
            evidence.write_text(json.dumps(record))
        guard = runpy.run_path(sys.argv[2])['paper_fixture_audit']
        sys.addaudithook(guard(project, disposable, record, save))
        assert ordinary.read_text() == linked.read_text() == 'allowed'
        for path in [escaped, origin]:
            try:
                path.read_text()
            except AssertionError:
                pass
            else:
                raise AssertionError('guard permitted an escaped or corpus-origin read')
        try:
            os.open('claims_review.json', os.O_RDONLY, dir_fd=dir_fd)
        except AssertionError:
            pass
        else:
            raise AssertionError('guard invented a base for an ambiguous relative open')
        finally:
            os.close(dir_fd)
        assert [x['reason'] for x in record['violations']] == [
            'escaped_paper_artifact', 'real_corpus_origin_or_target',
            'ambiguous_relative_paper_open']
        assert record['violations'][0]['lexical'] == str(escaped)
        assert record['violations'][0]['resolved'] == str(outside)
        assert record['violations'][1]['lexical'] == str(origin)
        assert record['violations'][1]['resolved'] == str(ordinary)
        assert record['violations'][2]['resolved'] is None
        assert json.loads(evidence.read_text()) == record
    ''')
    result = subprocess.run([sys.executable, '-B', '-c', program, str(tmp_path), str(helper)],
                            capture_output=True, text=True, timeout=30)
    assert result.returncode == 0, result.stderr


@pytest.fixture
def artifacts(tmp_path, monkeypatch):
    monkeypatch.setenv('SK_EFT_GRAPH_SOURCE', 'json')
    import provenance_dashboard as dash
    import build_graph as graph
    import readiness_gates as readiness
    import sentence_state as state
    import verification_state as verification
    root = tmp_path / 'fixture'
    papers = root / 'papers'
    papers.mkdir(parents=True)
    (root / 'lean' / 'SKEFTHawking').mkdir(parents=True)
    for module in (dash, graph):
        monkeypatch.setattr(module, 'PROJECT_ROOT', root)
    monkeypatch.setattr(readiness, 'PAPERS_DIR', papers)
    monkeypatch.setattr(state, 'PAPERS_ROOT', papers)
    monkeypatch.setattr(verification, 'LOG_PATH', root / 'verification_log.jsonl')
    monkeypatch.setattr(verification, 'LOCK_PATH', root / 'verification_log.jsonl.lock')
    monkeypatch.setitem(dash.app.config, 'PG_SYNC_ENABLED', False)
    monkeypatch.setattr(dash, 'get_cached_graph', lambda **kw: {'nodes': [], 'links': []})
    import psycopg
    monkeypatch.setattr(psycopg, 'connect', lambda *a, **k: pytest.fail('unexpected DB connection'))
    # Refuse actual reads outside this fixture for the artifact family, even if
    # a missed independently bound root or escaping symlink is encountered.
    original_open, original_io_open = builtins.open, io.open
    family = {'paper_draft.tex', 'claims_review.json', 'figure_review_report.json',
              'prose_state.json', 'audit_log.jsonl'}
    def guard(original):
        def opened(file, mode='r', *args, **kwargs):
            if isinstance(file, (str, bytes, os.PathLike)) and 'r' in mode:
                path = Path(os.fsdecode(file))
                if path.name in family:
                    resolved = path.resolve()
                    assert papers in resolved.parents, f'outside paper-family read: {path}'
            return original(file, mode, *args, **kwargs)
        return opened
    monkeypatch.setattr(builtins, 'open', guard(original_open))
    monkeypatch.setattr(io, 'open', guard(original_io_open))
    return root, papers, dash, graph, readiness, state


def seed(papers, name='paper_a'):
    directory = papers / name
    directory.mkdir()
    (directory / 'paper_draft.tex').write_text(
        r'\title{Dummy title}\begin{abstract}First proof claim in a dummy manuscript.\end{abstract}'
        r'\includegraphics{figures/dummy.png}\bibitem{Dummy2026}\texttt{dummy_theorem}')
    (directory / 'claims_review.json').write_text(json.dumps({'paper': name, 'sentences': []}))
    (directory / 'prose_state.json').write_text('{"sentences": {}}')
    (directory / 'audit_log.jsonl').write_text('{"id":"dummy","meta":{}}\n')
    (directory / 'figures').mkdir()
    (directory / 'figures' / 'figure_review_report.json').write_text('{"figures": []}')
    return directory


@pytest.mark.parametrize('artifact,loader,empty', [
    ('claims_review.json', '_pp_load_claims_review', None),
    ('figures/figure_review_report.json', '_pp_load_figure_review', None),
    ('prose_state.json', '_pp_load_prose_state', {'version': 1, 'paper': 'paper_a', 'sentences': {}}),
    ('audit_log.jsonl', '_pp_load_audit_log', []),
])
@pytest.mark.parametrize('kind', ['escape', 'dangling', 'cycle'])
def test_direct_readers_refuse_before_open(artifacts, tmp_path, artifact, loader, empty, kind):
    root, papers, dash, *_ = artifacts
    directory = seed(papers)
    target = directory / artifact
    target.unlink()
    outside = tmp_path / 'outside'
    outside.write_text('{"sentences": [], "outside": true}')
    destination = {'escape': outside, 'dangling': papers / 'missing', 'cycle': target}[kind]
    target.symlink_to(destination)
    assert getattr(dash, loader)('paper_a') == empty


def test_intermediate_directory_escape_is_refused(artifacts, tmp_path):
    _, papers, dash, *_ = artifacts
    directory = seed(papers)
    (directory / 'figures' / 'figure_review_report.json').unlink()
    (directory / 'figures').rmdir()
    outside = tmp_path / 'outside'; outside.mkdir()
    (outside / 'figure_review_report.json').write_text('{"outside": true}')
    (directory / 'figures').symlink_to(outside)
    assert dash._pp_load_figure_review('paper_a') is None


@pytest.mark.parametrize('kind', ['escape', 'dangling', 'cycle', 'missing'])
def test_tex_family_routes_discovery_and_readiness_refuse(artifacts, tmp_path, kind):
    _, papers, dash, graph, readiness, _ = artifacts
    directory = seed(papers)
    tex = directory / 'paper_draft.tex'; tex.unlink()
    outside = tmp_path / 'outside.tex'; outside.write_text('OUTSIDE TEX')
    if kind != 'missing':
        tex.symlink_to({'escape': outside, 'dangling': papers / 'missing', 'cycle': tex}[kind])
    assert dash._pp_list_papers() == []
    assert dash.app.test_client().get('/api/papers/list').json == {'papers': []}
    assert dash._pp_build_data('paper_a') is None
    assert dash._pp_extract_abstract(tex) == ''
    assert 'OUTSIDE TEX' not in dash._pp_paper_body_html({'paper_id': 'paper_a'}, '')
    assert dash.load_paper_claims(graph={'nodes': [], 'links': []}) == []
    assert graph.discover_paper_draft_paths(papers) == []
    assert graph._parse_tex_title(tex) is None
    assert graph.extract_prose_claim_nodes() == []
    assert graph.extract_has_figure_edges({'paper:paper_a', 'figure:dummy'}) == []
    assert graph.extract_cites_source_edges({'paper:paper_a', 'source:Dummy2026'}) == []
    assert readiness.GraphIndex({'nodes': [], 'links': []}).paper_tex('paper_a') is None


def test_in_root_links_keep_lexical_identity_and_empty_read(artifacts):
    _, papers, dash, graph, readiness, _ = artifacts
    a, b = seed(papers), seed(papers, 'paper_b')
    (a / 'paper_draft.tex').unlink()
    (a / 'paper_draft.tex').symlink_to(b / 'paper_draft.tex')
    assert dash._pp_build_data('paper_a')['paper_id'] == 'paper_a'
    nodes = graph.extract_paper_nodes()
    a_node = next(n for n in nodes if n['id'] == 'paper:paper_a')
    assert a_node['meta']['tex_path'] == 'papers/paper_a/paper_draft.tex'
    assert len(graph.discover_paper_draft_paths(papers)) == 2
    assert dash._pp_extract_abstract(a / 'paper_draft.tex') == 'First proof claim in a dummy manuscript.'
    for name in ('claims_review.json', 'prose_state.json', 'audit_log.jsonl'):
        (a / name).unlink(); (a / name).symlink_to(b / name)
    assert dash._pp_load_claims_review('paper_a')['paper'] == 'paper_b'
    assert graph._load_claims_review(a)['paper'] == 'paper_b'
    assert graph._load_audit_log(a)[0]['id'] == 'dummy'
    (b / 'paper_draft.tex').write_text('')
    assert readiness.GraphIndex({'nodes': [], 'links': []}).paper_tex('paper_a') == ''
    assert 'paper_a' in {p['paper_id'] for p in dash._pp_list_papers()}


def test_graph_json_state_readers_and_malformed_files(artifacts, tmp_path):
    _, papers, dash, graph, _, _ = artifacts
    directory = seed(papers)
    outside = tmp_path / 'outside.json'; outside.write_text('{}')
    for filename, loader, expected in [
        ('claims_review.json', graph._load_claims_review, None),
        ('prose_state.json', graph._load_prose_state, {'sentences': {}}),
        ('audit_log.jsonl', graph._load_audit_log, []),
    ]:
        target = directory / filename
        target.unlink(); target.symlink_to(outside)
        assert loader(directory) == expected
        target.unlink(); target.write_text('invalid json')
        assert loader(directory) == expected
    (directory / 'claims_review.json').write_text('[]')
    (directory / 'prose_state.json').write_text('[]')
    assert dash._pp_load_claims_review('paper_a') is None
    assert dash._pp_load_prose_state('paper_a')['sentences'] == {}
    assert graph._load_claims_review(directory) is None


@pytest.mark.parametrize('paper_id', ['../outside', '', '.', '..', 'x/y', 'x\\y', None, 42])
def test_bad_selected_ids_are_refused(artifacts, paper_id):
    _, papers, dash, *_ = artifacts
    assert paper_artifact_path(papers, paper_id, 'paper_draft.tex') is None
    assert dash._pp_build_data(paper_id) is None


@pytest.mark.parametrize('prerequisite', ['claims_review.json', 'prose_state.json', 'audit_log.jsonl', 'prose_state.json.lock'])
def test_writer_refuses_unsafe_prerequisite_before_audit(artifacts, tmp_path, prerequisite):
    _, papers, dash, graph, _, state = artifacts
    directory = seed(papers)
    sid = 'sentence:paper_a:abstract:12345678'
    (directory / 'claims_review.json').write_text(json.dumps({'sentences': [{'id': sid}]}))
    outside = tmp_path / 'outside.json'; outside.write_text('DO NOT TOUCH')
    target = directory / prerequisite
    if target.exists(): target.unlink()
    target.symlink_to(outside)
    args = argparse.Namespace(sentence_id=sid, state='verified', actor='user:test', notes='test')
    assert state.cmd_mark(args) == 1
    assert outside.read_text() == 'DO NOT TOUCH'
    assert not (directory / 'prose_state.json.lock').exists() or prerequisite == 'prose_state.json.lock'
    if prerequisite != 'audit_log.jsonl':
        assert (directory / 'audit_log.jsonl').read_text() == '{"id":"dummy","meta":{}}\n'


def test_selected_directory_escape_refuses_writer_without_outside_lock(artifacts, tmp_path):
    _, papers, dash, _, _, state = artifacts
    outside = tmp_path / 'outside'; outside.mkdir()
    (papers / 'paper_a').symlink_to(outside)
    assert dash._safe_paper_dir('paper_a') is None
    assert state.cmd_mark(argparse.Namespace(sentence_id='sentence:paper_a:a:12345678',
                         state='verified', actor='user:test', notes='')) == 1
    assert not (outside / 'prose_state.json.lock').exists()


@pytest.mark.parametrize('command,filename', [('cmd_reconcile', 'claims_review.json'),
    ('cmd_tombstone_sweep', 'claims_review.json'), ('cmd_rebuild_prose_state', 'audit_log.jsonl')])
def test_related_sentence_state_reads_refuse(artifacts, tmp_path, command, filename):
    _, papers, _, _, _, state = artifacts
    directory = seed(papers)
    outside = tmp_path / 'outside'; outside.write_text('{}')
    target = directory / filename; target.unlink(); target.symlink_to(outside)
    assert getattr(state, command)(argparse.Namespace(paper='paper_a', write=True)) == 1


def test_writer_audit_first_and_replay_preserved(artifacts, monkeypatch):
    _, papers, _, _, _, state = artifacts
    directory = seed(papers)
    (directory / 'audit_log.jsonl').write_text('')
    sid = 'sentence:paper_a:abstract:12345678'
    (directory / 'claims_review.json').write_text(json.dumps({'sentences': [{'id': sid}]}))
    original = state._atomic_write_prose_state
    def fail_after_audit(paper, value):
        assert json.loads((directory / 'audit_log.jsonl').read_text())['meta']['target_id'] == sid
        raise OSError('controlled atomic replacement failure')
    monkeypatch.setattr(state, '_atomic_write_prose_state', fail_after_audit)
    assert state.cmd_mark(argparse.Namespace(sentence_id=sid, state='verified', actor='user:test', notes='')) == 1
    assert json.loads((directory / 'prose_state.json').read_text()) == {'sentences': {}}
    monkeypatch.setattr(state, '_atomic_write_prose_state', original)
    assert state.cmd_rebuild_prose_state(argparse.Namespace(paper='paper_a', write=True)) == 0
    assert json.loads((directory / 'prose_state.json').read_text())['sentences'][sid]['human_state'] == 'human_verified'


def test_v1_v2_routes_and_sse_use_confined_tex(artifacts, tmp_path):
    _, papers, dash, _, _, _ = artifacts
    directory = seed(papers)
    client = dash.app.test_client()
    for review in ({'sentences': []}, {}):
        (directory / 'claims_review.json').write_text(json.dumps(review))
        response = client.get('/api/papers/paper_a/provenance')
        assert response.status_code == 200
        assert response.json['paper_id'] == 'paper_a'
        sse = client.get('/api/papers/paper_a/provenance', headers={'Accept': 'text/event-stream'})
        assert sse.status_code == 200 and b'datastar-' in sse.data
    (directory / 'paper_draft.tex').unlink()
    outside = tmp_path / 'outside.tex'; outside.write_text('OUTSIDE')
    (directory / 'paper_draft.tex').symlink_to(outside)
    assert client.get('/api/papers/paper_a/provenance').status_code == 404
    refused = client.get('/api/papers/paper_a/provenance', headers={'Accept': 'text/event-stream'})
    assert b'OUTSIDE' not in refused.data


def test_actual_tex_graph_extractors_and_sentence_ingestion(artifacts, monkeypatch, tmp_path):
    _, papers, _, graph, _, _ = artifacts
    directory = seed(papers)
    ids = {'paper:paper_a', 'figure:dummy', 'source:Dummy2026'}
    assert graph.extract_has_figure_edges(ids)[0]['source'] == 'paper:paper_a'
    assert graph.extract_cites_source_edges(ids)[0]['target'] == 'source:Dummy2026'
    assert graph.extract_prose_claim_nodes()[0]['meta']['paper'] == 'paper_a'
    assert isinstance(graph.extract_paper_claim_nodes(), list)
    monkeypatch.setattr(graph, 'extract_lean_declaration_nodes', lambda: [])
    monkeypatch.setattr(graph, 'extract_count_metric_nodes', lambda: [])
    # Exercise their actual reads without invoking unrelated Lean/count producers.
    assert graph.extract_cites_theorem_edges(ids) == []
    assert graph.extract_reports_edges(ids) == []
    sid = 'sentence:paper_a:abstract:12345678'
    (directory / 'claims_review.json').write_text(json.dumps({'sentences': [{'id': sid, 'quote': 'dummy'}]}))
    assert graph.extract_sentence_nodes()[0]['id'] == sid
    assert graph.extract_audit_event_nodes()[0]['id'] == 'dummy'
    outside = tmp_path / 'sentinel'; outside.write_text('{"sentences": [{"id":"OUTSIDE"}]}')
    for name in ('claims_review.json', 'prose_state.json', 'audit_log.jsonl'):
        target = directory / name; target.unlink(); target.symlink_to(outside)
    assert graph.extract_sentence_nodes() == []
    assert graph.extract_audit_event_nodes() == []
    assert graph.extract_backed_by_edges(ids) == []
    assert graph.extract_logged_by_edges(ids) == []
    tex = directory / 'paper_draft.tex'; tex.unlink(); tex.symlink_to(outside)
    assert graph.extract_cites_theorem_edges(ids) == []
    assert graph.extract_reports_edges(ids) == []
    assert not any(n['id'] == 'paper:paper_a' for n in graph.extract_paper_nodes())


def test_delegated_dashboard_writer_refuses_claims_and_prose_escapes(artifacts, tmp_path):
    _, papers, dash, _, _, _ = artifacts
    directory = seed(papers)
    sid = 'sentence:paper_a:abstract:12345678'
    (directory / 'claims_review.json').write_text(json.dumps({'sentences': [{'id': sid}]}))
    outside = tmp_path / 'sentinel'; outside.write_text('{"sentences": {}}')
    target = directory / 'prose_state.json'; target.unlink(); target.symlink_to(outside)
    response = dash.app.test_client().post(f'/api/papers/paper_a/sentences/{sid}/verify',
                                         json={'state': 'verified', 'actor': 'user:test'})
    assert response.status_code == 400
    assert response.json.get('ok') is not True
    assert outside.read_text() == '{"sentences": {}}'
    assert not (papers.parent / 'verification_log.jsonl').exists()
    assert (directory / 'audit_log.jsonl').read_text() == '{"id":"dummy","meta":{}}\n'


def test_writer_lexical_destination_and_explicit_cli_source_contract(artifacts, tmp_path):
    _, papers, _, _, _, state = artifacts
    a, b = seed(papers), seed(papers, 'paper_b')
    sid = 'sentence:paper_a:abstract:12345678'
    (a / 'claims_review.json').write_text(json.dumps({'sentences': [{'id': sid}]}))
    original = (b / 'prose_state.json').read_text()
    (a / 'prose_state.json').unlink()
    (a / 'prose_state.json').symlink_to(b / 'prose_state.json')
    assert state.cmd_mark(argparse.Namespace(sentence_id=sid, state='verified', actor='user:test', notes='')) == 0
    # Atomic replacement applies at the lexical destination, leaving linked paper unchanged.
    assert not (a / 'prose_state.json').is_symlink()
    assert (b / 'prose_state.json').read_text() == original
    assert state.prose_state_path('paper_a') == a / 'prose_state.json'
    # Explicit source validation is intentionally independent of paper-derived read paths.
    from scripts.test_helpers import make_v2_review, make_v2_sentence
    source = tmp_path / 'supplied_claims_review.json'
    sentence = make_v2_sentence('paper_a', quote='Dummy explicit source')
    source.write_text(json.dumps(make_v2_review('paper_a', [sentence])))
    assert state.cmd_validate(argparse.Namespace(path=str(source))) == 0


@pytest.mark.parametrize('text', ['', 'plain dummy prose without abstract'])
def test_readable_empty_and_normal_text_remain_measured(artifacts, text):
    _, papers, _, _, readiness, _ = artifacts
    directory = seed(papers)
    (directory / 'paper_draft.tex').write_text(text)
    paper = {'id': 'paper:paper_a', 'type': 'Paper', 'meta': {}}
    idx = readiness.GraphIndex({'nodes': [paper], 'links': []})
    result = readiness._eval_narrative_grounding(paper, idx)
    assert result.measured is True and result.state == 'passed'


def test_readiness_unsafe_tex_retains_unmeasured_propagation(artifacts, tmp_path):
    _, papers, _, _, readiness, _ = artifacts
    directory = seed(papers)
    outside = tmp_path / 'sentinel'; outside.write_text('')
    tex = directory / 'paper_draft.tex'; tex.unlink(); tex.symlink_to(outside)
    paper = {'id': 'paper:paper_a', 'type': 'Paper', 'meta': {}}
    graph = {'nodes': [paper], 'links': []}
    idx = readiness.GraphIndex(graph)
    # These actual evaluators reach paper_tex with this graph, so refusal is
    # observed in their verdicts instead of asserted only on the resolver.
    for evaluator in (readiness._eval_citation_integrity, readiness._eval_parameter_provenance,
                      readiness._eval_assumption_disclosure, readiness._eval_narrative_grounding,
                      readiness._eval_numerical_freshness):
        result = evaluator(paper, idx)
        assert result.measured is False and 'UNMEASURED' in result.notes
