"""Source mtime selection is independent of checkout ancestors."""
from __future__ import annotations

from datetime import datetime, timezone
import os
from pathlib import Path
import sys

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import bundle_source_manifest as manifest
import check_bundle_source_freshness as freshness

# A fractional timestamp pins both existing interfaces, including subsecond freshness.
STAMP = 1_700_000_000.25
UTC = datetime.fromtimestamp(STAMP, timezone.utc)


def put(path: Path, stamp: float = STAMP) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text('source\n')
    os.utime(path, (stamp, stamp))
    return path


@pytest.fixture(params=['checkout', '.checkout'])
def papers(request, tmp_path, monkeypatch):
    path = tmp_path / request.param / 'papers'
    path.mkdir(parents=True)
    monkeypatch.setattr(manifest, 'PAPERS_DIR', path)
    monkeypatch.setattr(freshness, 'PAPERS_DIR', path)
    return path


def assert_timestamp(source: str = 'source') -> None:
    assert manifest._last_source_modification(source) == '2023-11-14T22:13:20Z'
    assert freshness._latest_source_mtime(source) == UTC


def test_visible_and_hidden_checkout_ancestors_measure_nested_sources(papers):
    put(papers / 'source' / 'draft.tex', STAMP - 10)
    put(papers / 'source' / 'sections' / 'result.tex')
    assert_timestamp()


@pytest.mark.parametrize('excluded', [
    '.draft.tex', '.cache/recent.tex', 'sections/.draft/recent.tex',
    '__pycache__/recent.pyc', 'sections/__pycache__/recent.pyc',
])
def test_newer_hidden_and_cache_descendants_are_excluded(papers, excluded):
    put(papers / 'source' / 'draft.tex')
    put(papers / 'source' / excluded, STAMP + 100)
    assert_timestamp()


@pytest.mark.parametrize('state', ['missing', 'empty', 'excluded', 'zero', 'negative'])
def test_no_positive_eligible_mtime_remains_unmeasurable(papers, state):
    source = papers / 'source'
    if state != 'missing':
        source.mkdir()
    if state == 'excluded':
        put(source / 'nested' / '.cache' / 'draft.tex')
    elif state in {'zero', 'negative'}:
        put(source / 'draft.tex', 0 if state == 'zero' else -1)
    assert manifest._last_source_modification('source') is None
    assert freshness._latest_source_mtime('source') is None


@pytest.mark.parametrize('bookkeeping', ['bundle_metadata.json', 'append_log.json'])
def test_reader_specific_bookkeeping_exclusions_are_preserved(papers, bookkeeping):
    put(papers / 'source' / 'draft.tex', STAMP - 100)
    put(papers / 'source' / bookkeeping)
    # The manifest includes ordinary filenames; freshness excludes these two.
    assert manifest._last_source_modification('source') == '2023-11-14T22:13:20Z'
    assert freshness._latest_source_mtime('source') == datetime.fromtimestamp(
        STAMP - 100, timezone.utc)


def test_real_writer_renders_source_timestamp_without_metadata_writes(papers):
    put(papers / 'source' / 'draft.tex')
    (papers / 'E1').mkdir()
    metadata = papers / 'E1' / 'bundle_metadata.json'
    metadata.write_text('{"freshness_stale":true,"last_lift":"unchanged"}\n')
    before = metadata.read_bytes()
    output = manifest.write_source_manifest('E1', ['source'], {})
    assert '| `source` | (see mapping) | (unspecified) | (see mapping) | 2023-11-14T22:13:20Z |' in output.read_text()
    assert metadata.read_bytes() == before


def test_architecture_source_path_claim_matches_both_readers(papers):
    text = (ROOT / 'docs/architecture/QA_QI_INFRASTRUCTURE_MAP.md').read_text()
    claim = ('Both source-mtime readers filter hidden components and `__pycache__` '
             'relative to the selected source-paper directory, so checkout ancestors '
             'do not affect file eligibility.')
    assert claim in ' '.join(text.split())
    put(papers / 'source' / 'sections' / 'draft.tex')
    put(papers / 'source' / 'sections' / '.hidden' / 'draft.tex', STAMP + 100)
    assert_timestamp()


def test_freshness_check_reports_source_stale_beneath_either_ancestor(papers, monkeypatch, tmp_path):
    import bundle_migration
    import sentence_state
    import json

    put(papers / 'source' / 'draft.tex')
    bundle = papers / 'E1'
    bundle.mkdir()
    metadata = bundle / 'bundle_metadata.json'
    metadata.write_text(json.dumps({'last_lift': '2023-01-01T00:00:00Z',
                                    'freshness_stale': True}))
    before = metadata.read_bytes()
    mapping = tmp_path / 'mapping.md'
    mapping.write_text('parsed by controlled assignment below')
    monkeypatch.setattr(freshness, 'MAPPING_DOC', mapping)
    monkeypatch.setattr(bundle_migration, 'parse_mapping',
                        lambda text: {'source': {'bundle_destinations': ['E1']}})
    monkeypatch.setattr(sentence_state, '_VALID_BUNDLE_TARGETS', {'E1'})
    # Isolate the source reader; no Lean extraction/build is invoked.
    monkeypatch.setattr(freshness, '_git_last_commit_times', lambda: None)
    monkeypatch.setattr(freshness, '_lean_module_index', lambda: {})
    monkeypatch.setattr(freshness, '_dirty_lean_paths', lambda: set())
    monkeypatch.setattr(freshness, '_derived_lean_modules', lambda: None)
    findings = freshness.check(write_metadata=False)
    assert any(f['bundle'] == 'E1' and f['message'].startswith('freshness-stale')
               for f in findings)
    assert metadata.read_bytes() == before
