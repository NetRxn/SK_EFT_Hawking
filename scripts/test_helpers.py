"""
test_helpers.py — isolated-state context managers for Wave 10 modules.
====================================================================

Pre-Wave 10 smoke tests poked the real ``papers/`` tree and hand-rolled
restoration on cleanup. That worked but was fragile (the paper16
``claims_review.json`` leak in the cluster smoke test, caught only by a
KeyError downstream, was the canonical failure).

These helpers provide deterministic, opt-in path swaps for the three
sole-writer modules — ``sentence_state``, ``verification_state``,
``cluster_detect`` — so smoke tests and pytest fixtures can run against
isolated tmp dirs without touching the real repo state.

Usage (pytest fixture):

    @pytest.fixture
    def isolated_papers(tmp_path):
        with isolated_papers_root(tmp_path / 'papers'):
            yield tmp_path / 'papers'

    def test_my_thing(isolated_papers):
        ...  # sentence_state, build_graph, etc. all see tmp_path

Usage (inline smoke):

    with isolated_papers_root() as papers_dir:
        ...

The context manager swaps module-level ``PAPERS_ROOT`` / ``LOG_PATH``
references and restores on exit. Safe under exception (try/finally).
"""

from __future__ import annotations

import contextlib
import importlib
import shutil
import tempfile
from pathlib import Path
from typing import Iterator


@contextlib.contextmanager
def isolated_papers_root(
    papers_root: Path | None = None,
    *,
    seed_from: dict[str, dict] | None = None,
) -> Iterator[Path]:
    """Swap ``sentence_state.PAPERS_ROOT`` to a tmp dir for the duration.

    ``papers_root`` — explicit dir to use. If None, mkdtemp() is used and
    the dir is removed on exit.

    ``seed_from`` — optional ``{paper_id: claims_review_dict}`` to write
    initial v2 ``claims_review.json`` files into the isolated tree.
    Useful for smoke tests that need ≥1 paper to exist.
    """
    sentence_state = importlib.import_module('sentence_state')

    cleanup_dir = False
    if papers_root is None:
        papers_root = Path(tempfile.mkdtemp(prefix='sk_eft_papers_'))
        cleanup_dir = True
    else:
        papers_root.mkdir(parents=True, exist_ok=True)

    # Swap module-level PAPERS_ROOT (sentence_state derives all per-paper
    # paths from it, so flipping this is sufficient).
    original = sentence_state.PAPERS_ROOT
    sentence_state.PAPERS_ROOT = papers_root

    # Seed papers if requested
    if seed_from:
        import json
        for paper_id, cr in seed_from.items():
            pd = papers_root / paper_id
            pd.mkdir(parents=True, exist_ok=True)
            (pd / 'claims_review.json').write_text(
                json.dumps(cr, indent=2, sort_keys=True),
            )
            (pd / 'paper_draft.tex').write_text(
                r'\title{' + paper_id + r'}\begin{document}\end{document}'
            )

    try:
        yield papers_root
    finally:
        sentence_state.PAPERS_ROOT = original
        if cleanup_dir:
            shutil.rmtree(papers_root, ignore_errors=True)


@contextlib.contextmanager
def isolated_verification_log(
    log_path: Path | None = None,
) -> Iterator[Path]:
    """Swap ``verification_state.LOG_PATH`` to a tmp file for the duration.

    Tests that fire change-bus events should wrap inside this so events
    don't bleed into the real log. Returns the log_path so tests can
    inspect / pre-populate it.
    """
    verification_state = importlib.import_module('verification_state')

    cleanup_dir = False
    if log_path is None:
        d = Path(tempfile.mkdtemp(prefix='sk_eft_vlog_'))
        log_path = d / 'verification_log.jsonl'
        cleanup_dir = True
    else:
        log_path.parent.mkdir(parents=True, exist_ok=True)

    orig_log = verification_state.LOG_PATH
    orig_lock = verification_state.LOCK_PATH
    verification_state.LOG_PATH = log_path
    verification_state.LOCK_PATH = log_path.parent / (log_path.name + '.lock')

    try:
        yield log_path
    finally:
        verification_state.LOG_PATH = orig_log
        verification_state.LOCK_PATH = orig_lock
        if cleanup_dir:
            shutil.rmtree(log_path.parent, ignore_errors=True)


@contextlib.contextmanager
def isolated_v2_state(
    *,
    seed_papers: dict[str, dict] | None = None,
) -> Iterator[tuple[Path, Path]]:
    """Combined fixture: isolated papers/ + isolated verification log.

    Yields ``(papers_root, verification_log_path)``. The most ergonomic
    surface for tests covering Wave 10b/c/d/f flows together.
    """
    with isolated_papers_root(seed_from=seed_papers) as papers_root:
        with isolated_verification_log() as log_path:
            yield (papers_root, log_path)


# ── Helpers for synthetic v2 sentences ─────────────────────────────────────

def make_v2_sentence(
    paper: str,
    *,
    section: str = 'abstract',
    quote: str,
    sentence_type: str = 'formal-claim',
    finding_classes: list[str] | None = None,
    chain_links: list[dict] | None = None,
    agent_verdict: str = 'PASS',
    agent_run_id: str = 'claims-reviewer-v2:smoke',
    section_ordinal: int = 1,
    tex_line: int = 1,
) -> dict:
    """Build a single v2-schema sentence dict from minimal inputs.

    Computes the content-hash sentence ID via sentence_state primitives,
    matching the agent's emission. Smoke tests can build paper fixtures
    with one call per sentence.
    """
    sentence_state = importlib.import_module('sentence_state')
    sid, normalized, h = sentence_state.compute_sentence_id(paper, section, quote)
    return {
        'id': sid,
        'raw_id_parts': {
            'paper': paper, 'section_slug': sentence_state.slugify(section),
            'quote_hash': h, 'hash_algorithm': 'sha256_first_8',
        },
        'section': section, 'section_ordinal': section_ordinal,
        'tex_line_start': tex_line, 'tex_line_end': tex_line,
        'quote': quote, 'quote_normalized': normalized,
        'type': sentence_type,
        'finding_classes': finding_classes or [],
        'chain_proposed': {'links': chain_links or [], 'completeness': 'full'},
        'agent_verdict': agent_verdict,
        'agent_run_id': agent_run_id,
        'tombstone': False,
    }


def make_v2_review(
    paper: str,
    sentences: list[dict],
    *,
    review_date: str = '2026-04-26T00:00:00Z',
    blocking_issues: list[str] | None = None,
) -> dict:
    """Wrap sentences into a complete v2 claims_review.json payload."""
    return {
        'paper': paper,
        'review_date': review_date,
        'reviewer_version': 'claims-reviewer-v2',
        'reviewer_model': 'claude-opus-4-7-1m',
        'reviewer_run_id': 'claims-reviewer-v2:smoke',
        'sentences': sentences,
        'non_reproducing_prior_findings': [],
        'summary': '',
        'blocking_issues': blocking_issues or [],
        'non_blocking_followups': [],
    }
