#!/usr/bin/env python3
"""
cluster_detect.py — cross-paper ClaimCluster builder (Phase 5v Wave 10f)
========================================================================

Walks every ``papers/<paper>/claims_review.json`` v2 schema, groups
sentences making the same factual claim across papers, and writes
``papers/claim_clusters.json``. The Wave 10b ``build_graph`` extractors
(``extract_claim_cluster_nodes`` + ``extract_member_of_edges``) consume
that file to materialize ``ClaimCluster`` nodes + ``MEMBER_OF`` edges in
the knowledge graph.

Match strategies (cheap → expensive):
  1. **exact** — sentences share normalized-quote sha8. Confidence 1.0.
  2. **normalized** — same sha8 of further-normalized quote (strip leading
     citation hints, internal whitespace runs, more aggressive symbol
     unification). Confidence 0.9.
  3. **semantic** — Wave 10f-followup (needs an embedding model;
     deferred). Stub left in place.

Cross-paper requirement: a cluster must contain sentences from ≥2
distinct papers. Same-paper duplicates are intra-paper redundancy
(not a Gate 2 cross-paper consistency concern) and are skipped.

CLI:
  python scripts/cluster_detect.py
      [--out papers/claim_clusters.json]
      [--include-single-paper]   # debug: don't filter to ≥2 papers
      [--min-quote-len 30]       # skip very short sentences (transitions)
      [--strategy exact|normalized|all]
      [--dry-run]
"""

from __future__ import annotations

import argparse
import hashlib
import json
import logging
import re
import sys
import unicodedata
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterator

logger = logging.getLogger(__name__)

PROJECT_ROOT = Path(__file__).resolve().parent.parent
PAPERS_ROOT = PROJECT_ROOT / "papers"
DEFAULT_OUT = PAPERS_ROOT / "claim_clusters.json"

# ── Normalization (mirrors sentence_state.normalize_quote, more aggressive) ──

_LATEX_KEEP_ARG = re.compile(r'\\(?:texttt|emph|textbf|mathrm|text|textit|textsc)\{([^{}]*)\}')
_LATEX_DROP_ARG = re.compile(r'\\(?:cite|ref|label|footnote|autoref|eqref|nocite)\{[^{}]*\}')
_WS = re.compile(r'\s+')
_TRAILING_BRACKETS = re.compile(r'\s*\[[A-Za-z0-9 ,;.&\'-]+\]\s*\.?\s*$')
_PUNCT_TAIL = re.compile(r'[.,;:!?\s]+$')
_NON_ALNUM_SP = re.compile(r'[^a-z0-9\s]')


def normalize_basic(quote: str) -> str:
    """Same shape as sentence_state.normalize_quote — preserved so the
    sha8 produced here matches the per-paper agent's sha8 for exact-match
    cluster assembly."""
    q = quote.lower()
    prev = None
    while prev != q:
        prev = q
        q = _LATEX_KEEP_ARG.sub(lambda m: m.group(1), q)
    q = _LATEX_DROP_ARG.sub('', q)
    q = q.replace('“', '"').replace('”', '"')
    q = q.replace('‘', "'").replace('’', "'")
    q = q.replace('—', '--').replace('–', '-')
    q = q.replace('…', '...')
    q = q.replace(' ', ' ')
    q = _WS.sub(' ', q).strip()
    q = _TRAILING_BRACKETS.sub('', q).strip()
    return q


def normalize_aggressive(quote: str) -> str:
    """More aggressive normalization for ``match_kind=normalized`` — drops
    all punctuation, collapses runs of whitespace, NFKC unicode-folds.

    Two sentences that differ only in citation-style or hyphenation will
    collapse to the same hash.
    """
    q = normalize_basic(quote)
    q = unicodedata.normalize('NFKC', q)
    q = _NON_ALNUM_SP.sub(' ', q)
    q = _WS.sub(' ', q).strip()
    return q


def sha8(s: str) -> str:
    return hashlib.sha256(s.encode('utf-8')).hexdigest()[:8]


# ── Sentence iteration ─────────────────────────────────────────────────────

def iter_v2_paper_dirs() -> Iterator[tuple[str, Path]]:
    """Yield (paper_id, paper_dir) for every paper with a v2 claims_review."""
    if not PAPERS_ROOT.exists():
        return
    for p in sorted(PAPERS_ROOT.iterdir()):
        if not p.is_dir() or not p.name.startswith('paper'):
            continue
        cr = p / 'claims_review.json'
        if not cr.exists():
            continue
        try:
            data = json.loads(cr.read_text())
        except json.JSONDecodeError:
            logger.warning("Skipping %s — malformed JSON", cr)
            continue
        if not isinstance(data.get('sentences'), list):
            continue  # v1 schema
        yield (p.name, p)


def iter_sentences(min_quote_len: int = 0) -> Iterator[tuple[str, dict]]:
    """Yield (paper_id, sentence_dict) for every v2 sentence project-wide.

    Skips tombstoned sentences and (when ``min_quote_len > 0``) any
    quote shorter than the threshold (transitions, single-word stubs
    that would otherwise spuriously cluster).
    """
    for paper_id, paper_dir in iter_v2_paper_dirs():
        try:
            data = json.loads((paper_dir / 'claims_review.json').read_text())
        except json.JSONDecodeError:
            continue
        for s in data.get('sentences') or []:
            if s.get('tombstone'):
                continue
            if min_quote_len > 0 and len(s.get('quote', '')) < min_quote_len:
                continue
            if not s.get('id'):
                continue
            yield (paper_id, s)


# ── Cluster building ───────────────────────────────────────────────────────

def build_clusters_exact(
    sentences: list[tuple[str, dict]],
) -> list[dict]:
    """Group sentences by their existing sha8 (raw_id_parts.quote_hash).
    Confidence 1.0 — these passed through the same normalization pipeline.

    Falls back to recomputing the sha8 from scratch if a sentence record
    doesn't carry ``raw_id_parts.quote_hash`` (older agent runs).
    """
    by_hash: dict[str, list[tuple[str, dict]]] = defaultdict(list)
    for paper_id, s in sentences:
        h = (s.get('raw_id_parts') or {}).get('quote_hash')
        if not h:
            h = sha8(normalize_basic(s.get('quote', '')))
        by_hash[h].append((paper_id, s))

    clusters: list[dict] = []
    for h, members in by_hash.items():
        # Cross-paper requirement
        papers = {p for p, _ in members}
        if len(papers) < 2:
            continue
        sample_quote = members[0][1].get('quote', '')[:200]
        clusters.append({
            'id': f'claim_cluster:exact:{h}',
            'match_kind': 'exact',
            'confidence': 1.0,
            'label': sample_quote,
            'normalized_hash': h,
            'members': [s['id'] for _, s in members],
            'member_papers': sorted(papers),
        })
    return clusters


def build_clusters_normalized(
    sentences: list[tuple[str, dict]],
    *,
    skip_hashes: set[str],
) -> list[dict]:
    """Group sentences by aggressive normalization. Skips any normalized
    hash whose underlying members are already in an exact cluster (passed
    via ``skip_hashes``) — avoids double-counting.

    Confidence 0.9 — the basic and aggressive normalizers agree often
    enough to claim near-certain match without semantic embedding.
    """
    by_hash: dict[str, list[tuple[str, dict]]] = defaultdict(list)
    for paper_id, s in sentences:
        agg_h = sha8(normalize_aggressive(s.get('quote', '')))
        by_hash[agg_h].append((paper_id, s))

    clusters: list[dict] = []
    for h, members in by_hash.items():
        # Skip if every member's basic-hash is already in an exact cluster
        basic_hashes = {
            (s.get('raw_id_parts') or {}).get('quote_hash')
            or sha8(normalize_basic(s.get('quote', '')))
            for _, s in members
        }
        if basic_hashes.issubset(skip_hashes):
            # All members already covered; skip
            continue

        papers = {p for p, _ in members}
        if len(papers) < 2:
            continue

        sample_quote = members[0][1].get('quote', '')[:200]
        clusters.append({
            'id': f'claim_cluster:norm:{h}',
            'match_kind': 'normalized',
            'confidence': 0.9,
            'label': sample_quote,
            'normalized_hash': h,
            'members': [s['id'] for _, s in members],
            'member_papers': sorted(papers),
        })
    return clusters


# ── Output assembly ────────────────────────────────────────────────────────

def now_iso() -> str:
    return datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')


def assemble_record(clusters: list[dict], strategy: str) -> dict:
    return {
        'version': 1,
        'constructed_by': f'cluster_detect.py:{strategy}',
        'constructed_at': now_iso(),
        'cluster_count': len(clusters),
        'paper_coverage': sorted({
            p for c in clusters for p in c.get('member_papers', [])
        }),
        'clusters': [
            {
                **c,
                'constructed_by': f'cluster_detect.py:{c.get("match_kind", strategy)}',
                'constructed_at': now_iso(),
                'human_confirmed_at': None,
            }
            for c in clusters
        ],
    }


# ── CLI ────────────────────────────────────────────────────────────────────

def _build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog='cluster_detect.py',
        description='Build cross-paper ClaimCluster records from v2 claims_review files',
    )
    p.add_argument('--out', default=str(DEFAULT_OUT),
                   help=f'Output path (default: {DEFAULT_OUT})')
    p.add_argument('--strategy', default='all',
                   choices=['exact', 'normalized', 'all'],
                   help='Match strategy (default: all = exact + normalized)')
    p.add_argument('--include-single-paper', action='store_true',
                   help='Include intra-paper duplicates (debug only)')
    p.add_argument('--min-quote-len', type=int, default=30,
                   help='Skip sentences with quote shorter than this (default: 30)')
    p.add_argument('--dry-run', action='store_true',
                   help='Print summary, do not write')
    p.add_argument('--verbose', '-v', action='store_true')
    return p


def main(argv: list[str] | None = None) -> int:
    args = _build_parser().parse_args(argv)
    logging.basicConfig(level=logging.DEBUG if args.verbose else logging.INFO,
                        format='%(message)s')

    sentences = list(iter_sentences(min_quote_len=args.min_quote_len))
    logger.info("Indexed %d v2 sentences across papers", len(sentences))
    if not sentences:
        logger.info("No v2 papers found; emitting empty cluster file")

    clusters: list[dict] = []
    skip_hashes: set[str] = set()
    if args.strategy in ('exact', 'all'):
        exact = build_clusters_exact(sentences)
        logger.info("Exact-match clusters: %d", len(exact))
        clusters.extend(exact)
        # Track underlying basic-hashes for de-dup in normalized pass
        for c in exact:
            for sid in c['members']:
                # Sentence id encodes sha8 in last colon-segment
                skip_hashes.add(sid.rsplit(':', 1)[-1])

    if args.strategy in ('normalized', 'all'):
        normed = build_clusters_normalized(sentences, skip_hashes=skip_hashes)
        logger.info("Normalized-match clusters: %d", len(normed))
        clusters.extend(normed)

    record = assemble_record(clusters, strategy=args.strategy)

    out_path = Path(args.out).resolve()
    if args.dry_run:
        logger.info("(dry-run) would write %d clusters to %s",
                    len(clusters), out_path)
        sys.stdout.write(json.dumps(record, indent=2, sort_keys=True))
        sys.stdout.write('\n')
        return 0

    out_path.parent.mkdir(parents=True, exist_ok=True)
    with open(out_path, 'w', encoding='utf-8') as f:
        json.dump(record, f, indent=2, sort_keys=True)
        f.write('\n')
    logger.info("Wrote %d clusters across %d papers → %s",
                len(clusters), len(record['paper_coverage']), out_path)
    return 0


if __name__ == '__main__':
    sys.exit(main())
