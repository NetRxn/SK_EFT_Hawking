#!/usr/bin/env python3
"""
last_modified.py — freshness propagation for graph nodes (Phase 5v Wave 10b)
============================================================================

Computes `last_modified` timestamp for every graph node via a one-pass
dependency walk. The timestamp is the MAX of:

  1. Direct timestamp: file mtime, human_verified_date, cache hash change time,
     explicit meta.last_modified, else epoch_zero.
  2. Upstream: for each incoming dependency edge (edge.source → edge.target),
     the source's last_modified bubbles up.

This powers the Wave 10c cross-tab change-bus: when any artifact's
`last_modified` advances (parameter ratified, Lean file changed, citation
refreshed, etc.), all dependent Sentence nodes flip to `needs_recheck` if
their `human_ratified_at` predates the new `last_modified`.

Usage
-----
  # Compute last_modified on an already-built graph dict:
  from scripts.last_modified import annotate_last_modified
  graph = build_graph_json()
  annotate_last_modified(graph)   # mutates nodes in place

  # Check staleness of a single sentence:
  from scripts.last_modified import sentence_is_stale
  stale = sentence_is_stale(sentence_node, backed_by_edges, id_to_node)

Design: sentence_kg_schema_delta.md §6.
"""

from __future__ import annotations

from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable

EPOCH_ZERO = datetime(1970, 1, 1, tzinfo=timezone.utc).isoformat().replace('+00:00', 'Z')


# Edge types whose source's last_modified propagates to their target.
# Design sentence_kg_schema_delta.md §6.2
PROPAGATION_EDGE_TYPES: set[str] = {
    'USED_BY',             # Parameter → Formula: parameter changes → formula affected
    'VERIFIED_BY',         # Formula → LeanTheorem: theorem changes → formula affected
    'DEPENDS_ON_AXIOM',    # LeanTheorem → LeanAxiom: axiom changes → theorem affected
    'ASSUMES',             # LeanTheorem → Hypothesis: hypothesis changes → theorem affected
    'IMPORTS',             # Formula → Formula: imported changes → importing affected
    'CITES',               # Formula → PrimarySource
    'CITES_SOURCE',        # Paper → PrimarySource
    'GROUNDED_IN',         # ProseClaim/Sentence → Formula
    'BACKED_BY',           # Sentence → any artifact (the Wave 10b addition)
    'VERIFIES',            # PythonTest → Formula
}


def _parse_iso(ts: str | None) -> str:
    """Normalize an ISO timestamp (or None) to a Zulu-suffix form, defaulting to epoch_zero."""
    if not ts:
        return EPOCH_ZERO
    # Normalize various inputs to a sortable form
    t = str(ts)
    if t.endswith('+00:00'):
        t = t[:-6] + 'Z'
    return t


def _direct_last_modified(node: dict) -> str:
    """Compute the node's own direct last_modified timestamp (no upstream).

    Note: ``meta.last_modified`` is intentionally excluded — it is the
    OUTPUT of ``annotate_last_modified``, not an input. Including it
    would make the function non-idempotent (subsequent runs would
    short-circuit upstream propagation by reading their own prior
    output). Use ``last_modified_explicit`` for caller-provided
    timestamps that should win over file mtimes etc.
    """
    meta = node.get('meta', {}) or {}

    # Priority: explicit > file_mtime > human verification > cache hash > epoch
    for key in (
        'last_modified_explicit',
        'file_mtime',
        'human_verified_date',
        'human_ratified_at',
        'cache_hash_changed_at',
    ):
        v = meta.get(key)
        if v:
            return _parse_iso(v)
    return EPOCH_ZERO


def annotate_last_modified(graph: dict) -> None:
    """Compute + stamp `meta.last_modified` on every node in the graph.

    Mutates the graph dict in place. Safe to call multiple times (idempotent:
    subsequent runs produce the same values from the same inputs).

    The graph dict must have:
      graph['nodes'] — list of node dicts with id, type, meta
      graph['links'] — list of edge dicts with source, target, type
        (D3 convention; matches ``build_graph_json``'s output).
    """
    nodes: list[dict] = graph.get('nodes', [])
    edges: list[dict] = graph.get('links', [])

    id_to_node = {n['id']: n for n in nodes}

    # Build incoming-propagation adjacency: target_id -> list of source_ids
    # Only include edges whose type is in PROPAGATION_EDGE_TYPES
    incoming: dict[str, list[str]] = defaultdict(list)
    for e in edges:
        if e.get('type') not in PROPAGATION_EDGE_TYPES:
            continue
        src = e.get('source')
        tgt = e.get('target')
        if src and tgt and src in id_to_node and tgt in id_to_node:
            incoming[tgt].append(src)

    # Memoization with cycle guard (IN_PROGRESS sentinel).
    IN_PROGRESS = object()
    cache: dict[str, object] = {}

    def compute(node_id: str) -> str:
        cached = cache.get(node_id)
        if isinstance(cached, str):
            return cached
        if cached is IN_PROGRESS:
            # cycle — fall back to direct only
            n = id_to_node.get(node_id)
            return _direct_last_modified(n) if n else EPOCH_ZERO

        cache[node_id] = IN_PROGRESS
        node = id_to_node.get(node_id)
        if node is None:
            cache[node_id] = EPOCH_ZERO
            return EPOCH_ZERO

        direct = _direct_last_modified(node)
        # Walk upstream
        upstream_best = EPOCH_ZERO
        for src_id in incoming.get(node_id, []):
            src_last = compute(src_id)
            if src_last > upstream_best:
                upstream_best = src_last
        combined = max(direct, upstream_best)
        cache[node_id] = combined
        return combined

    # Compute for every node
    for n in nodes:
        n.setdefault('meta', {})
        n['meta']['last_modified'] = compute(n['id'])


def sentence_is_stale(
    sentence_node: dict,
    backed_by_edges: Iterable[dict],
    id_to_node: dict[str, dict],
) -> bool:
    """Return True iff the sentence's human_ratified_at predates any of its
    chain-link targets' last_modified timestamps.

    A tombstoned sentence is never 'stale' in this sense — the prose is gone.
    An unratified sentence is never 'stale' — there's nothing to re-check.
    """
    meta = sentence_node.get('meta', {}) or {}
    if meta.get('tombstone'):
        return False
    ratified = meta.get('human_ratified_at')
    if not ratified:
        return False
    ratified_iso = _parse_iso(ratified)

    for e in backed_by_edges:
        if e.get('type') != 'BACKED_BY':
            continue
        tgt = id_to_node.get(e.get('target', ''))
        if not tgt:
            continue
        tgt_lm = tgt.get('meta', {}).get('last_modified') or EPOCH_ZERO
        if tgt_lm > ratified_iso:
            return True
    return False


def compute_link_state(
    edge: dict,
    target_node: dict | None,
    agent_run_at_iso: str | None = None,
) -> str:
    """Derive the per-link freshness state (schema delta §3.3).

    Values: resolved | llm_verified_only | human_verified | stale | missing_target
    """
    if target_node is None:
        return 'missing_target'

    meta_edge = edge.get('meta', {}) or {}
    meta_tgt = target_node.get('meta', {}) or {}
    kind = meta_edge.get('link_kind')

    if kind == 'parameter':
        if meta_tgt.get('human_verified_date'):
            return 'human_verified'
        if meta_tgt.get('llm_verified_date'):
            return 'llm_verified_only'
        return 'unverified'

    if kind in ('theorem', 'axiom', 'formula'):
        file_mtime = meta_tgt.get('file_mtime')
        if file_mtime and agent_run_at_iso:
            if _parse_iso(file_mtime) > _parse_iso(agent_run_at_iso):
                return 'stale'

    return 'resolved'


if __name__ == '__main__':
    # CLI smoke test: read a graph.json and print last_modified distribution
    import argparse
    import json
    import sys

    p = argparse.ArgumentParser(description='Annotate a graph.json with last_modified')
    p.add_argument('graph', help='Path to graph.json (from build_graph.py --json)')
    p.add_argument('--out', default=None, help='Write annotated output here')
    args = p.parse_args()

    with open(args.graph) as f:
        g = json.load(f)
    annotate_last_modified(g)

    # Summary
    from collections import Counter
    by_year = Counter()
    for n in g['nodes']:
        lm = n.get('meta', {}).get('last_modified', EPOCH_ZERO)
        year = lm[:4] if lm else 'n/a'
        by_year[year] += 1
    print(f"Nodes annotated: {len(g['nodes'])}", file=sys.stderr)
    print(f"By year:", dict(sorted(by_year.items())), file=sys.stderr)

    if args.out:
        with open(args.out, 'w') as f:
            json.dump(g, f, indent=2, sort_keys=True)
        print(f"Wrote {args.out}", file=sys.stderr)
    else:
        json.dump(g, sys.stdout, indent=2, sort_keys=True)
