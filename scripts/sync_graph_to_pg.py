#!/usr/bin/env python3
"""Sync the provenance graph to PostgreSQL + Apache AGE (Phase 5v Wave 9f).

Standalone, idempotent. Builds the JSON graph via build_graph.build_graph_json(),
then writes all nodes + edges to the ``sk_eft`` graph in AGE. Includes
``USES`` edges (Phase 5v Wave 9c/9e proof-dep edges) when the
``SK_EFT_INCLUDE_USES=1`` environment variable is set.

**Type-agnostic by design.** Node and edge type labels are derived from the
graph contents at sync time (see ``build_graph._create_age_labels``); new
types added to ``SHAPE_MAP`` / emitted by extractors automatically flow
through without code changes here. Phase 5v Wave 10b added ``Sentence``,
``AuditEvent``, ``ClaimCluster`` nodes + ``BACKED_BY``, ``LOGGED_BY``,
``MEMBER_OF`` edges — no update needed in this file.

**Why standalone, not a dashboard hook?** Per Wave 9a fix, HTTP endpoints
must never block on DB connectivity. Sync is a deliberate, user-controlled
action (cron, post-extraction hook, or just ``uv run python
scripts/sync_graph_to_pg.py`` when you want the live dashboard to see
your latest work). The dashboard continues to serve from its in-memory
cache; PG is the durable / Cypher-queryable backing store.

Usage
-----
    # Standard sync (USES off — fast, smaller AGE footprint)
    uv run python scripts/sync_graph_to_pg.py

    # Full sync including proof-dep USES edges (slower, bigger graph)
    SK_EFT_INCLUDE_USES=1 uv run python scripts/sync_graph_to_pg.py

    # Dry-run — compute the graph, print summary, don't touch PG
    uv run python scripts/sync_graph_to_pg.py --dry-run

Prints a summary: nodes/edges by type, sync duration, whether AGE was
reachable. Exit 0 on success, non-zero on connection failure.
"""

from __future__ import annotations

import argparse
import logging
import os
import sys
import time
from collections import Counter
from pathlib import Path

logging.basicConfig(level=logging.INFO, format='%(asctime)s %(levelname)s %(message)s')
logger = logging.getLogger('sync_graph_to_pg')

SCRIPT_DIR = Path(__file__).resolve().parent
PROJECT_ROOT = SCRIPT_DIR.parent
sys.path.insert(0, str(PROJECT_ROOT))
sys.path.insert(0, str(SCRIPT_DIR))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dry-run', action='store_true',
                        help='Build graph, print summary, skip PG write.')
    parser.add_argument('--pretty', action='store_true',
                        help='Include per-type node/edge breakdown in summary.')
    args = parser.parse_args()

    # Suppress the dashboard's lake-refresh suppression here — this CLI
    # script is the canonical way to refresh. If lean_deps is stale the
    # user will explicitly run scripts/extract_lean_deps.py first; we
    # just fail loudly if the data isn't fresh enough.
    from build_graph import build_graph_json, write_graph_to_pg

    include_uses = os.environ.get('SK_EFT_INCLUDE_USES', '').strip().lower() in (
        '1', 'true', 'yes', 'on'
    )

    logger.info("Building graph (sync_pg=False)…")
    t0 = time.monotonic()
    graph = build_graph_json(sync_pg=False)
    t_build = time.monotonic() - t0
    meta = graph['meta']
    logger.info(
        "Graph built in %.2fs — %d nodes, %d edges (USES edges: %s)",
        t_build, meta['node_count'], meta['edge_count'],
        'ON' if include_uses else 'off (set SK_EFT_INCLUDE_USES=1 to include)',
    )

    if args.pretty:
        node_counter = Counter(n['type'] for n in graph['nodes'])
        edge_counter = Counter(e['type'] for e in graph['links'])
        logger.info("Node types:")
        for t, c in sorted(node_counter.items(), key=lambda x: -x[1]):
            logger.info("  %-25s %d", t, c)
        logger.info("Edge types:")
        for t, c in sorted(edge_counter.items(), key=lambda x: -x[1]):
            logger.info("  %-25s %d", t, c)

    if args.dry_run:
        logger.info("--dry-run: skipping PG write.")
        return 0

    logger.info("Writing to PostgreSQL + AGE (sk_eft graph)…")
    t1 = time.monotonic()
    try:
        write_graph_to_pg(graph)
    except Exception as exc:
        logger.error("PG+AGE write failed: %s", exc)
        return 2
    t_write = time.monotonic() - t1
    logger.info("PG+AGE write complete in %.2fs.", t_write)

    # Verify the write landed
    try:
        import psycopg  # type: ignore
        with psycopg.connect(
            "host=localhost port=5433 dbname=sk_eft_provenance "
            "user=sk_eft password=sk_eft_local"
        ) as conn, conn.cursor() as cur:
            cur.execute("LOAD 'age'")
            cur.execute("SET search_path = ag_catalog, '$user', public")
            cur.execute("""
                SELECT * FROM cypher('sk_eft', $$
                    MATCH (n) RETURN count(n)
                $$) AS (c agtype)
            """)
            n_vertices = int(str(cur.fetchone()[0]))
            cur.execute("""
                SELECT * FROM cypher('sk_eft', $$
                    MATCH ()-[r]->() RETURN count(r)
                $$) AS (c agtype)
            """)
            n_edges = int(str(cur.fetchone()[0]))
        logger.info(
            "Verified in PG: %d vertices, %d edges (graph had %d/%d).",
            n_vertices, n_edges, meta['node_count'], meta['edge_count'],
        )
        # Non-fatal if counts mismatch (DETACH DELETE might race with concurrent
        # writers); but log it so divergence is visible.
        if n_vertices != meta['node_count']:
            logger.warning(
                "Vertex count mismatch: PG=%d vs graph=%d",
                n_vertices, meta['node_count'],
            )
        if n_edges != meta['edge_count']:
            logger.warning(
                "Edge count mismatch: PG=%d vs graph=%d",
                n_edges, meta['edge_count'],
            )
    except ImportError:
        logger.warning("psycopg not available — skipping PG verification.")
    except Exception as exc:
        logger.warning("PG verification query failed: %s", exc)

    total = time.monotonic() - t0
    logger.info("All done in %.2fs.", total)
    return 0


if __name__ == '__main__':
    sys.exit(main())
