#!/usr/bin/env python3
"""
bundle_clusters.py — Phase 6i Wave 7.1 cross-bundle cluster detection
=====================================================================

Augments `papers/claim_clusters.json` with a `cross_bundle: bool` flag
per cluster, computed by projecting each cluster's `member_papers` list
through the per-paper bundle assignment table parsed from
`docs/PAPER_DRAFT_MAPPING.md`.

A cluster is `cross_bundle: true` iff its members span ≥2 distinct
bundle codes (e.g., a sentence that lives in both `L1` and `D3 §6` is
NOT cross-bundle by itself — it's the same content lifting to both
targets — but a cluster containing one sentence from a paper destined
for `L1` and one from a paper destined for `D2` IS cross-bundle).

Architecture
------------
This script is a *projection* layer that operates on the canonical
`claim_clusters.json` (built by `cluster_detect.py`) and the canonical
`PAPER_DRAFT_MAPPING.md` (manually curated). It does NOT mutate
prose_state.json files; it writes a `cluster_bundle_index.json`
sidecar that tags each cluster with its bundle distribution.

This is the Wave 7.3 dependency: `validate.py --check
bundle_consistency` walks `cluster_bundle_index.json` and flags any
cluster whose members carry inconsistent values across bundles.

Usage
-----
    uv run python scripts/bundle_clusters.py             # rebuild index
    uv run python scripts/bundle_clusters.py --report    # print summary
    uv run python scripts/bundle_clusters.py --json      # JSON output
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent
PAPERS_DIR = PROJECT_ROOT / "papers"
CLUSTERS_PATH = PAPERS_DIR / "claim_clusters.json"
INDEX_PATH = PAPERS_DIR / "cluster_bundle_index.json"

sys.path.insert(0, str(PROJECT_ROOT / "scripts"))
from bundle_migration import parse_mapping, MAPPING_DOC


def build_index() -> dict:
    """Load claim_clusters.json + PAPER_DRAFT_MAPPING.md and emit a
    cluster_bundle_index.json record listing per cluster:
      - cluster id
      - member_papers (passthrough)
      - bundle_destinations: union of bundle codes across members
      - cross_bundle: bool (True if ≥2 distinct codes)
      - representative_section_hint per bundle (from the mapping)
    """
    if not CLUSTERS_PATH.exists():
        raise FileNotFoundError(f"missing {CLUSTERS_PATH}")
    if not MAPPING_DOC.exists():
        raise FileNotFoundError(f"missing {MAPPING_DOC}")

    clusters_data = json.loads(CLUSTERS_PATH.read_text())
    mapping_text = MAPPING_DOC.read_text(encoding="utf-8")
    assignments = parse_mapping(mapping_text)

    index_clusters = []
    for c in clusters_data.get("clusters", []):
        bundles_seen: set[str] = set()
        per_paper_bundles: dict[str, list[str]] = {}
        for paper in c.get("member_papers", []):
            a = assignments.get(paper)
            if not a:
                # Paper not in mapping — leave empty bundle list
                per_paper_bundles[paper] = []
                continue
            paper_bundles = list(a["bundle_destinations"])
            per_paper_bundles[paper] = paper_bundles
            bundles_seen.update(paper_bundles)

        # Drop the universal flagship 'F' from the cross-bundle test
        # since every paper lifts into the flagship — using F to mark
        # cross-bundle would make every cluster cross-bundle.
        bundles_for_cross = bundles_seen - {"F"}
        cross_bundle = len(bundles_for_cross) >= 2

        index_clusters.append({
            "id": c.get("id"),
            "label": c.get("label"),
            "match_kind": c.get("match_kind"),
            "member_papers": c.get("member_papers"),
            "members": c.get("members"),
            "per_paper_bundles": per_paper_bundles,
            "bundle_destinations": sorted(bundles_seen),
            "bundle_destinations_excluding_flagship":
                sorted(bundles_for_cross),
            "cross_bundle": cross_bundle,
        })

    return {
        "schema_version": 1,
        "generated_by": "scripts/bundle_clusters.py",
        "source_clusters": str(CLUSTERS_PATH.relative_to(PROJECT_ROOT)),
        "source_mapping": str(MAPPING_DOC.relative_to(PROJECT_ROOT)),
        "cluster_count": len(index_clusters),
        "cross_bundle_count": sum(
            1 for c in index_clusters if c["cross_bundle"]
        ),
        "clusters": index_clusters,
    }


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Phase 6i Wave 7.1 cross-bundle cluster index"
    )
    parser.add_argument(
        "--report", action="store_true",
        help="print summary + cross-bundle clusters",
    )
    parser.add_argument(
        "--json", action="store_true",
        help="emit full index JSON to stdout",
    )
    args = parser.parse_args()

    index = build_index()

    if args.json:
        print(json.dumps(index, indent=2))
        return 0

    INDEX_PATH.write_text(json.dumps(index, indent=2))
    print(f"Cluster bundle index written to {INDEX_PATH.relative_to(PROJECT_ROOT)}")
    print(f"  {index['cluster_count']} clusters indexed")
    print(f"  {index['cross_bundle_count']} cross-bundle clusters")
    if args.report and index["cross_bundle_count"] > 0:
        print()
        print("Cross-bundle clusters:")
        for c in index["clusters"]:
            if not c["cross_bundle"]:
                continue
            bundles = ",".join(c["bundle_destinations_excluding_flagship"])
            print(f"  - {c['id']}: {bundles}")
            print(f"    label: {c.get('label', '')[:80]}")
            print(f"    member_papers: {c['member_papers']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
