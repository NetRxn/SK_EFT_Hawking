#!/usr/bin/env python3
"""SK-EFT Provenance Graph — Integrity Checker

Runs structural queries against the extracted graph to find:
- Orphan nodes (no edges)
- Broken provenance chains (claims without full grounding)
- Ungrounded claims (no GROUNDED_IN edge)
- Missing provenance (parameters without SOURCED_FROM edge)
- Verification conflicts

Usage:
    uv run python scripts/graph_integrity.py          # Print report
    uv run python scripts/graph_integrity.py --json   # JSON output
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import defaultdict
from pathlib import Path

# Path setup
SCRIPT_DIR = Path(__file__).resolve().parent
PROJECT_ROOT = SCRIPT_DIR.parent
sys.path.insert(0, str(PROJECT_ROOT))
sys.path.insert(0, str(SCRIPT_DIR))

from build_graph import extract_all_nodes, extract_all_edges


# ═══════════════════════════════════════════════════════════════════════
# Integrity checks
# ═══════════════════════════════════════════════════════════════════════

def run_integrity_checks() -> dict:
    """Build the provenance graph and run all integrity queries.

    Returns a dict with keys:
        orphan_nodes, conflicts, ungrounded_claims, broken_chains,
        missing_provenance, summary
    """
    nodes = extract_all_nodes()
    node_ids = {n['id'] for n in nodes}
    edges = extract_all_edges(node_ids)

    # Build lookup maps
    node_by_id = {n['id']: n for n in nodes}
    outgoing: dict[str, list[dict]] = defaultdict(list)   # node_id -> [edge, ...]
    incoming: dict[str, list[dict]] = defaultdict(list)    # node_id -> [edge, ...]
    for edge in edges:
        outgoing[edge['source']].append(edge)
        incoming[edge['target']].append(edge)

    # Connected node IDs (appear in any edge as source or target)
    connected = set()
    for edge in edges:
        connected.add(edge['source'])
        connected.add(edge['target'])

    # --- 1. Orphan nodes: zero edges (not source or target of anything) ---
    orphan_nodes = []
    for n in nodes:
        if n['id'] not in connected:
            orphan_nodes.append({
                'id': n['id'],
                'type': n['type'],
                'name': n['name'],
            })

    # --- 2. Conflicts: nodes with verification == 'conflict' ---
    conflicts = []
    for n in nodes:
        if n.get('verification') == 'conflict':
            conflicts.append({
                'id': n['id'],
                'type': n['type'],
                'name': n['name'],
                'detail': n.get('detail', ''),
            })

    # --- 3. Ungrounded claims: PaperClaim nodes without GROUNDED_IN edge ---
    ungrounded_claims = []
    for n in nodes:
        if n['type'] != 'PaperClaim':
            continue
        has_grounded = any(
            e['type'] == 'GROUNDED_IN' for e in outgoing.get(n['id'], [])
        )
        if not has_grounded:
            ungrounded_claims.append({
                'id': n['id'],
                'name': n['name'],
                'paper': n.get('meta', {}).get('paper', ''),
            })

    # --- 4. Broken provenance chains ---
    # Claims that have GROUNDED_IN -> Formula, but that Formula has no
    # VERIFIED_BY edge to a LeanTheorem
    broken_chains = []
    for n in nodes:
        if n['type'] != 'PaperClaim':
            continue
        grounded_edges = [
            e for e in outgoing.get(n['id'], [])
            if e['type'] == 'GROUNDED_IN'
        ]
        for ge in grounded_edges:
            formula_id = ge['target']
            formula_node = node_by_id.get(formula_id)
            if formula_node is None:
                continue
            has_verified_by = any(
                e['type'] == 'VERIFIED_BY' for e in outgoing.get(formula_id, [])
            )
            if not has_verified_by:
                broken_chains.append({
                    'claim': n['id'],
                    'formula': formula_id,
                    'issue': f"Formula {formula_node['name']} has no VERIFIED_BY edge to a LeanTheorem",
                })

    # --- 5. Missing provenance: Parameter nodes without SOURCED_FROM edge ---
    # Exclude PROJECTED tier parameters (they don't have experimental sources)
    missing_provenance = []
    for n in nodes:
        if n['type'] != 'Parameter':
            continue
        tier = n.get('meta', {}).get('tier', '')
        if tier == 'PROJECTED':
            continue
        has_sourced_from = any(
            e['type'] == 'SOURCED_FROM' for e in outgoing.get(n['id'], [])
        )
        if not has_sourced_from:
            missing_provenance.append({
                'id': n['id'],
                'name': n['name'],
                'tier': tier,
            })

    # --- Summary ---
    total_issues = (
        len(orphan_nodes) + len(conflicts) + len(ungrounded_claims)
        + len(broken_chains) + len(missing_provenance)
    )

    return {
        'orphan_nodes': orphan_nodes,
        'conflicts': conflicts,
        'ungrounded_claims': ungrounded_claims,
        'broken_chains': broken_chains,
        'missing_provenance': missing_provenance,
        'summary': {
            'total_nodes': len(nodes),
            'total_edges': len(edges),
            'total_issues': total_issues,
            'orphans': len(orphan_nodes),
            'conflicts': len(conflicts),
            'ungrounded': len(ungrounded_claims),
            'broken_chains': len(broken_chains),
            'missing_provenance': len(missing_provenance),
        },
    }


# ═══════════════════════════════════════════════════════════════════════
# CLI
# ═══════════════════════════════════════════════════════════════════════

def print_report(report: dict) -> None:
    """Print human-readable integrity report."""
    s = report['summary']
    print("SK-EFT Provenance Graph — Integrity Report")
    print(f"  Nodes: {s['total_nodes']}  Edges: {s['total_edges']}")
    print(f"  Total issues: {s['total_issues']}")
    print()

    if report['conflicts']:
        print(f"  CONFLICTS ({s['conflicts']}):")
        for c in report['conflicts']:
            print(f"    {c['id']}  — {c['detail'][:80]}")
        print()

    if report['orphan_nodes']:
        print(f"  ORPHAN NODES ({s['orphans']}):")
        for o in report['orphan_nodes']:
            print(f"    {o['id']}  ({o['type']})")
        print()

    if report['ungrounded_claims']:
        print(f"  UNGROUNDED CLAIMS ({s['ungrounded']}):")
        for u in report['ungrounded_claims']:
            print(f"    {u['id']}  paper={u['paper']}")
        print()

    if report['broken_chains']:
        print(f"  BROKEN CHAINS ({s['broken_chains']}):")
        for b in report['broken_chains']:
            print(f"    {b['claim']}  -> {b['formula']}  ({b['issue'][:60]})")
        print()

    if report['missing_provenance']:
        print(f"  MISSING PROVENANCE ({s['missing_provenance']}):")
        for m in report['missing_provenance']:
            print(f"    {m['id']}  tier={m['tier']}")
        print()

    if s['total_issues'] == 0:
        print("  All clear — no integrity issues found.")


def main():
    parser = argparse.ArgumentParser(
        description='SK-EFT Provenance Graph integrity checker.'
    )
    parser.add_argument('--json', action='store_true',
                        help='Output JSON instead of human-readable report')
    args = parser.parse_args()

    report = run_integrity_checks()

    if args.json:
        print(json.dumps(report, indent=2, default=str))
    else:
        print_report(report)

    # Exit with 1 if there are conflicts (hard failures)
    if report['summary']['conflicts'] > 0:
        sys.exit(1)


if __name__ == '__main__':
    main()
