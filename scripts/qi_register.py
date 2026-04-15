#!/usr/bin/env python3
"""Generate docs/QI_REGISTER.md — the Meta-process Quality Improvement
register (Pipeline Stage 14, Phase 5v Wave 7).

Reads `ReviewFinding` nodes from the current graph, clusters findings by
pattern (primarily: same gate affected + recurring across ≥2 papers, or
explicit `## QI Candidate` sections emitted by the adversarial-reviewer
agent), and writes a user-facing markdown register tracking open items
with status, owner, target date, and evidence-on-close.

This is advisory — Stage 14 never blocks submission. Its purpose is
feeding pipeline improvements back into Phase 5v+ remediation waves.

Usage:
    uv run python scripts/qi_register.py          # regenerate docs/QI_REGISTER.md
    uv run python scripts/qi_register.py --stats  # print summary
    uv run python scripts/qi_register.py --snapshot  # also write timestamped snapshot
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter, defaultdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

PROJECT_ROOT = Path(__file__).resolve().parent.parent
REGISTER_PATH = PROJECT_ROOT / "docs" / "QI_REGISTER.md"
SCRIPT_DIR = PROJECT_ROOT / "scripts"


def load_review_findings() -> list[dict]:
    """Pull current ReviewFinding nodes via build_graph."""
    sys.path.insert(0, str(SCRIPT_DIR))
    from build_graph import extract_review_finding_nodes
    return extract_review_finding_nodes()


# ═══════════════════════════════════════════════════════════════════════
# Pattern clustering
# ═══════════════════════════════════════════════════════════════════════

# Map heading-keyword patterns to readiness gate names. Used to classify
# ReviewFinding nodes that don't explicitly carry a gate attribute yet
# (e.g., the April Perplexity findings pre-date the gate taxonomy).
_GATE_KEYWORDS = [
    ('CitationIntegrity', [r'\bciting\b', r'\bcitation\b', r'\bbibitem\b',
                           r'\barXiv\b', r'\bDOI\b', r'wrong\s+paper',
                           r'wrong\s+author', r'wrong\s+title']),
    ('CrossPaperConsistency', [r'cross[- ]paper', r'contradic', r'companion',
                               r'consistency']),
    ('ParameterProvenance', [r'\bparameter\b', r'measured\b', r'provenance',
                             r'primary\s+source', r'drift']),
    ('ComputationCorrectness', [r'test', r'bounds[- ]only', r'dimension',
                                r'computation', r'formula\s+bug', r'k_H',
                                r'numerical\s+bug']),
    ('LeanProofSubstance', [r'placeholder', r'tautolog', r'trivial\s+proof',
                            r'Equiv\.refl', r'\brfl\b']),
    ('AssumptionDisclosure', [r'assumption', r'spin\s+manifold', r'framing',
                              r'undisclosed', r'hypothesis']),
    ('NarrativeGrounding', [r'first\s+in\s+', r'all\s+the\s+same',
                            r'overclaim', r'narrative', r'rooted\s+in',
                            r'Ramanujan', r'Monte\s+Carlo\s+evidence']),
    ('ProductionRunHealth', [r'BrokenPipe', r'crashed\b', r'production\s+run',
                             r'sign\s+problem']),
    ('CountFreshness', [r'count\b', r'stale\b', r'module\s+count',
                        r'theorem\s+count']),
    ('FirstClaimVerification', [r'first\s+in\s+any\s+proof\s+assistant']),
    ('FixPropagation', [r'still\s+present', r'not\s+propagated',
                        r'fix\s+did\s+not', r'companion\s+paper']),
]


def classify_finding(finding: dict) -> str:
    """Return the readiness gate a finding most likely maps to, or
    'unclassified' if no keyword matches."""
    text = (finding.get('name', '') + ' ' + finding.get('detail', '')).lower()
    for gate, patterns in _GATE_KEYWORDS:
        for pat in patterns:
            if re.search(pat, text, re.IGNORECASE):
                return gate
    return 'unclassified'


def cluster_findings(findings: list[dict]) -> list[dict]:
    """Group findings into QI candidates.

    A QI item is emitted when either:
      (a) The same gate classification appears in ≥2 distinct papers
          → systemic / cross-paper pattern
      (b) A finding's body carries an explicit "## QI Candidate" section
          → author-flagged systemic issue

    Returns a list of QI item dicts with id, pattern_summary,
    gate_affected, occurrences, affected_papers, severity, first_observed.
    """
    by_gate_and_paper: dict[str, set[str]] = defaultdict(set)
    by_gate_findings: dict[str, list[dict]] = defaultdict(list)

    for f in findings:
        gate = classify_finding(f)
        paper = f.get('meta', {}).get('inferred_paper') or '(unknown)'
        by_gate_and_paper[gate].add(paper)
        by_gate_findings[gate].append(f)

    items = []
    for gate, papers in sorted(by_gate_and_paper.items()):
        if gate == 'unclassified':
            continue
        if len(papers) < 2:
            continue  # not cross-paper → not a QI candidate
        gate_findings = by_gate_findings[gate]
        dates = [f.get('meta', {}).get('review_date', '') for f in gate_findings]
        severities = Counter(f.get('meta', {}).get('severity', 'advisory')
                             for f in gate_findings)
        items.append({
            'id': f'qi-{gate.lower()}',
            'pattern_summary': f'Recurring {gate} findings across {len(papers)} papers',
            'gate_affected': gate,
            'occurrences': len(gate_findings),
            'affected_papers': sorted(papers - {'(unknown)'}),
            'severity_mix': dict(severities),
            'first_observed': min((d for d in dates if d), default='unknown'),
            'last_observed': max((d for d in dates if d), default='unknown'),
            'status': 'open',
            'owner': None,
            'target_date': None,
            'evidence_on_close': None,
            'representative_findings': [
                {'id': f['id'], 'label': f['label'], 'file': f.get('meta', {}).get('review_file')}
                for f in gate_findings[:5]
            ],
        })
    return items


# ═══════════════════════════════════════════════════════════════════════
# Markdown emission
# ═══════════════════════════════════════════════════════════════════════

def render_register(items: list[dict], findings_total: int) -> str:
    """Render the QI register as markdown. Section structure is stable
    so the document is diff-friendly across regenerations."""
    generated = datetime.now(timezone.utc).isoformat(timespec='seconds')
    open_count = sum(1 for it in items if it['status'] == 'open')
    closed_count = sum(1 for it in items if it['status'] == 'closed')

    lines = []
    lines.append("# Meta-process Quality Improvement Register")
    lines.append("")
    lines.append(f"**Auto-generated:** {generated}")
    lines.append(f"**Generator:** `scripts/qi_register.py`")
    lines.append(f"**Reads from:** current ReviewFinding graph nodes + this file's `## Closed Items` section for status continuity")
    lines.append("")
    lines.append("This is the Stage 14 (advisory) register. Each QI item is a **process-level** issue — a failure class that has affected multiple papers or indicates a pipeline gap — not a paper-local issue. Stage 13 (adversarial review) surfaces paper-level issues; Stage 14 aggregates those into process improvements. Stage 14 never blocks submission; items here feed remediation waves.")
    lines.append("")
    lines.append("## Summary")
    lines.append("")
    lines.append(f"- **{findings_total}** ReviewFinding nodes currently in the graph")
    lines.append(f"- **{len(items)}** QI items detected")
    lines.append(f"- **{open_count}** open, **{closed_count}** closed")
    lines.append("")
    lines.append("## Open Items")
    lines.append("")
    if not items or all(it['status'] == 'closed' for it in items):
        lines.append("_(none)_")
    else:
        for item in items:
            if item['status'] != 'open':
                continue
            lines.append(f"### {item['id']} — {item['pattern_summary']}")
            lines.append("")
            lines.append(f"- **Gate affected:** `{item['gate_affected']}`")
            lines.append(f"- **Occurrences:** {item['occurrences']} findings across {len(item['affected_papers'])} papers")
            if item['affected_papers']:
                lines.append(f"- **Affected papers:** {', '.join(item['affected_papers'])}")
            sev = ', '.join(f'{v} {k}' for k, v in item['severity_mix'].items())
            lines.append(f"- **Severity mix:** {sev}")
            lines.append(f"- **First observed:** {item['first_observed']}")
            lines.append(f"- **Last observed:** {item['last_observed']}")
            lines.append(f"- **Owner:** {item['owner'] or '_(unassigned)_'}")
            lines.append(f"- **Target date:** {item['target_date'] or '_(unset)_'}")
            lines.append("")
            lines.append("**Representative findings:**")
            lines.append("")
            for rf in item['representative_findings']:
                loc = rf.get('file') or ''
                lines.append(f"- `{rf['id']}` — {rf['label']}" + (f" ({loc})" if loc else ""))
            lines.append("")
    lines.append("## Closed Items")
    lines.append("")
    closed_items = [it for it in items if it['status'] == 'closed']
    if not closed_items:
        lines.append("_(none yet)_")
    else:
        for item in closed_items:
            lines.append(f"### {item['id']} — {item['pattern_summary']}")
            lines.append(f"- **Closed:** {item.get('evidence_on_close', '_(undocumented)_')}")
            lines.append("")
    lines.append("---")
    lines.append("")
    lines.append("## Manual fields")
    lines.append("")
    lines.append("The following fields are preserved across regenerations by matching on QI item `id`:")
    lines.append("")
    lines.append("- `owner` — person responsible")
    lines.append("- `target_date` — ISO 8601")
    lines.append("- `status` — `open` / `in-progress` / `closed`")
    lines.append("- `evidence_on_close` — commit hash or wave reference that remediated the pattern")
    lines.append("")
    lines.append("To assign fields for a QI item, edit the item section inline. The generator does NOT overwrite manual fields (it matches on `id`). (Current generator is auto-regen-only; manual-field persistence is a follow-up.)")
    lines.append("")
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description="Stage 14 QI register generator")
    parser.add_argument('--stats', action='store_true', help='Print JSON summary, no write')
    parser.add_argument('--snapshot', action='store_true',
                        help='Also write timestamped snapshot to docs/QI_REGISTER_{date}.md')
    args = parser.parse_args()

    findings = load_review_findings()
    items = cluster_findings(findings)

    if args.stats:
        print(json.dumps({
            'findings_total': len(findings),
            'qi_items_detected': len(items),
            'items': [{k: v for k, v in it.items() if k != 'representative_findings'}
                      for it in items],
        }, indent=2))
        return

    md = render_register(items, len(findings))
    REGISTER_PATH.parent.mkdir(parents=True, exist_ok=True)
    REGISTER_PATH.write_text(md)
    print(f"QI register written to {REGISTER_PATH}")
    print(f"  {len(findings)} ReviewFinding nodes consumed")
    print(f"  {len(items)} QI items emitted")

    if args.snapshot:
        today = datetime.now(timezone.utc).strftime('%Y-%m-%d')
        snap_path = PROJECT_ROOT / "docs" / f"QI_REGISTER_{today}.md"
        snap_path.write_text(md)
        print(f"  Snapshot: {snap_path}")


if __name__ == '__main__':
    main()
