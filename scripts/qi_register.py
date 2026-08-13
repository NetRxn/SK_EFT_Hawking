#!/usr/bin/env python3
"""Generate docs/QI_REGISTER.md — the Meta-process Quality Improvement
register (Pipeline Stage 14, Phase 5v Wave 7).

Reads `ReviewFinding` nodes from the current graph, clusters findings by
pattern (same gate affected + recurring across ≥2 papers **within one
`YYYY-MM` occurrence window**), and writes a user-facing markdown register
tracking open items with status, owner, target date, and evidence-on-close.

⚠️ A QI item identifies a RECURRENCE, not a gate (`qi_id_for`). The id used to
be `qi-{gate}`, which capped the register at one item per gate for all time;
with nine of eleven gate ids already in `## Closed Items`, the derivation
returned zero items against the entire live corpus. `## Closed Items` still
holds those legacy ids and is preserved verbatim (Pipeline Invariant #13) —
their suppressing effect is reconstructed per-window by `closed_qi_windows`,
never by regenerating the section.

Nothing the derivation narrows away is silent: `derive_stats` reports the
`unclassified` bucket, the sub-threshold clusters and the closure-suppressed
clusters alongside what it emitted.

This is advisory — Stage 14 never blocks submission. Its purpose is
feeding pipeline improvements back into Phase 5v+ remediation waves.

Usage:
    uv run python scripts/qi_register.py          # regenerate docs/QI_REGISTER.md
    uv run python scripts/qi_register.py --stats  # print summary
    uv run python scripts/qi_register.py --snapshot  # also write timestamped snapshot
    uv run python scripts/qi_register.py --force     # write even if hand-curated Open
                                                     #   Items would be discarded
"""
from __future__ import annotations

import argparse
import hashlib
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


_CLOSED_QI_RE = re.compile(r"^### (qi-[a-z0-9-]+)\b", re.MULTILINE)


def load_closed_qi_ids() -> tuple[set[str], dict[str, str]]:
    """Parse the existing QI_REGISTER.md `## Closed Items` section to get
    the set of QI item IDs that have been manually closed (with their
    closure block as evidence). Wave 6 addition: the auto-regenerated
    Open Items section must NOT re-open a QI item already documented as
    closed in the manually-curated Closed Items section, since some
    QI items close via structural prevention (e.g. qi-citationintegrity
    closed via Wave 1 primary-sources cache + CHECK 19) without
    necessarily flipping every individual ReviewFinding's status.

    Returns (closed_ids, closure_blocks_by_id)."""
    if not REGISTER_PATH.exists():
        return set(), {}
    text = REGISTER_PATH.read_text()
    # Find the "## Closed Items" section
    m_closed = re.search(r"^## Closed Items\b", text, re.MULTILINE)
    if not m_closed:
        return set(), {}
    closed_section = text[m_closed.end():]
    # Stop at the next "## " heading (manual fields, etc.)
    m_next = re.search(r"^## ", closed_section, re.MULTILINE)
    if m_next:
        closed_section = closed_section[: m_next.start()]
    closed_ids = set()
    closure_blocks = {}
    # Each `### qi-<id>` heading starts a closure block
    for m in re.finditer(r"^### (qi-[a-z0-9-]+)[^\n]*\n", closed_section, re.MULTILINE):
        qi_id = m.group(1)
        start = m.end()
        # Block ends at next ### or end of section
        m_next_sub = re.search(r"^### ", closed_section[start:], re.MULTILINE)
        end = start + m_next_sub.start() if m_next_sub else len(closed_section)
        closed_ids.add(qi_id)
        closure_blocks[qi_id] = closed_section[m.start():end].rstrip() + "\n"
    return closed_ids, closure_blocks


def load_manual_fields() -> dict[str, dict]:
    """Hand-curated per-item fields already on disk, keyed by qi id.

    ⚠️ **THE GUARD ABOVE ONLY SEES IDS THAT VANISH; THIS SEES FIELDS THAT VANISH.** `main()`
    refuses to write when a curated id is ABSENT from the derivation. But an id the
    derivation still reproduces sails through the guard while `render_register` rebuilds its
    `Owner` / `Target date` / `Status` from the derived dict, where they are hardcoded
    `None`/`'open'`. Assign an owner to a derived item, regenerate, and it is silently
    replaced by `_(unassigned)_` — with the register's own "Manual fields" section
    asserting, one line up, that the generator "does NOT overwrite manual fields".

    Read back and merged, so the assertion becomes true instead of aspirational.
    """
    if not REGISTER_PATH.exists():
        return {}
    text = REGISTER_PATH.read_text()
    m_open = re.search(r"^## Open Items\b", text, re.MULTILINE)
    if not m_open:
        return {}
    m_closed = re.search(r"^## Closed Items\b", text[m_open.end():], re.MULTILINE)
    body = text[m_open.end():m_open.end() + (m_closed.start() if m_closed else len(text))]
    out: dict[str, dict] = {}
    #: `_(unassigned)_` / `_(unset)_` are the renderer's own placeholders for "no value";
    #: reading one back as a value would turn a blank into a curated blank.
    _placeholder = re.compile(r"^_\(.*\)_$")
    for block in re.split(r"^### ", body, flags=re.MULTILINE)[1:]:
        qid = block.split()[0].strip()
        fields = {}
        for label, key in (("Owner", "owner"), ("Target date", "target_date"),
                           ("Status", "status"), ("Evidence on close", "evidence_on_close")):
            m = re.search(rf"^- \*\*{re.escape(label)}:\*\* (.+?)\s*$", block, re.MULTILINE)
            if m and not _placeholder.match(m.group(1).strip()):
                fields[key] = m.group(1).strip()
        if fields:
            out[qid] = fields
    return out


def load_open_qi_ids() -> set[str]:
    """IDs currently sitting under `## Open Items` in the register on disk.

    ⚠️ These are *hand-curated* ids in the pre-2026-08 free-form style
    (`qi-bibfilename`, `qi-vizdiscipline`, …). `qi_id_for` cannot and does not
    reproduce them — they were never derived. `main()` uses this set to refuse a
    regeneration that would silently drop them (Pipeline Invariant #13: the register
    is auto-regenerated *and* manually curated, and is never wiped)."""
    if not REGISTER_PATH.exists():
        return set()
    text = REGISTER_PATH.read_text()
    m_open = re.search(r"^## Open Items\b", text, re.MULTILINE)
    if not m_open:
        return set()
    section = text[m_open.end():]
    m_next = re.search(r"^## ", section, re.MULTILINE)
    if m_next:
        section = section[: m_next.start()]
    return {m.group(1) for m in
            re.finditer(r"^### (qi-[A-Za-z0-9_-]+)[^\n]*\n", section, re.MULTILINE)}


_ISO_DATE_RE = re.compile(r"\d{4}-\d{2}-\d{2}")


def closed_qi_windows() -> dict[str, str]:
    """Map each closed QI id to the `YYYY-MM` window through which its closure holds.

    ⚠️ THE RECONCILIATION THE ID CHANGE FORCES. The legacy ids in `## Closed Items`
    are `qi-{gate}` — gate-wide and date-free — so under the old scheme a closure
    retired a failure class *permanently*. `qi_id_for` cannot reproduce any of them
    (they carry no papers and no window), and Invariant #13 forbids regenerating that
    section, so they are preserved verbatim and their suppressing effect is
    reconstructed here instead: a closure suppresses occurrences **up to and including
    the month it was closed**, and a later occurrence is a genuinely new recurrence.

    The window is the latest ISO date appearing anywhere in the closure block, not just
    its heading, because a block records re-closures in its body — `qi-assumptiondisclosure`
    reads "closed 2026-04-29" in the heading and "RE-CLOSED VIA STRUCTURAL PREVENTION
    (2026-06-13)" in the body, and the later one is the one that governs.
    """
    _, blocks = load_closed_qi_ids()
    windows: dict[str, str] = {}
    for qi_id, block in blocks.items():
        dates = _ISO_DATE_RE.findall(block)
        if dates:
            windows[qi_id] = max(dates)[:7]
    return windows


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


def window_for(review_date: Any) -> str:
    """Collapse a finding's `review_date` to the `YYYY-MM` occurrence window.

    ⚠️ `review_date` is NOT uniformly an ISO date. Measured over the live corpus it
    also carries run slugs — `2026-04-25-0135-internal-adversarial`,
    `2026-08-12-legacy-compile-triage`. Every one of them is `YYYY-MM-DD`-prefixed,
    so the month is recoverable, but a `datetime.fromisoformat` would reject most of
    the corpus. Anything the prefix does not match becomes `'unknown'`, which is a
    reported value and never a dropped one.
    """
    m = re.match(r'^(\d{4})-(\d{2})', str(review_date or ''))
    return f'{m.group(1)}-{m.group(2)}' if m else 'unknown'


def qi_id_for(gate: str, papers: list[str], window: str) -> str:
    """A QI item identifies a RECURRENCE, not a gate.

    ⚠️ The id was `qi-{gate}`, which meant the register could hold one item per gate
    for all time — and closing it retired that failure class permanently. Nine of the
    eleven gates were already closed, so the detector the operator asked for was
    switched off by its own success. The occurrence's papers and window are what make
    two recurrences distinguishable.

    Stability, stated honestly: the id is a function of `(gate, papers, window)`, so a
    recurrence that later spreads to a **new paper** gets a **new id**. That is the
    intended reading — the failure recurring somewhere it had not is a new occurrence —
    but it does mean an id is stable only while its paper set is.
    """
    key = f'{gate}|{"+".join(sorted(papers))}|{window}'
    return f'qi-{gate.lower()}-{hashlib.sha1(key.encode()).hexdigest()[:8]}'


def derive_stats(findings: list[dict] | None = None) -> dict:
    """What the derivation SAW, including what it could not classify.

    ⚠️ `unclassified` is the largest bucket in the corpus — larger than any single
    gate — and the old derivation dropped it at the top of the emit loop with a bare
    `continue`. Skipping it silently is the difference between "no recurrent failure
    modes" and "the detector cannot name them". It is still not emitted as a QI item
    (an unnamed cluster is not an actionable process item), but its size, its paper
    spread and its per-window breakdown are reported here and in `--stats`.

    Every population this function narrows is reported alongside the survivors:
    findings excluded by supersession status, clusters below the cross-paper
    threshold, and clusters suppressed by a legacy gate-wide closure. Nothing is
    capped or truncated.

    Returns the full derivation record; `items` is the QI item list and is what
    `cluster_findings` returns.
    """
    if findings is None:
        findings = load_review_findings()

    # (gate, window) → papers / findings. The WINDOW is what un-saturates the
    # derivation: one gate can recur in as many windows as it recurs in.
    by_cluster_papers: dict[tuple[str, str], set[str]] = defaultdict(set)
    by_cluster_findings: dict[tuple[str, str], list[dict]] = defaultdict(list)
    status_mix: Counter = Counter()
    gate_open_counts: Counter = Counter()

    for f in findings:
        meta = f.get('meta', {}) or {}
        status = meta.get('status', 'open')
        status_mix[status] += 1
        if status != 'open':
            continue  # Wave-6 status filter: skip superseded findings
        gate = classify_finding(f)
        gate_open_counts[gate] += 1
        window = window_for(meta.get('review_date', ''))
        # ⚠️ SECOND CAUSE OF THE SATURATION, measured here and not named in the plan.
        # Partitioning on `inferred_paper` ALONE collapses every bundle-era finding
        # onto the single `(unknown)` sentinel: measured on the live corpus, 687 of
        # 946 open findings carry `inferred_bundle` and NO `inferred_paper`, so the
        # ≥2-paper cross-paper threshold was being evaluated against 132 findings'
        # worth of spread. `bundle_readiness.load_findings_by_paper` took exactly this
        # fallback on 2026-07-31 (D11 Stage-13 round-5 BLOCKER 4.1) after the same
        # omission produced a FALSE GREEN there; qi_register never did.
        paper = (meta.get('inferred_paper') or meta.get('inferred_bundle')
                 or '(unknown)')
        by_cluster_papers[(gate, window)].add(paper)
        by_cluster_findings[(gate, window)].append(f)

    closed_ids, _ = load_closed_qi_ids()
    closure_windows = closed_qi_windows()

    items: list[dict] = []
    below_threshold: list[dict] = []
    suppressed: list[dict] = []
    unclassified_windows: dict[str, dict] = {}
    unclassified_papers: set[str] = set()

    for (gate, window), papers in sorted(by_cluster_papers.items()):
        cluster_findings_ = by_cluster_findings[(gate, window)]
        real_papers = sorted(papers - {'(unknown)'})

        if gate == 'unclassified':
            # REPORTED, not dropped. See the docstring.
            unclassified_windows[window] = {
                'findings': len(cluster_findings_),
                'papers': len(papers),
                'affected_papers': real_papers,
            }
            unclassified_papers |= papers
            continue

        if len(papers) < 2:
            below_threshold.append({'gate': gate, 'window': window,
                                    'papers': len(papers),
                                    'findings': len(cluster_findings_)})
            continue  # not cross-paper → not a QI candidate

        # A legacy `qi-{gate}` closure suppresses this gate through the month it was
        # closed, and no further. See `closed_qi_windows` for why this reconstruction
        # exists rather than `qi_id_for` reproducing the legacy id.
        legacy_id = f'qi-{gate.lower()}'
        closed_through = closure_windows.get(legacy_id)
        if legacy_id in closed_ids and closed_through and window != 'unknown' \
                and window <= closed_through:
            suppressed.append({'gate': gate, 'window': window,
                               'papers': len(papers),
                               'findings': len(cluster_findings_),
                               'closed_by': legacy_id,
                               'closed_through': closed_through})
            continue

        qi_id = qi_id_for(gate=gate, papers=real_papers, window=window)
        if qi_id in closed_ids:
            suppressed.append({'gate': gate, 'window': window,
                               'papers': len(papers),
                               'findings': len(cluster_findings_),
                               'closed_by': qi_id,
                               'closed_through': closure_windows.get(qi_id)})
            continue

        dates = [(f.get('meta', {}) or {}).get('review_date', '')
                 for f in cluster_findings_]
        severities = Counter((f.get('meta', {}) or {}).get('severity', 'advisory')
                             for f in cluster_findings_)
        # ⚠️ The ≥2 threshold counts '(unknown)' as a paper and always has, so a
        # cluster can pass it with one named paper plus an unattributed group. Say so
        # in the summary rather than rendering "across 2 papers" beside a
        # one-entry `affected_papers` list.
        unattributed = '(unknown)' in papers
        summary = (f'Recurring {gate} findings across {len(real_papers)} paper'
                   f'{"" if len(real_papers) == 1 else "s"}'
                   f'{" plus unattributed findings" if unattributed else ""} in {window}')
        items.append({
            'id': qi_id,
            'pattern_summary': summary,
            'gate_affected': gate,
            'window': window,
            'includes_unattributed': unattributed,
            'occurrences': len(cluster_findings_),
            'affected_papers': real_papers,
            'severity_mix': dict(severities),
            'first_observed': min((d for d in dates if d), default='unknown'),
            'last_observed': max((d for d in dates if d), default='unknown'),
            'status': 'open',
            'owner': None,
            'target_date': None,
            'evidence_on_close': None,
            'representative_findings': [
                {'id': f['id'], 'label': f['label'],
                 'file': (f.get('meta', {}) or {}).get('review_file')}
                for f in cluster_findings_[:5]
            ],
        })

    unclassified_open = gate_open_counts.get('unclassified', 0)
    return {
        'findings_total': len(findings),
        'open_total': status_mix.get('open', 0),
        'status_mix': dict(status_mix),
        'gate_open_counts': dict(gate_open_counts),
        'unclassified_open': unclassified_open,
        'unclassified_reported': True,
        'unclassified_papers': len(unclassified_papers - {'(unknown)'}),
        'unclassified_by_window': unclassified_windows,
        'clusters_total': len(by_cluster_papers),
        'clusters_below_paper_threshold': below_threshold,
        'clusters_suppressed_by_closure': suppressed,
        'closed_qi_ids': sorted(closed_ids),
        'closed_qi_windows': closure_windows,
        'qi_items_detected': len(items),
        'items': items,
    }


def cluster_findings(findings: list[dict]) -> list[dict]:
    """Group findings into QI candidates. Thin wrapper over `derive_stats`.

    A QI item is emitted when the same gate classification appears in ≥2 distinct
    papers **within one `YYYY-MM` occurrence window**, and that occurrence is not
    already covered by a closure in `## Closed Items`.

    ⚠️ The window is the de-saturation. Keying the id on the gate alone
    (`qi-{gate.lower()}`) capped the register at one item per gate for all time; with
    nine of eleven gate ids sitting in `## Closed Items`, the derivation returned an
    empty list against the whole live corpus.

    Findings whose `meta.status` resolves to 'fixed' or 'accepted' (via the project
    supersession ledger at docs/review_finding_supersessions.json, consumed by
    build_graph.extract_review_finding_nodes) are excluded from the open-cluster
    aggregate — only `status == 'open'` (or missing) counts toward an open QI item.

    Everything this narrows away — the unclassified bucket, sub-threshold clusters,
    closure-suppressed clusters — is counted and returned by `derive_stats`, which is
    the only caller-visible difference from silently dropping it.
    """
    return derive_stats(findings)['items']


# ═══════════════════════════════════════════════════════════════════════
# Markdown emission
# ═══════════════════════════════════════════════════════════════════════

def render_register(items: list[dict], findings_total: int,
                    stats: dict | None = None) -> str:
    """Render the QI register as markdown. Section structure is stable
    so the document is diff-friendly across regenerations.

    ⚠️ Hand-curated per-item fields on disk are read back and MERGED over the derived
    values, so a regeneration cannot silently blank an owner or a target date on an item
    the derivation still reproduces. Before this, only a VANISHED id was protected.
    """
    manual = load_manual_fields()
    items = [{**it, **manual.get(it['id'], {})} for it in items]
    generated = datetime.now(timezone.utc).isoformat(timespec='seconds')
    open_count = sum(1 for it in items if it['status'] == 'open')
    closed_ids_set, _ = load_closed_qi_ids()
    closed_count = len(closed_ids_set)
    total_qi_count = len(items) + closed_count

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
    lines.append(f"- **{total_qi_count}** QI items tracked ({len(items)} auto-detected open + {closed_count} closed via `## Closed Items` section)")
    lines.append(f"- **{open_count}** open, **{closed_count}** closed")
    if stats:
        # ⚠️ DISCLOSE THE BUCKET THE DERIVATION CANNOT NAME. This is the largest
        # single population in the corpus and it used to leave no trace at all, which
        # read as "nothing there" rather than "not classifiable".
        lines.append(
            f"- **{stats['unclassified_open']}** open findings across "
            f"{stats['unclassified_papers']} papers matched no gate keyword "
            f"(`unclassified`) and are reported here rather than emitted as QI items — "
            f"a recurrence the keyword map cannot name is still a recurrence")
        n_sup = len(stats.get('clusters_suppressed_by_closure', []))
        n_thin = len(stats.get('clusters_below_paper_threshold', []))
        lines.append(
            f"- of **{stats['clusters_total']}** (gate, window) clusters: "
            f"{stats['qi_items_detected']} emitted, {n_sup} suppressed by an existing "
            f"closure, {n_thin} below the ≥2-paper cross-paper threshold")
    lines.append("")
    lines.append("## Open Items")
    lines.append("")
    if not items or all(it['status'] == 'closed' for it in items):
        lines.append("_(none)_")
        lines.append("")
    else:
        for item in items:
            if item['status'] != 'open':
                continue
            lines.append(f"### {item['id']} — {item['pattern_summary']}")
            lines.append("")
            lines.append(f"- **Gate affected:** `{item['gate_affected']}`")
            if item.get('window'):
                lines.append(f"- **Occurrence window:** {item['window']}")
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
    # Wave-6: preserve manually-curated Closed Items section verbatim so
    # re-running the regen does NOT wipe evidence_on_close blocks. The
    # set of closed QI IDs is sourced from the existing register and
    # those IDs are excluded from the Open Items aggregate above.
    _, closure_blocks = load_closed_qi_ids()
    if not closure_blocks:
        lines.append("_(none yet)_")
    else:
        # Stable ordering by qi-id
        for qi_id in sorted(closure_blocks.keys()):
            lines.append(closure_blocks[qi_id].rstrip())
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
    lines.append("To assign fields for a QI item, edit the item section inline. `Owner`, `Target date`, `Status` and `Evidence on close` are read back and preserved across regenerations, matched on `id` — and the placeholders `_(unassigned)_` / `_(unset)_` read back as *no value*, not as a curated one. An item whose id the derivation no longer reproduces is not silently dropped either: `main()` refuses to write and names it, and `--force` is required.")
    lines.append("")
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description="Stage 14 QI register generator")
    parser.add_argument('--stats', action='store_true', help='Print JSON summary, no write')
    parser.add_argument('--snapshot', action='store_true',
                        help='Also write timestamped snapshot to docs/QI_REGISTER_{date}.md')
    parser.add_argument('--force', action='store_true',
                        help='Write even when regeneration would drop hand-curated '
                             'Open Items (see the Invariant #13 guard below)')
    args = parser.parse_args()

    findings = load_review_findings()
    stats = derive_stats(findings)
    items = stats['items']

    if args.stats:
        print(json.dumps({k: v for k, v in stats.items() if k != 'items'} | {
            'items': [{k: v for k, v in it.items() if k != 'representative_findings'}
                      for it in items],
        }, indent=2))
        return

    # ⚠️ INVARIANT #13 GUARD. `## Open Items` holds hand-curated entries in the
    # pre-derivation id style (`qi-bibfilename`, `qi-vizdiscipline`, …) that no
    # derivation reproduces, and this renderer rebuilds that section purely from
    # `items`. Writing therefore DELETES them. That was true before the id scheme
    # changed and is unchanged by it — but the derivation now emits, so a regen is
    # newly tempting. Refuse, name every id at risk, and make the operator opt in.
    orphaned = load_open_qi_ids() - {it['id'] for it in items}
    if orphaned and not args.force:
        print("REFUSING to write: regeneration would delete "
              f"{len(orphaned)} hand-curated Open Item(s) that the derivation does "
              "not reproduce (Pipeline Invariant #13 — the register is never wiped):",
              file=sys.stderr)
        for qi_id in sorted(orphaned):
            print(f"  - {qi_id}", file=sys.stderr)
        print("\nMove them to `## Closed Items` (preserved verbatim) or re-run with "
              "--force to discard them.", file=sys.stderr)
        return 1

    md = render_register(items, len(findings), stats)
    REGISTER_PATH.parent.mkdir(parents=True, exist_ok=True)
    REGISTER_PATH.write_text(md)
    print(f"QI register written to {REGISTER_PATH}")
    print(f"  {len(findings)} ReviewFinding nodes consumed")
    print(f"  {len(items)} QI items emitted")
    print(f"  {stats['unclassified_open']} open findings unclassified (reported, not dropped)")

    if args.snapshot:
        today = datetime.now(timezone.utc).strftime('%Y-%m-%d')
        snap_path = PROJECT_ROOT / "docs" / f"QI_REGISTER_{today}.md"
        snap_path.write_text(md)
        print(f"  Snapshot: {snap_path}")
    return 0


if __name__ == '__main__':
    sys.exit(main() or 0)
