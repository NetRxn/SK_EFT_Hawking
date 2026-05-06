#!/usr/bin/env python3
"""
bundle_readiness.py — Phase 6i Wave 7.4 per-bundle Stage-13 readiness summary
=============================================================================

Aggregates the existing per-paper Stage-13 review findings (extracted by
`scripts/build_graph.py:extract_review_finding_nodes`) by bundle, using
the per-paper → per-bundle assignment from
`docs/PAPER_DRAFT_MAPPING.md`. Produces:

  1. `papers/AutomatedReviews/<DATE>-bundle-stage13/<bundle>.md` per
     bundle — a readiness summary aggregating per-paper findings,
     classifying each finding by bundle scope (intra-bundle vs cross-
     bundle), and listing the bundle's anchor coverage.
  2. `docs/BUNDLE_READINESS_HEATMAP.md` — the N-gate × 13-bundle
     heatmap (the bundle-aware analog of the pre-existing
     `READINESS_GATES.md`).

This script does NOT run a fresh-context LLM-driven Stage-13 review —
that is a user-triggered downstream step per memory
`feedback_stages_11_13_reflexive.md`. The aggregation here lifts the
already-existing per-paper review findings into per-bundle summaries
so the user can see at a glance which bundles are submission-ready.

Usage
-----
    uv run python scripts/bundle_readiness.py             # generate everything
    uv run python scripts/bundle_readiness.py --bundle L1 # one bundle only
    uv run python scripts/bundle_readiness.py --heatmap   # only heatmap
"""
from __future__ import annotations

import argparse
import json
import sys
from collections import Counter, defaultdict
from datetime import datetime, timezone
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent
PAPERS_DIR = PROJECT_ROOT / "papers"
REVIEWS_DIR = PAPERS_DIR / "AutomatedReviews"
HEATMAP_PATH = PROJECT_ROOT / "docs" / "BUNDLE_READINESS_HEATMAP.md"

sys.path.insert(0, str(PROJECT_ROOT / "scripts"))
from bundle_migration import parse_mapping, MAPPING_DOC  # noqa: E402
from sentence_state import _VALID_BUNDLE_TARGETS  # noqa: E402


def load_findings_by_paper() -> dict[str, list[dict]]:
    """Pull current ReviewFinding nodes via build_graph and partition
    by paper."""
    from build_graph import extract_review_finding_nodes
    from qi_register import classify_finding

    findings = extract_review_finding_nodes()
    by_paper: dict[str, list[dict]] = defaultdict(list)
    for f in findings:
        m = f.get("meta", {}) or {}
        paper = m.get("inferred_paper")
        if not paper:
            continue
        by_paper[paper].append({
            "id": f["id"],
            "label": f["label"],
            "gate": classify_finding(f),
            "severity": m.get("severity", "advisory"),
            "status": m.get("status", "open"),
            "review_date": m.get("review_date", ""),
            "review_file": m.get("review_file", ""),
        })
    return dict(by_paper)


def aggregate_by_bundle(
    assignments: dict[str, dict],
    findings_by_paper: dict[str, list[dict]],
) -> dict[str, dict]:
    """For each bundle code, aggregate all findings from its source
    papers + collect bundle-level statistics."""
    by_bundle: dict[str, dict] = {}
    for b in _VALID_BUNDLE_TARGETS:
        sources = [p for p, a in assignments.items()
                   if b in a["bundle_destinations"]]
        all_findings = []
        for p in sources:
            for f in findings_by_paper.get(p, []):
                f_copy = dict(f)
                f_copy["paper"] = p
                all_findings.append(f_copy)

        # Open findings only (closed via supersession ledger no longer count)
        open_findings = [f for f in all_findings if f.get("status") == "open"]

        # Severity breakdown of open findings
        sev_counter = Counter(f["severity"] for f in open_findings)
        # Gate breakdown
        gate_counter = Counter(f["gate"] for f in open_findings)

        # Critical / blocker count = severity in {critical, major}
        n_blockers = sum(sev_counter[s] for s in ("critical", "major"))

        # Stage-13 readiness verdict
        if n_blockers == 0 and len(open_findings) <= 5:
            readiness = "GREEN"
        elif n_blockers == 0:
            readiness = "YELLOW"  # advisory residuals only
        else:
            readiness = "RED"

        by_bundle[b] = {
            "sources": sorted(sources),
            "source_count": len(sources),
            "total_findings": len(all_findings),
            "open_findings": len(open_findings),
            "severity_mix": dict(sev_counter),
            "gate_mix": dict(gate_counter),
            "blocker_count": n_blockers,
            "readiness": readiness,
            "open_finding_ids": [f["id"] for f in open_findings[:10]],
        }
    return by_bundle


def write_bundle_review_doc(
    bundle: str,
    info: dict,
    out_dir: Path,
) -> Path:
    """Write papers/AutomatedReviews/<DATE>-bundle-stage13/<bundle>.md."""
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / f"{bundle}.md"

    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    sources_lines = (
        "\n".join(f"- `papers/{s}/paper_draft.tex`" for s in info["sources"])
        or "_(no source papers assigned)_"
    )

    sev_lines = ", ".join(f"{v} {k}" for k, v in
                          sorted(info["severity_mix"].items())) or "_(none)_"
    gate_lines = ", ".join(f"{v} {k}" for k, v in
                           sorted(info["gate_mix"].items())) or "_(none)_"

    open_ids_block = (
        "\n".join(f"- `{i}`" for i in info["open_finding_ids"])
        or "_(no open findings)_"
    )

    content = f"""# Bundle {bundle} — Stage-13 readiness summary

**Date:** {today}
**Tool:** `scripts/bundle_readiness.py`
**Source mapping:** `docs/PAPER_DRAFT_MAPPING.md`
**Anchor list:** `docs/agents/claims-reviewer-bundle-prompts.md` §`{bundle}`

This is an *aggregation* of the existing per-paper Stage-13 review
findings, partitioned by the per-paper → per-bundle assignment. It is
NOT a fresh-context LLM Stage-13 review — that is user-triggered per
memory `feedback_stages_11_13_reflexive.md`.

## Source papers ({info['source_count']})

{sources_lines}

## Aggregated finding counts

- **Total findings (lifetime):** {info['total_findings']}
- **Open findings (post-supersession):** {info['open_findings']}
- **Blocker-class (critical + major):** {info['blocker_count']}
- **Severity mix:** {sev_lines}
- **Gate mix:** {gate_lines}

## Readiness verdict

**{info['readiness']}**

- GREEN: 0 blockers, ≤5 open advisories
- YELLOW: 0 blockers, advisory residuals only
- RED: ≥1 blocker (critical or major severity)

## Sample open finding IDs (first 10)

{open_ids_block}

## Next actions

- **GREEN:** ready for fresh-context Stage-13 LLM sweep when user
  authorizes; pair with `validate.py --check bundle_consistency` to
  ensure cross-bundle cross-bridges (anchor table in
  `docs/agents/claims-reviewer-bundle-prompts.md`) hold.
- **YELLOW:** review the open advisory list; decide per-finding whether
  to fix-in-place or supersede via `docs/review_finding_supersessions.json`.
- **RED:** address blocker findings before promoting to Stage-13
  fresh-context review. Walk each open critical/major finding via
  `scripts/build_graph.py:extract_review_finding_nodes` filtered by
  `inferred_paper` ∈ {{bundle source set}}.

---

*Generated by `scripts/bundle_readiness.py` (Phase 6i Wave 7.4).*
"""
    out_path.write_text(content)
    return out_path


def write_heatmap(
    by_bundle: dict[str, dict],
) -> Path:
    """Write docs/BUNDLE_READINESS_HEATMAP.md with the N-gate × 13-bundle
    summary."""
    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")

    # Collect all gate names that appear across bundles
    all_gates: set[str] = set()
    for info in by_bundle.values():
        all_gates.update(info["gate_mix"].keys())
    gate_order = sorted(all_gates)

    # Header row: bundles in tier order
    bundle_order = [
        "F",
        "D1", "D2", "D3", "D4", "D5",
        "L1", "L2", "L3",
        "I1", "I2", "I3",
        "E1", "E2",
    ]

    lines = [
        "# Bundle Readiness Heatmap",
        "",
        f"**Auto-generated:** {today}",
        f"**Tool:** `scripts/bundle_readiness.py --heatmap`",
        "",
        "**Companion to:** `docs/READINESS_GATES.md` (per-paper) — the "
        "per-bundle analog. Phase 6i Wave 7.4 deliverable.",
        "",
        "## Verdict legend",
        "",
        "- 🟢 **GREEN** — 0 blockers, ≤5 open advisories",
        "- 🟡 **YELLOW** — 0 blockers, advisory residuals only",
        "- 🔴 **RED** — ≥1 blocker (critical / major severity)",
        "",
        "## Bundle summary",
        "",
        "| Bundle | Tier | Sources | Open | Blockers | Severity mix | Verdict |",
        "|---|---:|---:|---:|---:|---|:---:|",
    ]

    tier_map = {
        "F": 0,
        "D1": 1, "D2": 1, "D3": 1, "D4": 1, "D5": 1,
        "L1": 2, "L2": 2, "L3": 2,
        "I1": 3, "I2": 3, "I3": 3,
        "E1": 4, "E2": 4,
    }
    icon = {"GREEN": "🟢", "YELLOW": "🟡", "RED": "🔴"}

    for b in bundle_order:
        info = by_bundle.get(b, {})
        if not info:
            continue
        sev = ", ".join(f"{v} {k}" for k, v in
                        sorted(info["severity_mix"].items()))
        if not sev:
            sev = "_(none)_"
        lines.append(
            f"| **{b}** | {tier_map[b]} | {info['source_count']} | "
            f"{info['open_findings']} | {info['blocker_count']} | "
            f"{sev} | {icon.get(info['readiness'], '?')} {info['readiness']} |"
        )

    lines.extend([
        "",
        "## Gate × Bundle distribution (open findings)",
        "",
        "| Bundle | " + " | ".join(g[:18] for g in gate_order) + " |",
        "|---|" + "|".join(["---:"] * len(gate_order)) + "|",
    ])
    for b in bundle_order:
        info = by_bundle.get(b, {})
        if not info:
            continue
        row_cells = [str(info["gate_mix"].get(g, 0)) for g in gate_order]
        lines.append(f"| **{b}** | " + " | ".join(row_cells) + " |")

    lines.extend([
        "",
        "## Notes",
        "",
        "- This heatmap aggregates *existing* per-paper Stage-13 review "
        "findings via `build_graph.extract_review_finding_nodes()` "
        "(post-supersession). It does NOT include findings from a fresh-"
        "context Stage-13 sweep on the bundle (those are user-triggered).",
        "- 'Open' means `meta.status == 'open'` after applying "
        "`docs/review_finding_supersessions.json` overrides.",
        "- 'Blockers' = findings with severity `critical` or `major`. "
        "RED bundles must close blockers before promoting to a fresh-"
        "context Stage-13 LLM review.",
        "- Cross-bundle consistency between bundle siblings is verified "
        "by `validate.py --check bundle_consistency` (Wave 7.3); see "
        "`papers/cluster_bundle_index.json` for the cross-bundle cluster "
        "registry.",
        "",
        "---",
        "",
        "*Generated by `scripts/bundle_readiness.py` (Phase 6i Wave 7.4).*",
    ])

    HEATMAP_PATH.parent.mkdir(parents=True, exist_ok=True)
    HEATMAP_PATH.write_text("\n".join(lines))
    return HEATMAP_PATH


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Phase 6i Wave 7.4 per-bundle readiness summary"
    )
    parser.add_argument(
        "--bundle", help="produce readiness doc for one bundle only",
    )
    parser.add_argument(
        "--heatmap", action="store_true",
        help="produce only the heatmap (skip per-bundle docs)",
    )
    parser.add_argument(
        "--json", action="store_true",
        help="emit aggregated dict as JSON, no files written",
    )
    args = parser.parse_args()

    mapping_text = MAPPING_DOC.read_text()
    assignments = parse_mapping(mapping_text)
    findings_by_paper = load_findings_by_paper()
    by_bundle = aggregate_by_bundle(assignments, findings_by_paper)

    if args.json:
        print(json.dumps(by_bundle, indent=2))
        return 0

    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    out_dir = REVIEWS_DIR / f"{today}-bundle-stage13"

    if not args.heatmap:
        target_bundles = (
            [args.bundle] if args.bundle else sorted(_VALID_BUNDLE_TARGETS)
        )
        for b in target_bundles:
            info = by_bundle.get(b)
            if info is None:
                print(f"[SKIP] {b} — not in valid bundle set")
                continue
            path = write_bundle_review_doc(b, info, out_dir)
            verdict = info["readiness"]
            n_open = info["open_findings"]
            n_blk = info["blocker_count"]
            print(f"  [{verdict:6s}] {b}: {path.relative_to(PROJECT_ROOT)}"
                  f"  open={n_open}, blockers={n_blk}")

    # Always emit the heatmap unless single-bundle mode
    if not args.bundle:
        heatmap_path = write_heatmap(by_bundle)
        print(f"\nHeatmap written to {heatmap_path.relative_to(PROJECT_ROOT)}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
