"""
datastar_bundles.py — Phase 6i Wave 7.5 dashboard data loader for
the Bundles tab.

Loads bundle assignments from `docs/PAPER_DRAFT_MAPPING.md`, per-bundle
readiness from `scripts/bundle_readiness.py`'s aggregation, cross-bundle
clusters from `papers/cluster_bundle_index.json`, and submission events
from `docs/submission_state.json`. Returns a single dict consumed by
the `templates/partials/bundles_tab.html` Jinja partial.

Usage from `provenance_dashboard.py`:

    from datastar_bundles import load_bundles_summary
    summary = load_bundles_summary()
    return render_template("dashboard.html", ..., bundles_summary=summary)
"""
from __future__ import annotations

import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
PROJECT_ROOT = SCRIPT_DIR.parent
PAPERS_DIR = PROJECT_ROOT / "papers"
MAPPING_DOC = PROJECT_ROOT / "docs" / "PAPER_DRAFT_MAPPING.md"
INDEX_PATH = PAPERS_DIR / "cluster_bundle_index.json"
SUBMISSION_STATE = PROJECT_ROOT / "docs" / "submission_state.json"
REVIEWS_DIR = PAPERS_DIR / "AutomatedReviews"


# Tier metadata. Phase 6i Wave 7.5; sourced from scripts/bundle_registry.py
# since the 2026-07-30 roster consolidation.
#
# The registry covers the full AUTHORIZED roster in docs/PAPER_STRATEGY.md, not
# just the bundles currently scaffolded on disk — scaffolding is deferred to
# first content-lift per BUNDLE_LIFT_PROCEDURE, so a newly authorized bundle
# does not render yet, but the tab does not break on the day it does.
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))
from bundle_registry import (  # noqa: E402
    BUNDLE_TITLES as _REGISTRY_TITLES,
    TIER_OF as _TIER_OF,
    UNKNOWN_TIER as _UNKNOWN_TIER,
    bundle_sort_key as _bundle_sort_key,
    complete_map,
)

# Module-specific data: the dashboard table is width-constrained, so a few
# bundles render under a shortened title. Everything else falls through to the
# registry's canonical title — and `complete_map` guarantees the result covers
# the WHOLE roster, so a new bundle can never render blank here.
_SHORT_TITLE_OVERRIDES = {
    "D12": "Kernel-Verified Detector & Readout Metrology",
    "I3": "Verified Stochastic Calculus for Mathlib4",
}
_BUNDLE_TITLES = complete_map(
    _SHORT_TITLE_OVERRIDES, _REGISTRY_TITLES, what="dashboard bundle titles",
)

_VERDICT_ICON = {"GREEN": "🟢", "YELLOW": "🟡", "RED": "🔴"}


def _latest_review_dir_for_bundle() -> Path | None:
    """Return the latest `<DATE>-bundle-stage13/` directory under
    `papers/AutomatedReviews/`, or None if no such dir exists."""
    if not REVIEWS_DIR.exists():
        return None
    candidates = sorted(
        d for d in REVIEWS_DIR.iterdir()
        if d.is_dir() and d.name.endswith("-bundle-stage13")
    )
    return candidates[-1] if candidates else None


def load_bundles_summary() -> dict[str, Any]:
    """Aggregate everything the Bundles tab needs into one dict."""
    from bundle_migration import parse_mapping
    from bundle_readiness import aggregate_by_bundle, load_findings_by_paper

    mapping_text = MAPPING_DOC.read_text()
    assignments = parse_mapping(mapping_text)
    findings_by_paper = load_findings_by_paper()
    by_bundle = aggregate_by_bundle(assignments, findings_by_paper)

    review_dir = _latest_review_dir_for_bundle()

    bundles_rows = []
    for code in sorted(by_bundle.keys(), key=_bundle_sort_key):
        info = by_bundle[code]
        review_doc = ""
        if review_dir is not None:
            doc_path = review_dir / f"{code}.md"
            if doc_path.exists():
                review_doc = str(doc_path.relative_to(PROJECT_ROOT))
        bundles_rows.append({
            "code": code,
            "tier": _TIER_OF.get(code, _UNKNOWN_TIER),
            "title": _BUNDLE_TITLES.get(code, ""),
            "source_count": info["source_count"],
            "open_findings": info["open_findings"],
            "blocker_count": info["blocker_count"],
            "readiness": info["readiness"],
            # readiness_display carries the nuance bundle_readiness.py computes
            # (e.g. "YELLOW (unreviewed)") that bare readiness flattens away.
            "readiness_display": info.get("readiness_display", info["readiness"]),
            "verdict_icon": _VERDICT_ICON.get(info["readiness"], "?"),
            "review_doc": review_doc,
        })

    # Cross-bundle clusters
    cross_bundle_clusters: list[dict] = []
    if INDEX_PATH.exists():
        idx = json.loads(INDEX_PATH.read_text())
        for c in idx.get("clusters", []):
            if not c.get("cross_bundle"):
                continue
            cross_bundle_clusters.append({
                "id": c.get("id"),
                "bundles": c.get("bundle_destinations_excluding_flagship", []),
                "match_kind": c.get("match_kind", "unknown"),
                "member_papers": c.get("member_papers", []),
            })

    # Submission events
    submission_events: list[dict] = []
    if SUBMISSION_STATE.exists():
        try:
            ss = json.loads(SUBMISSION_STATE.read_text())
            submission_events = ss.get("events", [])
        except (json.JSONDecodeError, OSError):
            submission_events = []

    return {
        "total_bundles": len(bundles_rows),
        "bundles": bundles_rows,
        "cross_bundle_count": len(cross_bundle_clusters),
        "cross_bundle_clusters": cross_bundle_clusters,
        "submission_events": submission_events,
    }


def append_submission_event(
    bundle: str, action: str, evidence: str = "",
) -> dict:
    """Append-only submission state event. Phase 6i Wave 7.5 schema:
    {bundle, action: "drafted" | "stage13_pass" | "submitted" |
     "accepted" | "published", date, evidence}."""
    if SUBMISSION_STATE.exists():
        ss = json.loads(SUBMISSION_STATE.read_text())
    else:
        ss = {"schema_version": 1, "events": []}

    event = {
        "date": datetime.now(timezone.utc).strftime("%Y-%m-%d"),
        "bundle": bundle,
        "action": action,
        "evidence": evidence,
    }
    ss["events"].append(event)
    SUBMISSION_STATE.parent.mkdir(parents=True, exist_ok=True)
    SUBMISSION_STATE.write_text(json.dumps(ss, indent=2))
    return event
