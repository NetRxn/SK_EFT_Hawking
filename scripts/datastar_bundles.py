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
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

PROJECT_ROOT = Path(__file__).resolve().parent.parent
PAPERS_DIR = PROJECT_ROOT / "papers"
MAPPING_DOC = PROJECT_ROOT / "docs" / "PAPER_DRAFT_MAPPING.md"
INDEX_PATH = PAPERS_DIR / "cluster_bundle_index.json"
SUBMISSION_STATE = PROJECT_ROOT / "docs" / "submission_state.json"
REVIEWS_DIR = PAPERS_DIR / "AutomatedReviews"


# Tier metadata. Phase 6i Wave 7.5.
_TIER_OF = {
    "F": 0,
    "D1": 1, "D2": 1, "D3": 1, "D4": 1, "D5": 1, "D6": 1, "D7": 1, "D8": 1,
    "L1": 2, "L2": 2, "L3": 2,
    "I1": 3, "I2": 3, "I3": 3,
    "E1": 4, "E2": 4,
}

_BUNDLE_TITLES = {
    "F": "Fluid-Based Approaches to Fundamental Physics — A Formally Verified Survey",
    "D1": "Analog Hawking across three platforms",
    "D2": "Anomaly constraints on SM particle content",
    "D3": "Emergent gravity through BH thermodynamics",
    "D4": "Topological quantum computation foundations",
    "D5": "Dark sector under substrate constraints",
    "D6": "Formally Verified Fault-Tolerant Quantum Computation Substrate",
    "D7": "Classical Simulability and Quantum Advantage via Tensor Networks: A Formally Verified Demarcation",
    "D8": "Kernel-Verified Universal Quantum Gate Compilation — Alphabet-Agnostic Solovay-Kitaev across Dimensions",
    "L1": "GW170817 / vestigial-graviton",
    "L2": "Three generations from modular invariance",
    "L3": "BCH four laws by regime",
    "I1": "Verification methodology with worked cases",
    "I2": "Verified statistical estimators + lean-tensor-categories",
    "I3": "Verified Stochastic Calculus for Mathlib4",
    "E1": "Paris-LKB polariton letter",
    "E2": "Dean-Kim-Lucas graphene letter",
}

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
    import sys
    sys.path.insert(0, str(PROJECT_ROOT / "scripts"))
    from bundle_migration import parse_mapping
    from bundle_readiness import aggregate_by_bundle, load_findings_by_paper

    mapping_text = MAPPING_DOC.read_text()
    assignments = parse_mapping(mapping_text)
    findings_by_paper = load_findings_by_paper()
    by_bundle = aggregate_by_bundle(assignments, findings_by_paper)

    review_dir = _latest_review_dir_for_bundle()

    bundles_rows = []
    for code in sorted(by_bundle.keys(), key=lambda b: (_TIER_OF[b], b)):
        info = by_bundle[code]
        review_doc = ""
        if review_dir is not None:
            doc_path = review_dir / f"{code}.md"
            if doc_path.exists():
                review_doc = str(doc_path.relative_to(PROJECT_ROOT))
        bundles_rows.append({
            "code": code,
            "tier": _TIER_OF[code],
            "title": _BUNDLE_TITLES.get(code, ""),
            "source_count": info["source_count"],
            "open_findings": info["open_findings"],
            "blocker_count": info["blocker_count"],
            "readiness": info["readiness"],
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
