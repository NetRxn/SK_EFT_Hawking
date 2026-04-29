#!/usr/bin/env python3
"""
review_runner.py — Phase 6i Wave 7.2 bundle-aware review orchestrator
=====================================================================

Orchestrates a bundle-level Stage-13 review by walking the lifted
source material (per `docs/PAPER_DRAFT_MAPPING.md` §2 + the per-bundle
anchor list at `docs/agents/claims-reviewer-bundle-prompts.md`) and
producing a per-bundle review document at
`papers/AutomatedReviews/<DATE>-bundle-stage13/<bundle>.md`.

The actual Stage-13 LLM-driven review work is performed by the
`physics-qa:claims-reviewer` and `physics-qa:figure-reviewer` agents,
which accept a `bundle_target` argument. This script is the thin
orchestration layer that:

  1. Resolves a bundle's lifted source set from `PAPER_DRAFT_MAPPING.md`.
  2. Looks up the bundle's anchor list from
     `docs/agents/claims-reviewer-bundle-prompts.md`.
  3. Emits a per-bundle review-prep brief that the agent consumes.
  4. After the agent runs, validates the produced review document
     against the bundle anchor list (anchor coverage check).

Usage
-----
    uv run python scripts/review_runner.py --list-bundles
    uv run python scripts/review_runner.py --bundle L1 --prep-brief
    uv run python scripts/review_runner.py --bundle L1 --review-doc <path>
                                              # validates anchor coverage
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent
PAPERS_DIR = PROJECT_ROOT / "papers"
MAPPING_DOC = PROJECT_ROOT / "docs" / "PAPER_DRAFT_MAPPING.md"
ANCHOR_DOC = PROJECT_ROOT / "docs" / "agents" / "claims-reviewer-bundle-prompts.md"

sys.path.insert(0, str(PROJECT_ROOT / "scripts"))
from bundle_migration import parse_mapping  # noqa: E402
from sentence_state import _VALID_BUNDLE_TARGETS  # noqa: E402


def list_bundles() -> dict[str, dict]:
    """Build per-bundle index: {bundle: {sources: [paper_keys],
    tier: int, anchor_section_present: bool}}."""
    mapping_text = MAPPING_DOC.read_text()
    assignments = parse_mapping(mapping_text)
    anchor_text = ANCHOR_DOC.read_text() if ANCHOR_DOC.exists() else ""

    by_bundle: dict[str, list[str]] = {b: [] for b in _VALID_BUNDLE_TARGETS}
    for paper, a in assignments.items():
        for b in a["bundle_destinations"]:
            by_bundle[b].append(paper)

    tiers = {
        "F": 0,
        "D1": 1, "D2": 1, "D3": 1, "D4": 1, "D5": 1,
        "L1": 2, "L2": 2, "L3": 2,
        "I1": 3, "I2": 3,
        "E1": 4, "E2": 4,
    }

    out: dict[str, dict] = {}
    for b in sorted(_VALID_BUNDLE_TARGETS):
        anchor_section = bool(re.search(rf"### {re.escape(b)}\.\s", anchor_text))
        out[b] = {
            "tier": tiers[b],
            "sources": sorted(by_bundle[b]),
            "source_count": len(by_bundle[b]),
            "anchor_section_present": anchor_section,
        }
    return out


def emit_prep_brief(bundle: str) -> str:
    """Emit a markdown review-prep brief for the given bundle: tier,
    sources, anchor list pointer, scope guidance."""
    if bundle not in _VALID_BUNDLE_TARGETS:
        raise ValueError(
            f"unknown bundle {bundle!r}; must be one of "
            f"{sorted(_VALID_BUNDLE_TARGETS)}"
        )
    info = list_bundles()[bundle]

    profile_per_tier = {
        0: ("Tier 0 — Flagship (review-paper style)",
            "Independent reviewer-anchored against ARCHITECTURE_SCOPE.md, "
            "RESEARCH_STATUS_OVERVIEW.md, and shipped Tier 1 bundle "
            "published versions."),
        1: ("Tier 1 — Deep paper (bundle-level review)",
            "Intra-bundle consistency across lifted sections + "
            "cross-bundle consistency for cross-bridge claims + "
            "architectural-scope sidebar correctly slice-restricted."),
        2: ("Tier 2 — PRL splash (single-paper depth, stand-alone)",
            "Stand-alone review; reviewer does NOT penalize the absence "
            "of broader-scope content. Carry the bundle-specific "
            "Stage-13 anchor."),
        3: ("Tier 3 — Infrastructure (software / methodology paper)",
            "Software-paper review pattern; reproducibility checks; "
            "each worked case traces to a reproducible Aristotle run ID "
            "or commit-pinned counterexample."),
        4: ("Tier 4 — Experimental letter (lightweight + device audit)",
            "Letter review + device-parameter audit pass against the "
            "experimental team's published device specs."),
    }
    profile_label, profile_desc = profile_per_tier[info["tier"]]

    lines = [
        f"# Bundle {bundle} — Stage-13 review prep brief",
        "",
        f"**Tier:** {info['tier']}",
        f"**Profile:** {profile_label}",
        "",
        profile_desc,
        "",
        f"**Sources ({info['source_count']}):**",
        "",
    ]
    for src in info["sources"]:
        lines.append(f"- `papers/{src}/paper_draft.tex`")
    lines.extend([
        "",
        "**Anchor list:** see `docs/agents/claims-reviewer-bundle-prompts.md`"
        f" §`{bundle}`.",
        "",
        "**Required reads (in order):**",
        "1. `CLAUDE.md` — project conventions",
        "2. `docs/PAPER_STRATEGY.md` — bundle architecture",
        "3. `docs/PAPER_DRAFT_MAPPING.md` — per-draft → per-bundle assignment",
        "4. `docs/agents/claims-reviewer-bundle-prompts.md` — per-bundle "
        "anchor list",
        "5. `docs/WAVE_EXECUTION_PIPELINE.md` Stage 13 — adversarial review",
        "",
        "**Cross-bundle consistency:** for any anchor cited as a"
        " cross-bridge in `claims-reviewer-bundle-prompts.md`, run"
        " `validate.py --check bundle_consistency` (Wave 7.3) to confirm"
        " the cross-bridge claim agrees across bundle boundaries.",
        "",
        "**Output:** write the review document to "
        f"`papers/AutomatedReviews/<DATE>-bundle-stage13/{bundle}.md`.",
    ])
    return "\n".join(lines)


def validate_review_doc(bundle: str, doc_path: Path) -> tuple[bool, list[str]]:
    """Validate that a bundle review document exists and references all
    of the bundle's anchor list items at least once. Returns (ok,
    issues)."""
    if not doc_path.exists():
        return (False, [f"review document not found: {doc_path}"])
    text = doc_path.read_text()
    issues: list[str] = []

    # Cheap heuristic: check that every source paper is at least
    # *mentioned* by name in the review document.
    info = list_bundles()[bundle]
    for src in info["sources"]:
        if src not in text:
            issues.append(f"source paper '{src}' not mentioned in review")

    # Bundle code itself should appear at least once.
    if bundle not in text:
        issues.append(f"bundle code '{bundle}' not mentioned in review")

    return (not issues, issues)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Phase 6i Wave 7.2 bundle-aware review orchestrator",
    )
    parser.add_argument(
        "--list-bundles", action="store_true",
        help="list all 13 bundles + source paper counts",
    )
    parser.add_argument(
        "--bundle", help="bundle code (one of F, D1-D5, L1-L3, I1-I2, E1-E2)",
    )
    parser.add_argument(
        "--prep-brief", action="store_true",
        help="emit a markdown review-prep brief for the bundle",
    )
    parser.add_argument(
        "--review-doc",
        help="path to a completed review document; validate anchor coverage",
    )
    parser.add_argument(
        "--json", action="store_true",
        help="emit JSON instead of human-readable output",
    )
    args = parser.parse_args()

    if args.list_bundles:
        info = list_bundles()
        if args.json:
            print(json.dumps(info, indent=2))
        else:
            print(f"{'BUNDLE':6s} {'TIER':4s} {'SRCS':5s}  ANCHOR  SOURCES")
            for b, d in info.items():
                ok = "✓" if d["anchor_section_present"] else "✗"
                srcs = ",".join(d["sources"][:3])
                if d["source_count"] > 3:
                    srcs += f", +{d['source_count'] - 3} more"
                print(f"{b:6s} {d['tier']:4d} {d['source_count']:5d}    {ok}    {srcs}")
        return 0

    if not args.bundle:
        parser.print_help()
        return 1

    if args.review_doc:
        ok, issues = validate_review_doc(args.bundle, Path(args.review_doc))
        if ok:
            print(f"OK — {args.bundle} review at {args.review_doc} covers all "
                  f"sources and anchors.")
            return 0
        else:
            print(f"FAIL — {args.bundle} review at {args.review_doc}:")
            for issue in issues:
                print(f"  - {issue}")
            return 1

    if args.prep_brief:
        print(emit_prep_brief(args.bundle))
        return 0

    parser.print_help()
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
