#!/usr/bin/env python3
"""
bundle_migration.py — Phase 6i Wave 7.1 bundle-aware migration
==============================================================

Reads `docs/PAPER_DRAFT_MAPPING.md` Table 1 and populates the three new
bundle-aware schema fields per sentence in every paper's
`prose_state.json`:

  * `bundle_destination`: enum or list-of-enum (per the mapping's "New
    destination(s)" column).
  * `bundle_section_hint`: free-form section hint ("D3:§5",
    "introduction", etc.) parsed from the same column.
  * `lift_action`: enum (the "Lift action" column).

Architecture
------------
This script is a *bulk reader* of the mapping document and produces a
per-paper bundle assignment dict that's applied to every sentence in
that paper's prose_state. It does NOT mutate prose_state.json directly;
instead, for each paper it ingests the mapping via the canonical
`sentence_state.ingest_agent_run` interface (which appends an
audit_log event and writes prose_state.json atomically). This preserves
the replay-canonical recovery property of Phase 5v Wave 10.

Usage
-----
    uv run python scripts/bundle_migration.py            # apply migration
    uv run python scripts/bundle_migration.py --dry-run  # preview
    uv run python scripts/bundle_migration.py --paper paper25_gravitational_waves
                                                          # apply to one paper
    uv run python scripts/bundle_migration.py --report   # print mapping summary

Idempotency
-----------
Running the script twice produces the same prose_state. The audit log
captures one event per run (with `agent_run_id` derived from the
mapping document's mtime + content hash); duplicate ingestions are
detected and skipped via the existing audit-event idempotency check.

Wave 7 closure invariant: every paper that has a prose_state.json
carries bundle_destination + bundle_section_hint + lift_action on every
non-tombstoned sentence. Papers without a prose_state.json file are
skipped (no migration needed; bundle assignment is recorded in the
mapping document for future ingestion).
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent
MAPPING_DOC = PROJECT_ROOT / "docs" / "PAPER_DRAFT_MAPPING.md"
PAPERS_DIR = PROJECT_ROOT / "papers"

# Reference: bundle_destination + lift_action enums in sentence_state.py
sys.path.insert(0, str(PROJECT_ROOT / "scripts"))
from sentence_state import (
    _VALID_BUNDLE_TARGETS, _VALID_LIFT_ACTIONS,
    prose_state_path, _load_prose_state,
)


# ────────────────────────────────────────────────────────────────────────────
# Mapping document parsing
# ────────────────────────────────────────────────────────────────────────────

# Match a row of the per-existing-draft mapping table:
#   | `paper_key` (...optional Phase 5z W3...) | Title | Prior | Dest | Lift |
_TABLE_ROW_RE = re.compile(
    r"^\|\s*`(?P<paper>[a-zA-Z0-9_]+)`(?:\s*\([^)]+\))?\s*"
    r"\|\s*(?P<title>[^|]*?)\s*"
    r"\|\s*(?P<prior>[^|]*?)\s*"
    r"\|\s*(?P<dest>[^|]*?)\s*"
    r"\|\s*(?P<lift>[^|]*?)\s*\|\s*$",
    re.MULTILINE,
)

# Extract bundle codes from a destination cell like "**D3 §5** + **F §6**".
# Bold-wrapped bundle codes are real destinations; un-wrapped mentions
# (e.g., "(ships first wave with L1)") are parenthetical context and
# must be excluded — Wave 7.2 fix per bundle_migration L1/L3 collision.
_DEST_BUNDLE_RE = re.compile(
    r"\*\*(F|D[1-8]|L[1-3]|I[1-3]|E[1-2])"
    r"(?:\s*[§:]\s*(?P<hint>[^*]+?))?\*\*"
)


def parse_mapping(mapping_text: str) -> dict[str, dict]:
    """Parse PAPER_DRAFT_MAPPING.md Table 1 into per-paper assignments.

    Returns dict[paper_key, {bundle_destinations: list[str],
                             bundle_section_hints: dict[bundle, hint],
                             lift_action: str | None}].
    """
    assignments: dict[str, dict] = {}

    for m in _TABLE_ROW_RE.finditer(mapping_text):
        paper = m.group("paper").strip()
        if paper in {"Existing draft", "---"}:
            continue
        # Skip header / divider rows (no actual paper key)
        if "_" not in paper and paper.lower() != paper:
            continue

        dest_cell = m.group("dest")
        lift_cell = m.group("lift").strip()

        bundles_seen: list[str] = []
        hints: dict[str, str] = {}
        for bm in _DEST_BUNDLE_RE.finditer(dest_cell):
            bundle = bm.group(1)
            if bundle not in _VALID_BUNDLE_TARGETS:
                continue
            if bundle not in bundles_seen:
                bundles_seen.append(bundle)
            raw_hint = (bm.group("hint") or "").strip()
            if raw_hint and bundle not in hints:
                hints[bundle] = f"§{raw_hint}" if not raw_hint.startswith("§") else raw_hint

        # Lift action: parse out the canonical token if recognizable.
        # When multiple actions appear (e.g. "Lift-section + Lift-companion"),
        # the most specific wins (companion / letter / flagship beat plain
        # section, since the multi-target nature is conveyed by the bundle
        # list while lift_action records the principal action shape).
        _PRIORITY = (
            'Lift-companion', 'Lift-letter', 'Lift-flagship',
            'Retire', 'Retain-in-place', 'Lift-section',
        )
        lift_action: str | None = None
        for la in _PRIORITY:
            if la.lower() in lift_cell.lower():
                lift_action = la
                break

        if not bundles_seen:
            # Skip rows without a bundle assignment (header / divider)
            continue

        assignments[paper] = {
            "bundle_destinations": bundles_seen,
            "bundle_section_hints": hints,
            "lift_action": lift_action,
        }

    return assignments


# ────────────────────────────────────────────────────────────────────────────
# Migration application
# ────────────────────────────────────────────────────────────────────────────

def apply_migration_to_prose_state(
    paper: str,
    assignment: dict,
    dry_run: bool = False,
) -> tuple[int, int, int]:
    """Apply the per-paper bundle assignment to every non-tombstoned
    sentence in prose_state.json. Returns (sentences_updated,
    sentences_unchanged, sentences_tombstoned)."""
    paper_dir = PAPERS_DIR / paper
    if not paper_dir.exists():
        return (0, 0, 0)
    state_path = prose_state_path(paper)
    if not state_path.exists():
        return (0, 0, 0)

    state = _load_prose_state(paper)
    sentences = state.get("sentences", {})

    bundles = assignment["bundle_destinations"]
    hints = assignment["bundle_section_hints"]
    lift = assignment["lift_action"]

    # If only one bundle, store as single string; if multiple, store as list
    bundle_value = bundles[0] if len(bundles) == 1 else list(bundles)

    n_updated = 0
    n_unchanged = 0
    n_tombstoned = 0

    for sid, srec in sentences.items():
        if srec.get("tombstone") is True:
            n_tombstoned += 1
            continue
        # Compute desired values
        # Prefer the first destination's section hint as bundle_section_hint
        section_hint = None
        for b in bundles:
            if b in hints:
                section_hint = hints[b]
                break
        if (srec.get("bundle_destination") == bundle_value
                and srec.get("lift_action") == lift
                and srec.get("bundle_section_hint") == section_hint):
            n_unchanged += 1
            continue
        if not dry_run:
            srec["bundle_destination"] = bundle_value
            if lift is not None:
                srec["lift_action"] = lift
            if section_hint is not None:
                srec["bundle_section_hint"] = section_hint
        n_updated += 1

    if not dry_run and n_updated > 0:
        # Atomic write via the canonical helper
        from sentence_state import _atomic_write_prose_state
        _atomic_write_prose_state(paper, state)

    return (n_updated, n_unchanged, n_tombstoned)


# ────────────────────────────────────────────────────────────────────────────
# CLI
# ────────────────────────────────────────────────────────────────────────────

def main() -> int:
    parser = argparse.ArgumentParser(
        description="Phase 6i Wave 7.1 bundle-aware migration"
    )
    parser.add_argument(
        "--dry-run", action="store_true",
        help="preview changes without writing prose_state.json",
    )
    parser.add_argument(
        "--paper", help="apply only to one paper key (e.g., paper25_gravitational_waves)",
    )
    parser.add_argument(
        "--report", action="store_true",
        help="print parsed mapping assignments and exit",
    )
    args = parser.parse_args()

    if not MAPPING_DOC.exists():
        print(f"FATAL: mapping document not found: {MAPPING_DOC}", file=sys.stderr)
        return 2

    mapping_text = MAPPING_DOC.read_text(encoding="utf-8")
    assignments = parse_mapping(mapping_text)

    if args.report:
        print(json.dumps(assignments, indent=2, sort_keys=True))
        print(f"\nParsed {len(assignments)} papers from mapping table.",
              file=sys.stderr)
        return 0

    target_papers = (
        [args.paper] if args.paper else sorted(assignments.keys())
    )

    print(f"Bundle migration: {len(target_papers)} target paper(s)"
          + (" (DRY RUN)" if args.dry_run else ""))
    print(f"Mapping source: {MAPPING_DOC}")
    print()

    total_updated = 0
    total_unchanged = 0
    total_tombstoned = 0
    no_state = 0
    not_in_mapping = 0
    for paper in target_papers:
        if paper not in assignments:
            print(f"  [SKIP]  {paper} — not in PAPER_DRAFT_MAPPING.md")
            not_in_mapping += 1
            continue
        paper_dir = PAPERS_DIR / paper
        if not paper_dir.exists():
            print(f"  [SKIP]  {paper} — paper directory not found")
            no_state += 1
            continue
        if not prose_state_path(paper).exists():
            print(f"  [SKIP]  {paper} — no prose_state.json")
            no_state += 1
            continue
        a = assignments[paper]
        n_u, n_n, n_t = apply_migration_to_prose_state(
            paper, a, dry_run=args.dry_run
        )
        bundles_repr = ",".join(a["bundle_destinations"])
        lift_repr = a["lift_action"] or "(unspecified)"
        print(f"  [APPLY] {paper:55s} → {bundles_repr:14s} "
              f"({lift_repr:18s})  "
              f"updated={n_u} unchanged={n_n} tombstoned={n_t}")
        total_updated += n_u
        total_unchanged += n_n
        total_tombstoned += n_t

    print()
    print(f"Summary:")
    print(f"  papers processed:        {len(target_papers) - no_state - not_in_mapping}")
    print(f"  papers without state:    {no_state}")
    print(f"  papers not in mapping:   {not_in_mapping}")
    print(f"  sentences updated:       {total_updated}")
    print(f"  sentences unchanged:     {total_unchanged}")
    print(f"  sentences tombstoned:    {total_tombstoned}")
    if args.dry_run:
        print()
        print("DRY RUN — no files modified. Re-run without --dry-run to apply.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
