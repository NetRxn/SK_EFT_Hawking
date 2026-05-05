#!/usr/bin/env python3
"""
bundle_source_manifest.py — Phase 7a sub-wave 7a.1.2 deliverable
================================================================

Auto-generates `papers/<bundle>/source_manifest.md` for one or all
bundles by reading `docs/PAPER_DRAFT_MAPPING.md` and filtering by bundle
target. Also initializes `papers/<bundle>/bundle_metadata.json` and
`papers/<bundle>/append_log.json` on first run, and refreshes
`source_manifest_last_regen` on every subsequent run.

Schema reference: `docs/BUNDLE_DIRECTORY_SCHEMA.md` (Phase 7a sub-wave
7a.1.1). Consumers: `scripts/bundle_append.py`,
`scripts/check_bundle_source_freshness.py`,
`scripts/datastar_bundles.py`, the bundle reviewer agents.

Usage
-----
    uv run python scripts/bundle_source_manifest.py             # all bundles
    uv run python scripts/bundle_source_manifest.py --bundle I1 # one bundle
    uv run python scripts/bundle_source_manifest.py --init I1   # initialize files only
    uv run python scripts/bundle_source_manifest.py --report    # report parsed mapping; no writes

This script does NOT mutate `paper_draft.tex` or any source-paper file.
It only writes/refreshes the bundle's own bookkeeping files.
"""
from __future__ import annotations

import argparse
import json
import sys
from datetime import datetime, timezone
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent
PAPERS_DIR = PROJECT_ROOT / "papers"
MAPPING_DOC = PROJECT_ROOT / "docs" / "PAPER_DRAFT_MAPPING.md"
SUPERSESSION_LEDGER = PROJECT_ROOT / "docs" / "review_finding_supersessions.json"

sys.path.insert(0, str(PROJECT_ROOT / "scripts"))
from bundle_migration import parse_mapping  # noqa: E402
from sentence_state import _VALID_BUNDLE_TARGETS  # noqa: E402

# Bundle metadata mirrors `scripts/datastar_bundles.py` (single source of
# truth — if you edit one, edit both, or refactor into a shared module
# in a follow-up wave).
_TIER_OF = {
    "F": 0,
    "D1": 1, "D2": 1, "D3": 1, "D4": 1, "D5": 1,
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
    "L1": "GW170817 / vestigial-graviton",
    "L2": "Three generations from modular invariance",
    "L3": "BCH four laws by regime",
    "I1": "Verification methodology with worked cases",
    "I2": "Verified statistical estimators + lean-tensor-categories",
    "I3": "Verified Stochastic Calculus for Mathlib4 — Stochastic Integral, Quadratic Variation, Itô's Lemma, and Large-Deviation Foundations",
    "E1": "Paris-LKB polariton letter",
    "E2": "Dean-Kim-Lucas graphene letter",
}

_BUNDLE_TARGET_JOURNAL = {
    "F": "Living Rev. Relativity | Phys. Rep.",
    "D1": "PRD",
    "D2": "PRD | JHEP",
    "D3": "PRD",
    "D4": "Comm. Math. Phys. | PRX Quantum",
    "D5": "PRD",
    "L1": "PRL",
    "L2": "PRL",
    "L3": "PRL",
    "I1": "CPC | Phys. Rep.",
    "I2": "JOSS",
    "I3": "JOSS | CPC",
    "E1": "PRL | PRR",
    "E2": "PRL | PRR",
}

# Bundle-target → sub-phase scheduled (per Phase7_Roadmap.md). I1+I2 in 7a;
# D5+L1+L3 in 7b; D3 in 7c; D2+L2 in 7d; D1+E1+E2 in 7e; D4 in 7f; F in 7g.
# I3 in Phase 6o.ζ (community Mathlib4 contribution; out-of-band of the Phase 7 sub-phase ladder).
_BUNDLE_SUBPHASE = {
    "F": "7g",
    "D1": "7e", "D2": "7d", "D3": "7c", "D4": "7f", "D5": "7b",
    "L1": "7b", "L2": "7d", "L3": "7b",
    "I1": "7a", "I2": "7a", "I3": "6o.zeta",
    "E1": "7e", "E2": "7e",
}


def _now_iso() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _bundle_dir(bundle: str) -> Path:
    return PAPERS_DIR / bundle


def _last_source_modification(paper: str) -> str | None:
    """Return the most recent mtime of any file under papers/<paper>/ as
    an ISO-8601 UTC timestamp, or None if the directory does not exist.

    Used both by source_manifest.md (informational) and by CHECK 22
    (`bundle_source_freshness`)."""
    paper_dir = PAPERS_DIR / paper
    if not paper_dir.exists():
        return None
    latest = 0.0
    for p in paper_dir.rglob("*"):
        if not p.is_file():
            continue
        # Skip caches / generated bookkeeping
        if any(part.startswith(".") or part == "__pycache__" for part in p.parts):
            continue
        latest = max(latest, p.stat().st_mtime)
    if latest == 0.0:
        return None
    return datetime.fromtimestamp(latest, timezone.utc).strftime(
        "%Y-%m-%dT%H:%M:%SZ"
    )


def _phase_wave_hint_from_mapping(paper: str, dest_cell: str) -> str:
    """Best-effort phase / wave annotation from the mapping cell.

    The mapping doc embeds Phase / Wave context as parenthetical
    suffixes on paper keys (e.g., `paper17 (Phase 5x W1)`). We don't
    have a separate column for this, so we leave it to "see mapping"
    when no parenthetical is present.
    """
    return ""  # Best-effort; manual annotation acceptable for now.


def initialize_bundle_files(bundle: str, sources: list[str], *, force: bool = False) -> dict:
    """Create papers/<bundle>/ and write the four mandatory bookkeeping
    files: source_manifest.md, append_log.json, bundle_metadata.json,
    change_log.md. Returns the bundle_metadata dict.

    If files already exist, this is a no-op unless `force=True`.
    """
    if bundle not in _VALID_BUNDLE_TARGETS:
        raise ValueError(f"Invalid bundle target {bundle!r}")

    bdir = _bundle_dir(bundle)
    bdir.mkdir(parents=True, exist_ok=True)
    (bdir / "figures").mkdir(exist_ok=True)
    (bdir / "tables").mkdir(exist_ok=True)

    metadata_path = bdir / "bundle_metadata.json"
    append_log_path = bdir / "append_log.json"
    change_log_path = bdir / "change_log.md"

    now = _now_iso()

    # bundle_metadata.json
    if force or not metadata_path.exists():
        metadata = {
            "bundle_target": bundle,
            "tier": _TIER_OF[bundle],
            "title": _BUNDLE_TITLES[bundle],
            "target_journal": _BUNDLE_TARGET_JOURNAL[bundle],
            "phase7_subphase": _BUNDLE_SUBPHASE[bundle],
            "stage9_status": "pending",
            "stage10_status": "pending",
            "stage13_status": "pending",
            "stage13_redo_required": False,
            "freshness_stale": False,
            "source_manifest_last_regen": now,
            "last_lift": None,
            "last_stage9_review": None,
            "last_stage10_review": None,
            "last_stage13_review": None,
            "blockers_open": 0,
            "advisories_open": 0,
            "stage13_review_doc": None,
            "audit_log_path": f"papers/{bundle}/audit_log.jsonl",
            "supersession_ledger_anchor": "docs/review_finding_supersessions.json",
            "notes": None,
        }
        metadata_path.write_text(json.dumps(metadata, indent=2) + "\n")
    else:
        metadata = json.loads(metadata_path.read_text())
        # Refresh the regen timestamp; preserve other fields.
        metadata["source_manifest_last_regen"] = now
        metadata_path.write_text(json.dumps(metadata, indent=2) + "\n")

    # append_log.json
    if force or not append_log_path.exists():
        append_log = {"bundle_target": bundle, "events": []}
        append_log_path.write_text(json.dumps(append_log, indent=2) + "\n")

    # change_log.md
    if force or not change_log_path.exists():
        change_log_path.write_text(
            f"# Bundle {bundle} — Change Log\n\n"
            f"_Initial bookkeeping created {now} by "
            f"`scripts/bundle_source_manifest.py`. Append history accumulates "
            f"as `scripts/bundle_append.py` invocations land._\n"
        )

    # audit_log.jsonl is created lazily by reviewer agents (Stage 9/10);
    # touch it so consumers can `tail` it without a FileNotFoundError.
    audit_log_path = bdir / "audit_log.jsonl"
    if not audit_log_path.exists():
        audit_log_path.touch()

    return metadata


def write_source_manifest(bundle: str, sources: list[str], assignments: dict[str, dict]) -> Path:
    """Write papers/<bundle>/source_manifest.md based on the per-paper
    assignment dict from `bundle_migration.parse_mapping()`."""
    bdir = _bundle_dir(bundle)
    out_path = bdir / "source_manifest.md"

    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    rows = []
    for paper in sorted(sources):
        a = assignments.get(paper, {})
        section = (
            a.get("bundle_section_hints", {}).get(bundle, "(see mapping)")
        )
        lift = a.get("lift_action") or "(unspecified)"
        last_mod = _last_source_modification(paper) or "(missing)"
        rows.append(
            f"| `{paper}` | {section} | {lift} | (see mapping) | {last_mod} |"
        )

    rows_block = (
        "\n".join(rows)
        if rows
        else "| _(no sources mapped)_ | | | | |"
    )

    content = f"""# Bundle {bundle} — Source Manifest

**Auto-generated:** {today}
**Tool:** `scripts/bundle_source_manifest.py`
**Source mapping:** `docs/PAPER_DRAFT_MAPPING.md`
**Bundle anchor list:** `docs/agents/claims-reviewer-bundle-prompts.md` §`{bundle}`
**Schema:** `docs/BUNDLE_DIRECTORY_SCHEMA.md`

## Contributing source papers ({len(sources)})

| Source paper | Bundle section | Lift action | Phase / Wave | Last source modification |
|---|---|---|---|---|
{rows_block}

## Coverage notes

- Insertion points are derived from `PAPER_DRAFT_MAPPING.md`'s "New destination(s)" column.
- "Last source modification" is the latest mtime in `papers/<source>/`, used by `validate.py --check bundle_source_freshness` (CHECK 22).
- `Lift-flagship` rows appear in the F bundle's manifest as well as the source's primary bundle.
- Re-run `scripts/bundle_source_manifest.py --bundle {bundle}` after any change to `docs/PAPER_DRAFT_MAPPING.md` affecting this bundle.

---

*Generated by `scripts/bundle_source_manifest.py` (Phase 7a sub-wave 7a.1.2).*
"""
    out_path.write_text(content)
    return out_path


def regenerate_for_bundle(bundle: str, assignments: dict[str, dict]) -> dict:
    """Init bookkeeping (idempotent) + write source_manifest.md.

    Returns the bundle_metadata.json contents post-regen.
    """
    sources = sorted([
        p for p, a in assignments.items()
        if bundle in a["bundle_destinations"]
    ])
    metadata = initialize_bundle_files(bundle, sources)
    write_source_manifest(bundle, sources, assignments)
    return metadata


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Phase 7a sub-wave 7a.1.2: regenerate "
            "`papers/<bundle>/source_manifest.md` and initialize "
            "`bundle_metadata.json` / `append_log.json` / `change_log.md`."
        )
    )
    parser.add_argument(
        "--bundle",
        help="regenerate one bundle only (default: all 13)",
    )
    parser.add_argument(
        "--init",
        help="initialize bookkeeping files for one bundle (no source manifest)",
    )
    parser.add_argument(
        "--report",
        action="store_true",
        help="print parsed mapping summary (no writes)",
    )
    parser.add_argument(
        "--force",
        action="store_true",
        help="overwrite existing bundle_metadata.json + append_log.json",
    )
    args = parser.parse_args()

    if not MAPPING_DOC.exists():
        print(f"FATAL: {MAPPING_DOC} not found", file=sys.stderr)
        return 2

    assignments = parse_mapping(MAPPING_DOC.read_text())

    if args.report:
        per_bundle: dict[str, list[str]] = {b: [] for b in _VALID_BUNDLE_TARGETS}
        for p, a in assignments.items():
            for b in a["bundle_destinations"]:
                per_bundle[b].append(p)
        for b in sorted(_VALID_BUNDLE_TARGETS, key=lambda x: (_TIER_OF[x], x)):
            print(f"  {b}: {len(per_bundle[b])} sources")
            for p in sorted(per_bundle[b]):
                hint = (assignments[p].get("bundle_section_hints", {})
                        .get(b, ""))
                print(f"    - {p} {hint}")
        return 0

    if args.init:
        if args.init not in _VALID_BUNDLE_TARGETS:
            print(f"FATAL: invalid bundle {args.init!r}", file=sys.stderr)
            return 2
        sources = [p for p, a in assignments.items()
                   if args.init in a["bundle_destinations"]]
        metadata = initialize_bundle_files(args.init, sources, force=args.force)
        print(f"  [INIT]   {args.init} → {_bundle_dir(args.init)}")
        print(f"           tier={metadata['tier']} title={metadata['title'][:60]!r}")
        return 0

    targets = (
        [args.bundle] if args.bundle
        else sorted(_VALID_BUNDLE_TARGETS, key=lambda b: (_TIER_OF[b], b))
    )

    n_ok = 0
    for b in targets:
        if b not in _VALID_BUNDLE_TARGETS:
            print(f"  [SKIP]   {b} — not a valid bundle target")
            continue
        sources = sorted([p for p, a in assignments.items()
                          if b in a["bundle_destinations"]])
        metadata = initialize_bundle_files(b, sources, force=args.force)
        write_source_manifest(b, sources, assignments)
        verdict = "INIT" if metadata.get("last_lift") is None else "REGEN"
        print(f"  [{verdict:5s}]  {b}: {len(sources)} sources → "
              f"{_bundle_dir(b).relative_to(PROJECT_ROOT)}/source_manifest.md")
        n_ok += 1

    print(f"\nProcessed {n_ok} bundle(s); regen timestamp = {_now_iso()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
