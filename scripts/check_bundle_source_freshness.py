#!/usr/bin/env python3
"""
check_bundle_source_freshness.py — Phase 7a sub-wave 7a.1.4 deliverable
=======================================================================

Implementation of `validate.py --check bundle_source_freshness` (CHECK 22).

For every bundle directory under `papers/<bundle>/`:

  - Read `bundle_metadata.json` to find `last_lift` timestamp.
  - For each source paper mapped to the bundle (per PAPER_DRAFT_MAPPING.md),
    compute the latest mtime under `papers/<source>/` (excluding
    bookkeeping caches).
  - If any source mtime is newer than the bundle's `last_lift`,
    the bundle is `freshness-stale` — flag at WARN level.

Also detects:
  - bundles with `bundle_metadata.json.stage13_redo_required = true`
    (set by `bundle_append.py`; cleared by Stage-13 reviewer agent
    after re-review).

Default: advisory; promotable to FAIL at the Phase 8 submission gate
via `validate.py --strict`.

Schema reference: `docs/BUNDLE_DIRECTORY_SCHEMA.md`.

This module exposes a single public function `check()` that returns a
list of per-bundle finding dicts. `validate.py` consumes it via
`@register_check("bundle_source_freshness", ...)`.
"""
from __future__ import annotations

import json
import sys
from datetime import datetime, timezone
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent
PAPERS_DIR = PROJECT_ROOT / "papers"
MAPPING_DOC = PROJECT_ROOT / "docs" / "PAPER_DRAFT_MAPPING.md"

sys.path.insert(0, str(PROJECT_ROOT / "scripts"))


def _parse_iso(s: str | None) -> datetime | None:
    if not s:
        return None
    try:
        # Accept both "2026-04-30T12:00:00Z" and "...+00:00"
        if s.endswith("Z"):
            return datetime.strptime(s, "%Y-%m-%dT%H:%M:%SZ").replace(
                tzinfo=timezone.utc
            )
        return datetime.fromisoformat(s)
    except (ValueError, TypeError):
        return None


def _latest_source_mtime(source: str) -> datetime | None:
    """Return the latest mtime of any meaningful file under
    papers/<source>/, or None if the directory is missing/empty."""
    pdir = PAPERS_DIR / source
    if not pdir.exists():
        return None
    latest = 0.0
    for p in pdir.rglob("*"):
        if not p.is_file():
            continue
        if any(part.startswith(".") or part == "__pycache__" for part in p.parts):
            continue
        # Skip bundle-bookkeeping files when source happens to be a
        # bundle (it shouldn't, but be defensive).
        if p.name in {"bundle_metadata.json", "append_log.json"}:
            continue
        latest = max(latest, p.stat().st_mtime)
    if latest == 0.0:
        return None
    return datetime.fromtimestamp(latest, timezone.utc)


def check() -> list[dict]:
    """Run the freshness check across all bundle directories.

    Returns a list of finding dicts, each:
      {
        "bundle": str,
        "passed": bool,
        "warning": bool,    # advisory only
        "message": str,
      }

    Empty list means: no bundle directories found yet (acceptable
    pre-Phase-7-execution state).
    """
    from bundle_migration import parse_mapping
    from sentence_state import _VALID_BUNDLE_TARGETS

    if not MAPPING_DOC.exists():
        return [{
            "bundle": "_meta",
            "passed": False,
            "warning": False,
            "message": f"PAPER_DRAFT_MAPPING.md not found at {MAPPING_DOC}",
        }]

    assignments = parse_mapping(MAPPING_DOC.read_text())

    findings: list[dict] = []
    for bundle in sorted(_VALID_BUNDLE_TARGETS):
        bdir = PAPERS_DIR / bundle
        md_path = bdir / "bundle_metadata.json"
        if not md_path.exists():
            # No bookkeeping yet → bundle hasn't been initialized.
            # This is acceptable pre-Phase-7-execution; not a finding.
            continue

        try:
            md = json.loads(md_path.read_text())
        except (json.JSONDecodeError, OSError) as exc:
            findings.append({
                "bundle": bundle,
                "passed": False,
                "warning": False,
                "message": f"failed to read bundle_metadata.json: {exc}",
            })
            continue

        last_lift = _parse_iso(md.get("last_lift"))

        # Sub-finding A: stage13_redo_required flag
        if md.get("stage13_redo_required") is True:
            findings.append({
                "bundle": bundle,
                "passed": True,
                "warning": True,
                "message": (
                    "stage13_redo_required=true (set by bundle_append.py); "
                    "Stage-13 reviewer agent must re-clear before bundle close"
                ),
            })

        # Sub-finding B: source-paper mtime newer than last_lift
        if last_lift is None:
            # Bundle initialized but never appended → freshness check
            # is not applicable (no lifts to compare against).
            findings.append({
                "bundle": bundle,
                "passed": True,
                "warning": False,
                "message": "bundle initialized; no lifts yet (skip)",
            })
            continue

        sources = sorted([
            p for p, a in assignments.items()
            if bundle in a["bundle_destinations"]
        ])
        stale_sources: list[tuple[str, datetime]] = []
        for src in sources:
            mt = _latest_source_mtime(src)
            if mt is not None and mt > last_lift:
                stale_sources.append((src, mt))

        if stale_sources:
            sample = ", ".join(
                f"{s}({mt.strftime('%Y-%m-%d')})"
                for s, mt in stale_sources[:3]
            )
            extra = (
                f" ... and {len(stale_sources) - 3} more"
                if len(stale_sources) > 3 else ""
            )
            findings.append({
                "bundle": bundle,
                "passed": True,
                "warning": True,
                "message": (
                    f"freshness-stale: {len(stale_sources)} of {len(sources)} "
                    f"source paper(s) modified after last_lift "
                    f"({last_lift.strftime('%Y-%m-%d')}); "
                    f"sample: {sample}{extra}"
                ),
            })
            # Set freshness_stale=true in metadata so dashboard reflects it
            try:
                md["freshness_stale"] = True
                md_path.write_text(json.dumps(md, indent=2) + "\n")
            except OSError:
                pass
        else:
            findings.append({
                "bundle": bundle,
                "passed": True,
                "warning": False,
                "message": (
                    f"fresh: all {len(sources)} source paper(s) older than "
                    f"last_lift ({last_lift.strftime('%Y-%m-%d')})"
                ),
            })
            # Clear stale flag if previously set
            if md.get("freshness_stale"):
                md["freshness_stale"] = False
                try:
                    md_path.write_text(json.dumps(md, indent=2) + "\n")
                except OSError:
                    pass

    return findings


def main() -> int:
    """Standalone CLI: run the check, print findings, exit 0 always
    (advisory). Return non-zero only on hard errors."""
    findings = check()
    if not findings:
        print("CHECK 22 (bundle_source_freshness): no bundle directories "
              "found; pre-Phase-7-execution state — skip.")
        return 0

    print(f"CHECK 22 (bundle_source_freshness): {len(findings)} sub-finding(s)")
    for f in findings:
        if not f["passed"]:
            tag = "FAIL"
        elif f["warning"]:
            tag = "WARN"
        else:
            tag = "PASS"
        print(f"  [{tag}] {f['bundle']}: {f['message']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
