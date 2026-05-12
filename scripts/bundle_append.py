#!/usr/bin/env python3
"""
bundle_append.py — Phase 7a sub-wave 7a.1.3 deliverable
=======================================================

Semi-automated tool for absorbing a new source paper into an
already-drafted bundle, or for recording bookkeeping-only events
(non-content-changing drift acknowledgements). Three modes:

  - **Initial lift**: bundle directory has no `paper_draft.tex` yet;
    creates a minimal `paper_draft.tex` skeleton, runs
    `scripts/bundle_source_manifest.py` to bootstrap bookkeeping,
    appends the first source's section.
  - **Append (additive)**: bundle has been drafted; appends a new
    section / subsection to `paper_draft.tex` for a newly-mapped
    source paper. Per Pipeline Invariant #14, the source paper must
    already have a row in `docs/PAPER_DRAFT_MAPPING.md` mapping it to
    `<bundle>`.
  - **Bookkeeping-only** (`--bookkeeping-only`): records a freshness /
    prose-revision / inline-absorption event in `append_log.json` +
    `change_log.md`, bumps `last_lift`, and resets `freshness_stale =
    false` *without* inserting a `\\section` and *without* flipping
    stage9/10/13 statuses to pending. Use when source-paper mtimes
    drifted but bundle content was already correct (verified case:
    auto-regenerated tables; or per-paper prose revisions that didn't
    have a counterpart in the bundle draft). Required: `--lift-action`
    and `--notes`. Optional: `--source-paper` (use a sentinel like
    `none` or omit).

Effects (full-lift modes):
  - validates source ↔ bundle mapping
  - computes the next `\\section` / `\\subsection` heading using the
    `--insertion-point` hint (e.g., "§13", "§§4.2")
  - appends the heading + a stub body to `papers/<bundle>/paper_draft.tex`
  - appends an entry to `papers/<bundle>/append_log.json`
  - appends a dated H2 to `papers/<bundle>/change_log.md`
  - re-runs `scripts/bundle_source_manifest.py --bundle <bundle>` to
    refresh `source_manifest.md` + `bundle_metadata.json`
  - sets `bundle_metadata.json.stage13_redo_required = true` and
    `last_lift = <now>`

Effects (bookkeeping-only mode):
  - appends an entry to `papers/<bundle>/append_log.json` with
    `stage13_redo_required = false` and a `(bookkeeping)` source marker
  - appends a dated H2 to `papers/<bundle>/change_log.md`
  - re-runs `scripts/bundle_source_manifest.py --bundle <bundle>`
  - sets `last_lift = <now>` and `freshness_stale = false`
  - **does NOT** touch `paper_draft.tex` or flip stage9/10/13 statuses

Effects NOT done by this script (out of scope; deferred to manual or
later sub-waves):
  - sentence_state migration (Phase 6i Wave 7.1; run
    `scripts/bundle_migration.py --paper <source>` separately)
  - bibliography merge (per BUNDLE_LIFT_PROCEDURE.md §5)
  - figure copy (per BUNDLE_LIFT_PROCEDURE.md §6)
  - actual prose lift from source (manual; the script appends a stub
    section only)

Refer to `docs/BUNDLE_LIFT_PROCEDURE.md` §3 for the full lift workflow
context. This script is one mechanical step in that procedure.

Usage
-----
    # Initial lift / additive lift
    uv run python scripts/bundle_append.py \\
        --bundle D5 --source-paper paper17_dark_sector \\
        --insertion-point '§2-§3' \\
        --notes "Initial lift; paper17 SFDM cluster-merger forecast"

    uv run python scripts/bundle_append.py \\
        --bundle D5 --source-paper paper29_bbn_unified \\
        --insertion-point '§4'

    uv run python scripts/bundle_append.py \\
        --bundle I1 --source-paper paper15_methodology \\
        --insertion-point '§1' --initial-lift

    # Bookkeeping-only event (no content change)
    uv run python scripts/bundle_append.py \\
        --bundle D1 --bookkeeping-only \\
        --lift-action Freshness-bookkeeping \\
        --notes "Auto-gen tables in source papers regenerated; bundle does not \\input source tables; no content change required."
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent
PAPERS_DIR = PROJECT_ROOT / "papers"
MAPPING_DOC = PROJECT_ROOT / "docs" / "PAPER_DRAFT_MAPPING.md"

sys.path.insert(0, str(PROJECT_ROOT / "scripts"))
from bundle_migration import parse_mapping  # noqa: E402
from sentence_state import _VALID_BUNDLE_TARGETS  # noqa: E402


def _now_iso() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _bundle_dir(bundle: str) -> Path:
    return PAPERS_DIR / bundle


def _source_paper_dir(source: str) -> Path:
    return PAPERS_DIR / source


def _source_title_from_mapping(source: str) -> str:
    """Extract the source paper's mapping title (col 2) from
    PAPER_DRAFT_MAPPING.md if available, else fallback to a derived
    name from the directory key."""
    text = MAPPING_DOC.read_text()
    pat = re.compile(
        rf"^\|\s*`{re.escape(source)}`(?:\s*\([^)]+\))?\s*\|\s*"
        r"(?P<title>[^|]*?)\s*\|",
        re.MULTILINE,
    )
    m = pat.search(text)
    if m:
        title = m.group("title").strip().strip("*")
        # Mapping titles are sometimes paragraph-length; truncate at the
        # first natural break (em-dash, colon, semicolon, or 80 chars).
        for sep in (" — ", ": ", "; ", " ("):
            if sep in title:
                title = title.split(sep, 1)[0]
                break
        if len(title) > 80:
            title = title[:77].rstrip() + "..."
        return title
    # Fallback: humanize the directory key
    parts = source.split("_", 1)
    return parts[1].replace("_", " ").title() if len(parts) > 1 else source


def _ensure_paper_draft_skeleton(bundle: str, metadata: dict) -> Path:
    """Create papers/<bundle>/paper_draft.tex if it doesn't exist."""
    bdir = _bundle_dir(bundle)
    draft = bdir / "paper_draft.tex"
    if draft.exists():
        return draft

    title = metadata.get("title", bundle)
    journal = metadata.get("target_journal", "")
    skeleton = f"""\\documentclass[aps,prd,reprint,nofootinbib,superscriptaddress]{{revtex4-2}}

\\usepackage{{graphicx}}
\\usepackage{{hyperref}}
\\usepackage{{amsmath, amssymb}}
\\usepackage{{booktabs}}

%% Bundle-skeleton header (Phase 7a sub-wave 7a.1.3)
%% Bundle target: {bundle} (tier {metadata.get('tier', '?')}, journal {journal})
%% Generated: {_now_iso()}
%% Schema: docs/BUNDLE_DIRECTORY_SCHEMA.md
%% Source manifest: papers/{bundle}/source_manifest.md
%% Change log: papers/{bundle}/change_log.md
%% Append log: papers/{bundle}/append_log.json (machine-readable)

\\begin{{document}}

\\title{{{title}}}

\\author{{John Roehm}}

\\begin{{abstract}}
TODO: bundle abstract.
\\end{{abstract}}

\\maketitle

%% ─────────────────────────────────────────────────────────────────────
%% Sections appended below by `scripts/bundle_append.py` invocations.
%% Each lift inserts at the heading location specified by the lift
%% command's --insertion-point. Manual edits welcome between lifts.
%% ─────────────────────────────────────────────────────────────────────

\\section{{Introduction}}

TODO: bundle introduction.

%% BUNDLE_APPEND_INSERT_HERE — bundle_append.py inserts new sections at
%% this marker by default. To insert at a specific section, edit the
%% body manually after the script runs.

\\bibliography{{bibliography}}
\\bibliographystyle{{apsrev4-2}}

\\end{{document}}
"""
    draft.write_text(skeleton)
    return draft


def _insertion_marker_pattern() -> re.Pattern:
    return re.compile(r"%% BUNDLE_APPEND_INSERT_HERE.*?$", re.MULTILINE)


def _append_section_to_draft(
    draft: Path,
    *,
    bundle: str,
    source: str,
    source_title: str,
    insertion_point: str,
    notes: str,
) -> tuple[bool, str]:
    """Insert a new \\section / \\subsection skeleton into paper_draft.tex
    at the BUNDLE_APPEND_INSERT_HERE marker (default) or after the most
    recent \\section if the marker is missing.

    Returns (modified, msg).
    """
    text = draft.read_text()

    # Detect section vs subsection from insertion_point hint
    is_subsection = (
        insertion_point.startswith("§§")
        or "subsection" in insertion_point.lower()
    )
    cmd = "subsection" if is_subsection else "section"

    section_block = f"""
%% ─── Lifted from {source} ({insertion_point}) — {_now_iso()} ───
\\{cmd}{{{source_title}}}
\\label{{sec:{bundle.lower()}-{source}}}

%% Insertion point hint from PAPER_DRAFT_MAPPING.md: {insertion_point}
%% Lift notes: {notes or '(none)'}
%% TODO: lift content from papers/{source}/paper_draft.tex
%% TODO: ensure all numerical claims trace via formulas.py / counts.tex
%% TODO: ensure all citations have primary-source cache entries

%% ─── End lift from {source} ───
"""

    marker = _insertion_marker_pattern()
    m = marker.search(text)
    if m:
        new_text = text[: m.start()] + section_block + "\n" + text[m.start():]
    else:
        # Fallback: insert before \bibliography
        bib_match = re.search(r"^\\bibliography\{", text, re.MULTILINE)
        if bib_match:
            new_text = text[: bib_match.start()] + section_block + "\n" + text[bib_match.start():]
        else:
            # Last resort: append before \end{document}
            end_match = re.search(r"^\\end\{document\}", text, re.MULTILINE)
            if not end_match:
                return (False, "could not locate insertion site (no marker, "
                               "no \\bibliography, no \\end{document})")
            new_text = text[: end_match.start()] + section_block + "\n" + text[end_match.start():]

    draft.write_text(new_text)
    return (True, f"appended \\{cmd}{{{source_title}}} ({insertion_point})")


def _append_to_change_log(
    bundle: str, source: str, source_title: str,
    insertion_point: str, lift_action: str, notes: str,
) -> None:
    log_path = _bundle_dir(bundle) / "change_log.md"
    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    entry = f"""
## {today} — {lift_action} from `{source}` ({insertion_point})

- Source title: {source_title}
- Lift action: {lift_action}
- Insertion point: {insertion_point}
- Stage-13 redo required: yes
- Notes: {notes or "(none)"}
"""
    if log_path.exists():
        log_path.write_text(log_path.read_text().rstrip() + "\n" + entry)
    else:
        log_path.write_text(f"# Bundle {bundle} — Change Log\n" + entry)


def _append_to_append_log(
    bundle: str, source: str, lift_action: str, insertion_point: str,
    notes: str, lean_modules: list[str],
) -> None:
    log_path = _bundle_dir(bundle) / "append_log.json"
    if log_path.exists():
        data = json.loads(log_path.read_text())
    else:
        data = {"bundle_target": bundle, "events": []}
    event = {
        "date": _now_iso(),
        "source_paper": source,
        "lift_action": lift_action,
        "bundle_section_inserted": insertion_point,
        "lean_modules_referenced": lean_modules,
        "citation_count_added": 0,  # filled in by manual citation-merge step
        "stage13_redo_required": True,
        "agent_run_id": f"bundle_append-{_now_iso()}",
        "notes": notes,
    }
    data["events"].append(event)
    log_path.write_text(json.dumps(data, indent=2) + "\n")


def _update_metadata_post_append(bundle: str) -> None:
    """Mark bundle as needing Stage-13 re-review and refresh last_lift."""
    md_path = _bundle_dir(bundle) / "bundle_metadata.json"
    if not md_path.exists():
        return
    md = json.loads(md_path.read_text())
    now = _now_iso()
    md["last_lift"] = now
    md["stage13_redo_required"] = True
    md["freshness_stale"] = False  # we just lifted; no longer stale
    # Stages 9/10/13 transition back to pending until re-review confirms
    if md.get("stage13_status") == "green":
        md["stage13_status"] = "pending"
    if md.get("stage9_status") == "green":
        md["stage9_status"] = "pending"
    if md.get("stage10_status") == "green":
        md["stage10_status"] = "pending"
    md_path.write_text(json.dumps(md, indent=2) + "\n")


def _append_to_change_log_bookkeeping(
    bundle: str, lift_action: str, notes: str, source: str,
) -> None:
    """Bookkeeping-only variant of `_append_to_change_log`: no insertion
    point, explicit Stage-13-redo-required = no, source marker indicates
    bookkeeping."""
    log_path = _bundle_dir(bundle) / "change_log.md"
    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    src_marker = f"`{source}`" if source else "(none — bookkeeping event)"
    entry = f"""
## {today} — {lift_action} (bookkeeping)

- Source: {src_marker}
- Lift action: {lift_action}
- Insertion point: (n/a)
- Stage-13 redo required: no
- Notes: {notes or "(none)"}
"""
    if log_path.exists():
        log_path.write_text(log_path.read_text().rstrip() + "\n" + entry)
    else:
        log_path.write_text(f"# Bundle {bundle} — Change Log\n" + entry)


def _append_to_append_log_bookkeeping(
    bundle: str, lift_action: str, notes: str, source: str,
) -> None:
    """Bookkeeping-only variant of `_append_to_append_log`: empty
    lean_modules, `stage13_redo_required = false`, source marker
    indicates bookkeeping."""
    log_path = _bundle_dir(bundle) / "append_log.json"
    if log_path.exists():
        data = json.loads(log_path.read_text())
    else:
        data = {"bundle_target": bundle, "events": []}
    event = {
        "date": _now_iso(),
        "source_paper": source or "(none — bookkeeping)",
        "lift_action": lift_action,
        "bundle_section_inserted": "(n/a — bookkeeping)",
        "lean_modules_referenced": [],
        "citation_count_added": 0,
        "stage13_redo_required": False,
        "agent_run_id": f"bundle_append-bookkeeping-{_now_iso()}",
        "notes": notes,
    }
    data["events"].append(event)
    log_path.write_text(json.dumps(data, indent=2) + "\n")


def _update_metadata_post_bookkeeping(bundle: str) -> None:
    """Bookkeeping variant of `_update_metadata_post_append`: refreshes
    `last_lift` and clears `freshness_stale`, but does NOT flip
    stage9/10/13 statuses and does NOT set `stage13_redo_required`."""
    md_path = _bundle_dir(bundle) / "bundle_metadata.json"
    if not md_path.exists():
        return
    md = json.loads(md_path.read_text())
    md["last_lift"] = _now_iso()
    md["freshness_stale"] = False
    md_path.write_text(json.dumps(md, indent=2) + "\n")


def _refresh_source_manifest(bundle: str) -> None:
    """Re-run bundle_source_manifest.py to refresh the manifest after
    append. Use subprocess so we don't tightly couple imports."""
    subprocess.run(
        ["uv", "run", "python", "scripts/bundle_source_manifest.py",
         "--bundle", bundle],
        cwd=str(PROJECT_ROOT),
        check=True,
        capture_output=True,
    )


def append(
    *,
    bundle: str,
    source: str,
    insertion_point: str,
    notes: str = "",
    lean_modules: list[str] | None = None,
    initial_lift: bool = False,
) -> int:
    """Run a single append operation. Returns 0 on success, nonzero on
    error."""
    if bundle not in _VALID_BUNDLE_TARGETS:
        print(f"FATAL: invalid bundle {bundle!r}", file=sys.stderr)
        return 2

    if not _source_paper_dir(source).exists():
        print(f"WARN: source paper directory papers/{source}/ not found "
              f"(continuing — may be a Lean-module-only source)",
              file=sys.stderr)

    # Validate mapping
    assignments = parse_mapping(MAPPING_DOC.read_text())
    a = assignments.get(source)
    if a is None:
        print(f"FATAL: source paper {source!r} has no row in "
              f"`docs/PAPER_DRAFT_MAPPING.md` — Pipeline Invariant #14 "
              f"requires bundle assignment before lift.",
              file=sys.stderr)
        return 2
    if bundle not in a["bundle_destinations"]:
        print(f"FATAL: source {source!r} is mapped to "
              f"{a['bundle_destinations']}, not {bundle!r}",
              file=sys.stderr)
        return 2

    lift_action = a.get("lift_action") or "Lift-section"
    source_title = _source_title_from_mapping(source)

    # Bootstrap bookkeeping if missing
    bdir = _bundle_dir(bundle)
    md_path = bdir / "bundle_metadata.json"
    if not md_path.exists():
        # Run bundle_source_manifest.py --init to create the bookkeeping
        subprocess.run(
            ["uv", "run", "python", "scripts/bundle_source_manifest.py",
             "--init", bundle],
            cwd=str(PROJECT_ROOT),
            check=True,
            capture_output=True,
        )
    metadata = json.loads(md_path.read_text())

    # Ensure paper_draft.tex skeleton exists
    draft = _ensure_paper_draft_skeleton(bundle, metadata)
    if initial_lift and not draft.exists():
        print(f"FATAL: --initial-lift requested but skeleton not created",
              file=sys.stderr)
        return 2

    # Append the section
    ok, msg = _append_section_to_draft(
        draft,
        bundle=bundle,
        source=source,
        source_title=source_title,
        insertion_point=insertion_point,
        notes=notes,
    )
    if not ok:
        print(f"FATAL: append to paper_draft.tex failed: {msg}",
              file=sys.stderr)
        return 2

    # Update bookkeeping
    _append_to_change_log(
        bundle, source, source_title, insertion_point, lift_action, notes
    )
    _append_to_append_log(
        bundle, source, lift_action, insertion_point, notes,
        lean_modules or [],
    )
    _update_metadata_post_append(bundle)
    _refresh_source_manifest(bundle)

    print(f"  [APPEND] {bundle} ← {source}  ({insertion_point})  "
          f"lift_action={lift_action}")
    print(f"           {msg}")
    print(f"           paper_draft.tex: {draft.relative_to(PROJECT_ROOT)}")
    print(f"           Stage-13 redo flagged. Re-run reviewer triple before bundle close.")
    return 0


def bookkeeping_only(
    *,
    bundle: str,
    lift_action: str,
    notes: str,
    source: str = "",
) -> int:
    """Record a bookkeeping-only event (no content change). Bumps
    `last_lift`, clears `freshness_stale`, appends event rows to
    `append_log.json` + `change_log.md`. Does NOT touch
    `paper_draft.tex` and does NOT flip stage9/10/13 statuses.

    Returns 0 on success, nonzero on error."""
    if bundle not in _VALID_BUNDLE_TARGETS:
        print(f"FATAL: invalid bundle {bundle!r}", file=sys.stderr)
        return 2

    md_path = _bundle_dir(bundle) / "bundle_metadata.json"
    if not md_path.exists():
        print(f"FATAL: papers/{bundle}/bundle_metadata.json missing; cannot "
              f"book-keep a bundle that hasn't been bootstrapped",
              file=sys.stderr)
        return 2

    if not notes.strip():
        print("FATAL: --notes is required for --bookkeeping-only (the notes "
              "field is the only signal explaining why no content changed)",
              file=sys.stderr)
        return 2

    _append_to_change_log_bookkeeping(bundle, lift_action, notes, source)
    _append_to_append_log_bookkeeping(bundle, lift_action, notes, source)
    _update_metadata_post_bookkeeping(bundle)
    _refresh_source_manifest(bundle)

    print(f"  [BOOKKEEPING] {bundle}  lift_action={lift_action}")
    print(f"                last_lift bumped; freshness_stale cleared; "
          f"stages untouched.")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Phase 7a sub-wave 7a.1.3: append a new source paper into "
            "an already-drafted (or fresh) bundle, OR record a "
            "bookkeeping-only event (--bookkeeping-only)."
        )
    )
    parser.add_argument("--bundle", required=True,
                        help="bundle target (e.g., D5, I1)")
    parser.add_argument("--source-paper", default="",
                        help="source paper directory key (e.g., paper17_dark_sector); "
                             "required in lift modes, optional in --bookkeeping-only")
    parser.add_argument("--insertion-point", default="",
                        help="section / subsection hint (e.g., '§2-§3', '§§4.2'); "
                             "required in lift modes, ignored in --bookkeeping-only")
    parser.add_argument("--notes", default="",
                        help="lift notes (free-form, recorded in change_log.md); "
                             "required when --bookkeeping-only is set")
    parser.add_argument("--lean-modules", default="",
                        help="comma-separated Lean module names referenced (e.g., "
                             "'CausalSetDarkEnergy,EntropicGravityDarkEnergy'); "
                             "lift-mode only")
    parser.add_argument("--initial-lift", action="store_true",
                        help="bundle has no paper_draft.tex yet; bootstrap skeleton")
    parser.add_argument("--bookkeeping-only", action="store_true",
                        help="record a bookkeeping-only event (no \\section "
                             "insertion, no stage flips); requires --lift-action "
                             "and --notes")
    parser.add_argument("--lift-action", default="",
                        help="lift action name recorded in append_log.json and "
                             "change_log.md (e.g., 'Freshness-bookkeeping', "
                             "'Prose-revision-bookkeeping'); required for "
                             "--bookkeeping-only, inherited from "
                             "PAPER_DRAFT_MAPPING.md in lift modes")
    args = parser.parse_args()

    if args.bookkeeping_only:
        if not args.lift_action:
            print("FATAL: --lift-action is required when --bookkeeping-only "
                  "is set", file=sys.stderr)
            return 2
        return bookkeeping_only(
            bundle=args.bundle,
            lift_action=args.lift_action,
            notes=args.notes,
            source=args.source_paper,
        )

    if not args.source_paper:
        print("FATAL: --source-paper is required in lift mode (omit it only "
              "with --bookkeeping-only)", file=sys.stderr)
        return 2
    if not args.insertion_point:
        print("FATAL: --insertion-point is required in lift mode",
              file=sys.stderr)
        return 2

    lean_modules = [m.strip() for m in args.lean_modules.split(",") if m.strip()]
    return append(
        bundle=args.bundle,
        source=args.source_paper,
        insertion_point=args.insertion_point,
        notes=args.notes,
        lean_modules=lean_modules,
        initial_lift=args.initial_lift,
    )


if __name__ == "__main__":
    raise SystemExit(main())
