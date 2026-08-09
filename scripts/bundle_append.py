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

**A source registration does not create a section (F-02, TODO-D26).** A lift
must name the existing top-level section it belongs under
(`--target-section "<title>"`), and lands as a `\\subsection` inside it.
Creating a new top-level section is a change to the bundle's argument
structure, so it takes `--new-section --section-rationale "<why>"` and the
reason is written into the draft, `change_log.md` and `append_log.json`.
`--initial-lift` implies the new-section path: a bundle with no draft has no
section plan to append into.

Effects (full-lift modes):
  - validates source ↔ bundle mapping
  - resolves `--target-section` against the draft's own top-level sections
    (or takes the explicit `--new-section` path)
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
    # Additive lift into an existing section (the normal case)
    uv run python scripts/bundle_append.py \\
        --bundle D5 --source-paper paper29_bbn_unified \\
        --insertion-point '§4' \\
        --target-section 'Cosmological constraints'

    # A lift that genuinely changes the bundle's architecture
    uv run python scripts/bundle_append.py \\
        --bundle D5 --source-paper paper17_dark_sector \\
        --insertion-point '§2-§3' --new-section \\
        --section-rationale "SFDM cluster-merger forecasts are a distinct \\
                             observational channel; no existing section argues it" \\
        --notes "paper17 SFDM cluster-merger forecast"

    # First lift into an undrafted bundle (implies --new-section)
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
from bundle_json import write_bundle_json  # noqa: E402
from validation._tex import _strip_tex_comments  # noqa: E402


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


# ═══════════════════════════════════════════════════════════════════════
# F-02 — registering a source must not create a section (TODO-D26)
# ═══════════════════════════════════════════════════════════════════════
#
# MEASURED 2026-08-09, across all 21 bundles' `append_log.json`: **74 of 74
# content lifts inserted a top-level `\section`.** The `§§` subsection form the
# old `is_subsection` hint recognised was used ZERO times, because nothing ever
# required it — a source registration silently bought a top-level heading, and
# 28 of those 74 landed in D3, which is exactly how it reached 31 sections.
#
# The fix is NOT to stop inserting a skeleton. `append_log.json`'s
# `bundle_section_inserted` is the anchor the absorption protocol reads to find
# where a lift landed; an append that inserts nothing makes that field a lie.
# The fix is that the anchor must be a *planned* place: an append now attaches a
# `\subsection` inside a section the bundle's architecture already has, and
# creating a new top-level section is an explicit, justified, logged act
# (`--new-section` + `--section-rationale`) rather than the default.
#
# The section plan is read off the draft's own top-level sections rather than a
# separate `CHARTER.md`. A plan stored beside the document it describes drifts
# from it; a plan *read from* the document cannot. The validation this buys is
# the same one the charter was for: you may only append where the architecture
# already has a home, or say out loud that you are changing the architecture.

#: Commands that terminate a top-level section's body.
_SECTION_TERMINATORS = (
    r"\\section\b",
    r"\\appendix\b",
    r"\\bibliography\b",
    r"\\begin\{thebibliography\}",
    r"\\end\{document\}",
)
_TERMINATOR_RE = re.compile("|".join(_SECTION_TERMINATORS))
_SECTION_START_RE = re.compile(r"\\section\*?\s*\{")


def _brace_matched(text: str, open_idx: int) -> tuple[str, int]:
    """Content of the `{...}` group starting at `open_idx`, and the offset just
    past its closing brace.

    Brace matching rather than `[^}]*` because section titles in this corpus
    carry nested groups (`\\mathbb{Z}`, `\\texttt{...}`); a non-greedy character
    class stops at the inner brace and truncates the title.
    """
    depth = 0
    i = open_idx
    while i < len(text):
        c = text[i]
        if c == "\\":
            i += 2
            continue
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0:
                return text[open_idx + 1:i], i + 1
        i += 1
    raise ValueError(f"unbalanced brace group at offset {open_idx}")


def _top_level_sections(text: str) -> list[tuple[str, int, int]]:
    """`(title, heading_start, body_end)` for every top-level `\\section`.

    Scanned against a comment-stripped copy that preserves every offset, so a
    `\\section` inside a `%%` banner (this script writes several) is not seen as
    structure while the offsets still index into the original text.
    """
    scan = _strip_tex_comments(text)
    out: list[tuple[str, int, int]] = []
    for m in _SECTION_START_RE.finditer(scan):
        title, after = _brace_matched(scan, m.end() - 1)
        term = _TERMINATOR_RE.search(scan, after)
        end = term.start() if term else len(scan)
        out.append((title.strip(), m.start(), _back_over_banner(scan, end)))
    return out


def _back_over_banner(scan: str, end: int) -> int:
    """Rewind `end` past the blank and comment lines that introduce whatever
    follows.

    Drafts in this corpus precede each `\\section` with a `%% ===== §N — ... =====`
    banner. Inserting exactly at the terminator drops the new subsection
    *between that banner and the section it announces*, so the banner reads as
    belonging to the wrong body. Comments are already blanked to spaces in
    `scan`, so rewinding over whitespace-only lines covers both cases.
    """
    while end > 0:
        prev_nl = scan.rfind("\n", 0, end - 1)
        line = scan[prev_nl + 1:end - 1] if prev_nl != -1 else scan[:end - 1]
        if line.strip():
            break
        end = prev_nl + 1
        if prev_nl == -1:
            break
    return end


def _resolve_target_section(text: str, wanted: str) -> tuple[str, int]:
    """`(matched_title, insertion_offset)` for the section a lift targets.

    Matching widens exact → case-insensitive → unique substring, and an
    ambiguous or absent name is a hard error listing what the draft actually
    has. Guessing here would put content under the wrong argument, which is the
    failure the target is meant to prevent.
    """
    secs = _top_level_sections(text)
    if not secs:
        raise LookupError("the draft has no top-level \\section to target; "
                          "use --new-section (or --initial-lift)")
    exact = [s for s in secs if s[0] == wanted]
    if not exact:
        exact = [s for s in secs if s[0].lower() == wanted.lower()]
    if not exact:
        exact = [s for s in secs if wanted.lower() in s[0].lower()]
    if len(exact) == 1:
        title, _start, body_end = exact[0]
        return title, body_end
    listing = "\n".join(f"    - {s[0]}" for s in secs)
    if not exact:
        raise LookupError(
            f"no top-level section matches {wanted!r}. The draft's section "
            f"plan is:\n{listing}\n  Append into one of these, or pass "
            f"--new-section --section-rationale '<why the architecture needs a "
            f"new top-level section>'.")
    raise LookupError(
        f"{wanted!r} matches {len(exact)} sections "
        f"({', '.join(repr(s[0]) for s in exact)}); name one exactly.")


def _append_section_to_draft(
    draft: Path,
    *,
    bundle: str,
    source: str,
    source_title: str,
    insertion_point: str,
    notes: str,
    target_section: str = "",
    new_section: bool = False,
    section_rationale: str = "",
) -> tuple[bool, str, str]:
    """Insert a lift skeleton into paper_draft.tex.

    Two shapes, and which one runs is a decision the caller must have made
    (F-02). With `target_section`, a `\\subsection` skeleton lands at the end of
    that existing section's body. With `new_section`, a top-level `\\section`
    lands at the BUNDLE_APPEND_INSERT_HERE marker, falling back to before the
    bibliography and then before `\\end{document}` — and `section_rationale`
    goes into the draft beside it, so the justification for a new heading sits
    where the next reader of the architecture will find it.

    Returns `(modified, msg, anchor)`; `anchor` is the resolved
    `bundle_section_inserted` value, not the caller's hint.
    """
    text = draft.read_text()

    if new_section:
        block = f"""
%% ─── Lifted from {source} ({insertion_point}) — {_now_iso()} ───
\\section{{{source_title}}}
\\label{{sec:{bundle.lower()}-{source}}}

%% NEW TOP-LEVEL SECTION. Rationale: {section_rationale}
%% Insertion point hint from PAPER_DRAFT_MAPPING.md: {insertion_point}
%% Lift notes: {notes or '(none)'}
%% TODO: lift content from papers/{source}/paper_draft.tex
%% TODO: ensure all numerical claims trace via formulas.py / counts.tex
%% TODO: ensure all citations have primary-source cache entries

%% ─── End lift from {source} ───
"""
        m = _insertion_marker_pattern().search(text)
        if m:
            cut = m.start()
        else:
            bib = re.search(r"^\\bibliography\{", text, re.MULTILINE)
            end = re.search(r"^\\end\{document\}", text, re.MULTILINE)
            if bib:
                cut = bib.start()
            elif end:
                cut = end.start()
            else:
                return (False, "could not locate insertion site (no marker, "
                               "no \\bibliography, no \\end{document})", "")
        draft.write_text(text[:cut] + block + "\n" + text[cut:])
        anchor = f"§ (new) {source_title}"
        return (True, f"appended \\section{{{source_title}}} — NEW top-level "
                      f"section, rationale recorded", anchor)

    try:
        matched, cut = _resolve_target_section(text, target_section)
    except LookupError as exc:
        return (False, str(exc), "")

    block = f"""
%% ─── Lifted from {source} ({insertion_point}) — {_now_iso()} ───
\\subsection{{{source_title}}}
\\label{{sec:{bundle.lower()}-{source}}}

%% Appended into the existing section "{matched}" (F-02: a source
%% registration does not create a top-level section).
%% Insertion point hint from PAPER_DRAFT_MAPPING.md: {insertion_point}
%% Lift notes: {notes or '(none)'}
%% TODO: lift content from papers/{source}/paper_draft.tex
%% TODO: ensure all numerical claims trace via formulas.py / counts.tex
%% TODO: ensure all citations have primary-source cache entries

%% ─── End lift from {source} ───
"""
    draft.write_text(text[:cut].rstrip() + "\n" + block + "\n" + text[cut:])
    anchor = f"§ {matched} / §§ {source_title}"
    return (True, f"appended \\subsection{{{source_title}}} into "
                  f"\\section{{{matched}}}", anchor)


def _append_to_change_log(
    bundle: str, source: str, source_title: str,
    insertion_point: str, lift_action: str, notes: str,
    anchor: str = "", section_rationale: str = "",
) -> None:
    log_path = _bundle_dir(bundle) / "change_log.md"
    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    rationale_row = (f"\n- New top-level section rationale: {section_rationale}"
                     if section_rationale else "")
    entry = f"""
## {today} — {lift_action} from `{source}` ({insertion_point})

- Source title: {source_title}
- Lift action: {lift_action}
- Insertion point: {insertion_point}
- Anchor: {anchor or insertion_point}{rationale_row}
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
    anchor: str = "", section_rationale: str = "",
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
        # The RESOLVED anchor, not the caller's hint: the absorption protocol
        # reads this field to find where a lift landed, and a hint like "§13"
        # names a position no reader can locate in the draft.
        "bundle_section_inserted": anchor or insertion_point,
        "insertion_point_hint": insertion_point,
        "new_top_level_section": bool(section_rationale),
        "new_section_rationale": section_rationale,
        "lean_modules_referenced": lean_modules,
        "citation_count_added": 0,  # filled in by manual citation-merge step
        "stage13_redo_required": True,
        "agent_run_id": f"bundle_append-{_now_iso()}",
        "notes": notes,
    }
    data["events"].append(event)
    write_bundle_json(log_path, data)


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
    write_bundle_json(md_path, md)


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
    write_bundle_json(log_path, data)


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
    write_bundle_json(md_path, md)


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
    target_section: str = "",
    new_section: bool = False,
    section_rationale: str = "",
) -> int:
    """Run a single append operation. Returns 0 on success, nonzero on
    error.

    Exactly one of `target_section` / `new_section` decides the shape (F-02).
    `initial_lift` implies `new_section`: a bundle with no draft has no section
    plan to append into, so its first heading is not a change of architecture.
    """
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
    draft_existed = (_bundle_dir(bundle) / "paper_draft.tex").exists()
    draft = _ensure_paper_draft_skeleton(bundle, metadata)
    if initial_lift and not draft.exists():
        print(f"FATAL: --initial-lift requested but skeleton not created",
              file=sys.stderr)
        return 2

    # F-02: a bundle with no pre-existing draft has no architecture to append
    # into, so its first lift creates a section by construction rather than by
    # default. Recorded as such so the log does not read like an opt-in.
    if initial_lift or not draft_existed:
        new_section = True
        section_rationale = section_rationale or (
            "initial lift — bundle had no paper_draft.tex, so no section plan "
            "existed to append into")

    # Append the section
    ok, msg, anchor = _append_section_to_draft(
        draft,
        bundle=bundle,
        source=source,
        source_title=source_title,
        insertion_point=insertion_point,
        notes=notes,
        target_section=target_section,
        new_section=new_section,
        section_rationale=section_rationale,
    )
    if not ok:
        print(f"FATAL: append to paper_draft.tex failed: {msg}",
              file=sys.stderr)
        return 2

    # Update bookkeeping
    _append_to_change_log(
        bundle, source, source_title, insertion_point, lift_action, notes,
        anchor=anchor, section_rationale=section_rationale,
    )
    _append_to_append_log(
        bundle, source, lift_action, insertion_point, notes,
        lean_modules or [],
        anchor=anchor, section_rationale=section_rationale,
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
    parser.add_argument("--target-section", default="",
                        help="EXISTING top-level section title to append into; the "
                             "lift lands as a \\subsection inside it (F-02). "
                             "Required in lift mode unless --new-section or "
                             "--initial-lift. Matching is exact, then "
                             "case-insensitive, then unique-substring; an "
                             "ambiguous or absent name lists the draft's sections "
                             "and exits nonzero.")
    parser.add_argument("--new-section", action="store_true",
                        help="create a NEW top-level section for this lift — a "
                             "change to the bundle's architecture, not a "
                             "registration side-effect. Requires "
                             "--section-rationale.")
    parser.add_argument("--section-rationale", default="",
                        help="why the bundle's architecture needs a new top-level "
                             "section; recorded in the draft, change_log.md and "
                             "append_log.json. Required with --new-section.")
    parser.add_argument("--initial-lift", action="store_true",
                        help="bundle has no paper_draft.tex yet; bootstrap skeleton "
                             "(implies --new-section)")
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

    # F-02 (TODO-D26). Measured across all 21 bundles: 74 of 74 content lifts
    # created a top-level section, because creating one was the default and
    # nothing had to be said to get it. It now has to be said.
    if args.new_section and args.target_section:
        print("FATAL: --new-section and --target-section are exclusive; a lift "
              "either goes into the existing architecture or changes it",
              file=sys.stderr)
        return 2
    if args.new_section and not args.section_rationale.strip():
        print("FATAL: --new-section requires --section-rationale. A new "
              "top-level section is a change to the bundle's argument "
              "structure; the reason belongs in change_log.md next to it.",
              file=sys.stderr)
        return 2
    if not args.new_section and not args.initial_lift and not args.target_section:
        print("FATAL: lift mode requires --target-section '<existing section "
              "title>' (the lift lands as a \\subsection inside it), or an "
              "explicit --new-section --section-rationale '<why>'. Registering "
              "a source does not by itself buy a top-level section (F-02).",
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
        target_section=args.target_section,
        new_section=args.new_section,
        section_rationale=args.section_rationale,
    )


if __name__ == "__main__":
    raise SystemExit(main())
