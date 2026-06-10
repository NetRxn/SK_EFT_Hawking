#!/usr/bin/env python3
"""Promote sidecar fetch state into src/core/citations.py.

Reads:
    - docs/primary_sources_state.json  (sidecar from back_fill_primary_sources.py)
    - docs/missing_bibkey_stubs.json   (from extract_missing_bibkeys.py)

Writes:
    - src/core/citations.py — two operations:
        (a) for each existing registry entry whose sidecar verdict is
            "success" or "pre-existing": insert
                'inprep': False,
                'primary_source_path': '<sidecar.primary_source_path>',
            immediately after the entry's `'doi_verified': X,` line.
            Skips entries that already carry an 'inprep' field.
        (b) for each missing-bibkey stub: append a new dict entry to a
            Wave-1-marked block at the end of CITATION_REGISTRY. The stub's
            metadata (authors, title, journal, year, doi, arxiv) populates
            the entry; sidecar fetch results populate primary_source_path.

After write, the script re-imports citations.py and re-runs the validate
check `citation_primary_sources_present` to confirm no regressions.

Designed as a one-shot per Wave 1 close. Idempotent: re-running with the
same sidecar produces no further changes.
"""
from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent
SK_ROOT = Path(__file__).resolve().parent.parent
CITATIONS_PATH = SK_ROOT / "src" / "core" / "citations.py"
SIDECAR_PATH = SK_ROOT / "docs" / "primary_sources_state.json"
STUBS_PATH = SK_ROOT / "docs" / "missing_bibkey_stubs.json"


# ────────────────────────────────────────────────────────────────────────
# Parse citations.py: locate each entry's line range and doi_verified line
# ────────────────────────────────────────────────────────────────────────

ENTRY_OPEN_RE = re.compile(r"^    '([^']+)': \{\s*$")
ENTRY_CLOSE_RE = re.compile(r"^    \},?\s*$")
# Match the doi_verified line regardless of value type (bool / None / date)
# and tolerate a trailing `  # comment` annotation.
DOI_VERIFIED_RE = re.compile(r"^        'doi_verified':\s*\S")
INPREP_RE = re.compile(r"^        'inprep':\s*")
REGISTRY_OPEN_RE = re.compile(r"^CITATION_REGISTRY = \{\s*$")
REGISTRY_CLOSE_RE = re.compile(r"^\}\s*$")


@dataclass
class EntryLocation:
    bibkey: str
    open_line: int        # 0-indexed line of `    'Key': {`
    close_line: int       # 0-indexed line of `    },`
    doi_verified_line: int | None
    has_inprep: bool


def scan_citations(text: str) -> tuple[list[EntryLocation], int, int]:
    """Return (entries, registry_open_line, registry_close_line).

    `registry_close_line` is the line index of the `}` closing the
    CITATION_REGISTRY dict literal. Stub entries get inserted immediately
    before this line.
    """
    lines = text.split("\n")
    entries: list[EntryLocation] = []
    registry_open = None
    registry_close = None

    in_entry = False
    cur_key = None
    cur_open = None
    cur_doi_line = None
    cur_has_inprep = False

    for i, line in enumerate(lines):
        if registry_open is None:
            if REGISTRY_OPEN_RE.match(line):
                registry_open = i
            continue

        if not in_entry:
            m = ENTRY_OPEN_RE.match(line)
            if m:
                in_entry = True
                cur_key = m.group(1)
                cur_open = i
                cur_doi_line = None
                cur_has_inprep = False
                continue
            # Detect registry close: a top-level `}` line with no matching entry open
            if REGISTRY_CLOSE_RE.match(line):
                registry_close = i
                break
            continue

        # Inside entry
        if INPREP_RE.match(line):
            cur_has_inprep = True
        if cur_doi_line is None and DOI_VERIFIED_RE.match(line):
            cur_doi_line = i
        if ENTRY_CLOSE_RE.match(line):
            entries.append(EntryLocation(
                bibkey=cur_key,
                open_line=cur_open,
                close_line=i,
                doi_verified_line=cur_doi_line,
                has_inprep=cur_has_inprep,
            ))
            in_entry = False
            cur_key = None

    if registry_close is None:
        # Fallback: last `}` line in the file at top of indent
        for i in range(len(lines) - 1, -1, -1):
            if REGISTRY_CLOSE_RE.match(lines[i]):
                registry_close = i
                break
        if registry_close is None:
            raise RuntimeError("Could not find CITATION_REGISTRY closing brace")

    return entries, registry_open, registry_close


# ────────────────────────────────────────────────────────────────────────
# Stub formatter — produces a CITATION_REGISTRY-style block
# ────────────────────────────────────────────────────────────────────────

def py_repr(v):
    """Render a Python value the way the existing registry does."""
    if v is None:
        return "None"
    if isinstance(v, bool):
        return "True" if v else "False"
    if isinstance(v, str):
        # repr() guarantees a valid, round-trippable literal: it escapes
        # backslashes and control chars (NOT doing so was the bug that wrote
        # LaTeX text like 'Nucl.\ Phys.' and '\bibitem' with bare backslashes,
        # yielding SyntaxWarnings and silent \b->0x08 corruption) while keeping
        # the same single-vs-double quote preference and printable Unicode.
        return repr(v)
    if isinstance(v, list):
        if not v:
            return "[]"
        inner = ",\n                    ".join(py_repr(x) for x in v)
        return "[" + inner + "]"
    return repr(v)


def render_stub_entry(stub: dict, primary_source_path: str | None) -> str:
    """Render a stub dict as a block of source text matching registry style."""
    bibkey = stub["bibkey"]
    authors = stub.get("authors") or "Unknown"
    title = stub.get("title") or ""
    journal = stub.get("journal")
    volume = stub.get("volume")
    page = stub.get("page")
    year = stub.get("year")
    doi = stub.get("doi")
    arxiv = stub.get("arxiv")
    cited_in = stub.get("cited_in", [])
    used_in = [f"papers/{p}/paper_draft.tex" for p in cited_in]

    # Notes: prefer an explicit curated stub note; else factual provenance.
    bibitem_source = stub.get("bibitem_source") or "(unknown)"
    if stub.get("notes"):
        notes = stub["notes"]
    else:
        notes_parts = [
            "Auto-generated stub from \\bibitem block in "
            f"`papers/{bibitem_source}/paper_draft.tex`."
        ]
        if not stub.get("title"):
            notes_parts.append("Title not present in source bibitem.")
        notes = " ".join(notes_parts)

    lines = [f"    '{bibkey}': {{"]
    lines.append(f"        'authors': {py_repr(authors)},")
    lines.append(f"        'title': {py_repr(title)},")
    lines.append(f"        'journal': {py_repr(journal)},")
    lines.append(f"        'volume': {py_repr(volume)},")
    lines.append(f"        'page': {py_repr(page)},")
    lines.append(f"        'year': {py_repr(year)},")
    lines.append(f"        'doi': {py_repr(doi)},")
    lines.append(f"        'arxiv': {py_repr(arxiv)},")
    lines.append(f"        'doi_verified': False,")
    lines.append(f"        'inprep': False,")
    lines.append(f"        'primary_source_path': {py_repr(primary_source_path)},")
    lines.append(f"        'used_in': {py_repr(used_in)},")
    lines.append(f"        'provides': [],")
    lines.append(f"        'notes': {py_repr(notes)},")
    lines.append("    },")
    return "\n".join(lines)


# ────────────────────────────────────────────────────────────────────────
# Diff application
# ────────────────────────────────────────────────────────────────────────

def apply_promotions(
    text: str,
    sidecar_entries: dict[str, dict],
    stubs: list[dict],
    stubs_only: bool = False,
) -> tuple[str, dict[str, int]]:
    """Return (new_text, counts).

    counts records: existing-updated, existing-skipped-already, existing-no-doi-line,
    existing-no-sidecar-success, stubs-appended.
    """
    locations, _, registry_close = scan_citations(text)
    by_key = {loc.bibkey: loc for loc in locations}
    lines = text.split("\n")
    counts = {
        "existing-updated-cached": 0,
        "existing-updated-uncached": 0,
        "existing-skipped-already": 0,
        "existing-no-doi-line": 0,
        "stubs-appended": 0,
        "stubs-no-sidecar": 0,
    }

    # 1. Build (line_index, insert_block) edits for existing entries.
    # Every external entry without an `inprep` field gets one, regardless of
    # sidecar verdict. Path is set when the fetch succeeded; None otherwise.
    # Entries that already have `inprep` (PoC + inprep self-cites) are left
    # alone, even if their sidecar path differs from the registry value.
    #
    # NOTE: the line-anchored scanner only sees `inprep`/`doi_verified` when
    # each lives on its own line. Compact entries that pack several fields onto
    # one line (`'doi_verified': True, 'inprep': True, ...`) read as
    # inprep-less, so op (a) would insert a DUPLICATE `inprep` key and (last
    # wins) silently flip the entry. Pass `stubs_only=True` to skip op (a)
    # entirely when only appending new stub entries is intended.
    insertions: list[tuple[int, list[str]]] = []
    for bibkey, loc in ([] if stubs_only else by_key.items()):
        if loc.has_inprep:
            counts["existing-skipped-already"] += 1
            continue
        if loc.doi_verified_line is None:
            counts["existing-no-doi-line"] += 1
            continue
        rec = sidecar_entries.get(bibkey)
        path = None
        if rec and rec.get("verdict") in ("success", "pre-existing"):
            path = rec.get("primary_source_path")
            counts["existing-updated-cached"] += 1
        else:
            counts["existing-updated-uncached"] += 1
        block = [
            "        'inprep': False,",
            f"        'primary_source_path': {py_repr(path)},",
        ]
        insertions.append((loc.doi_verified_line + 1, block))

    # 2. Build the appended-stubs block
    stub_blocks: list[str] = []
    if stubs:
        stub_blocks.append("")
        stub_blocks.append("    # ════════════════════════════════════════════════════════════════")
        stub_blocks.append("    # Auto-stubs from \\bibitem blocks (Phase 6i Wave 1 backfill)")
        stub_blocks.append("    # ════════════════════════════════════════════════════════════════")
        stub_blocks.append("")
        for stub in sorted(stubs, key=lambda s: s["bibkey"]):
            rec = sidecar_entries.get(stub["bibkey"])
            if rec is None:
                counts["stubs-no-sidecar"] += 1
                primary_path = None
            elif rec.get("verdict") in ("success", "pre-existing"):
                primary_path = rec.get("primary_source_path")
            else:
                primary_path = None
            stub_blocks.append(render_stub_entry(stub, primary_path))
            stub_blocks.append("")
            counts["stubs-appended"] += 1
        # Trim trailing blank
        if stub_blocks and stub_blocks[-1] == "":
            stub_blocks.pop()

    # 3. Apply edits in REVERSE line order so indices remain valid
    insertions.sort(key=lambda t: t[0], reverse=True)
    new_lines = list(lines)
    for ins_line, block in insertions:
        # Insert block lines at ins_line
        for offset, b in enumerate(block):
            new_lines.insert(ins_line + offset, b)

    # 4. Append stub block before registry close
    # registry_close was computed against the ORIGINAL line numbers, but the
    # insertions above are all at smaller line indices than registry_close
    # only when the entry was BEFORE the close (always true here). Since we
    # inserted lines, registry_close has shifted. Recompute by scanning new_lines.
    new_close = None
    depth = 0
    for i, line in enumerate(new_lines):
        if REGISTRY_OPEN_RE.match(line):
            depth = 1
            continue
        if depth >= 1 and REGISTRY_CLOSE_RE.match(line):
            new_close = i
            break
    if new_close is None:
        raise RuntimeError("registry close vanished after edits")
    if stub_blocks:
        for offset, b in enumerate(stub_blocks):
            new_lines.insert(new_close + offset, b)

    return "\n".join(new_lines), counts


# ────────────────────────────────────────────────────────────────────────
# CLI
# ────────────────────────────────────────────────────────────────────────

def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--dry-run", action="store_true",
                   help="Preview counts; don't write citations.py.")
    p.add_argument("--no-validate", action="store_true",
                   help="Skip the post-write validate.py re-run.")
    p.add_argument("--stubs-only", action="store_true",
                   help="Append new stub entries only; skip op (a) updates to "
                        "existing entries (required when existing entries use "
                        "the compact multi-field-per-line style).")
    args = p.parse_args(argv)

    if not SIDECAR_PATH.is_file():
        print(f"error: sidecar not found at {SIDECAR_PATH}", file=sys.stderr)
        return 1
    sidecar_payload = json.loads(SIDECAR_PATH.read_text(encoding="utf-8"))
    sidecar_entries = sidecar_payload.get("entries", {})

    stubs = []
    if STUBS_PATH.is_file():
        stubs_payload = json.loads(STUBS_PATH.read_text(encoding="utf-8"))
        stubs = stubs_payload.get("stubs", [])

    text = CITATIONS_PATH.read_text(encoding="utf-8")
    new_text, counts = apply_promotions(text, sidecar_entries, stubs,
                                        stubs_only=args.stubs_only)

    print("Promotion summary:")
    for k in (
        "existing-updated-cached", "existing-updated-uncached",
        "existing-skipped-already", "existing-no-doi-line",
        "stubs-appended", "stubs-no-sidecar",
    ):
        print(f"  {k:34s} {counts[k]}")

    if args.dry_run:
        print()
        print("Dry-run; citations.py unchanged.")
        return 0

    if new_text == text:
        print()
        print("No changes (idempotent re-run); citations.py unchanged.")
        return 0

    backup = CITATIONS_PATH.with_suffix(".py.bak")
    shutil.copy2(CITATIONS_PATH, backup)
    CITATIONS_PATH.write_text(new_text, encoding="utf-8")

    # Verify by re-importing
    proc = subprocess.run(
        ["uv", "run", "python", "-c",
         "from src.core.citations import CITATION_REGISTRY; "
         "print(f'len={len(CITATION_REGISTRY)}')"],
        cwd=SK_ROOT, capture_output=True, text=True,
    )
    if proc.returncode != 0:
        # Roll back
        shutil.copy2(backup, CITATIONS_PATH)
        print("error: post-write import failed; rolled back", file=sys.stderr)
        print(proc.stderr, file=sys.stderr)
        return 1
    print(f"  import-check ok: {proc.stdout.strip()}")
    backup.unlink()

    if not args.no_validate:
        proc = subprocess.run(
            ["uv", "run", "python", "scripts/validate.py",
             "--check", "citation_primary_sources_present", "--no-archive"],
            cwd=SK_ROOT, capture_output=True, text=True,
        )
        # Forward the relevant summary lines
        for line in proc.stdout.splitlines():
            if "summary" in line or "missing_from_registry" in line or "missing_cache" in line[:25]:
                print(f"  validate: {line.strip()}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
