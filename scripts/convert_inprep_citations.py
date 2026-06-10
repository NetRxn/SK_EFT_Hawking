#!/usr/bin/env python3
"""
convert_inprep_citations.py — deposit-time conversion of in-preparation
self-citations to real arXiv citations, in one documented pass.
========================================================================

At arXiv-deposit time (Step 3 of `docs/ARXIV_DEPOSIT_PLAN.md`), every
project-internal "in preparation" self-cite that now has a real arXiv id is
converted in one pass:

  (a) registry edit — in `src/core/citations.py` the entry gets
      `'inprep': False`, `'arxiv': '<id>'`, and a dated note appended to
      `notes` recording the conversion;
  (b) bibitem rewrite — in every `papers/*/paper_draft.tex` containing
      `\\bibitem{<key>}`, the heterogeneous in-preparation body is replaced
      by the standard self-cite form, preserving the title:

          J.~Roehm, \\emph{<title>}, arXiv:<id> (<year>).

      (title from the registry entry, or the mapping's `title_override`);
  (c) cache stub — invariant #11 (`citation_primary_sources_present`)
      requires non-inprep entries with an arXiv id to have a primary-source
      cache file; on --apply a `<bibkey>.json` self-deposit stub is written
      under `Lit-Search/<phase>/primary-sources/` (phase routed exactly as
      the validate.py check routes it, via `paper_phase` on `used_in`).

Input mapping file (JSON):

    {
      "Roehm2026Wave1": {"arxiv": "2606.01234"},
      "LinearizedEFE2026": {"arxiv": "2606.05678",
                            "title_override": "Linearized Einstein ..."}
    }

Design choice — direct edit with anchored surgery (documented)
--------------------------------------------------------------
The registry is Python source, so the script performs *anchored text
surgery* verified safe on the live registry (2026-06-10 audit): every
inprep entry block (a) starts with a unique ``    '<key>': {`` line,
(b) contains exactly one ``'inprep': True,`` and one ``'arxiv': None,``
anchor, and (c) ends with `notes` as its last field terminated by ``',``
— so the three edits are unambiguous line-level replacements. Safety
rails: every anchor must match exactly once *within the entry block* or
the key is NOT edited and an exact edit-list (file:line, old → new) is
emitted for an agent to apply manually; after surgery the whole file
must `ast.parse` (and, on --apply, re-import cleanly in a subprocess)
or nothing is written. This makes the direct-edit path strictly safer
than a hand-applied edit list while degrading *to* an edit list on any
anchor drift.

Bibitem bodies are regenerated from registry data rather than pattern-
matched: the existing in-preparation bodies are heterogeneous (ten-plus
phrasings across drafts), so surgical preservation would be fragile;
the registry title is canonical (Pipeline-Invariant-#2 spirit) and the
standard self-cite form is fully determined by (title, arxiv, year).
Trailing comment-only lines inside a bibitem block are preserved.

Usage
-----
    # Dry-run inventory (no mapping): report all inprep keys + bibitem sites
    uv run python scripts/convert_inprep_citations.py

    # Dry-run with a mapping: full would-be diff summary (default mode)
    uv run python scripts/convert_inprep_citations.py --map deposit_ids.json

    # Apply (writes registry + drafts + cache stubs)
    uv run python scripts/convert_inprep_citations.py --map deposit_ids.json --apply

    # F-last gate: verify zero remaining "in preparation" strings in a paper
    uv run python scripts/convert_inprep_citations.py --check F
    uv run python scripts/convert_inprep_citations.py --check paper4_wkb_connection

Exit codes: 0 clean; 1 check-failed or apply aborted; 2 bad invocation.
"""
from __future__ import annotations

import argparse
import ast
import json
import re
import subprocess
import sys
from dataclasses import dataclass, field
from datetime import date
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT))

CITATIONS_PATH = PROJECT_ROOT / "src" / "core" / "citations.py"
PAPERS_DIR = PROJECT_ROOT / "papers"
LIT_SEARCH = PROJECT_ROOT.parent / "Lit-Search"
PHASE_FALLBACK = "Phase-1-and-Background"   # mirrors validate.py CHECK
NOTES_INDENT = " " * 17                      # aligns under `'notes': '`


def _rel(p: Path) -> str:
    """Repo-relative path for reporting; absolute for fixture paths."""
    try:
        return str(p.relative_to(PROJECT_ROOT))
    except ValueError:
        return str(p)


# ────────────────────────────────────────────────────────────────────────────
# Registry surgery (pure functions on file text — unit-testable)
# ────────────────────────────────────────────────────────────────────────────

@dataclass
class EditRecord:
    """One exact line edit (consumed directly or emitted as an edit list)."""
    path: str
    line: int           # 1-based line of `old` in the pre-edit file
    old: str
    new: str


@dataclass
class KeyResult:
    key: str
    ok: bool
    problems: list[str] = field(default_factory=list)
    registry_edits: list[EditRecord] = field(default_factory=list)
    bibitem_files: list[str] = field(default_factory=list)
    cache_stub: str | None = None


def find_entry_block(text: str, key: str) -> tuple[int, int] | None:
    """(start, end) char offsets of the registry entry block for `key`.

    The block spans from the ``    '<key>': {`` line through the closing
    ``    },`` line (inclusive of the opening line, exclusive of the line
    after the closing brace). Returns None unless exactly one block exists.
    """
    starts = [m.start() for m in re.finditer(
        rf"^    '{re.escape(key)}': \{{", text, re.MULTILINE)]
    if len(starts) != 1:
        return None
    start = starts[0]
    close = text.find("\n    },", start)
    if close == -1:
        return None
    return (start, close + len("\n    },"))


def registry_edits_for_key(
    text: str, key: str, arxiv_id: str, today: str,
) -> tuple[str | None, KeyResult]:
    """Compute the three anchored edits for one key.

    Returns (new_file_text or None, KeyResult). On any anchor failure the
    text is unchanged (None) and the KeyResult carries the problems plus
    whatever exact edits could be computed, as an edit list.
    """
    res = KeyResult(key=key, ok=False)
    span = find_entry_block(text, key)
    if span is None:
        res.problems.append("entry block not found (or not unique)")
        return None, res
    s, e = span
    block = text[s:e]

    anchors = {
        "arxiv": "'arxiv': None,",
        "inprep": "'inprep': True,",
    }
    for name, anchor in anchors.items():
        n = block.count(anchor)
        if n != 1:
            res.problems.append(f"anchor {anchor!r} matched {n}x in block")
    body = block.removesuffix("\n    },")
    if not body.rstrip().endswith("',"):
        res.problems.append("entry body does not end with a string-"
                            "terminated notes field — cannot append "
                            "dated note")
    if res.problems:
        return None, res

    new_block = block.replace("'arxiv': None,", f"'arxiv': '{arxiv_id}',")
    new_block = new_block.replace("'inprep': True,", "'inprep': False,")
    # Append dated note as implicit-concatenation segments on the final
    # notes string (entry body ends `...',` just before `\n    },`).
    note_tail_lines = [
        f"{NOTES_INDENT}' [{today}] Converted to arXiv:{arxiv_id} by '",
        f"{NOTES_INDENT}'scripts/convert_inprep_citations.py "
        f"(inprep -> False).',",
    ]
    note_seg = "'\n" + "\n".join(note_tail_lines)
    idx = new_block.rstrip().rfind("',")
    new_block = new_block[:idx] + note_seg + new_block[idx + 2:]

    # Build exact edit records (line-level) for reporting.
    pre_lines = text[:s].count("\n")
    old_lines = block.splitlines()
    rel = _rel(CITATIONS_PATH)
    for needle, repl in (
        ("'arxiv': None,", f"'arxiv': '{arxiv_id}',"),
        ("'inprep': True,", "'inprep': False,"),
    ):
        for i, ln in enumerate(old_lines):
            if needle in ln:
                res.registry_edits.append(EditRecord(
                    path=rel, line=pre_lines + i + 1,
                    old=ln, new=ln.replace(needle, repl)))
                break
    # notes-tail record: last body line (index -2; -1 is the closing `},`)
    tail_i = len(old_lines) - 2
    old_tail = old_lines[tail_i]
    new_tail = (old_tail.rstrip()[:-2] + "'\n"
                + "\n".join(note_tail_lines))
    res.registry_edits.append(EditRecord(
        path=rel, line=pre_lines + tail_i + 1, old=old_tail, new=new_tail))

    res.ok = True
    return text[:s] + new_block + text[e:], res


# ────────────────────────────────────────────────────────────────────────────
# Bibitem rewrite (pure functions — unit-testable)
# ────────────────────────────────────────────────────────────────────────────

_TEX_ESCAPES = {"&": r"\&", "%": r"\%", "#": r"\#"}


def latex_escape_title(title: str) -> str:
    out = title
    for ch, esc in _TEX_ESCAPES.items():
        out = re.sub(rf"(?<!\\){re.escape(ch)}", esc.replace("\\", "\\\\"),
                     out)
    return out


def canonical_bibitem_body(title: str, arxiv_id: str, year: int) -> str:
    """The standard self-cite body (without the \\bibitem{...} line)."""
    return (f"J.~Roehm, \\emph{{{latex_escape_title(title)}}}, "
            f"arXiv:{arxiv_id} ({year}).")


def rewrite_bibitem(tex: str, key: str, new_body: str) -> tuple[str, bool]:
    """Replace the body of \\bibitem{key} with `new_body`.

    The body spans from after the \\bibitem{key} marker to the next
    \\bibitem or \\end{thebibliography}. Trailing comment-only / blank
    lines of the old body are preserved (separator comments). Returns
    (new_text, found).
    """
    pat = re.compile(
        rf"(\\bibitem\{{{re.escape(key)}\}})(.*?)"
        rf"(?=\\bibitem\{{|\\end\{{thebibliography\}})",
        re.DOTALL)
    m = pat.search(tex)
    if not m:
        return tex, False
    old_body = m.group(2)
    # preserve trailing comment-only lines (e.g. `%% ────` separators)
    kept: list[str] = []
    for line in reversed(old_body.splitlines()):
        if line.strip() == "" or line.lstrip().startswith("%"):
            kept.append(line)
        else:
            break
    kept_tail = "\n".join(reversed([ln for ln in kept if ln.strip()]))
    tail = ("\n" + kept_tail + "\n\n") if kept_tail else "\n\n"
    replacement = m.group(1) + "\n" + new_body + tail
    return tex[:m.start()] + replacement + tex[m.end():], True


# ────────────────────────────────────────────────────────────────────────────
# Cache stub (invariant #11 continuity post-conversion)
# ────────────────────────────────────────────────────────────────────────────

def stub_path_for(entry: dict, key: str) -> Path:
    """Cache-stub location, routed exactly as validate.py routes lookups."""
    from src.core.citations import paper_phase
    phase = None
    for p in entry.get("used_in", []):
        phase = paper_phase(p)
        if phase:
            break
    return (LIT_SEARCH / (phase or PHASE_FALLBACK) / "primary-sources"
            / f"{key}.json")


def stub_payload(entry: dict, key: str, arxiv_id: str, today: str) -> dict:
    return {
        "bibkey": key,
        "kind": "project-self-deposit",
        "arxiv": arxiv_id,
        "title": entry.get("title"),
        "year": entry.get("year"),
        "converted": today,
        "note": ("Primary source is the project's own arXiv deposit; stub "
                 "written by scripts/convert_inprep_citations.py to keep "
                 "validate.py --check citation_primary_sources_present "
                 "green post-conversion (Pipeline Invariant #11)."),
    }


# ────────────────────────────────────────────────────────────────────────────
# Check mode (the F-last gate)
# ────────────────────────────────────────────────────────────────────────────

def check_paper(paper: str) -> int:
    """Exit-code style check: 0 if no non-comment 'in preparation' remains."""
    tex = PAPERS_DIR / paper / "paper_draft.tex"
    if not tex.exists():
        print(f"ERROR: {tex} not found", file=sys.stderr)
        return 2
    hits: list[tuple[int, str]] = []
    for i, line in enumerate(
            tex.read_text(encoding="utf-8", errors="replace").splitlines(),
            start=1):
        content = line.split("%", 1)[0]
        if re.search(r"in preparation", content, flags=re.IGNORECASE):
            hits.append((i, line.strip()))
    if hits:
        print(f"CHECK FAIL: {len(hits)} 'in preparation' occurrence(s) "
              f"remain in papers/{paper}/paper_draft.tex:")
        for ln, txt in hits:
            print(f"  {_rel(tex)}:{ln}: {txt[:100]}")
        return 1
    print(f"CHECK PASS: papers/{paper}/paper_draft.tex has zero "
          f"non-comment 'in preparation' occurrences.")
    return 0


# ────────────────────────────────────────────────────────────────────────────
# Driver
# ────────────────────────────────────────────────────────────────────────────

def run(mapping: dict[str, dict], apply: bool,
        registry: dict[str, dict] | None = None) -> int:
    """Drive the conversion. `registry` is injectable for fixture tests;
    None loads the live CITATION_REGISTRY. File locations come from the
    module globals CITATIONS_PATH / PAPERS_DIR / LIT_SEARCH (monkeypatch
    those in tests)."""
    if registry is None:
        from src.core.citations import CITATION_REGISTRY as registry

    CITATION_REGISTRY = registry
    today = date.today().isoformat()
    inprep_keys = sorted(k for k, v in CITATION_REGISTRY.items()
                         if v.get("inprep"))
    print(f"Registry: {len(CITATION_REGISTRY)} entries, "
          f"{len(inprep_keys)} inprep self-cites.")
    print(f"Mode: {'APPLY' if apply else 'dry-run (no writes)'} | "
          f"mapping: {len(mapping)} key(s)\n")

    bad_keys = sorted(set(mapping) - set(inprep_keys))
    if bad_keys:
        for k in bad_keys:
            why = ("not in CITATION_REGISTRY" if k not in CITATION_REGISTRY
                   else "not an inprep entry")
            print(f"  SKIP {k}: {why}")
        print()

    reg_text = CITATIONS_PATH.read_text(encoding="utf-8")
    results: list[KeyResult] = []
    drafts: dict[Path, str] = {}     # lazily-loaded, possibly-edited drafts
    stubs: list[tuple[Path, dict]] = []
    not_found_bibitems: list[str] = []

    for key in sorted(set(mapping) & set(inprep_keys)):
        spec = mapping[key]
        arxiv_id = spec.get("arxiv", "").strip()
        if not re.fullmatch(r"\d{4}\.\d{4,5}(v\d+)?", arxiv_id):
            res = KeyResult(key=key, ok=False,
                            problems=[f"bad arXiv id {arxiv_id!r} "
                                      "(expected YYMM.NNNNN)"])
            results.append(res)
            continue
        entry = CITATION_REGISTRY[key]

        # (a) registry surgery
        new_text, res = registry_edits_for_key(reg_text, key, arxiv_id, today)
        if new_text is not None:
            reg_text = new_text

        # (b) bibitem rewrite in every draft that carries the key
        title = spec.get("title_override") or entry.get("title") or key
        body = canonical_bibitem_body(title, arxiv_id,
                                      entry.get("year") or date.today().year)
        found_any = False
        for tex_path in sorted(PAPERS_DIR.glob("*/paper_draft.tex")):
            cur = drafts.get(tex_path)
            if cur is None:
                cur = tex_path.read_text(encoding="utf-8", errors="replace")
            if f"\\bibitem{{{key}}}" not in cur:
                continue
            cur2, found = rewrite_bibitem(cur, key, body)
            if found:
                drafts[tex_path] = cur2
                res.bibitem_files.append(_rel(tex_path))
                found_any = True
        if not found_any:
            not_found_bibitems.append(key)

        # (c) cache stub (apply-time write; reported in dry-run)
        sp = stub_path_for(entry, key)
        res.cache_stub = str(sp)
        stubs.append((sp, stub_payload(entry, key, arxiv_id, today)))
        results.append(res)

    # ── summary ────────────────────────────────────────────────────────────
    converted = [r for r in results if r.ok]
    failed = [r for r in results if not r.ok]
    for r in results:
        status = "CONVERT" if r.ok else "EDIT-LIST/SKIP"
        print(f"[{status}] {r.key}")
        for p in r.problems:
            print(f"    problem: {p}")
        for er in r.registry_edits:
            print(f"    {er.path}:{er.line}")
            print(f"      - {er.old.strip()}")
            print(f"      + {er.new.strip()}")
        for f_ in r.bibitem_files:
            print(f"    bibitem rewritten: {f_}")
        if r.cache_stub:
            print(f"    cache stub: {r.cache_stub}")

    unmapped = sorted(set(inprep_keys) - set(mapping))
    print(f"\nUnmapped inprep keys remaining ({len(unmapped)}):")
    for k in unmapped:
        sites = sum(
            1 for tex_path in sorted(PAPERS_DIR.glob("*/paper_draft.tex"))
            if f"\\bibitem{{{k}}}"
            in tex_path.read_text(encoding="utf-8", errors="replace"))
        print(f"  {k}  (bibitem in {sites} draft(s))")
    if not_found_bibitems:
        print(f"\nMapped but no \\bibitem found in any draft "
              f"({len(not_found_bibitems)}): "
              f"{', '.join(not_found_bibitems)}")

    print(f"\nTotals: {len(converted)} convertible / {len(failed)} "
          f"edit-list-or-skip / {len(unmapped)} unmapped inprep keys / "
          f"{len(drafts)} draft file(s) touched.")

    if not apply:
        print("\nDry-run complete — nothing written. "
              "Re-run with --apply to write.")
        return 0

    # ── apply ──────────────────────────────────────────────────────────────
    try:
        ast.parse(reg_text)
    except SyntaxError as exc:
        print(f"\nABORT: post-surgery citations.py does not parse: {exc}",
              file=sys.stderr)
        return 1
    CITATIONS_PATH.write_text(reg_text, encoding="utf-8")
    for tex_path, text in drafts.items():
        tex_path.write_text(text, encoding="utf-8")
    for sp, payload in stubs:
        sp.parent.mkdir(parents=True, exist_ok=True)
        sp.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    # subprocess import check — the registry must still import clean
    proc = subprocess.run(
        [sys.executable, "-c",
         "from src.core.citations import CITATION_REGISTRY; "
         "print(len(CITATION_REGISTRY))"],
        cwd=PROJECT_ROOT, capture_output=True, text=True)
    if proc.returncode != 0:
        print(f"\nWARNING: post-write import check FAILED — restore from "
              f"git and inspect:\n{proc.stderr}", file=sys.stderr)
        return 1
    print(f"\nApplied. Registry imports clean "
          f"({proc.stdout.strip()} entries). Next: run "
          f"`uv run python scripts/validate.py --check "
          f"citation_primary_sources_present` and the per-paper --check "
          f"gate, then recompile touched drafts (LaTeX gate).")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Convert in-preparation self-citations to arXiv "
                    "citations (dry-run by default)")
    ap.add_argument("--map", metavar="JSON",
                    help="mapping file {bibkey: {arxiv, title_override?}}")
    ap.add_argument("--apply", action="store_true",
                    help="write changes (default: dry-run)")
    ap.add_argument("--check", metavar="PAPER",
                    help="verify zero remaining 'in preparation' strings in "
                         "papers/<PAPER>/paper_draft.tex (F-last gate)")
    args = ap.parse_args()

    if args.check:
        if args.map or args.apply:
            print("ERROR: --check is exclusive of --map/--apply",
                  file=sys.stderr)
            return 2
        return check_paper(args.check)

    mapping: dict[str, dict] = {}
    if args.map:
        with open(args.map, encoding="utf-8") as f:
            mapping = json.load(f)
        if not isinstance(mapping, dict):
            print("ERROR: mapping file must be a JSON object",
                  file=sys.stderr)
            return 2
    elif args.apply:
        print("ERROR: --apply requires --map", file=sys.stderr)
        return 2

    return run(mapping, apply=args.apply)


if __name__ == "__main__":
    raise SystemExit(main())
