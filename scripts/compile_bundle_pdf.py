#!/usr/bin/env python3
"""Compile a bundle draft to PDF WITHOUT writing build artifacts into the bundle.

Why this exists
---------------
`pdflatex` run with cwd inside `papers/<BUNDLE>/` writes `paper_draft.aux`, `.log`,
`.out` and `.synctex.gz` right next to the source. Those paths are shared by every
process that touches the bundle — the author, `validate.py`, and any Stage-9/10/13
review agent verifying the compile gate. Two of them overlapping corrupts the build
state, and the corruption is *silent and misleading* rather than loud:

  * measured 2026-07-31 — an `.aux` losing section labels between sequential passes
    (6 `\\label{sec:…}` in the source, 2 in the `.aux` after a pass);
  * a `.log` reporting 13 undefined references across four passes while the `.aux`
    held every label and the rendered PDF had zero `??`;
  * one `paper_draft.synctex.gz` written entirely NUL-filled.

A `.log` is therefore NOT trustworthy evidence about a shared bundle. This script
compiles into a private temp directory and copies back only `paper_draft.pdf`, so
concurrent compiles cannot interfere, and it reports the gate from artifacts it owns.

Usage
-----
    uv run python scripts/compile_bundle_pdf.py D11 D12
    uv run python scripts/compile_bundle_pdf.py --all
    uv run python scripts/compile_bundle_pdf.py D12 --keep-artifacts   # debugging

A draft whose PDF is already newer than every file feeding it is SKIPPED; pass
`--force` to recompile regardless. Without the skip this script recompiled all 64
drafts on every run, so every run dirtied ~45 tracked PDFs whether or not anything
had changed.

Exit code is non-zero if any bundle fails the gate (TeX error, unresolved reference
in the RENDERED pdf, or a missing PDF).
"""
from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import validate_helpers as _H  # noqa: E402

REPO = Path(__file__).resolve().parent.parent
PAPERS = REPO / "papers"
PASSES = 3  # revtex4-2 + hyperref: 2 to settle refs, a 3rd to settle page-dependent ones


def _bundle_dirs(names: list[str] | None) -> list[Path]:
    if names:
        return [PAPERS / n for n in names]
    return sorted(d for d in PAPERS.iterdir()
                  if d.is_dir() and (d / "paper_draft.tex").is_file())


#: Last compile verdict per draft, for EVERY `papers/<dir>` — the 21 bundles and the 43
#: legacy drafts alike. Gitignored, like the sibling `.latex_compile_cache.json`: it is
#: a local build cache, and a verdict from another machine's TeX install is not evidence
#: about this one.
GATE_CACHE = "papers/.compile_gate_cache.json"


def _gate_cache() -> dict:
    try:
        loaded = json.loads((REPO / GATE_CACHE).read_text())
        return loaded if isinstance(loaded, dict) else {}
    except (OSError, json.JSONDecodeError):
        return {}          # unreadable cache recompiles everything — fail-safe


def _record_gate(name: str, ok: bool, pages: int | None) -> None:
    cache = _gate_cache()
    cache[name] = {"ok": ok, "pages": pages}
    try:
        (REPO / GATE_CACHE).write_text(json.dumps(cache, indent=2, sort_keys=True) + "\n")
    except OSError:
        pass               # a cache that cannot be written is a slow run, not a failure


def _pdf_pages(pdf: Path) -> int | None:
    """Page count of an existing PDF, or `None` if it cannot be read."""
    if not shutil.which("pdfinfo") or not pdf.is_file():
        return None
    try:
        info = subprocess.run(["pdfinfo", str(pdf)], capture_output=True,
                              text=True, timeout=60).stdout
    except (subprocess.SubprocessError, OSError):
        return None
    m = re.search(r"Pages:\s+(\d+)", info)
    return int(m.group(1)) if m else None


def _up_to_date(bundle_dir: Path, tex: Path) -> tuple[bool, int | None]:
    """`(skip?, page count)` — may this draft's compile be skipped?

    Two conditions, and the second is the one that matters:

    1. the on-disk PDF is newer than every file in
       `validate_helpers.draft_input_closure(tex)` — the single definition of "which
       files change this draft", shared with `paper_latex_compiles`'s per-draft hash and
       `bundle_manuscript_length`'s staleness test; **and**
    2. **the last recorded verdict for this draft was a PASS** (`GATE_CACHE`).

    ⚠️ **Condition 2 exists because skipping asserts the gate passed.** Without it, a
    draft that genuinely FAILS the gate — D3 has 3 unresolved references in the rendered
    PDF — would be reported `SKIPPED` and counted as passing on every run after the
    first, because its PDF is perfectly fresh. A freshness heuristic that converts a
    standing FAIL into a PASS is a gate that stops firing, which is the defect class this
    repository keeps rediscovering (`viz_consistency` returning unconditional `True`;
    Stage 9's "ALL figures PASS" over an empty set). A failing draft therefore recompiles
    every run and keeps saying so.

    ⚠️ **mtime, not content hash.** `touch`ing a source recompiles needlessly; that is
    the cheap failure. The expensive one — a source edited without its mtime moving —
    cannot happen through an editor. `--force` is the escape hatch for every case this
    heuristic gets wrong, and is what to reach for when in any doubt.

    The verdict lives in one sidecar covering **all 64 drafts**, not in
    `bundle_metadata.json`, which only the 21 bundles have. Keying the skip off the
    metadata blob meant the 43 legacy drafts could never record a verdict and so
    recompiled forever — and since pdflatex stamps a creation date into the PDF, every
    recompile rewrites the bytes. That is the churn this skip exists to stop, and
    two-thirds of it sat outside the store.

    Errs toward RECOMPILING everywhere else too: an unreadable closure, a missing PDF, or
    no recorded verdict all return `False`.
    """
    pdf = bundle_dir / "paper_draft.pdf"
    if not pdf.is_file():
        return False, None
    if _gate_cache().get(bundle_dir.name, {}).get("ok") is not True:
        return False, None   # no recorded PASS -> no basis to skip
    try:
        newest = max(p.stat().st_mtime
                     for p in _H.draft_input_closure(tex) if p.is_file())
    except (OSError, ValueError):
        return False, None
    if pdf.stat().st_mtime < newest:
        return False, None
    return True, _pdf_pages(pdf)


def compile_one(bundle_dir: Path, keep: bool = False,
                force: bool = False) -> tuple[bool, str, int | None]:
    """Compile one bundle. Returns (passed, one-line report, page count or None).

    ⚠️ The page count used to be computed here and thrown away — it reached the
    human-readable string at the end of this function and nothing else, so
    `ManuscriptLength` had no instrument despite one existing (audit 2026-08-01
    §5.2: *"The instrument exists and is deliberately unwired."*). It is now
    returned, and `main()` persists it to `bundle_metadata.json.compiled_pages`
    so the heatmap can render a size without recompiling 21 drafts.

    Returned rather than written here, because a function that both compiles and
    mutates tracked metadata cannot be called from a read-only context — the same
    split `check_bundle_source_freshness` had to make after it wrote its own
    verdict into the file its readers trust.
    """
    tex = bundle_dir / "paper_draft.tex"
    if not tex.is_file():
        return False, f"{bundle_dir.name}: no paper_draft.tex", None

    pdflatex = shutil.which("pdflatex")
    if pdflatex is None:
        return True, f"{bundle_dir.name}: SKIPPED (pdflatex not on PATH)", None

    if not force:
        fresh, pages = _up_to_date(bundle_dir, tex)
        if fresh:
            return True, (f"{bundle_dir.name}: SKIPPED (up to date) "
                          f"pages={pages if pages is not None else '?'}"), pages

    out = Path(tempfile.mkdtemp(prefix=f"skeft-{bundle_dir.name}-"))
    try:
        for _ in range(PASSES):
            subprocess.run(
                [pdflatex, "-interaction=nonstopmode", "-no-shell-escape",
                 f"-output-directory={out}", tex.name],
                cwd=bundle_dir,          # so \includegraphics{figures/…} resolves
                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                timeout=300, check=False)

        log = out / "paper_draft.log"
        pdf = out / "paper_draft.pdf"
        if not pdf.is_file():
            return False, f"{bundle_dir.name}: NO PDF PRODUCED", None

        log_text = log.read_text(encoding="utf-8", errors="replace") if log.is_file() else ""
        errors = re.findall(r"^! .*$", log_text, re.M)
        overfull = len(re.findall(r"Overfull", log_text))

        # A silently-dropped \documentclass option means the document was typeset under a
        # different configuration than it declares. Whether that changes the layout depends
        # on the option: the case that prompted this guard (D12 declaring `prxquantum`,
        # which this revtex4-2 does not implement) turned out to change NOTHING —
        # compiling both gives identical extracted text, 10 pages, 0 Overfull, because
        # `aps4-2.rtx` defines `\rtx@apsprx` as a no-op. The round-8 claim that it
        # invalidated prior measurements was wrong (corrected round-9).
        #
        # The guard is still a hard failure rather than a warning, for the reason that
        # survives: you cannot tell from the PDF whether a dropped option was inert or
        # load-bearing, and a wrong-class page count reads exactly like a right one. Fail
        # and let the author check, rather than measure something and hope.
        unused_opts = re.findall(r"Unused global option\(s\):\s*\[([^\]]*)\]", log_text)

        # Unresolved references are judged from the RENDERED pdf, not the log: `??`
        # is what a reader would actually see, and it cannot be produced by another
        # process racing us.
        unresolved = -1
        if shutil.which("pdftotext"):
            txt = subprocess.run(["pdftotext", str(pdf), "-"],
                                 capture_output=True, text=True, timeout=120).stdout
            unresolved = txt.count("??")

        pages: str | int = "?"
        if shutil.which("pdfinfo"):
            info = subprocess.run(["pdfinfo", str(pdf)],
                                  capture_output=True, text=True, timeout=60).stdout
            m = re.search(r"Pages:\s+(\d+)", info)
            if m:
                pages = int(m.group(1))

        shutil.copy2(pdf, bundle_dir / "paper_draft.pdf")

        ok = not errors and unresolved <= 0 and not unused_opts
        detail = (f"{bundle_dir.name}: {'OK ' if ok else 'FAIL'} "
                  f"pages={pages} overfull={overfull} tex_errors={len(errors)} "
                  f"unresolved_refs_in_pdf="
                  f"{'n/a (no pdftotext)' if unresolved < 0 else unresolved} "
                  f"dropped_class_opts={len(unused_opts)}")
        if unused_opts:
            detail += (f"\n    ⚠️ DROPPED CLASS OPTION(S): {', '.join(unused_opts)} — the document "
                       f"was typeset under a DIFFERENT configuration than it declares. The "
                       f"option may be inert (revtex's `prxquantum` is), but that cannot be "
                       f"read off the PDF: compile with a recognised option, or confirm this "
                       f"one is a no-op, before trusting the layout numbers above.")
        if errors:
            detail += f"\n    first error: {errors[0][:160]}"
        if keep:
            detail += f"\n    artifacts kept: {out}"
        return ok, detail, (pages if isinstance(pages, int) else None)
    finally:
        if not keep:
            shutil.rmtree(out, ignore_errors=True)


def _persist_pages(bundle_dir: Path, pages: int | None, ok: bool | None = None) -> None:
    """Record `compiled_pages` in the bundle's metadata — CLI-only, by design.

    `bundle_manuscript_length` does NOT read this field; it measures the PDF
    itself, because a stored number cannot be distinguished from a stale one.
    This exists so the heatmap and dashboard can render a size without
    recompiling 21 drafts.

    `None` (no pdfinfo, or no PDF) CLEARS the field rather than leaving the
    previous value: a compile that could not be measured must not leave a number
    behind that reads as this compile's.
    """
    meta = bundle_dir / "bundle_metadata.json"
    if not meta.is_file():
        return
    try:
        md = json.loads(meta.read_text())
    except (OSError, json.JSONDecodeError):
        return
    if md.get("compiled_pages") == pages and md.get("compile_gate_ok") == ok:
        return
    md["compiled_pages"] = pages
    # The gate verdict, so `_up_to_date` can refuse to skip a draft that last FAILED.
    # A skip asserts the gate passed; without a recorded pass there is no basis for it.
    if ok is not None:
        md["compile_gate_ok"] = ok
    # ⚠️ `ensure_ascii=False` is REQUIRED, not cosmetic. These blobs carry `§` and `—`
    # in their apex `claims` strings; the default re-encodes every one as `\uXXXX`,
    # which rewrites ~450 lines of a file this function means to touch by one field.
    # Four writers disagree on this today (TODO-D25) — match the on-disk form.
    meta.write_text(json.dumps(md, indent=2, ensure_ascii=False) + "\n")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("bundles", nargs="*", help="bundle codes, e.g. D11 D12")
    ap.add_argument("--all", action="store_true", help="every bundle with a paper_draft.tex")
    ap.add_argument("--keep-artifacts", action="store_true",
                    help="keep the temp build dir and print its path")
    ap.add_argument("--force", action="store_true",
                    help="recompile even when the PDF is newer than every input "
                         "(bypasses the mtime skip; use whenever in doubt)")
    args = ap.parse_args()

    if not args.bundles and not args.all:
        ap.error("name at least one bundle, or pass --all")

    def skipped(rep: str) -> bool:
        return 'SKIPPED' in rep

    dirs = _bundle_dirs(None if args.all else args.bundles)
    failed = 0
    for d in dirs:
        ok, report, pages = compile_one(d, keep=args.keep_artifacts, force=args.force)
        print(report)
        if not ok:
            failed += 1
        _persist_pages(d, pages, ok)
        if not skipped(report):
            _record_gate(d.name, ok, pages)
    print(f"\n{len(dirs) - failed}/{len(dirs)} bundle(s) passed the compile gate")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
