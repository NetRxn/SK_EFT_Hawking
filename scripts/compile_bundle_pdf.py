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

Exit code is non-zero if any bundle fails the gate (TeX error, unresolved reference
in the RENDERED pdf, or a missing PDF).
"""
from __future__ import annotations

import argparse
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
PAPERS = REPO / "papers"
PASSES = 3  # revtex4-2 + hyperref: 2 to settle refs, a 3rd to settle page-dependent ones


def _bundle_dirs(names: list[str] | None) -> list[Path]:
    if names:
        return [PAPERS / n for n in names]
    return sorted(d for d in PAPERS.iterdir()
                  if d.is_dir() and (d / "paper_draft.tex").is_file())


def compile_one(bundle_dir: Path, keep: bool = False) -> tuple[bool, str]:
    """Compile one bundle. Returns (passed, one-line report)."""
    tex = bundle_dir / "paper_draft.tex"
    if not tex.is_file():
        return False, f"{bundle_dir.name}: no paper_draft.tex"

    pdflatex = shutil.which("pdflatex")
    if pdflatex is None:
        return True, f"{bundle_dir.name}: SKIPPED (pdflatex not on PATH)"

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
            return False, f"{bundle_dir.name}: NO PDF PRODUCED"

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

        pages = "?"
        if shutil.which("pdfinfo"):
            info = subprocess.run(["pdfinfo", str(pdf)],
                                  capture_output=True, text=True, timeout=60).stdout
            m = re.search(r"Pages:\s+(\d+)", info)
            if m:
                pages = m.group(1)

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
        return ok, detail
    finally:
        if not keep:
            shutil.rmtree(out, ignore_errors=True)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("bundles", nargs="*", help="bundle codes, e.g. D11 D12")
    ap.add_argument("--all", action="store_true", help="every bundle with a paper_draft.tex")
    ap.add_argument("--keep-artifacts", action="store_true",
                    help="keep the temp build dir and print its path")
    args = ap.parse_args()

    if not args.bundles and not args.all:
        ap.error("name at least one bundle, or pass --all")

    dirs = _bundle_dirs(None if args.all else args.bundles)
    failed = 0
    for d in dirs:
        ok, report = compile_one(d, keep=args.keep_artifacts)
        print(report)
        if not ok:
            failed += 1
    print(f"\n{len(dirs) - failed}/{len(dirs)} bundle(s) passed the compile gate")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
