"""Shared LaTeX-scanning utilities — ADR-009 Phase 2.

Two functions used by check modules on both sides of the prose split, so they live
below both rather than being imported across a sibling boundary or duplicated.

`_strip_tex_comments` blanks unescaped `%`-to-EOL with spaces, **preserving every
character offset and line break** — that is the whole point of it. Callers match
against the stripped text and report positions in the original file; a version that
deleted the comments would silently shift every reported line number.

`_strip_tex_comments` is in the frozen external surface
(`tests/test_validate_prose_checks.py`), so `validate` re-exports it from here.
"""
from __future__ import annotations


def _strip_tex_comments(text: str) -> str:
    """Blank out LaTeX comments (unescaped ``%`` to end-of-line) with
    spaces, preserving every character offset and line break so that
    match offsets in the stripped text map 1:1 onto the original file.
    """
    out = []
    for line in text.split("\n"):
        idx = None
        i = 0
        while i < len(line):
            if line[i] == "%":
                # escaped \% is content, not a comment
                n_bs = 0
                j = i - 1
                while j >= 0 and line[j] == "\\":
                    n_bs += 1
                    j -= 1
                if n_bs % 2 == 0:
                    idx = i
                    break
            i += 1
        if idx is None:
            out.append(line)
        else:
            out.append(line[:idx] + " " * (len(line) - idx))
    return "\n".join(out)


def _line_of(text: str, offset: int) -> int:
    """1-based line number of a character offset."""
    return text.count("\n", 0, offset) + 1
