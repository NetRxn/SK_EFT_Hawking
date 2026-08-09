"""Shared LaTeX-scanning utilities — ADR-009 Phase 2.

Two functions used by check modules on both sides of the prose split, so they live
below both rather than being imported across a sibling boundary or duplicated.

`_strip_tex_comments` blanks unescaped `%`-to-EOL with spaces, **preserving every
character offset and line break** — that is the whole point of it. Callers match
against the stripped text and report positions in the original file; a version that
deleted the comments would silently shift every reported line number.

`_strip_tex_comments` is in the frozen external surface
(`tests/test_validate_prose_checks.py`), so `validate` re-exports it from here.

`find_inline_numerical_literals` lives here for a different reason — see its own
docstring. It is imported by `scripts/readiness_gates.py`, which sits OUTSIDE this
package. That direction is safe precisely because this module imports nothing from
the suite (same property as `_config` and `_registry`), so it cannot close a cycle
with `validation.checks.bundles_readiness → readiness_gates`.
"""
from __future__ import annotations

import re


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


# ═══════════════════════════════════════════════════════════════════════
# Inline unit-bearing numerical literals — ONE definition, two consumers
# ═══════════════════════════════════════════════════════════════════════
# Audit finding QI-02. This predicate existed TWICE, byte-identical: as
# `papers_prose._NUMERICAL_LITERAL_RE` (feeding the `numerical_literals` check) and
# as an inline `lit_re` inside `readiness_gates._eval_numerical_freshness` (feeding
# P2 Gate 9). Verified identical — same pattern string, same flags, and both wrapped
# in the same two-step strip — before they were merged, so the merge is provably
# behaviour-preserving.
#
# Two copies of one predicate is not merely duplication here: `validate.py --check
# readiness_verdicts_agree` exists to assert that the finding-derived verdict and the
# gate-derived verdict AGREE. Tuning one copy and not the other would make the two
# subsystems disagree by construction, and the check built to catch disagreement
# would be reporting on a difference someone introduced in its own blind spot.

#: A hand-typed numeric literal in body prose that could drift from the pipeline
#: and therefore belongs in an `\input{tables/...}` file (Invariant #1).
#:
#: ⚠️ THIS COMMENT SAID "a literal with a physical unit" UNTIL 2026-08-09, AND THAT
#: WAS FALSE FOR MOST OF ITS OWN POPULATION (TODO-D37). Measured across all drafts:
#:
#:     117 matches total
#:        11  fired a unit alternative (nK, mK, mu m, mm/s, s^-1, \mathrm{...})
#:       106  fired the final `\times 10^` alternative
#:             46 of those carry a unit after the exponent
#:             60 of those are DIMENSIONLESS  <-- 51 % of the whole population
#:
#: The dimensionless majority is correction ratios (delta_disp, delta_diss),
#: thresholds and table entries. **They are in scope deliberately.** A
#: dimensionless computed value drifts from the pipeline exactly as a unit-bearing
#: one does, so the freshness concern is identical; "unit-bearing" was never the
#: property this predicate was protecting, only the property its comment claimed.
#:
#: TODO-D37 offered narrowing the leg to require an adjacent unit. **Rejected:** it
#: would drop 60 of 117 matches at a stroke, which is loosening a gate rather than
#: fixing one, and the goal forbids forcing a gate green by narrowing a check.
#:
#: The genuine tension D37 surfaced is a DIFFERENT axis: pipeline-derived values
#: (should be generated) versus source-anchored constants that must stay literal —
#: e.g. D6 §7's `2.73 \times 10^{-5}`, both the published rigorous bound of the
#: primary source and the constant asserted in `steaneAGPThreshold_gt`. Routing a
#: theorem's own statement through a regenerated file is the wrong direction. That
#: distinction is a per-site Stage-13 judgement, not a regex change, and the
#: down-only `NUMERICAL_LITERAL_CEILING` is what tracks it.
NUMERICAL_LITERAL_RE = re.compile(
    r'(?<!\\)\b(\d+\.\d+|\d+(?:\.\d+)?e[+-]?\d+)\s*'
    r'(~?)\\?(?:'
    r'(?:mu|\\mu)\s*m\b|'
    r'nK\b|'
    r'mK\b|'
    r'\\mathrm\{[a-zA-Z]+\}|'
    r's\^?(?:-|\{-|\^{-)1\}?|'
    r'mm/s\b|'
    r'\\mu m\b|'
    r'\\times\s*10\^'
    r')',
    re.IGNORECASE,
)

_INPUT_TABLES_RE = re.compile(r'\\input\{tables/[^}]+\}')
_CAPTION_RE = re.compile(r'\\caption\{[^}]*\}', re.DOTALL)


def find_inline_numerical_literals(text: str) -> tuple[str, list]:
    """Return ``(stripped_text, matches)`` for unit-bearing literals in BODY prose.

    Two regions are removed before scanning, and both exclusions are deliberate:

    * ``\\input{tables/...}`` — generated tables own their own literals; that is the
      mechanism this check exists to push authors toward, so counting them would
      penalise compliance.
    * ``\\caption{...}`` — captions legitimately quote reference values from primary
      sources ("290 s^-1") to situate the paper against them.

    ``stripped_text`` is returned alongside the matches because a caller reporting
    line numbers must count them in the SAME string the offsets index into. Counting
    them in the original would shift every reported line by the length of whatever
    was stripped above it.
    """
    stripped = _INPUT_TABLES_RE.sub('', text)
    stripped = _CAPTION_RE.sub('', stripped)
    return stripped, list(NUMERICAL_LITERAL_RE.finditer(stripped))


# ═══════════════════════════════════════════════════════════════════════
# TODO-D2: the LaTeX-escaped-identifier trap, in ONE place
# ═══════════════════════════════════════════════════════════════════════
#
# A draft writes `gapped\_interface\_axiom`, never the raw identifier. Any scan
# of `papers/**/*.tex` for a Lean name that does not account for `\_` reports
# ZERO HITS AND IS WRONG. That produced a false claim in
# `QA_QI_INFRASTRUCTURE_MAP.md` (ledger V8 atom Q10).
#
# ⚠️ Measured 2026-08-09: the trap had ALREADY been rediscovered independently
# by two consumers, each with its own private correct handling —
# `prose_lean_refs._PROSE_UNESCAPE_RE` (unescape, then match) and
# `lean_substrate._tex_name_pattern` (build an escape-tolerant pattern). Two
# solutions to one problem in two modules is precisely the duplication this
# entry predicted, so the helpers live here now and both call sites use them.
#
# Two shapes are needed because the two directions are genuinely different:
#   * you HAVE a Lean name and want to find it in prose  -> `tex_escaped_name_pattern`
#   * you HAVE a prose token and want the Lean name      -> `unescape_tex_identifier`

#: Characters LaTeX escapes with a backslash inside an identifier.
_TEX_ESCAPED_CHARS_RE = re.compile(r"\\([_\\&%$#{}~^])")


def unescape_tex_identifier(token: str) -> str:
    """A prose token with LaTeX escaping removed: ``a\\_b`` -> ``a_b``.

    Use when you hold a token lifted out of a draft and want the Lean name.
    """
    return _TEX_ESCAPED_CHARS_RE.sub(r"\1", token)


def tex_escaped_name_pattern(name: str) -> re.Pattern:
    """Pattern matching `name` as a draft may write it, escaped or not.

    Use when you hold a Lean name and want to find it in prose. Matching an
    escape-tolerant pattern beats unescaping the whole document: it does not
    disturb any other backslash in the source.
    """
    return re.compile(re.escape(name).replace("_", r"(?:\\_|_)"))
