"""Paper-prose gates — ADR-009 Phase 2.

Claims a draft makes about itself, checked against the pipeline: figure/theorem
references and placeholder bibliography (`paper_provenance`), unit-bearing and
count literals that should come from `\\input{tables/}` (`numerical_literals`,
`count_literals`), axiom-count prose vs `docs/counts.json`
(`axiom_count_prose_consistency`), whether the draft still compiles
(`paper_latex_compiles`), and toolchain-pin drift (`paper_toolchain_pin_drift`).

SPLIT FROM `prose_lean_refs` — the second half of the planned `papers_prose`
measured 1,507 lines together, failing D1's readable-in-one-pass criterion. The
seam: this module asks *does the prose agree with the numbers*; `prose_lean_refs`
asks *do the names it cites resolve in the Lean library*. They shared exactly one
3-line helper, `_line_of`, which now lives in `validation/_tex.py` along with
`_strip_tex_comments` — below both, rather than imported across a sibling boundary.

`paper_latex_compiles` and `paper_toolchain_pin_drift` were two of the eight
ALWAYS-PASS checks; ADR-009 §Deferred item 3 dispositioned them in OPPOSITE
directions and this header must not blur them:

* `paper_latex_compiles` was a DEFECT and now **hard-fails** on a fatal compile
  error. It is still slow-gated behind `_cfg.FORCE_LATEX`, so a default full run
  skips it — skipped is not the same as advisory.
* `paper_toolchain_pin_drift` is **advisory by design** and stays that way: a
  stale pin in a draft is a publication decision for Stage 13, not a defect.

⚠️ This header said both "return `passed=True` even after a real compile failure"
until 2026-08-04 (audit finding QI-13), which was false for the first and made the
two look like one disposition.

`paper_toolchain_pin_drift` was UNASSIGNED in the migration table and is placed
here deliberately: it scans paper drafts for stale version literals.

Import rules: framework from `validation._registry`; paths as `_H.<NAME>` at each
use (never a module-level alias, never from `__file__` — H1); flags by attribute on
`validation._config` (H5). MOVED VERBATIM otherwise.
"""
from __future__ import annotations

import json
import re
import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import List

import validate_helpers as _H
from validation import _config as _cfg
from validation._registry import CheckResult, Detail, register_check
from validation._tex import (
    NUMERICAL_LITERAL_RE,
    _line_of,
    _strip_tex_comments,
    find_inline_numerical_literals,
)


# Fatal-error markers in a pdflatex .log. A `! ` line is TeX's universal
# error sentinel (e.g. "! Undefined control sequence", "! Misplaced
# alignment tab character &", "! LaTeX Error: ..."). Undefined-reference /
# undefined-citation / overfull-box warnings are NOT fatal and are ignored.
_LATEX_FATAL_RE = re.compile(r"^! ", re.MULTILINE)

# The unit-bearing-literal predicate moved to `validation/_tex.py` on 2026-08-04
# (audit finding QI-02). It was duplicated byte-identically inside
# `readiness_gates._eval_numerical_freshness`, and the two feed verdicts that
# `readiness_verdicts_agree` requires to agree — so a divergence between the copies
# would have been introduced in that check's blind spot. `_NUMERICAL_LITERAL_RE` is
# kept as an alias because it is a module-level name this suite's tests reach.
_NUMERICAL_LITERAL_RE = NUMERICAL_LITERAL_RE

# Patterns that strongly suggest a hardcoded count literal in paper prose.
# Each pattern captures (\d+) together with a domain noun; the assumption
# is that any such count should come from \input{../../docs/counts.tex}
# macros (\totaltheorems, \leanmodules, etc.) so counts stay fresh.
_COUNT_LITERAL_PATTERNS = [
    # "N theorems", "N Lean theorems", "N formally-verified theorems"
    (re.compile(r'(?<![\\{\d])\b(\d{2,5})\s+(?:formally[- ]?verified\s+|machine[- ]?checked\s+|Lean\s+)?theorems?\b', re.IGNORECASE), "theorems"),
    # "N Lean modules" / "N modules"
    (re.compile(r'(?<![\\{\d])\b(\d{2,4})\s+(?:Lean\s+)?modules?\b', re.IGNORECASE), "modules"),
    # "N sorry" (remaining sorry count)
    (re.compile(r'(?<![\\{\d])\b(\d{1,4})\s+(?:remaining\s+)?sorry\b', re.IGNORECASE), "sorry"),
    # "N Aristotle-proved"
    (re.compile(r'(?<![\\{\d])\b(\d{2,4})\s+Aristotle[- ]?proved', re.IGNORECASE), "aristotle_proved"),
]


# The roster's single source of truth (H2 keeps `validate.BUNDLE_CODES` alive for
# the roster gate; this is the same object, imported from its owner rather than
# re-bound here — a module-level rebinding is the by-value pattern this package
# bans for flags and paths, and there is no reason to make an exception for it).
from bundle_registry import BUNDLE_CODES  # noqa: E402


# ═══════════════════════════════════════════════════════════════════════
# CHECK 14: Paper claim provenance
# ═══════════════════════════════════════════════════════════════════════

@register_check("paper_provenance",
                "Paper numerical claims trace to computations within 0.5%")
def check_paper_provenance() -> CheckResult:
    """Verify paper theorem references exist in Lean and figures are present."""
    details = []
    all_pass = True

    # Build set of all Lean theorem names.
    # ⚠️ rglob, NOT glob (fixed 2026-08-04, audit finding QI-01). `glob` covered
    # 1,373 of 2,039 files, hiding 5,469 theorem names in subdirectories. This
    # check FAILS on a `\texttt{}` reference it cannot resolve, so the error
    # direction was toward false positives — a draft citing a theorem in
    # `QuantumNetwork/` or `FaultTolerance/` would have been reported as citing a
    # nonexistent theorem. No draft did, which is why it never fired.
    lean_names = set()
    for lean_file in _H.LEAN_DIR.rglob("*.lean"):
        for line in lean_file.read_text().splitlines():
            if line.startswith("theorem "):
                name = line.split()[1].split("(")[0].split(":")[0].strip()
                lean_names.add(name)

    for tex_file in _H.all_paper_drafts():     # ALL drafts (bundles + legacy)
        paper_dir = tex_file.parent
        tex = tex_file.read_text()

        # Check 1: \\texttt{theorem_name} refs exist in Lean
        texttt_refs = re.findall(r'\\texttt\{([a-z_][a-zA-Z0-9_]*)\}', tex)
        theorem_refs = [r for r in texttt_refs if '_' in r]
        missing = [r for r in theorem_refs if r not in lean_names]
        if missing:
            all_pass = False
            details.append(Detail(
                f"{paper_dir.name}/theorem_refs", False,
                f"Not in Lean: {missing}"
            ))
        elif theorem_refs:
            details.append(Detail(
                f"{paper_dir.name}/theorem_refs", True,
                f"{len(theorem_refs)} theorem references verified"
            ))

        # Check 2: No \\fbox placeholder figures
        if '\\fbox{\\parbox' in tex:
            all_pass = False
            details.append(Detail(
                f"{paper_dir.name}/figures", False,
                "Has \\fbox placeholder figures — must use \\includegraphics"
            ))
        elif '\\includegraphics' in tex:
            # Resolve each \includegraphics{PATH} relative to the paper tex dir.
            # Papers may reference local figures/ (most) or shared figures/phase*/ (paper16).
            includegraphics_refs = re.findall(
                r'\\includegraphics(?:\[[^\]]*\])?\{([^}]+)\}', tex
            )
            missing_figs = []
            resolved_count = 0
            for ref in includegraphics_refs:
                ref_path = (paper_dir / ref).resolve()
                # Accept the exact path, or the path with any of the common
                # graphics extensions appended (LaTeX auto-appends .pdf/.png).
                candidates = [ref_path] + [
                    ref_path.with_suffix(ext) for ext in ('.png', '.pdf', '.jpg')
                ]
                if any(c.exists() for c in candidates):
                    resolved_count += 1
                else:
                    missing_figs.append(ref)
            if missing_figs:
                all_pass = False
                details.append(Detail(
                    f"{paper_dir.name}/figures", False,
                    f"Missing {len(missing_figs)} referenced figure(s): {missing_figs[:3]}"
                    + (f" (+{len(missing_figs) - 3} more)" if len(missing_figs) > 3 else "")
                ))
            else:
                details.append(Detail(
                    f"{paper_dir.name}/figures", True,
                    f"{resolved_count} referenced figure(s) resolved"
                ))

        # Check 3: No placeholder bibliography entries
        # Strip LaTeX line comments first so historical cleanup notes
        # like "% [2026-05-04 cleanup: ... arXiv:2604.XXXXX ...]" don't
        # false-positive. A LaTeX line comment starts at an unescaped %
        # and continues to end-of-line.
        tex_comment_stripped = re.sub(r'(?<!\\)%[^\n]*', '', tex)
        if (
            'xxxxx' in tex_comment_stripped.lower()
            or 'Nature \\textbf{XXX}' in tex_comment_stripped
        ):
            all_pass = False
            details.append(Detail(
                f"{paper_dir.name}/bibliography", False,
                "Has placeholder bibliography entries (xxxxx or XXX)"
            ))

    return CheckResult(passed=all_pass, details=details)


@register_check("numerical_literals",
                "Paper .tex files free of inline numerical literals outside \\input{} blocks")
def check_numerical_literals() -> CheckResult:
    """CHECK 17b: Flag hardcoded numerical literals in paper body.

    Counterpart to CHECK 17 count_literals. Values with physical units
    should come from auto-generated tables/*.tex files, not be
    hand-coded in the body.

    RATCHET, not advisory (ADR-009 §Deferred item **3**, 2026-08-03). The debt is
    frozen at ``NUMERICAL_LITERAL_CEILING`` and any NEW inline literal FAILS.
    ⚠️ This docstring said "WARN-level during retrofit; flip to FAIL once every
    paper uses \\input{tables/...}" until 2026-08-04 (audit finding QI-14) — a
    promise the check could no longer keep, since the corpus grew from 15 papers
    to 64 and the target receded faster than it was approached.
    """
    if not _H.PAPERS_DIR.exists():
        return CheckResult(passed=True, details=[
            Detail("papers_dir", True, "papers/ not found; skipping", warning=True),
        ])

    details = []
    total_findings = 0
    total_inputs = 0
    # Glob widened 2026-07-31: was `paper*_*/`, which matched only the legacy
    # `paperNN_<slug>/` layout and left ALL 21 publication bundles (D1-D12, I1-I3,
    # L1-L3, E1, E2, F) unscanned. Filed as a Stage-13 QI candidate in two
    # consecutive rounds before being fixed. Use the same `*/` form the bundle-aware
    # checks already use.
    for tex_path in _H.all_paper_drafts():     # ALL drafts (bundles + legacy)
        paper_name = tex_path.parent.name
        try:
            text = tex_path.read_text()
        except UnicodeDecodeError:
            details.append(Detail(paper_name, True, "unreadable; skipping",
                                  warning=True))
            continue

        # Papers that \input{tables/...} have opted in for data rows
        input_count = len(re.findall(r'\\input\{tables/[^}]+\}', text))
        total_inputs += input_count

        # Strip `\input{tables/...}` and `\caption{}` regions, then scan the
        # remainder. Both the stripping and the pattern now live in
        # `validation/_tex.find_inline_numerical_literals` — the SAME function P2
        # Gate 9 calls, so the two verdicts cannot drift apart (audit QI-02).
        stripped, matches = find_inline_numerical_literals(text)
        findings = []
        for m in matches:
            line_no = _line_of(stripped, m.start())
            findings.append((line_no, m.group(0).strip()))

        if not findings:
            details.append(Detail(
                paper_name, True,
                f"no inline unit-bearing literals in body"
                + (f" (uses {input_count} \\input tables)" if input_count else ""),
            ))
            continue

        total_findings += len(findings)
        sample = "; ".join(f'L{ln} "{lit}"' for ln, lit in findings[:3])
        suffix = f" (+{len(findings)-3} more)" if len(findings) > 3 else ""
        prefix = f"uses {input_count} \\input, " if input_count else ""
        details.append(Detail(
            paper_name, True,
            f"{prefix}{len(findings)} inline literal(s): {sample}{suffix}",
            warning=(len(findings) > 0),
        ))

    # ── RATCHET (ADR-009 §Deferred item 3) — reasoning in check_count_literals.
    from src.core.constants import NUMERICAL_LITERAL_CEILING as _CEIL
    over = total_findings > _CEIL
    details.insert(0, Detail(
        "summary", not over,
        f"{total_findings} inline literals across papers; "
        f"{total_inputs} \\input{{tables/}} references in use (ceiling {_CEIL})"
        + (f" — EXCEEDS by {total_findings - _CEIL}" if over
           else f" — {_CEIL - total_findings} below; lower the ceiling" if total_findings < _CEIL
           else ""),
        warning=(total_findings > 0 and not over),
    ))
    if over:
        details.insert(1, Detail(
            "ratchet", False,
            f"inline unit-bearing literal total grew to {total_findings}, above the "
            f"frozen ceiling {_CEIL}. Move it into \\input{{tables/...}} (Invariant #1), "
            f"or raise NUMERICAL_LITERAL_CEILING with a rationale."))
    return CheckResult(passed=not over, details=details)


@register_check("count_literals",
                "Paper .tex files reference counts via \\input{counts.tex} macros, not literals")
def check_count_literals() -> CheckResult:
    """CHECK 17: Flag hardcoded count literals in paper .tex files.

    Papers should pull counts from docs/counts.tex via \\input + macros
    (\\totaltheorems, \\leanmodules, \\sorrycount, etc.) so stale counts
    can't ship. This check greps every paper_draft.tex for patterns like
    "N theorems", "N Lean modules", etc., and WARNs when found outside
    of an \\input context.

    RATCHET, not advisory (ADR-009 §Deferred item **3**, 2026-08-03). The debt is
    frozen at ``COUNT_LITERAL_CEILING`` and any NEW count literal FAILS.
    ⚠️ This docstring said it "will escalate to FAIL once all 15 papers use macros"
    until 2026-08-04 (audit finding QI-14). That condition was written when the
    corpus HAD 15 papers; it now has 64, so the escalation could never trigger —
    the check promised a future it had made unreachable. Freezing the debt keeps
    the promise today rather than deferring it again.
    """
    if not _H.PAPERS_DIR.exists():
        return CheckResult(passed=True, details=[
            Detail("papers_dir", True, "papers/ directory not found; skipping",
                   warning=True),
        ])

    # Papers that have \input'd counts.tex are exempt — they've opted in
    # Glob widened 2026-07-31: `paper*/` matched only `paperNN_<slug>/`, so every
    # publication bundle's count literals were ungated and desynchronized silently on
    # each substrate edit. See check_numerical_literals for the same fix.
    paper_tex_files = _H.all_paper_drafts()     # ALL drafts (bundles + legacy)
    details = []
    total_findings = 0

    for tex_path in paper_tex_files:
        paper_name = tex_path.parent.name
        try:
            text = tex_path.read_text()
        except UnicodeDecodeError:
            details.append(Detail(paper_name, True,
                                  "unreadable (encoding); skipping",
                                  warning=True))
            continue

        # Has this paper opted in to macros?
        uses_macros = (
            r'\input{../../docs/counts.tex}' in text
            or r'\input{../docs/counts.tex}' in text
            or r'\input{counts.tex}' in text
            or any(macro in text for macro in [
                r'\totaltheorems', r'\substantivetheorems',
                r'\leanmodules', r'\sorrycount', r'\aristotleproved',
            ])
        )

        findings = []
        for pattern, kind in _COUNT_LITERAL_PATTERNS:
            for m in pattern.finditer(text):
                # Compute a rough line number for reporting
                line_no = text.count("\n", 0, m.start()) + 1
                findings.append((line_no, kind, m.group(0).strip()))

        if not findings:
            details.append(Detail(
                paper_name, True,
                "no count literals found" + (" (macros in use)" if uses_macros else ""),
            ))
            continue

        # Found literals — WARN (passes but advisory)
        total_findings += len(findings)
        sample = "; ".join(
            f"L{ln} \"{lit}\" ({kind})" for ln, kind, lit in findings[:3]
        )
        suffix = f" (+{len(findings)-3} more)" if len(findings) > 3 else ""
        status_prefix = "USES MACROS but " if uses_macros else ""
        details.append(Detail(
            paper_name, True,
            f"{status_prefix}{len(findings)} count-literal matches: {sample}{suffix}",
            warning=True,
        ))
    # ── RATCHET (ADR-009 §Deferred item 3) ──────────────────────────────────
    # Was `passed=True` under "WARN-only until retrofit complete". The retrofit's
    # condition — "once all 15 papers use macros" — was written when the corpus had
    # 15 papers; it now has 64, so the target receded faster than it was approached
    # and the check could never fail. Its own docstring promised escalation, so it is
    # NOT permanently advisory and is not walked back: the existing debt is frozen and
    # any NEW literal fails. Same shape as NATIVE_DECIDE_DECL_CLOSURE_CEILING.
    from src.core.constants import COUNT_LITERAL_CEILING as _CEIL
    over = total_findings > _CEIL
    details.insert(0, Detail(
        "summary", not over,
        f"{total_findings} count-literal matches across {len(paper_tex_files)} papers "
        f"(ceiling {_CEIL})"
        + (f" — EXCEEDS by {total_findings - _CEIL}" if over
           else f" — {_CEIL - total_findings} below; lower the ceiling" if total_findings < _CEIL
           else ""),
        warning=(total_findings > 0 and not over),
    ))
    if over:
        details.insert(1, Detail(
            "ratchet", False,
            f"count-literal total grew to {total_findings}, above the frozen ceiling "
            f"{_CEIL}. Move the new value into a counts.tex macro (Invariants #1/#2), "
            f"or raise COUNT_LITERAL_CEILING in the same commit with a rationale."))
    return CheckResult(passed=not over, details=details)


@register_check("paper_latex_compiles",
                "Bundle drafts compile under pdflatex (HARD-FAILS on a fatal "
                "error; slow — pass --force-latex or --check paper_latex_compiles)")
def check_paper_latex_compiles() -> CheckResult:
    """Slow-gated compile gate: actually compile each bundle draft with
    ``pdflatex`` and HARD-FAIL on fatal (``! ``-marked) breakage.

    Why this exists: the 2026-06-10 paper15 incident — 108 fatal LaTeX
    errors injected by unescaped ``&``/``_`` and an executed ``\\input{}``
    in autogenerated tables — was invisible to *every* structural check.
    Only a real compile catches a draft that no longer builds. The fix
    (table-generator escaping in ``scripts/paper_tables/sources.py``) is
    durable, but a compile gate prevents the next such regression.

    Posture:
      - **Slow-gated**: SKIPPED in the default full run (pdflatex × all
        bundles is minutes). Runs only when ``--force-latex`` is passed or
        ``paper_latex_compiles`` is the explicitly selected ``--check``.
      - **Blocking**: a fatal compile error FAILS the check. Repaired
        2026-08-03 (ADR-009 §Deferred item **3**); it previously computed the
        verdict and discarded it. Transient toolchain gaps cannot reach this
        branch — pdflatex-missing and the slow-gate skip both return above —
        so what remains is a draft a working pdflatex could not compile.
        ⚠️ This bullet read "**Advisory**: always ``passed=True``" for a day
        after the repair (audit finding QI-13).

    One non-stop pass per draft (enough to surface fatal breakage; full
    reference/citation resolution is out of scope for a build gate).
    Compiles with the paper dir as cwd (so relative ``\\input``/
    ``\\includegraphics`` resolve) and ``-output-directory`` pointed at a
    throwaway temp dir (so no ``.aux``/``.log``/``.pdf`` lands in the repo).
    """
    details: List[Detail] = []

    if not _cfg.FORCE_LATEX:
        return CheckResult(passed=True, details=[Detail(
            "skipped", True,
            "SKIPPED (slow) — pass --force-latex or "
            "--check paper_latex_compiles to compile all bundle drafts")])

    pdflatex = shutil.which("pdflatex")
    if pdflatex is None:
        return CheckResult(passed=True, details=[Detail(
            "toolchain", True,
            "SKIPPED — pdflatex not on PATH (install a TeX distribution)")])

    n_ok = 0
    n_missing = 0
    failed: List[tuple[str, int, str]] = []  # (code, n_fatal, first_error)

    for code in BUNDLE_CODES:
        tex = _H.PAPERS_DIR / code / "paper_draft.tex"
        if not tex.is_file():
            n_missing += 1
            continue
        paper_dir = tex.parent
        with tempfile.TemporaryDirectory(prefix=f"latexchk_{code}_") as out_dir:
            try:
                # capture_output without text= → bytes (unused; pdflatex logs
                # often carry non-UTF-8 bytes). We parse the .log file instead.
                subprocess.run(
                    [pdflatex, "-interaction=nonstopmode", "-halt-on-error",
                     "-no-shell-escape", f"-output-directory={out_dir}",
                     "paper_draft.tex"],
                    cwd=paper_dir, capture_output=True, timeout=180,
                )
            except subprocess.TimeoutExpired:
                failed.append((code, -1, "compile timed out (>180s)"))
                continue
            except Exception as exc:  # noqa: BLE001 — advisory: never hard-error
                failed.append((code, -1, f"compile invocation failed: {exc}"))
                continue
            log_path = Path(out_dir) / "paper_draft.log"
            log = log_path.read_text(errors="replace") if log_path.is_file() else ""
            fatal = _LATEX_FATAL_RE.findall(log)
            if fatal:
                # Capture the first "! ..." error line for the report.
                m = re.search(r"^(! .*)$", log, re.MULTILINE)
                first = m.group(1).strip()[:90] if m else "(see log)"
                failed.append((code, len(fatal), first))
            else:
                n_ok += 1

    details.append(Detail(
        "summary",
        len(failed) == 0,
        f"{n_ok}/{n_ok + len(failed)} bundle drafts compiled clean "
        f"({n_missing} missing draft(s) skipped) — {len(failed)} with fatal errors"
    ))
    for code, n_fatal, first in failed:
        cnt = "timeout" if n_fatal < 0 else f"{n_fatal} fatal"
        details.append(Detail(
            f"compile:{code}", False,
            f"{code}: {cnt} — first: {first}"))

    # ── FIXED 2026-08-03 (ADR-009 §Deferred item 3) ─────────────────────────────
    # This returned `passed=True` unconditionally, under "Advisory: never block the
    # suite on a compile WARN". It computed `all_pass` from the failure list and then
    # DISCARDED it — the QA/QI map §7 shape exactly: the check works out the right
    # answer and throws it away.
    #
    # The stated justification was that transient toolchain gaps must not block
    # development. That case is already handled ABOVE by two early returns: pdflatex
    # missing, and the slow-gate skip when `_cfg.FORCE_LATEX` is false (which is the
    # default, so a normal full run is unaffected by this change). What remains when
    # we reach here is a draft that a working pdflatex could not compile — which is
    # a real defect, and the incident this check was built for (108 fatal errors
    # injected by unescaped & / _ in generated tables) is exactly that.
    #
    # Measured at the moment of the fix: 20/21 clean, **D3 fails with 2 fatal errors
    # ("! Undefined control sequence")** — reported as a passing ⚠ WARN for as long
    # as the check has existed.
    return CheckResult(passed=len(failed) == 0, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 24: Axiom-count ↔ paper-prose consistency
# ═══════════════════════════════════════════════════════════════════════

# Present-tense single-axiom claims ("one axiom", "a single axiom",
# "1~axiom", "one tracked axiom", ...). `~` is the LaTeX non-breaking
# space; word separators may also be newlines.
_AXIOM_SEP = r"(?:\s|~)+"
_AXIOM_SINGULAR_RE = re.compile(
    r"\b(?:one|single|sole|lone|1)" + _AXIOM_SEP
    + r"(?:(?:true|tracked|remaining|residual|project-local|project|"
    + r"genuine|physical|global)" + _AXIOM_SEP + r")?"
    + r"axiom\b(?!-)",
    re.IGNORECASE,
)
# Present-tense naming of the retired axiom ("the axiom \texttt{gapped...").
_AXIOM_GAPPED_PRESENT_RE = re.compile(
    r"the" + _AXIOM_SEP + r"axiom" + _AXIOM_SEP + r"\\texttt\{gapped",
    re.IGNORECASE,
)
# Numeric plural claims ("0 axioms", "3 axioms", "zero axioms"). The
# qualifier group is captured so per-wave delta claims ("zero NEW
# axioms") can be excluded from the total-count comparison.
_AXIOM_PLURAL_RE = re.compile(
    r"\b(zero|\d+)" + _AXIOM_SEP
    + r"(?:(new|additional|extra|tracked|project-local|true|active|"
    + r"declared)" + _AXIOM_SEP + r")?"
    + r"axioms\b",
    re.IGNORECASE,
)
# Historical-attribution context tokens: a single-axiom claim sitting
# within ±120 chars of one of these is a legitimate retrospective
# (D2/F-style "formerly axiom gapped_interface_axiom" usage).
_AXIOM_HISTORICAL_RE = re.compile(
    r"formerly|converted|retired|was\s+an\s+axiom|2026-05-19",
    re.IGNORECASE,
)
_AXIOM_HIST_WINDOW = 120
# Narrow immediately-preceding negation guard ("no single axiom ...").
_AXIOM_NEG_BEFORE_RE = re.compile(r"\b(?:no|without)\b[^.\n]{0,15}$",
                                  re.IGNORECASE)


def _axiom_prose_findings(text: str, axiom_count: int) -> list:
    """Pure scanning core for CHECK 24 (unit-testable).

    Returns a list of dicts: ``{kind, line, excerpt, fail}`` where
    ``kind`` is one of ``singular`` / ``gapped_present`` /
    ``plural_mismatch``. ``fail=True`` only for the hard-failure class:
    a non-historical single-axiom claim while the live axiom count is 0.
    LaTeX comments are blanked before scanning (offsets preserved).
    """
    stripped = _strip_tex_comments(text)
    findings = []

    def _is_historical(start: int, end: int) -> bool:
        lo = max(0, start - _AXIOM_HIST_WINDOW)
        hi = min(len(stripped), end + _AXIOM_HIST_WINDOW)
        return bool(_AXIOM_HISTORICAL_RE.search(stripped[lo:hi]))

    for m in _AXIOM_SINGULAR_RE.finditer(stripped):
        if _is_historical(m.start(), m.end()):
            continue
        if _AXIOM_NEG_BEFORE_RE.search(stripped[max(0, m.start() - 18):m.start()]):
            continue
        findings.append({
            "kind": "singular",
            "line": _line_of(stripped, m.start()),
            "excerpt": " ".join(m.group(0).split()),
            # claim value is 1; hard-fail iff the live count is 0,
            # advisory mismatch iff the live count is some other N ≠ 1.
            "fail": axiom_count == 0,
            "mismatch": axiom_count != 1,
        })

    for m in _AXIOM_GAPPED_PRESENT_RE.finditer(stripped):
        if _is_historical(m.start(), m.end()):
            continue
        findings.append({
            "kind": "gapped_present",
            "line": _line_of(stripped, m.start()),
            "excerpt": " ".join(m.group(0).split()),
            "fail": axiom_count == 0,
            "mismatch": True,
        })

    for m in _AXIOM_PLURAL_RE.finditer(stripped):
        qualifier = (m.group(2) or "").lower()
        if qualifier in ("new", "additional", "extra"):
            continue  # per-wave delta claim, not a total-count claim
        value = 0 if m.group(1).lower() == "zero" else int(m.group(1))
        if value == axiom_count:
            continue
        if _is_historical(m.start(), m.end()):
            continue
        findings.append({
            "kind": "plural_mismatch",
            "line": _line_of(stripped, m.start()),
            "excerpt": " ".join(m.group(0).split()),
            "fail": False,  # numeric plural drift is advisory-only
            "mismatch": True,
        })

    return findings


@register_check("axiom_count_prose_consistency",
                "Paper prose axiom-count claims agree with docs/counts.json")
def check_axiom_count_prose_consistency() -> CheckResult:
    """Prevent the F-flagship failure class from the 2026-06-05 external
    review: paper prose claiming "one (true) axiom" while
    ``docs/counts.json`` reports 0 project-local axioms (the
    ``gapped_interface_axiom`` was retired into the tracked Prop
    ``TPFConjecture`` on 2026-05-19; see Pipeline Invariant #15).

    Scans every ``papers/*/paper_draft.tex`` (bundle drafts AND legacy
    per-paper drafts). Failure classes:

    - **FAIL** — live axiom count is 0 and a present-tense single-axiom
      claim ("one axiom", "a single axiom", "1~axiom", "one tracked
      axiom", "the axiom \\texttt{gapped...") appears outside a
      historical-attribution context (±120 chars of
      formerly/converted/retired/"was an axiom"/2026-05-19 — the
      D2/F-style "formerly axiom gapped_interface_axiom" usage is
      legitimate and never flags).
    - **WARN (advisory)** — a numeric plural claim ("N axioms", digit or
      "zero" literal) disagrees with the live count. Word-numeral
      plurals ("three axioms" — the Son-action physics-axioms idiom in
      D1/F) and per-wave delta claims ("zero NEW axioms") are excluded
      by design. The ``\\axiomcount{}`` macro is the preferred
      mechanism and never flags (it carries no prose literal).

    LaTeX comments are stripped before scanning. Calibrated live
    2026-06-10: the sweep surfaced 16 genuinely-missed stale sites
    across D5 + 10 legacy drafts (paper4/6/7/9/11/12/17/18/20/21/26),
    all fixed in the same commit that ships this check.
    """
    counts_path = _H.PROJECT_ROOT / "docs" / "counts.json"
    if not counts_path.exists():
        return CheckResult(passed=False,
                           error=f"missing {counts_path}; run scripts/update_counts.py")
    try:
        axiom_count = int(json.loads(counts_path.read_text())["lean"]["axioms"])
    except (json.JSONDecodeError, KeyError, TypeError, ValueError) as exc:
        return CheckResult(passed=False,
                           error=f"counts.json unreadable / missing lean.axioms: {exc}")

    details: List[Detail] = []
    n_fail = 0
    n_warn = 0
    n_scanned = 0

    for tex in _H.all_paper_drafts():           # ALL drafts (bundles + legacy)
        n_scanned += 1
        try:
            text = tex.read_text()
        except OSError as exc:
            details.append(Detail(f"unreadable:{tex.parent.name}", False, str(exc)))
            n_fail += 1
            continue
        for f in _axiom_prose_findings(text, axiom_count):
            rel = f"papers/{tex.parent.name}/paper_draft.tex:{f['line']}"
            if f["fail"]:
                n_fail += 1
                details.append(Detail(
                    f"stale_axiom_claim:{tex.parent.name}:{f['line']}",
                    False,
                    f"{rel} — present-tense '{f['excerpt']}' claim but "
                    f"counts.json reports {axiom_count} project-local axioms "
                    f"(non-historical context)",
                ))
            elif f["mismatch"]:
                n_warn += 1
                details.append(Detail(
                    f"axiom_count_mismatch:{tex.parent.name}:{f['line']}",
                    True,
                    f"{rel} — '{f['excerpt']}' disagrees with counts.json "
                    f"axiom count {axiom_count} (advisory)",
                    warning=True,
                ))

    details.insert(0, Detail(
        "summary",
        n_fail == 0,
        f"axiom count {axiom_count} (docs/counts.json) vs {n_scanned} "
        f"paper drafts — {n_fail} stale single-axiom FAIL(s) / "
        f"{n_warn} advisory mismatch(es)",
    ))
    if n_fail == 0 and n_warn == 0:
        details.append(Detail(
            "all_consistent", True,
            "No non-historical axiom-count drift in any paper draft",
        ))
    return CheckResult(passed=(n_fail == 0), details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK: Paper toolchain-pin drift — Class TP (advisory)
# ═══════════════════════════════════════════════════════════════════════
# `docs/agents/claims_reviewer.md` defines Class TP (Toolchain Pin drift) as a
# STRUCTURAL check — "Literal Lean/Mathlib version in paper != project pin",
# sourced from `lean-toolchain` + `lakefile.toml`. That same doc records that
# Classes TN and HD were mirrored into validate.py "at zero-agent-cost for
# per-save CI-like invocation". TP never was, so it fired only when the
# claims-reviewer agent ran — i.e. at Stage 13.
#
# The v4.29.1 -> v4.32.0 bump (2026-07-29) made that gap load-bearing: every
# bundle draft's verification-provenance sentence went stale in a single commit,
# while Stage 13 was explicitly deferred. This check closes that window.
#
# ADVISORY by construction (always passes, warns) — mirroring
# `inventory_index_autogen_fresh`. A stale pin in a DRAFT is a provenance-hygiene
# signal, not a soundness failure, and the remedy is a publication decision that
# belongs to Stage 13: does this paper re-verify under the new pin (update the
# literal), or does it record the pin it was actually verified under (keep it,
# and say so explicitly)? A find-and-replace at gate time would silently assert
# the former for every draft. This check reports; Stage 13 decides.
#
# Two buckets, because the bump puts different kinds of sentence at risk:
#   pin-drift        — "verified by `lake build` (v4.29.1, Mathlib 5e932f97)":
#                      a reproducibility instruction that now points at a
#                      toolchain the repo no longer pins.
#   capability-claim — "Mathlib v4.29.1 has no Kunneth theorem": a justification
#                      for an in-tree construction or a tracked gap, whose truth
#                      value a Mathlib bump can silently FLIP.
#
# Third-party environments are exempt by construction: a version literal whose
# context names Aristotle (whose sandbox is pinned at v4.28.0 independently of
# our toolchain) is a fact about that service, not a claim about our pin.

_TP_LEAN_VER_RE = re.compile(r"\bv?(4\.\d+\.\d+)\b")
_TP_HEX_RE = re.compile(r"\b([0-9a-f]{8,40})\b")
_TP_THIRD_PARTY_RE = re.compile(r"aristotle|sandbox|harmonic", re.IGNORECASE)
_TP_MATHLIB_CTX_RE = re.compile(r"mathlib", re.IGNORECASE)
_TP_CAPABILITY_RE = re.compile(
    r"\b(has|have|had|lacks?|lacking|ships?|provides?|contains?|carries|"
    r"absent|missing|no longer|does not|doesn't|not (?:currently )?in)\b",
    re.IGNORECASE,
)


def _tp_live_pins() -> tuple[str | None, str | None]:
    """Read the live (toolchain_version, mathlib_rev) from the Lean project."""
    lean_root = _H.LEAN_DIR.parent
    version = None
    try:
        raw = (lean_root / "lean-toolchain").read_text(encoding="utf-8").strip()
        m = _TP_LEAN_VER_RE.search(raw)
        if m:
            version = m.group(1)
    except OSError:
        pass

    rev = None
    try:
        toml_text = (lean_root / "lakefile.toml").read_text(encoding="utf-8")
        # Find the mathlib [[require]] stanza and take its rev.
        for block in toml_text.split("[[require]]"):
            if re.search(r'name\s*=\s*"mathlib"', block):
                m = re.search(r'rev\s*=\s*"([0-9a-f]{8,40})"', block)
                if m:
                    rev = m.group(1)
                break
    except OSError:
        pass
    return version, rev


def _tp_scan_lines(lines: list[str], live_ver: str, live_rev: str
                   ) -> tuple[list[tuple[int, str]], list[tuple[int, str]]]:
    """Pure core of Class TP: scan draft lines for non-live pin literals.

    Returns ``(pin_hits, capability_hits)`` as ``(line_number, found)`` pairs.
    Split out from the check so it is unit-testable with synthetic fixtures.
    """
    pin_hits: list[tuple[int, str]] = []
    cap_hits: list[tuple[int, str]] = []
    for i, line in enumerate(lines, start=1):
        # Context window: the line plus its neighbours, so a claim split across
        # a TeX line-wrap still sees its own qualifiers.
        ctx = " ".join(lines[max(0, i - 2):i + 1])
        if _TP_THIRD_PARTY_RE.search(ctx):
            continue  # a third-party service's own pin, not ours

        stale_vers = {v for v in _TP_LEAN_VER_RE.findall(line) if v != live_ver}
        stale_revs: set[str] = set()
        if _TP_MATHLIB_CTX_RE.search(ctx):
            stale_revs = {
                h for h in _TP_HEX_RE.findall(line)
                if not (live_rev.startswith(h) or h.startswith(live_rev))
            }

        if not stale_vers and not stale_revs:
            continue

        found = ", ".join(sorted(stale_vers | stale_revs))
        # A capability claim names Mathlib AND a have/lack verb: the bump can
        # flip its truth value, which is a strictly worse failure than a stale
        # reproducibility coordinate.
        is_capability = bool(
            _TP_MATHLIB_CTX_RE.search(line) and _TP_CAPABILITY_RE.search(line)
        )
        (cap_hits if is_capability else pin_hits).append((i, found))
    return pin_hits, cap_hits


@register_check("paper_toolchain_pin_drift",
                "Advisory (Class TP): paper-draft toolchain/Mathlib pins match "
                "lean-toolchain + lakefile.toml")
def check_paper_toolchain_pin_drift() -> CheckResult:
    """Flag paper drafts whose stated Lean/Mathlib pin differs from the live pin.

    Structural mirror of claims-reviewer Class TP, so the drift is visible on
    every validate run rather than only when Stage 13 executes. Always passes;
    warnings only.
    """
    try:
        live_ver, live_rev = _tp_live_pins()
    except Exception as exc:  # defensive: an advisory never breaks the suite
        return CheckResult(passed=True, details=[
            Detail("pins", True, f"SKIPPED — could not read live pins: {exc}",
                   warning=True)])

    if live_ver is None or live_rev is None:
        return CheckResult(passed=True, details=[
            Detail("pins", True,
                   "SKIPPED — lean-toolchain / lakefile.toml pin not parseable",
                   warning=True)])

    drafts = _H.all_paper_drafts()              # ALL drafts (bundles + legacy)
    drafts += sorted(_H.PAPERS_DIR.glob("*/preprint_draft.md"))   # 1 file today
    if not drafts:
        return CheckResult(passed=True, details=[
            Detail("scan", True, "no paper drafts found — nothing to check")])

    pin_hits: list[str] = []
    cap_hits: list[str] = []

    for draft in drafts:
        try:
            lines = draft.read_text(encoding="utf-8").splitlines()
        except OSError:
            continue
        rel = f"papers/{draft.parent.name}/{draft.name}"
        file_pin, file_cap = _tp_scan_lines(lines, live_ver, live_rev)
        pin_hits += [f"{rel}:{ln} — {found}" for ln, found in file_pin]
        cap_hits += [f"{rel}:{ln} — {found}" for ln, found in file_cap]

    details: list[Detail] = []
    details.append(Detail(
        "live-pin", True,
        f"live pin: toolchain v{live_ver}, Mathlib {live_rev[:8]}"))

    for hit in pin_hits:
        details.append(Detail("pin-drift", True, f"{hit} (live v{live_ver} / "
                                                 f"{live_rev[:8]})", warning=True))
    for hit in cap_hits:
        details.append(Detail(
            "capability-claim", True,
            f"{hit} — asserts what the PINNED Mathlib does/does not provide; "
            "a pin bump can flip this", warning=True))

    n = len(pin_hits) + len(cap_hits)
    details.insert(1, Detail(
        "summary", True,
        f"scanned {len(drafts)} draft(s) — {len(pin_hits)} pin-drift, "
        f"{len(cap_hits)} capability-claim site(s) referencing a non-live pin"
        + ("; resolve at each bundle's Stage 13" if n else ""),
        warning=bool(n)))

    return CheckResult(passed=True, details=details)
