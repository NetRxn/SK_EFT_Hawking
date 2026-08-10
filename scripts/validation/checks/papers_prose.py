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
  error, on EVERY run. ⚠️ This bullet read "it is still slow-gated behind
  `_cfg.FORCE_LATEX`, so a default full run skips it" until 2026-08-05 — written
  true, then left standing when that same day's commit deleted the slow gate in
  THIS FILE. `--force-latex` now only bypasses the per-draft content-hash cache.
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
import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import Dict, List

import validate_helpers as _H
from validation import _config as _cfg
from validation import _memo
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
                "Paper figure references resolve and no placeholder bibliography ships")
def check_paper_provenance() -> CheckResult:
    """Verify every draft's `\\includegraphics{}` resolves on disk and no draft
    ships a placeholder figure box or bibliography entry. All 64 drafts.

    ⚠️ THE THEOREM-REFERENCE LEG WAS REMOVED 2026-08-05 (audit finding QI-32).
    It read:

        texttt_refs = re.findall(r'\\\\texttt\\{([a-z_][a-zA-Z0-9_]*)\\}', tex)
        theorem_refs = [r for r in texttt_refs if '_' in r]

    and the character class cannot cross a backslash — but LaTeX escapes `_` as
    `\\_`, so a reference to `wen_adw_factor` is written `\\texttt{wen\\_adw\\_factor}`
    and never matched. `theorem_refs` was therefore the subset of matches
    containing an underscore, of a population that by construction contained
    none. Measured across all 64 drafts: **480 raw matches, 0 with `_`, against
    1,963 `\\texttt{}` blocks containing `\\_`.** The leg had been empty since the
    regex landed on 2026-03-26, and it FAILED loudly on nothing for five months
    while printing "N theorem references verified" for zero references.

    ⚠️ It is also the leg audit finding QI-01 "fixed": the `glob`→`rglob` repair
    was applied to a population that was already empty, and the "verdict movement:
    zero" recorded then as evidence the exposure was latent was in fact evidence
    the leg was dead.

    It is NOT revived here. Resolving a Lean name cited in prose is
    `prose_lean_refs`'s question, not this module's — this module asks whether the
    prose agrees with the numbers (ADR-009's stated seam) — and `prose_lean_refs`
    already owns a real extractor (`\\_`-unescaping, candidate filter) and a real
    resolver (Mathlib / PhysLib / private namespaces, disclaimer and negation
    context, documented waivers) where this leg had a raw `theorem `-line grep.
    The 43 legacy drafts this leg nominally covered are picked up by that check's
    new legacy leg, under a measured ratchet. See
    `check_prose_theorem_reference_coverage`.
    """
    details = []
    all_pass = True

    for tex_file in _H.all_paper_drafts():     # ALL drafts (bundles + legacy)
        paper_dir = tex_file.parent
        tex = tex_file.read_text()

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
        return CheckResult(passed=True, measured=False, details=[
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
        return CheckResult(passed=True, measured=False, details=[
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


#: Local (git-ignored) per-draft compile cache: bundle code -> content hash of the
#: draft's full input closure at its last clean compile. Mirrors
#: `NOTEBOOK_EXEC_CACHE` and the `extract_lean_deps.py` hash-skip.
LATEX_COMPILE_CACHE = "papers/.latex_compile_cache.json"

#: Hand-written `\begin{tabular}` blocks still in publication-target bundle drafts.
#: MEASURED 2026-08-05: **4** across 3 bundles — D1 (1), E1 (1), L2 (2). Zero
#: headroom; this may only shrink.
#:
#: The discharge is a `papers/<bundle>/tables.py` spec per table, rendered by
#: `scripts/render_paper_tables.py` — NOT deleting the table.
BUNDLE_HANDWRITTEN_TABLE_CEILING = 4


@register_check("bundle_tables_use_pipeline",
                "Bundle drafts source tables from the pipeline (\\input{tables/}), "
                "not hand-written tabulars (ratcheted)")
def check_bundle_tables_use_pipeline() -> CheckResult:
    r"""A publication-target bundle must take tabular content from the table
    pipeline rather than hand-authoring it.

    WHY (git archaeology, `68899aef` 2026-04-15, the pipeline's originating commit):
    *"After this lands, tabular numerical claims cannot drift from the canonical
    pipeline: every value comes from an autogenerated tex snippet produced by a
    declarative spec."* A hand-written `\begin{tabular}` in a bundle re-opens
    exactly the drift that commit closed — and `BUNDLE_LIFT_PROCEDURE.md` §7 makes
    it procedure: *"Replace inline numerical literals with
    `\input{tables/<spec_id>.tex}`."*

    MEASURED 2026-08-05: **zero of 21 bundles have a `tables.py`**, while 3 carry
    hand-written tabulars. The pipeline exists, is tested, and no bundle is wired
    to it — so its guarantee currently protects only the legacy per-paper drafts it
    was retrofitted onto.

    RATCHETED rather than hard-failed on day one: 4 tables pre-exist, and a bare
    FAIL would redden the suite on debt with no discharge path in the same commit.
    The ceiling may only shrink. Discharge = add the `tables.py` spec, not delete
    the table.

    Scope is BUNDLE_CODES — publication targets. Legacy `papers/paperN_*/` drafts
    are substrate, explicitly out of review scope (`BUNDLE_LIFT_PROCEDURE.md` §188).
    """
    details: List[Detail] = []
    offenders: List[tuple[str, int, int]] = []
    n_seen = 0

    for code in BUNDLE_CODES:
        tex = _H.PAPERS_DIR / code / "paper_draft.tex"
        if not tex.is_file():
            continue
        n_seen += 1
        body = _strip_tex_comments(tex.read_text(errors="replace"))
        hand = len(re.findall(r"\\begin\{tabular\}", body))
        piped = len(re.findall(r"\\input\{tables/", body))
        if hand:
            offenders.append((code, hand, piped))

    if not n_seen:
        return CheckResult(passed=False, measured=False, details=[Detail(
            "drafts", False,
            "no bundle drafts found — UNVERIFIED, not passing")])

    total = sum(h for _, h, _ in offenders)
    over = total > BUNDLE_HANDWRITTEN_TABLE_CEILING
    details.append(Detail(
        "summary", not over,
        f"{total} hand-written tabular(s) across {len(offenders)} of {n_seen} bundle "
        f"draft(s) (ceiling {BUNDLE_HANDWRITTEN_TABLE_CEILING})"
        + (f" — EXCEEDS by {total - BUNDLE_HANDWRITTEN_TABLE_CEILING}" if over
           else f" — {BUNDLE_HANDWRITTEN_TABLE_CEILING - total} below; LOWER THE CEILING "
                f"in the same commit" if total < BUNDLE_HANDWRITTEN_TABLE_CEILING else ""),
        warning=(bool(total) and not over)))
    for code, hand, piped in offenders:
        details.append(Detail(
            f"bundle:{code}", not over,
            f"{code}: {hand} hand-written tabular(s), {piped} \\input{{tables/}} — add a "
            f"papers/{code}/tables.py spec and render with render_paper_tables.py",
            warning=not over))
    return CheckResult(passed=not over, details=details)


@register_check("paper_latex_compiles",
                "Every papers/*/paper_draft.tex compiles under pdflatex — bundles "
                "HARD-FAIL, legacy drafts ratchet; per-draft content-hash cache "
                "(--force-latex recompiles all)")
def check_paper_latex_compiles() -> CheckResult:
    """Compile each bundle draft with ``pdflatex`` and HARD-FAIL on fatal
    (``! ``-marked) breakage.

    Why this exists: the 2026-06-10 paper15 incident — 108 fatal LaTeX
    errors injected by unescaped ``&``/``_`` and an executed ``\\input{}``
    in autogenerated tables — was invisible to *every* structural check.
    Only a real compile catches a draft that no longer builds. The fix
    (table-generator escaping in ``scripts/paper_tables/sources.py``) is
    durable, but a compile gate prevents the next such regression.

    Posture:
      - **Always on, change-scoped.** ⚠️ CHANGED 2026-08-05. This was
        *slow-gated*: without ``--force-latex`` it returned ``passed=True``
        with detail "SKIPPED (slow)", so a plain ``validate.py`` reported this
        check green while D3 carried two fatal errors. A gate whose default is
        not to measure is the audit's central defect class, and the "slow"
        premise was never re-measured: pdflatex × 21 bundle drafts is **16.6 s**,
        not the "minutes" the docstring claimed. With the per-draft cache below
        an unchanged corpus costs ~0 s, so there is nothing left to gate on.
      - **Blocking**: a fatal compile error FAILS the check. Repaired
        2026-08-03 (ADR-009 §Deferred item **3**); it previously computed the
        verdict and discarded it. Transient toolchain gaps cannot reach that
        branch — pdflatex-missing returns above — so what remains is a draft a
        working pdflatex could not compile. ⚠️ This bullet read "**Advisory**:
        always ``passed=True``" for a day after the repair (audit finding QI-13).

    **Per-draft cache**: a draft whose full input closure
    (:func:`validate_helpers.draft_input_closure` — the ``.tex``, everything it ``\\input``s
    transitively, its figures, its ``.bib``) hashes to the value recorded at its
    last CLEAN compile is skipped. Only clean compiles are recorded and a failure
    evicts, so a broken draft recompiles every run until it is fixed.
    ``--force-latex`` bypasses the cache entirely.

    One non-stop pass per draft (enough to surface fatal breakage; full
    reference/citation resolution is out of scope for a build gate).
    Compiles with the paper dir as cwd (so relative ``\\input``/
    ``\\includegraphics`` resolve) and ``-output-directory`` pointed at a
    throwaway temp dir (so no ``.aux``/``.log``/``.pdf`` lands in the repo).
    """
    details: List[Detail] = []

    pdflatex = shutil.which("pdflatex")
    if pdflatex is None:
        return CheckResult(passed=True, measured=False, details=[Detail(
            "toolchain", True,
            "SKIPPED — pdflatex not on PATH (install a TeX distribution)")])

    n_ok = 0
    n_missing = 0
    n_cached = 0
    failed: List[tuple[str, int, str]] = []  # (code, n_fatal, first_error)

    # ⚠️ THE BYPASS SET MUST MATCH `_memo`'s (fixed 2026-08-05, reviewer R4-I1).
    # This cache was gated on `_cfg.FORCE_LATEX` alone, so `--strict`, `--no-memo`
    # and `SKEFT_VALIDATION_NO_MEMO=1` all read it — while `_memo`'s docstring
    # claimed, for both caches, that the Paper Submission Gate "always re-measures".
    # Two caches with two different bypass rules and one docstring covering both is
    # exactly how a guarantee becomes false without anyone editing it.
    # ⚠️ `SKEFT_VALIDATION_NO_MEMO` NO LONGER BYPASSES *THIS* CACHE, and the two
    # caches are different animals — which is the whole point of the paragraph
    # above. The VERDICT memo is keyed on a check name, so a patched test run can
    # poison a key a real run later reads: `conftest.py` is right to disable it
    # suite-wide. THIS cache is keyed on each draft's own content closure, so a
    # test that seeds a defect changes the hash and correctly misses — there is
    # nothing to poison.
    #
    # Conflating them cost 41.84 s per run: every `-m slow` recompiled all 64
    # drafts with pdflatex to re-derive an answer the content hash already had.
    # `SKEFT_VALIDATION_NO_LATEX_CACHE=1` is the escape hatch for anyone who
    # genuinely wants a forced recompile, and `--force-latex` still does it.
    _bypass_cache = (_cfg.FORCE_LATEX or _cfg.STRICT_MODE
                     or os.environ.get("SKEFT_VALIDATION_NO_LATEX_CACHE") == "1")

    cache_path = _H.PROJECT_ROOT / LATEX_COMPILE_CACHE
    prev_clean: Dict[str, str] = {}
    if not _bypass_cache:
        try:
            loaded = json.loads(cache_path.read_text())
            if isinstance(loaded, dict):
                prev_clean = loaded.get("clean", {}) or {}
        except (OSError, json.JSONDecodeError):
            prev_clean = {}   # fail-safe: an unreadable cache compiles everything
    new_clean: Dict[str, str] = {}

    # Bundles hard-fail; LEGACY drafts ratchet. Both are compiled: this check exists
    # because of a fatal-error incident in `paper15_methodology`, which is a legacy
    # draft, so a bundle-only population cannot see the very class it was built for.
    legacy_failed: List[tuple] = []
    legacy_codes = sorted(
        d.name for d in _H.PAPERS_DIR.iterdir()
        if d.is_dir() and d.name not in set(BUNDLE_CODES)
        and (d / "paper_draft.tex").is_file())

    for code in list(BUNDLE_CODES) + legacy_codes:
        is_bundle = code in set(BUNDLE_CODES)
        sink = failed if is_bundle else legacy_failed
        tex = _H.PAPERS_DIR / code / "paper_draft.tex"
        if not tex.is_file():
            n_missing += 1
            continue

        closure_hash = _memo.files_fingerprint(_H.draft_input_closure(tex))
        if not _bypass_cache and prev_clean.get(code) == closure_hash:
            n_cached += 1
            n_ok += 1
            new_clean[code] = closure_hash
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
                sink.append((code, -1, "compile timed out (>180s)"))
                continue
            except Exception as exc:  # noqa: BLE001 — advisory: never hard-error
                sink.append((code, -1, f"compile invocation failed: {exc}"))
                continue
            log_path = Path(out_dir) / "paper_draft.log"
            log = log_path.read_text(errors="replace") if log_path.is_file() else ""
            fatal = _LATEX_FATAL_RE.findall(log)
            if fatal:
                # Capture the first "! ..." error line for the report.
                m = re.search(r"^(! .*)$", log, re.MULTILINE)
                first = m.group(1).strip()[:90] if m else "(see log)"
                sink.append((code, len(fatal), first))
            else:
                n_ok += 1
                new_clean[code] = closure_hash

    # Only clean compiles are recorded, so a failing draft never acquires a key and
    # recompiles every run until fixed. Written even when nothing changed: the file
    # is how a fresh checkout starts warming.
    if not _bypass_cache:
        try:
            cache_path.write_text(json.dumps(
                {"clean": new_clean}, indent=2, sort_keys=True))
        except OSError:
            pass

    from src.core.constants import LEGACY_DRAFT_LATEX_BROKEN_CEILING as _LEG_CEIL
    if len(legacy_failed) > _LEG_CEIL:
        details.append(Detail(
            "legacy_ratchet", False,
            f"{len(legacy_failed)} legacy draft(s) fail to compile, above the frozen "
            f"ceiling of {_LEG_CEIL}. A NEW legacy draft was broken — commonly by an "
            f"unescaped character in a GENERATED table, which is how this check's "
            f"originating incident happened. Fix it, or raise "
            f"LEGACY_DRAFT_LATEX_BROKEN_CEILING in src/core/constants.py with a stated "
            f"reason in the same commit. Broken: "
            f"{', '.join(c for c, _n, _f in legacy_failed)}"))
    elif legacy_failed:
        details.append(Detail(
            "legacy_ratchet", True,
            f"{len(legacy_failed)} legacy draft(s) fail to compile, at or under the "
            f"frozen ceiling {_LEG_CEIL} (inherited debt; repair is ADR-010 scope): "
            f"{', '.join(c for c, _n, _f in legacy_failed)}", warning=True))

    # "clean", not "compiled clean": `n_ok` counts cached drafts too, and a detail
    # line that says a draft compiled when nothing ran is the same overstatement
    # this check's own history is about.
    details.append(Detail(
        "summary",
        len(failed) == 0,
        f"{n_ok}/{n_ok + len(failed) + len(legacy_failed)} drafts clean "
        f"({len(BUNDLE_CODES) - len(failed)}/{len(BUNDLE_CODES)} bundles, "
        f"{len(legacy_codes) - len(legacy_failed)}/{len(legacy_codes)} legacy) — "
        f"{n_cached} from cache, {n_ok - n_cached} freshly compiled, "
        f"{n_missing} missing skipped; {len(failed)} BUNDLE failure(s), "
        f"{len(legacy_failed)} legacy (ratcheted)"
    ))
    if n_cached:
        details.append(Detail(
            "skip_cache", True,
            f"{n_cached} draft(s) unchanged since their last clean compile — "
            f"not recompiled; --force-latex recompiles all"))
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
    # development. That case is handled ABOVE by the pdflatex-missing early return.
    # (It was also handled by the slow-gate skip, which is gone as of 2026-08-05 —
    # that "safety" was the check declining to measure at all.) What remains when
    # we reach here is a draft that a working pdflatex could not compile — which is
    # a real defect, and the incident this check was built for (108 fatal errors
    # injected by unescaped & / _ in generated tables) is exactly that.
    #
    # Measured at the moment of the fix: 20/21 clean, **D3 fails with 2 fatal errors
    # ("! Undefined control sequence")** — reported as a passing ⚠ WARN for as long
    # as the check has existed.
    # BOTH legs bind: a bundle failure, and a legacy ratchet BREACH. Returning only
    # `len(failed) == 0` would compute the legacy verdict and discard it — the same
    # shape this check's own history is about, one leg further in.
    _legacy_breach = len(legacy_failed) > _LEG_CEIL
    return CheckResult(passed=(len(failed) == 0 and not _legacy_breach), details=details)


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
    counts_path = _H.COUNTS_JSON_PATH   # one owner (audit QI-11); was re-derived
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


def _tp_live_dep_revs() -> dict[str, str]:
    """Every `rev` currently pinned in `lakefile.toml`, keyed by dependency name.

    DERIVED, not hand-listed: a `[[require]]` stanza added later is picked up
    without editing this function. Exists because `_tp_live_pins` returns only
    Mathlib's rev, so a sentence naming Mathlib and PhysLib together had the
    PhysLib hash compared against Mathlib's and a CORRECT pin reported as drift
    (TODO-D22; D11 and D12 both hit it). Citing any currently-pinned rev is
    accurate, so the test is membership in this set, not equality with one rev.
    """
    revs: dict[str, str] = {}
    try:
        toml_text = (_H.LEAN_DIR.parent / "lakefile.toml").read_text(encoding="utf-8")
    except OSError:
        return revs
    for block in toml_text.split("[[require]]")[1:]:
        n = re.search(r'name\s*=\s*"([^"]+)"', block)
        r = re.search(r'rev\s*=\s*"([0-9a-f]{8,40})"', block)
        if n and r:
            revs[n.group(1).lower()] = r.group(1)
    return revs


def _tp_scan_lines(lines: list[str], live_ver: str, live_rev: str,
                   other_revs: frozenset[str] = frozenset()
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
            live_set = {live_rev, *other_revs}
            stale_revs = {
                h for h in _TP_HEX_RE.findall(line)
                if not any(lr.startswith(h) or h.startswith(lr)
                           for lr in live_set if lr)
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
        # Every other currently-pinned dep rev (PhysLib, repl, ...). Citing any
        # of them is accurate; comparing them to Mathlib's rev is TODO-D22.
        other_revs = frozenset(
            v for k, v in _tp_live_dep_revs().items() if k != "mathlib")
    except Exception as exc:  # defensive: an advisory never breaks the suite
        return CheckResult(passed=True, measured=False, details=[
            Detail("pins", True, f"SKIPPED — could not read live pins: {exc}",
                   warning=True)])

    if live_ver is None or live_rev is None:
        return CheckResult(passed=True, measured=False, details=[
            Detail("pins", True,
                   "SKIPPED — lean-toolchain / lakefile.toml pin not parseable",
                   warning=True)])

    drafts = _H.all_paper_drafts()              # ALL drafts (bundles + legacy)
    drafts += sorted(_H.PAPERS_DIR.glob("*/preprint_draft.md"))   # 1 file today
    if not drafts:
        # ⚠️ `measured=False`, matching the two siblings a dozen lines above which had
        # it right. An empty draft population is the ADR-009 H1 anchor-retarget
        # scenario — a moved module makes the glob return nothing — and this branch
        # converted it into measured green. The correct version of it was already in
        # this file; that adjacency is this branch's signature failure mode.
        return CheckResult(passed=True, measured=False, details=[
            Detail("scan", True, "no paper drafts found — nothing to check",
                   measured=False)])

    pin_hits: list[str] = []
    cap_hits: list[str] = []

    for draft in drafts:
        try:
            lines = draft.read_text(encoding="utf-8").splitlines()
        except OSError:
            continue
        rel = f"papers/{draft.parent.name}/{draft.name}"
        file_pin, file_cap = _tp_scan_lines(lines, live_ver, live_rev,
                                            other_revs=other_revs)
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


# ═══════════════════════════════════════════════════════════════════════
# CHECK: bundle cross-references resolve (a `??` in a rendered PDF)
# ═══════════════════════════════════════════════════════════════════════

_LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
_REF_RE = re.compile(r"\\(?:eq|c|C)?ref\{([^}]+)\}")


@register_check(
    "bundle_cross_references_resolve",
    "Every \\ref in a bundle draft has a matching \\label somewhere in its input closure")
def check_bundle_cross_references_resolve() -> CheckResult:
    """CHECK: a `\\ref` with no `\\label` renders as a literal `??` to the reader.

    **Found 2026-08-09 in D3**, the heaviest bundle: `\\S\\ref{sec:cfl-z3-matching}` and
    two `\\S\\ref{sec:singularity-thms}` named labels that do not exist, so the 58-page
    PDF carried three *"see Section ??"*. Both target sections were present under other
    labels (`sec:cfl`, `sec:penrose`); the references had simply never been repointed.

    ⚠️ **The measurement existed and reached no gate.** `compile_bundle_pdf.py` reports
    `unresolved_refs_in_pdf` and treats a nonzero value as failure, and
    `BUNDLE_LIFT_PROCEDURE.md` §7 forbids invoking Stage 9 until the draft *"compiles
    cleanly"*. But `paper_latex_compiles` hard-fails on fatal `!`-marked breakage only,
    by design and as its docstring says, so it reported **21/21 bundles clean** on the
    same tree where a direct `compile_bundle_pdf.py D3` reported FAIL. Two instruments,
    one corpus, opposite verdicts.

    ⚠️ **And the failing verdict was already committed.** `papers/D3/bundle_metadata.json`
    carried `compile_gate_ok: false` in tracked state. That field has one writer
    (`compile_bundle_pdf.py`) and **no readers**, so the suite reported 21/21 clean over a
    recorded failure sitting in the repository. A verdict nobody consumes is worse than an
    absent one: it looks like diligence in the diff.

    **Why this is a static scan and not a leg of `paper_latex_compiles`.** Two reasons,
    and each rules out the cheaper option on its own:

    * *A single pdflatex pass cannot tell the difference.* Reference resolution needs the
      `.aux` from a prior pass, so on run one LaTeX warns `Reference ... undefined` for
      **every** reference in the file. `paper_latex_compiles` runs one pass, so its log
      cannot distinguish a dangling label from a not-yet-resolved one.
    * *That check is cache-gated.* It skips any draft whose input closure is unchanged,
      so a leg living inside it would silently not run on exactly the drafts nobody has
      touched, which is where a stale reference survives longest.

    Labels are collected across the **whole input closure** (`_H.draft_input_closure`),
    not just the draft, so a label defined in a generated `tables/*.tex` counts. That
    helper is the same one `paper_latex_compiles` and `bundle_manuscript_length` use, so
    three consumers cannot disagree about which files belong to a draft.

    **Zero headroom, deliberately: the corpus measured clean across all 21 bundles after
    the D3 repair.** A ratchet with slack here would permit a `??` to reach a referee.

    ⚠️ **UNMEASURABLE is not PASS.** An unreadable or absent draft is counted and named,
    and a run that reaches no draft at all returns `measured=False`.
    """
    codes, _roster_err = _H.bundle_codes_or_unmeasured()
    if codes is None:
        return CheckResult(passed=False, measured=False, details=[Detail(
            "roster", False, _roster_err)])

    details: List[Detail] = []
    dangling: dict[str, list[str]] = {}
    unread: List[str] = []
    scanned = 0
    total_refs = 0

    for code in codes:
        tex = _H.PAPERS_DIR / code / "paper_draft.tex"
        if not tex.is_file():
            unread.append(code)
            continue
        try:
            labels: set[str] = set()
            for f in _H.draft_input_closure(tex):
                if f.suffix.lower() in {".tex", ".sty", ""} and f.is_file():
                    labels |= set(_LABEL_RE.findall(f.read_text(errors="replace")))
            body = tex.read_text(errors="replace")
            labels |= set(_LABEL_RE.findall(body))
            refs = _REF_RE.findall(body)
        except OSError:
            unread.append(code)
            continue
        scanned += 1
        total_refs += len(refs)
        missing = sorted({r for r in refs if r not in labels})
        if missing:
            dangling[code] = missing

    if unread:
        details.append(Detail(
            "unread", True,
            f"{len(unread)} bundle draft(s) could not be read, so their cross-references "
            f"are UNKNOWN: {', '.join(sorted(unread))}", warning=True))

    # Seam guard (authoring-guide §2.5): a scan that reached nothing passes vacuously.
    if not scanned or not total_refs:
        details.append(Detail(
            "seam", False,
            f"scanned {scanned} draft(s) carrying {total_refs} reference(s) — an empty "
            f"population cannot evidence resolvable references; UNVERIFIED, not passing"))
        return CheckResult(passed=False, measured=False, details=details)

    for code, missing in sorted(dangling.items()):
        details.append(Detail(
            f"dangling:{code}", False,
            f"{code}: {len(missing)} \\ref target(s) have no \\label anywhere in the "
            f"draft's input closure, so each renders as `??` to a reader: "
            f"{', '.join(missing)}. Repoint to the live label or add the missing one"))

    details.append(Detail(
        "summary", not dangling,
        f"{scanned} bundle draft(s) scanned, {total_refs} reference site(s), "
        f"{sum(len(v) for v in dangling.values())} unresolved (target 0)"))
    return CheckResult(passed=not dangling, details=details)
