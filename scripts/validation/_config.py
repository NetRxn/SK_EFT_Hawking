"""Runtime flags for the validation suite — ADR-009 H5.

WHY THIS MODULE EXISTS
----------------------
Three flags are set by `validate.main()` from the CLI and read inside check
bodies:

    STRICT_MODE            promotes paper-submission advisories to hard failures
    FORCE_LATEX            runs the slow-gated pdflatex check
    FORCE_NOTEBOOK_REEXEC  bypasses the notebook-execution skip-cache

While every check lived in one file these were module globals and a plain name
lookup always saw the current value. Split across modules that stops being true:

    from validate import STRICT_MODE     # binds a COPY at import time

`main()` then sets `validate.STRICT_MODE = True`, the copy stays `False`, and
every affected check silently takes its non-strict branch. Nothing raises,
`--strict` becomes a no-op, and the suite still reports green — the failure shape
this project has shipped eight times.

**A structural `co_names` test does NOT catch this.** The imported copy is still
a global lookup, so the flag name still appears in the function's `co_names` —
just resolving against the wrong module's namespace. That gap was found while
planning this split, in the guard written for exactly this hazard.

THE RULE
--------
Reach a flag by **attribute access on this module**, never by importing its
value:

    from validation import _config
    ...
    if _config.STRICT_MODE:            # ✅ resolved at call time, always current

    from validation._config import STRICT_MODE
    if STRICT_MODE:                    # ❌ frozen at import time

This module imports nothing from the suite, so it can be imported from anywhere
without a cycle. `tests/test_validate_flag_propagation.py` asserts that no check
module carries a flag in its own namespace.
"""
from __future__ import annotations

#: Promote paper-submission advisory warnings to hard failures. Set by
#: `validate.main()` from `--strict`. Read by `parameter_provenance`,
#: `axiom_closure_allowlist`, `provenance_doi_in_registry`,
#: `bundle_source_freshness`, `bibitem_title_primary_source`,
#: `theorem_name_embedded_citations`.
STRICT_MODE: bool = False

#: Bypass the notebook-execution skip-cache and re-execute every notebook. Set
#: from `--force-notebooks`. A silently-stuck `False` makes `notebook_exec`
#: return cached verdicts without executing anything.
FORCE_NOTEBOOK_REEXEC: bool = False

#: Run the slow-gated `paper_latex_compiles` check. Set from `--force-latex`, or
#: automatically when that check is the explicitly selected `--check` (otherwise
#: `--check paper_latex_compiles` would skip the very check it names). A
#: silently-stuck `False` makes it skip forever.
FORCE_LATEX: bool = False
