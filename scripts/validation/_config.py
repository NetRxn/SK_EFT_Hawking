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

#: Recompile every bundle draft, bypassing `paper_latex_compiles`' per-draft
#: content-hash cache. Set from `--force-latex`.
#:
#: ⚠️ MEANING CHANGED 2026-08-05. This used to *enable* the check at all: without
#: it `paper_latex_compiles` returned `passed=True` with detail "SKIPPED (slow)".
#: That is how the suite reported green while D3 carried two fatal compile errors
#: — a check whose default was not to measure. The compile is now always on and
#: costs ~0 s when no draft moved (see `validation/_memo.py`), so this flag now
#: only forces a re-compile of unchanged drafts.
FORCE_LATEX: bool = False

#: Bypass the expensive-check memo (`validation/_memo.py`) and re-measure
#: everything. Set from `--no-memo`; also implied by `--strict`, so the Paper
#: Submission Gate never reads a cached verdict.
NO_MEMO: bool = False

#: Unattended-runner mode. Set from `--ci`. Read by `validate.main()` (NOT by any
#: check body) to skip the checks whose premise does not hold on a fresh clone, and
#: to enforce a coverage floor.
#:
#: WHY A MODE AND NOT A CHECK LIST: a hardcoded list in a workflow file drifts from
#: the registry silently — the failure this audit found in `EXPECTED_CHECKS`,
#: `_REGENERATORS` and `validation_checks()`. The exclusions live next to the code
#: that justifies them.
#:
#: MEASURED, and this is the whole reason the mode exists: on a real `git clone`
#: of this branch, `docs/counts.json` is written BEFORE `src/`, `lean/` and
#: `papers/` — so all four of `counts_fresh`'s staleness criteria read STALE on an
#: untouched checkout, and it shells out to `update_counts.py` (1800 s timeout,
#: needs `lake`). mtime freshness is a workstation convenience; on a runner it is
#: noise that costs half an hour.
CI_MODE: bool = False

#: Checks skipped under `--ci`, each with the reason. Kept HERE rather than in a
#: workflow file so the justification travels with the exclusion.
CI_SKIP: dict[str, str] = {
    "counts_fresh": "mtime-based; every criterion reads stale on a fresh clone, then "
                    "shells to update_counts.py (1800s, needs lake)",
    "tables_fresh": "same mtime premise; shells to render_paper_tables.py (300s). "
                    "Content is covered by `paper_table`, which parses the shipped "
                    "table (QI-31)",
    "claim_clusters_fresh": "same mtime premise; shells to cluster_detect.py",
    "notebook_exec": "the per-notebook skip-cache is gitignored, so a fresh runner "
                     "executes all 91 from cold. On a workstation this check is "
                     "already change-scoped twice over (the skip-cache, plus "
                     "scripts/pre-commit-notebooks.sh executing only STAGED "
                     "notebooks), and `notebooks/` moved in 3 of the last 400 "
                     "commits — so the cost is an artifact of the runner, not of "
                     "the check",
}

#: The coverage floor for `--ci`. **This is the point of the mode.**
#:
#: Dropping the Lean toolchain from a runner makes the suite ~200 s faster and stops
#: 7 checks that read `lean_deps.json` plus 3 that shell to `lake` from measuring
#: anything — while the run still reports green. That is "absence of measurement
#: rendered as success" reintroduced at the CI layer, which is the finding this
#: entire audit exists to close.
#:
#: ⚠️ COUNTS MEASUREMENTS, NOT INVOCATIONS (fixed 2026-08-05). As first written the
#: floor compared `len(results)`, which `run_checks` fills for every registered spec —
#: so it was identically 55 against a floor of 55 and could never fire. Four reviewers
#: found that independently. `validate.main()` now counts `r.measured`.
#:
#: So `--ci` FAILS when fewer checks MEASURE than this. A missing toolchain becomes a
#: red build reading "48 of 55 ran", not a green tick. Lower it only with a stated
#: reason, exactly like every other ratchet in this codebase.
CI_MIN_CHECKS_RUN: int = 58
