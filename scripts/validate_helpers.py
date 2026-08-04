"""Shared helpers for the validation suite — ADR-009 Phase 1.

WHAT THIS IS FOR
----------------
`scripts/validate.py` had grown 8 independent `lean_deps.json` load sites, 3
mutually inconsistent paper-draft scoping idioms, and 13 redundant `sys.path`
mutations. Each duplicate was individually reasonable and collectively a defect:
the 8 loaders disagree about what a MISSING `lean_deps.json` means (five treat it
as PASS, two as FAIL, one as a warning, one is unguarded and raises), and no
reader of any single check can see that.

This module owns **where things are and how they are read**. It deliberately does
NOT own **what their absence means** — see the policy note below.

THE POLICY LINE (ADR-009 H4) — READ BEFORE EXTENDING
----------------------------------------------------
A single `load_lean_deps()` that also decided the missing-file verdict would
silently unify eight checks' behaviour in one commit. That is a semantic change
wearing a mechanical disguise, and it is how a cleanup turns five live gates into
no-ops.

So the split is:

* **Here**: path resolution and parsing. `load_lean_deps()` RAISES on absence.
* **At each call site**: the guard, unchanged, returning that check's own
  `CheckResult` exactly as it did before.

Every call site therefore still reads `if not lean_deps_present(): return <its own
verdict>`. The divergence stays visible and is marked for the Phase-3 semantic
review, rather than being erased by a refactor nobody reviewed as a behaviour
change.

NO MEMOIZATION — still true, but NOT for the reason first written here
----------------------------------------------------------------------
`load_lean_deps()` re-reads and re-parses the 70 MB file on every call, and it
stays that way. It reads the file DIRECTLY rather than through
`extract_lean_deps.load_lean_deps()`, so it never triggers that function's
hash-guarded refresh — deliberate, and preserved.

⚠️ **This section described the pre-fix world as current until 2026-08-04 (audit
finding QI-18).** It said the readers at ~55/56/58 "currently observe the
regenerated file" while those at ~5/7/8/9 "observed the pre-regeneration one", and
concluded that caching was a Phase-3 candidate. That divergence was CLOSED by
ADR-009 §Deferred item 0: `validate.main()` now calls
:func:`ensure_lean_deps_fresh` once, before any check runs, so all eight readers
observe one snapshot. The exact positions are measured in that function's own
docstring, sixty lines below — and this section contradicted it inside the same
file, which is precisely the shape a reader cannot resolve without going to the
code.

What remains true: a cache here would still be a behaviour change rather than an
optimisation, because `counts_fresh` shells out to `update_counts.py`, which *can*
rewrite `lean/lean_deps.json` mid-run. With the up-front refresh in place the hash
guard makes that a no-op in practice, but the ordering hazard is structural and the
cache would freeze whichever state was read first. The remaining performance item
is the shared GRAPH handle, which ADR-009 §Deferred item 0 **DECLINED** on
measurement (8% of one command's runtime against a three-module signature change).
"""
from __future__ import annotations

import json
from pathlib import Path

# ── The single path anchor (ADR-009 H1) ──────────────────────────────────
# Every path in the suite derives from these two. When `validate.py` becomes
# `scripts/validate/` in Phase 2, `Path(__file__).parent` shifts by one level and
# a per-module anchor would silently retarget PROJECT_ROOT into `scripts/` —
# where every artifact lookup misses and every check takes its "absent" branch,
# turning the whole suite green while measuring nothing. Anchoring once, here,
# means that failure has exactly one place to be fixed.
SCRIPT_DIR = Path(__file__).resolve().parent
PROJECT_ROOT = SCRIPT_DIR.parent

SRC_DIR = PROJECT_ROOT / "src"
LEAN_DIR = PROJECT_ROOT / "lean" / "SKEFTHawking"
LEAN_DEPS_PATH = PROJECT_ROOT / "lean" / "lean_deps.json"
NOTEBOOKS_DIR = PROJECT_ROOT / "notebooks"
PAPERS_DIR = PROJECT_ROOT / "papers"
DOCS_DIR = PROJECT_ROOT / "docs"
COUNTS_JSON_PATH = DOCS_DIR / "counts.json"
COUNTS_TEX_PATH = DOCS_DIR / "counts.tex"


# ── lean_deps.json ───────────────────────────────────────────────────────

def lean_deps_present() -> bool:
    """True if `lean/lean_deps.json` exists. Call sites use this to keep their
    OWN missing-file verdict (see the policy note in the module docstring)."""
    return LEAN_DEPS_PATH.exists()


def load_lean_deps() -> list[dict]:
    """Parse `lean/lean_deps.json` and return its declaration records.

    RAISES `FileNotFoundError` if absent — deliberately. Deciding what absence
    means belongs to the caller; see the module docstring. Reads the file
    directly, without the hash-guarded refresh in
    `extract_lean_deps.load_lean_deps()`, matching what the inline sites did.

    Whole-run freshness is the job of :func:`ensure_lean_deps_fresh`, called once
    by `validate.main()` for a FULL run. Doing it per-call here would fire an
    ExtractDeps inside `--check native_decide_regression`, which the commit gate
    forbids (see that function's docstring).
    """
    return json.loads(LEAN_DEPS_PATH.read_text())


def ensure_lean_deps_fresh() -> tuple[bool, str]:
    """Hash-guarded refresh of `lean/lean_deps.json`. Returns `(refreshed, note)`.

    WHY THIS EXISTS — the readers disagreed with each other
    -------------------------------------------------------
    Measured 2026-08-04 against the live registry: `counts_fresh` sits at position
    **29**, and the eight `lean_deps.json` readers straddle it — **five before**
    (`tracked_hypothesis_ledger` 4, `formula_grounding` 6, `vacuous_statement_audit` 7,
    `nogo_substrate_integrity` 8, `native_decide_regression` 9) and **three after**
    (`prose_theorem_reference_coverage` 54, `theorem_name_embedded_citations` 55,
    `lean_docstring_refs_resolve` 57).

    Nothing refreshed the file before position 29, and `load_lean_deps()` reads it
    directly with no hash guard. So on exactly the runs where Lean changed — a wave
    close — the first five validated the PREVIOUS extraction while the last three
    validated the fresh one, inside a single run. Among the five is the
    `native_decide_regression` ratchet: a ratchet measuring the previous wave's
    substrate cannot see the trust surface the current wave added, which is the one
    thing it exists to catch.

    A cache would not have fixed that — it would have frozen one of the two states.
    Refreshing once, up front, makes all eight observe the same snapshot.

    SCOPE IS DELIBERATELY "FULL RUN ONLY"
    -------------------------------------
    `validate.main()` calls this only when no `--check` filter is given.
    `scripts/pre-commit-sync.sh` runs `--check native_decide_regression` in the commit
    gate and states plainly that it must NEVER run the 30-minute ExtractDeps
    (`:72-74`, and the file header: *"INCREMENTAL lean guard — never the 30-min clean
    ExtractDeps"*). Refreshing inside `load_lean_deps()` would have violated that.

    COST IS ZERO WHEN NOTHING CHANGED, AND NOT NEW WHEN IT DID
    ----------------------------------------------------------
    The guard is a SHA-256 over every `.lean` source: **46 ms** measured, against
    **150 ms** for one parse of the 70 MB artifact. When a refresh IS needed, a full
    run already pays for that same extraction at position 29 via `counts_fresh` →
    `update_counts.py`; this moves the cost earlier, it does not add it.

    Degrades to a no-op (never raises) if `extract_lean_deps` is unavailable, so a
    partial checkout behaves exactly as before.
    """
    try:
        import extract_lean_deps
    except ImportError as exc:  # pragma: no cover - partial checkout
        return False, f"skipped — extract_lean_deps unavailable ({exc})"
    try:
        if not extract_lean_deps._needs_refresh():
            return False, "lean_deps.json already fresh (hash matches .lean sources)"
        extract_lean_deps._run_extraction()
        return True, "lean_deps.json refreshed before any check read it"
    except Exception as exc:  # noqa: BLE001
        # NEVER fail the run here. Each check keeps its own missing/stale verdict
        # (H4); this is a best-effort freshening, not a gate.
        return False, f"refresh attempted and failed ({type(exc).__name__}: {exc})"


# ── counts.json ──────────────────────────────────────────────────────────

def counts_present() -> bool:
    return COUNTS_JSON_PATH.exists()


def load_counts() -> dict:
    """Parse `docs/counts.json`. Raises on absence / malformed JSON."""
    return json.loads(COUNTS_JSON_PATH.read_text())


# ── paper drafts ─────────────────────────────────────────────────────────
# TWO functions, never one with a flag. The scopes differ by design and the
# difference is load-bearing: `prose_theorem_reference_coverage` is deliberately
# bundle-only (documented in its own docstring), while the prose-hygiene checks
# cover every draft on disk. A single `paper_drafts(bundles_only=False)` would
# make that distinction an argument someone can get wrong, which is exactly how
# D10 shipped for a month outside the one gate that catches Lean-name drift.

def all_paper_drafts() -> list[Path]:
    """Every `papers/*/paper_draft.tex` on disk — bundles AND legacy per-paper
    drafts (64 today). Sorted for stable iteration order."""
    if not PAPERS_DIR.exists():
        return []
    return sorted(PAPERS_DIR.glob("*/paper_draft.tex"))


def bundle_drafts(bundle_codes) -> list[tuple[str, Path]]:
    """`(code, path)` for each publication-bundle draft that exists on disk.

    Scope is the 21 roster codes only. `bundle_codes` is passed in rather than
    imported so this module stays independent of `bundle_registry` — the roster's
    single source of truth is gated separately by
    `check_bundle_registry_consistency`, and importing it here would add a second
    consumer that gate would then have to know about.
    """
    out: list[tuple[str, Path]] = []
    for code in bundle_codes:
        tex = PAPERS_DIR / code / "paper_draft.tex"
        if tex.exists():
            out.append((code, tex))
    return out
