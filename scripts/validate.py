#!/usr/bin/env python3
"""
SK-EFT Hawking Project — Cross-Layer Validation Suite
=====================================================

Single entry point for verifying consistency across:
  Python source  ↔  Lean formal proofs  ↔  Notebooks  ↔  Papers

Usage
-----
    # From project root (recommended):
    python scripts/validate.py

    # With JSON output for CI:
    python scripts/validate.py --json

    # Save timestamped report to docs/validation/reports/:
    python scripts/validate.py --archive

    # Run a single check:
    python scripts/validate.py --check formulas

    # List available checks:
    python scripts/validate.py --list

Exit Codes
----------
    0 — all checks passed
    1 — one or more checks failed
    2 — script error (bad arguments, missing files)

Architecture & Extensibility
----------------------------
Each check is a function decorated with @register_check. To add a new check:

    @register_check("my_new_check", "Description of what it validates")
    def check_my_new_thing() -> CheckResult:
        ...
        return CheckResult(passed=True, details=[...])

The decorator handles registration, output formatting, and CI integration.
Checks are run in registration order, and any check can be run individually
via --check <name>.

Design Decisions
----------------
- Pure stdlib (no pytest dependency for the validation itself).
  This means validation works even if the test environment is degraded.
- Path-agnostic: resolves PROJECT_ROOT from this file's location,
  works from any working directory.
- Timestamped archival: --archive writes a dated JSON + text report
  to docs/validation/reports/ for historical tracking.
- Lean integration: if `lake` is on PATH, runs `lake build` as a check.
  If not available, skips gracefully with a warning.
"""

from __future__ import annotations

import argparse
import ast
import hashlib
import importlib
import json
import re
import shutil
import subprocess
import sys
import tempfile
import time
from dataclasses import asdict          # `dataclass`/`field` moved with the result types
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List, Optional  # `Callable` moved with `register_check`

# ═══════════════════════════════════════════════════════════════════════
# Path resolution
# ═══════════════════════════════════════════════════════════════════════

# Bootstrap only — the minimum needed to make sibling modules importable. Every
# other path below is an ALIAS of `validate_helpers`, which owns the anchor.
_BOOTSTRAP_SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(_BOOTSTRAP_SCRIPT_DIR.parent))   # repo root, so `src.*` imports
if str(_BOOTSTRAP_SCRIPT_DIR) not in sys.path:          # siblings (tests import this module)
    sys.path.insert(0, str(_BOOTSTRAP_SCRIPT_DIR))

from bundle_registry import BUNDLE_CODES as _REGISTRY_BUNDLE_CODES  # noqa: E402
# ADR-009 Phase 1: shared path anchors + artifact loaders. Owns WHERE things are
# and HOW they are read; each call site keeps its OWN verdict on absence (H4).
import validate_helpers as _H  # noqa: E402
# ADR-009 H5: runtime flags live in ONE module, reached by ATTRIBUTE ACCESS so the
# value is resolved at call time. Importing them by value binds a copy at import
# time and silently freezes --strict once the checks are split across modules.
from validation import _config as _cfg  # noqa: E402

# ── Path anchors — ALIASES, not independent derivations (ADR-009 H1) ─────
# These were each computed from `Path(__file__)`. That is safe while this file
# lives at `scripts/validate.py` and silently wrong the moment it becomes
# `scripts/validate/__init__.py`: `PROJECT_ROOT` would resolve to `scripts/`,
# every artifact lookup would miss, every check would take its "absent" branch,
# and the suite would go GREEN having measured nothing. Aliasing a single anchor
# in `validate_helpers` (which stays at `scripts/`) makes the Phase-2 move
# provably path-neutral instead of a silent catastrophe.
SCRIPT_DIR = _H.SCRIPT_DIR
PROJECT_ROOT = _H.PROJECT_ROOT
SRC_DIR = _H.SRC_DIR
LEAN_DIR = _H.LEAN_DIR
NOTEBOOKS_DIR = _H.NOTEBOOKS_DIR
PAPERS_DIR = _H.PAPERS_DIR
def _reports_dir():
    # ⚠️ H1: resolved AT EACH USE, not bound at import. A module-level
    # `X = _H.ANCHOR / "..."` is an import-time COPY: a test monkeypatching the
    # anchor does not reach it, so the check silently reads the PRODUCTION tree
    # while the test believes it is reading a fixture. Converted 2026-08-05
    # (PR-review pass 2, R3-I5 / R1).
    return _H.DOCS_DIR / "validation" / "reports"


# ═══════════════════════════════════════════════════════════════════════
# Data structures + registry — RE-EXPORTED from `validation._registry`
# ═══════════════════════════════════════════════════════════════════════
# These moved out so that `validation/checks/*.py` can import them without
# importing `validate`, which would be a cycle (validate imports the check
# modules for their registration side-effect). See `validation/_registry.py`.
#
# ⚠️ `_CHECKS` is re-exported BY BINDING, and that is load-bearing: registration
# appends to it and `_apply_canonical_order()` sorts it in place, so this name and
# `validation._registry._CHECKS` must remain THE SAME list. Never rebind it
# (`_CHECKS = [...]`) — that yields two registries, one filled by registration and
# a different one iterated by `run_checks` / `--list`, and since `all([])` is True
# the suite would report success while running fewer checks.
#
# The re-export itself is required by ADR-009 D2 item 8: nine test files and
# `scripts/sync_manifest.py` import names from `validate` directly.
# `tests/test_validate_public_surface.py` freezes the full external surface and
# asserts the `_CHECKS` identity above. That file's `EXPECTED_SURFACE` is the
# AUTHORITATIVE list — do not restate its size here. (This comment read "the full
# 33-name surface" until 2026-08-04; the real surface is 54, and ADR-009 D2 item 8
# carries the same stale figure with the account of how the measurement was voided.)
from validation._registry import (  # noqa: E402
    Detail, CheckResult, CheckSpec, _CHECKS, register_check,
)


# ═══════════════════════════════════════════════════════════════════════
# Execution order (ADR-009 H3)
# ═══════════════════════════════════════════════════════════════════════
#
# Registration order is SEMANTIC, not cosmetic: `counts_fresh`, `tables_fresh` and
# `claim_clusters_fresh` shell out and REGENERATE artifacts that later checks read.
# `run_checks` iterates `_CHECKS` in order, so what a later check observes depends on
# what ran before it.
#
# ⚠️ This comment used to name TWO consumers of `docs/counts.json`, and so did the test
# that enforced the ordering. Measured 2026-08-07, the real population was larger and
# three of the undeclared readers ran BEFORE the regenerator — `lean_zero_sorry` (the
# Invariant #4 gate), `native_decide_regression` and `axiom_closure_allowlist`. Naming a
# consumer set in prose is the same hand-maintained-list failure the suite exists to
# catch, so the set is now DERIVED by AST in
# `tests/test_validate_registry_contract.py::_counts_consumers`, and `counts_fresh` runs
# first. Do not re-enumerate consumers here.
#
# Until now that order was an EMERGENT PROPERTY of where each `@register_check`
# happened to sit in one 7,800-line file. That is fine while there is one file and
# impossible to preserve once the checks are split by domain: the current order
# interleaves domains (#10 Lean, #11 physics, #13 papers, #16 Lean), so no ordering
# of domain modules reproduces it.
#
# So import order and execution order are decoupled. Modules may be organised
# however reads best; execution order is declared HERE, as data, and applied once
# after registration. A registered check absent from this list raises on sort —
# the correct loud failure for a check nobody declared a position for.
#
# NOTE `tests/test_validate_registry_contract.py` keeps its OWN frozen copy and
# must NOT import this one; otherwise it would assert only that production agrees
# with itself.
_CANONICAL_ORDER: tuple[str, ...] = (
    # `counts_fresh` FIRST — it regenerates `docs/counts.json`, and three checks that
    # read it (`lean_zero_sorry`, `native_decide_regression`, `axiom_closure_allowlist`)
    # used to run BEFORE it. On a run over a tree whose Lean sources had changed, the
    # Invariant #4 gate evaluated the PREVIOUS extraction. Moved 2026-08-07; the
    # consumer set is now DERIVED by AST in the ordering test, so a new consumer
    # registered ahead of it fails rather than silently reading stale counts.
    # Safe to run first: it depends on `lean_deps.json`, which `main()` already
    # snapshots via `ensure_lean_deps_fresh()` before any check runs.
    'counts_fresh',
    'formulas', 'lean_zero_sorry', 'placeholder_not_cited', 'disclosure_consistency',
    'proxy_body_audit', 'tracked_hypothesis_ledger', 'tracked_hypotheses_fresh',
    'formula_grounding', 'vacuous_statement_audit', 'nogo_substrate_integrity',
    'native_decide_regression', 'numerical', 'identities',
    'paper_table', 'd1_hierarchy_table', 'f_hierarchy_claims',
    'theorems', 'notebooks', 'lean_source',
    # `lean_modules_in_build_graph` precedes `lean_build` and everything that reads
    # lean_deps.json, and the position is semantic: it answers "is the population the
    # rest of this suite measures actually the whole project?". A red here means every
    # downstream count, the atlas and the axiom closure are computed over a proper
    # subset — so the reader needs it BEFORE they trust any of them.
    'cgl_fdr', 'lean_modules_in_build_graph', 'lean_build', 'axiom_closure_allowlist',
    'elaboration_knob_watchlist', 'bundle_figure_integrity', 'viz_consistency',
    'notebook_exec', 'physical_bounds', 'cross_path_consistency',
    'paper_provenance', 'parameter_provenance',
    'tables_fresh', 'claim_clusters_fresh', 'numerical_literals', 'bundle_tables_use_pipeline',
    'graph_integrity', 'gate_edge_types_are_emitted', 'atlas_integrity',
    'atlas_hypothesis_discipline',
    'count_literals', 'recurrence_reopens_closures', 'review_severity_declared',
    'review_docs_mint_findings', 'accepted_findings_carry_rationale',
    'chain_backing_targets_resolve',
    'bundle_metadata_matches_graph', 'bundle_stage13_claim_consistent',
    'bundle_manuscript_length', 'bundle_reviewer_stage_ordering',
    'bundle_prose_em_dash_free', 'bundle_reader_facing_voice',
    'bundle_sentence_length',
    'bundle_figure_adequacy', 'bundle_structural_coherence',
    'bundle_lean_module_coverage',
    'notebook_stored_outputs_current',
    'readiness_verdicts_agree', 'readiness_submission_gate',
    'citation_primary_sources_present', 'provenance_doi_in_registry',
    'bundle_consistency', 'bundle_source_freshness',
    'bibitem_title_primary_source', 'quantum_network',
    # `bundle_apex_resolves` follows the roster gate and precedes the prose checks: it
    # gates the ONE hand-maintained input to the derived substrate closure, so a reader
    # needs its verdict before any per-bundle substrate figure downstream.
    'bundle_registry_consistency', 'bundle_apex_resolves',
    # Both of these read the DECLARED-APEX CLOSURE, so they must follow
    # `bundle_apex_resolves` — it gates the one hand-maintained input the closure rests
    # on. Reporting a per-bundle compiler-trust figure derived from an apex list that
    # does not resolve would be a measurement over a population nobody validated, which
    # is the defect class this suite exists to close.
    # `bundle_todo_free_before_green` reads `stage13_status`, so it also belongs after
    # `bundle_reviewer_stage_ordering` above: a green that should never have been
    # recorded is that check's finding, and this one should not be the first to report it.
    'bundle_native_decide_debt', 'bundle_todo_free_before_green',
    # Precedes `paper_latex_compiles`: a dangling \ref is cheap to detect statically and
    # is exactly what that check cannot see (one pdflatex pass reports every reference as
    # undefined, and its per-draft cache skips untouched drafts).
    'bundle_counts_fresh', 'bundle_cross_references_resolve', 'paper_latex_compiles',
    'axiom_count_prose_consistency', 'prose_theorem_reference_coverage',
    'theorem_name_embedded_citations', 'inventory_index_autogen_fresh', 'architecture_inventory_fresh',
    'lean_docstring_refs_resolve', 'paper_toolchain_pin_drift',
)


def _apply_canonical_order() -> None:
    """Sort `_CHECKS` into `_CANONICAL_ORDER`. Idempotent; a no-op while every
    check still lives in this file in canonical sequence, which is exactly why it
    is introduced BEFORE any module moves — the mechanism is proven inert before
    anything depends on it."""
    index = {name: i for i, name in enumerate(_CANONICAL_ORDER)}
    unknown = [s.name for s in _CHECKS if s.name not in index]
    if unknown:
        raise RuntimeError(
            f"check(s) registered with no declared execution position: {unknown}. "
            f"Add them to _CANONICAL_ORDER — position is semantic (see above), so "
            f"it must be chosen, not inherited from import order.")
    _CHECKS.sort(key=lambda s: index[s.name])


# ⚠️ THE CALL IS DELIBERATELY NOT HERE. It lives at the BOTTOM of this module,
# after the last `@register_check`. Placing it here — which is where it was first
# written, on 2026-08-03 — sorted only the 45 checks registered above this point
# and left the 14 below it appended, unsorted, in import order. Two consequences,
# both invisible because the tail happened to already be in canonical sequence:
#
#   1. The mechanism was inert for 14/59 checks, i.e. exactly the ones a Phase-2
#      module move is most likely to reorder.
#   2. The `raise` above — the "loud failure for a check nobody declared a
#      position for" — could not fire for anything registered below, INCLUDING
#      the end of the file, which is where a new check naturally goes. Verified
#      by mutation: an undeclared check added at :7441 ran, listed, and exited 0.
#
# So the guard written to make ordering explicit was itself order-dependent.
# `tests/test_validate_registry_contract.py` now asserts the call's position
# structurally, because no behavioural test can see this while the tail is
# coincidentally correct.


# ═══════════════════════════════════════════════════════════════════════
# Runner
# ═══════════════════════════════════════════════════════════════════════

def run_checks(
    check_filter: Optional[str] = None,
    skip: "Optional[frozenset[str]]" = None,
) -> Dict[str, CheckResult]:
    """Run all (or one) registered checks, return results keyed by name.

    `skip` names checks NOT to execute. It must be applied HERE, before the call —
    filtering results afterwards runs every check and then deletes its answer, which
    avoids none of the cost the skip exists to avoid and silently discards a real
    failure.
    """
    results = {}
    for spec in _CHECKS:
        if check_filter and spec.name != check_filter:
            continue
        if skip and spec.name in skip:
            continue
        try:
            results[spec.name] = spec.func()
        except Exception as e:
            # ⚠️ `measured=False`, and this is the single most central place it
            # matters. An unhandled exception is the STRONGEST "could not
            # measure" the suite can produce, and `measured` defaults True — so
            # a crashed check used to count toward `--ci`'s coverage floor as
            # evidence that it ran. The verdict was never wrong (`passed=False`
            # still fails the suite); the FLOOR was, and the floor is the guard
            # that exists because the previous floor could not fire.
            results[spec.name] = CheckResult(
                passed=False, measured=False, error=str(e))
    return results


def print_results(results: Dict[str, CheckResult]) -> None:
    """Pretty-print validation results to stdout."""
    for spec in _CHECKS:
        if spec.name not in results:
            continue
        cr = results[spec.name]
        status = "\033[32m✓ PASS\033[0m" if cr.passed else "\033[31m✗ FAIL\033[0m"
        print(f"\n{'═'*70}")
        print(f"  {status}  {spec.name}: {spec.description}")
        print(f"{'═'*70}")

        if cr.error:
            print(f"  ERROR: {cr.error}")

        for d in cr.details:
            # ⚠️ FAILURE IS TESTED FIRST, and the order is the whole point.
            # `warning` and `passed` are independent axes, and the pair
            # (passed=False, warning=True) is REAL: it is what `--strict`
            # produces when it promotes an advisory to a failure
            # (`checks/freshness.py`). Testing `warning` first rendered every
            # one of those as a yellow ⚠ while `CheckResult.passed` correctly
            # went False — so the human-readable report contradicted the exit
            # code on exactly the runs that matter. `⚠✗` keeps both facts: this
            # failed, and it failed by promotion rather than on its own terms.
            if not d.passed:
                sym = "\033[33m⚠\033[0m\033[31m✗\033[0m" if d.warning else "✗"
            elif d.warning:
                sym = "\033[33m⚠\033[0m"
            else:
                sym = "✓"
            line = f"  {sym} {d.name}"
            if d.message:
                line += f"  —  {d.message}"
            print(line)

    total = len(results)
    passed = sum(1 for r in results.values() if r.passed)
    total_warnings = sum(
        1 for r in results.values() for d in r.details if d.warning
    )
    print(f"\n{'═'*70}")
    summary = f"  Overall: {passed}/{total} checks passed"
    if total_warnings:
        summary += f" ({total_warnings} warning{'s' if total_warnings > 1 else ''})"
    print(summary)
    if passed == total:
        print("  \033[32mALL CHECKS PASSED\033[0m")
    else:
        print("  \033[31mSOME CHECKS FAILED\033[0m")
        _print_failure_provenance(results)
    print(f"{'═'*70}\n")


#: Check modules whose subject is the PAPER CORPUS rather than the Lean/Python
#: substrate. Derived from the module a check is DEFINED in — deliberately not a
#: hand-listed set of check names, which would be a parallel list that drifts
#: (the defect class this suite keeps finding).
#: Which check-module belongs to which side. The CLASSIFICATION of an individual check
#: is derived (from its defining module, via the registry), but this partition is a
#: judgement and is declared. It must be TOTAL: `tests/test_ci_mode.py` asserts every
#: module owning a registered check appears in exactly one side, so a new check module
#: fails loudly rather than defaulting to "substrate" and silently gaining the power to
#: block a Lean wave.
_PAPER_SIDE_MODULES = frozenset({
    "papers_prose", "prose_lean_refs", "citations", "bundles_readiness", "reviews",
})
_SUBSTRATE_SIDE_MODULES = frozenset({
    "lean_substrate", "lean_toolchain", "lean_statements", "physics",
    "graph_atlas", "freshness", "notebooks",
})


def _check_modules() -> set:
    """Leaf module name of every module that owns a registered check."""
    return {_defining_module(sp.func) for sp in _CHECKS}


def _spec_of(name: str):
    """The registered CheckSpec for `name`, or None."""
    return next((sp for sp in _CHECKS if sp.name == name), None)


def _defining_module(func) -> str:
    """Leaf name of the module a check function is DEFINED in.

    Unwraps the memo decorator: a memoized check's `__module__` is `_memo`, the
    wrapper's home, not the check's. `_memo.memoize_check` exposes `__memo_body__`
    for exactly this.
    """
    body = getattr(func, "__memo_body__", None) or func
    return body.__module__.rsplit(".", 1)[-1]


def _leaf_module_of(name: str) -> str:
    """Leaf name of the module a check is DEFINED in — derived from the registry, so a
    check that moves module carries its classification with it."""
    sp = _spec_of(name)
    return _defining_module(sp.func) if sp is not None else ""


def _print_failure_provenance(results: Dict[str, CheckResult]) -> None:
    """Split the failures into paper-corpus vs substrate, and say so.

    WHY THIS EXISTS (2026-08-05). `gate_precheck.py s13` runs the FULL suite before
    dispatching an expensive Stage-13 reviewer, so closing a **pure-Lean wave** can
    be blocked by paper-corpus state the wave never touched. The rationale for
    running everything is sound — do not spend reviewer budget on a known-bad tree
    — but "the tree is clean" was being reported as one undifferentiated verdict.

    ⚠️ This changes NOTHING about what runs or what blocks. A `--scope` flag that
    skipped the 23 paper-side checks would be a filter that silently narrows the
    population, which is precisely the defect class this suite exists to catch. The
    fix for an unreadable verdict is to make it readable, not to shrink it.
    """
    by_name = {spec.name: spec for spec in _CHECKS}
    paper, substrate = [], []
    for name, cr in results.items():
        if cr.passed:
            continue
        spec = by_name.get(name)
        mod = getattr(spec.func, "__module__", "") if spec else ""
        leaf = mod.rsplit(".", 1)[-1]
        (paper if leaf in _PAPER_SIDE_MODULES else substrate).append(name)
    if not (paper and substrate) and not paper:
        return
    print()
    if substrate:
        print(f"  \033[31m✗ SUBSTRATE ({len(substrate)}):\033[0m "
              f"{', '.join(sorted(substrate))}")
    else:
        print("  \033[32m✓ SUBSTRATE: clean\033[0m — no Lean/Python-side failure")
    if paper:
        print(f"  \033[33m● PAPER CORPUS ({len(paper)}):\033[0m "
              f"{', '.join(sorted(paper))}")
        print("    These concern the paper corpus, not the Lean/Python substrate. A "
              "Lean-only wave\n    cannot have caused them — see "
              "docs/architecture/VALIDATION_GATE_TOPOLOGY.md §2.")


def archive_results(results: Dict[str, CheckResult]) -> Path:
    """Write timestamped JSON + text report to docs/validation/reports/."""
    _reports_dir().mkdir(parents=True, exist_ok=True)
    ts = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")

    # JSON report
    json_path = _reports_dir() / f"validation_{ts}.json"
    payload = {
        "timestamp": ts,
        "project_root": str(PROJECT_ROOT),
        "checks": {},
    }
    for name, cr in results.items():
        payload["checks"][name] = {
            "passed": cr.passed,
            # ⚠️ `measured` must cross EVERY persistence boundary. `_registry`
            # justifies the field by naming the `--json` payload and the
            # pre-commit consumers as the reason it exists; dropping it here
            # re-created, in the archived historical record, exactly the state
            # it was added to remove — a cannot-measure PASS stored
            # byte-identically to a real one.
            "measured": cr.measured,
            "error": cr.error,
            "details": [asdict(d) for d in cr.details],
        }
    payload["summary"] = {
        "total": len(results),
        "passed": sum(1 for r in results.values() if r.passed),
        "measured": sum(1 for r in results.values() if r.measured),
        "failed": sum(1 for r in results.values() if not r.passed),
    }
    class _Encoder(json.JSONEncoder):
        def default(self, o):
            if isinstance(o, (bool,)):
                return bool(o)
            try:
                return float(o)  # numpy scalars
            except (TypeError, ValueError):
                return super().default(o)

    with open(json_path, 'w') as f:
        json.dump(payload, f, indent=2, cls=_Encoder)

    # Text report (human-readable)
    txt_path = _reports_dir() / f"validation_{ts}.txt"
    lines = [
        f"SK-EFT Hawking Validation Report",
        f"Generated: {ts}",
        f"Project: {PROJECT_ROOT}",
        "",
    ]
    for name, cr in results.items():
        status = "PASS" if cr.passed else "FAIL"
        lines.append(f"[{status}] {name}")
        if cr.error:
            lines.append(f"  ERROR: {cr.error}")
        for d in cr.details:
            sym = "+" if d.passed else "-"
            line = f"  {sym} {d.name}"
            if d.message:
                line += f" — {d.message}"
            lines.append(line)
        lines.append("")

    total = len(results)
    passed = sum(1 for r in results.values() if r.passed)
    lines.append(f"Overall: {passed}/{total} passed")
    with open(txt_path, 'w') as f:
        f.write('\n'.join(lines))

    return json_path


# ═══════════════════════════════════════════════════════════════════════
# BUNDLE_CODES re-export — required by the roster gate (ADR-009 H2)
# ═══════════════════════════════════════════════════════════════════════
# ⚠️ This header read "Shared helpers for the prose-consistency checks (CHECK 24–26)"
# until 2026-08-04 (audit finding QI-26b). Those helpers moved to
# `validation/checks/papers_prose.py` and `prose_lean_refs.py` in Phase 2; what
# remains under it is the BUNDLE_CODES re-export, which is unrelated.

#: Bundle codes per docs/PAPER_STRATEGY.md, from THE roster source of truth
#: (scripts/bundle_registry.py). Re-exported under the historical name because
#: three checks below and `tests/` import it.
#:
#: This was a hand-maintained literal until 2026-07-30. It omitted D10–D12,
#: which meant `prose_theorem_reference_coverage` — the one gate that catches
#: Lean theorem-name drift in bundle prose — never scanned D10 at all between
#: its 2026-06-30 first lift and 2026-07-30. A short tuple does not error; it
#: just checks fewer bundles and reports a clean pass.
BUNDLE_CODES = _REGISTRY_BUNDLE_CODES


# ═══════════════════════════════════════════════════════════════════════
# Check modules — imported for their registration side-effect (ADR-009 Phase 2)
# ═══════════════════════════════════════════════════════════════════════
# Import order does NOT determine execution order; `_CANONICAL_ORDER` below does
# (H3). Organise `validation/checks/*` for reading, not for sequencing.
#
# The names are re-exported because nine test files and `scripts/sync_manifest.py`
# import them from `validate` directly (D2 item 8). `tests/test_validate_public_surface.py`
# freezes that surface.
from validation.checks import notebooks as _checks_notebooks  # noqa: E402
from validation.checks import physics as _checks_physics      # noqa: E402
from validation.checks import graph_atlas as _checks_graph_atlas  # noqa: E402
from validation.checks import freshness as _checks_freshness      # noqa: E402
from validation.checks import lean_toolchain as _checks_lean_toolchain  # noqa: E402
from validation.checks import lean_substrate as _checks_lean_substrate  # noqa: E402
from validation.checks import lean_statements as _checks_lean_statements  # noqa: E402
from validation.checks import papers_prose as _checks_papers_prose      # noqa: E402
from validation.checks import prose_lean_refs as _checks_prose_refs     # noqa: E402
from validation.checks import citations as _checks_citations           # noqa: E402
from validation.checks import reviews as _checks_reviews               # noqa: E402
from validation.checks import bundles_readiness as _checks_bundles     # noqa: E402

check_notebook_isolation = _checks_notebooks.check_notebook_isolation
check_viz_consistency = _checks_notebooks.check_viz_consistency
check_notebook_execution = _checks_notebooks.check_notebook_execution
notebook_exec_cache = _checks_notebooks.notebook_exec_cache
_src_core_fingerprint = _checks_notebooks._src_core_fingerprint
_notebook_code_hash = _checks_notebooks._notebook_code_hash

check_numerical_consistency = _checks_physics.check_numerical_consistency
check_formula_identities = _checks_physics.check_formula_identities
check_paper_table_consistency = _checks_physics.check_paper_table_consistency
check_d1_hierarchy_table = _checks_physics.check_d1_hierarchy_table
check_f_hierarchy_claims = _checks_physics.check_f_hierarchy_claims
check_cgl_fdr = _checks_physics.check_cgl_fdr
check_physical_bounds = _checks_physics.check_physical_bounds
check_cross_path_consistency = _checks_physics.check_cross_path_consistency
check_quantum_network = _checks_physics.check_quantum_network
_parse_latex_number = _checks_physics._parse_latex_number

check_graph_integrity = _checks_graph_atlas.check_graph_integrity
check_atlas_integrity = _checks_graph_atlas.check_atlas_integrity
check_atlas_hypothesis_discipline = _checks_graph_atlas.check_atlas_hypothesis_discipline
_hyp_module_stem = _checks_graph_atlas._hyp_module_stem

check_counts_fresh = _checks_freshness.check_counts_fresh
check_tables_fresh = _checks_freshness.check_tables_fresh
check_claim_clusters_fresh = _checks_freshness.check_claim_clusters_fresh
check_bundle_source_freshness = _checks_freshness.check_bundle_source_freshness
check_inventory_index_autogen_fresh = _checks_freshness.check_inventory_index_autogen_fresh
check_notebook_stored_outputs_current = _checks_freshness.check_notebook_stored_outputs_current
_counts_is_stale = _checks_freshness._counts_is_stale      # scripts/sync_manifest.py
_tables_is_stale = _checks_freshness._tables_is_stale      # scripts/sync_manifest.py
_claim_clusters_is_stale = _checks_freshness._claim_clusters_is_stale
COUNTS_JSON_PATH = _checks_freshness._H.COUNTS_JSON_PATH
COUNTS_TEX_PATH = _checks_freshness._H.COUNTS_TEX_PATH
claim_clusters_path = _checks_freshness.claim_clusters_path

check_native_decide_regression = _checks_lean_toolchain.check_native_decide_regression
check_theorem_count = _checks_lean_toolchain.check_theorem_count
check_lean_source = _checks_lean_toolchain.check_lean_source
check_lean_build = _checks_lean_toolchain.check_lean_build
check_axiom_closure_allowlist = _checks_lean_toolchain.check_axiom_closure_allowlist
check_elaboration_knob_watchlist = _checks_lean_toolchain.check_elaboration_knob_watchlist
check_lean_docstring_refs_resolve = _checks_lean_toolchain.check_lean_docstring_refs_resolve

check_formulas_to_theorems = _checks_lean_substrate.check_formulas_to_theorems
check_placeholder_not_cited = _checks_lean_substrate.check_placeholder_not_cited
check_disclosure_consistency = _checks_lean_substrate.check_disclosure_consistency
check_proxy_body_audit = _checks_lean_substrate.check_proxy_body_audit
check_tracked_hypothesis_ledger = _checks_lean_substrate.check_tracked_hypothesis_ledger
check_tracked_hypotheses_fresh = _checks_lean_substrate.check_tracked_hypotheses_fresh
# ── moved to checks/lean_statements.py 2026-08-04 (statement-level analysis) ──
check_formula_grounding = _checks_lean_statements.check_formula_grounding
check_vacuous_statement_audit = _checks_lean_statements.check_vacuous_statement_audit
check_nogo_substrate_integrity = _checks_lean_statements.check_nogo_substrate_integrity
# Regexes + pure cores imported directly by tests/test_substrate_integrity_gates.py
_tex_name_pattern = _checks_lean_substrate._tex_name_pattern
_VERIFY_CLAIM_RE = _checks_lean_substrate._VERIFY_CLAIM_RE
_HEDGE_CLAIM_RE = _checks_lean_substrate._HEDGE_CLAIM_RE
_OVERCLAIM_VERB_RE = _checks_lean_substrate._OVERCLAIM_VERB_RE
_LEDGER_HEDGE_RE = _checks_lean_substrate._LEDGER_HEDGE_RE
_STRUCTURAL_NAME_RE = _checks_lean_substrate._STRUCTURAL_NAME_RE
_TRIVIAL_BODY_RES = _checks_lean_substrate._TRIVIAL_BODY_RES
_NONTRIVIAL_MARKER_RE = _checks_lean_substrate._NONTRIVIAL_MARKER_RE
_TRACKED_PROP_NAME_RE = _checks_lean_substrate._TRACKED_PROP_NAME_RE
_THIN_HARD = _checks_lean_statements._THIN_HARD
_is_prop_codomain = _checks_lean_substrate._is_prop_codomain
_is_autogen_decl = _checks_lean_statements._is_autogen_decl
_thin_type_label = _checks_lean_statements._thin_type_label
_is_vacuous_identity_wrapper = _checks_lean_statements._is_vacuous_identity_wrapper
_parse_formula_lean_refs = _checks_lean_statements._parse_formula_lean_refs

check_paper_provenance = _checks_papers_prose.check_paper_provenance
check_numerical_literals = _checks_papers_prose.check_numerical_literals
check_count_literals = _checks_papers_prose.check_count_literals
check_paper_latex_compiles = _checks_papers_prose.check_paper_latex_compiles
check_axiom_count_prose_consistency = _checks_papers_prose.check_axiom_count_prose_consistency
check_paper_toolchain_pin_drift = _checks_papers_prose.check_paper_toolchain_pin_drift
_axiom_prose_findings = _checks_papers_prose._axiom_prose_findings
_tp_live_pins = _checks_papers_prose._tp_live_pins
_tp_scan_lines = _checks_papers_prose._tp_scan_lines
check_prose_theorem_reference_coverage = _checks_prose_refs.check_prose_theorem_reference_coverage
check_theorem_name_embedded_citations = _checks_prose_refs.check_theorem_name_embedded_citations
_prose_occurrence_disclaimed = _checks_prose_refs._prose_occurrence_disclaimed
_extract_prose_lean_candidates = _checks_prose_refs._extract_prose_lean_candidates
_resolve_prose_ref = _checks_prose_refs._resolve_prose_ref
_embedded_citation_pairs = _checks_prose_refs._embedded_citation_pairs
_paper_bibitems = _checks_prose_refs._paper_bibitems
_PROSE_REF_WAIVERS = _checks_prose_refs._PROSE_REF_WAIVERS
from validation._tex import _strip_tex_comments  # noqa: E402  frozen surface

check_parameter_provenance = _checks_citations.check_parameter_provenance
check_citation_primary_sources_present = _checks_citations.check_citation_primary_sources_present
check_provenance_doi_in_registry = _checks_citations.check_provenance_doi_in_registry
check_bibitem_title_primary_source = _checks_citations.check_bibitem_title_primary_source
check_recurrence_reopens_closures = _checks_reviews.check_recurrence_reopens_closures
check_review_severity_declared = _checks_reviews.check_review_severity_declared
check_review_docs_mint_findings = _checks_reviews.check_review_docs_mint_findings
check_accepted_findings_carry_rationale = _checks_reviews.check_accepted_findings_carry_rationale
check_chain_backing_targets_resolve = _checks_reviews.check_chain_backing_targets_resolve
_recurrence_norm = _checks_reviews._recurrence_norm
_RECURRENCE_MIN_TITLE = _checks_reviews._RECURRENCE_MIN_TITLE
_RECURRENCE_MIN_OVERLAP = _checks_reviews._RECURRENCE_MIN_OVERLAP
check_bundle_figure_integrity = _checks_bundles.check_bundle_figure_integrity
check_bundle_metadata_matches_graph = _checks_bundles.check_bundle_metadata_matches_graph
check_bundle_stage13_claim_consistent = _checks_bundles.check_bundle_stage13_claim_consistent
check_bundle_manuscript_length = _checks_bundles.check_bundle_manuscript_length
check_bundle_reviewer_stage_ordering = _checks_bundles.check_bundle_reviewer_stage_ordering
check_bundle_prose_em_dash_free = _checks_bundles.check_bundle_prose_em_dash_free
check_bundle_reader_facing_voice = _checks_bundles.check_bundle_reader_facing_voice
check_bundle_sentence_length = _checks_bundles.check_bundle_sentence_length
check_bundle_figure_adequacy = _checks_bundles.check_bundle_figure_adequacy
check_bundle_structural_coherence = _checks_bundles.check_bundle_structural_coherence
check_bundle_lean_module_coverage = _checks_bundles.check_bundle_lean_module_coverage
check_readiness_verdicts_agree = _checks_bundles.check_readiness_verdicts_agree
check_readiness_submission_gate = _checks_bundles.check_readiness_submission_gate
check_bundle_consistency = _checks_bundles.check_bundle_consistency
check_bundle_registry_consistency = _checks_bundles.check_bundle_registry_consistency
check_bundle_apex_resolves = _checks_bundles.check_bundle_apex_resolves
check_bundle_native_decide_debt = _checks_bundles.check_bundle_native_decide_debt
check_bundle_todo_free_before_green = _checks_bundles.check_bundle_todo_free_before_green
check_bundle_cross_references_resolve = _checks_papers_prose.check_bundle_cross_references_resolve
check_bundle_counts_fresh = _checks_freshness.check_bundle_counts_fresh
check_lean_zero_sorry = _checks_lean_substrate.check_lean_zero_sorry
check_gate_edge_types_are_emitted = _checks_graph_atlas.check_gate_edge_types_are_emitted
check_architecture_inventory_fresh = _checks_freshness.check_architecture_inventory_fresh


# ═══════════════════════════════════════════════════════════════════════
# Apply the declared execution order — AFTER every registration (ADR-009 H3)
# ═══════════════════════════════════════════════════════════════════════
# This must be the last statement following the final `@register_check`, and it
# must run at IMPORT time rather than inside `main()`: the tests, the
# characterization harness and `gate_precheck.py` all read `_CHECKS` directly
# without ever calling `main`, so a sort deferred to the CLI would leave every
# in-process consumer running an unordered registry.
#
# In Phase 2 this becomes structurally safe rather than positionally safe — the
# framework will import the check modules and then sort, so "after all
# registrations" is enforced by the import block rather than by where this line
# happens to sit. Until then, the position IS the contract, and the registry
# test asserts it.
_apply_canonical_order()


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        description="SK-EFT Hawking cross-layer validation suite",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python scripts/validate.py              # run all checks + archive result
  python scripts/validate.py --no-archive # run without saving report
  python scripts/validate.py --json       # JSON output for CI (no archive)
  python scripts/validate.py --check formulas  # run one check
  python scripts/validate.py --list       # list available checks
""",
    )
    parser.add_argument("--check", help="Run only this check (by name)")
    parser.add_argument("--json", action="store_true", help="JSON output to stdout")
    parser.add_argument("--no-archive", action="store_true",
                        help="Skip saving timestamped report (default: always archive)")
    parser.add_argument("--list", action="store_true", help="List available checks")
    parser.add_argument(
        "--strict", action="store_true",
        help=("Promote paper-submission advisory warnings to hard failures. "
              "Read by 6 checks: parameter_provenance, provenance_doi_in_registry, "
              "bibitem_title_primary_source, theorem_name_embedded_citations, "
              "axiom_closure_allowlist, bundle_source_freshness. Used at the "
              "paper-submission gate, not at Stage-1 development.")
    )
    parser.add_argument(
        "--force-notebooks", action="store_true",
        help=("Bypass the CHECK 11 notebook-exec skip-cache and re-execute every "
              "notebook (default skips unchanged, previously-vetted notebooks). "
              "Use after a kernel / dependency upgrade.")
    )
    parser.add_argument(
        "--force-latex", action="store_true",
        help=("Recompile EVERY bundle draft, bypassing paper_latex_compiles' "
              "per-draft content-hash cache. The compile itself is no longer "
              "opt-in (it used to skip by default, which is how the suite stayed "
              "green over a draft with fatal errors).")
    )
    parser.add_argument(
        "--no-memo", action="store_true",
        help=("Re-measure the expensive checks instead of reusing a cached PASS "
              "keyed on their inputs (axiom_closure_allowlist, "
              "lean_docstring_refs_resolve). Implied by --strict.")
    )
    parser.add_argument(
        "--scope", choices=("all", "substrate"), default="all",
        help=("Which failures bind the EXIT CODE. `all` (default) is unchanged: any "
              "failure fails. `substrate` fails only on Lean/Python-side checks — "
              "paper-corpus failures are still RUN and still PRINTED, they just do not "
              "block. For a pure-Lean wave close, whose Stage-13 dispatch a red in "
              "another bundle's LaTeX should not veto. Never use it at the submission "
              "gate: `--strict` is that gate and is deliberately scope-blind."))
    parser.add_argument(
        "--ci", action="store_true",
        help=("Unattended-runner mode: skip the checks whose premise does not hold on "
              "a fresh clone (the three mtime regenerators + notebook_exec), never "
              "archive, and FAIL if fewer than CI_MIN_CHECKS_RUN checks actually ran. "
              "Does NOT imply --strict: that is the submission gate (Invariant #12).")
    )
    args = parser.parse_args(argv)

    _cfg.CI_MODE = args.ci
    _cfg.STRICT_MODE = args.strict
    _cfg.FORCE_NOTEBOOK_REEXEC = args.force_notebooks
    _cfg.FORCE_LATEX = args.force_latex
    _cfg.NO_MEMO = args.no_memo

    if args.list:
        print("Available checks:")
        for spec in _CHECKS:
            print(f"  {spec.name:20s} {spec.description}")
        return 0

    # An UNKNOWN --check name must hard-error, not silently pass: run_checks filters by
    # spec.name, so an unknown filter yields an empty result set and `all([]) == True`
    # -> exit 0, silently DISABLING the gate (the commit gate / gate_precheck rely on a
    # real failure surfacing). Fail loud with rc2 (run_check in pre-commit-sync.sh maps
    # rc2 -> SKIP-printed; gate_precheck propagates it as FAIL).
    if args.check and args.check not in {spec.name for spec in _CHECKS}:
        print(f"ERROR: unknown check {args.check!r}. Run 'validate.py --list' for the registry.",
              file=sys.stderr)
        return 2

    # ── ONE lean_deps snapshot per full run (ADR-009 §Deferred item 0) ──────
    # Eight checks read `lean/lean_deps.json`; five of them run BEFORE
    # `counts_fresh` (position 29) regenerates it and three run after, so on a
    # wave close the two groups validated different extractions inside one run.
    # Refreshing once here — hash-guarded, 46 ms when nothing changed — makes the
    # whole run observe a single snapshot.
    #
    # FULL RUNS ONLY. `--check` must stay byte-identical: the commit gate runs
    # `--check native_decide_regression` and `scripts/pre-commit-sync.sh:72-74`
    # states it must NEVER trigger the heavy ExtractDeps pass. See
    # `validate_helpers.ensure_lean_deps_fresh` for the full reasoning.
    if not args.check:
        refreshed, note = _H.ensure_lean_deps_fresh()
        if refreshed or not args.json:
            print(f"  lean_deps: {note}", file=sys.stderr)

    # `--ci` skips are applied at the CALL, not to the results: see run_checks.
    _ci_skip = _cfg.CI_SKIP if (_cfg.CI_MODE and not args.check) else None
    t0 = time.monotonic()
    results = run_checks(check_filter=args.check, skip=_ci_skip)
    elapsed = time.monotonic() - t0

    # ── `--ci`: drop the checks whose premise does not hold on a runner ────────
    # Applied HERE rather than inside the checks so no check body learns about CI —
    # a check that behaves differently under CI is a check whose CI result means
    # something different from its local result, which is how a green build stops
    # being evidence. The exclusions and their reasons live in `_config.CI_SKIP`.
    ci_skipped: list = sorted(_ci_skip) if _ci_skip else []

    if args.json:
        payload = {
            "elapsed_seconds": round(elapsed, 2),
            "checks": {
                name: {
                    "passed": cr.passed,
                    "measured": cr.measured,   # see archive_results
                    "error": cr.error,
                    "details": [asdict(d) for d in cr.details],
                }
                for name, cr in results.items()
            },
            "summary": {
                "total": len(results),
                "passed": sum(1 for r in results.values() if r.passed),
                "measured": sum(1 for r in results.values() if r.measured),
            },
        }
        class _Enc(json.JSONEncoder):
            def default(self, o):
                try:
                    return float(o)
                except (TypeError, ValueError):
                    return super().default(o)
        print(json.dumps(payload, indent=2, cls=_Enc))
    else:
        print_results(results)
        print(f"  Completed in {elapsed:.1f}s")

    if not args.no_archive and not args.json and not args.check and not args.ci:
        path = archive_results(results)
        print(f"\n  Archived to: {path}")

    all_passed = all(r.passed for r in results.values())

    # ── The coverage floor. THIS is the point of `--ci`. ──────────────────────
    # Dropping the Lean toolchain from a runner makes the suite ~200 s faster and
    # stops 7 lean_deps readers plus 3 `lake` shell-outs from measuring anything —
    # while the run still reports green. That is "absence of measurement rendered
    # as success" reintroduced one layer up, which is the finding this whole audit
    # exists to close. A green tick over 48 of 59 is worse than no CI, because it
    # manufactures confidence.
    if _cfg.CI_MODE and not args.check:
        # ⚠️ COUNTS MEASUREMENTS, NOT INVOCATIONS (fixed 2026-08-05).
        #
        # This read `n_ran = len(results)`, and `run_checks` inserts an entry for
        # EVERY registered spec — including from its `except` handler. So `n_ran`
        # was identically `59 - len(CI_SKIP)` = 55 against a floor of 55, and
        # `55 < 55` is never true: the floor could not fire, on any input.
        #
        # SIX reviewers found this independently in PR-review pass 2, and one
        # identified why it was invisible: `test_ci_mode.py`'s zero-headroom test
        # asserts `CI_MIN_CHECKS_RUN == len(_CHECKS) - len(CI_SKIP)` — the very
        # definition of the quantity being compared — so the guard and its test
        # were jointly self-sealing. A green tick over 48 of 59 is worse than no
        # CI because it manufactures confidence; a floor that cannot fire is worse
        # still, because it manufactures confidence *in the guard*.
        measured = [n for n, r in results.items() if r.measured]
        unmeasured = sorted(n for n, r in results.items() if not r.measured)
        n_ran = len(measured)
        if ci_skipped:
            print(f"\n  --ci: skipped {len(ci_skipped)} check(s) whose premise does not "
                  f"hold on a fresh clone: {', '.join(sorted(ci_skipped))}", file=sys.stderr)
        if unmeasured:
            print(f"\n  --ci: {len(unmeasured)} check(s) returned WITHOUT MEASURING "
                  f"(absent artifact or toolchain): {', '.join(unmeasured)}",
                  file=sys.stderr)
        if n_ran < _cfg.CI_MIN_CHECKS_RUN:
            print(f"\n  ✗ CI COVERAGE FLOOR: {n_ran} of {len(results)} check(s) actually "
                  f"MEASURED, floor is {_cfg.CI_MIN_CHECKS_RUN}. The suite got SMALLER, "
                  f"not greener — most likely the Lean toolchain is absent, which "
                  f"silently disables the lean_deps readers. Install it on the runner, "
                  f"or lower CI_MIN_CHECKS_RUN with a stated reason.", file=sys.stderr)
            return 1

    if args.scope == "substrate" and not all_passed:
        blocking = [n for n, r in results.items()
                    if not r.passed
                    and getattr(_spec_of(n), "func", None) is not None
                    and _leaf_module_of(n) not in _PAPER_SIDE_MODULES]
        if not blocking:
            print("\n  \033[33m--scope substrate:\033[0m the only failures are paper-corpus; "
                  "exiting 0. They are REAL and still listed above — this flag changes what "
                  "BLOCKS, never what is measured or reported.", file=sys.stderr)
            return 0
    return 0 if all_passed else 1


if __name__ == "__main__":
    sys.exit(main())

