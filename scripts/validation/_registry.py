"""Result types and the check registry — ADR-009 Phase 2.

WHY THIS MODULE EXISTS
----------------------
The Phase-2 split moves check bodies into `validation/checks/*.py`. Each of those
needs `register_check`, `CheckResult` and `Detail`; `validate` needs to import
them for their registration side-effect. Left in `validate`, that is a genuine
import cycle:

    validate  ──imports──▶  validation.checks.physics
        ▲                            │
        └────────imports─────────────┘   (for register_check / CheckResult)

Python happens to tolerate this *if* `validate` defines the names before it
imports the check modules — the partially-initialized module already carries
them. That is a property of statement order in a 7,900-line file, which is
precisely the kind of load-bearing coincidence this ADR exists to remove (see the
`_apply_canonical_order` placement defect for the same shape). It also breaks
outright the moment anything imports a check module *first*.

So the primitives live here, below both. `validation._registry` imports nothing
from the suite, exactly like `validation._config`.

RE-EXPORT, DO NOT COPY
----------------------
`validate` re-exports these names (ADR-009 D2 item 8). The authoritative list is
`EXPECTED_SURFACE` in `tests/test_validate_public_surface.py` — **54 names**, not
the "33" this docstring claimed until 2026-08-04 (audit QI-17). That figure came
from an AST scan that filtered on `module == "validate"` while
`tests/test_substrate_integrity_gates.py` still spelled its imports
`scripts.validate`, so the whole file and every name it reached were invisible.
Do not restate the size here; point at the frozen list. For `_CHECKS` that
re-export is safe **only because it binds the same list object**: registration
appends to it and `_apply_canonical_order()` sorts it in place, so both bindings
observe every mutation.

Rebinding it anywhere — `_CHECKS = [...]` — silently creates two registries, with
registration filling one while `run_checks` and `--list` iterate the other. That
is a checks-silently-vanish failure, and `all([])` is `True`, so it would report
success. `tests/test_validate_public_surface.py` asserts the identity
`validate._CHECKS is validation._registry._CHECKS` for that reason.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable, List, Optional


@dataclass
class Detail:
    """Single sub-check result."""
    name: str
    passed: bool
    message: str = ""
    warning: bool = False  # True = passed but with advisory warning (⚠)
    #: False = this sub-finding MEASURED NOTHING. Additive and default-True, so
    #: every existing construction keeps its meaning.
    #:
    #: ⚠️ `CheckResult.measured` alone was not enough. A check whose sub-findings
    #: each said "the Lean half did not run" still returned `measured=True`,
    #: because the wrapper built its verdict from `passed` and dropped the rest —
    #: so a bundle whose freshness could not be established was byte-identical to
    #: a fresh one at every consumer, including the `--ci` coverage floor. Three
    #: reviewers found it independently. A cannot-measure branch sets this False
    #: and the check derives its own `measured` from its details.
    #:
    #: ⚠️ THERE IS NO AUTOMATIC WRAPPER, and an earlier version of this sentence said
    #: there was. `run_checks` derives nothing; the fold is PER-CHECK and MANUAL, done
    #: by whichever checks need it.
    #:
    #: ⚠️ **DO NOT WRITE THE NUMBER HERE.** This sentence has now been falsified
    #: three times by hunks of its own commit: it said "two", was corrected to
    #: "SIX" with the six named — and a seventh, `check_bundle_manuscript_length`,
    #: was added by the same commit range that wrote the correction. A census in a
    #: comment about a population the commit is actively changing is a claim with a
    #: guaranteed short shelf life. Derive it:
    #:
    #:     grep -rn 'measured=' scripts/validation/ \
    #:       | grep -vE 'measured=(True|False)' | grep -vE ':\s*#'
    #:
    #: (POSIX ERE has no negative lookahead, so the single-`grep -E` form of this
    #: exits 2 with a syntax error instead of an answer. Verified to run: 11 sites
    #: across `freshness.py`, `graph_atlas.py`, `bundles_readiness.py`. The third
    #: `grep -v` drops comment lines so this instruction does not count itself.)
    #:
    #: Automating the fold would erase a real distinction: a check that measured its
    #: primary population and merely lacked coverage of PART of it IS measured (the
    #: uncovered-figure census in `bundle_figure_integrity`), while one whose
    #: population was UNREACHABLE is not (`bundle_source_freshness`'s dark Lean leg).
    #: Do not read this field as feeding anything on its own.
    #:
    #: ⚠️ This paragraph previously named `bundle_manuscript_length`'s stale PDFs as
    #: the second example of the UNREACHABLE case, contradicting its own preceding
    #: sentence — a stale PDF for SOME bundles is exactly "coverage of PART of the
    #: population", the case the sentence assigns to measured=True. The check's
    #: implementation followed the wrong half (`measured=not unmeasured`) and one
    #: stale PDF took the whole `--ci` coverage floor down. Partial coverage keeps
    #: `CheckResult.measured=True` and marks the SKIPPED MEMBERS `Detail(measured=
    #: False)`; only a wholly unreachable population clears the check-level flag.
    measured: bool = True


@dataclass
class CheckResult:
    """Result of one top-level check.

    NOTE `passed` is a bare `bool` with no third state. Measured 2026-08-04 across
    the 59 checks then registered (80 today): **60 cannot-measure return sites — 35 FAIL and 25 PASS**, the
    latter collapsing to **22 (check, kind) pairs**. (This docstring said "~20
    sites" — audit QI-17; the figure is now computed, not estimated.)

    ADR-009 §Deferred item 4 **DECLINED** adding an `UNEVALUATED` state: `passed`
    is D2 contract item 5, read by the `--json` payload, `gate_precheck.py` and
    `pre-commit-sync.sh`, so a third state is a contract break rather than a local
    refactor. The population is instead FROZEN by
    `tests/test_cannot_measure_baseline.py`, which fails in both directions.
    """
    passed: bool
    details: List[Detail] = field(default_factory=list)
    error: Optional[str] = None

    #: False when the check RETURNED WITHOUT MEASURING — a missing artifact, an
    #: absent toolchain, an unparseable input. Added 2026-08-05 after PR-review
    #: pass 2, where **six reviewers** independently found the same root cause:
    #: nothing could distinguish "measured and passed" from "could not measure, so
    #: said PASS". Two guards were built on `len(results)` and on `passed`, and
    #: both were therefore blind:
    #:
    #:   * `--ci`'s coverage floor counted checks *invoked* — `run_checks` inserts
    #:     an entry for every spec including on exception — so `n_ran` was
    #:     identically 55 against a floor of 55 and could never fire;
    #:   * `_memo` cached a `SKIPPED — lake not found` PASS under a key
    #:     byte-identical to the real measurement's, and replayed it after the
    #:     toolchain came back (trigger: the repo's own `rm -rf .lake/build` step).
    #:
    #: ⚠️ THIS IS A SEPARATE FIELD, NOT A THIRD VALUE OF `passed`, and that is
    #: deliberate. ADR-009 §Deferred item 4 declined an `UNEVALUATED` *passed*
    #: state because `passed` is D2 contract item 5, read by the `--json` payload,
    #: `gate_precheck.py` and `pre-commit-sync.sh`; a third value would break them.
    #: An additive field with a True default leaves every existing reader correct.
    #:
    #: Setting it False does NOT change `passed`. A cannot-measure branch that
    #: returns PASS keeps returning PASS — it just stops counting as evidence.
    measured: bool = True


@dataclass
class CheckSpec:
    """Registered check metadata."""
    name: str
    description: str
    func: Callable[[], CheckResult]


#: THE registry. Mutated in place only — see the module docstring.
_CHECKS: List[CheckSpec] = []


def register_check(name: str, description: str):
    """Decorator to register a validation check.

    Registration is the suite's ONLY import-time side effect (ADR-009 D2 item 7).
    Note that it does not determine when the check RUNS: execution order is
    declared separately by `validate._CANONICAL_ORDER` and applied after every
    module has been imported (H3).
    """
    def decorator(func: Callable[[], CheckResult]) -> Callable[[], CheckResult]:
        _CHECKS.append(CheckSpec(name=name, description=description, func=func))
        return func
    return decorator
