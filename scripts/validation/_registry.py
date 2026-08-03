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
`validate` re-exports these names (ADR-009 D2 item 8 — 33 names are imported from
`validate` by nine test files and one production script). For `_CHECKS` that
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


@dataclass
class CheckResult:
    """Result of one top-level check.

    NOTE `passed` is a bare `bool` with no third state, so ~20 sites across the
    suite encode "could not measure" as PASS. That is a known defect with its own
    review item (ADR-009 §Deferred item 4, `UNEVALUATED`); it is deliberately NOT
    changed by the mechanical move.
    """
    passed: bool
    details: List[Detail] = field(default_factory=list)
    error: Optional[str] = None


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
