"""Every ratcheted check sits at ZERO HEADROOM — PR-review pass 2, R3.

WHY THIS FILE EXISTS
--------------------
The house idiom is a frozen ceiling that may only shrink: `COUNT_LITERAL_CEILING`,
`NATIVE_DECIDE_DECL_CLOSURE_CEILING`, `ARISTOTLE_REGISTRY_UNRESOLVED_CEILING`, and
their siblings. The idiom only works at **zero headroom** — a ceiling above the
live population is a ratchet that cannot fire, and reports green while the thing
it guards drifts underneath it.

Reviewer R3 measured all ten ceilings as correct **today**, and found that **not
one of them had a test asserting it**. So the values were right by hand and free
to drift by accident: lower the population and the ceiling silently gains slack,
which is exactly how `test_cannot_measure_baseline`'s seam guard came to sit at
`>= 30` against a live 54 (**44 % headroom**, tightened in the same pass).

WHAT THIS ASSERTS, AND WHAT IT DELIBERATELY DOES NOT
-----------------------------------------------------
It runs each ratcheted check against the **live tree** and asserts the population
it reports equals the ceiling it reports. It does NOT re-implement any check's
counting logic — a test that recomputed the population would assert only that two
copies of the same arithmetic agree, which is the "test agrees with itself" shape
this audit keeps finding.

⚠️ **Checks whose summary does not state a ceiling are REPORTED, not skipped
silently.** A guard that quietly narrows its own population is the defect class
this suite exists to catch; `test_the_covered_set_is_declared` fails if coverage
drops below the frozen roster.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

import pytest

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT / "scripts"))
sys.path.insert(0, str(SK_ROOT))

import validate  # noqa: E402

#: Checks whose summary Detail states "<N> ... (ceiling <M>)" or "<N> <= ceiling <M>".
#: FROZEN. Removing one is a decision — it means a ratchet lost its zero-headroom
#: guard, which is how slack creeps back in.
RATCHETED_CHECKS = (
    "native_decide_regression",
    "count_literals",
    "numerical_literals",
    "theorems",
    "elaboration_knob_watchlist",
    "bundle_tables_use_pipeline",
)

_CEIL_RE = re.compile(r"ceiling\s+(\d+)", re.IGNORECASE)
_LEAD_RE = re.compile(r"(\d+)")


def _population_and_ceiling(check: str):
    """(population, ceiling) as the check itself reports them, or None."""
    fn = next(s.func for s in validate._CHECKS if s.name == check)
    result = fn()
    for d in result.details:
        msg = d.message or ""
        m_ceil = _CEIL_RE.search(msg)
        if not m_ceil:
            continue
        m_pop = _LEAD_RE.search(msg)
        if not m_pop:
            continue
        return int(m_pop.group(1)), int(m_ceil.group(1))
    return None


class TestRatchetsHaveZeroHeadroom:

    @pytest.mark.parametrize("check", RATCHETED_CHECKS)
    def test_population_equals_ceiling(self, check):
        """FIRES ON A SEEDED DEFECT: raise any ceiling above its live population and
        this fails — before the ratchet silently stops guarding."""
        got = _population_and_ceiling(check)
        assert got is not None, (
            f"{check} no longer reports a '(ceiling N)' in any Detail, so its "
            f"headroom cannot be measured. Restore the phrasing or remove it from "
            f"RATCHETED_CHECKS deliberately — do not let it fall out silently.")
        population, ceiling = got
        assert population == ceiling, (
            f"{check}: live population {population} against ceiling {ceiling} — "
            f"{abs(ceiling - population)} of headroom. "
            + ("LOWER the ceiling in the same commit (the population shrank, which is "
               "good news the ratchet must record)." if population < ceiling else
               "The population GREW past its ceiling; fix the underlying debt rather "
               "than raising the number."))

    def test_the_covered_set_is_declared(self):
        """Guard the seam. If a ratcheted check drops out of RATCHETED_CHECKS the
        parametrization above silently shrinks and every remaining case still
        passes — the exact narrowing this suite exists to catch."""
        assert len(RATCHETED_CHECKS) >= 6, (
            f"only {len(RATCHETED_CHECKS)} ratcheted checks are covered; the roster "
            f"shrank. Removing one means a ratchet lost its zero-headroom guard.")
        registered = {s.name for s in validate._CHECKS}
        missing = [c for c in RATCHETED_CHECKS if c not in registered]
        assert not missing, f"RATCHETED_CHECKS names unregistered check(s): {missing}"
