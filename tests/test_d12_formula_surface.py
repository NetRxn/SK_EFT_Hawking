"""D12's Gate-4 formula list must cover its whole region of `formulas.py`.

D12 Stage-13 round-12 finding 2.2. Gate 4 (`ComputationCorrectness`) evaluates exactly
`PAPER_DEPENDENCIES['D12']['formulas']`, and `paper:D12` carries **zero** `GROUNDED_IN`
edges — so the evaluator degenerates to a hand-written list authored by the party the gate
audits. When that list held 23 of the region's 27 public functions, Gate 4 read
`passed — 23 formulas grounding paper claims`, which is a true statement about the
curation and says nothing about the bundle.

⚠️ **Adding the five missing entries did not close it, and the finding says so**: "the
verdict is again a property of the list rather than of the bundle". A hand-written list
that happens to be complete today can go short again tomorrow, silently, and the gate
stays green either way. This test is what makes "cannot be short again" true — it is the
seam guard, not the repair.

The region is delimited exactly as the finding measured it: from `poisson_avg_error_floor`
to the end of `bloch_siegert_scale`.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT))

from src.core.provenance import PAPER_DEPENDENCIES  # noqa: E402

_FIRST = "def poisson_avg_error_floor"
_LAST = "def bloch_siegert_scale"


def _d12_region_functions() -> list[str]:
    src = (PROJECT_ROOT / "src" / "core" / "formulas.py").read_text(encoding="utf-8")
    i = src.find(_FIRST)
    assert i >= 0, f"{_FIRST!r} not found — the D12 region moved; re-derive this test"
    j = src.find(_LAST)
    assert j > i, f"{_LAST!r} not found after {_FIRST!r} — the D12 region moved"
    end = src.find("\ndef ", j + 1)
    region = src[i:end if end > 0 else len(src)]
    return [m.group(1) for m in re.finditer(r"^def ([a-z][A-Za-z0-9_]*)\(", region, re.M)]


def test_the_region_is_non_empty():
    """⚠️ Guard the seam. Every assertion below is 'the region minus the list is empty',
    which an empty region satisfies perfectly — so a rename of either delimiter would turn
    this file into a tautology that passes forever."""
    fns = _d12_region_functions()
    assert len(fns) >= 20, (
        f"only {len(fns)} public function(s) found in the D12 region; the finding measured "
        f"27, so the delimiters have drifted and this test is no longer measuring D12")


def test_every_public_function_in_the_D12_region_is_in_the_gate_4_list():
    """FIRES ON THE SEEDED DEFECT — remove any entry and this goes red.

    This is the property Gate 4 cannot check for itself.
    """
    declared = set(PAPER_DEPENDENCIES["D12"]["formulas"])
    missing = sorted(set(_d12_region_functions()) - declared)
    assert not missing, (
        f"{len(missing)} public function(s) in D12's region of formulas.py are absent from "
        f"PAPER_DEPENDENCIES['D12']['formulas']: {missing}. Gate 4 evaluates that list "
        f"exactly, so it would report a green verdict about the curation while saying "
        f"nothing about these. Add them, or make Gate 4 derive its set from the draft.")


def test_the_list_names_nothing_that_does_not_exist():
    """The converse direction. A list entry naming a deleted function makes Gate 4 audit a
    formula that is not there, which reads as coverage."""
    src = (PROJECT_ROOT / "src" / "core" / "formulas.py").read_text(encoding="utf-8")
    defined = set(re.findall(r"^def ([a-z][A-Za-z0-9_]*)\(", src, re.M))
    declared = PAPER_DEPENDENCIES["D12"]["formulas"]
    assert declared, "D12 declares no formulas — Gate 4 would pass over an empty set"
    ghosts = sorted(f for f in declared if f not in defined)
    assert not ghosts, f"D12's Gate-4 list names non-existent formulas: {ghosts}"
