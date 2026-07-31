#!/usr/bin/env python3
"""
bundle_registry.py — THE single source of truth for the publication-bundle roster
==================================================================================

Every publication bundle in `docs/PAPER_STRATEGY.md` §6 is declared exactly
once, here. Bundle code, tier, title, target journal and scheduled sub-phase
travel together as one record.

Why this module exists
----------------------
Before 2026-07-30 the roster was hardcoded in **seven** independent places.
The D11/D12 first content-lift had to patch each by hand, and every omission
failed *differently and silently*:

  - `validate.py` `BUNDLE_CODES` omitted D10–D12, so
    `prose_theorem_reference_coverage` — the one gate that catches Lean
    theorem-name drift in bundle prose — never scanned D10 at all between
    2026-06-30 and 2026-07-30.
  - `bundle_readiness.py` omitted them, so `BUNDLE_READINESS_HEATMAP.md`
    rendered 19 of 21 bundles while *looking* complete.
  - `review_runner.py` raised `KeyError('D10')`. `list_bundles()` builds the
    whole listing in one pass, so a single unmapped code took down the
    documented Stage-13 prep-brief entry point for **every** bundle — from
    D10's first lift in June until 98660389.
  - `aristotle_usage_by_bundle.py` `ALL_BUNDLES` still stopped at D9 (found
    2026-07-30 during this consolidation, never patched): D10/D11/D12 were
    silently excluded from the register-driven AI-disclosure-variant verdict
    in `docs/DISCLOSURE_TEXT.md`, so those three bundles had no derived
    Aristotle-clause applicability at all.

Three distinct silent-wrong-answer modes and one hard crash, from one
duplicated list. Hence: one registry, every consumer imports it, and
`validate.py --check bundle_registry_consistency` fails the suite if a
consumer ever re-hardcodes the roster or drifts from PAPER_STRATEGY.md.

Adding a newly authorized bundle
--------------------------------
1. Record the authorization in `docs/PAPER_STRATEGY.md` (§2.x prose + the §6
   summary table row).
2. Add ONE `Bundle(...)` record below.
3. Run `uv run python scripts/validate.py --check bundle_registry_consistency`.

That is the whole procedure. No other module needs editing — and the check in
step 3 fails loudly if one does.

Module-specific data
--------------------
A consumer that genuinely needs its own per-bundle values keeps them, but
derives its KEY SET from the roster via `complete_map()`, so a bundle missing
from that map is an import-time error rather than a silent gap. See
`scripts/datastar_bundles.py` `_BUNDLE_TITLES` for the worked example
(dashboard-table short titles overriding the canonical long ones).
"""
from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path
from typing import Mapping, TypeVar

PROJECT_ROOT = Path(__file__).resolve().parent.parent
STRATEGY_DOC = PROJECT_ROOT / "docs" / "PAPER_STRATEGY.md"

T = TypeVar("T")


@dataclass(frozen=True)
class Bundle:
    """One publication target from `docs/PAPER_STRATEGY.md` §6."""

    code: str
    tier: int
    title: str
    target_journal: str
    subphase: str


#: The authorized roster, in canonical presentation order (tier 0 flagship,
#: then the Tier 1 deep series in numeric order, then Tier 2 / 3 / 4).
#:
#: Sub-phase scheduling per `docs/Phase7_Roadmap.md`: I1+I2 in 7a; D5+L1+L3 in
#: 7b; D3 in 7c; D2+L2 in 7d; D1+E1+E2 in 7e; D4 in 7f; F in 7g. I3 ships in
#: Phase 6o.ζ (community Mathlib4 contribution, out-of-band of the Phase 7
#: ladder). D6–D12 are post-freeze deep-paper additions scheduled against
#: their own Phase 6 sub-phases.
BUNDLES: tuple[Bundle, ...] = (
    Bundle(
        "F", 0,
        "Fluid-Based Approaches to Fundamental Physics — A Formally Verified Survey",
        "Living Rev. Relativity | Phys. Rep.", "7g",
    ),
    Bundle(
        "D1", 1,
        "Analog Hawking across three platforms",
        "PRD", "7e",
    ),
    Bundle(
        "D2", 1,
        "Anomaly constraints on SM particle content",
        "PRD | JHEP", "7d",
    ),
    Bundle(
        "D3", 1,
        "Emergent gravity through BH thermodynamics",
        "PRD", "7c",
    ),
    Bundle(
        "D4", 1,
        "Topological quantum computation foundations",
        "Comm. Math. Phys. | PRX Quantum", "7f",
    ),
    Bundle(
        "D5", 1,
        "Dark sector under substrate constraints",
        "PRD", "7b",
    ),
    Bundle(
        "D6", 1,
        "Formally Verified Fault-Tolerant Quantum Computation Substrate",
        "PRD | PRX Quantum | JHEP", "6v",
    ),
    Bundle(
        "D7", 1,
        "Classical Simulability and Quantum Advantage via Tensor Networks: "
        "A Formally Verified Demarcation",
        "PRX Quantum | PRX", "6w",
    ),
    Bundle(
        "D8", 1,
        "Kernel-Verified Universal Quantum Gate Compilation — "
        "Alphabet-Agnostic Solovay-Kitaev across Dimensions",
        "PRX Quantum | Quantum", "6xz",
    ),
    Bundle(
        "D9", 1,
        "Kernel-Verified Quantum-Network and Device-Characterization "
        "Certification Substrate",
        "PRX Quantum | Quantum", "6AA-AQ",
    ),
    Bundle(
        "D10", 1,
        "Kernel-Verified Foundations of Computational Quantum Chemistry & "
        "Open-System Dynamics",
        "PRD | PRX Quantum | J. Chem. Phys.", "6BA-BC",
    ),
    Bundle(
        "D11", 1,
        "Kernel-Verified Topological Band Theory & Metamaterial Substrate",
        "PRD | PRX Quantum | PRB", "6CA-CE+6ED",
    ),
    Bundle(
        "D12", 1,
        "Kernel-Verified Detector & Readout Metrology — From Photon "
        "Statistics to Composite Fidelity Ceilings",
        "PRX Quantum | Quantum | Phys. Rev. Applied", "6EA-EE",
    ),
    Bundle(
        "L1", 2,
        "GW170817 / vestigial-graviton",
        "PRL", "7b",
    ),
    Bundle(
        "L2", 2,
        "Three generations from modular invariance",
        "PRL", "7d",
    ),
    Bundle(
        "L3", 2,
        "BCH four laws by regime",
        "PRL", "7b",
    ),
    Bundle(
        "I1", 3,
        "Verification methodology with worked cases",
        "CPC | Phys. Rep.", "7a",
    ),
    Bundle(
        "I2", 3,
        "Verified statistical estimators + lean-tensor-categories",
        "JOSS", "7a",
    ),
    Bundle(
        "I3", 3,
        "Verified Stochastic Calculus for Mathlib4 — Stochastic Integral, "
        "Quadratic Variation, Itô's Lemma, and Large-Deviation Foundations",
        "JOSS | CPC", "6o.zeta",
    ),
    Bundle(
        "E1", 4,
        "Paris-LKB polariton letter",
        "PRL | PRR", "7e",
    ),
    Bundle(
        "E2", 4,
        "Dean-Kim-Lucas graphene letter",
        "PRL | PRR", "7e",
    ),
)

#: Bundle codes in canonical presentation order.
BUNDLE_CODES: tuple[str, ...] = tuple(b.code for b in BUNDLES)

#: Membership test for bundle-target validation.
VALID_BUNDLE_TARGETS: frozenset[str] = frozenset(BUNDLE_CODES)

BY_CODE: dict[str, Bundle] = {b.code: b for b in BUNDLES}
TIER_OF: dict[str, int] = {b.code: b.tier for b in BUNDLES}
BUNDLE_TITLES: dict[str, str] = {b.code: b.title for b in BUNDLES}
BUNDLE_TARGET_JOURNAL: dict[str, str] = {b.code: b.target_journal for b in BUNDLES}
BUNDLE_SUBPHASE: dict[str, str] = {b.code: b.subphase for b in BUNDLES}

#: An un-registered code sorts last rather than crashing a render.
UNKNOWN_TIER = 9

if len(BY_CODE) != len(BUNDLES):  # pragma: no cover — structural guard
    _dupes = sorted({b.code for b in BUNDLES if BUNDLE_CODES.count(b.code) > 1})
    raise ValueError(f"duplicate bundle codes in BUNDLES: {_dupes}")


def bundle_sort_key(code: str) -> tuple[int, str, int]:
    """Order by tier, then letter, then NUMERICALLY within the letter.

    A plain string sort puts D10 between D1 and D2 (and D11/D12 with it),
    which reads as a rendering bug. Splitting the trailing digits runs the
    deep-paper series D1..D12 in the order a reader expects.
    """
    letter = code.rstrip("0123456789")
    digits = code[len(letter):]
    return (TIER_OF.get(code, UNKNOWN_TIER), letter, int(digits) if digits else 0)


def require_registered(code: str, *, context: str = "bundle") -> str:
    """Return `code` if registered; raise `ValueError` naming the roster if not."""
    if code not in VALID_BUNDLE_TARGETS:
        raise ValueError(
            f"unknown {context} {code!r}; must be one of "
            f"{sorted(VALID_BUNDLE_TARGETS)} "
            f"(register it in scripts/bundle_registry.py)"
        )
    return code


def complete_map(
    overrides: Mapping[str, T],
    fallback: Mapping[str, T],
    *, what: str = "bundle map",
) -> dict[str, T]:
    """Build a roster-complete dict: `overrides` layered over `fallback`.

    This is the supported way to keep module-specific per-bundle data. The KEY
    SET always comes from the registry, so a bundle missing from `overrides`
    inherits the registry value instead of vanishing from the output — and an
    `overrides` key that is not a registered bundle is a loud error rather than
    dead configuration.
    """
    stray = sorted(set(overrides) - VALID_BUNDLE_TARGETS)
    if stray:
        raise ValueError(f"{what}: not registered bundles: {stray}")
    missing = sorted(set(BUNDLE_CODES) - set(overrides) - set(fallback))
    if missing:
        raise ValueError(f"{what}: no value for registered bundles: {missing}")
    return {c: overrides.get(c, fallback[c]) for c in BUNDLE_CODES}


# ────────────────────────────────────────────────────────────────────────────
# Documentary cross-check — PAPER_STRATEGY.md §6 is the human-authoritative
# roster; this registry is the machine-authoritative one. They must agree.
# ────────────────────────────────────────────────────────────────────────────

#: `| <tier> | <code> | <short title> | <target> | <len> | <ships> | <deps> |`
_STRATEGY_ROW_RE = re.compile(
    r"^\|\s*(?P<tier>\d)\s*\|\s*(?P<code>[FDLIE]\d*)\s*\|", re.MULTILINE
)


def parse_strategy_roster(text: str | None = None) -> dict[str, int]:
    """Parse `docs/PAPER_STRATEGY.md` §6 into ``{code: tier}``.

    Only code and tier are cross-checkable: the table's title column is
    abbreviated for width, and its target column collapses this registry's
    ``|``-separated journal alternatives (a literal ``|`` would break the
    markdown cell). Comparing those would produce noise, not signal.
    """
    if text is None:
        text = STRATEGY_DOC.read_text(encoding="utf-8")
    section = text.split("## 6. Summary table", 1)
    if len(section) < 2:
        raise ValueError("PAPER_STRATEGY.md: '## 6. Summary table' not found")
    body = section[1].split("\n## ", 1)[0]
    return {
        m.group("code"): int(m.group("tier"))
        for m in _STRATEGY_ROW_RE.finditer(body)
    }
