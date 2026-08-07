"""Dependency-free regression guards for the Knowledge Graph tab fix (the
dangling-edge crash + hidden load error). Always run — no browser needed.
Complements the browser test tests/e2e/test_graph_tab.py.
"""
from __future__ import annotations

from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent
GRAPH_TPL = (PROJECT_ROOT / "scripts" / "templates" / "partials" / "graph_tab.html").read_text()


def test_graph_drops_dangling_edges_before_forcelink():
    # d3.forceLink throws "node not found" on the first edge referencing an absent
    # node, blanking the whole graph. initGraph must filter such edges first.
    assert "links = links.filter" in GRAPH_TPL
    assert "dangling edge" in GRAPH_TPL.lower()


def test_graph_load_error_is_made_visible():
    # The fetch .catch writes into #kg-loading, which the success path set to
    # display:none — it must restore display so the error isn't silently hidden.
    assert "el.style.display = ''" in GRAPH_TPL


# ═══════════════════════════════════════════════════════════════════════
# The dashboard is the surface a human reads before sign-off, so anything it
# reimplements from the evaluator needs an arbiter. Both guards below exist
# because `docs/architecture/END_TO_END_MAP.md` §6 found the gate roster and
# the per-paper verdict rule each implemented twice, with neither pair
# cross-checked — "the copy most likely to be believed is the one nothing
# validates."
# ═══════════════════════════════════════════════════════════════════════

def test_dashboard_gate_roster_is_the_evaluator_roster():
    """GATE_DEFS must carry exactly the gates `readiness_gates` evaluates.

    Until 2026-08-06 GATE_DEFS was a hand-written copy whose own comment called
    itself "the canonical list of the 11 readiness gates". It is now derived; this
    fails if anyone re-hardcodes it and it drifts.
    """
    import sys

    sys.path.insert(0, str(PROJECT_ROOT / "scripts"))
    from provenance_dashboard import GATE_DEFS
    from readiness_gates import GATES

    assert [(n, p) for n, p, _ in GATE_DEFS] == [(n, p) for n, p, _ in GATES]


def test_every_gate_has_a_display_abbreviation():
    """A gate added upstream must not reach the tab with a missing column header.

    The fallback is the gate's own name, so this cannot crash the tab — but a long
    name in a narrow column is a visible regression, and an abbreviation map that
    silently stops covering the roster is the drift this whole guard is about.
    """
    import sys

    sys.path.insert(0, str(PROJECT_ROOT / "scripts"))
    from provenance_dashboard import _GATE_ABBREV
    from readiness_gates import GATES

    names = {n for n, _p, _e in GATES}
    assert names - set(_GATE_ABBREV) == set(), "gate(s) with no abbreviation"
    assert set(_GATE_ABBREV) - names == set(), "abbreviation(s) for a retired gate"


def test_dashboard_and_submission_gate_classify_identically():
    """Exhaustive equivalence of the two per-paper verdict rules.

    `provenance_dashboard._classify_paper` and
    `validation.checks.bundles_readiness.classify_readiness` + `partition_readiness`
    are separate implementations of one rule. They agree today; nothing asserted it.

    The verdict depends only on WHICH (priority, state) pairs are present, so
    enumerating every non-empty subset of the 8 possible pairs is genuinely
    exhaustive — not a sample.
    """
    import itertools
    import sys

    sys.path.insert(0, str(PROJECT_ROOT / "scripts"))
    from provenance_dashboard import _classify_paper
    from validation.checks.bundles_readiness import (
        classify_readiness,
        partition_readiness,
    )

    pairs = [(p, s) for p in (1, 2)
             for s in ('passed', 'blocked', 'needs-recheck', 'open')]

    compared = 0
    for r in range(1, len(pairs) + 1):
        for combo in itertools.combinations(pairs, r):
            gates = [
                {'meta': {'paper': 'X', 'gate': f'G{i}', 'priority': p,
                          'state': s, 'notes': ''}}
                for i, (p, s) in enumerate(combo)
            ]
            green, yellow, red = partition_readiness(classify_readiness(gates))
            expected = 'RED' if red else ('YELLOW' if yellow else 'GREEN')
            actual = _classify_paper([s for _p, s in combo])
            assert actual == expected, (
                f"verdicts diverge on {combo}: dashboard={actual} gate={expected}"
            )
            compared += 1

    assert compared == 2 ** len(pairs) - 1 == 255
