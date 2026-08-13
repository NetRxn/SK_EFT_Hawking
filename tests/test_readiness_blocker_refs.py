"""A gate can name what blocks it — ADR-012 D15 S1.

WHY THIS FILE EXISTS
--------------------
`GateResult.blockers` is prose and always has been: a 60-character slice of a finding's
label. The finding **id** existed only inside `_eval_fix_propagation`, which held the whole
`ReviewFinding` dict — id, severity, lane, target, status — and kept the label slice. One
lossy line, and every `FLAGS` edge in the graph became invisible to the operator: a blocked
gate cell had nothing to drill through *to*.

That is why S1 is an **evaluator** change and not a render fix. Nothing downstream could
recover what was discarded upstream, so no amount of dashboard work could have produced the
drill-through. ADR-012 D15's own table was corrected on this point after a read of the code.

THE CAP IS THE SECOND HALF, AND IT IS EASY TO GET WRONG
-------------------------------------------------------
The evaluator truncated to ten *before* assigning, so `len(result.blockers)` was already the
truncated length. A `blockers_total` computed from it would have reported 10 for a paper
carrying 44 — a disclosure that lies is worse than a silent cap, because it reads as
diligence. **A cap can only be disclosed by a layer that can still see what it cut**, so the
evaluator now assigns everything, `to_node_payload` bounds the payload and states both
figures, and the dashboard bounds the display and says so.

D12 carries 44 open blocking findings. The old cap was hiding 34 of them.
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

import readiness_gates as rg  # noqa: E402


# ── The dataclass contract ────────────────────────────────────────────────────────────

def test_a_gate_result_can_carry_the_identity_of_what_blocks_it():
    r = rg.GateResult(gate="FixPropagation", paper="D1", priority=2)
    r.blocker_refs = [{"id": "review:d:X:1", "label": "x", "severity": "major",
                       "lane": "prose", "status": "open", "target": "papers/D1"}]
    payload = r.to_node_payload()
    assert payload["meta"]["blocker_refs"][0]["id"] == "review:d:X:1"


def test_blockers_stays_prose_so_the_other_evaluators_need_no_change():
    """ADDITIVE is the whole design. Ten other evaluators build a prose `blockers` list and
    know nothing about findings; replacing the field would have broken every one of them."""
    r = rg.GateResult(gate="CitationIntegrity", paper="D1", priority=1)
    r.blockers = ["some prose reason"]
    payload = r.to_node_payload()
    assert payload["meta"]["blockers"] == ["some prose reason"]
    assert payload["meta"]["blocker_refs"] == []


@pytest.mark.parametrize("n,expect_trunc", [(3, False), (50, False), (60, True)])
def test_the_payload_states_the_total_and_whether_it_truncated(n, expect_trunc):
    r = rg.GateResult(gate="FixPropagation", paper="D1", priority=2)
    r.blocker_refs = [{"id": f"review:d:X:{i}", "label": str(i), "severity": "major",
                       "lane": "prose", "status": "open", "target": ""}
                      for i in range(n)]
    r.blockers = [x["label"] for x in r.blocker_refs]
    m = r.to_node_payload()["meta"]
    assert m["blocker_refs_total"] == n
    assert m["blockers_total"] == n
    assert m["blocker_refs_truncated"] is expect_trunc
    assert len(m["blocker_refs"]) == min(n, 50)


def test_evidence_discloses_its_cap_too():
    """`evidence[:50]` was the other silent truncation in this method."""
    r = rg.GateResult(gate="FixPropagation", paper="D1", priority=2)
    r.evidence = [f"e{i}" for i in range(60)]
    m = r.to_node_payload()["meta"]
    assert m["evidence_total"] == 60 and m["evidence_truncated"] is True


# ── Against the LIVE corpus (production-seeded, CHECK_AUTHORING_GUIDE §2.4) ────────────

@pytest.fixture(scope="module")
def live_gates():
    from build_graph import build_graph_json
    return rg.evaluate_all_gates(build_graph_json())


def test_fix_propagation_keeps_the_finding_id_it_already_has(live_gates):
    blocked = [g for g in live_gates
               if g.gate == "FixPropagation" and g.state == "blocked"]
    assert blocked, ("no blocked FixPropagation gate in the live corpus — this assertion "
                     "would pass vacuously, so it is a failure, not a skip")
    for g in blocked:
        assert g.blocker_refs, f"{g.paper}: blocked on findings but named none of them"
        assert len(g.blocker_refs) == len(g.blockers)
        bad = [r["id"] for r in g.blocker_refs if not r["id"].startswith("review:")]
        assert not bad, f"{g.paper}: blocker refs that are not review findings: {bad[:3]}"


def test_the_refs_carry_the_routing_fields_the_operator_needs(live_gates):
    """id alone is a link; lane and target are what make the cell a ROUTING instrument
    rather than a status light — ADR-012's distinction between the two."""
    refs = [r for g in live_gates for r in g.blocker_refs]
    assert refs, "no blocker refs anywhere in the live corpus"
    for key in ("id", "label", "severity", "lane", "status", "target"):
        assert all(key in r for r in refs), f"a ref is missing `{key}`"
    lanes = {r["lane"] for r in refs}
    assert lanes - {"unclassified"}, (
        "every live blocker ref reads `unclassified` — the lane is not reaching the gate, "
        "so the drill-through cannot route anything")


def test_an_absent_lane_reads_unclassified_and_never_a_default(live_gates):
    """`lane` is forward-only. An unrouted finding must not be mistaken for a routed one,
    so absence maps to `unclassified` — never to a plausible-looking lane."""
    refs = [r for g in live_gates for r in g.blocker_refs]
    assert all(r["lane"] for r in refs), "a ref carries an empty lane rather than a value"


@pytest.mark.parametrize("state", ["blocked", "needs-recheck"])
def test_the_evaluator_no_longer_truncates_before_it_counts(live_gates, state):
    """⚠️ THE REGRESSION THIS FILE EXISTS FOR — AND THE FIRST VERSION COULD NOT CATCH IT.

    `_eval_fix_propagation` assigns blockers at TWO sites, one per branch. The original test
    took `max` over all `FixPropagation` gates without filtering on state, so reinstating
    `blocking[:10]` on the `blocked` branch dropped D12 from 44 to 10 while D4's
    `needs-recheck` 31 kept the maximum above the threshold — **the whole file stayed green
    over the exact defect it names.** Confirmed by mutation. Both sites changed, so both must
    be pinned, which is what parametrizing on `state` does.

    The bound is COMPUTED, not a magic number: it is the count of open findings the graph
    actually attaches to that paper. A literal `> 10` would go red the day ADR-012 P10 drives
    the population below eleven, and its message would say "the evaluator is truncating"
    when the truth was that remediation worked.
    """
    gates = [g for g in live_gates if g.gate == "FixPropagation" and g.state == state]
    assert gates, (
        f"no FixPropagation gate in state {state!r} — this branch of the evaluator is "
        f"unexercised, so the assertion would pass over nothing")
    worst = max(gates, key=lambda g: len(g.blocker_refs))
    payload = worst.to_node_payload()["meta"]
    assert payload["blocker_refs_total"] == len(worst.blocker_refs)
    assert payload["blockers_total"] == len(worst.blockers)
    # Ground truth from the graph: however many findings reach this paper, the evaluator
    # must have kept all of them.
    n_expected = _open_findings_for_paper(worst.paper, blocking=(state == "blocked"))
    assert len(worst.blocker_refs) == n_expected, (
        f"{worst.paper} reports {len(worst.blocker_refs)} of {n_expected} findings the "
        f"graph attaches to it — the evaluator is truncating before it counts, so every "
        f"total downstream is the truncated number wearing the name of a disclosure")


def _open_findings_for_paper(paper: str, blocking: bool) -> int:
    """How many open findings the graph FLAGS onto this paper — derived independently of
    the evaluator, so the two cannot agree with each other by construction."""
    from build_graph import build_graph_json
    import readiness_gates as _rg
    g = build_graph_json()
    by_id = {n["id"]: n for n in g["nodes"]}
    n = 0
    for e in g["links"]:
        if e.get("type") != "FLAGS" or e["target"] != f"paper:{paper}":
            continue
        m = (by_id.get(e["source"]) or {}).get("meta") or {}
        if m.get("status", "open") not in ("open",):
            continue
        sev = str(m.get("severity", "")).lower()
        if blocking == (sev in _rg.BLOCKING_SEVERITIES):
            n += 1
    return n
