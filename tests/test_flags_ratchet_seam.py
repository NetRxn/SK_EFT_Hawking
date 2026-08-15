"""THE SEAM: a finding reaches a bundle's ratchet **iff** it FLAGS that bundle.

⚠️ **This file exists because two layers resolved the same question with two different
mechanisms, and a finding present in one surface and absent from the other cannot be
reconciled by looking at either.**

On 2026-08-15 the readiness AGGREGATION was taught to honour what a review document
DECLARES about its own target (`bundle_target:`, and `paper:` through
`PAPER_DRAFT_MAPPING`). `build_graph.extract_flags_edges` was not, and went on resolving
attribution from the two INFERENCES — a literal `paper<digit>` in the text and the
filename stem against the bundle roster. Measured immediately afterwards: **531 findings
disagreed between the two layers, 11 of them open blockers**, and every one of the 531
ran the same way — counted against a bundle's ratchet, flagged onto no bundle node.
`FixPropagation` is the ONLY readiness gate that reads `FLAGS`, so each of those 11
passed it vacuously for D1, D2, D3, D4, D5, E1, F, I1, L2 while the same finding was
holding those bundles RED in the heatmap.

**What this file asserts, and why it is shaped this way.** It compares the two DECIDERS
against each other — `aggregate_by_bundle`'s own `open_finding_ids` and the live graph's
own `FLAGS` edges — and never recomputes attribution itself. A test that re-implemented
the precedence rules would agree with a wrong resolver as happily as with a right one
(the trap `feedback-assert-the-decider-not-the-proxy` names); a test that asks the two
production paths for their answers and demands equality cannot. That is why divergence
here is not merely detected but made impossible to reintroduce: the only way to satisfy
it is for both layers to call one resolver.

Companion: `tests/test_declared_attribution.py` pins WHAT the resolver decides. This file
pins that BOTH LAYERS ASK IT.
"""

import sys
from collections import defaultdict
from pathlib import Path

import pytest

PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT / "scripts"))


# ── The two production surfaces, each computed by its own module ────────────────────

@pytest.fixture(scope="module")
def aggregation():
    """`bundle code -> set of open finding ids`, from the readiness aggregation.

    This is leg 1's own input: `check_bundle_stage13_claim_consistent` sums
    `severity_mix` over exactly this population, and leg 2 counts the complement of
    `open_finding_ids` across all bundles.
    """
    from bundle_readiness import (MAPPING_DOC, parse_mapping, load_findings_by_paper,
                                  resolve_stage13_reviews, aggregate_by_bundle)
    by_bundle = aggregate_by_bundle(
        parse_mapping(MAPPING_DOC.read_text()),
        load_findings_by_paper(),
        resolve_stage13_reviews(backfill=False))
    return {b: set(d.get("open_finding_ids") or ()) for b, d in by_bundle.items()}


@pytest.fixture(scope="module")
def graph():
    from build_graph import build_graph_json
    return build_graph_json()


@pytest.fixture(scope="module")
def flags_by_bundle(graph):
    """`bundle code -> set of ids of OPEN findings that FLAGS `paper:<code>`.

    Derived from the emitted graph, not from the extractor's internals, so a change to
    how the edge is produced cannot make this side agree by construction.
    """
    from bundle_registry import VALID_BUNDLE_TARGETS
    roster = frozenset(VALID_BUNDLE_TARGETS)
    status = {n["id"]: (n.get("meta") or {}).get("status", "open")
              for n in graph["nodes"] if n.get("type") == "ReviewFinding"}
    out: dict[str, set[str]] = defaultdict(set)
    for e in graph["links"]:
        if e.get("type") != "FLAGS":
            continue
        target = e["target"]
        if not target.startswith("paper:"):
            continue
        code = target[len("paper:"):]
        if code in roster and status.get(e["source"], "open") == "open":
            out[code].add(e["source"])
    return dict(out)


# ── Non-vacuity: an empty population would satisfy every assertion below ────────────

def test_both_surfaces_are_non_empty(aggregation, flags_by_bundle):
    """⚠️ THE GUARD ON THE GUARD. Two empty dicts are equal, and an equality over
    nothing is the exact failure mode this repo has recorded repeatedly: every readiness
    check green with nothing to check. Assert the populations exist BEFORE comparing
    them, so a resolver that returns `None` for everything fails here rather than
    passing the seam."""
    assert sum(len(v) for v in aggregation.values()) > 0, (
        "the aggregation reached no finding at all — the seam comparison below would "
        "pass over an empty population")
    assert sum(len(v) for v in flags_by_bundle.values()) > 0, (
        "no open finding FLAGS any bundle node — the seam comparison below would pass "
        "over an empty population")


# ── The seam itself, both directions ────────────────────────────────────────────────

def test_every_finding_in_a_bundle_ratchet_flags_that_bundle(aggregation, flags_by_bundle):
    """→ direction. THE DEFECT THIS FILE WAS WRITTEN FOR.

    A finding the aggregation counts against bundle B's ceiling must emit a FLAGS edge
    to `paper:B`. Eleven open blockers violated this on 2026-08-15 — reached by D1, D2,
    D3, D4, D5, E1, F, I1 and L2's ratchets, invisible to those bundles' FixPropagation
    gate — because the two layers resolved attribution differently.
    """
    missing = {b: sorted(ids - flags_by_bundle.get(b, set()))
               for b, ids in aggregation.items()
               if ids - flags_by_bundle.get(b, set())}
    assert not missing, (
        "findings reach a bundle's ratchet but emit NO FLAGS edge to that bundle, so "
        "they are counted by `check_bundle_stage13_claim_consistent` and invisible to "
        "`FixPropagation` — the only readiness gate that reads FLAGS:\n"
        + "\n".join(f"  {b}: {len(v)} — {v[:5]}" for b, v in sorted(missing.items()))
        + "\nBoth layers must call `build_graph.resolve_attribution`.")


def test_every_bundle_flagged_by_a_finding_counts_it_in_its_ratchet(aggregation,
                                                                   flags_by_bundle):
    """← direction, and it is NOT the same assertion.

    An edge with no matching ratchet entry is the mirror defect: the gate blocks on a
    finding no ceiling bounds and no closure sweep will find, so the bundle can never go
    green and nothing tells anyone why. Asserting only the → direction would let a
    future extractor fan edges out to bundles the aggregation never reached and still
    pass.
    """
    extra = {b: sorted(ids - aggregation.get(b, set()))
             for b, ids in flags_by_bundle.items()
             if ids - aggregation.get(b, set())}
    assert not extra, (
        "open findings FLAG a bundle that does NOT count them in its aggregation, so "
        "`FixPropagation` blocks on findings no per-bundle ceiling bounds:\n"
        + "\n".join(f"  {b}: {len(v)} — {v[:5]}" for b, v in sorted(extra.items()))
        + "\nBoth layers must call `build_graph.resolve_attribution`.")


# ── The structural reasons the seam cannot silently reopen ──────────────────────────

def test_there_is_exactly_one_attribution_resolver():
    """⚠️ A SECOND IMPLEMENTATION BESIDE AN EXISTING ONE IS THE FAILURE THIS REPO KEEPS
    RECORDING, and it is what put the two layers out of step in the first place. Object
    identity, not name equality: a `bundle_readiness.resolve_attribution` re-authored as
    its own function would still be importable under that name and would still drift."""
    import build_graph
    import bundle_readiness
    assert bundle_readiness.resolve_attribution is build_graph.resolve_attribution, (
        "`bundle_readiness.resolve_attribution` is no longer the same object as "
        "`build_graph.resolve_attribution` — a second implementation has been "
        "reintroduced, and the two layers will disagree again the moment one is edited")


def test_both_layers_read_the_same_bundle_roster():
    """The resolver returns EITHER a mapping key OR a bundle code, and each layer decides
    which it got by testing membership in a roster. Two rosters that differ by one code
    would put that bundle's findings in the paper branch on one side and the bundle
    branch on the other — a divergence the seam tests above would report as a mystery."""
    from build_graph import _valid_bundle_codes
    from sentence_state import _VALID_BUNDLE_TARGETS
    assert frozenset(_valid_bundle_codes()) == frozenset(_VALID_BUNDLE_TARGETS)


def test_every_bundle_the_aggregation_iterates_has_a_paper_node(graph):
    """⚠️ `_emit` IS A SILENT NO-OP WHEN ITS TARGET IS ABSENT from `node_ids`, so a
    bundle with no `paper:<code>` node would fail the → direction above with no
    explanation of why. Name the real cause here instead: the bundle's directory carries
    no `paper_draft.tex`, so the graph has nothing for the edge to land on."""
    from sentence_state import _VALID_BUNDLE_TARGETS
    ids = {n["id"] for n in graph["nodes"] if n.get("type") == "Paper"}
    absent = sorted(b for b in _VALID_BUNDLE_TARGETS if f"paper:{b}" not in ids)
    assert not absent, (
        f"bundles with no Paper node: {absent}. FLAGS edges to them are dropped "
        f"silently by `_emit`, so their findings can reach a ratchet and no gate")
