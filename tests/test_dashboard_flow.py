"""The Flow board (ADR-012 D15, S2) — and the five things it must never do.

WHAT THESE TESTS ARE FOR
------------------------
Every assertion here corresponds to a way this board could lie while looking correct, and
each one was written so that it FAILS when the corresponding line of `dashboard_flow.py`
is mutated. The mutations were run — see `MUTATION EVIDENCE` at the bottom of this file
for the seeded defect, the observed failure and the restoration.

The board's data is expensive (two graph builds), so almost everything here drives a
synthetic roster through the injection points. Two live tests are marked `slow`: the
board must also be true of the actual tree, and a purely synthetic suite would pass over a
roster that no longer resolves.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

import dashboard_flow as df  # noqa: E402


# ── Synthetic fixtures ────────────────────────────────────────────────────────────────

def _finding(fid, *, bundle=None, paper=None, lane="prose", status="open"):
    meta = {"status": status, "lane": lane, "severity": "major"}
    if bundle:
        meta["inferred_bundle"] = bundle
    if paper:
        meta["inferred_paper"] = paper
    return {"id": fid, "label": f"label {fid}", "meta": meta}


def _gate(paper, gate, state, priority=1):
    return {"id": f"gate:{paper}:{gate}", "type": "ReadinessGate",
            "meta": {"paper": paper, "gate": gate, "state": state,
                     "priority": priority, "notes": ""}}


@pytest.fixture
def board_env(tmp_path, monkeypatch):
    """A one-bundle roster over a temp `papers/` tree, fully under the test's control."""
    papers = tmp_path / "papers"
    (papers / "X1").mkdir(parents=True)
    monkeypatch.setattr(df, "PAPERS_DIR", papers)
    monkeypatch.setattr(df, "BUNDLE_CODES", ("X1",))

    def build(metadata=None, *, findings=None, aggregate=None, gates=None,
              freshness=None, tex=True, pdf=True, claims=False):
        d = papers / "X1"
        if metadata is not None:
            (d / "bundle_metadata.json").write_text(json.dumps(metadata))
        if tex:
            (d / "paper_draft.tex").write_text("draft")
        if pdf:
            (d / "paper_draft.pdf").write_bytes(b"%PDF")
        if claims:
            (d / "claims_review.json").write_text("{}")
        fs = findings if findings is not None else [_finding("f1", bundle="X1")]
        agg = aggregate if aggregate is not None else {
            "X1": {"open_finding_ids": [f["id"] for f in fs
                                        if f["meta"]["status"] == "open"],
                   "readiness": "RED", "readiness_display": "RED"}}
        return df.flow_board(
            by_bundle=agg, finding_nodes=fs,
            gate_nodes=gates if gates is not None else [_gate("X1", "G1", "passed")],
            freshness_findings=freshness if freshness is not None else [
                {"bundle": "X1", "passed": True, "warning": False,
                 "message": "fresh", "measured": True}])

    return build


def _row(board):
    assert len(board["rows"]) == 1
    return board["rows"][0]


# ── 1. The roster is the registry, never a list ───────────────────────────────────────

@pytest.mark.slow
def test_rows_are_exactly_the_registry_roster():
    """`bundle_registry_consistency` Leg C exists because a literal roster is known-bad.

    Leg C's AST walk catches a literal in `scripts/`; this catches the subtler version —
    a roster derived from something *else* (a papers/ glob, a mapping doc) that happens to
    agree today and silently diverges when a bundle is authorized before its directory is
    created.
    """
    from bundle_registry import BUNDLE_CODES
    board = df.flow_board()
    assert [r["bundle"] for r in board["rows"]] == sorted(
        BUNDLE_CODES, key=df.bundle_sort_key)
    assert len(board["rows"]) == len(BUNDLE_CODES)


def test_module_declares_no_bundle_code_literal():
    """No roster literal in this module, checked the way Leg C checks it.

    Duplicated deliberately at test scope: Leg C runs in `validate.py`, which is not what
    a developer editing this file runs.
    """
    import ast
    from bundle_registry import BUNDLE_CODES
    tree = ast.parse((ROOT / "scripts" / "dashboard_flow.py").read_text())
    for node in ast.walk(tree):
        elts = (node.keys if isinstance(node, ast.Dict) else
                node.elts if isinstance(node, (ast.List, ast.Tuple, ast.Set)) else None)
        if not elts:
            continue
        hits = {e.value for e in elts
                if isinstance(e, ast.Constant) and e.value in set(BUNDLE_CODES)}
        assert len(hits) < 3, f"roster literal at line {node.lineno}: {sorted(hits)}"


# ── 2. §7.5 has no field and must never render as a verdict ───────────────────────────

def test_read_through_is_not_tracked_and_never_a_verdict(board_env):
    cell = _row(board_env({"stage9_status": "green"}))["cells"]["read_through"]
    assert cell["kind"] == "not-tracked"
    assert cell["kind"] not in {"green", "red", "pending"}
    assert "prose-reviewer" in cell["detail"]


def test_read_through_ignores_every_other_stage_field(board_env):
    """The failure mode is wiring §7.5 to an adjacent signal. Nothing may move it."""
    a = _row(board_env({"stage9_status": "green", "stage10_status": "green",
                        "stage13_status": "green",
                        "stage13_review_kind": "full-adversarial"},
                       claims=True))["cells"]["read_through"]
    b = _row(board_env({"stage9_status": "red"}))["cells"]["read_through"]
    assert a == b


def test_read_through_column_is_present_in_the_column_set():
    """Dropping the column is the other way to hide the gap — silently."""
    assert "read_through" in {c.key for c in df.COLUMNS}


# ── 3. The status enum has drifted and the board must not hide it ─────────────────────

@pytest.mark.parametrize("raw", ["pending-redo", "skeleton", "not_started"])
def test_undeclared_status_renders_verbatim(board_env, raw):
    cell = _row(board_env({"stage9_status": raw}))["cells"]["stage9_figure"]
    assert cell["value"] == raw, "an undeclared value must render as ITSELF"
    assert cell["kind"] == "undeclared"


def test_a_value_nobody_has_ever_seen_still_renders_verbatim(board_env):
    """The guard must be 'not in the declared enum', not 'in a known-drift list'.

    A drift list would render tomorrow's new value as the nearest known state — the exact
    coercion this test exists to forbid, relocated one edit later.
    """
    cell = _row(board_env({"stage9_status": "quarantined"}))["cells"]["stage9_figure"]
    assert (cell["value"], cell["kind"]) == ("quarantined", "undeclared")


def test_undeclared_status_is_not_coerced_to_pending(board_env):
    cell = _row(board_env({"stage9_status": "not_started"}))["cells"]["stage9_figure"]
    assert cell["kind"] != "pending" and cell["value"] != "pending"


def test_status_census_reports_the_undeclared_values(board_env):
    census = board_env({"stage9_status": "skeleton", "stage10_status": "pending",
                        "stage13_status": "red"})["status_census"]
    assert census["undeclared_by_roadmap"] == ["skeleton"]
    assert census["per_field"]["stage9_status"] == {"skeleton": 1}


def test_absent_status_field_is_absent_not_pending(board_env):
    cell = _row(board_env({}))["cells"]["stage9_figure"]
    assert cell["kind"] == "absent"


# ── 4. Only `full-adversarial` earns green at S13 ─────────────────────────────────────

def test_s13_green_requires_full_adversarial(board_env):
    cell = _row(board_env({"stage13_status": "green",
                           "stage13_review_kind": "full-adversarial",
                           "stage13_redo_required": False}))["cells"]["stage13_adversarial"]
    assert cell["kind"] == "green"


@pytest.mark.parametrize("kind", ["targeted-attribution", "partial", None, ""])
def test_s13_green_withheld_for_any_other_kind(board_env, kind):
    cell = _row(board_env({"stage13_status": "green", "stage13_review_kind": kind,
                           "stage13_redo_required": False}))["cells"]["stage13_adversarial"]
    assert cell["kind"] == "unmeasured", "a non-full-adversarial review cannot earn green"
    assert cell["value"] == "green", "the raw value is still reported, not rewritten"
    assert "full-adversarial" in cell["green_withheld"]


def test_s13_redo_required_withholds_green(board_env):
    cell = _row(board_env({"stage13_status": "green",
                           "stage13_review_kind": "full-adversarial",
                           "stage13_redo_required": True}))["cells"]["stage13_adversarial"]
    assert cell["kind"] == "unmeasured"
    assert "redo" in cell["green_withheld"]


# ── 5. Absence is a state ─────────────────────────────────────────────────────────────

def test_missing_claims_review_is_its_own_state(board_env):
    cell = _row(board_env({"stage10_status": "pending"}, claims=False))["cells"]["stage10_claims"]
    assert cell["claims_review"] == "absent"
    assert cell["kind"] not in {"green", "red"}, "absence is neither a pass nor a failure"


def test_stage10_green_withheld_without_the_artifact(board_env):
    cell = _row(board_env({"stage10_status": "green"}, claims=False))["cells"]["stage10_claims"]
    assert cell["kind"] == "unmeasured"
    assert cell["value"] == "green"


def test_stage10_green_stands_with_the_artifact(board_env):
    cell = _row(board_env({"stage10_status": "green"}, claims=True))["cells"]["stage10_claims"]
    assert cell["kind"] == "green"


def test_missing_draft_is_absent_not_red(board_env):
    cell = _row(board_env({}, tex=False, pdf=False))["cells"]["draft_exists"]
    assert cell["kind"] == "absent"
    assert _row(board_env({}, tex=True, pdf=False))["cells"]["draft_exists"]["kind"] == "warning"


def test_freshness_with_no_findings_is_absent_not_green(board_env):
    """A bundle the freshness check SKIPPED is not a bundle it cleared."""
    cell = _row(board_env({}, freshness=[]))["cells"]["stage12_sync"]
    assert cell["kind"] == "absent"


def test_freshness_unmeasured_leg_never_reads_green(board_env):
    cell = _row(board_env({}, freshness=[
        {"bundle": "X1", "passed": True, "warning": False,
         "message": "git history unavailable", "measured": False}]))["cells"]["stage12_sync"]
    assert cell["kind"] == "unmeasured"


# ── The overlay — the point of the board ──────────────────────────────────────────────

def test_overlay_breaks_findings_down_by_lane(board_env):
    findings = ([_finding(f"s{i}", bundle="X1", lane="substrate") for i in range(6)]
                + [_finding("p1", bundle="X1", lane="prose"),
                   _finding("u1", bundle="X1", lane="unclassified")])
    row = _row(board_env({}, findings=findings))
    assert row["overlay"]["by_lane"] == {"substrate": 6, "prose": 1, "unclassified": 1}
    assert row["overlay"]["open_total"] == 8


def test_overlay_has_no_silent_cap(board_env):
    """No cap anywhere. A capped overlay understates the bottleneck it exists to name."""
    findings = [_finding(f"f{i}", bundle="X1", lane="infra") for i in range(500)]
    row = _row(board_env({}, findings=findings))
    assert row["overlay"]["by_lane"] == {"infra": 500}
    assert len(row["overlay_ids"]) == 500


def test_overlay_id_with_no_known_lane_is_reported_not_defaulted():
    """An id the lane index never saw is a measurement gap, not a lane."""
    ov = df.lane_overlay(["known", "ghost"], {"known": "lean"})
    assert ov["by_lane"] == {"lean": 1}
    assert ov["unresolved_ids"] == ["ghost"]
    assert ov["open_total"] == 2


def test_overlay_for_an_unreached_bundle_is_unmeasured_not_zero(board_env):
    row = _row(board_env({}, aggregate={}))
    assert row["overlay"]["measured"] is False
    assert "UNMEASURED" in row["overlay"]["note"]


def test_closed_findings_do_not_enter_the_overlay(board_env):
    findings = [_finding("open1", bundle="X1"),
                _finding("closed1", bundle="X1", status="closed")]
    row = _row(board_env({}, findings=findings))
    assert row["overlay"]["open_total"] == 1


# ── Submission ────────────────────────────────────────────────────────────────────────

def test_submission_all_p1_passed_is_green(board_env):
    cell = _row(board_env({}, gates=[_gate("X1", "G1", "passed"),
                                     _gate("X1", "G2", "passed", 2)]))["cells"]["submission"]
    assert cell["kind"] == "green"


def test_submission_blocked_p1_is_red(board_env):
    cell = _row(board_env({"blockers_open": 6},
                          gates=[_gate("X1", "G1", "blocked")]))["cells"]["submission"]
    assert cell["kind"] == "red"
    assert cell["blocked_gates"] == ["G1"]
    assert cell["blockers_open"] == 6


def test_submission_with_no_gate_nodes_at_all_is_unmeasured_never_green(board_env):
    """The exact defect `readiness_submission_gate` shipped with: zero gates read as pass."""
    cell = _row(board_env({}, gates=[]))["cells"]["submission"]
    assert cell["kind"] == "unmeasured"
    assert "vacuous" in cell["detail"]


def test_submission_for_a_bundle_the_gates_never_name_is_unmeasured(board_env):
    """A DIFFERENT no-verdict state from 'no gates exist', and it needs its own branch.

    Collapsing the two is how the surviving-mutation dead branch got there in the first
    place: one of them was unreachable, so `green` could be substituted into it with the
    whole suite still passing.
    """
    cell = _row(board_env({}, gates=[_gate("SOMETHING_ELSE", "G1", "passed")]))[
        "cells"]["submission"]
    assert cell["kind"] == "unmeasured"
    assert "none of them names this bundle" in cell["detail"]


# ── Coverage: what the board cannot see ───────────────────────────────────────────────

def test_coverage_partitions_the_open_population(board_env):
    findings = [_finding("a", bundle="X1"),
                _finding("b", paper="paper_not_in_any_bundle"),
                _finding("c"),
                _finding("d", bundle="X1", status="closed")]
    # The aggregation reaches only `a`: `b`'s key maps to no bundle and `c` has no key at
    # all, so `aggregate_by_bundle` drops both before any row can see them.
    cov = board_env({}, findings=findings,
                    aggregate={"X1": {"open_finding_ids": ["a"]}})["coverage"]
    assert cov["open_findings"] == 3
    assert cov["attributed_to_a_row"] == 1
    assert cov["keyed_to_something_off_the_roster"] == 1
    assert cov["carry_no_bundle_or_paper_key"] == 1
    assert (cov["attributed_to_a_row"] + cov["keyed_to_something_off_the_roster"]
            + cov["carry_no_bundle_or_paper_key"] == cov["open_findings"])


def test_coverage_counts_the_unclassified_lane(board_env):
    findings = [_finding("a", bundle="X1", lane="unclassified"),
                _finding("b", bundle="X1", lane="lean")]
    cov = board_env({}, findings=findings)["coverage"]
    assert cov["attributed_with_no_declared_lane"] == 1


def test_coverage_counts_rows_without_metadata(board_env):
    cov = board_env(None)["coverage"]  # no bundle_metadata.json written
    assert cov["rows_without_metadata"] == 1


# ── Empty populations are failures, not passes ────────────────────────────────────────

def test_empty_roster_raises(monkeypatch):
    monkeypatch.setattr(df, "BUNDLE_CODES", ())
    with pytest.raises(RuntimeError, match="EMPTY"):
        df.flow_board(by_bundle={}, finding_nodes=[_finding("f")], gate_nodes=[],
                      freshness_findings=[])


def test_empty_finding_population_raises(board_env):
    with pytest.raises(RuntimeError, match="EMPTY"):
        board_env({}, findings=[])


def test_load_finding_nodes_raises_on_an_empty_extraction(monkeypatch):
    import build_graph
    monkeypatch.setattr(build_graph, "extract_review_finding_nodes", lambda: [])
    with pytest.raises(RuntimeError, match="NOTHING"):
        df.load_finding_nodes()


# ── Structural guards ─────────────────────────────────────────────────────────────────

def test_unknown_cell_kind_raises():
    with pytest.raises(ValueError, match="unknown cell kind"):
        df._cell("greenish", "x")


def test_every_emitted_kind_is_declared(board_env):
    for row in board_env({"stage9_status": "quarantined"})["rows"]:
        for cell in row["cells"].values():
            assert cell["kind"] in df.CELL_KINDS


def test_cells_and_columns_cannot_drift_apart(board_env):
    row = _row(board_env({}))
    assert set(row["cells"]) == {c.key for c in df.COLUMNS}


# ── The two soft signals, and their guards ────────────────────────────────────────────

def test_caveats_name_both_soft_signals_and_their_todos(board_env):
    text = "\n".join(board_env({})["caveats"])
    assert "TODO-D50" in text and "TODO-D51" in text
    assert "HAND-TYPED" in text
    assert "docs/counts.tex" in text


def test_caveats_always_state_the_read_through_gap(board_env):
    assert any("§7.5" in c and "NOT TRACKED" in c for c in board_env({})["caveats"])


def test_row_renders_both_soft_signal_fields(board_env):
    soft = _row(board_env({}))["soft_signals"]
    assert set(soft) == {"registered_lean_modules", "manuscript_length"}
    assert "TODO-D50" in soft["registered_lean_modules"]["note"]
    assert "TODO-D51" in soft["manuscript_length"]["note"]


def test_unmeasured_length_reports_its_reason(board_env):
    length = _row(board_env({}, tex=False, pdf=False))["soft_signals"]["manuscript_length"]
    assert length["measured"] is False
    assert length["unmeasured_reason"]


def test_unreadable_append_log_is_unmeasured_not_empty(tmp_path, monkeypatch):
    """`None` from `_registered_lean_modules` means UNMEASURED. `0 modules` would be a lie."""
    import check_bundle_source_freshness as fresh
    monkeypatch.setattr(fresh, "_registered_lean_modules", lambda code: None)
    out = df.registered_lean_modules("X1")
    assert out["measured"] is False and out["count"] is None


# ── The live tree ─────────────────────────────────────────────────────────────────────

@pytest.mark.slow
def test_live_board_is_internally_consistent():
    board = df.flow_board()
    assert board["rows"], "an empty live board is a failure, not a clean portfolio"
    assert board["coverage"]["open_findings"] > 0
    assert board["caveats"]
    for row in board["rows"]:
        assert row["cells"]["read_through"]["kind"] == "not-tracked"
        for cell in row["cells"].values():
            assert cell["kind"] in df.CELL_KINDS
    # The drift D15 says the board must not hide is still present; if this ever goes
    # empty, the enum was reconciled and the caveat text should be revisited.
    assert board["status_census"]["undeclared_by_roadmap"]


@pytest.mark.slow
def test_live_overlay_is_never_larger_than_the_aggregation_says():
    board = df.flow_board()
    for row in board["rows"]:
        assert row["overlay"]["open_total"] == len(row["overlay_ids"])
        assert sum(row["overlay"]["by_lane"].values()) + len(
            row["overlay"]["unresolved_ids"]) == row["overlay"]["open_total"]


# ══════════════════════════════════════════════════════════════════════════════════════
# MUTATION EVIDENCE — each seeded defect, and the test that caught it
#
# Run 2026-08-12 against `scripts/dashboard_flow.py`, default (fast) selection, 46 tests.
# Every mutation was applied, the suite run, the named tests observed RED, and the file
# restored — verified by a final green run at the end of the sweep.
#
#  1. `_status_cell`: the undeclared branch replaced by `_cell("pending", "pending")` —
#     the coercion D15 forbids.                                            (5 failed)
#     RED: test_undeclared_status_renders_verbatim[pending-redo|skeleton|not_started],
#          test_a_value_nobody_has_ever_seen_still_renders_verbatim,
#          test_undeclared_status_is_not_coerced_to_pending.
#     ⚠️ `test_status_census_reports_the_undeclared_values` stayed GREEN, correctly: the
#     census reads `raw_status` off the metadata, not the rendered cell. Two independent
#     paths, and the mutation only broke one — which is the reason both are asserted.
#
#  2. `_read_through_cell`: returned `_cell("green", "read")`.             (1 failed)
#     RED: test_read_through_is_not_tracked_and_never_a_verdict.
#
#  3. `_stage13_cell`: `sufficient = True` unconditionally.                (4 failed)
#     RED: test_s13_green_withheld_for_any_other_kind[all 4 params].
#
#  4. `_stage10_cell`: `green_ok=True` regardless of the artifact.         (1 failed)
#     RED: test_stage10_green_withheld_without_the_artifact.
#
#  5. `lane_overlay`: `open_finding_ids[:10]` — the classic silent cap.    (1 failed)
#     RED: test_overlay_has_no_silent_cap.
#
#  6. `_submission_cell`, both no-verdict branches, each -> `_cell("green", "ready")`:
#     6a no-gate-nodes-at-all                                              (1 failed)
#        RED: test_submission_with_no_gate_nodes_at_all_is_unmeasured_never_green.
#     6b gates exist but none names this bundle                            (1 failed)
#        RED: test_submission_for_a_bundle_the_gates_never_name_is_unmeasured.
#     ⚠️ **THIS SWEEP FOUND A REAL DEFECT.** The first version of `_submission_cell` had a
#     third branch, `state is None`, which `readiness_by_bundle` can never produce — so
#     substituting `green` into it left the whole suite GREEN. A surviving mutation in a
#     board whose job is to never render an unmeasured thing as fine is exactly the finding
#     this file's mutation discipline exists to produce. The dead branch was deleted and
#     the two reachable no-verdict states were split, at which point both mutations died.
#
#  7. `coverage`: keyless findings counted as attributed.                  (1 failed)
#     RED: test_coverage_partitions_the_open_population — via the module's OWN partition
#          assert, which fires before the test's assertions do.
#
#  8. `flow_board`: the empty-roster `raise` replaced by a `{'rows': []}` return.
#     RED: test_empty_roster_raises.                                       (1 failed)
# ══════════════════════════════════════════════════════════════════════════════════════
