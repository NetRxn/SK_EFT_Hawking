"""Attention surface — ADR-012 D12/D15 S3, the four unmerged feeds.

Spec: `docs/adrs/ADR-012-finding-lifecycle-routing-and-closure.md` §D12, §D15 S3.

Each test names the defect it would catch. The properties being defended are the ones whose
failure is SILENT — an absent store rendering as a calm empty feed, a three-valued release
condition collapsing to two, a top-8 view read as a population — because those are
indistinguishable from good news at the pane.
"""
from __future__ import annotations

import json
import sys
import time
from pathlib import Path

import pytest

PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT))
sys.path.insert(0, str(PROJECT_ROOT / "scripts"))

import dashboard_attention as att  # noqa: E402


# ─────────────────────────────────────────────────────────────────────────────
# fixtures — synthetic stores, so no test depends on this machine's local state
# ─────────────────────────────────────────────────────────────────────────────
def _finding(fid, needs_operator=None, status="open", **meta):
    m = {"status": status, "severity": "major", "lane": "lean",
         "target": "papers/D12/paper_draft.tex:100", "verify": "uv run pytest -q",
         "needs_operator": needs_operator}
    m.update(meta)
    return {"id": fid, "type": "ReviewFinding", "label": f"label for {fid}", "meta": m}


NODES = [
    _finding("review:a:1", "queue"),
    _finding("review:a:2", "now"),
    _finding("review:a:3", None),
    _finding("review:a:4", "urgent"),          # an unrecognised value — must be counted
    _finding("review:a:5", "queue", status="fixed"),   # closed: out of every feed
    _finding("review:a:6", "queue", target=None),      # no target → no orientation
]


def _parked(pid, tokens, lane="pyrust"):
    return {"id": f"parked:{pid}", "type": "ParkedItem",
            "meta": {"lane": lane, "target": "docs/X.md", "reason": "r",
                     "blocked_by": list(tokens), "source": "docs/roadmaps/P.md",
                     "status": "open"}}


@pytest.fixture
def active_issues(tmp_path):
    p = tmp_path / "active_issues.json"
    p.write_text(json.dumps({"generated": time.time() - 86400, "issues": [
        {"title": "low tally automatic", "tier": "automatic", "tally": 2, "kind": "issue"},
        {"title": "human one", "tier": "human-reviewed", "tally": 5, "kind": "issue"},
        {"title": "agent one", "tier": "agent-reviewed", "tally": 9, "kind": "issue"},
        {"title": "human two", "tier": "human-reviewed", "tally": 11, "kind": "issue"},
    ]}))
    return p


@pytest.fixture
def blocked_log(tmp_path):
    p = tmp_path / "blocked_questions.jsonl"
    now = time.time()
    rows = [
        {"ts": now - 10 * 86400, "session_id": "s1", "questions": [
            {"question": "Which route?", "header": "Next phase", "multiSelect": False,
             "options": [{"label": "A", "description": "do A"},
                         {"label": "B", "description": "do B"}]}]},
        {"ts": now - 2 * 86400, "session_id": "s2", "questions": [
            {"question": "Which route again?", "header": "next phase",
             "multiSelect": False, "options": []},
            {"question": "Close out?", "header": "Close-out", "multiSelect": False,
             "options": []}]},
    ]
    p.write_text("\n".join(json.dumps(r) for r in rows) + "\n{ this is not json }\n")
    return p


# ─────────────────────────────────────────────────────────────────────────────
# THE FOUR FEEDS ARE NOT MERGED
# ─────────────────────────────────────────────────────────────────────────────
class TestFeedsAreNotMerged:
    """Operator ruling (D12): four feeds, surfaced together, NOT flattened."""

    def test_the_four_feeds_are_four_separate_lists(self, active_issues, blocked_log,
                                                    monkeypatch):
        monkeypatch.setattr(att, "ACTIVE_ISSUES_PATH", active_issues)
        monkeypatch.setattr(att, "BLOCKED_QUESTIONS_PATH", blocked_log)
        assert isinstance(att.publication(NODES, qi_items=[]), list)
        assert isinstance(att.process(active_issues), list)
        assert isinstance(att.decisions(NODES, blocked_log), list)
        assert isinstance(att.parked([]), list)

    def test_each_feed_keeps_its_own_vocabulary(self, active_issues, blocked_log):
        """A common row schema is the failure: it is what makes every item 'a thing with a
        title'. Each feed must carry fields the others do not."""
        pub = att.publication(NODES, qi_items=[])[0]
        proc = att.process(active_issues)[0]
        dec = [d for d in att.decisions(NODES, blocked_log)
               if d["source"] == "blocked_question"][0]
        park = att.parked([_parked("x", ["phase:5q.G"])])[0]
        assert "decision_package" in pub and "conditions" not in pub
        assert "tier" in proc and "severity" not in proc
        assert "options" in dec and "lane" not in dec
        assert "conditions" in park and "tier" not in park

    def test_a_now_finding_appears_in_both_panes_and_says_so(self, blocked_log):
        """D15 places `needs_operator: now` in Decisions AND Publication. The overlap is by
        design, so it must be MARKED — an unmarked duplicate reads as a double count."""
        pub_ids = {r["id"] for r in att.publication(NODES, qi_items=[])}
        dec = [d for d in att.decisions(NODES, blocked_log)
               if d["source"] == "review_finding"]
        assert [d["id"] for d in dec] == ["review:a:2"]
        assert dec[0]["also_in"] == "publication"
        assert "review:a:2" in pub_ids


# ─────────────────────────────────────────────────────────────────────────────
# feed A — publication
# ─────────────────────────────────────────────────────────────────────────────
class TestPublicationFeed:
    def test_only_open_needs_operator_findings_are_routed(self):
        ids = {r["id"] for r in att.publication(NODES, qi_items=[])
               if r["source"] == "review_finding"}
        assert ids == {"review:a:1", "review:a:2", "review:a:4", "review:a:6"}
        assert "review:a:5" not in ids, "a fixed finding is not waiting on the operator"
        assert "review:a:3" not in ids, "no needs_operator means unrouted, not routed"

    def test_the_decision_package_reports_what_it_CANNOT_check(self):
        """D11 requires five components; exactly one is derivable from the store. Claiming
        the other four are satisfied because nothing contradicts them turns 'deferred' into
        'routed' by omission."""
        by_id = {r["id"]: r for r in att.publication(NODES, qi_items=[])
                 if r["source"] == "review_finding"}
        pkg = by_id["review:a:1"]["decision_package"]
        assert pkg["orientation_available"] is True
        assert "review_runner.py --finding review:a:1" in pkg["orientation_command"]
        assert len(pkg["not_machine_checkable"]) == 4
        assert set(pkg["not_machine_checkable"]) < set(att.DECISION_PACKAGE_COMPONENTS)
        no_target = by_id["review:a:6"]["decision_package"]
        assert no_target["orientation_available"] is False
        assert no_target["orientation_command"] is None

    def test_qi_items_join_the_feed_under_their_own_vocabulary(self):
        qi = [{"id": "qi-x-1", "pattern_summary": "recurring", "gate_affected": "Gate",
               "window": "2026-08", "occurrences": 7, "status": "open"}]
        rows = att.publication(NODES, qi_items=qi, qi_error=None)
        qrow = [r for r in rows if r["source"] == "qi_derived"][0]
        assert qrow["occurrences"] == 7 and qrow["window"] == "2026-08"
        assert "severity" not in qrow, "a QI pattern has no severity; do not invent one"

    def test_a_failed_qi_derivation_is_an_ERROR_not_an_empty_feed(self):
        """The derivation emitted zero for months and the zero was unreadable as a defect."""
        cov = att.coverage(NODES, parked_source=[], qi_items=[],
                           qi_error="RuntimeError: boom")
        assert cov["publication"]["qi_error"] == "RuntimeError: boom"
        assert any("QI derivation did not run" in c for c in att.caveats(cov))


# ─────────────────────────────────────────────────────────────────────────────
# feed B — process (READ-ONLY, and a TOP-N VIEW)
# ─────────────────────────────────────────────────────────────────────────────
class TestProcessFeed:
    def test_the_store_shape_is_the_one_on_disk(self, active_issues):
        rows = att.process(active_issues)
        assert {"title", "tier", "tally", "kind"} <= set(rows[0])
        assert rows[0]["governor"] == "/skeft-qa:debrief"

    def test_tier_then_tally_ordering(self, active_issues):
        rows = att.process(active_issues)
        assert [r["title"] for r in rows] == [
            "human two", "human one", "agent one", "low tally automatic"]

    def test_feed_B_NEVER_writes(self, active_issues):
        """`_clamp_tier` guarantees no writer but /debrief exceeds `agent-reviewed`. A second
        writer here would break that guarantee."""
        before = active_issues.stat().st_mtime_ns, active_issues.read_bytes()
        att.process(active_issues)
        att.coverage(NODES, active_issues_path=active_issues, parked_source=[], qi_items=[])
        assert (active_issues.stat().st_mtime_ns, active_issues.read_bytes()) == before

    def test_the_top_N_CAP_IS_REPORTED_never_silent(self, active_issues):
        cov = att.coverage(NODES, active_issues_path=active_issues, parked_source=[],
                           qi_items=[])
        assert cov["process"]["writer_cap"] == att._active_issues_cap()
        assert cov["process"]["population_recoverable"] is False
        assert any("FLOOR" in c for c in att.caveats(cov))

    def test_an_absent_store_is_a_REPORTED_STATE_not_an_empty_feed(self, tmp_path):
        missing = tmp_path / "nope.json"
        assert att.process(missing) == []
        cov = att.coverage(NODES, active_issues_path=missing, parked_source=[], qi_items=[])
        assert cov["process"]["exists"] is False
        assert cov["process"]["items"] is None, "None (unknown) — never 0 (nothing open)"
        assert any("NO STORE" in c for c in att.caveats(cov))

    def test_a_malformed_store_is_reported_as_an_error(self, tmp_path):
        bad = tmp_path / "active_issues.json"
        bad.write_text("{ not json")
        cov = att.coverage(NODES, active_issues_path=bad, parked_source=[], qi_items=[])
        assert cov["process"]["error"]
        assert cov["process"]["items"] is None

    def test_the_gitignored_paths_are_the_measured_ones(self):
        """These three are `git check-ignore`-verified; the honesty claim rests on it."""
        LOCAL = att.LOCAL_ONLY_SOURCES
        assert ".claude/dev-harness/active_issues.json" in LOCAL
        assert ".claude/dev-harness/blocked_questions.jsonl" in LOCAL
        assert "docs/dev-loops/SYSTEM2_REGISTER.md" in LOCAL


# ─────────────────────────────────────────────────────────────────────────────
# feed C — decisions
# ─────────────────────────────────────────────────────────────────────────────
class TestDecisionsFeed:
    def test_each_question_carries_its_options_and_its_AGE(self, blocked_log):
        """D12: what feed C lacks is an operator-facing surface and a LATENCY FLOOR — it has
        two live readers already. Age is the load-bearing new field."""
        rows = [d for d in att.decisions(NODES, blocked_log)
                if d["source"] == "blocked_question"]
        assert len(rows) == 3
        oldest = max(rows, key=lambda r: r["age_days"])
        assert 9.5 < oldest["age_days"] < 10.5
        assert [o["label"] for o in oldest["options"]] == ["A", "B"]

    def test_resolution_is_UNKNOWN_for_every_question(self, blocked_log):
        """The log records asks; nothing records outcomes. `False` would claim every
        historical question is still waiting."""
        rows = [d for d in att.decisions(NODES, blocked_log)
                if d["source"] == "blocked_question"]
        assert all(r["resolved"] is None for r in rows)
        cov = att.coverage(NODES, blocked_questions_path=blocked_log, parked_source=[],
                           qi_items=[])
        assert cov["decisions"]["resolution_recorded"] is False

    def test_every_question_carries_the_graduation_affordance(self, blocked_log):
        rows = [d for d in att.decisions(NODES, blocked_log)
                if d["source"] == "blocked_question"]
        assert all(r["graduation_affordance"]["route"] == "/skeft-qa:debrief" for r in rows)

    def test_malformed_lines_are_COUNTED_not_silently_dropped(self, blocked_log):
        cov = att.coverage(NODES, blocked_questions_path=blocked_log, parked_source=[],
                           qi_items=[])
        assert cov["decisions"]["malformed_lines"] == 1
        assert any("did not parse" in c for c in att.caveats(cov))

    def test_an_absent_log_is_a_REPORTED_STATE(self, tmp_path):
        missing = tmp_path / "nope.jsonl"
        assert [d for d in att.decisions(NODES, missing)
                if d["source"] == "blocked_question"] == []
        cov = att.coverage(NODES, blocked_questions_path=missing, parked_source=[],
                           qi_items=[])
        assert cov["decisions"]["exists"] is False
        assert cov["decisions"]["questions"] is None
        assert any(c.startswith("Decisions has NO STORE") for c in att.caveats(cov))


class TestGraduationSignal:
    def test_a_class_asked_twice_is_surfaced(self, blocked_log):
        """D12: a class asked more than once with no graduated pre-decision behind it is a
        PROCESS DEFECT. The header is case-normalised or the repeat hides."""
        sig = att.graduation_signal(blocked_log)
        assert sig["asks_total"] == 3
        assert sig["repeat_classes"] == ["next phase"]
        assert sig["classes"]["next phase"]["asks"] == 2
        assert sig["classes"]["next phase"]["sessions"] == 2

    def test_per_class_graduation_is_NOT_FAKED(self, blocked_log):
        """No back-link exists between a pre-decision and the class that motivated it."""
        sig = att.graduation_signal(blocked_log)
        assert all(c["graduated_pre_decision"] is None for c in sig["classes"].values())
        assert len(sig["not_computable"]) == 2

    def test_graduated_count_is_parsed_when_the_section_exists(self, tmp_path):
        p = tmp_path / "PRE_DECISIONS.md"
        p.write_text("## Full\n\n### Graduated pre-decisions (appended by `/debrief`)\n\n"
                     "- **PD-G1** when X do Y\n- **PD-G2** when A do B\n\n### Next\n\nfoo\n")
        n, basis = att._graduated_pre_decisions(p)
        assert n == 2 and "Graduated" in basis

    def test_an_absent_section_is_UNKNOWN_not_zero(self, tmp_path):
        p = tmp_path / "PRE_DECISIONS.md"
        p.write_text("## Core\n\nno graduated section here\n")
        n, basis = att._graduated_pre_decisions(p)
        assert n is None, "unknown and zero must not render identically"
        assert "no `Graduated pre-decisions` section" in basis

    def test_an_empty_section_is_ZERO_not_unknown(self, tmp_path):
        p = tmp_path / "PRE_DECISIONS.md"
        p.write_text("### Graduated pre-decisions\n\n_(empty — the long tail)_\n")
        n, _ = att._graduated_pre_decisions(p)
        assert n == 0, "an italic placeholder is not an entry"

    def test_an_absent_log_reports_unavailability(self, tmp_path):
        sig = att.graduation_signal(tmp_path / "nope.jsonl")
        assert sig["source_available"] is False
        assert sig["asks_total"] is None, "None (cannot see) — never 0 (nobody asked)"


# ─────────────────────────────────────────────────────────────────────────────
# feed D — parked. THE THREE-VALUED CONTRACT.
# ─────────────────────────────────────────────────────────────────────────────
class TestParkedFeedThreeValued:
    def test_run_tokens_are_UNKNOWN_by_design(self):
        """`run:` is unresolvable until a run registry exists. Rendering it unmet parks
        released work forever; rendering it met releases work on no evidence."""
        row = att.parked([_parked("mlx", ["run:mlx-rhmc-2026-08"])])[0]
        assert row["conditions"][0]["met"] is None
        assert row["state"] == "unknown"
        assert row["conditions"][0]["why"]

    def test_None_does_not_collapse_to_False(self, monkeypatch):
        import parked_items
        monkeypatch.setattr(parked_items, "release_condition_met",
                            lambda t: {"a:1": True, "b:1": False, "c:1": None}[t])
        assert att.parked([_parked("x", ["a:1"])])[0]["state"] == "released"
        assert att.parked([_parked("x", ["b:1"])])[0]["state"] == "parked"
        assert att.parked([_parked("x", ["c:1"])])[0]["state"] == "unknown"

    def test_ONE_unknown_condition_dominates_a_satisfied_one(self, monkeypatch):
        """Releasing on partial evidence is the exact failure the contract prevents."""
        import parked_items
        monkeypatch.setattr(parked_items, "release_condition_met",
                            lambda t: True if t == "a:1" else None)
        row = att.parked([_parked("x", ["a:1", "c:1"])])[0]
        assert row["state"] == "unknown"
        assert [c["met"] for c in row["conditions"]] == [True, None]

    def test_an_unmet_condition_beats_a_met_one(self, monkeypatch):
        import parked_items
        monkeypatch.setattr(parked_items, "release_condition_met",
                            lambda t: t == "a:1")
        assert att.parked([_parked("x", ["a:1", "b:1"])])[0]["state"] == "parked"

    def test_no_conditions_cannot_read_as_released(self):
        """Vacuous `all()` over an empty list is True — 'no evidence' must not mean 'met'."""
        assert att.parked([_parked("x", [])])[0]["state"] == "unknown"

    def test_zero_declared_blocks_is_distinguishable_from_no_source(self):
        cov = att.coverage(NODES, parked_source=[], qi_items=[])
        assert cov["parked"]["roadmaps_dir_present"] is True
        assert cov["parked"]["declared_blocks"] == 0
        assert any("opt-in" in c for c in att.caveats(cov))

    def test_unknown_conditions_are_counted_and_caveated(self):
        cov = att.coverage(NODES, parked_source=[_parked("m", ["run:x"])], qi_items=[])
        assert cov["parked"]["unresolvable_conditions"] == 1
        assert cov["parked"]["unknown"] == 1
        assert any("UNKNOWN, not unmet" in c for c in att.caveats(cov))


# ─────────────────────────────────────────────────────────────────────────────
# coverage partitions + caveats
# ─────────────────────────────────────────────────────────────────────────────
class TestCoveragePartitions:
    def test_needs_operator_buckets_partition_the_open_population(self):
        p = att.coverage(NODES, parked_source=[], qi_items=[])["publication"]
        assert p["open_findings"] == 5
        assert (p["needs_operator_now"] + p["needs_operator_queue"]
                + p["needs_operator_unrecognised_value"]
                + p["no_needs_operator"]) == p["open_findings"]

    def test_an_unrecognised_needs_operator_value_is_COUNTED_not_dropped(self):
        p = att.coverage(NODES, parked_source=[], qi_items=[])["publication"]
        assert p["needs_operator_unrecognised_value"] == 1, (
            "`urgent` is not in the enum; a dropped value is an invisible routed finding")

    def test_the_publication_partition_assertion_actually_FIRES(self, monkeypatch):
        """A partition asserted in prose is one that drifts. Prove the assert is live: a
        bucketer that invents a fifth bucket must break the sum, not disappear from it."""
        monkeypatch.setattr(att, "_needs_operator_bucket", lambda v: "somewhere_else")
        with pytest.raises(AssertionError, match="do not partition"):
            att.coverage(NODES, parked_source=[], qi_items=[])

    def test_the_parked_partition_assertion_actually_FIRES(self, monkeypatch):
        monkeypatch.setattr(att, "_release_state", lambda conds: "dunno")
        with pytest.raises(AssertionError, match="do not partition"):
            att.coverage(NODES, parked_source=[_parked("x", ["run:y"])], qi_items=[])

    def test_parked_state_buckets_partition(self, monkeypatch):
        import parked_items
        monkeypatch.setattr(parked_items, "release_condition_met",
                            lambda t: {"a": True, "b": False, "c": None}[t[0]])
        src = [_parked("1", ["a:x"]), _parked("2", ["b:x"]), _parked("3", ["c:x"])]
        d = att.coverage(NODES, parked_source=src, qi_items=[])["parked"]
        assert d["released"] + d["parked"] + d["unknown"] == d["declared_blocks"] == 3


class TestCaveats:
    def test_caveats_are_never_empty(self, active_issues, blocked_log):
        cov = att.coverage(NODES, active_issues_path=active_issues,
                           blocked_questions_path=blocked_log, parked_source=[],
                           qi_items=[])
        c = att.caveats(cov)
        assert c and all(isinstance(s, str) and s.strip() for s in c)

    def test_every_feed_gets_at_least_one_sentence(self, active_issues, blocked_log):
        cov = att.coverage(NODES, active_issues_path=active_issues,
                           blocked_questions_path=blocked_log, parked_source=[],
                           qi_items=[])
        joined = " ".join(att.caveats(cov))
        for token in ("Publication", "Process", "Decisions", "Parked"):
            assert token in joined, f"no caveat covers the {token} pane"

    def test_the_unrouted_population_is_stated(self, active_issues, blocked_log):
        """949 open findings declare nothing on this machine; a pane showing 5 must say the
        other population exists, or a short feed reads as a quiet corpus."""
        cov = att.coverage(NODES, active_issues_path=active_issues,
                           blocked_questions_path=blocked_log, parked_source=[],
                           qi_items=[])
        assert any("declare nothing and are NOT shown" in c for c in att.caveats(cov))


# ─────────────────────────────────────────────────────────────────────────────
# aggregator, against the LIVE stores
# ─────────────────────────────────────────────────────────────────────────────
class TestAttentionAggregator:
    def test_the_surface_carries_items_coverage_AND_caveats(self):
        a = att.attention()
        assert set(a) == {"publication", "process", "decisions", "parked",
                          "graduation", "coverage", "caveats"}
        for feed in ("publication", "process", "decisions", "parked"):
            assert isinstance(a[feed], list)
        assert a["caveats"], "a caller must not be able to get items without the caveats"

    def test_it_is_json_serialisable(self):
        """The pane's data layer crosses a render boundary; sets and Paths do not."""
        json.dumps(att.attention(), default=None)

    def test_live_coverage_partitions_hold_on_this_machine(self):
        cov = att.attention()["coverage"]
        p = cov["publication"]
        assert (p["needs_operator_now"] + p["needs_operator_queue"]
                + p["needs_operator_unrecognised_value"]
                + p["no_needs_operator"]) == p["open_findings"]
        d = cov["parked"]
        assert d["released"] + d["parked"] + d["unknown"] == d["declared_blocks"]
