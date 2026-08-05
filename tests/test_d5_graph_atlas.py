"""D5 both-directions tests for `validation/checks/graph_atlas.py` — audit QI-27.

Three checks: `graph_integrity`, `atlas_integrity`, `atlas_hypothesis_discipline`.

`graph_integrity` is the single most defect-dense check in the suite by its own
comment history — the roster round-trip (two-digit bundle codes silently unresolved),
the orphan-finding guard (strengthened after a reviewer passed it under three
mutations), the ledger-dangling baseline (pinned at 67 against a population of 66, so
it carried exactly one slot of headroom in the guard whose purpose is catching newly
filed closures that name nothing), and TWO exception handlers converted from
fail-open to fail-closed. Every one of those is a leg below.

Each test drives the REAL check over a synthetic graph — `build_graph_json`,
`_infer_bundle_from_text` and `run_integrity_checks` are monkeypatched at their owning
modules, because a real build costs ~9 s and would make the failure modes
unreachable anyway (they need a graph that is WRONG in a specific way).

MUTATION-VERIFIED 2026-08-04 — 10 mutations, all CAUGHT, clean negative control.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT / "scripts"))
sys.path.insert(0, str(SK_ROOT))

import build_graph  # noqa: E402
import graph_integrity as gi_mod  # noqa: E402
import validate_helpers as _H  # noqa: E402
from src.core import constants as _c  # noqa: E402
from validation.checks import graph_atlas as ga  # noqa: E402

CLEAN_SUMMARY = {
    "total_nodes": 10, "total_edges": 5, "conflicts": 0, "orphans": 0,
    "orphan_claims": 0, "ungrounded": 0, "broken_chains": 0, "missing_provenance": 0,
}


def _report(**over):
    s = dict(CLEAN_SUMMARY, **over)
    return {"summary": s, "conflicts": [], "orphan_nodes": [], "orphan_claims": [],
            "ungrounded_claims": [], "broken_chains": [], "missing_provenance": []}


def _finding(fid: str, bundle: str | None, review_file: str = "") -> dict:
    return {"id": fid, "type": "ReviewFinding",
            "meta": {"inferred_bundle": bundle, "review_file": review_file}}


class TestGraphIntegrity:

    def _run(self, tmp_path, monkeypatch, *, nodes=(), edges=(), ledger=None,
             report=None, roster=("D1", "D11"), infer=None):
        monkeypatch.setattr(build_graph, "_infer_bundle_from_text",
                            infer or (lambda t: t))
        monkeypatch.setattr(build_graph, "build_graph_json",
                            lambda: {"nodes": list(nodes), "edges": list(edges)})
        monkeypatch.setattr(gi_mod, "run_integrity_checks",
                            lambda: report or _report())
        import bundle_registry
        monkeypatch.setattr(bundle_registry, "VALID_BUNDLE_TARGETS", frozenset(roster))
        docs = tmp_path / "docs"
        docs.mkdir(parents=True, exist_ok=True)
        (docs / "review_finding_supersessions.json").write_text(
            json.dumps({"supersessions": ledger or []}))
        monkeypatch.setattr(_H, "DOCS_DIR", docs)
        return ga.check_graph_integrity()

    FLAGGED = ([_finding("review:r:D11:1.1", "D11", "papers/AutomatedReviews/r/D11.md")],
               [{"type": "FLAGS", "source": "review:r:D11:1.1", "target": "paper:D11"}])

    def test_a_clean_graph_passes(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA."""
        nodes, edges = self.FLAGGED
        r = self._run(tmp_path, monkeypatch, nodes=nodes, edges=edges)
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_a_bundle_code_that_does_not_round_trip_fails(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT. `D[1-9]` silently failed on every TWO-DIGIT
        code, so D10–D12's findings were invisible to the FLAGS-edge builder and D12
        rendered 'Blockers 0' while carrying 36 open ReviewFindings."""
        nodes, edges = self.FLAGGED
        r = self._run(tmp_path, monkeypatch, nodes=nodes, edges=edges,
                      infer=lambda t: t if len(t) <= 2 else None)
        assert r.passed is False, (
            "a roster bundle code that does not round-trip passed — two-digit codes "
            "are invisible to the graph again")
        assert any(d.name == "bundle_code_roundtrip" and not d.passed for d in r.details)

    def test_a_finding_flagging_the_wrong_target_fails(self, tmp_path, monkeypatch):
        """The STRENGTHENED predicate (round-6). The first version asked only 'does
        this finding emit SOME FLAGS edge', which a reviewer passed under three
        mutations — including retargeting D11's 39 edges to a source-paper stub. It
        now asserts that a finding about bundle X flags `paper:X`."""
        r = self._run(tmp_path, monkeypatch,
                      nodes=[_finding("review:r:D11:1.1", "D11")],
                      edges=[{"type": "FLAGS", "source": "review:r:D11:1.1",
                              "target": "paper:some_source_stub"}])
        assert r.passed is False, (
            "a finding flagging a DIFFERENT paper than its own bundle passed — the "
            "guard is back to 'some edge exists'")
        assert any(d.name == "findings_reach_the_graph" and not d.passed
                   for d in r.details)

    def test_a_bundle_named_review_whose_findings_do_not_resolve_fails(
            self, tmp_path, monkeypatch):
        """The SECOND leg. A finding whose bundle inference FAILS is excluded from the
        first scan by construction, so the guard was blind to the very layer-1 defect
        that started the class."""
        r = self._run(tmp_path, monkeypatch,
                      nodes=[_finding("review:r:D11:1.1", None,
                                      "papers/AutomatedReviews/r/D11.md")],
                      edges=[])
        assert r.passed is False
        assert any("yield no finding resolving to it" in (d.message or "")
                   for d in r.details)

    def test_a_failing_orphan_scan_fails_rather_than_warns(self, tmp_path, monkeypatch):
        """D12 round-6 finding 8.2 — the original handler used `warning=True` and
        failed OPEN. A guard that exists to make invisible findings visible must not
        make a build error indistinguishable from a clean scan."""
        def _boom():
            raise RuntimeError("graph build failed")
        monkeypatch.setattr(build_graph, "build_graph_json", _boom)
        monkeypatch.setattr(build_graph, "_infer_bundle_from_text", lambda t: t)
        monkeypatch.setattr(gi_mod, "run_integrity_checks", lambda: _report())
        monkeypatch.setattr(_H, "DOCS_DIR", tmp_path)
        r = ga.check_graph_integrity()
        assert r.passed is False
        assert any(d.name == "findings_reach_the_graph" and "unverified" in (d.message or "")
                   for d in r.details)

    def test_a_dangling_closure_above_the_baseline_fails(self, tmp_path, monkeypatch):
        """The ledger guard. ⚠️ Its baseline sat at 67 against a population of 66 —
        exactly one slot of headroom, in the guard whose entire purpose is catching a
        NEWLY filed closure that names nothing. Three such records were filed while it
        was effectively inert."""
        nodes, edges = self.FLAGGED
        ledger = [{"finding_id": f"review:r:ghost:{i}"} for i in range(67)]
        r = self._run(tmp_path, monkeypatch, nodes=nodes, edges=edges, ledger=ledger)
        assert r.passed is False, (
            "67 dangling closures did not exceed the pinned baseline of 66 — the "
            "ratchet has headroom again")
        assert any(d.name == "ledger_ids_resolve" and not d.passed for d in r.details)

    def test_dangling_closures_at_the_baseline_pass_with_a_warning(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA — pre-existing debt is tracked, not failed."""
        nodes, edges = self.FLAGGED
        ledger = [{"finding_id": f"review:r:ghost:{i}"} for i in range(66)]
        r = self._run(tmp_path, monkeypatch, nodes=nodes, edges=edges, ledger=ledger)
        assert r.passed is True
        assert any(d.name == "ledger_ids_resolve" and d.warning for d in r.details)

    def test_legacy_scheme_ledger_ids_are_out_of_scope(self, tmp_path, monkeypatch):
        """Only `review:`-scheme ids ever minted nodes. Flagging the legacy
        `bundle-stage10:` records would be noise, not signal."""
        nodes, edges = self.FLAGGED
        ledger = [{"finding_id": f"bundle-stage10:x:{i}"} for i in range(200)]
        r = self._run(tmp_path, monkeypatch, nodes=nodes, edges=edges, ledger=ledger)
        assert r.passed is True

    def test_an_unreadable_ledger_fails_rather_than_passes(self, tmp_path, monkeypatch):
        """Converted from fail-open 2026-08-01: ANY exception in the scan used to
        make the guard silently absent, which is the state a mutation test found it
        in — planting a dangling record left the check green with no detail emitted."""
        nodes, edges = self.FLAGGED
        self._run(tmp_path, monkeypatch, nodes=nodes, edges=edges)
        (tmp_path / "docs" / "review_finding_supersessions.json").write_text("{not json")
        r = ga.check_graph_integrity()
        assert r.passed is False
        assert any(d.name == "ledger_ids_resolve" and "FAILED TO RUN" in (d.message or "")
                   for d in r.details)

    def test_a_verification_conflict_is_a_hard_failure(self, tmp_path, monkeypatch):
        nodes, edges = self.FLAGGED
        r = self._run(tmp_path, monkeypatch, nodes=nodes, edges=edges,
                      report={**_report(conflicts=2),
                              "conflicts": [{"name": "a"}, {"name": "b"}]})
        assert r.passed is False

    def test_an_orphan_claim_is_a_hard_failure(self, tmp_path, monkeypatch):
        """R-06 regression guard: every discovered paper claim must be CLAIMS-connected
        to its paper. Distinct from generic orphans, which are expected substrate."""
        nodes, edges = self.FLAGGED
        r = self._run(tmp_path, monkeypatch, nodes=nodes, edges=edges,
                      report={**_report(orphan_claims=1),
                              "orphan_claims": [{"id": "claim:x"}]})
        assert r.passed is False

    def test_generic_orphans_and_broken_chains_stay_advisory(self, tmp_path, monkeypatch):
        """Unconnected Lean declaration nodes are expected substrate. Hard-failing
        them would make the check unusable and it would be turned off."""
        nodes, edges = self.FLAGGED
        r = self._run(tmp_path, monkeypatch, nodes=nodes, edges=edges,
                      report={**_report(orphans=3, broken_chains=4, ungrounded=2,
                                        missing_provenance=1),
                              "orphan_nodes": [{"id": "a"}], "broken_chains": [{"formula": "f"}],
                              "ungrounded_claims": [{"id": "c"}],
                              "missing_provenance": [{"name": "p"}]})
        assert r.passed is True
        assert any(d.name == "orphan_nodes" and d.warning for d in r.details)


def _atlas(nodes=(), unknowns=()):
    return {"nodes": list(nodes), "unknowns": list(unknowns)}


class TestAtlasIntegrity:
    """ADR-005 D-F. The atlas is a PROJECTION of `lean_deps.json` ∪ registries, so it
    cannot drift — but the registries it projects can lie."""

    def _run(self, monkeypatch, *, atlas, deps=(), registry=None, metadata=None,
             axioms=None):
        import atlas_view
        monkeypatch.setattr(atlas_view, "load_lean_deps_file", lambda: list(deps))
        monkeypatch.setattr(atlas_view, "build_atlas", lambda d: atlas)
        monkeypatch.setattr(atlas_view, "_genuine_project_axioms",
                            axioms or (lambda r: []))
        monkeypatch.setattr(_c, "AXIOM_METADATA", metadata or {})
        monkeypatch.setattr(_c, "HYPOTHESIS_REGISTRY", registry or {})
        return ga.check_atlas_integrity()

    def test_a_consistent_atlas_passes(self, monkeypatch):
        """SILENT ON CORRECT DATA."""
        r = self._run(monkeypatch, atlas=_atlas(
            nodes=[{"fqn": "A.b", "atlas_kind": "PROVED", "atlas_status": "PROVED"}],
            unknowns=[{"id": "hyp:H_x", "atlas_kind": "UNKNOWN", "atlas_status": "OPEN"}]))
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_conflicting_atlas_kinds_fail(self, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — one FQN classified two ways means the
        projection is inconsistent with itself."""
        r = self._run(monkeypatch, atlas=_atlas(nodes=[
            {"fqn": "A.b", "atlas_kind": "PROVED", "atlas_status": "PROVED"},
            {"fqn": "A.b", "atlas_kind": "OBSTRUCTION", "atlas_status": "PROVED"}]))
        assert r.passed is False
        assert any(d.name == "kind_consistency" and not d.passed for d in r.details)

    def test_an_undisclosed_project_axiom_fails(self, monkeypatch):
        """Invariant: every GENUINE project axiom must be disclosed in
        `AXIOM_METADATA`. Currently 0 — this catches a future stray."""
        r = self._run(monkeypatch, atlas=_atlas(),
                      deps=[{"name": "A.b"}],
                      axioms=lambda r: ["SKEFTHawking.stray_axiom"])
        assert r.passed is False
        assert any(d.name == "no_undisclosed_project_axiom" and not d.passed
                   for d in r.details)

    def test_a_disclosed_axiom_passes(self, monkeypatch):
        """The escape is DISCLOSURE, matching the project's axiom policy."""
        r = self._run(monkeypatch, atlas=_atlas(), deps=[{"name": "A.b"}],
                      axioms=lambda r: ["SKEFTHawking.stray_axiom"],
                      metadata={"stray_axiom": {"reason": "documented"}})
        assert r.passed is True

    def test_a_silently_discharged_apex_fails(self, monkeypatch):
        """ADR-005 D-H failure mode (a): the apex is still marked OPEN but a producer
        theorem already proves it. The atlas would keep advertising an open headline
        target that is in fact closed, so fan-out aims at nothing."""
        r = self._run(monkeypatch, atlas=_atlas(
            nodes=[{"fqn": "A.H_apex", "atlas_kind": "PROVED", "atlas_status": "PROVED"}],
            unknowns=[{"id": "hyp:H_apex", "atlas_kind": "UNKNOWN",
                       "atlas_status": "OPEN", "is_apex": True}]))
        assert r.passed is False
        assert any("open but producer" in (d.message or "") for d in r.details)

    def test_a_bogus_apex_closure_fails(self, monkeypatch):
        """Failure mode (b): marked DISCHARGED with NO producer theorem — a closure
        with nothing behind it."""
        r = self._run(monkeypatch, atlas=_atlas(
            unknowns=[{"id": "hyp:H_apex", "atlas_kind": "UNKNOWN",
                       "atlas_status": "DISCHARGED", "is_apex": True}]))
        assert r.passed is False
        assert any("no producer theorem found" in (d.message or "") for d in r.details)

    def test_a_suffixed_discharge_theorem_counts_as_a_producer(self, monkeypatch):
        """R-07: a discharge theorem's short name may be SUFFIXED
        (`H_x_unconditional` discharges `H_x`), so exact-name matching alone reports
        a correct closure as bogus."""
        r = self._run(monkeypatch, atlas=_atlas(
            nodes=[{"fqn": "A.H_apex_unconditional", "atlas_kind": "PROVED",
                    "atlas_status": "PROVED"}],
            unknowns=[{"id": "hyp:H_apex", "atlas_kind": "UNKNOWN",
                       "atlas_status": "DISCHARGED", "is_apex": True}]))
        assert r.passed is True, (
            "a suffixed discharge theorem was not recognised as a producer — correct "
            "closures would be reported as bogus (R-07)")

    def test_a_phantom_dependent_theorem_fails(self, monkeypatch):
        """R-07 caught `SKEFTHawking.central_charge_from_sm`: a registry naming a
        theorem that exists nowhere."""
        r = self._run(monkeypatch, atlas=_atlas(), deps=[{"name": "A.real"}],
                      registry={"H_x": {"dependent_theorems": ["A.ghost"]}})
        assert r.passed is False
        assert any(d.name == "dependent_theorems_resolve" and not d.passed
                   for d in r.details)

    def test_namespace_drift_is_advisory_not_a_phantom(self, monkeypatch):
        """The theorem EXISTS, only the registry's FQN prefix is stale. Hard-failing
        that would conflate a stale prefix with a nonexistent target."""
        r = self._run(monkeypatch, atlas=_atlas(), deps=[{"name": "Other.real"}],
                      registry={"H_x": {"dependent_theorems": ["A.real"]}})
        assert r.passed is True
        assert any(d.name == "dependent_theorems_namespace_drift" and d.warning
                   for d in r.details)

    def test_a_failing_atlas_build_fails_rather_than_passes(self, monkeypatch):
        import atlas_view

        def _boom():
            raise RuntimeError("bad lean_deps")
        monkeypatch.setattr(atlas_view, "load_lean_deps_file", _boom)
        assert ga.check_atlas_integrity().passed is False


class TestAtlasHypothesisDiscipline:
    """INFO-ONLY BY DESIGN. ADR-009 §Alternatives note 3 records a subagent reporting
    this as contradicting its own 'never a gate' description — the `passed=False` it
    saw is in the EXCEPTION handler, which is a fail-on-cannot-measure and the correct
    pattern. Both facts are pinned here."""

    def _run(self, monkeypatch, unknowns):
        import atlas_view
        monkeypatch.setattr(atlas_view, "load_lean_deps_file", lambda: [])
        monkeypatch.setattr(atlas_view, "build_atlas",
                            lambda d: _atlas(unknowns=unknowns))
        return ga.check_atlas_hypothesis_discipline()

    def test_it_never_gates_however_bad_the_distribution(self, monkeypatch):
        """On a clean tree MOST tracked hypotheses are legitimately ORPHAN — external
        boundary / future landmarks that gate nothing yet. Failing on them would
        punish precise parked statements, so this is INFO-only by design."""
        r = self._run(monkeypatch, [{"id": f"hyp:H_{i}", "module": "M"} for i in range(50)])
        assert r.passed is True, (
            "atlas_hypothesis_discipline started gating — it is INFO-ONLY by design "
            "(ADR-007 PD-2); the bank-or-grind discipline lives in the coach")

    def test_it_reports_the_gating_vs_orphan_split(self, monkeypatch):
        """The output IS the product, so both directions are on the numbers."""
        r = self._run(monkeypatch, [
            {"id": "hyp:H_a", "module": "Alpha (Phase 6)", "dependent_theorems": ["A.t"]},
            {"id": "hyp:H_b", "module": "Beta"},
        ])
        msg = next(d for d in r.details if d.name == "gating_vs_orphan").message
        assert "1 gate >=1 downstream theorem" in msg and "1 orphan" in msg

    def test_the_module_stem_strips_a_phase_annotation(self, monkeypatch):
        """`module` is often annotated `Foo (Phase X…)`; without stripping, the same
        module counts as several and the density figure is meaningless."""
        r = self._run(monkeypatch, [
            {"id": "hyp:H_a", "module": "Alpha (Phase 6AA)"},
            {"id": "hyp:H_b", "module": "Alpha (Phase 6AB)"},
        ])
        msg = next(d for d in r.details if d.name == "per_module_distribution").message
        assert "Alpha=2" in msg, f"module stems were not collapsed: {msg}"

    def test_a_failing_atlas_build_fails(self, monkeypatch):
        """⚠️ The ONE place this check returns False — a fail-on-cannot-measure in the
        exception handler, which is the CORRECT pattern and not a contradiction of
        'never a gate'. ADR-009 §Alternatives note 3 records a reconnaissance agent
        misreading exactly this."""
        import atlas_view

        def _boom():
            raise RuntimeError("bad")
        monkeypatch.setattr(atlas_view, "load_lean_deps_file", _boom)
        assert ga.check_atlas_hypothesis_discipline().passed is False
