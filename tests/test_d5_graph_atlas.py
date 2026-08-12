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

def _count_in(message: str, unit: str) -> int:
    """Extract the integer preceding `unit` in a summary message.

    ⚠️ USE THIS INSTEAD OF `f"{n} {unit}" in message`. A count substring is true
    for infinitely many values: `"0 drawn"` is a substring of `"10 drawn"`,
    `"1 em-dash"` of `"11 em-dash"`, `"2254 jobs"` of `"12254 jobs"`. Chunk-review
    mutations that inflated five separate production counts by 10x left every one
    of those assertions green.

    This is a CLASS sweep, not a one-site fix. The same defect was found and fixed
    once in `test_d5_papers_prose.py` (`"0 unresolved" in message`) and the other
    sites were not swept — which is exactly how it survived to be found again.
    """
    m = re.search(rf"(\d+) {re.escape(unit)}", message)
    assert m is not None, f"no '<int> {unit}' in message: {message!r}"
    return int(m.group(1))


import json
import re
import sys
from pathlib import Path

import pytest

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


def _live_dangling_baseline() -> int:
    """The production `_LEDGER_DANGLING_BASELINE`, read from source.

    ⚠️ It is a FUNCTION-LOCAL constant, so it cannot be imported. These tests used to
    hardcode 66 and broke the day the re-key lowered it to 59 — a test asserting a ratchet
    has zero headroom must move WITH the ratchet, or it becomes a second, stale copy of the
    number it is guarding.
    """
    import re as _re
    from pathlib import Path as _P
    src = (_P(__file__).resolve().parent.parent
           / "scripts" / "validation" / "checks" / "graph_atlas.py").read_text()
    m = _re.search(r"^\s*_LEDGER_DANGLING_BASELINE\s*=\s*(\d+)", src, _re.M)
    assert m, "_LEDGER_DANGLING_BASELINE not found in graph_atlas.py"
    return int(m.group(1))


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
        base = _live_dangling_baseline()
        ledger = [{"finding_id": f"review:r:ghost:{i}"} for i in range(base + 1)]
        r = self._run(tmp_path, monkeypatch, nodes=nodes, edges=edges, ledger=ledger)
        assert r.passed is False, (
            f"{base + 1} dangling closures did not exceed the pinned baseline of {base} "
            "— the ratchet has headroom again")
        assert any(d.name == "ledger_ids_resolve" and not d.passed for d in r.details)

    def test_dangling_closures_at_the_baseline_pass_with_a_warning(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA — pre-existing debt is tracked, not failed."""
        nodes, edges = self.FLAGGED
        ledger = [{"finding_id": f"review:r:ghost:{i}"}
                  for i in range(_live_dangling_baseline())]
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

    def test_a_MISSING_lean_deps_does_not_kill_the_interpreter(self, tmp_path,
                                                               monkeypatch):
        """⚠️ `atlas_view.load_lean_deps_file` raised `SystemExit` (PR review, fixed
        2026-08-05). `SystemExit` derives from `BaseException`, so it is NOT caught by
        `except Exception` — and BOTH handlers on the path are `except Exception`:
        `check_atlas_integrity`'s own, and `validate.run_checks`'s.

        Measured: `atlas_integrity` runs partway through the suite, so a missing `lean_deps.json`
        did not fail the atlas check — it terminated the interpreter and **the other 24
        checks never ran**, with no report distinguishing that from a clean exit.

        The test asserts the exception TYPE at the source, because that is the whole
        defect: a library function taking a decision that belongs to the CLI boundary.
        `test_no_check_path_raises_SystemExit` below holds the class."""
        import atlas_view
        monkeypatch.setattr(atlas_view, "LEAN_DEPS_PATH", tmp_path / "absent.json")
        with pytest.raises(FileNotFoundError):
            atlas_view.load_lean_deps_file()
        # ...and the check contains it rather than dying.
        r = ga.check_atlas_integrity()
        assert r.passed is False
        assert "lean_deps.json not found" in (r.error or "")

    def test_no_check_path_raises_SystemExit(self):
        """The CLASS, not the instance — the discipline QI-01 established after its
        `glob` fix turned out to be one of six sites.

        A `sys.exit()` / `raise SystemExit` anywhere reachable from a check bypasses
        every `except Exception` in the suite and silently truncates the run. This
        asserts there is none outside a `if __name__ == "__main__"` guard, across every
        `scripts/*.py` module the check package imports.

        Measured when written: exactly one violation (`atlas_view.load_lean_deps_file`,
        fixed) and one correct site (`graph_integrity.main`, inside `main()`, which no
        check calls)."""
        import ast
        import re as _re
        scripts_dir = Path(__file__).resolve().parent.parent / "scripts"
        imported: set = set()
        for f in (scripts_dir / "validation" / "checks").glob("*.py"):
            for m in _re.finditer(r"^\s*(?:import|from)\s+([A-Za-z_][\w.]*)",
                                  f.read_text(), _re.M):
                imported.add(m.group(1).split(".")[0])

        offenders: list[str] = []
        for name in sorted(imported):
            p = scripts_dir / f"{name}.py"
            if not p.is_file():
                continue
            tree = ast.parse(p.read_text())
            guards = [(n.lineno, n.end_lineno) for n in ast.walk(tree)
                      if isinstance(n, ast.If) and "__name__" in ast.unparse(n.test)]
            # A `main()`-only exit is the CLI boundary and is correct; only flag sites a
            # check could reach.
            mains = [(n.lineno, n.end_lineno) for n in ast.walk(tree)
                     if isinstance(n, ast.FunctionDef) and n.name == "main"]
            def _inside(ln, spans):
                return any(a <= ln <= b for a, b in spans)
            for n in ast.walk(tree):
                bad = (isinstance(n, ast.Raise) and n.exc is not None
                       and "SystemExit" in ast.unparse(n.exc)) or (
                      isinstance(n, ast.Call)
                      and ast.unparse(n.func) in ("sys.exit", "exit"))
                if bad and not _inside(n.lineno, guards) and not _inside(n.lineno, mains):
                    offenders.append(f"{name}.py:{n.lineno}")
        assert not offenders, (
            f"SystemExit/sys.exit reachable from a check: {offenders}. These bypass "
            f"`except Exception` in both check_* and validate.run_checks and truncate "
            f"the suite silently — raise a normal exception and convert at the CLI.")


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
        assert _count_in(msg, "gate >=1 downstream theorem") == 1
        assert _count_in(msg, "orphan") == 1

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


class TestInferBundleFromTextIsActuallyTested:
    """⚠️ PR-review pass 2, R2-MAJ3 — the sharpest coverage finding of the pass.

    `_infer_bundle_from_text` appeared in `tests/` ONLY as a monkeypatch target
    (`lambda t: t`), i.e. every test that touched it replaced it. R2 restored the
    genuine historical regression verbatim — `D\\d{1,2}` narrowed back to `D[1-9]`,
    the bug that made 'D12' match as 'D1' — and the full suite returned **5,482
    passed, byte-identical to baseline.**

    That bug was not hypothetical. Per this module's own comment block: with no
    bundle resolved, the paper-key text matcher fired instead and minted **FALSE
    `FLAGS` edges** — a D11 finding attributed to `paper18_doublon_gate`, a D12
    finding to `paper3_` — and D12 rendered "Blockers 0" while carrying 36 open
    findings.

    So: every registered check (80 today) is protected against deletion, and the one regression
    that actually happened was invisible. These tests close that.
    """

    def _infer(self, name):
        return build_graph._infer_bundle_from_text(name)

    def test_two_digit_bundles_do_not_truncate(self):
        """FIRES ON THE HISTORICAL REGRESSION. Narrow the pattern to `D[1-9]` and
        'D12' resolves to 'D1' — findings land on the wrong bundle."""
        assert self._infer("D12.md") == "D12"
        assert self._infer("D11_r2.md") == "D11"
        assert self._infer("D10-figures.md") == "D10"

    def test_single_digit_bundles_still_resolve(self):
        """SILENT ON CORRECT DATA — the greedy fix must not break the common case."""
        assert self._infer("D1.md") == "D1"
        assert self._infer("D2_r1.md") == "D2"
        assert self._infer("D9.md") == "D9"

    def test_non_D_rosters_resolve(self):
        for stem, want in [("F_r1.md", "F"), ("I1-figures.md", "I1"),
                           ("L3.md", "L3"), ("E2_r1.md", "E2")]:
            assert self._infer(stem) == want, stem

    def test_a_code_outside_the_roster_is_REJECTED_not_invented(self):
        """The roster check is what makes `\\d{1,2}` safe: a widened numeric
        pattern must not be able to invent bundles."""
        assert self._infer("D99.md") is None
        assert self._infer("D0.md") is None

    def test_a_legacy_paper_name_does_not_match(self):
        """Older reviews are `paperN_slug.md` and must fall through to the
        paper-key matcher — matching them here is how a finding gets attributed
        to a bundle it has nothing to do with."""
        assert self._infer("paper18_doublon_gate.md") is None
        assert self._infer("phase6x_item_G.md") is None

    def test_the_boundary_is_enforced(self):
        """`(?=$|[-_.])` — 'D1abc' is not bundle D1."""
        assert self._infer("D1abc.md") is None
        assert self._infer("Ffoo.md") is None


class TestGraphClassifiesAutogenStructurally:
    """The graph's declaration and module extractors decide compiler-generated the same
    way the atlas and `validate.py` do — through `validate_helpers.autogen_index`, which
    reads Lean's `autogen` field plus a PARENT-KIND-GUARDED suffix supplement.

    The population is one population; three instruments disagreeing about it is how a
    figure the human reviewer reads drifts from the figure a check ratchets on.

    Measured at the swap over the live corpus: the graph's own name regex kept **270**
    compiler-generated declarations the shared index rejects, and the change adds back
    **zero** author-written declarations — the new drop set is a strict superset, which
    is the safest shape a classifier swap can have.
    """

    def _autogen(self, corpus):
        import sys as _sys
        _sys.path.insert(0, str(SK_ROOT / "scripts"))
        from validate_helpers import autogen_index
        return autogen_index(corpus)

    def test_a_derived_instance_field_is_generated(self):
        """`deriving Repr` emits `instReprFoo.repr`, whose parent is the INSTANCE — the
        inductive/structure guard cannot reach it, so it has its own branch."""
        corpus = [{"name": "SKEFTHawking.Foo.instReprFoo.repr", "kind": "def"},
                  {"name": "SKEFTHawking.Foo.instReprFoo", "kind": "instance"}]
        assert self._autogen(corpus)["SKEFTHawking.Foo.instReprFoo.repr"] is True

    def test_an_author_written_declaration_named_like_a_companion_SURVIVES(self):
        """FIRES ON THE SEEDED DEFECT: replace the parent-kind guard with a bare suffix
        match and this author-written `inj` disappears from the graph.

        `inj`, `ofNat`, `repr` and `decEq` are ordinary mathematical names as well as
        Lean companion names. Only the parent's kind tells the two apart.
        """
        corpus = [{"name": "SKEFTHawking.Sheaf.restriction.inj", "kind": "theorem"},
                  {"name": "SKEFTHawking.Sheaf.restriction", "kind": "def"}]
        assert self._autogen(corpus)["SKEFTHawking.Sheaf.restriction.inj"] is False

    def test_the_same_leaf_on_a_structure_parent_is_generated(self):
        """SILENT ON CORRECT DATA — the guard must not blind the filter either."""
        corpus = [{"name": "SKEFTHawking.GapParams.mk.inj", "kind": "theorem"},
                  {"name": "SKEFTHawking.GapParams", "kind": "structure"}]
        assert self._autogen(corpus)["SKEFTHawking.GapParams.mk.inj"] is True

    def test_the_graph_holds_no_private_name_regex_for_this(self):
        """The regex is gone, not merely unused — a dormant one invites a caller back."""
        import build_graph
        assert not hasattr(build_graph, "_AUTOGEN_SHORT_RE"), (
            "build_graph re-declares a name-shape autogen regex; classification belongs "
            "to validate_helpers.autogen_index so all three instruments agree")


def build_graph_atlas_is_obstruction(rec):
    """Reach the production predicate through its owning module."""
    import atlas_view
    # Exercise the PRODUCTION classification path, not a stand-in for it.
    #
    # A real record carries `autogen` from ExtractDeps (Lean's own predicates), and the
    # reserved-suffix residue Lean's public predicates miss (`ctorIdx`,
    # `noConfusionType`, `sizeOf_spec`) is resolved by `autogen_index`, which needs the
    # PARENT's kind. So build the minimal corpus that gives it one: the declaration plus
    # its parent as an inductive — which is what the tree actually looks like.
    import sys as _sys
    _sys.path.insert(0, str(SK_ROOT / "scripts"))
    from validate_helpers import autogen_index  # noqa: E402
    name = rec.get("name", "")
    parent = name.rsplit(".", 1)[0] if "." in name else name
    corpus = [rec, {"name": parent, "kind": "inductive"}]
    return atlas_view._is_obstruction(rec, autogen_index(corpus))


class TestAutogenIsNotAnObstruction:
    """⚠️ PR-review pass 2, R6-M1. `_is_obstruction` tests a FULLY QUALIFIED name,
    so anything inside a namespace like `DarkEnergyObstructionPrinciple` matched on
    its namespace — including Lean-synthesised artifacts.

    Measured at the fix: **577** declarations classified OBSTRUCTION; 284 justified
    by the leaf name or a negated type; 293 by namespace alone, of which **68 were
    auto-generated** (44 `def`, 24 `theorem`). Those were being ranked on the atlas
    NEGATIVE FRONTIER — the view a `/goal` loop reads to steer away from dead paths.

    ⚠️ This count has been measured four times across two review passes (pass 1:
    29 from 3 modules; the lead's re-count: same; R6: 144 from 14; here: 577/293/68).
    They disagree because each used a different predicate, not because the data
    moved. Assert against the predicate, and state it.
    """

    def _rec(self, name, module="SKEFTHawking.Foo", typ="Prop", kind="theorem"):
        return {"name": name, "module": module, "type": typ, "kind": kind}

    def test_structure_eliminators_in_a_nogo_namespace_are_NOT_obstructions(self):
        """FIRES ON THE SEEDED DEFECT: drop the `_AUTOGEN_RE` guard and these are
        classified as mathematical obstructions."""
        ns = "SKEFTHawking.DarkEnergyObstructionPrinciple"
        for leaf in ("EmergentDarkEnergyModel.casesOn",
                     "EmergentDarkEnergyModel.ctorIdx",
                     "EmergentDarkEnergyModel.recOn",
                     "H_Something_falsified.match_1_1"):
            rec = self._rec(f"{ns}.{leaf}", module=ns)
            assert build_graph_atlas_is_obstruction(rec) is False, (
                f"{leaf} classified as an OBSTRUCTION — it is a Lean-synthesised "
                f"artifact, not a mathematical claim")

    def test_a_REAL_nogo_declaration_is_still_an_obstruction(self):
        """SILENT ON CORRECT DATA — the exclusion must not blind the frontier."""
        rec = self._rec("SKEFTHawking.SoftTheorems.DissipativeNoGo.dissipative_no_go",
                        module="SKEFTHawking.SoftTheorems.DissipativeNoGo")
        assert build_graph_atlas_is_obstruction(rec) is True

    def test_a_negated_type_is_still_an_obstruction(self):
        rec = self._rec("SKEFTHawking.Foo.some_lemma", typ="¬ P")
        assert build_graph_atlas_is_obstruction(rec) is True

    def test_an_ordinary_theorem_is_not(self):
        assert build_graph_atlas_is_obstruction(self._rec("SKEFTHawking.Foo.bar")) is False
