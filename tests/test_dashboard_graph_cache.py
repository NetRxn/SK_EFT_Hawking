"""Guards for the dashboard graph cache's staleness key.

WHAT THEY PROTECT
-----------------
`_graph_fingerprint` decides when the dashboard rebuilds its graph. The graph
embeds a ReviewFinding node per finding and applies the supersession ledger's
status overrides, so filing a finding — or closing one through
`close_finding.py` — must invalidate the cache. A key that misses an input fails
silently and in the green direction: the dashboard serves a pre-change finding
set with nothing to indicate it.

⛔ The key must stay derived from what the build actually reads. A hand-listed
set of inputs is correct only until someone adds one.

WHY MOST OF THESE ASSERT THE KEY AND ONE ASSERTS THE CACHE
----------------------------------------------------------
A full rebuild is ~7.4 s, so proving every invalidation end-to-end would cost a
minute. Asserting "the fingerprint moved" is, strictly, asserting a PROXY for
"the cache rebuilds" — so exactly one test
(`test_a_newly_filed_finding_reaches_the_dashboard_graph`) goes the whole way
through `get_cached_graph` and requires the node to appear in the served graph.
That one covers the seam; the rest are cheap assertions on the key it depends
on. Deleting the end-to-end test would leave the others provable by a
fingerprint that nothing consumes.
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

PROJECT_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PROJECT_ROOT / "scripts"))

import provenance_dashboard as pd  # noqa: E402

REVIEWS = PROJECT_ROOT / "papers" / "AutomatedReviews"
LEDGER = PROJECT_ROOT / "docs" / "review_finding_supersessions.json"


@pytest.fixture(scope="module")
def warmed():
    """One real build, so a read set exists. Everything else keys off it."""
    pd.app.config["PG_SYNC_ENABLED"] = False
    pd.get_cached_graph(sync_pg=False)
    assert pd._READ_SET["paths"], "no read set was captured — nothing below is meaningful"
    return pd._graph_fingerprint()


class TestTheKeyCoversTheReviewCorpus:
    """The specific inputs the old hand-listed key missed."""

    def test_the_review_corpus_is_in_the_watched_read_set(self, warmed):
        watched = pd._READ_SET["paths"]
        assert any("AutomatedReviews" in p for p in watched), (
            "no review document is watched — this is the original defect")
        assert any("review_finding_supersessions" in p for p in watched), (
            "the supersession ledger is not watched — closing a finding would "
            "not invalidate the cache")

    def test_editing_a_review_document_moves_the_key(self, warmed):
        before = pd._graph_fingerprint()          # NOT `warmed` — see the note below
        sorted(REVIEWS.glob("*/*.md"))[-1].touch()
        assert pd._graph_fingerprint() != before

    def test_editing_the_ledger_moves_the_key(self, warmed):
        before = pd._graph_fingerprint()
        LEDGER.touch()
        assert pd._graph_fingerprint() != before


class TestTheKeyCoversFilesThatDoNotExistYet:
    """The ancestor-directory leg.

    ⛔ Watching each read file's IMMEDIATE parent is not enough: findings live in
    `papers/AutomatedReviews/<date>/*.md`, so the immediate parents are the
    `<date>` directories and `papers/AutomatedReviews/` itself goes unwatched —
    leaving a brand-new `<date>/`, which is what filing a finding creates,
    invalidating nothing.
    """

    def test_the_corpus_root_itself_is_watched(self, warmed):
        assert str(REVIEWS) in pd._READ_SET["dirs"], (
            "papers/AutomatedReviews/ is not watched as a directory, so a newly "
            "filed finding in a new dated subdirectory cannot move the key")

    def test_creating_a_new_finding_directory_moves_the_key(self, warmed):
        """⛔ Take the baseline HERE, never from the module-scoped `warmed`.

        Earlier tests in this file touch files, so `warmed` has already moved for
        reasons of its own and an assertion against it holds no matter what this
        test did — green even under the immediate-parent-only defect it exists to
        catch. Only a baseline captured immediately before the change attributes
        the movement to the change.
        """
        from seed_journal import seeded_directory
        before = pd._graph_fingerprint()
        with seeded_directory(REVIEWS / "2026-08-14-key-coverage-probe",
                              reason="a new dated review directory must move the "
                                     "dashboard's graph key"):
            assert pd._graph_fingerprint() != before, (
                "a new dated directory did not move the key — paths alone cannot "
                "see a file that did not exist at the last build")


class TestTheCacheStillCaches:
    """Non-vacuity in the other direction: a key that never matches would pass
    every test above and make the cache useless."""

    def test_an_unchanged_tree_keeps_the_key_stable(self, warmed):
        assert pd._graph_fingerprint() == pd._graph_fingerprint()

    def test_an_unchanged_tree_serves_the_cached_object(self, warmed):
        first = pd.get_cached_graph(sync_pg=False)
        second = pd.get_cached_graph(sync_pg=False)
        assert first is second, "the cache rebuilt although nothing changed"


class TestTheFailSafeDirection:

    def test_no_read_set_yields_a_key_that_cannot_match(self, warmed):
        """Before the first build, and after any unrecordable or raced build.

        ⚠️ Must not be `None`: `_GRAPH_CACHE['fingerprint']` is initialised to
        `None`, so a `None` key would compare equal to an empty cache and turn
        the cold-start miss into a hit.
        """
        saved = pd._READ_SET["paths"], pd._READ_SET["dirs"]
        pd._READ_SET["paths"], pd._READ_SET["dirs"] = None, None
        try:
            a, b = pd._graph_fingerprint(), pd._graph_fingerprint()
            assert a != b, "the no-read-set key matched itself — the cold cache would hit"
            assert a is not None and b is not None
        finally:
            pd._READ_SET["paths"], pd._READ_SET["dirs"] = saved


class TestTheSeam:
    """The one end-to-end proof, through the real consumer."""

    def test_a_newly_filed_finding_reaches_the_dashboard_graph(self, warmed):
        """PRODUCTION-SEEDED. Writes a real review document, then requires the
        graph the dashboard SERVES to contain its node — not merely that a
        fingerprint moved."""
        import build_graph as bg
        from seed_journal import SEED_MARKER, seeded_artifact

        before = pd.get_cached_graph(sync_pg=False)
        expected = bg.mint_finding_id("2026-08-14-seam-probe", "infra", "1")
        with seeded_artifact(
                REVIEWS / "2026-08-14-seam-probe" / "infra.md",
                "# Seam probe\n\n### 1 — probe finding\n\n"
                "- **Severity:** minor\n- **Lane:** infra\n"
                "- **Observed:** seeded by tests/test_dashboard_graph_cache.py "
                f"<!-- {SEED_MARKER} -->\n",
                reason="a newly filed finding must reach the graph the dashboard SERVES"):
            after = pd.get_cached_graph(sync_pg=False)
            assert after is not before, "the dashboard served its cached graph"
            assert expected in {n["id"] for n in after["nodes"]}, (
                "a finding was filed and the dashboard's graph does not contain it")
        restored = pd.get_cached_graph(sync_pg=False)
        assert expected not in {n["id"] for n in restored["nodes"]}


def _exercise_flow_request_in_fresh_process(scratch, *, warm):
    """Real route/cache/board/aggregate; only corpus producers use temporary inputs.

    Called in a fresh interpreter, so collection order cannot pre-import Flow's readers.
    No production graph build, PG scheduling, source seed or artifact repair occurs here.
    """
    import copy
    import importlib
    import json
    from unittest.mock import patch
    import build_graph as bg
    import readiness_gates as rg

    assert "dashboard_flow" not in sys.modules
    scratch = Path(scratch)
    papers = scratch / "papers"
    for code in ("X1", "X2"):
        (papers / code).mkdir(parents=True)
        (papers / code / "bundle_metadata.json").write_text(json.dumps({"stage9_status": "pending-redo"}))
    findings = [{"id": f"review:f{i}", "type": "ReviewFinding", "label": f"finding {i}",
                 "meta": {"status": "open", "severity": "minor", "lane": "unclassified",
                          "inferred_bundle": "X1"}} for i in range(12)]
    findings.append({"id": "review:unattributed", "type": "ReviewFinding", "label": "unattributed",
                     "meta": {"status": "open", "severity": "major", "lane": "infra"}})
    graph = {"nodes": [{"id": f"paper:{c}", "type": "Paper", "meta": {}} for c in ("X1", "X2")]
                      + findings + [rg.GateResult(gate="Fixture", paper=c, priority=1,
                                                  state="passed").to_node_payload()
                                    for c in ("X1", "X2", "outside-roster")],
             "links": [{"source": "review:f0", "target": "paper:X1", "type": "FLAGS"}]}
    original = copy.deepcopy(graph)
    builds, claims, aggregates, evaluations, boards, gate_inputs, fallback = [], [], [], [], [], [], []
    real_claims = pd.load_paper_claims
    def claims_spy(*args, **kwargs):
        claims.append(kwargs.get("graph"))
        return real_claims(*args, **kwargs)
    def builder(*args, **kwargs):
        # The real builder imports this registry in extract_source_nodes. Retain that
        # dependency even though the fixture replaces the expensive corpus build.
        from src.core.citations import CITATION_REGISTRY
        assert CITATION_REGISTRY
        # Captured read set remains real; this owned source is read, never changed here.
        (PROJECT_ROOT / "scripts" / "dashboard_flow.py").read_text()
        builds.append(dict(kwargs))
        return graph
    real_evaluate = rg.evaluate_all_gates
    def evaluate(g):
        evaluations.append(g)
        return real_evaluate(g)
    real_import = importlib.import_module
    configured = False
    stack = __import__('contextlib').ExitStack()
    def set_attr(obj, name, value):
        stack.enter_context(patch.object(obj, name, value))
    def import_pane(name, *args, **kwargs):
        nonlocal configured
        module = real_import(name, *args, **kwargs)
        if name == "dashboard_flow" and not configured:
            configured = True
            import bundle_readiness as br
            import check_bundle_source_freshness as fresh
            from validation.checks import bundles_readiness as checks
            set_attr(module, "PAPERS_DIR", papers)
            set_attr(module, "BUNDLE_CODES", ("X1", "X2"))
            set_attr(module, "parse_mapping", lambda text: {})
            set_attr(br, "PAPERS_DIR", papers)
            set_attr(br, "_VALID_BUNDLE_TARGETS", ("X1", "X2"))
            set_attr(br, "resolve_stage13_reviews", lambda **kw: {})
            set_attr(br, "load_findings_by_paper", lambda: {"X1": [
                {"id": n["id"], "label": n["label"], "status": "open", "severity": "minor",
                 "gate": "fixture"} for n in findings[:-1]]})
            set_attr(fresh, "check", lambda **kw: [{"bundle": "X1", "passed": True,
                "warning": False, "message": "fixture unmeasured", "measured": False}])
            set_attr(fresh, "_registered_lean_modules", lambda code: [])
            set_attr(checks, "_measure_manuscript", lambda code: (None, "pages", "fixture unmeasured"))
            real_aggregate = br.aggregate_by_bundle
            def aggregate(*args, **kwargs):
                aggregates.append(kwargs.get("graph"))
                return real_aggregate(*args, **kwargs)
            set_attr(br, "aggregate_by_bundle", aggregate)
            real_board = module.flow_board
            def board(**kwargs):
                gate_inputs.append(kwargs.get("gate_nodes"))
                out = real_board(**kwargs)
                boards.append(out)
                return out
            set_attr(module, "flow_board", board)
            real_fallback = module.load_gate_nodes
            def gates():
                fallback.append(True)
                return real_fallback()
            set_attr(module, "load_gate_nodes", gates)
        return module
    with stack:
        set_attr(bg, "build_graph_json", builder)
        set_attr(bg, "extract_review_finding_nodes", lambda: findings)
        set_attr(pd, "load_paper_claims", claims_spy)
        set_attr(rg, "evaluate_all_gates", evaluate)
        set_attr(rg, "GATES", [("FixPropagation", 2, rg._eval_fix_propagation)])
        set_attr(importlib, "import_module", import_pane)
        pd.app.config.update(TESTING=True, PG_SYNC_ENABLED=False)
        def no_sync(*args):
            raise AssertionError("PG scheduling must be disabled in route tests")
        set_attr(pd, "_schedule_pg_sync", no_sync)
        client = pd.app.test_client()
        if warm:
            assert client.get('/').status_code == 200
            assert len(builds) == 1
        before = len(builds)
        observations = []
        for _ in range(2):
            response = client.get('/?tab=flow')
            html = response.get_data(as_text=True)
            cached_key = pd._GRAPH_CACHE['fingerprint']
            current_key = pd._graph_fingerprint()
            observations.append({'builds': len(builds), 'added_key_entries': [
                str(e) for e in current_key if e not in cached_key]})
            assert response.status_code == 200
            assert 'failed to build the flow pane' not in html
            assert 'class="flow-cell flow-not-tracked"' in html
            assert 'class="flow-cell flow-undeclared"' in html
            assert 'class="flow-cell flow-unmeasured"' in html
            assert 'TODO-D50' in html and 'TODO-D51' in html
            assert 'class="data-table flow-coverage"' in html
        assert len(builds) == before + 1, f"graph builds: {builds!r}; observations: {observations!r}"
        assert fallback == [], "Flow used its standalone gate fallback"
        assert all(g is graph for g in claims[-2:])
        assert len(aggregates) == 2 and all(g is graph for g in aggregates)
        assert len(evaluations) == 2 and all(g is graph for g in evaluations)
        expected = [n for n in graph['nodes'] if n['type'] == 'ReadinessGate']
        assert len(expected) == 3  # Includes a gate outside the controlled row roster.
        assert len(gate_inputs) == 2
        for supplied in gate_inputs:
            assert supplied == expected
            assert all(a is b for a, b in zip(supplied, expected))
        for board in boards:
            assert [r['bundle'] for r in board['rows']] == ['X1', 'X2']
            assert board['rows'][0]['overlay']['open_total'] == 12
            assert board['coverage']['open_findings'] == 13
            assert board['coverage']['attributed_to_a_row'] == 12
            assert board['coverage']['carry_no_bundle_or_paper_key'] == 1
            assert board['coverage']['attributed_with_no_declared_lane'] == 12
            assert board['rows'][0]['overlay']['unclassified'] == 12
        assert graph == original
        assert pd._GRAPH_CACHE['fingerprint'] == pd._graph_fingerprint()
        print(json.dumps({'warm': warm, 'builds': len(builds), 'fallbacks': len(fallback),
                          'aggregate_calls': len(aggregates), 'gate_population': len(expected),
                          'fingerprint_stable': True}))


@pytest.mark.parametrize("warm", [False, True], ids=["first-flow", "warm-then-flow"])
def test_flow_request_reuses_full_graph_in_fresh_process(tmp_path, warm):
    import os
    import subprocess
    source = Path(__file__).resolve()
    code = ("import runpy; from pathlib import Path; "
            f"ns=runpy.run_path({str(source)!r}); "
            f"ns['_exercise_flow_request_in_fresh_process'](Path({str(tmp_path)!r}), warm={warm!r})")
    result = subprocess.run([sys.executable, '-B', '-c', code], cwd=PROJECT_ROOT,
                            env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'},
                            text=True, capture_output=True)
    assert result.returncode == 0, result.stdout + result.stderr
    assert '"fingerprint_stable": true' in result.stdout
    print(result.stdout)


class TestIsolatedGraphCachePolicy:
    """Actual cache/keys with a temporary read set; no live builds or source seeds."""

    @pytest.fixture
    def cache(self, monkeypatch, tmp_path):
        import build_graph
        data = tmp_path / 'ledger.json'
        data.write_text('{}')
        graph = {'nodes': [], 'links': []}
        builds, schedules = [], []
        def build(*, sync_pg):
            assert sync_pg is False
            data.read_text()
            builds.append(True)
            return graph
        monkeypatch.setattr(build_graph, 'build_graph_json', build)
        monkeypatch.setattr(pd, '_GRAPH_CACHE', {'graph': None, 'fingerprint': None, 'built_at': None})
        monkeypatch.setattr(pd, '_READ_SET', {'paths': None, 'dirs': None})
        monkeypatch.setattr(pd, '_schedule_pg_sync', lambda g, fp: schedules.append((g, fp)))
        monkeypatch.setitem(pd.app.config, 'PG_SYNC_ENABLED', False)
        return graph, data, builds, schedules

    @pytest.mark.parametrize('enabled', [False, True])
    def test_configured_pg_policy_only_schedules_after_rebuild(self, cache, monkeypatch, enabled):
        graph, _, builds, schedules = cache
        monkeypatch.setitem(pd.app.config, 'PG_SYNC_ENABLED', enabled)
        assert pd.get_cached_graph() is graph
        assert pd.get_cached_graph() is graph
        assert len(builds) == 1
        assert len(schedules) == int(enabled)
        if enabled:
            assert schedules[0][0] is graph
        pd.get_cached_graph(force_rebuild=True, sync_pg=False)
        assert len(builds) == 2
        assert len(schedules) == int(enabled)

    def test_data_directory_and_code_changes_rebuild_served_graph(self, cache, monkeypatch, tmp_path):
        import types
        graph, data, builds, _ = cache
        # Let the real imported-module observer see a temporary repository module.
        monkeypatch.setattr(pd, 'PROJECT_ROOT', tmp_path)
        assert pd.get_cached_graph() is graph
        assert len(builds) == 1
        data.write_text('{"closed": true}')
        assert pd.get_cached_graph() is graph
        assert len(builds) == 2
        (tmp_path / 'new-review-directory').mkdir()
        assert pd.get_cached_graph() is graph
        assert len(builds) == 3
        source = tmp_path / 'reader.py'
        source.write_text('VALUE = 1\n')
        pd.get_cached_graph()  # Directory creation is an independent invalidation.
        before_import = len(builds)
        module = types.ModuleType('isolated_flow_reader')
        module.__file__ = str(source)
        monkeypatch.setitem(sys.modules, module.__name__, module)
        assert str(source) in pd._loaded_repo_module_sources()
        assert pd.get_cached_graph() is graph
        assert len(builds) == before_import + 1
        source.write_text('VALUE = 22\n')
        assert pd.get_cached_graph() is graph
        assert len(builds) == before_import + 2
        assert pd.get_cached_graph() is graph
        assert len(builds) == before_import + 2

    def test_missing_readset_and_unlistable_directory_force_misses(self, cache, monkeypatch):
        graph, data, builds, _ = cache
        pd.get_cached_graph()
        pd._READ_SET['paths'] = None
        pd.get_cached_graph()
        assert len(builds) == 2
        real_listdir = pd.os.listdir
        def unlistable(path):
            if str(path) == str(data.parent):
                raise OSError('controlled directory observation failure')
            return real_listdir(path)
        monkeypatch.setattr(pd.os, 'listdir', unlistable)
        assert pd.get_cached_graph() is graph
        assert pd.get_cached_graph() is graph
        assert len(builds) == 4
