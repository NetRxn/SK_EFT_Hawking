"""Guards for the within-build extractor memo (`build_graph._BUILD_MEMO_TLS`).

WHAT THESE PROTECT, AND WHY IT IS NOT THE OBVIOUS THING
-------------------------------------------------------
The memo exists for speed — measured 2026-08-14, it takes `build_graph_json()`
from 14.4 s to 7.1 s by deriving each argument-free extractor once per build
instead of the up-to-eight times a build otherwise calls them. Speed is not what
these tests guard.

The hazard is that a caching layer over a derivation can make a **seeded
mutation invisible**. A large family of this repo's tests writes a defect into a
production artifact and asserts the dependent check turns red; if a cache
answered the post-seeding read from a pre-seeding snapshot, those tests would
pass FOR THE WRONG REASON. That failure is silent — a check that cannot fire is
indistinguishable from a check that found nothing — which is why the guard has
to seed the real corpus rather than a fixture.

⚠️ `test_a_finding_seeded_into_the_REAL_corpus_is_visible_to_the_next_build` is
the load-bearing one. It writes an actual review document into
`papers/AutomatedReviews/`, builds, and requires the node to appear. Every other
test here can be satisfied by a memo that is merely well-behaved in-process;
only this one fails if the memo ever outlives a build.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

PROJECT_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PROJECT_ROOT / "scripts"))

import build_graph as bg  # noqa: E402

#: Fields that legitimately differ between two builds a second apart. Verified
#: by running two *unmemoized* builds against each other: 704 gate nodes
#: differed and `last_evaluated` was the sole differing key. Normalising these is
#: therefore not weakening the comparison — without it the test would assert a
#: property the code never had.
#:
#: ⛔ NORMALISE ONLY THESE TWO. In particular do not add `last_modified`:
#: `scripts/last_modified.py` propagates it UP DEPENDENCY EDGES, so a defect that
#: changed the edge set or fed an assembly site a stale upstream node surfaces
#: there and almost nowhere else in a whole-graph comparison. Blanking a field
#: that does not vary is not harmless caution — it deletes the comparison's most
#: sensitive signal.
_VOLATILE = {"built_at", "last_evaluated"}


def _normalise(obj):
    if isinstance(obj, dict):
        return {k: ("<TS>" if k in _VOLATILE else _normalise(v)) for k, v in obj.items()}
    if isinstance(obj, list):
        return [_normalise(v) for v in obj]
    return obj


def _canonical(graph) -> str:
    return json.dumps(_normalise(graph), sort_keys=True, default=str)


@pytest.fixture
def tmp_probe():
    """A real (initially empty) review directory in the real corpus.

    Swept unconditionally, including any file a failing test left behind, so a
    probe finding can never become part of the corpus the ratchets count.
    """
    import shutil
    probe_dir = PROJECT_ROOT / "papers" / "AutomatedReviews" / "2026-08-14-live-state-probe"
    shutil.rmtree(probe_dir, ignore_errors=True)
    probe_dir.mkdir(parents=True)
    try:
        yield probe_dir, bg.mint_finding_id(probe_dir.name, "infra", "1")
    finally:
        shutil.rmtree(probe_dir, ignore_errors=True)


class TestTheMemoIsPerThread:
    """The memo must be per-thread, and only a concurrency test can show it.

    `_build_memo_scope` save/restores, which is right for nesting on one stack and
    wrong for a global shared across threads: A installs `{}`; B sees a non-None
    outer and shares A's memo; A exits restoring `None`; B exits restoring A's
    dict — leaving a memo installed with no build running, after which every later
    extractor call in the process is served from A's snapshot.

    Concurrency is reachable here: the dashboard runs Flask `threaded=True`, and
    `dashboard_flow.py` and `bundle_readiness.py` both call `build_graph_json()`
    holding no lock.
    """

    def test_two_interleaved_scopes_do_not_leave_a_memo_installed(self):
        import threading
        a_entered = threading.Event()
        b_entered = threading.Event()
        a_exited = threading.Event()
        failures: list[str] = []

        def thread_a():
            with bg._build_memo_scope():
                bg.extract_review_finding_nodes()
                a_entered.set()
                b_entered.wait(timeout=10)
            a_exited.set()
            if bg._current_build_memo() is not None:
                failures.append("A's memo survived A's scope")

        def thread_b():
            a_entered.wait(timeout=10)
            with bg._build_memo_scope():
                if bg._current_build_memo() is None:
                    failures.append("B got no memo of its own")
                b_entered.set()
                a_exited.wait(timeout=10)
            if bg._current_build_memo() is not None:
                failures.append("a memo is installed on B with no build running")

        ta, tb = threading.Thread(target=thread_a), threading.Thread(target=thread_b)
        ta.start(); tb.start(); ta.join(15); tb.join(15)
        assert not failures, failures
        assert bg._current_build_memo() is None

    def test_one_threads_scope_is_invisible_to_another(self):
        import threading
        seen: list[object] = []

        def observer():
            seen.append(bg._current_build_memo())

        with bg._build_memo_scope():
            bg.extract_review_finding_nodes()
            assert bg._current_build_memo() is not None
            t = threading.Thread(target=observer); t.start(); t.join(10)
        assert seen == [None], (
            f"another thread saw this build's memo ({seen!r}) — it is not thread-local, "
            f"so its entries can be served to a caller with no build on its stack")


class TestTheMemoCannotOutliveABuild:
    """The whole safety argument is the memo's lifetime. These pin it."""

    def test_the_memo_is_drained_at_rest(self):
        assert bg._current_build_memo() is None, (
            "the memo must be None outside a build — a non-None value at rest means "
            "some path enabled it without a scope to tear it down")

    def test_the_memo_is_drained_after_a_build(self):
        bg.build_graph_json(sync_pg=False)
        assert bg._current_build_memo() is None

    def test_an_extractor_called_outside_a_build_reads_LIVE_state(self, tmp_probe):
        """Direct callers must always read live state.

        `bundle_readiness.load_findings_by_paper` calls
        `extract_review_finding_nodes` with no build in progress. If the memo
        were process-scoped, that call would replay whatever the last build saw.

        ⛔ ASSERT LIVENESS, NOT IDENTITY. `first is not second` is vacuous here:
        the wrapper deepcopies on every hit, so two calls are never the same
        object whatever the memo's scope, and the assertion stays green while a
        process-lifetime memo serves a stale snapshot. Seed the real corpus and
        assert the content moves.
        """
        from seed_journal import SEED_MARKER, seeded_artifact
        assert bg._current_build_memo() is None
        probe_dir, expected_id = tmp_probe

        bg.build_graph_json(sync_pg=False)   # give a process-wide memo a chance to fill

        doc = probe_dir / "infra.md"
        with seeded_artifact(
                doc,
                "# probe\n\n### 1 — probe\n\n- **Severity:** minor\n- **Lane:** infra\n"
                f"<!-- {SEED_MARKER} -->\n",
                reason="a direct extractor call must see a finding written after the "
                       "last build"):
            assert expected_id in {n["id"] for n in bg.extract_review_finding_nodes()}, (
                "a direct extractor call did not see a finding written after the last "
                "build — the memo is outliving its build")

        assert expected_id not in {n["id"] for n in bg.extract_review_finding_nodes()}, (
            "a direct extractor call still reports a deleted finding")

    def test_a_nested_build_does_not_tear_down_the_outer_memo(self):
        with bg._build_memo_scope():
            bg.extract_review_finding_nodes()
            assert bg._current_build_memo() is not None
            with bg._build_memo_scope():
                pass
            assert bg._current_build_memo() is not None, (
                "an inner scope exiting must not drain the outer build's memo")
        assert bg._current_build_memo() is None


class TestTheMemoIsSemanticallyInvisible:

    def test_the_memoized_build_equals_the_unmemoized_build(self):
        """The only assertion that covers the whole graph at once.

        `_build_graph_json_uncached` never enables the memo, so it is exactly
        the pre-memo behaviour — this compares the change against the code it
        replaced rather than against an expectation written by hand.

        ⚠️ REQUIRES A QUIET TREE, and observed failing without one. It builds the
        graph twice and compares; a *concurrent* pytest process seeding a
        production artifact between the two builds makes them legitimately
        differ, and the failure looks exactly like a memo defect. That is not a
        weakness peculiar to this test — the seeded-mutation family is
        inherently non-parallel-safe against a shared working tree — but this is
        the test most likely to surface it, so the cause is named here.
        """
        memoized = bg.build_graph_json(sync_pg=False)
        plain = bg._build_graph_json_uncached(sync_pg=False)
        assert len(memoized["nodes"]) == len(plain["nodes"])
        assert len(memoized["links"]) == len(plain["links"])
        assert _canonical(memoized) == _canonical(plain)

    def test_the_memo_hands_out_copies(self):
        """Two assembly sites hold their results independently.

        `extract_all_nodes` builds the real node list while
        `extract_readiness_gate_nodes` builds a separate pre-gate view, and
        `_overlay_atlas` / `_overlay_closure` then annotate nodes IN PLACE. If
        the memo returned one shared list, an overlay applied through one view
        would appear in the other.
        """
        with bg._build_memo_scope():
            first = bg.extract_review_finding_nodes()
            assert first, "corpus is empty — this test would be vacuous"
            first[0]["meta"]["seeded_by_test"] = True
            first.append({"id": "node-appended-by-test"})

            second = bg.extract_review_finding_nodes()
            assert second is not first
            assert "seeded_by_test" not in second[0]["meta"], (
                "mutating one caller's result leaked into another's — the memo is "
                "handing out shared objects")
            assert not any(n["id"] == "node-appended-by-test" for n in second)


class TestTheDocumentedClaimStaysTrue:
    """Two-way pin, per the house rule for load-bearing prose.

    Asserts the sentence is still in the document AND the code fact behind it.
    Rewording the doc breaks this (forcing a re-verification); widening the
    memo's scope in code breaks it too. A one-way assertion would rot the moment
    someone rephrased the sentence.

    The claim is pinned here rather than in `tests/test_architecture_claims.py`
    because that file declares its scope as `docs/architecture/`, and
    `KNOWLEDGE_GRAPH.md` is not in it.
    """

    CLAIM = ("The memo lives only for the dynamic extent of one "
             "`build_graph_json()` call, and that boundary is the whole safety "
             "argument — do not widen it.")

    def test_the_claim_is_still_in_the_document(self):
        doc = (PROJECT_ROOT / "docs" / "KNOWLEDGE_GRAPH.md").read_text()
        assert self.CLAIM in doc, (
            "KNOWLEDGE_GRAPH.md no longer carries the memo-scope claim verbatim — "
            "re-verify it against the code before rewording")

    def test_the_code_fact_behind_the_claim(self):
        """`build_graph_json` is the ONLY thing that opens a memo scope."""
        source = (PROJECT_ROOT / "scripts" / "build_graph.py").read_text()
        openers = source.count("_build_memo_scope()")
        assert openers == 2, (
            f"expected exactly two occurrences of `_build_memo_scope()` — the "
            f"definition and the single use in `build_graph_json` — found {openers}. "
            f"A third means something else opens a memo scope, and the documented "
            f"boundary no longer holds.")
        assert "with _build_memo_scope():\n        return _build_graph_json_uncached(" in source


class TestASeededMutationSurvivesTheMemo:
    """Production-artifact seeding — the non-vacuity bar."""

    SEEDED_DIR = "2026-08-14-memo-nonvacuity-probe"

    @pytest.fixture
    def seeded_finding(self):
        """Write a real review document into the real corpus, then remove it.

        Through `seed_journal.seeded_artifact` since 2026-08-15: the removal is journalled
        before the file appears, so a killed run leaves a repairable record rather than a
        stray review directory that the next build reads as a real finding.
        """
        from seed_journal import SEED_MARKER, seeded_artifact
        doc = (PROJECT_ROOT / "papers" / "AutomatedReviews" / self.SEEDED_DIR / "infra.md")
        expected_id = bg.mint_finding_id(self.SEEDED_DIR, "infra", "1")
        with seeded_artifact(
                doc,
                "# Memo non-vacuity probe\n\n"
                "### 1 — probe finding written by tests/test_build_graph_memo.py\n\n"
                "- **Severity:** minor\n"
                "- **Lane:** infra\n"
                "- **Observed:** seeded by a test to prove the within-build memo "
                f"cannot hide a corpus change from the next build. <!-- {SEED_MARKER} -->\n",
                reason="a finding filed mid-session must be visible to the NEXT build"):
            yield expected_id

    def test_a_finding_seeded_into_the_REAL_corpus_is_visible_to_the_next_build(
            self, seeded_finding):
        """⚠️ THE LOAD-BEARING GUARD.

        A memo that outlived a single build would serve the pre-seeding node set
        here and this would fail. Nothing else in this file would.
        """
        graph = bg.build_graph_json(sync_pg=False)
        ids = {n["id"] for n in graph["nodes"]}
        assert seeded_finding in ids, (
            f"{seeded_finding} was written into papers/AutomatedReviews/ but the "
            f"next build did not see it — the memo is outliving its build")

    def test_removing_the_seeded_finding_is_visible_too(self, seeded_finding):
        """Both directions. A cache keyed on 'has the corpus grown' would pass
        the appearance test and fail this one."""
        assert seeded_finding in {n["id"] for n in bg.build_graph_json(sync_pg=False)["nodes"]}
        review_dir = PROJECT_ROOT / "papers" / "AutomatedReviews" / self.SEEDED_DIR
        (review_dir / "infra.md").unlink()
        assert seeded_finding not in {
            n["id"] for n in bg.build_graph_json(sync_pg=False)["nodes"]}
        (review_dir / "infra.md").write_text("# removed and restored by the fixture\n")
