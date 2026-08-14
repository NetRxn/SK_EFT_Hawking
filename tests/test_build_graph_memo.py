"""Guards for the within-build extractor memo (`build_graph._BUILD_MEMO`).

WHAT THESE PROTECT, AND WHY IT IS NOT THE OBVIOUS THING
-------------------------------------------------------
The memo exists for speed — measured 2026-08-14, it takes `build_graph_json()`
from 14.4 s to 7.1 s by not re-deriving the argument-free extractors the 4-6
times each that a single build otherwise calls them. Speed is not what these
tests guard.

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
#: to be the ONLY difference by running two *unmemoized* builds against each
#: other: 704 gate nodes differed, and `last_evaluated` was the sole differing
#: key. Normalising them is therefore not weakening the comparison — without it
#: the test would assert a property the code never had.
_VOLATILE = {"built_at", "last_evaluated", "last_modified", "generated_at"}


def _normalise(obj):
    if isinstance(obj, dict):
        return {k: ("<TS>" if k in _VOLATILE else _normalise(v)) for k, v in obj.items()}
    if isinstance(obj, list):
        return [_normalise(v) for v in obj]
    return obj


def _canonical(graph) -> str:
    return json.dumps(_normalise(graph), sort_keys=True, default=str)


class TestTheMemoCannotOutliveABuild:
    """The whole safety argument is the memo's lifetime. These pin it."""

    def test_the_memo_is_drained_at_rest(self):
        assert bg._BUILD_MEMO is None, (
            "the memo must be None outside a build — a non-None value at rest means "
            "some path enabled it without a scope to tear it down")

    def test_the_memo_is_drained_after_a_build(self):
        bg.build_graph_json(sync_pg=False)
        assert bg._BUILD_MEMO is None

    def test_an_extractor_called_outside_a_build_is_not_memoized(self):
        """Direct callers must always read live state.

        `bundle_readiness.load_findings_by_paper` calls
        `extract_review_finding_nodes` with no build in progress. If the memo
        were process-scoped, that call would replay whatever the last build saw.
        """
        assert bg._BUILD_MEMO is None
        first = bg.extract_review_finding_nodes()
        second = bg.extract_review_finding_nodes()
        assert first is not second, "a fresh computation must return a fresh object"

    def test_a_nested_build_does_not_tear_down_the_outer_memo(self):
        with bg._build_memo_scope():
            bg.extract_review_finding_nodes()
            assert bg._BUILD_MEMO is not None
            with bg._build_memo_scope():
                pass
            assert bg._BUILD_MEMO is not None, (
                "an inner scope exiting must not drain the outer build's memo")
        assert bg._BUILD_MEMO is None


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
        """Write a real review document into the real corpus, then remove it."""
        review_dir = PROJECT_ROOT / "papers" / "AutomatedReviews" / self.SEEDED_DIR
        review_dir.mkdir(parents=True, exist_ok=False)
        doc = review_dir / "infra.md"
        doc.write_text(
            "# Memo non-vacuity probe\n\n"
            "### 1 — probe finding written by tests/test_build_graph_memo.py\n\n"
            "- **Severity:** minor\n"
            "- **Lane:** infra\n"
            "- **Observed:** seeded by a test to prove the within-build memo "
            "cannot hide a corpus change from the next build.\n"
        )
        expected_id = bg.mint_finding_id(self.SEEDED_DIR, "infra", "1")
        try:
            yield expected_id
        finally:
            doc.unlink(missing_ok=True)
            review_dir.rmdir()

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
