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
        before = pd._graph_fingerprint()
        probe = REVIEWS / "2026-08-14-key-coverage-probe"
        probe.mkdir(parents=True, exist_ok=False)
        try:
            assert pd._graph_fingerprint() != before, (
                "a new dated directory did not move the key — paths alone cannot "
                "see a file that did not exist at the last build")
        finally:
            probe.rmdir()


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

        before = pd.get_cached_graph(sync_pg=False)
        probe_dir = REVIEWS / "2026-08-14-seam-probe"
        probe_dir.mkdir(parents=True, exist_ok=False)
        (probe_dir / "infra.md").write_text(
            "# Seam probe\n\n### 1 — probe finding\n\n"
            "- **Severity:** minor\n- **Lane:** infra\n"
            "- **Observed:** seeded by tests/test_dashboard_graph_cache.py\n")
        expected = bg.mint_finding_id("2026-08-14-seam-probe", "infra", "1")
        try:
            after = pd.get_cached_graph(sync_pg=False)
            assert after is not before, "the dashboard served its cached graph"
            assert expected in {n["id"] for n in after["nodes"]}, (
                "a finding was filed and the dashboard's graph does not contain it")
        finally:
            (probe_dir / "infra.md").unlink()
            probe_dir.rmdir()
        restored = pd.get_cached_graph(sync_pg=False)
        assert expected not in {n["id"] for n in restored["nodes"]}
