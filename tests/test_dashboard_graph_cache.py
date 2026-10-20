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


# These controls extend the original real-build/seam module above. Syscall
# exceptions below are path-specific semantic fixtures, not native host faults.
import errno  # noqa: E402
import os  # noqa: E402


@pytest.fixture
def io_state_inputs(tmp_path, monkeypatch, warmed):
    """Record real successful and attempted missing opens through the owner.

    A local read-set dictionary keeps these temporary observations from changing
    the real warmed graph's retained population after this test finishes.
    Imported repository code remains in every fingerprint by the normal owner.
    """
    tmp_path = tmp_path.resolve()
    anchor = tmp_path / "anchor.txt"
    anchor.write_bytes(b"recorded anchor")
    missing = tmp_path / "optional" / "input.json"
    monkeypatch.setattr(pd, "_READ_SET", dict(pd._READ_SET))
    with pd._record_build_reads():
        anchor.read_bytes()
        with pytest.raises(FileNotFoundError) as caught:
            missing.read_bytes()
        assert caught.value.errno == errno.ENOENT
    assert str(anchor) in pd._READ_SET["paths"]
    assert str(missing) in pd._READ_SET["paths"]
    assert str(missing.parent) in pd._READ_SET["dirs"]
    return {"anchor": anchor, "file": missing, "directory": missing.parent}


class TestKnownAbsenceIsAnObservation:

    @pytest.mark.parametrize("kind", ["file", "directory"])
    def test_recorded_known_absence_repeats_without_an_error_warning(
            self, io_state_inputs, caplog, kind):
        target = str(io_state_inputs[kind])
        caplog.clear()
        first, second = pd._graph_fingerprint(), pd._graph_fingerprint()
        assert first == second, "a known missing input disabled the real key"
        assert next(row for row in first if row[0] == target) == next(
            row for row in second if row[0] == target)
        assert not any(target in record.getMessage()
                       and "forcing a rebuild" in record.getMessage()
                       for record in caplog.records)

    def test_missing_empty_nonempty_removed_and_recreated_directory(
            self, io_state_inputs):
        directory = io_state_inputs["directory"]
        missing = pd._graph_fingerprint()
        missing_entry = next(row for row in missing if row[0] == str(directory))
        directory.mkdir()
        empty = pd._graph_fingerprint()
        empty_entry = next(row for row in empty if row[0] == str(directory))
        assert empty_entry == (str(directory), ())
        assert missing_entry != empty_entry and missing != empty
        child = directory / "new-child.txt"
        child.write_bytes(b"new")
        nonempty = pd._graph_fingerprint()
        nonempty_entry = next(row for row in nonempty if row[0] == str(directory))
        assert nonempty_entry != empty_entry and nonempty != empty
        child.unlink()
        emptied = pd._graph_fingerprint()
        assert next(row for row in emptied if row[0] == str(directory)) == empty_entry
        assert emptied != nonempty
        directory.rmdir()
        removed = pd._graph_fingerprint()
        assert next(row for row in removed if row[0] == str(directory)) == missing_entry
        assert removed != emptied
        directory.mkdir()
        recreated = pd._graph_fingerprint()
        assert next(row for row in recreated if row[0] == str(directory)) == empty_entry
        assert recreated != removed

    def test_missing_empty_nonempty_removed_and_recreated_file(
            self, io_state_inputs):
        target = io_state_inputs["file"]
        missing = pd._graph_fingerprint()
        missing_entry = next(row for row in missing if row[0] == str(target))
        target.parent.mkdir()
        target.write_bytes(b"")
        empty = pd._graph_fingerprint()
        empty_entry = next(row for row in empty if row[0] == str(target))
        assert empty_entry[2] == 0
        assert empty_entry != missing_entry and empty != missing
        target.write_bytes(b"nonempty")
        nonempty = pd._graph_fingerprint()
        nonempty_entry = next(row for row in nonempty if row[0] == str(target))
        assert nonempty_entry != empty_entry and nonempty != empty
        target.unlink()
        removed = pd._graph_fingerprint()
        assert next(row for row in removed if row[0] == str(target)) == missing_entry
        assert removed != nonempty
        target.write_bytes(b"")
        recreated = pd._graph_fingerprint()
        assert next(row for row in recreated if row[0] == str(target)) != missing_entry
        assert recreated != removed

    def test_same_size_write_with_changed_nanosecond_mtime_moves_file_entry(
            self, io_state_inputs):
        target = io_state_inputs["anchor"]
        before = pd._graph_fingerprint()
        before_entry = next(row for row in before if row[0] == str(target))
        observed = target.stat()
        target.write_bytes(b"X" * observed.st_size)
        os.utime(target, ns=(observed.st_atime_ns,
                             observed.st_mtime_ns + 1_000_000_000))
        after = pd._graph_fingerprint()
        after_entry = next(row for row in after if row[0] == str(target))
        assert after_entry[2] == before_entry[2]
        assert after_entry[1] != before_entry[1]
        assert after_entry != before_entry and after != before

    def test_real_graph_with_recorded_missing_input_keeps_its_cached_identity(
            self, tmp_path, monkeypatch, warmed):
        """The wrapper adds a read; the original full graph builder still runs.

        This is an actual recorded build and consumer, with PG off, not a fake
        graph or a preinstalled green fingerprint. No missing directory is made.
        """
        import build_graph as bg

        missing = tmp_path.resolve() / "never-created" / "optional.json"
        real_builder = bg.build_graph_json

        def build_with_missing_read(*, sync_pg=False):
            with pytest.raises(FileNotFoundError) as caught:
                missing.read_bytes()
            assert caught.value.errno == errno.ENOENT
            return real_builder(sync_pg=sync_pg)

        monkeypatch.setattr(pd, "_READ_SET", dict(pd._READ_SET))
        monkeypatch.setattr(pd, "_GRAPH_CACHE", dict(pd._GRAPH_CACHE))
        monkeypatch.setattr(bg, "build_graph_json", build_with_missing_read)
        first = pd.get_cached_graph(force_rebuild=True, sync_pg=False)
        assert str(missing) in pd._READ_SET["paths"]
        assert str(missing.parent) in pd._READ_SET["dirs"]
        before = pd._graph_fingerprint()
        second = pd.get_cached_graph(sync_pg=False)
        assert pd._graph_fingerprint() == before
        assert second is first, "known absence prevented a real cached-object hit"


class TestUnavailableIOCannotCertifyFreshness:

    @pytest.mark.parametrize("operation,kind", [("stat", "file"),
                                               ("listdir", "directory")])
    @pytest.mark.parametrize("error", [
        pytest.param(errno.EACCES, id="EACCES"),
        pytest.param(errno.EPERM, id="EPERM"),
        pytest.param(errno.ENFILE, id="ENFILE"),
        pytest.param(errno.EMFILE, id="EMFILE"),
        pytest.param(errno.EIO, id="EIO"),
        pytest.param(errno.ELOOP, id="ELOOP"),
        pytest.param(errno.ENOTDIR, id="ENOTDIR"),
        *([pytest.param(errno.ESTALE, id="ESTALE")]
          if hasattr(errno, "ESTALE") else []),
        pytest.param(987654, id="unrecognized-errno"),
        pytest.param(None, id="opaque-OSError"),
        pytest.param("no-errno-FileNotFoundError", id="class-without-errno"),
        pytest.param("contradictory-FileNotFoundError", id="class-with-EACCES"),
    ])
    def test_unknown_repeat_and_unknown_to_missing_or_present_never_match(
            self, io_state_inputs, monkeypatch, caplog, operation, kind, error):
        """Inject only the selected syscall/path; all other observations are real.

        File unknown-repeat and unknown-to-ENOENT are the old file-branch
        false-hit countermodels. Looking at the affected entry prevents another
        directory change from making these assertions pass accidentally.
        """
        target = io_state_inputs[kind]
        original = getattr(pd.os, operation)
        fault = {"active": False, "error": error}

        def selected_path_fault(path, *args, **kwargs):
            if (isinstance(path, (str, bytes, os.PathLike))
                    and os.fsdecode(os.fspath(path)) == str(target)
                    and fault["active"]):
                if fault["error"] == "no-errno-FileNotFoundError":
                    raise FileNotFoundError("synthetic class without errno")
                if fault["error"] == "contradictory-FileNotFoundError":
                    raise FileNotFoundError(errno.EACCES, "synthetic class", str(target))
                if fault["error"] is None:
                    raise OSError("synthetic opaque observation")
                raise OSError(fault["error"], "synthetic syscall observation", str(target))
            return original(path, *args, **kwargs)

        monkeypatch.setattr(pd.os, operation, selected_path_fault)
        missing = pd._graph_fingerprint()
        missing_entry = next(row for row in missing if row[0] == str(target))
        caplog.clear()
        fault["active"] = True
        unknown_first = pd._graph_fingerprint()
        unknown_second = pd._graph_fingerprint()
        first_entry = next(row for row in unknown_first if row[0] == str(target))
        second_entry = next(row for row in unknown_second if row[0] == str(target))
        assert first_entry != second_entry and unknown_first != unknown_second
        assert first_entry != missing_entry and unknown_first != missing
        assert any(str(target) in record.getMessage()
                   and "forcing a rebuild" in record.getMessage()
                   for record in caplog.records)
        fault["error"] = errno.EIO if error != errno.EIO else errno.EACCES
        different_unknown = pd._graph_fingerprint()
        assert next(row for row in different_unknown if row[0] == str(target)) != second_entry
        fault["active"] = False
        known_missing = pd._graph_fingerprint()
        known_missing_entry = next(row for row in known_missing if row[0] == str(target))
        assert known_missing_entry == missing_entry
        assert second_entry != known_missing_entry and unknown_second != known_missing
        if kind == "file":
            target.parent.mkdir()
            target.write_bytes(b"present")
        else:
            target.mkdir()
        present = pd._graph_fingerprint()
        present_entry = next(row for row in present if row[0] == str(target))
        fault["active"] = True
        unknown_from_present = pd._graph_fingerprint()
        from_present_entry = next(row for row in unknown_from_present
                                  if row[0] == str(target))
        assert from_present_entry != present_entry and unknown_from_present != present
        fault["active"] = False
        restored_present = pd._graph_fingerprint()
        assert next(row for row in restored_present if row[0] == str(target)) == present_entry
        assert from_present_entry != present_entry and unknown_from_present != restored_present

    @pytest.mark.parametrize("operation,kind", [("stat", "file"),
                                               ("listdir", "directory")])
    def test_FileNotFoundError_is_stable_only_with_reported_ENOENT(
            self, io_state_inputs, monkeypatch, operation, kind):
        target = io_state_inputs[kind]
        original = getattr(pd.os, operation)

        def known_missing(path, *args, **kwargs):
            if (isinstance(path, (str, bytes, os.PathLike))
                    and os.fsdecode(os.fspath(path)) == str(target)):
                raise FileNotFoundError(errno.ENOENT, "known missing", str(target))
            return original(path, *args, **kwargs)

        before = pd._graph_fingerprint()
        monkeypatch.setattr(pd.os, operation, known_missing)
        first, second = pd._graph_fingerprint(), pd._graph_fingerprint()
        assert first == second and first == before

    def test_real_intermediate_file_is_unknown_for_stat_and_listing(
            self, io_state_inputs, tmp_path):
        obstruction = tmp_path.resolve() / "not-a-directory"
        obstruction.write_bytes(b"file")
        blocked = obstruction / "input.json"
        with pd._record_build_reads():
            io_state_inputs["anchor"].read_bytes()
            with pytest.raises(NotADirectoryError) as caught:
                blocked.read_bytes()
            assert caught.value.errno == errno.ENOTDIR
        assert str(blocked) in pd._READ_SET["paths"]
        assert str(obstruction) in pd._READ_SET["dirs"]
        first, second = pd._graph_fingerprint(), pd._graph_fingerprint()
        for target in (blocked, obstruction):
            assert next(row for row in first if row[0] == str(target)) != next(
                row for row in second if row[0] == str(target))
        assert first != second


class TestRecordedPopulationAndFailSafes:

    @pytest.mark.parametrize("paths", [None, (), []],
                             ids=["unavailable", "empty-tuple", "empty-list"])
    def test_unavailable_or_empty_population_stays_nonmatching(
            self, monkeypatch, warmed, paths):
        monkeypatch.setattr(pd, "_READ_SET", {"paths": paths, "dirs": None})
        first, second = pd._graph_fingerprint(), pd._graph_fingerprint()
        assert first != second
        assert first is not None and second is not None

    def test_failed_finalization_discards_the_previous_population(
            self, io_state_inputs, monkeypatch):
        def fail_finalization(captured, started_ns):
            raise OSError(errno.EIO, "synthetic recorder finalization fault")

        monkeypatch.setattr(pd, "_finalise_read_set", fail_finalization)
        with pd._record_build_reads():
            io_state_inputs["anchor"].read_bytes()
        assert pd._READ_SET == {"paths": None, "dirs": None}
        assert pd._RECORDED_READS is None
        assert pd._graph_fingerprint() != pd._graph_fingerprint()

    def test_no_captured_reads_discards_the_previous_population(
            self, io_state_inputs):
        pd._finalise_read_set(set(), pd.time.time_ns())
        assert pd._READ_SET == {"paths": None, "dirs": None}
        assert pd._graph_fingerprint() != pd._graph_fingerprint()

    def test_existing_mtime_during_build_predicate_discards_the_population(
            self, io_state_inputs):
        """Exercise the actual predicate with a controlled start timestamp.

        This is not a native concurrent-write experiment or an atomic-snapshot
        claim. The real current artifact is newer than the supplied start.
        """
        anchor = io_state_inputs["anchor"]
        pd._finalise_read_set({str(anchor)}, anchor.stat().st_mtime_ns - 1)
        assert pd._READ_SET == {"paths": None, "dirs": None}
        assert pd._graph_fingerprint() != pd._graph_fingerprint()

    def test_actual_recorded_inputs_and_loaded_graph_code_remain_in_the_key(
            self, io_state_inputs):
        key_paths = {row[0] for row in pd._graph_fingerprint()}
        assert str(io_state_inputs["anchor"]) in key_paths
        assert str(io_state_inputs["file"]) in key_paths
        assert str(io_state_inputs["directory"]) in key_paths
        builder = str((PROJECT_ROOT / "scripts" / "build_graph.py").resolve())
        assert builder in pd._loaded_repo_module_sources()
        assert builder in key_paths, "already-imported graph code left the actual key"

    def test_actual_recorder_keeps_every_nested_repo_ancestor(
            self, tmp_path, monkeypatch, io_state_inputs):
        """A bounded fixture repo exercises the existing ancestor owner itself."""
        tmp_path = tmp_path.resolve()
        monkeypatch.setattr(pd, "PROJECT_ROOT", tmp_path)
        missing = tmp_path / "first" / "second" / "third" / "input.json"
        with pd._record_build_reads():
            with pytest.raises(FileNotFoundError):
                missing.read_bytes()
        assert str(missing) in pd._READ_SET["paths"]
        expected = {str(tmp_path), str(tmp_path / "first"),
                    str(tmp_path / "first" / "second"),
                    str(tmp_path / "first" / "second" / "third")}
        assert set(pd._READ_SET["dirs"]) == expected

    def test_dangling_file_lookup_changes_when_its_watched_target_is_created(
            self, io_state_inputs, tmp_path):
        target = io_state_inputs["file"]
        alias = tmp_path.resolve() / "alias.json"
        alias.symlink_to(target)
        with pd._record_build_reads():
            io_state_inputs["anchor"].read_bytes()
            for path in (alias, target):
                with pytest.raises(FileNotFoundError) as caught:
                    path.read_bytes()
                assert caught.value.errno == errno.ENOENT
        assert str(target) in pd._READ_SET["paths"]
        assert str(alias) in pd._READ_SET["paths"]
        before = pd._graph_fingerprint()
        assert before == pd._graph_fingerprint()
        target.parent.mkdir()
        target.write_bytes(b"target exists")
        after = pd._graph_fingerprint()
        for path in (alias, target):
            assert next(row for row in before if row[0] == str(path)) != next(
                row for row in after if row[0] == str(path))
        assert before != after

    def test_external_dangling_directory_tracks_its_raw_alias_parent(
            self, io_state_inputs, tmp_path):
        """An external failed open watches its raw alias directory parent."""
        target = tmp_path.resolve() / "missing-directory"
        alias = tmp_path.resolve() / "directory-alias"
        alias.symlink_to(target, target_is_directory=True)
        with pd._record_build_reads():
            io_state_inputs["anchor"].read_bytes()
            with pytest.raises(FileNotFoundError):
                (alias / "input.json").read_bytes()
        assert str(alias) in pd._READ_SET["dirs"]
        before = pd._graph_fingerprint()
        before_entry = next(row for row in before if row[0] == str(alias))
        assert before_entry == (str(alias), '<missing>')
        assert before == pd._graph_fingerprint()
        target.mkdir()
        after = pd._graph_fingerprint()
        after_entry = next(row for row in after if row[0] == str(alias))
        assert after_entry == (str(alias), ())
        assert before_entry != after_entry
        assert before != after
