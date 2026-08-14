"""D5 both-directions tests for `validation/checks/freshness.py` — audit QI-27.

Six checks: `counts_fresh`, `tables_fresh`, `claim_clusters_fresh`,
`notebook_stored_outputs_current`, `bundle_source_freshness`,
`inventory_index_autogen_fresh`.

THREE OF THESE REGENERATE THE TREE, so they are QUARANTINED from the characterization
harness and cannot be covered by a snapshot. That makes a real test the only protection
they have ever had. Every test here replaces `subprocess.run` with a recorder — the
point under test is the STALENESS PREDICATE and the verdict, never whether
`update_counts.py` works (it has its own tests, and shelling out here would make this
file a 30-minute run).

⚠️ `_COUNTS_SOURCES`, `_TABLES_SOURCES` and `CLAIM_CLUSTERS_PATH` are MODULE-LEVEL
paths built from `_H.*` at import time (the `X = _H.NAME / "y"` BinOp form that
`test_no_check_module_aliases_a_path` documents as a known gap — audit §4 residuals),
so patching `_H.PROJECT_ROOT` alone does not move them. These tests patch the module
attributes directly, and `TestPathAliasCoupling` pins the derivation so the two cannot
drift apart silently.

`notebook_stored_outputs_current` gets the most coverage here, and deliberately: its
docstring records **five successive rounds in which a reviewer defeated it** —
string-only comparison, scalar-position moves, length-only array summaries, a narrow
MIME allow-list, and finally a hand-edited SVG. Each is a leg below, so a future
narrowing reopens a demonstrated attack rather than an imagined one.

MUTATION-VERIFIED 2026-08-04 — 11 mutations, all CAUGHT, clean negative control.
"""
from __future__ import annotations

import ast
import base64
import json
import struct
import sys

import pytest
from pathlib import Path

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT / "scripts"))
sys.path.insert(0, str(SK_ROOT))

import validate_helpers as _H  # noqa: E402
from validation import _config as _cfg  # noqa: E402
from validation.checks import freshness as fr  # noqa: E402


class _Ran:
    """Recorder standing in for `subprocess.run`. Regeneration is a side effect on the
    real tree; the predicate and the verdict are what these tests are about."""

    def __init__(self, returncode=0, stdout="2 tables", stderr=""):
        self.calls: list[list[str]] = []
        self._rc, self._out, self._err = returncode, stdout, stderr

    def __call__(self, cmd, **kw):
        self.calls.append(cmd)
        class _R:
            returncode, stdout, stderr = self._rc, self._out, self._err
        return _R()


def _touch(p: Path, mtime: float, body: str = "x") -> Path:
    import os
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(body)
    os.utime(p, (mtime, mtime))
    return p


class TestCountsFreshness:
    """`counts.json`/`counts.tex` reflect the current codebase. Papers `\\input` these
    macros, so a stale value is a wrong number in a published paper."""

    @staticmethod
    def _republish(counts_json, mtime):
        """Rewrite the fixture's `python` block from the (retargeted) live trees."""
        import os
        import update_counts as _uc
        data = json.loads(counts_json.read_text())
        data["python"] = _uc.count_python_cheap(
            src_dir=_H.SRC_DIR, tests_dir=_H.TESTS_DIR,
            notebooks_dir=_H.NOTEBOOKS_DIR, papers_dir=_H.PAPERS_DIR,
            viz_file=_H.SRC_DIR / "core" / "visualizations.py")
        counts_json.write_text(json.dumps(data))
        os.utime(counts_json, (mtime, mtime))

    def _setup(self, tmp_path, monkeypatch, *, counts_mtime, source_mtime,
               lean_mtime=None, tex=True):
        docs = tmp_path / "docs"
        cj = _touch(docs / "counts.json", counts_mtime, json.dumps(
            {"lean": {"theorems_total": 10}, "python": {}, "aristotle": {}}))
        monkeypatch.setattr(_H, "COUNTS_JSON_PATH", cj)
        ct = docs / "counts.tex"
        if tex:
            _touch(ct, counts_mtime)
        monkeypatch.setattr(_H, "COUNTS_TEX_PATH", ct)
        src = _touch(tmp_path / "src" / "core" / "constants.py", source_mtime)
        monkeypatch.setattr(fr, "_COUNTS_SOURCES", [src])
        lean = tmp_path / "lean" / "SKEFTHawking"
        _touch(lean / "Sub" / "M.lean", lean_mtime if lean_mtime else 0.0)
        monkeypatch.setattr(_H, "LEAN_DIR", lean)
        # `counts.json` also publishes pytest_cases / test_files / notebooks /
        # papers, so those trees are staleness inputs too (added 2026-08-10 after
        # \totaltests drifted 6163→6171 with this check green). Retarget them at
        # empty tmp dirs, exactly as LEAN_DIR is: a fixture that leaves a real-tree
        # anchor in place is testing the developer's working copy, not the check.
        for _name in ("TESTS_DIR", "NOTEBOOKS_DIR", "PAPERS_DIR", "SRC_DIR"):
            _d = tmp_path / _name.lower()
            _d.mkdir(parents=True, exist_ok=True)
            monkeypatch.setattr(_H, _name, _d)
        # ⚠️ REPUBLISH IS THE CALLER'S JOB, NOT THE FIXTURE'S — and getting that wrong
        # here VOIDED THREE PRE-EXISTING TESTS (pr-review 2026-08-13). Publishing counts
        # at setup time meant that when a test later seeded a file into one of these
        # trees, the LIVE count moved too, so the new value leg fired and
        # `test_every_tree_counts_json_publishes_is_a_staleness_input[SRC_DIR|TESTS_DIR|
        # NOTEBOOKS_DIR]` stayed green even with the entire four-tree MTIME loop deleted.
        # They no longer tested their named subject. The fixture now publishes only the
        # empty state; a test that seeds must call `_republish` itself if it wants the
        # count leg silent, and the mtime cases assert on the REASON so each leg is
        # attributed to the mechanism it is named for.
        self._republish(cj, counts_mtime)
        runner = _Ran()
        monkeypatch.setattr(fr.subprocess, "run", runner)
        return runner

    def test_fresh_counts_do_not_regenerate(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA — and, importantly, does not shell out. A check that
        regenerates unconditionally would make every run pay the 30-minute ExtractDeps."""
        runner = self._setup(tmp_path, monkeypatch, counts_mtime=2000, source_mtime=1000)
        r = fr.check_counts_fresh()
        assert r.passed is True
        assert runner.calls == [], "update_counts.py ran against FRESH counts"

    def test_a_newer_source_marks_counts_stale(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — `constants.py` edited after counts were built."""
        runner = self._setup(tmp_path, monkeypatch, counts_mtime=1000, source_mtime=2000)
        r = fr.check_counts_fresh()
        assert runner.calls, (
            "a source newer than counts.json did not trigger regeneration — papers "
            "would `\\input` stale macro values")
        assert any("stale" in (d.message or "") for d in r.details)

    def test_a_lean_file_in_a_subdirectory_marks_counts_stale(self, tmp_path, monkeypatch):
        """ADR-004 W7 finding M2 — the ORIGINAL instance of the QI-01 class, and the
        one place it had already been fixed. `rglob`, not `glob`: a `native_decide`
        added in `FKLW/` or `QuantumNetwork/` must mark counts stale, or the
        declaration-closure metric silently measures the previous wave."""
        runner = self._setup(tmp_path, monkeypatch, counts_mtime=1000,
                             source_mtime=500, lean_mtime=3000)
        fr.check_counts_fresh()
        assert runner.calls, (
            "a .lean file in a SUBDIRECTORY did not mark counts stale — this is "
            "ADR-004 W7 M2 reopened, and it is the seed of audit QI-01")

    @pytest.mark.parametrize("anchor,rel", [
        ("SRC_DIR", "core/formulas.py"),
        ("TESTS_DIR", "test_thing.py"),
        ("NOTEBOOKS_DIR", "nb.ipynb"),
        ("PAPERS_DIR", "D1/paper_draft.tex"),
    ])
    def test_every_tree_counts_json_publishes_is_a_staleness_input(
            self, tmp_path, monkeypatch, anchor, rel):
        """ONE LEG PER PUBLISHED TREE. `counts.json` publishes figures derived from
        `src/`, `tests/`, `notebooks/` and `papers/`; a tree that is not a staleness
        input lets its figure drift while this check stays green — exactly how
        `\\totaltests` drifted 6163→6171. Each parameter case fails if its leg is
        dropped from `_counts_is_stale`. The SRC_DIR case is the one added
        2026-08-10; the other three had no positive test at all before it."""
        runner = self._setup(tmp_path, monkeypatch, counts_mtime=1000, source_mtime=500)
        _touch(getattr(_H, anchor) / rel, 3000)
        # Republish AFTER seeding, so the published counts already include the new file:
        # the count leg is then silent and only the MTIME leg can explain a stale verdict.
        # Without this the count leg answers, and this test passes with its subject deleted.
        self._republish(_H.COUNTS_JSON_PATH, 1000)
        stale, reason = fr._counts_is_stale()
        assert stale and "newer than counts.json" in reason, (
            f"the mtime leg did not fire; verdict was {(stale, reason)!r} — if the count "
            f"leg answered instead, this case is no longer testing its named subject")
        fr.check_counts_fresh()
        assert runner.calls, (
            f"a file under {anchor} newer than counts.json did not mark counts stale — "
            f"counts.json publishes a figure derived from that tree, so the figure can "
            f"now drift with this check green")

    def test_a_deleted_test_file_marks_counts_stale(self, tmp_path, monkeypatch):
        """THE DIRECTION EVERY MTIME LEG IS BLIND TO, and it shipped.

        Deleting a file leaves every surviving file's mtime untouched, so an
        mtime-max cannot move and the check reports fresh. Measured 2026-08-13:
        `tests/test_inventory_index_autogen.py` was deleted in `bee7608c` and
        `docs/counts.json` shipped `test_files: 194` against a live 193 for three
        commits with `counts_fresh` green. Note the fixture's mtimes: counts is
        NEWER than every source, so this can only pass via the count leg.
        """
        runner = self._setup(tmp_path, monkeypatch, counts_mtime=2000, source_mtime=1000)
        victim = _touch(_H.TESTS_DIR / "test_gone.py", 500)
        self._republish(_H.COUNTS_JSON_PATH, 2000)   # counts.json knows about it
        assert fr._counts_is_stale()[0] is False, "fixture was not fresh to begin with"
        victim.unlink()                              # ← no surviving mtime moves
        stale, reason = fr._counts_is_stale()
        assert stale is True, (
            "a DELETED test file did not mark counts stale — every leg here is an "
            "mtime-max, which cannot see a deletion; this is bee7608c reopened")
        assert "test_files" in reason, reason
        fr.check_counts_fresh()
        assert runner.calls, "stale counts did not trigger regeneration"

    def test_production_seeded_a_wrong_published_count_is_stale(self, monkeypatch):
        """PRODUCTION-SEEDED MUTATION (guide §2.4) — the defect goes into
        `docs/counts.json` itself, not a fixture. A fixture-only mutation proves the
        test works; only this proves the check can fail against the artifact it
        actually reads. Restores byte-for-byte, mtime included."""
        import os
        real = _H.COUNTS_JSON_PATH
        original, st = real.read_bytes(), real.stat()
        try:
            data = json.loads(original)
            data["python"]["test_files"] = data["python"]["test_files"] + 1
            real.write_text(json.dumps(data, indent=2))
            # ⚠️ Stamp counts.json as the NEWEST thing in the repo. `_counts_is_stale`
            # returns on its FIRST stale reason, so on any working copy where a source
            # was edited after the last regeneration an mtime leg fires first and this
            # test can never reach — or isolate — the count leg. Without this the test
            # is green on a clean tree and spuriously red on a working one.
            future = max(p.stat().st_mtime for p in (_H.SRC_DIR.rglob("*.py"))) + 60
            os.utime(real, (future, future))
            stale, reason = fr._counts_is_stale()
            assert stale is True, (
                "counts.json publishing a test_files one higher than the live tree "
                "was reported FRESH — this is exactly what shipped at bee7608c")
            assert "test_files" in reason, reason
        finally:
            real.write_bytes(original)
            os.utime(real, (st.st_atime, st.st_mtime))
        # ⚠️ THE NEGATIVE CONTROL ASSERTS THE COUNT LEG, NOT THE WHOLE PREDICATE.
        # It used to assert `_counts_is_stale()[0] is False`, which is a claim about the
        # DEVELOPER'S TREE: any edit under src/, tests/, notebooks/ or papers/ since the
        # last regeneration makes an mtime leg fire and this test go red for a reason that
        # has nothing to do with its subject. It fired on exactly that, one edit later, in
        # this very file. The subject here is "published == live", so assert that.
        import update_counts as _uc
        published = json.loads(real.read_text(encoding="utf-8"))["python"]
        live = _uc.count_python_cheap()
        assert {k: published.get(k) for k in live} == live, (
            "counts.json's published glob figures no longer match the live tree after "
            "restore — regenerate with `uv run python scripts/update_counts.py`")

    def test_the_count_leg_covers_every_published_glob_figure(self):
        """SEAM GUARD (§2.5). The leg loops over whatever `count_python_cheap`
        returns, so a helper that returned `{}` — or quietly lost a key — would make
        every comparison above pass against nothing. Assert the leg set itself."""
        import update_counts as _uc
        legs = _uc.count_python_cheap()
        assert set(legs) == {"python_modules", "test_files", "notebooks",
                             "papers", "figures"}, legs
        assert all(isinstance(v, int) for v in legs.values()), legs
        assert legs["test_files"] > 0 and legs["python_modules"] > 0, (
            "the helper matched nothing against the real tree — a scan that matches "
            "nothing passes vacuously")

    def test_the_cheap_split_agrees_with_the_full_counter(self):
        """`count_python` delegates to `count_python_cheap`; if the split ever grows a
        second derivation the freshness check and the writer can disagree, and the
        check would then demand a regeneration that changes nothing."""
        import update_counts as _uc
        cheap = _uc.count_python_cheap()
        full = _uc.count_python()
        assert {k: full[k] for k in cheap} == cheap
        assert "pytest_cases" in full and "pytest_cases" not in cheap

    def test_a_missing_counts_tex_is_stale(self, tmp_path, monkeypatch):
        runner = self._setup(tmp_path, monkeypatch, counts_mtime=2000,
                             source_mtime=1000, tex=False)
        fr.check_counts_fresh()
        assert runner.calls

    def test_a_failed_regeneration_fails_the_check(self, tmp_path, monkeypatch):
        """Cannot-measure is not success: if the generator cannot run, the counts are
        unverified, not fresh."""
        self._setup(tmp_path, monkeypatch, counts_mtime=1000, source_mtime=2000)
        monkeypatch.setattr(fr.subprocess, "run", _Ran(returncode=1, stderr="boom"))
        r = fr.check_counts_fresh()
        assert r.passed is False
        assert any("failed" in (d.message or "") for d in r.details)

    def test_an_unrunnable_generator_fails_the_check(self, tmp_path, monkeypatch):
        self._setup(tmp_path, monkeypatch, counts_mtime=1000, source_mtime=2000)

        def _missing(cmd, **kw):
            raise FileNotFoundError("uv not found")
        monkeypatch.setattr(fr.subprocess, "run", _missing)
        assert fr.check_counts_fresh().passed is False


class TestTablesFreshness:
    """`papers/*/tables/*.tex` are `\\input` by the drafts. Same shape as counts."""

    def _papers(self, tmp_path, monkeypatch, *, spec_mtime, out_mtime, with_output=True):
        papers = tmp_path / "papers"
        _touch(papers / "paper1_x" / "tables.py", spec_mtime)
        if with_output:
            _touch(papers / "paper1_x" / "tables" / "t1.tex", out_mtime)
        monkeypatch.setattr(_H, "PAPERS_DIR", papers)
        monkeypatch.setattr(fr, "_TABLES_SOURCES", [])
        runner = _Ran()
        monkeypatch.setattr(fr.subprocess, "run", runner)
        return runner

    def test_fresh_tables_do_not_regenerate(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA."""
        runner = self._papers(tmp_path, monkeypatch, spec_mtime=1000, out_mtime=2000)
        assert fr.check_tables_fresh().passed is True
        assert runner.calls == []

    def test_a_newer_spec_marks_tables_stale(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT."""
        runner = self._papers(tmp_path, monkeypatch, spec_mtime=3000, out_mtime=1000)
        fr.check_tables_fresh()
        assert runner.calls, "a tables.py newer than its output did not regenerate"

    def test_a_LYING_generator_fails(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — PR-review R4-I7, fixed 2026-08-05.

        The one outcome these three checks could not report: a generator that exits 0
        **having written nothing**. Staleness was measured ONCE, before shelling out,
        and never asked again; the only `passed=False` paths were subprocess failures
        (non-zero rc, `FileNotFoundError`, timeout). Live proof from the review's own
        run, unchanged at HEAD before the fix:

            counts_fresh  detail 1: "stale: constants.py newer than counts.json"
                          detail 2: "update_counts.py succeeded"
                          verdict : PASS

        The `_Ran` stub reproduces exactly that: rc=0, no side effect on the tree. So
        the artifact is still stale afterwards, and the check must now say so instead
        of reporting the generator's own exit code as the answer.
        """
        self._papers(tmp_path, monkeypatch, spec_mtime=3000, out_mtime=1000)
        r = fr.check_tables_fresh()
        assert r.passed is False, (
            "the regenerator exited 0 and wrote nothing; the table is still stale and "
            "the check passed — it is reporting the generator's exit code, not the "
            "artifact's state")
        assert any(d.name == "post_regenerate" and not d.passed for d in r.details)

    def test_a_generator_that_actually_works_still_passes(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA, and the leg that keeps the fix from being a
        regression: re-testing must change nothing on the happy path. A generator that
        does its job leaves the artifact fresh."""
        papers = tmp_path / "papers"
        _touch(papers / "paper1_x" / "tables.py", 3000)
        _touch(papers / "paper1_x" / "tables" / "t1.tex", 1000)
        monkeypatch.setattr(_H, "PAPERS_DIR", papers)
        monkeypatch.setattr(fr, "_TABLES_SOURCES", [])

        def _renders(cmd, **kw):
            _touch(papers / "paper1_x" / "tables" / "t1.tex", 9000)
            class _R:
                returncode, stdout, stderr = 0, "1 tables", ""
            return _R()
        monkeypatch.setattr(fr.subprocess, "run", _renders)
        r = fr.check_tables_fresh()
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]
        assert any(d.name == "post_regenerate" and d.passed for d in r.details)

    def test_a_spec_with_no_output_is_stale(self, tmp_path, monkeypatch):
        """A spec that has never been rendered is the most stale state there is —
        and the easiest one to read as 'nothing to do'."""
        runner = self._papers(tmp_path, monkeypatch, spec_mtime=1000, out_mtime=0,
                              with_output=False)
        fr.check_tables_fresh()
        assert runner.calls

    def test_no_specs_is_not_staleness(self, tmp_path, monkeypatch):
        """A repo with no table specs is legitimately clean, not stale."""
        monkeypatch.setattr(_H, "PAPERS_DIR", tmp_path / "papers")
        runner = _Ran()
        monkeypatch.setattr(fr.subprocess, "run", runner)
        assert fr.check_tables_fresh().passed is True
        assert runner.calls == []

    def test_staleness_uses_the_OLDEST_output(self, tmp_path, monkeypatch):
        """`min`, not `max`. If one table is regenerated and another is not, the set
        is stale — taking the newest would let a single fresh file vouch for all."""
        papers = tmp_path / "papers"
        _touch(papers / "paper1_x" / "tables.py", 2000)
        _touch(papers / "paper1_x" / "tables" / "old.tex", 1000)
        _touch(papers / "paper1_x" / "tables" / "new.tex", 3000)
        monkeypatch.setattr(_H, "PAPERS_DIR", papers)
        monkeypatch.setattr(fr, "_TABLES_SOURCES", [])
        runner = _Ran()
        monkeypatch.setattr(fr.subprocess, "run", runner)
        fr.check_tables_fresh()
        assert runner.calls, (
            "one stale table among fresh ones was not detected — the comparison is "
            "against the newest output instead of the oldest")


class TestClaimClustersFreshness:
    """`papers/claim_clusters.json` vs the v2 `claims_review.json` files that feed it."""

    def _setup(self, tmp_path, monkeypatch, *, review_mtime, cluster_mtime,
               v2=True, with_cluster=True):
        papers = tmp_path / "papers"
        payload = {"sentences": []} if v2 else {"claims": []}
        _touch(papers / "paper1_x" / "claims_review.json", review_mtime,
               json.dumps(payload))
        monkeypatch.setattr(_H, "PAPERS_DIR", papers)
        cp = papers / "claim_clusters.json"
        if with_cluster:
            _touch(cp, cluster_mtime, json.dumps({"cluster_count": 1,
                                                  "paper_coverage": ["paper1_x"]}))
        monkeypatch.setattr(fr, "claim_clusters_path", lambda _p=cp: _p)
        runner = _Ran()
        monkeypatch.setattr(fr.subprocess, "run", runner)
        return runner

    def test_fresh_clusters_do_not_regenerate(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA."""
        runner = self._setup(tmp_path, monkeypatch, review_mtime=1000, cluster_mtime=2000)
        assert fr.check_claim_clusters_fresh().passed is True
        assert runner.calls == []

    def test_a_newer_review_marks_clusters_stale(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — stale clusters mean
        `graph_integrity.claim_cluster_inconsistency` runs against stale member sets."""
        runner = self._setup(tmp_path, monkeypatch, review_mtime=3000, cluster_mtime=1000)
        fr.check_claim_clusters_fresh()
        assert runner.calls

    def test_a_v1_review_does_not_participate(self, tmp_path, monkeypatch):
        """Only v2 files (those carrying a top-level `sentences` list) cluster. A v1
        file must not trigger regeneration — that would be a guard firing on data it
        does not govern."""
        runner = self._setup(tmp_path, monkeypatch, review_mtime=3000,
                             cluster_mtime=1000, v2=False)
        assert fr.check_claim_clusters_fresh().passed is True
        assert runner.calls == []

    def test_a_v2_review_with_no_cluster_file_is_stale(self, tmp_path, monkeypatch):
        runner = self._setup(tmp_path, monkeypatch, review_mtime=1000,
                             cluster_mtime=0, with_cluster=False)
        fr.check_claim_clusters_fresh()
        assert runner.calls

    def test_an_unreadable_cluster_file_fails(self, tmp_path, monkeypatch):
        self._setup(tmp_path, monkeypatch, review_mtime=1000, cluster_mtime=2000)
        fr.claim_clusters_path().write_text("{not json")
        assert fr.check_claim_clusters_fresh().passed is False


def _plotly_out(title: str, xs: list[float]) -> dict:
    return {"output_type": "display_data", "metadata": {},
            "data": {"application/vnd.plotly.v1+json":
                     {"data": [{"x": xs, "y": xs}],
                      "layout": {"title": {"text": title}}}}}


def _bdata_out(values: list[float]) -> dict:
    raw = b"".join(struct.pack("<d", v) for v in values)
    return {"output_type": "display_data", "metadata": {},
            "data": {"application/vnd.plotly.v1+json":
                     {"data": [{"y": {"dtype": "f8",
                                      "bdata": base64.b64encode(raw).decode()}}]}}}


def _mime_out(mime: str, text: str) -> dict:
    return {"output_type": "display_data", "metadata": {}, "data": {mime: text}}


class _StoredFakeClient:
    """Installs `produce` as the FRESH run's output, leaving the stored notebook alone.
    Real execution would make this file cost ~10 minutes; the logic under test is the
    COMPARISON, which is where all five historical defeats happened."""
    produce: list | None = None

    def __init__(self, nbobj, **kw):
        self.nb = nbobj

    def execute(self):
        if _StoredFakeClient.produce is None:
            return
        for c in self.nb.cells:
            if c.cell_type == "code":
                c["outputs"] = json.loads(json.dumps(_StoredFakeClient.produce))


class TestNotebookStoredOutputsCurrent:
    """Stored notebook output must be what the code actually produces.

    These notebooks SHIP as bundle artifacts, so the stored output is what a reader
    sees. Each leg below is a reviewer-demonstrated bypass of an earlier version.
    """

    def setup_method(self):
        _StoredFakeClient.produce = None

    def _run(self, tmp_path, monkeypatch, stored_outputs, fresh_outputs):
        import nbclient
        monkeypatch.setattr(nbclient, "NotebookClient", _StoredFakeClient)
        _StoredFakeClient.produce = fresh_outputs
        d = tmp_path / "notebooks"
        d.mkdir(parents=True, exist_ok=True)
        (d / "D11_companion.ipynb").write_text(json.dumps({
            "cells": [{"cell_type": "code", "source": ["fig.show()\n"], "metadata": {},
                       "id": "c0", "execution_count": 1, "outputs": stored_outputs}],
            "metadata": {}, "nbformat": 4, "nbformat_minor": 5}))
        monkeypatch.setattr(_H, "NOTEBOOKS_DIR", d)
        return fr.check_notebook_stored_outputs_current()

    def test_matching_output_passes(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA."""
        out = [_plotly_out("Maxwell-Garnett", [1.0, 2.0])]
        r = self._run(tmp_path, monkeypatch, out, out)
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_an_empty_scope_fails(self, tmp_path, monkeypatch):
        """D11 round-12. The glob IS the scope, so renaming a notebook out of the
        pattern silently emptied it and the check reported success having examined
        nothing — the same fail-open shape as the readiness guards."""
        d = tmp_path / "notebooks"
        d.mkdir(parents=True, exist_ok=True)
        monkeypatch.setattr(_H, "NOTEBOOKS_DIR", d)
        r = fr.check_notebook_stored_outputs_current()
        assert r.passed is False, (
            "no bundle companion notebook matched the glob and the check PASSED — "
            "an empty scope is unverified, not clean")

    def test_a_stale_figure_title_fails(self, tmp_path, monkeypatch):
        """D11 round-7 BLOCKER 5.1, the original: the shipped notebook rendered
        `Voigt-Reuss elastic bounds` and `effective modulus M`, two namings the paper
        and the Lean module header explicitly retract."""
        r = self._run(tmp_path, monkeypatch,
                      [_plotly_out("Voigt-Reuss elastic bounds", [1.0, 2.0])],
                      [_plotly_out("Maxwell-Garnett", [1.0, 2.0])])
        assert r.passed is False, (
            "stored figure output asserting a RETRACTED naming passed — this is the "
            "original round-7 blocker")

    def test_a_moved_scalar_marker_fails(self, tmp_path, monkeypatch):
        """D11 round-8. A reviewer moved the *certified* marker from `f = 1/2` to
        `f = 0.55` while its label still read `f = 1/2 ⟹ ε_eff = 2 (certified)`.
        Scalar coordinates serialize as JSON numbers, so a text-only comparison
        cannot see a certified point that has silently moved off its own value."""
        stored = {"output_type": "display_data", "metadata": {},
                  "data": {"application/vnd.plotly.v1+json":
                           {"data": [{"x": 0.5, "text": "f = 1/2 (certified)"}]}}}
        fresh = {"output_type": "display_data", "metadata": {},
                 "data": {"application/vnd.plotly.v1+json":
                          {"data": [{"x": 0.55, "text": "f = 1/2 (certified)"}]}}}
        assert self._run(tmp_path, monkeypatch, [stored], [fresh]).passed is False

    def test_a_markdown_only_claim_change_fails(self, tmp_path, monkeypatch):
        """D11 round-10. A `text/markdown` output asserting `C = +1` beside the name
        of the theorem certifying `C = −1` was invisible to the MIME allow-list."""
        r = self._run(tmp_path, monkeypatch,
                      [_mime_out("text/markdown", "The invariant is C = +1.")],
                      [_mime_out("text/markdown", "The invariant is C = -1.")])
        assert r.passed is False

    def test_a_hand_edited_svg_fails(self, tmp_path, monkeypatch):
        """D11 round-12. SVG was in neither the allow-list nor the json branch, so a
        reviewer appended an SVG cell, executed it, then edited ONLY the stored SVG to
        read `C = +1` and `3.3177 (certified)`. It is the realistic attack because
        GitHub does not render Plotly JSON, so a static renderer is what an author
        reaches for."""
        r = self._run(tmp_path, monkeypatch,
                      [_mime_out("image/svg+xml", "<svg><text>C = +1</text></svg>")],
                      [_mime_out("image/svg+xml", "<svg><text>C = -1</text></svg>")])
        assert r.passed is False

    def test_float_jitter_in_a_bulk_array_does_not_fail(self, tmp_path, monkeypatch):
        """The false-positive side. Bulk trace arrays move in their low-order digits
        with library/BLAS versions; a digest at 9 significant figures rounds that away.
        A check that fired here would be flagging non-claims."""
        # ⚠️ MEASURED, not eyeballed: 1e-16 is BELOW float64 eps, so `v * (1 + 1e-16)`
        # is bit-identical to `v` and the fixture would compare a list to itself —
        # testing nothing. 1e-12 genuinely changes the bytes while still rounding away
        # at 9 significant figures, which is the property under test.
        base = [1.0 + i for i in range(12)]
        jittered = [v * (1 + 1e-12) for v in base]
        assert jittered != base, "the jitter fixture is bit-identical — it tests nothing"
        r = self._run(tmp_path, monkeypatch,
                      [_plotly_out("t", base)], [_plotly_out("t", jittered)])
        assert r.passed is True, (
            "float jitter failed the check — it will fire on library upgrades "
            "and be silenced, which is how a guard dies")

    def test_a_genuinely_different_curve_fails(self, tmp_path, monkeypatch):
        """D11 round-9. Length-only summaries made the VALUES of any array longer than
        8 invisible: the reviewer demonstrated the shipped notebook plotting
        `ε = 1 + 3f` instead of Maxwell–Garnett, under an annotation reading
        `(certified)`, with this check reporting 'stored output matches a fresh run'."""
        base = [1.0 + i for i in range(12)]
        wrong = [1.0 + 3 * i for i in range(12)]
        r = self._run(tmp_path, monkeypatch,
                      [_plotly_out("t", base)], [_plotly_out("t", wrong)])
        assert r.passed is False, (
            "a bulk array with genuinely different VALUES passed — the digest has "
            "reverted to a length-only summary (round-9 finding 5.1)")

    def test_a_base64_array_is_digested_not_compared_bytewise(self, tmp_path, monkeypatch):
        """D11 round-8 measurement: Plotly serializes numpy as
        `{"dtype": ..., "bdata": <base64>}`, and `bdata` is a STRING — so without the
        dedicated branch it was compared byte-for-byte while plain lists were
        length-summarised. The discriminator was 'numpy or list at the call site', not
        'claim or not', and 56 bulk curves were being compared to the last bit.

        Both directions in one test: jitter passes, a different curve fails.
        """
        base = [1.0 + i for i in range(12)]
        jittered = [v * (1 + 1e-12) for v in base]   # see the note above on 1e-16
        assert jittered != base, "the jitter fixture is bit-identical — it tests nothing"
        assert self._run(tmp_path, monkeypatch,
                         [_bdata_out(base)], [_bdata_out(jittered)]).passed is True, (
            "a base64 numpy array is being compared byte-for-byte again — a 1e-15 "
            "jitter now fails the check")
        assert self._run(tmp_path, monkeypatch,
                         [_bdata_out(base)],
                         [_bdata_out([1.0 + 3 * i for i in range(12)])]).passed is False

    def test_a_notebook_that_cannot_re_execute_fails(self, tmp_path, monkeypatch):
        import nbclient

        class _Boom:
            def __init__(self, nbobj, **kw):
                pass

            def execute(self):
                raise RuntimeError("kernel died")
        monkeypatch.setattr(nbclient, "NotebookClient", _Boom)
        d = tmp_path / "notebooks"
        d.mkdir(parents=True)
        (d / "D11_x.ipynb").write_text(json.dumps({
            "cells": [], "metadata": {}, "nbformat": 4, "nbformat_minor": 5}))
        monkeypatch.setattr(_H, "NOTEBOOKS_DIR", d)
        assert fr.check_notebook_stored_outputs_current().passed is False


class TestBundleSourceFreshness:
    """Advisory by default; `--strict` promotes WARN to FAIL. That promotion is the
    only behaviour here that a bug could silently disable."""

    def _run(self, monkeypatch, findings, *, strict=False):
        import check_bundle_source_freshness as m
        monkeypatch.setattr(m, "check", lambda: findings)
        monkeypatch.setattr(_cfg, "STRICT_MODE", strict)
        return fr.check_bundle_source_freshness()

    WARN = [{"bundle": "D1", "message": "source newer than last_lift",
             "passed": True, "warning": True}]

    def test_a_warning_passes_in_default_mode(self, monkeypatch):
        """SILENT ON CORRECT DATA — a stale bundle is a Stage-13 signal, not a build
        break, outside the submission gate."""
        assert self._run(monkeypatch, self.WARN).passed is True

    def test_a_warning_fails_under_strict(self, monkeypatch):
        """FIRES ON THE SEEDED DEFECT. `--strict` is the documented Paper Submission
        Gate (ADR-009 §Deferred item 6), and the flag is read by ATTRIBUTE — importing
        it by value would freeze it at import time and make `--strict` a silent
        no-op (H5)."""
        r = self._run(monkeypatch, self.WARN, strict=True)
        assert r.passed is False, (
            "--strict did not promote a freshness WARN to a FAIL — either the "
            "promotion is gone or STRICT_MODE is bound by value (H5)")
        assert "strict mode" in next(d for d in r.details if d.name == "summary").message

    def test_a_hard_finding_fails_in_both_modes(self, monkeypatch):
        hard = [{"bundle": "D1", "message": "broken", "passed": False, "warning": False}]
        assert self._run(monkeypatch, hard).passed is False
        assert self._run(monkeypatch, hard, strict=True).passed is False

    def test_no_findings_is_the_pre_initialization_state(self, monkeypatch):
        r = self._run(monkeypatch, [])
        assert r.passed is True
        assert any(d.name == "scope" for d in r.details)

    def test_an_absent_source_directory_is_UNMEASURABLE_not_fresh(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT. `_latest_source_mtime` returns None for a
        missing directory and the staleness loop skips every None — so a bundle whose
        sources all name absent directories used to fall through to the `else` branch
        and announce "fresh: all 1 source paper(s) older than last_lift" over a
        population of ZERO. Absence of measurement rendered as success, in the
        absorption instrument itself (ADR-010 measurement pass M6, 2026-08-05).
        """
        import check_bundle_source_freshness as m
        papers = tmp_path / "papers"
        (papers / "B1").mkdir(parents=True)
        (papers / "B1" / "bundle_metadata.json").write_text(
            json.dumps({"last_lift": "2026-01-01T00:00:00Z"}))
        monkeypatch.setattr(m, "PAPERS_DIR", papers)
        monkeypatch.setattr(m, "MAPPING_DOC", tmp_path / "map.md")
        (tmp_path / "map.md").write_text("unused — parse_mapping is stubbed")
        monkeypatch.setitem(
            sys.modules, "bundle_migration",
            type(sys)("bundle_migration"))
        sys.modules["bundle_migration"].parse_mapping = (
            lambda _t: {"ghost_source": {"bundle_destinations": ["B1"]}})
        monkeypatch.setitem(sys.modules, "sentence_state", type(sys)("sentence_state"))
        sys.modules["sentence_state"]._VALID_BUNDLE_TARGETS = {"B1"}

        msg = next(f for f in m.check() if f["bundle"] == "B1")["message"]
        assert "UNMEASURABLE" in msg, (
            f"a bundle whose only source names an absent directory reported {msg!r} — "
            f"the vacuous-freshness hole is back")
        assert "fresh:" not in msg

    def test_the_LIVE_corpus_reports_no_vacuous_freshness(self):
        """PRODUCTION-SEEDED (QI-30). Run against the real `papers/` and the real
        `PAPER_DRAFT_MAPPING.md`, because a fixture proves the branch exists, not that
        the corpus reaches it. Nine live bundles (D6-D12, I2, I3) declare sources that
        are synthetic tokens naming no directory; every one of them must say so rather
        than claim freshness.
        """
        import check_bundle_source_freshness as m
        by_bundle = {}
        for f in m.check():
            by_bundle.setdefault(f["bundle"], []).append(f["message"])
        for code in ("D6", "D7", "D8", "D9", "D10", "D11", "D12", "I2", "I3"):
            msgs = by_bundle.get(code)
            if not msgs:                       # pragma: no cover - bundle present in-repo
                continue
            # ⚠️ The prefix is `source-fresh:`, NOT `fresh:`. This read
            # `msg.startswith("fresh:")`, which matches NOTHING the production code
            # emits (`check_bundle_source_freshness.py:685` writes
            # "source-fresh: all N measurable source paper(s) ..."), so the sole
            # assertion of a PRODUCTION-SEEDED test was unfalsifiable.
            assert not any("source-fresh:" in msg for msg in msgs), (
                f"{code} claims freshness, but all of its declared sources name "
                f"directories absent from papers/ — re-derive this test's premise if "
                f"real source directories were finally created for it, rather than "
                f"deleting the assertion")

    def test_an_unavailable_module_fails_rather_than_passes(self, monkeypatch):
        import builtins
        real = builtins.__import__

        def _blocked(name, *a, **k):
            if name == "check_bundle_source_freshness":
                raise ImportError("gone")
            return real(name, *a, **k)
        monkeypatch.setattr(builtins, "__import__", _blocked)
        assert fr.check_bundle_source_freshness().passed is False




class TestPathAliasCoupling:
    """The module-level path aliases are the known `test_no_check_module_aliases_a_path`
    gap (BinOp form). Pinning their derivation here means a change shows up as a
    failure rather than as a future test silently writing into the real tree."""

    def test_counts_sources_derive_from_the_helpers(self):
        assert _H.LEAN_DEPS_PATH in fr._COUNTS_SOURCES
        assert all(p.is_absolute() for p in fr._COUNTS_SOURCES)

    def test_claim_clusters_path_sits_under_papers(self):
        assert fr.claim_clusters_path().parent == _H.PROJECT_ROOT / "papers"
        assert fr.claim_clusters_path().name == "claim_clusters.json"


class TestBundleCountsFresh:
    """`bundle_counts_fresh` — a paper's own substrate figures cannot drift.

    Exists because the PROJECT-wide `\\substantivetheorems` was used for PAPER-scoped
    claims (TODO-D9): E2 stated 26,329 against a verified chain of 6 theorems.
    """

    def test_live_tree_is_fresh(self):
        assert fr.check_bundle_counts_fresh().passed

    def test_a_hand_edited_count_is_stale(self, tmp_path, monkeypatch):
        import render_bundle_counts as rbc
        monkeypatch.setattr(rbc, "build", lambda: {"D1": "\\newcommand{\\bundleTheorems}{7}\n"})
        papers = tmp_path / "papers"; (papers / "D1").mkdir(parents=True)
        (papers / "D1" / "bundle_counts.tex").write_text("\\newcommand{\\bundleTheorems}{999}\n")
        monkeypatch.setattr(_H, "PAPERS_DIR", papers)
        r = fr.check_bundle_counts_fresh()
        assert not r.passed and any(d.name == "stale:D1" for d in r.details)

    def test_a_missing_file_for_a_DECLARED_bundle_fails(self, tmp_path, monkeypatch):
        import render_bundle_counts as rbc
        monkeypatch.setattr(rbc, "build", lambda: {"D1": "\\newcommand{\\bundleTheorems}{7}\n"})
        papers = tmp_path / "papers"; (papers / "D1").mkdir(parents=True)
        monkeypatch.setattr(_H, "PAPERS_DIR", papers)
        r = fr.check_bundle_counts_fresh()
        assert not r.passed and any(d.name == "missing:D1" for d in r.details)

    def test_an_UNDECLARED_bundle_emits_no_file_and_that_is_not_a_failure(self, tmp_path, monkeypatch):
        """PINS THE DESIGN: substrate UNKNOWN is not substrate ZERO. Emitting 0 would put
        a confident wrong number in a manuscript."""
        import render_bundle_counts as rbc
        monkeypatch.setattr(rbc, "build",
                            lambda: {"D1": "\\newcommand{\\bundleTheorems}{7}\n", "D2": None})
        papers = tmp_path / "papers"
        (papers / "D1").mkdir(parents=True); (papers / "D2").mkdir(parents=True)
        (papers / "D1" / "bundle_counts.tex").write_text("\\newcommand{\\bundleTheorems}{7}\n")
        monkeypatch.setattr(_H, "PAPERS_DIR", papers)
        r = fr.check_bundle_counts_fresh()
        assert r.passed and any(d.name == "undeclared" for d in r.details)

    def test_an_empty_population_is_UNVERIFIED_not_fresh(self, tmp_path, monkeypatch):
        import render_bundle_counts as rbc
        monkeypatch.setattr(rbc, "build", lambda: {"D1": None})
        monkeypatch.setattr(_H, "PAPERS_DIR", tmp_path / "papers")
        r = fr.check_bundle_counts_fresh()
        assert not r.passed and not r.measured


class TestTheShellDecider:
    """ADR-013 D5. Shell has no AST, so the census needs a second decider — and a decider
    is exactly the thing this repository keeps getting wrong by substituting a proxy.

    The rule is the LEADING comment block only. Scanning a whole script for comments would
    call any script with an explanatory note "described", which is the false positive the
    Python leg avoids by using `ast.get_docstring` rather than a source regex.
    """

    @property
    def _mc(self):
        import module_census
        return module_census

    def test_the_leading_block_is_taken(self):
        assert self._mc._shell_header("#!/usr/bin/env bash\n# Does a thing.\n# In two lines.\n\nset -e\n") \
            == "Does a thing.\nIn two lines."

    def test_a_script_with_no_shebang_still_works(self):
        assert self._mc._shell_header("# Just a header.\nset -e\n") == "Just a header."

    def test_a_comment_AFTER_code_is_NOT_a_description(self):
        """THE FALSE POSITIVE THIS BOUNDING EXISTS TO PREVENT."""
        assert self._mc._shell_header("#!/bin/bash\nset -e\n# an explanatory note mid-file\n") is None

    def test_a_script_with_only_a_shebang_is_undescribed(self):
        assert self._mc._shell_header("#!/bin/bash\nset -e\n") is None

    def test_the_block_stops_at_the_first_non_comment(self):
        assert self._mc._shell_header("#!/bin/bash\n# One.\nset -e\n# Two.\n") == "One."

    def test_the_four_real_scripts_are_all_described(self):
        """Measured before the walk widened. The ceiling holds at 4 BECAUSE these are
        described — had one lacked a header the fix would be writing it, never raising
        the ceiling to admit it (a ratchet is scoped by its population predicate)."""
        data = self._mc.collect()
        sh = [r for r, _ in data["documented"] if r.endswith(".sh")]
        assert len(sh) == 4, f"expected 4 described shell scripts, got {sh}"
        assert not [r for r, _ in data["undocumented"] if r.endswith(".sh")]

    def test_shell_is_actually_walked(self):
        """SEAM GUARD. If the glob silently stopped matching `*.sh`, every leg above
        would still pass on synthetic strings while the census covered nothing."""
        assert any(r.endswith(".sh") for r, _ in self._mc.collect()["documented"])


class TestTheNotebookDecider:
    """ADR-013 D3. Measured 2026-08-13: 91 of 91 notebooks already open with a markdown
    heading, so this ENCODES a universal convention rather than imposing a new one —
    which is why adopting it moved no ceiling."""

    @property
    def _mc(self):
        import module_census
        return module_census

    def test_heading_plus_prose_becomes_the_description(self):
        assert self._mc._notebook_header("# D11 — Band Theory\n\nCompanion to the draft.") \
            == "D11 — Band Theory — Companion to the draft."

    def test_a_bare_heading_is_enough(self):
        assert self._mc._notebook_header("# Just A Title") == "Just A Title"

    def test_rule_lines_do_not_reach_the_published_row(self):
        """The wall-of-`=` defect, in the notebook leg."""
        out = self._mc._notebook_header("# Title\n=======\n\nReal prose.")
        assert "=" not in out and out.endswith("Real prose.")

    def test_an_empty_cell_is_no_description(self):
        assert self._mc._notebook_header("   \n\n") is None

    def test_the_real_corpus_is_fully_described(self):
        data = self._mc.collect()
        nb = [r for r, _ in data["documented"] if r.endswith(".ipynb")]
        assert len(nb) == 91, f"expected 91 described notebooks, got {len(nb)}"
        assert not [r for r, _ in data["undocumented"] if r.endswith(".ipynb")]

    def test_checkpoints_are_not_double_counted(self):
        """`.ipynb_checkpoints` holds stale copies under near-identical names."""
        assert not [r for r, _ in self._mc.collect()["documented"]
                    if ".ipynb_checkpoints" in r]

    def test_notebooks_are_actually_walked(self):
        """SEAM GUARD — without it the legs above pass on synthetic strings while the
        census covers no notebook at all."""
        assert any(r.endswith(".ipynb") for r, _ in self._mc.collect()["documented"])


class TestModuleCensusFresh:
    """PRODUCTION-SEEDED (guide §2.4): every mutation writes into the REAL tree — a real
    module's docstring, or the real `docs/MODULE_CENSUS.md` — and restores in a `finally`.

    ADR-013. The census replaces two hand-maintained files whose narrative drifted while
    their generated blocks stayed fresh. The legs below are what makes that trade safe:
    the artifact must match a fresh derivation, and the population the census CANNOT
    describe must not grow.
    """

    @staticmethod
    def _mod():
        import module_census
        return module_census

    def _leg(self, name):
        return next(d for d in fr.check_module_census_fresh().details if d.name == name)

    def test_the_live_tree_is_green_on_every_leg(self):
        r = fr.check_module_census_fresh()
        assert r.passed and r.measured
        assert {"population", "census_fresh", "undocumented_modules"} == {
            d.name for d in r.details}

    def test_the_ratchet_has_zero_headroom(self):
        """Guide §2.3 — a ceiling above the live population cannot fire."""
        assert not any(d.name == "ratchet_slack"
                       for d in fr.check_module_census_fresh().details)

    def test_a_changed_docstring_makes_the_census_stale_in_production(self):
        """FIRES ON THE SEEDED DEFECT — the leg that catches a description drifting away
        from the module it describes, which is the whole failure the hand files had."""
        mc = self._mod()
        target = mc.PROJECT_ROOT / "src" / "core" / "transonic_background.py"
        orig = target.read_text(encoding="utf-8")
        try:
            target.write_text(orig.replace(
                "Transonic Background Solver", "SEEDED DEFECT Solver", 1), encoding="utf-8")
            leg = self._leg("census_fresh")
            assert not leg.passed and "STALE" in (leg.message or "")
        finally:
            target.write_text(orig, encoding="utf-8")

    def test_removing_a_real_docstring_trips_the_ratchet(self):
        """FIRES ON THE SEEDED DEFECT. ⚠️ The ratchet reads SOURCE, not the rendered
        artifact — a leg keyed on the artifact would be satisfied by the regeneration that
        introduced the regression, because the artifact always agrees with itself."""
        mc = self._mod()
        target = mc.PROJECT_ROOT / "src" / "core" / "transonic_background.py"
        orig = target.read_text(encoding="utf-8")
        tree = ast.parse(orig)
        node = tree.body[0]
        assert isinstance(node, ast.Expr) and isinstance(node.value, ast.Constant), (
            "fixture assumption broken: the target module has no docstring")
        try:
            # Drop the docstring by its AST line span rather than by matching the literal —
            # quoting style and escapes make a text match fragile, and a seed that silently
            # fails to apply is a mutation test that proves nothing.
            lines = orig.splitlines(keepends=True)
            del lines[node.lineno - 1:node.end_lineno]
            target.write_text("".join(lines), encoding="utf-8")
            assert ast.get_docstring(ast.parse(target.read_text(encoding="utf-8"))) is None
            leg = self._leg("undocumented_modules")
            assert not leg.passed
            assert f"{fr._NO_DOCSTRING_CEILING + 1} module(s)" in (leg.message or "")
        finally:
            target.write_text(orig, encoding="utf-8")

    def test_a_walk_that_reaches_nothing_is_UNMEASURED_not_clean(self, monkeypatch):
        """Guide §2.5 — the seam. A scan over an empty population passes vacuously; that
        must read as UNVERIFIED rather than as a clean bill."""
        monkeypatch.setattr(self._mod(), "TREES", ("no_such_tree",))
        r = fr.check_module_census_fresh()
        assert not r.passed and not r.measured
        assert "vacuously" in (r.details[0].message or "")

    def test_the_census_states_its_scope_on_its_face(self):
        """ADR-013 D1b. An unstated boundary is how the next hand catalogue gets started."""
        mc = self._mod()
        text = mc.render(mc.collect())
        assert "**Scope: Python, shell and notebooks**" in text
        assert "lean.module_names" in text, "the header must name where Lean is answered"

    def test_undocumented_modules_are_named_not_merely_counted(self):
        """ADR-013 D3 — a surface silent about its blind spot reads as complete."""
        mc = self._mod()
        data = mc.collect()
        text = mc.render(data)
        assert "## Modules this census cannot describe" in text
        for rel, _ in data["undocumented"]:
            assert f"`{rel}`" in text, f"{rel} is counted but not named"
