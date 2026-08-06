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

import base64
import json
import struct
import sys
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
            assert not any(msg.startswith("fresh:") for msg in msgs), (
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


class TestInventoryIndexAutogenFresh:
    """ADVISORY BY DESIGN (ADR-009 §Deferred item 3 — kept, because `sync.py --fast`
    regenerates it on every commit so staleness is transient by construction). The two
    directions are therefore on the WARNING."""

    def _run(self, monkeypatch, result):
        import update_inventory_index as m
        monkeypatch.setattr(m, "compute_stale", lambda: result)
        return fr.check_inventory_index_autogen_fresh()

    def test_it_stays_advisory(self, monkeypatch):
        """Pins the disposition — changing it must update ADR-009 item 3 too."""
        assert self._run(monkeypatch, (True, "3 blocks stale")).passed is True

    def test_staleness_warns(self, monkeypatch):
        """FIRES ON THE SEEDED DEFECT (as a warning)."""
        d = self._run(monkeypatch, (True, "3 blocks stale")).details[0]
        assert d.warning and "stale" in (d.message or "")
        assert "update_inventory_index" in (d.message or ""), (
            "the warning must name the one command that fixes it")

    def test_a_fresh_index_does_not_warn(self, monkeypatch):
        """SILENT ON CORRECT DATA."""
        d = self._run(monkeypatch, (False, "all blocks current")).details[0]
        assert not d.warning

    def test_a_raising_generator_never_fails_the_suite(self, monkeypatch):
        """Deliberately defensive: an advisory must not be able to break a build."""
        import update_inventory_index as m

        def _boom():
            raise RuntimeError("bad")
        monkeypatch.setattr(m, "compute_stale", _boom)
        r = fr.check_inventory_index_autogen_fresh()
        assert r.passed is True and r.details[0].warning


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
