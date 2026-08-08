"""`compile_bundle_pdf.py`'s recompile skip (ADR-011 Phase 2b, operator-approved).

The script recompiled all 64 drafts unconditionally on every run, so every run
dirtied ~45 tracked PDFs whether or not anything had changed.

**The whole risk of a skip is that skipping asserts the gate passed.** These tests
are therefore weighted toward the refusals: a draft that FAILS the gate must never
become skippable, because its PDF is perfectly fresh and a naive mtime check would
report it `SKIPPED` and count it as passing forever after.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))

import compile_bundle_pdf as cbp  # noqa: E402


@pytest.fixture
def draft(tmp_path, monkeypatch):
    """A draft dir with a fresh PDF and a recorded PASS — the skippable state."""
    monkeypatch.setattr(cbp, "REPO", tmp_path)
    papers = tmp_path / "papers"
    d = papers / "D1"
    d.mkdir(parents=True)
    (d / "paper_draft.tex").write_text(r"\documentclass{article}\begin{document}x\end{document}")
    (d / "paper_draft.pdf").write_bytes(b"%PDF-1.4")
    (tmp_path / cbp.GATE_CACHE).write_text(json.dumps({"D1": {"ok": True, "pages": 3}}))
    return d


def _set_verdict(tmp_path, payload):
    (tmp_path / cbp.GATE_CACHE).write_text(payload)


def _touch_newer(path: Path, ref: Path):
    import os
    import time
    os.utime(path, (time.time() + 10, time.time() + 10))
    assert path.stat().st_mtime > ref.stat().st_mtime


class TestWhenItSkips:
    def test_a_fresh_pdf_with_a_recorded_pass_is_skipped(self, draft):
        skip, pages = cbp._up_to_date(draft, draft / "paper_draft.tex")
        assert skip

    def test_the_skip_reports_a_page_count(self, draft, monkeypatch):
        monkeypatch.setattr(cbp, "_pdf_pages", lambda p: 42)
        assert cbp._up_to_date(draft, draft / "paper_draft.tex") == (True, 42)


class TestWhenItRefusesToSkip:
    def test_a_recorded_FAILURE_is_never_skipped(self, tmp_path, draft):
        """THE LOAD-BEARING TEST. D3 fails the gate with 3 unresolved references and
        its PDF is perfectly fresh. Without this, the second run onward reports it
        SKIPPED and counts it as passing — a standing FAIL silently becomes a PASS."""
        _set_verdict(tmp_path, json.dumps({"D1": {"ok": False, "pages": 3}}))
        skip, _ = cbp._up_to_date(draft, draft / "paper_draft.tex")
        assert not skip

    def test_no_recorded_verdict_is_never_skipped(self, tmp_path, draft):
        """Absent is UNKNOWN, not pass. A first run, or a blob predating the field,
        has no basis on which to assert the gate passed."""
        _set_verdict(tmp_path, json.dumps({}))
        assert not cbp._up_to_date(draft, draft / "paper_draft.tex")[0]

    def test_an_unreadable_cache_is_never_skipped(self, tmp_path, draft):
        _set_verdict(tmp_path, "{ not json")
        assert not cbp._up_to_date(draft, draft / "paper_draft.tex")[0]

    def test_a_missing_cache_is_never_skipped(self, tmp_path, draft):
        (tmp_path / cbp.GATE_CACHE).unlink()
        assert not cbp._up_to_date(draft, draft / "paper_draft.tex")[0]

    def test_a_LEGACY_draft_with_no_bundle_metadata_can_still_skip(self, tmp_path, draft):
        """The 43 legacy drafts have no `bundle_metadata.json`. Keying the skip off
        that blob meant two-thirds of the corpus recompiled forever — and pdflatex
        stamps a creation date, so every recompile rewrote the bytes."""
        assert not (draft / "bundle_metadata.json").exists(), "precondition"
        assert cbp._up_to_date(draft, draft / "paper_draft.tex")[0]

    def test_a_stale_pdf_is_never_skipped(self, draft):
        _touch_newer(draft / "paper_draft.tex", draft / "paper_draft.pdf")
        assert not cbp._up_to_date(draft, draft / "paper_draft.tex")[0]

    def test_a_newer_INPUT_defeats_the_skip_not_just_the_tex(self, draft):
        r"""The closure, not the `.tex` alone — an edited `\input`ed table changes the
        compiled output while the `.tex` mtime stands still."""
        tex = draft / "paper_draft.tex"
        (draft / "tables").mkdir()
        inc = draft / "tables" / "t1.tex"
        inc.write_text("row")
        tex.write_text(r"\documentclass{article}\begin{document}"
                       r"\input{tables/t1.tex}\end{document}")
        (draft / "paper_draft.pdf").write_bytes(b"%PDF-1.4")   # newer than both
        assert cbp._up_to_date(draft, tex)[0], "precondition: skippable"
        _touch_newer(inc, draft / "paper_draft.pdf")
        assert not cbp._up_to_date(draft, tex)[0], "an input moved; must recompile"

    def test_a_missing_pdf_is_never_skipped(self, draft):
        (draft / "paper_draft.pdf").unlink()
        assert not cbp._up_to_date(draft, draft / "paper_draft.tex")[0]


class TestForce:
    def test_force_bypasses_the_skip_entirely(self, draft, monkeypatch):
        """The operator's condition on approving the skip: it must be overridable."""
        called = []
        monkeypatch.setattr(cbp, "_up_to_date",
                            lambda *a: (called.append(1), (True, 1))[1])
        monkeypatch.setattr(cbp.shutil, "which", lambda n: None)  # stop before pdflatex
        cbp.compile_one(draft, force=True)
        assert not called, "_up_to_date must not even be consulted under --force"


class TestReproducibleOutput:
    """The skip alone cannot take PDF churn to zero, because a draft that FAILS the
    gate must recompile every run. It stops dirtying the tree only if the recompile
    is byte-reproducible.

    MEASURED before the fix: two back-to-back `--force` compiles of an unchanged D3
    differed in 58 bytes (`/CreationDate` + `/ModDate`), then in 56 more (`/ID`).
    After: zero, across a full `--all --force` of all 64 drafts.
    """

    def test_the_source_date_is_pinned_to_the_input_closure(self, draft):
        env = cbp._reproducible_env(draft / "paper_draft.tex")
        assert env["FORCE_SOURCE_DATE"] == "1"
        newest = int(max(p.stat().st_mtime
                         for p in cbp._H.draft_input_closure(draft / "paper_draft.tex")
                         if p.is_file()))
        assert env["SOURCE_DATE_EPOCH"] == str(newest)

    def test_the_date_is_STABLE_across_calls_on_unchanged_sources(self, draft):
        """The whole point: identical content ⇒ identical stamp ⇒ identical bytes."""
        tex = draft / "paper_draft.tex"
        assert (cbp._reproducible_env(tex)["SOURCE_DATE_EPOCH"]
                == cbp._reproducible_env(tex)["SOURCE_DATE_EPOCH"])

    def test_the_date_MOVES_when_an_input_changes(self, draft):
        """Pinned, not frozen — a real edit must still restamp, or the date would
        become a lie about when the document was last written."""
        tex = draft / "paper_draft.tex"
        before = cbp._reproducible_env(tex)["SOURCE_DATE_EPOCH"]
        _touch_newer(tex, draft / "paper_draft.pdf")
        assert cbp._reproducible_env(tex)["SOURCE_DATE_EPOCH"] != before

    def test_an_unreadable_closure_still_yields_a_usable_env(self, draft, monkeypatch):
        """Never raise out of the env builder — a compile that cannot be made
        reproducible must still compile."""
        monkeypatch.setattr(cbp._H, "draft_input_closure",
                            lambda t, _s=None: (_ for _ in ()).throw(OSError("boom")))
        env = cbp._reproducible_env(draft / "paper_draft.tex")
        assert env["SOURCE_DATE_EPOCH"].isdigit()

    def test_the_trailer_id_is_zeroed_on_the_command_line(self, draft, monkeypatch):
        r"""`\pdftrailerid{}` must be passed per-invocation, not required of every
        draft: pdfTeX derives `/ID` independently of SOURCE_DATE_EPOCH, so without it
        an unchanged draft still rewrites 56 bytes."""
        seen = {}
        monkeypatch.setattr(cbp.shutil, "which", lambda n: "/usr/bin/" + n)
        monkeypatch.setattr(cbp.subprocess, "run",
                            lambda argv, **kw: seen.setdefault("argv", argv))
        cbp.compile_one(draft, force=True)
        joined = " ".join(seen.get("argv", []))
        assert r"\pdftrailerid{}" in joined
        assert "-jobname=paper_draft" in joined, "output must stay paper_draft.pdf"
