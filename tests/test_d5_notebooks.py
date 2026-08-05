"""D5 both-directions tests for `validation/checks/notebooks.py` — audit QI-27.

Three checks: `notebooks` (no re-implemented physics), `viz_consistency` (advisory), and
`notebook_exec` (every notebook runs clean, behind a content-hash skip-cache).

WHAT "BOTH DIRECTIONS" MEANS FOR AN ADVISORY CHECK
---------------------------------------------------
`viz_consistency` is **deliberately always-pass** — ADR-009 §Deferred item 3 dispositioned
it individually and KEPT it advisory, because it grades authoring style in exploratory
notebooks while the artifacts that actually ship are gated by `bundle_figure_integrity`,
which can fail.

So its D5 obligation is not "make it fail". A check whose verdict is constant still has a
measurable output, and here it is the WARNING. The tests below assert that a seeded defect
produces the warning and clean input does not — the same two directions, one level down
from `passed`. Asserting `passed is True` would be vacuous by construction, and asserting
`passed is False` would be demanding a behaviour change the ADR declined.

⚠️ `NOTEBOOK_EXEC_CACHE` is a MODULE-LEVEL path built from `_H.NOTEBOOKS_DIR` at import
time, so monkeypatching `_H.NOTEBOOKS_DIR` alone does not move it. That is the `X = _H.NAME
/ "y"` BinOp form which `test_no_check_module_aliases_a_path` documents in its own
assertion message as a known gap — see the audit's §4 residuals. These tests patch both,
and `test_the_cache_path_is_derived_from_the_notebooks_dir` pins the coupling so the two
cannot silently drift apart.

MUTATION-VERIFIED 2026-08-04 — 6 mutations, all CAUGHT, clean negative control.

  | mutation                                                     | caught by |
  |---|---|
  | `notebooks`: `ok = len(violations) == 0` -> `ok = True`       | `…redefines…` |
  | `notebooks`: the parse-error branch -> `pass`                 | `…unparseable…` |
  | `viz_consistency`: drop the untagged-`.show()` warning        | `…untagged_show…` |
  | `viz_consistency`: drop the hardcoded-hex warning             | `…hardcoded_color…` |
  | `notebook_exec`: the per-notebook skip -> never skip           | `…skipped_on_the_second_run…` |
  | `notebook_exec`: `new_passed[...] = code_hash` -> `pass`       | `…skipped_on_the_second_run…` |

⚠️ **A SEVENTH MUTATION WAS MISSED, AND IT IS *NOT* A DEFECT — recorded so nobody
re-derives it.** Dropping `and not _cfg.FORCE_NOTEBOOK_REEXEC` from the cache-LOAD
condition (`if NOTEBOOK_EXEC_CACHE.is_file() and not _cfg.FORCE_NOTEBOOK_REEXEC:`)
fails no test, and should not: the per-notebook skip fifteen lines below is
independently FORCE-gated, so loading `prev_passed` under `--force-notebooks` cannot
change any verdict. The conjunct is a redundant I/O short-circuit — it avoids reading
a file whose contents will be ignored.

It is deliberately LEFT IN PLACE rather than deleted, which is the opposite call from
audit QI-03 (where a redundant guard inside a fix being authored was removed). The
distinction that matters: that one was dead code in new work, and this is pre-existing
production code whose redundancy is a cheap, legible defence. Neither is claimed as
mutation-verified — an unverifiable line should not be counted as verified in either
direction.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT / "scripts"))
sys.path.insert(0, str(SK_ROOT))

import validate_helpers as _H  # noqa: E402
from validation import _config as _cfg  # noqa: E402
from validation.checks import notebooks as nb  # noqa: E402


def _nb_json(cells: list[str]) -> str:
    # `id` is required from nbformat 4.5; omitting it emits MissingIDFieldWarning on
    # every read. Deterministic (index-based), never random — a fixture that varies
    # run to run makes a content-hash test meaningless.
    return json.dumps({
        "cells": [{"cell_type": "code", "source": [c], "metadata": {},
                   "id": f"cell{i}", "execution_count": None, "outputs": []}
                  for i, c in enumerate(cells)],
        "metadata": {"kernelspec": {"name": "python3", "language": "python",
                                    "display_name": "Python 3"},
                     "language_info": {"name": "python"}},
        "nbformat": 4, "nbformat_minor": 5,
    })


def _notebooks(tmp_path: Path, monkeypatch, files: dict[str, str]) -> Path:
    d = tmp_path / "notebooks"
    d.mkdir(parents=True, exist_ok=True)
    for name, body in files.items():
        (d / name).write_text(body)
    monkeypatch.setattr(_H, "NOTEBOOKS_DIR", d)
    monkeypatch.setattr(nb, "NOTEBOOK_EXEC_CACHE", d / ".notebook_exec_cache.json")
    return d


class TestNotebookIsolation:
    """Invariant #1 at the notebook boundary: physics lives in `src.core` and is
    IMPORTED, never re-implemented in a notebook where it can drift unseen."""

    def test_a_clean_notebook_passes(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA."""
        _notebooks(tmp_path, monkeypatch,
                   {"a.ipynb": _nb_json(["from src.core.formulas import damping_rate\n"])})
        r = nb.check_notebook_isolation()
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]
        assert r.details, "the check reported success having scanned nothing"

    def test_a_notebook_redefining_physics_fails(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — a local `def damping_rate(...)` is a second
        implementation that no cross-path check can see."""
        _notebooks(tmp_path, monkeypatch,
                   {"a.ipynb": _nb_json(["def damping_rate(k, w):\n    return 0.0\n"])})
        r = nb.check_notebook_isolation()
        assert r.passed is False, (
            "a notebook redefining `damping_rate` passed — `formulas.py is canonical` "
            "is unenforced at the notebook boundary")
        assert any("redefines" in (d.message or "") for d in r.details)

    def test_merely_calling_the_function_is_not_a_redefinition(self, tmp_path, monkeypatch):
        """The predicate is `def NAME(`, not the bare name — otherwise every correct
        notebook that USES the physics would be flagged."""
        _notebooks(tmp_path, monkeypatch,
                   {"a.ipynb": _nb_json(["result = damping_rate(1.0, 2.0)\n"])})
        assert nb.check_notebook_isolation().passed is True

    def test_a_markdown_cell_is_not_scanned(self, tmp_path, monkeypatch):
        """Prose describing `def damping_rate(...)` is documentation, not code."""
        payload = json.dumps({
            "cells": [{"cell_type": "markdown",
                       "source": ["We could write `def damping_rate(k, w):` here.\n"],
                       "metadata": {}}],
            "metadata": {}, "nbformat": 4, "nbformat_minor": 5})
        _notebooks(tmp_path, monkeypatch, {"a.ipynb": payload})
        assert nb.check_notebook_isolation().passed is True

    def test_an_unparseable_notebook_fails_rather_than_passes(self, tmp_path, monkeypatch):
        """Cannot-measure is not success — a corrupt notebook is unvetted, not clean."""
        _notebooks(tmp_path, monkeypatch, {"a.ipynb": "{not json"})
        r = nb.check_notebook_isolation()
        assert r.passed is False
        assert any("Parse error" in (d.message or "") for d in r.details)


class TestVizConsistency:
    """ADVISORY BY DESIGN (ADR-009 §Deferred item 3 — kept). The verdict is constant,
    so these tests assert the WARNING, which is the check's real output."""

    def test_it_stays_advisory(self, tmp_path, monkeypatch):
        """Pins the disposition itself. If this check ever starts failing, that is a
        deliberate decision that must update ADR-009 §Deferred item 3 and
        `test_cannot_measure_baseline.py` — not a drive-by tightening."""
        _notebooks(tmp_path, monkeypatch,
                   {"a.ipynb": _nb_json(["fig.show()\n"])})
        assert nb.check_viz_consistency().passed is True, (
            "viz_consistency started failing. That may be right, but ADR-009 "
            "§Deferred item 3 dispositioned it as advisory with a stated reason — "
            "update the ADR and this test together.")

    def test_an_untagged_show_warns(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT (as a warning) — an untracked figure."""
        _notebooks(tmp_path, monkeypatch, {"a.ipynb": _nb_json(["fig.show()\n"])})
        d = next(d for d in nb.check_viz_consistency().details if d.name == "a.ipynb")
        assert d.warning and "untagged .show()" in (d.message or ""), (
            f"expected an untagged-.show() warning, got {d.message!r}")

    def test_a_tagged_show_is_clean(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA — the opt-in tag is the whole point of the safety net."""
        _notebooks(tmp_path, monkeypatch,
                   {"a.ipynb": _nb_json(["# viz-ref: fig_spectrum\nfig.show()\n"])})
        d = next(d for d in nb.check_viz_consistency().details if d.name == "a.ipynb")
        assert not d.warning or "untagged" not in (d.message or "")

    def test_a_viz_ref_naming_no_function_warns(self, tmp_path, monkeypatch):
        """A tag pointing at a function that does not exist is worse than no tag: it
        reads as tracked while tracking nothing."""
        src = tmp_path / "src"
        (src / "core").mkdir(parents=True, exist_ok=True)
        (src / "core" / "visualizations.py").write_text("def fig_real():\n    pass\n")
        monkeypatch.setattr(_H, "SRC_DIR", src)
        _notebooks(tmp_path, monkeypatch,
                   {"a.ipynb": _nb_json(["# viz-ref: fig_ghost\nfig.show()\n"])})
        d = next(d for d in nb.check_viz_consistency().details if d.name == "a.ipynb")
        assert d.warning and "fig_ghost" in (d.message or "")

    def test_a_hardcoded_colors_hex_warns(self, tmp_path, monkeypatch):
        """Invariant #3: `visualizations.py` owns the palette. A literal that MATCHES a
        COLORS value is a copy that will not follow the palette when it changes."""
        from src.core.constants import COLORS
        known = next(v for v in COLORS.values() if isinstance(v, str) and v.startswith("#"))
        _notebooks(tmp_path, monkeypatch,
                   {"a.ipynb": _nb_json([f'c = "{known}"\n'])})
        d = next(d for d in nb.check_viz_consistency().details if d.name == "a.ipynb")
        assert d.warning and "hardcoded COLORS hex" in (d.message or "")

    def test_an_unrelated_hex_does_not_warn(self, tmp_path, monkeypatch):
        """Only hexes that duplicate a COLORS entry are flagged — an arbitrary colour
        is an authoring choice, not a palette copy."""
        _notebooks(tmp_path, monkeypatch, {"a.ipynb": _nb_json(['c = "#123456"\n'])})
        d = next(d for d in nb.check_viz_consistency().details if d.name == "a.ipynb")
        assert "hardcoded" not in (d.message or "")


class _FakeClient:
    """Stand-in for `nbclient.NotebookClient`. Executing real notebooks here would
    make the D5 test as slow as the check it guards (~25 min), and the thing under
    test is the CACHE and FLAG logic, not nbclient."""
    raised = None

    def __init__(self, nbobj, **kw):
        self.nb = nbobj

    def execute(self):
        if _FakeClient.raised:
            raise RuntimeError(_FakeClient.raised)


class TestNotebookExecution:
    """The skip-cache and the `--force-notebooks` flag. The cache is what makes this
    check affordable; a broken cache either re-runs everything (~25 min) or, worse,
    skips a notebook that changed."""

    def setup_method(self):
        _FakeClient.raised = None

    def _run(self, tmp_path, monkeypatch, files, *, force=False):
        import nbclient
        monkeypatch.setattr(nbclient, "NotebookClient", _FakeClient)
        monkeypatch.setattr(_cfg, "FORCE_NOTEBOOK_REEXEC", force)
        _notebooks(tmp_path, monkeypatch, files)
        return nb.check_notebook_execution()

    NB = _nb_json(["1 + 1\n"])

    def test_a_clean_notebook_passes(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA."""
        r = self._run(tmp_path, monkeypatch, {"a.ipynb": self.NB})
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_a_failing_notebook_fails(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT."""
        _FakeClient.raised = "NameError: name 'undefined_symbol' is not defined"
        r = self._run(tmp_path, monkeypatch, {"a.ipynb": self.NB})
        assert r.passed is False, "a notebook that raised during execution passed"
        assert any("NameError" in (d.message or "") for d in r.details)

    def test_a_failing_notebook_is_not_recorded_as_vetted(self, tmp_path, monkeypatch):
        """The subtle half: a failure must NOT enter the skip-cache, or the next run
        skips it and the failure disappears until someone edits the notebook."""
        _FakeClient.raised = "ValueError: boom"
        self._run(tmp_path, monkeypatch, {"a.ipynb": self.NB})
        cache = json.loads(nb.NOTEBOOK_EXEC_CACHE.read_text())
        assert cache["passed"] == {}, (
            f"a FAILED notebook was recorded as vetted ({cache['passed']}) — the next "
            f"run would skip it and the failure would vanish")

    def test_an_unchanged_notebook_is_skipped_on_the_second_run(self, tmp_path, monkeypatch):
        """The cache hit. Without it this check re-executes ~89 notebooks every run
        and becomes the dominant cost of `validate.py`."""
        self._run(tmp_path, monkeypatch, {"a.ipynb": self.NB})
        r = self._run(tmp_path, monkeypatch, {"a.ipynb": self.NB})
        assert any(d.name == "skip_cache" for d in r.details), (
            "the second run did not skip an unchanged, previously-vetted notebook — "
            "the skip-cache is not being consulted")

    def test_the_force_flag_bypasses_the_cache(self, tmp_path, monkeypatch):
        """ADR-009 H5. The flag is read by ATTRIBUTE on `_config`; a `from _config
        import FORCE_NOTEBOOK_REEXEC` would bind a copy at import time and the flag
        would silently become a no-op — meaning `--force-notebooks` would return a
        cache verdict without executing anything."""
        self._run(tmp_path, monkeypatch, {"a.ipynb": self.NB})
        r = self._run(tmp_path, monkeypatch, {"a.ipynb": self.NB}, force=True)
        assert not any(d.name == "skip_cache" for d in r.details), (
            "--force-notebooks did not bypass the skip-cache — the flag is bound by "
            "value somewhere (H5)")

    def test_a_changed_notebook_is_re_executed(self, tmp_path, monkeypatch):
        """The cache is keyed on a CODE hash, so an edit must invalidate it."""
        self._run(tmp_path, monkeypatch, {"a.ipynb": self.NB})
        r = self._run(tmp_path, monkeypatch, {"a.ipynb": _nb_json(["2 + 2\n"])})
        assert not any(d.name == "skip_cache" for d in r.details)

    def test_a_src_core_change_invalidates_the_whole_cache(self, tmp_path, monkeypatch):
        """A `formulas.py`/`constants.py` edit can change notebook OUTCOMES without
        changing notebook CONTENT — so the fingerprint covers `src/core`, not just the
        notebook. Without this the cache would vouch for stale results after a
        physics change, which is the worst failure this cache could have."""
        src = tmp_path / "src"
        (src / "core").mkdir(parents=True, exist_ok=True)
        (src / "core" / "formulas.py").write_text("A = 1\n")
        monkeypatch.setattr(_H, "SRC_DIR", src)
        self._run(tmp_path, monkeypatch, {"a.ipynb": self.NB})
        (src / "core" / "formulas.py").write_text("A = 2\n")
        r = self._run(tmp_path, monkeypatch, {"a.ipynb": self.NB})
        assert not any(d.name == "skip_cache" for d in r.details), (
            "a src/core edit did not invalidate the notebook skip-cache — notebooks "
            "would be vouched for against physics they never ran against")

    def test_the_cache_path_is_derived_from_the_notebooks_dir(self):
        """Pins the `NOTEBOOK_EXEC_CACHE = _H.NOTEBOOKS_DIR / …` coupling.

        This module-level BinOp is the known gap in
        `test_no_check_module_aliases_a_path` (documented in that guard's own assertion
        message; audit §4 residuals). It is benign in production because paths are never
        reassigned — but a test that patches only `_H.NOTEBOOKS_DIR` would write the
        cache into the REAL notebooks directory. Asserting the relationship here means
        that if the derivation changes, this fails rather than a future test silently
        polluting the repo.
        """
        assert nb.NOTEBOOK_EXEC_CACHE.parent == _H.NOTEBOOKS_DIR
        assert nb.NOTEBOOK_EXEC_CACHE.name == ".notebook_exec_cache.json"
