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

import pytest

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
    monkeypatch.setattr(nb, "notebook_exec_cache",
                        lambda _d=d: _d / ".notebook_exec_cache.json")
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

    def test_an_edit_OUTSIDE_src_core_invalidates_the_skip_cache(self, tmp_path,
                                                                 monkeypatch):
        """FIRES ON THE SEEDED DEFECT — PR-review R4-I10, fixed 2026-08-05.

        `_src_core_fingerprint` hashed `src/core/*.py` only — **11 of 177 files** —
        while its docstring claimed it covered "the physics the notebooks import".

        MEASURED over all 91 notebooks: they import **26 distinct `src.*` packages**
        across 293 import sites. `src.core` is 215 of them; the other **78 reach
        `src.wkb`, `src.adw`, `src.vestigial`, `src.chirality`, `src.higher_curvature`**
        and 21 more. So editing any of those left every unchanged notebook SKIPPED as
        "previously vetted" while the physics it executes had changed underneath.

        The fingerprint must move when `src/wkb/spectrum.py` moves. This is the QI-01
        scope class one directory over: a fingerprint naming a population narrower than
        the thing it claims to fingerprint.
        """
        src = tmp_path / "src"
        (src / "core").mkdir(parents=True)
        (src / "core" / "constants.py").write_text("C = 1\n")
        (src / "wkb").mkdir(parents=True)
        wkb = src / "wkb" / "spectrum.py"
        wkb.write_text("def spectrum(): return 1\n")
        monkeypatch.setattr(_H, "SRC_DIR", src)
        before = nb._src_core_fingerprint()

        wkb.write_text("def spectrum(): return 2\n")   # physics changed
        after = nb._src_core_fingerprint()
        assert before != after, (
            "an edit to src/wkb/spectrum.py did not move the notebook skip-cache "
            "fingerprint — every unchanged notebook stays 'previously vetted' while "
            "the physics it executes has changed (R4-I10)")


    def test_a_failing_notebook_is_not_recorded_as_vetted(self, tmp_path, monkeypatch):
        """The subtle half: a failure must NOT enter the skip-cache, or the next run
        skips it and the failure disappears until someone edits the notebook."""
        _FakeClient.raised = "ValueError: boom"
        self._run(tmp_path, monkeypatch, {"a.ipynb": self.NB})
        cache = json.loads(nb.notebook_exec_cache().read_text())
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

    def test_the_cache_path_FOLLOWS_a_patched_notebooks_dir(self, tmp_path, monkeypatch):
        """⚠️ STRENGTHENED 2026-08-05 (PR-review pass 2, R3-I5 / R1).

        This asserted the *static* coupling `NOTEBOOK_EXEC_CACHE = _H.NOTEBOOKS_DIR /
        …`, and its own docstring named the reason it had to: the module-level BinOp
        was an import-time COPY, so *"a test that patches only `_H.NOTEBOOKS_DIR`
        would write the cache into the REAL notebooks directory."* The test existed to
        COMPENSATE for the gap rather than to close it.

        The gap is closed — `notebook_exec_cache()` resolves through `_H` at call
        time — so this now asserts the property that was actually wanted: patch the
        anchor, and the cache path follows.
        """
        assert nb.notebook_exec_cache().parent == _H.NOTEBOOKS_DIR
        assert nb.notebook_exec_cache().name == ".notebook_exec_cache.json"
        monkeypatch.setattr(_H, "NOTEBOOKS_DIR", tmp_path / "fixture_notebooks")
        assert nb.notebook_exec_cache().parent == tmp_path / "fixture_notebooks", (
            "the cache path did NOT follow a patched anchor — it is an import-time "
            "copy again, and a test using a fixture would write into the real "
            "notebooks directory")


class TestNotebookCommitHookTarget:
    """Real Git fixtures plus an execution spy, not kernel/science validation.

    Installed hooks and the research checkout are never fixture targets. Actual
    candidate journaled red/restore/green remains a separate ROOT obligation.
    """

    def _fixture_env(self, context=None):
        import os
        # Fixture ONLY: discard every inherited Git selector before any Git write.
        base = {k: v for k, v in os.environ.items() if not k.startswith('GIT_')}
        base.update(GIT_CONFIG_NOSYSTEM='1', GIT_CONFIG_GLOBAL=os.devnull,
                    GIT_CONFIG_SYSTEM=os.devnull, GIT_OPTIONAL_LOCKS='0')
        if context:
            assert set(context) <= {'GIT_DIR', 'GIT_COMMON_DIR', 'GIT_WORK_TREE', 'GIT_INDEX_FILE'}
            for value in context.values():
                assert Path(value).is_absolute() and Path(value).resolve().is_relative_to(self._fixture_root)
            base.update(context)
        return base

    def _git(self, repo, *args, env=None):
        import subprocess
        assert Path(repo).resolve().is_relative_to(self._fixture_root)
        command = ['git', '-c', 'core.hooksPath=' + str(self._fixture_root / 'empty-hooks'),
                   '-c', 'init.templateDir=' + str(self._fixture_root / 'empty-template'), *args]
        result = subprocess.run(command, cwd=repo, env=self._fixture_env(env),
                                capture_output=True, text=True)
        assert result.returncode == 0, (args, result.stderr)
        return result.stdout.rstrip('\n')

    def _case(self, tmp_path, linked=False):
        import os
        import sys
        self._fixture_root = tmp_path.resolve()
        (tmp_path / 'empty-hooks').mkdir()
        (tmp_path / 'empty-template').mkdir()
        primary = tmp_path / "primary"
        primary.mkdir()
        self._git(primary, "init", "-q")
        (primary / "src" / "core").mkdir(parents=True)
        for name in ("src/__init__.py", "src/core/__init__.py", "src/core/constants.py", "src/core/formulas.py"):
            (primary / name).write_text("# Git fixture source, never imported\n")
        (primary / "README").write_text("fixture\n")
        self._git(primary, "add", ".")
        self._git(primary, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                  "commit", "-qm", "fixture")
        candidate = primary
        if linked:
            candidate = tmp_path / "detached candidate"
            self._git(primary, "worktree", "add", "--detach", str(candidate), "HEAD")
        spy = tmp_path / "selected-python-spy"
        spy.write_text("#!" + sys.executable + "\n" +
                       "import json,os,pathlib,sys\n"
                       "c=json.loads(sys.argv[-1]); o=pathlib.Path(c['output'])\n"
                       "with open(os.environ['SPY_LOG'],'a') as f: f.write(json.dumps({'argv':sys.argv[1:6],'cwd':os.getcwd(),'context':c})+'\\n')\n"
                       "(o/'driver.json').write_text(json.dumps({'status':'failed' if os.environ.get('SPY_FAIL') else 'passed','fixture_spy_only':True}))\n"
                       "if os.environ.get('SPY_MUTATE'): (pathlib.Path(c['checkout'])/'src/core/formulas.py').write_text('# mutated during fixture call\\n')\n"
                       "print('controlled one-execution diagnostic',file=sys.stderr)\n"
                       "sys.exit(7 if os.environ.get('SPY_FAIL') else 0)\n")
        spy.chmod(0o755)
        gd = self._git(candidate, "rev-parse", "--absolute-git-dir")
        environment = self._fixture_env({'GIT_DIR': gd})
        environment.update(SKEFT_NOTEBOOK_PYTHON=str(spy),
                           SPY_LOG=str(tmp_path / "calls.jsonl"), TMPDIR=str(tmp_path))
        return primary, candidate, environment

    def _stage(self, candidate, name, env=None):
        path = candidate / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(_nb_json(["# candidate fixture, not executed\n"]))
        self._git(candidate, "add", "--", name, env=env)
        return path

    def _run(self, primary, env, script=None):
        import subprocess
        # Public fixture of a shared caller that already changed cwd. The Git
        # context remains in env; no installed implementation is copied/read.
        return subprocess.run(["bash", str(script or SK_ROOT / "scripts/pre-commit-notebooks.sh")],
                              cwd=primary, env=env, capture_output=True, text=True)

    def _calls(self, env):
        path = Path(env["SPY_LOG"])
        return [json.loads(x) for x in path.read_text().splitlines()] if path.exists() else []

    def test_primary_working_input_and_explicit_interpreter(self, tmp_path):
        primary, candidate, env = self._case(tmp_path)
        name = "notebooks/space and\nnewline.ipynb"
        self._stage(candidate, name)
        result = self._run(primary, env)
        assert result.returncode == 0, result.stderr
        call, = self._calls(env)
        assert call['context']['notebook'] == name
        assert call['context']['checkout'] == str(candidate)
        assert call['cwd'] == str(candidate)
        assert call['argv'] == ['-I', '-B', '-X',
                                'pycache_prefix=' + call['context']['driver_pycache_prefix'], '-c']

    def test_shared_cwd_detached_linked_and_symlink(self, tmp_path):
        primary, candidate, env = self._case(tmp_path, linked=True)
        name = "notebooks/candidate only.ipynb"
        self._stage(candidate, name)
        assert not (primary / name).exists()
        link = tmp_path / "hook-entry-symlink"
        link.symlink_to(SK_ROOT / "scripts/pre-commit-notebooks.sh")
        result = self._run(primary, env, script=link)
        assert result.returncode == 0, result.stderr
        call, = self._calls(env)
        assert call['context']['checkout'] == str(candidate)
        assert call['context']['notebook'] == name
        assert call['cwd'] == str(candidate)

    def test_absolute_alternate_index_is_the_active_population(self, tmp_path):
        import shutil
        primary, candidate, env = self._case(tmp_path, linked=True)
        alternate = tmp_path / "alternate index"
        shutil.copyfile(Path(env['GIT_DIR']) / 'index', alternate)
        env['GIT_INDEX_FILE'] = str(alternate)
        self._stage(candidate, 'alternate.ipynb', env={'GIT_INDEX_FILE': str(alternate)})
        assert not self._git(candidate, 'diff', '--cached', '--name-only')
        result = self._run(primary, env)
        assert result.returncode == 0, result.stderr
        call, = self._calls(env)
        assert call['context']['notebook'] == 'alternate.ipynb'

    def test_no_notebooks_needs_no_scientific_interpreter(self, tmp_path):
        primary, candidate, env = self._case(tmp_path, linked=True)
        env.pop('SKEFT_NOTEBOOK_PYTHON')
        result = self._run(primary, env)
        assert result.returncode == 0, result.stderr
        assert self._calls(env) == []

    def test_absent_or_mismatched_target_refuses_before_empty_success(self, tmp_path):
        primary, candidate, env = self._case(tmp_path, linked=True)
        env['GIT_WORK_TREE'] = str(primary)
        assert self._run(primary, env).returncode == 2
        env.pop('GIT_WORK_TREE')
        env.pop('GIT_DIR')
        assert self._run(primary, env).returncode == 2
        assert self._calls(env) == []

    def test_relative_alternate_index_refuses(self, tmp_path):
        primary, candidate, env = self._case(tmp_path, linked=True)
        env['GIT_INDEX_FILE'] = 'relative index'
        assert self._run(primary, env).returncode == 2
        assert self._calls(env) == []

    def test_partial_notebook_staging_and_missing_file_refuse(self, tmp_path):
        primary, candidate, env = self._case(tmp_path)
        path = self._stage(candidate, 'partial.ipynb')
        path.write_text(_nb_json(['# changed after staging\n']))
        assert self._run(primary, env).returncode == 2
        path.unlink()
        assert self._run(primary, env).returncode == 2
        assert self._calls(env) == []

    def test_unstaged_tracked_source_refuses(self, tmp_path):
        primary, candidate, env = self._case(tmp_path)
        self._stage(candidate, 'source.ipynb')
        (candidate / 'src/core/formulas.py').write_text('# different working source\n')
        assert self._run(primary, env).returncode == 2
        assert self._calls(env) == []

    def test_failure_runs_once_and_retains_output(self, tmp_path):
        primary, candidate, env = self._case(tmp_path)
        self._stage(candidate, 'failure.ipynb')
        env['SPY_FAIL'] = '1'
        result = self._run(primary, env)
        assert result.returncode == 1, result.stderr
        call, = self._calls(env)
        output = Path(call['context']['output'])
        assert 'controlled one-execution diagnostic' in (output / 'stderr.log').read_text()
        assert json.loads((output.parent / 'receipt.json').read_text())['status'] == 'failed'
        assert result.stderr.count('controlled one-execution diagnostic') == 1

    def test_successive_invocations_use_distinct_output_directories(self, tmp_path):
        primary, candidate, env = self._case(tmp_path)
        self._stage(candidate, 'unique.ipynb')
        for _ in range(2):
            result = self._run(primary, env)
            assert result.returncode == 0, result.stderr
        calls = self._calls(env)
        assert len(calls) == 2
        assert calls[0]['context']['output'] != calls[1]['context']['output']


    def test_primary_relative_default_context_is_supported(self, tmp_path):
        primary, candidate, env = self._case(tmp_path)
        self._stage(candidate, 'primary.ipynb')
        env['GIT_DIR'] = '.git'
        env['GIT_INDEX_FILE'] = '.git/index'
        result = self._run(primary, env)
        assert result.returncode == 0, result.stderr
        assert len(self._calls(env)) == 1

    def test_missing_interpreter_refuses_a_nonempty_population(self, tmp_path):
        primary, candidate, env = self._case(tmp_path)
        self._stage(candidate, 'requires interpreter.ipynb')
        env.pop('SKEFT_NOTEBOOK_PYTHON')
        assert self._run(primary, env).returncode == 2
        assert self._calls(env) == []

    def test_hidden_working_source_difference_refuses(self, tmp_path):
        primary, candidate, env = self._case(tmp_path)
        self._stage(candidate, 'source-byte-check.ipynb')
        self._git(candidate, 'update-index', '--assume-unchanged', 'src/core/formulas.py')
        (candidate / 'src/core/formulas.py').write_text('# hidden working difference\n')
        assert self._run(primary, env).returncode == 2
        assert self._calls(env) == []

    def test_broken_reciprocal_link_refuses(self, tmp_path):
        primary, candidate, env = self._case(tmp_path, linked=True)
        (candidate / '.git').write_text('gitdir: /missing-fixture-admin\n')
        assert self._run(primary, env).returncode == 2
        assert self._calls(env) == []

    def test_source_drift_during_execution_refuses_acceptance(self, tmp_path):
        primary, candidate, env = self._case(tmp_path)
        self._stage(candidate, 'drift.ipynb')
        env['SPY_MUTATE'] = '1'
        result = self._run(primary, env)
        assert result.returncode == 2, result.stderr
        assert len(self._calls(env)) == 1
        assert 'changed during execution' in result.stderr


    def test_inherited_git_selectors_cannot_escape_fixture(self, tmp_path, monkeypatch):
        import hashlib
        import shlex
        poison = tmp_path / 'poison'
        poison.mkdir()
        objects = poison / 'objects'
        objects.mkdir()
        hooks = poison / 'hooks'
        hooks.mkdir()
        marker = poison / 'activated'
        command = '#!/bin/sh\nprintf activated > ' + shlex.quote(str(marker)) + '\n'
        for name in ('pre-commit', 'post-checkout'):
            path = hooks / name
            path.write_text(command)
            path.chmod(0o755)
        template = poison / 'template'
        (template / 'hooks').mkdir(parents=True)
        (template / 'hooks/pre-commit').write_text(command)
        (template / 'hooks/pre-commit').chmod(0o755)
        config = poison / 'config'
        config.write_text('[core]\n hooksPath = ' + str(hooks) + '\n')
        original = hashlib.sha256(config.read_bytes()).hexdigest()
        selectors = {'GIT_DIR': str(poison / 'git'), 'GIT_COMMON_DIR': str(poison / 'common'),
                     'GIT_WORK_TREE': str(poison), 'GIT_INDEX_FILE': str(poison / 'index'),
                     'GIT_OBJECT_DIRECTORY': str(objects), 'GIT_ALTERNATE_OBJECT_DIRECTORIES': str(objects),
                     'GIT_TEMPLATE_DIR': str(template), 'GIT_NAMESPACE': 'fixture-poison',
                     'GIT_CONFIG_GLOBAL': str(config), 'GIT_CONFIG_SYSTEM': str(config),
                     'GIT_CONFIG_COUNT': '1', 'GIT_CONFIG_KEY_0': 'core.hooksPath',
                     'GIT_CONFIG_VALUE_0': str(hooks),
                     'GIT_CONFIG_PARAMETERS': "'core.hooksPath=" + str(hooks) + "'"}
        for key, value in selectors.items():
            monkeypatch.setenv(key, value)
        primary, candidate, env = self._case(tmp_path, linked=True)
        self._stage(candidate, 'clean-context.ipynb')
        result = self._run(primary, env)
        assert result.returncode == 0, result.stderr
        assert len(self._calls(env)) == 1
        assert not marker.exists()
        assert list(objects.iterdir()) == []
        assert not (poison / 'index').exists() and not (poison / 'git').exists()
        assert hashlib.sha256(config.read_bytes()).hexdigest() == original
        assert any((primary / '.git/objects').iterdir())
        assert not any(key in env for key in selectors if key not in {'GIT_DIR', 'GIT_CONFIG_GLOBAL', 'GIT_CONFIG_SYSTEM'})

    def test_production_context_preserved_or_refused_without_environment_reset(self, tmp_path):
        primary, candidate, clean = self._case(tmp_path, linked=True)
        self._stage(candidate, 'production-boundary.ipynb')
        cases = [('GIT_OBJECT_DIRECTORY', 'relative-objects'), ('GIT_COMMON_DIR', 'relative-common'),
                 ('GIT_CONFIG_GLOBAL', 'relative-config'), ('GIT_CONFIG_COUNT', '1'),
                 ('GIT_NAMESPACE', 'unsupported-namespace')]
        for key, value in cases:
            env = dict(clean, **{key: value})
            result = self._run(primary, env)
            assert result.returncode == 2, result.stderr
            assert key in result.stderr
            assert self._calls(clean) == []
        config = tmp_path / 'explicit-absolute-empty-config'
        config.write_text('')
        env = dict(clean, GIT_CONFIG_GLOBAL=str(config))
        result = self._run(primary, env)
        assert result.returncode == 0, result.stderr
        assert len(self._calls(clean)) == 1

    def _actual_python(self):
        import os
        import pytest
        if os.environ.get('SKEFT_RUN_NOTEBOOK_HOOK_DRIVER_CONTROLS') != '1':
            pytest.skip('actual driver/kernel controls require a separate ROOT-admitted interval')
        selected = os.environ.get('SKEFT_NOTEBOOK_PYTHON', '')
        assert Path(selected).is_absolute() and Path(selected).is_file() and os.access(selected, os.X_OK)
        return selected

    def test_actual_driver_reads_new_source_despite_stale_timestamp_and_hash_cache(self, tmp_path):
        import hashlib
        import os
        import subprocess
        selected = self._actual_python()
        for mode in ('TIMESTAMP', 'UNCHECKED_HASH'):
            case = tmp_path / mode
            case.mkdir()
            primary, candidate, env = self._case(case)
            module = candidate / 'src/core/cache_probe.py'
            old = "marker = 'old'\n"
            new = "marker = 'new'\n"
            assert len(old) == len(new)
            module.write_text(old)
            stat = module.stat()
            warm = ("import importlib.util,json,py_compile,sys; "
                    "p=sys.argv[1]; py_compile.compile(p,doraise=True,invalidation_mode="
                    "getattr(py_compile.PycInvalidationMode,sys.argv[2])); "
                    "print(json.dumps(importlib.util.cache_from_source(p)))")
            child = subprocess.run([selected, '-I', '-S', '-c', warm, str(module), mode],
                                   cwd=candidate, env=self._fixture_env(), capture_output=True, text=True)
            assert child.returncode == 0, child.stderr
            cache = Path(json.loads(child.stdout))
            before = hashlib.sha256(cache.read_bytes()).hexdigest()
            module.write_text(new)
            os.utime(module, ns=(stat.st_atime_ns, stat.st_mtime_ns))
            assert module.stat().st_mtime_ns == stat.st_mtime_ns and module.stat().st_size == stat.st_size
            self._git(candidate, 'add', '--', 'src/core/cache_probe.py')
            # Independent actual-interpreter witness: default cache still executes OLD code.
            witness = ("import sys; sys.path.insert(0,sys.argv[1]); "
                       "from src.core.cache_probe import marker; assert marker == 'old'")
            child = subprocess.run([selected, '-I', '-S', '-B', '-c', witness, str(candidate)],
                                   cwd=candidate, env=self._fixture_env(), capture_output=True, text=True)
            assert child.returncode == 0, child.stderr
            nb = candidate / 'fresh-source.ipynb'
            nb.write_text(_nb_json(["from src.core.cache_probe import marker\nassert marker == 'new'\n"]))
            self._git(candidate, 'add', '--', nb.name)
            env['SKEFT_NOTEBOOK_PYTHON'] = selected
            result = self._run(primary, env)
            assert result.returncode == 0, result.stderr
            assert self._calls(env) == []  # the real driver, not the selected-executable spy
            receipt, = list(case.glob('skeft-notebook-commit-*/receipt.json'))
            observed = json.loads(receipt.read_text())['results'][0]['driver']
            assert observed['status'] == 'passed'
            start = observed['origins']['start']
            end = observed['origins']['end']
            assert start['pycache_prefix'] == end['pycache_prefix'] == observed['cache_policy']['kernel_prefix']
            assert start['cache_prefix_empty'] and end['cache_prefix_empty']
            assert observed['cache_policy']['driver_prefix'] != start['pycache_prefix']
            assert Path(end['modules']['src.core.cache_probe']) == module
            assert hashlib.sha256(cache.read_bytes()).hexdigest() == before
            assert module.read_text() == new and module.stat().st_mtime_ns == stat.st_mtime_ns

    def test_actual_driver_refuses_untracked_source(self, tmp_path):
        selected = self._actual_python()
        primary, candidate, env = self._case(tmp_path)
        (candidate / 'src/core/untracked_probe.py').write_text('marker = 1\n')
        nb = candidate / 'untracked-origin.ipynb'
        nb.write_text(_nb_json(['import src.core.untracked_probe\n']))
        self._git(candidate, 'add', '--', nb.name)
        env['SKEFT_NOTEBOOK_PYTHON'] = selected
        result = self._run(primary, env)
        assert result.returncode == 1, result.stderr
        assert 'untracked or wrong-checkout source' in result.stderr
        assert self._calls(env) == []

    def test_actual_driver_refuses_missing_guard_output(self, tmp_path):
        selected = self._actual_python()
        primary, candidate, env = self._case(tmp_path)
        nb = candidate / 'guard-output.ipynb'
        code = ("import os\nfrom pathlib import Path\n"
                "paths = list(Path(os.environ['TMPDIR']).glob('skeft-notebook-commit-*/0/start-origins.json'))\n"
                "assert len(paths) == 1\npaths[0].unlink()\n")
        nb.write_text(_nb_json([code]))
        self._git(candidate, 'add', '--', nb.name)
        env['SKEFT_NOTEBOOK_PYTHON'] = selected
        result = self._run(primary, env)
        assert result.returncode == 1, result.stderr
        assert 'start-origins.json' in result.stderr
        assert self._calls(env) == []


    def test_actual_driver_refuses_other_checkout_package_search_path(self, tmp_path):
        selected = self._actual_python()
        primary, candidate, env = self._case(tmp_path)
        other = tmp_path / 'other-checkout/src/core'
        other.mkdir(parents=True)
        (other / 'foreign_probe.py').write_text('marker = 1\n')
        nb = candidate / 'wrong-origin.ipynb'
        code = ("import src.core\nsrc.core.__path__.insert(0, " + repr(str(other)) + ")\n"
                "import src.core.foreign_probe\n")
        nb.write_text(_nb_json([code]))
        self._git(candidate, 'add', '--', nb.name)
        env['SKEFT_NOTEBOOK_PYTHON'] = selected
        result = self._run(primary, env)
        assert result.returncode == 1, result.stderr
        assert 'wrong-checkout' in result.stderr
        assert self._calls(env) == []

    def _pager_query_probe(self, tmp_path, env):
        import os
        import shutil
        import sys
        real_git = shutil.which('git')
        assert real_git and Path(real_git).is_absolute()
        bindir = tmp_path / 'pager-query-bin'
        bindir.mkdir()
        log = tmp_path / 'pager-query-log.jsonl'
        proxy = bindir / 'git'
        proxy.write_text('#!' + sys.executable + '\n' +
                         "import json,os,sys\n" +
                         "with open(" + repr(str(log)) + ",'a') as f: f.write(json.dumps({'argv':sys.argv[1:],'pager':os.environ.get('GIT_PAGER')})+'\\n')\n" +
                         "assert sys.argv[1] == '--no-pager', sys.argv\n" +
                         "os.execv(" + repr(real_git) + ", [" + repr(real_git) + "]+sys.argv[1:])\n")
        proxy.chmod(0o755)
        env['PATH'] = str(bindir) + os.pathsep + env['PATH']
        return log

    def test_inherited_normal_cat_pager_preserves_target_and_proceeds(self, tmp_path):
        primary, candidate, env = self._case(tmp_path, linked=True)
        name = 'pager-cat.ipynb'
        self._stage(candidate, name)
        env['GIT_PAGER'] = 'cat'
        log = self._pager_query_probe(tmp_path, env)
        result = self._run(primary, env)
        assert result.returncode == 0, result.stderr
        call, = self._calls(env)
        assert call['context']['checkout'] == str(candidate)
        assert call['context']['notebook'] == name
        queries = [json.loads(line) for line in log.read_text().splitlines()]
        assert queries and all(q['pager'] == 'cat' and q['argv'][0] == '--no-pager' for q in queries)

    def test_inherited_command_pager_is_not_executed_by_helper_queries(self, tmp_path):
        import hashlib
        import shlex
        primary, candidate, env = self._case(tmp_path, linked=True)
        self._stage(candidate, 'pager-command.ipynb')
        marker = tmp_path / 'pager-was-executed'
        pager = tmp_path / 'pager-command'
        pager.write_text('#!/bin/sh\nprintf called > ' + shlex.quote(str(marker)) + '\n')
        pager.chmod(0o755)
        before = hashlib.sha256(pager.read_bytes()).hexdigest()
        env['GIT_PAGER'] = shlex.quote(str(pager))
        log = self._pager_query_probe(tmp_path, env)
        result = self._run(primary, env)
        assert result.returncode == 0, result.stderr
        call, = self._calls(env)
        assert call['context']['checkout'] == str(candidate)
        queries = [json.loads(line) for line in log.read_text().splitlines()]
        assert queries and all(q['pager'] == env['GIT_PAGER'] and q['argv'][0] == '--no-pager' for q in queries)
        assert not marker.exists()
        assert hashlib.sha256(pager.read_bytes()).hexdigest() == before

    def test_actual_driver_custom_kernel_uses_memory_history(self, tmp_path):
        selected = self._actual_python()
        primary, candidate, env = self._case(tmp_path)
        nb = candidate / 'memory-history.ipynb'
        nb.write_text(_nb_json(["assert str(get_ipython().history_manager.hist_file) == ':memory:'\n"]))
        self._git(candidate, 'add', '--', nb.name)
        env['SKEFT_NOTEBOOK_PYTHON'] = selected
        result = self._run(primary, env)
        assert result.returncode == 0, result.stderr
        assert self._calls(env) == []
        receipt, = list(tmp_path.glob('skeft-notebook-commit-*/receipt.json'))
        observed = json.loads(receipt.read_text())['results'][0]['driver']
        assert observed['status'] == 'passed'
        assert observed['origins']['start']['history_file'] == ':memory:'
        assert observed['origins']['end']['history_file'] == ':memory:'


    @pytest.mark.parametrize("linked", [False, True])
    @pytest.mark.parametrize("stat_target", ["notebook", "source"])
    def test_stat_only_notebook_restore_preserves_raw_index(self, tmp_path, linked, stat_target):
        import hashlib
        import os
        import time
        primary, candidate, env = self._case(tmp_path, linked=linked)
        notebook = self._stage(candidate, 'stat-only-restore.ipynb')
        index = Path(self._git(candidate, 'rev-parse', '--path-format=absolute', '--git-path', 'index'))
        raw_index = index.read_bytes()
        restored = notebook if stat_target == "notebook" else candidate / "src/core/formulas.py"
        original = restored.read_bytes()
        stat = restored.stat()
        time.sleep(0.01)
        restored.write_bytes(original)
        os.utime(restored, ns=(stat.st_atime_ns, stat.st_mtime_ns))
        assert restored.read_bytes() == original
        assert restored.stat().st_mtime_ns == stat.st_mtime_ns
        assert restored.stat().st_ctime_ns != stat.st_ctime_ns
        assert index.read_bytes() == raw_index
        env['GIT_PAGER'] = 'cat'
        log = self._pager_query_probe(tmp_path, env)
        result = self._run(primary, env)
        assert result.returncode == 0, result.stderr
        call, = self._calls(env)
        assert call['context']['checkout'] == str(candidate)
        assert call['context']['notebook'] == notebook.name
        assert index.read_bytes() == raw_index
        receipt, = list(tmp_path.glob('skeft-notebook-commit-*/receipt.json'))
        observed = json.loads(receipt.read_text())
        expected = hashlib.sha256(raw_index).hexdigest()
        assert observed['before']['index_sha256'] == observed['after']['index_sha256'] == expected
        queries = [json.loads(line) for line in log.read_text().splitlines()]
        assert queries and all(q['argv'][:3] == ['--no-pager', '-c', 'diff.autoRefreshIndex=false']
                               and q['pager'] == 'cat' for q in queries)

    def _raw_index_query_mutation_probe(self, tmp_path, env, trigger):
        import os
        import shutil
        import sys
        real_git = shutil.which('git')
        assert real_git and Path(real_git).is_absolute()
        bindir = tmp_path / 'raw-index-query-bin'
        bindir.mkdir()
        log = tmp_path / 'raw-index-mutation.json'
        proxy = bindir / 'git'
        code = ("import hashlib,json,os,pathlib,subprocess,sys\n"
                "r=subprocess.run([" + repr(real_git) + "]+sys.argv[1:],capture_output=True)\n"
                "trigger=" + repr(trigger) + "\n"
                "if r.returncode == 0 and trigger in sys.argv[1:]:\n"
                "    p=pathlib.Path(os.environ['GIT_INDEX_FILE'])\n"
                "    original=p.read_bytes(); data=bytearray(original)\n"
                "    assert data[:4] == b'DIRC' and len(data) > 32\n"
                "    data[12] ^= 1\n"
                "    data[-20:]=hashlib.sha1(data[:-20]).digest()\n"
                "    p.write_bytes(data)\n"
                "    pathlib.Path(" + repr(str(log)) + ").write_text(json.dumps({'argv':sys.argv[1:],'before':hashlib.sha256(original).hexdigest(),'after':hashlib.sha256(data).hexdigest(),'index':str(p)}))\n"
                "sys.stdout.buffer.write(r.stdout);sys.stderr.buffer.write(r.stderr)\n"
                "sys.exit(r.returncode)\n")
        proxy.write_text('#!' + sys.executable + '\n' + code)
        proxy.chmod(0o755)
        env['PATH'] = str(bindir) + os.pathsep + env['PATH']
        return log

    @pytest.mark.parametrize("trigger,with_notebook", [("--git-path", True), ("--diff-filter=ACM", False)])
    def test_raw_index_drift_refuses_early_query_and_empty_selection(self, tmp_path, trigger, with_notebook):
        import hashlib
        primary, candidate, env = self._case(tmp_path, linked=True)
        if with_notebook:
            self._stage(candidate, 'early-query.ipynb')
        index = Path(self._git(candidate, 'rev-parse', '--path-format=absolute', '--git-path', 'index'))
        original = index.read_bytes()
        log = self._raw_index_query_mutation_probe(tmp_path, env, trigger)
        result = self._run(primary, env)
        assert result.returncode == 2, result.stderr
        assert 'active index bytes changed during query/execution; no acceptance' in result.stderr
        observed = json.loads(log.read_text())
        assert trigger in observed['argv'] and observed['index'] == str(index)
        assert observed['before'] == hashlib.sha256(original).hexdigest()
        assert observed['after'] == hashlib.sha256(index.read_bytes()).hexdigest()
        assert observed['after'] != observed['before']
        assert self._calls(env) == []
        assert list(tmp_path.glob('skeft-notebook-commit-*')) == []


    @pytest.mark.parametrize("mode_target", ["notebook", "source"])
    def test_mode_only_partial_staging_refuses_before_driver(self, tmp_path, mode_target):
        primary, candidate, env = self._case(tmp_path, linked=True)
        notebook = self._stage(candidate, 'mode-only.ipynb')
        target = notebook if mode_target == "notebook" else candidate / "src/core/formulas.py"
        index = Path(self._git(candidate, 'rev-parse', '--path-format=absolute', '--git-path', 'index'))
        raw_index = index.read_bytes()
        original = target.read_bytes()
        target.chmod(target.stat().st_mode ^ 0o100)
        assert target.read_bytes() == original and index.read_bytes() == raw_index
        result = self._run(primary, env)
        assert result.returncode == 2, result.stderr
        assert 'working file mode differs from the active index; partial staging unsupported' in result.stderr
        assert self._calls(env) == []
        assert index.read_bytes() == raw_index
        assert list(tmp_path.glob('skeft-notebook-commit-*')) == []


    @pytest.mark.parametrize("mode_target", ["notebook", "source"])
    def test_mode_only_drift_during_execution_retains_failed_receipt(self, tmp_path, mode_target):
        import hashlib
        import subprocess
        import sys
        primary, candidate, env = self._case(tmp_path, linked=True)
        notebook = self._stage(candidate, 'execution-mode.ipynb')
        source = candidate / 'src/core/formulas.py'
        selected = {notebook.name: notebook, 'src/core/formulas.py': source}
        originals = {name: path.read_bytes() for name, path in selected.items()}
        modes = {name: '100755' if path.stat().st_mode & 0o100 else '100644'
                 for name, path in selected.items()}
        index = Path(self._git(candidate, 'rev-parse', '--path-format=absolute', '--git-path', 'index'))
        raw_index = index.read_bytes()
        records = self._git(candidate, '--literal-pathspecs', 'ls-files', '--stage', '--', *selected).splitlines()
        indexed_modes = {}
        for record in records:
            header, name = record.split('\t', 1)
            mode, object_id, stage = header.split()
            assert stage == '0' and name not in indexed_modes
            indexed_modes[name] = mode
        assert indexed_modes == modes
        for name, original in originals.items():
            blob = subprocess.run(['git', '--no-pager', 'show', ':0:' + name], cwd=candidate,
                                  env=self._fixture_env(), capture_output=True)
            assert blob.returncode == 0, blob.stderr
            assert blob.stdout == original
        assert index.read_bytes() == raw_index
        target_name = notebook.name if mode_target == 'notebook' else 'src/core/formulas.py'
        target = selected[target_name]
        # This selected fixture spy succeeds, then changes only the working mode.
        spy = Path(env['SKEFT_NOTEBOOK_PYTHON'])
        spy.write_text('#!' + sys.executable + '\n' +
                       "import json,os,pathlib,sys\n"
                       "c=json.loads(sys.argv[-1]); o=pathlib.Path(c['output'])\n"
                       "with open(os.environ['SPY_LOG'],'a') as f: f.write(json.dumps({'argv':sys.argv[1:6],'cwd':os.getcwd(),'context':c})+'\\n')\n"
                       "(o/'driver.json').write_text(json.dumps({'status':'passed','fixture_spy_only':True}))\n"
                       "p=pathlib.Path(" + repr(str(target)) + ")\n"
                       "p.chmod(p.stat().st_mode ^ 0o100)\n"
                       "sys.exit(0)\n")
        result = self._run(primary, env)
        assert result.returncode == 2, result.stderr
        assert 'index/source/notebook bytes changed during execution; no acceptance' in result.stderr
        call, = self._calls(env)
        assert call['context']['checkout'] == str(candidate)
        assert call['context']['notebook'] == notebook.name
        assert {name: path.read_bytes() for name, path in selected.items()} == originals
        assert index.read_bytes() == raw_index
        after_modes = {name: '100755' if path.stat().st_mode & 0o100 else '100644'
                       for name, path in selected.items()}
        assert after_modes[target_name] != modes[target_name]
        assert all(after_modes[name] == modes[name] for name in selected if name != target_name)
        receipts = list(tmp_path.glob('skeft-notebook-commit-*/receipt.json'))
        receipt, = receipts
        observed = json.loads(receipt.read_text())
        assert observed['status'] == 'failed'
        assert 'index/source/notebook bytes changed during execution; no acceptance' in observed['protocol_error']
        execution, = observed['results']
        assert execution['returncode'] == 0 and execution['passed'] is True
        assert execution['driver']['status'] == 'passed' and execution['driver']['fixture_spy_only'] is True
        expected = hashlib.sha256(raw_index).hexdigest()
        assert observed['before']['index_sha256'] == observed['after']['index_sha256'] == expected
        assert observed['before']['sources'] == observed['after']['sources']
        assert observed['before']['notebooks'] == observed['after']['notebooks']
        assert observed['before']['modes'][target_name] == modes[target_name]
        assert observed['after']['modes'][target_name] == after_modes[target_name]
        assert observed['before']['modes'] != observed['after']['modes']
