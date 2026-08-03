"""ADR-009 Phase 0, Guard 2 — runtime flags must still reach the checks that read them.

WHY THIS FILE EXISTS
--------------------
`validate.py` carries three runtime flags as MODULE GLOBALS, assigned by `main()`
(`validate.py:7751-7754`) and read inside check bodies:

    STRICT_MODE            12 read sites across 6 checks
    FORCE_LATEX             1 read site  (paper_latex_compiles)
    FORCE_NOTEBOOK_REEXEC   2 read sites (notebook_exec)

ADR-009 splits this file into `scripts/validate/`. The hazard (ADR-009 H5) is
that a check module written as ``from validate import STRICT_MODE`` binds a
COPY at import time: `main()` then sets `validate.STRICT_MODE = True`, the
copy stays `False`, and every affected check silently takes its non-strict
branch. Nothing raises. `--strict` becomes a no-op and the suite still reports
green — the exact failure shape this project has shipped eight times.

Before this file, exactly ONE of those twelve `STRICT_MODE` sites had a test
(`test_validate_prose_checks.py::test_theorem_name_embedded_citations_passes_strict`),
and `FORCE_LATEX` / `FORCE_NOTEBOOK_REEXEC` had none at all. A stuck-`False`
`FORCE_LATEX` makes `paper_latex_compiles` skip forever; a stuck-`False`
`FORCE_NOTEBOOK_REEXEC` makes `notebook_exec` return cached verdicts without
executing a single notebook.

TEST STRATEGY
-------------
Two legs, because either alone is defeatable:

* **Behavioural** — toggle the flag and assert an observable outcome changes.
  `parameter_provenance` is the canary: it is fast (<10 ms), reads only Python
  registries, and genuinely flips (`passed=True` -> `passed=False`) under
  `--strict`, because non-PROJECTED parameters still lack `human_verified_date`.
  An end-to-end subprocess leg additionally proves the whole CLI -> global ->
  check -> exit-code path, which is what actually breaks on a bad split.
* **Structural** — assert each consuming function performs a global-name lookup
  for the flag (`__code__.co_names`). This catches a refactor that rebinds the
  flag as a local or a default argument, which the behavioural leg would miss
  for the two checks too slow to run here.

MEASURED LIMIT, stated rather than papered over: there is no behavioural leg for
`FORCE_NOTEBOOK_REEXEC` (executing ~91 notebooks) or for the `True` direction of
`FORCE_LATEX` (pdflatex over 21 drafts). Those two are structural-only. If the
`notebook_exec` cache logic is ever extracted into a pure helper, add the
behavioural leg and delete this paragraph.
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT / "scripts"))

import validate as v  # noqa: E402
from validation import _config as cfg  # noqa: E402


def _check(name: str):
    return next(s.func for s in v._CHECKS if s.name == name)


@pytest.fixture(autouse=True)
def _restore_flags():
    """Flags live on `validation._config`; never leak a mutation into another test."""
    saved = (cfg.STRICT_MODE, cfg.FORCE_LATEX, cfg.FORCE_NOTEBOOK_REEXEC)
    yield
    cfg.STRICT_MODE, cfg.FORCE_LATEX, cfg.FORCE_NOTEBOOK_REEXEC = saved


# ────────────────────────────────────────────────────────────────────────
# STRICT_MODE — behavioural, in-process
# ────────────────────────────────────────────────────────────────────────

class TestStrictModeReachesChecks:
    def test_parameter_provenance_flips_under_strict(self):
        """The canary. If this stops flipping, `--strict` has been severed from
        the checks that implement it."""
        fn = _check("parameter_provenance")

        cfg.STRICT_MODE = False
        lenient = fn()
        cfg.STRICT_MODE = True
        strict = fn()

        assert lenient.passed is True, (
            "parameter_provenance should PASS in default mode — if it now fails "
            "lenient, this canary needs re-picking, not silencing."
        )
        assert strict.passed is False, (
            "parameter_provenance did NOT fail under STRICT_MODE. Either the "
            "human-verification backlog was cleared (re-pick the canary) or "
            "STRICT_MODE no longer reaches the check body — the ADR-009 H5 "
            "import-by-value hazard."
        )

    def test_strict_changes_the_reported_detail(self):
        """Not just the verdict: the strict path must emit its own finding, so a
        check that flipped for an unrelated reason does not read as success."""
        fn = _check("parameter_provenance")
        cfg.STRICT_MODE = True
        names = [d.name for d in fn().details]
        assert "human_verification" in names
        assert any(
            d.name == "human_verification" and not d.passed
            for d in fn().details
        ), "strict mode did not turn human_verification into a failing detail"


# ────────────────────────────────────────────────────────────────────────
# STRICT_MODE — end to end through the CLI
# ────────────────────────────────────────────────────────────────────────

class TestStrictModePropagatesThroughMain:
    """CLI -> `global STRICT_MODE` -> check body -> exit code. This is the leg
    that a package split breaks, and the only one that exercises `main()`'s
    assignment at `validate.py:7752`."""

    def _rc(self, *args: str) -> int:
        return subprocess.run(
            [sys.executable, "scripts/validate.py", "--check",
             "parameter_provenance", *args],
            cwd=SK_ROOT, capture_output=True, text=True,
        ).returncode

    def test_default_mode_exits_zero(self):
        assert self._rc() == 0

    def test_strict_mode_exits_one(self):
        assert self._rc("--strict") == 1, (
            "`--strict` did not change the exit code. The flag is parsed but is "
            "not reaching the check — a no-op gate that still reports green."
        )


# ────────────────────────────────────────────────────────────────────────
# FORCE_LATEX
# ────────────────────────────────────────────────────────────────────────

class TestForceLatex:
    def test_default_skips_without_running_pdflatex(self):
        cfg.FORCE_LATEX = False
        r = _check("paper_latex_compiles")()
        assert r.passed is True
        assert any("SKIPPED" in (d.message or "") for d in r.details), (
            "paper_latex_compiles no longer reports its slow-gate skip. If it "
            "now runs by default that is a deliberate change; if it silently "
            "reports nothing, FORCE_LATEX has been severed."
        )

    def test_selecting_the_check_by_name_auto_enables_it(self):
        """`validate.py:7754` sets FORCE_LATEX when the check is selected
        explicitly — otherwise `--check paper_latex_compiles` would skip the very
        check it names. Asserted against the source because the behavioural test
        would run pdflatex over 21 drafts."""
        src = (SK_ROOT / "scripts" / "validate.py").read_text()
        assert 'args.force_latex or args.check == "paper_latex_compiles"' in src, (
            "the auto-enable clause is gone; `--check paper_latex_compiles` "
            "would now skip itself and report PASS."
        )


# ────────────────────────────────────────────────────────────────────────
# Structural leg — the flags are read as module globals, at call time
# ────────────────────────────────────────────────────────────────────────

class TestFlagsAreReadAsGlobals:
    """`co_names` holds the names a function looks up globally. A refactor that
    rebinds a flag as a local, a default argument, or an import-time copy drops
    it from this set. This is the only leg available for the two flags whose
    behavioural test is prohibitively slow."""

    @pytest.mark.parametrize("check_name,flag", [
        ("parameter_provenance", "STRICT_MODE"),
        ("axiom_closure_allowlist", "STRICT_MODE"),
        ("provenance_doi_in_registry", "STRICT_MODE"),
        ("bundle_source_freshness", "STRICT_MODE"),
        ("bibitem_title_primary_source", "STRICT_MODE"),
        ("theorem_name_embedded_citations", "STRICT_MODE"),
        ("paper_latex_compiles", "FORCE_LATEX"),
        ("notebook_exec", "FORCE_NOTEBOOK_REEXEC"),
    ])
    def test_check_reads_flag_from_module_globals(self, check_name, flag):
        fn = _check(check_name)
        assert flag in fn.__code__.co_names, (
            f"`{check_name}` no longer performs a global lookup of `{flag}`. "
            f"After the ADR-009 split this is how the flag silently stops "
            f"working: the check keeps an import-time copy and always takes its "
            f"default branch."
        )

    @pytest.mark.parametrize("check_name", [
        "parameter_provenance", "axiom_closure_allowlist",
        "provenance_doi_in_registry", "bundle_source_freshness",
        "bibitem_title_primary_source", "theorem_name_embedded_citations",
        "paper_latex_compiles", "notebook_exec",
    ])
    def test_check_reaches_the_flag_through_the_config_module(self, check_name):
        """The flag must be reached as `_cfg.<FLAG>`, never as a bare global.

        ⚠️ THE TEST ABOVE IS NOT SUFFICIENT, and finding that out is why this one
        exists. `co_names` records names used for BOTH `LOAD_GLOBAL` and
        `LOAD_ATTR`, so a module doing `from validate import STRICT_MODE` still
        shows `STRICT_MODE` in `co_names` — it is a global lookup, merely
        resolving against the WRONG module's namespace. The value is frozen at
        import time, `--strict` becomes a no-op, and the guard written for
        exactly that hazard stays green.

        Requiring `_cfg` in `co_names` closes it: an import-time copy would be a
        bare global with no `_cfg` attribute access anywhere in the function.
        """
        fn = _check(check_name)
        assert "_cfg" in fn.__code__.co_names, (
            f"`{check_name}` does not reach its runtime flag through the config "
            f"module. A bare global (or an import-time copy) is frozen at import "
            f"time once the checks are split across modules — see ADR-009 H5."
        )


class TestNoCheckModuleShadowsAFlag:
    """No module in the suite may bind a flag in its OWN namespace.

    This is the cross-module form of the H5 hazard, and it is the one a
    `co_names` assertion cannot see. `from validation._config import STRICT_MODE`
    at the top of a check module creates `that_module.STRICT_MODE` — a copy that
    `main()` will never update. Asserting the attribute is ABSENT catches it
    regardless of how the function body then reads it.
    """

    _FLAGS = ("STRICT_MODE", "FORCE_LATEX", "FORCE_NOTEBOOK_REEXEC")

    def _suite_modules(self):
        """Every loaded module belonging to the validation suite, except the two
        that legitimately own the flags (`validation._config` defines them;
        `validate` is where `main()` assigns them)."""
        import validation
        out = []
        for name, mod in list(sys.modules.items()):
            if mod is None:
                continue
            if name == "validate" or name.startswith("validation"):
                if name in ("validate", "validation._config"):
                    continue
                out.append((name, mod))
        return out

    def test_no_suite_module_carries_a_flag_copy(self):
        offenders = [
            f"{name}.{flag}"
            for name, mod in self._suite_modules()
            for flag in self._FLAGS
            if hasattr(mod, flag)
        ]
        assert not offenders, (
            f"module(s) hold an import-time COPY of a runtime flag: {offenders}. "
            f"`main()` assigns `validation._config.<FLAG>`, so these copies stay "
            f"at their default forever and the flag silently becomes a no-op. "
            f"Use `from validation import _config as _cfg` + `_cfg.<FLAG>`."
        )

    def test_validate_itself_no_longer_defines_them(self):
        """`validate` used to own these. It must not still, or two writers exist
        and whichever a check happens to read decides the behaviour."""
        for flag in self._FLAGS:
            assert not hasattr(v, flag), (
                f"`validate.{flag}` still exists alongside "
                f"`validation._config.{flag}` — two sources of truth for one flag."
            )
