"""`validate.py --ci` — the unattended-runner mode (PR-review R5-C1).

WHY THIS MODE EXISTS, AND WHY IT IS NOT A WORKFLOW FILE
--------------------------------------------------------
R5 filed "no CI" as a Critical and proposed the one-file answer: a GitHub Actions
workflow running `validate.py && pytest`. Measured on this branch, that workflow
breaks on its first run and then, once "fixed" the obvious way, becomes actively
harmful. Two findings, both measured, both recorded here because a workflow file
cannot carry them:

**1. mtime freshness is meaningless on a fresh checkout.** Git sets every file's
mtime to checkout time in index order, so `docs/` lands before `src/`, `lean/` and
`papers/`. Measured on a real `git clone` of this branch:

    docs/counts.json           mtime = 1785915261.937
      src/core/constants.py            1785915262.606   STALE
      src/core/visualizations.py       1785915262.608   STALE
      lean/lean_deps.json              1785915262.338   STALE
      newest of 2039 *.lean            1785915262.269   STALE

All four of `counts_fresh`'s criteria read stale on an untouched clone, and it then
shells out to `update_counts.py` — 1800-second timeout, needs `lake`. The three
regenerators are workstation conveniences registered as checks.

**2. A CI that loses the Lean toolchain gets faster AND greener.** Dropping `lake`
removes ~200 s (`axiom_closure_allowlist` 145 s, `lean_docstring_refs_resolve` 53 s)
and stops 7 `lean_deps.json` readers from measuring anything — while the run still
exits 0. That is *"absence of measurement rendered as success"* reintroduced one
layer up, which is the finding this entire audit exists to close.

So the mode's real content is the COVERAGE FLOOR, and that is what these tests are
mostly about. A green tick over 71 of 79 is worse than no CI.

WHAT IS DELIBERATELY *NOT* HERE
-------------------------------
`--ci` does NOT imply `--strict`. `WAVE_EXECUTION_PIPELINE.md` Invariant #12 scopes
`--strict` to the Paper Submission Gate, and there is a concrete demonstration:
`bundle_source_freshness` WARNs whenever a source paper moved after its last bundle
lift — the normal state of an in-progress bundle. A strict CI would go red on
correct work in the middle of every wave, and a gate that fires on correct work gets
switched off.
"""
from __future__ import annotations

import contextlib
import io
import sys
from pathlib import Path

import pytest

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT / "scripts"))
sys.path.insert(0, str(SK_ROOT))

import validate  # noqa: E402
from validation import _config as _cfg  # noqa: E402
from validation._registry import CheckResult, CheckSpec, Detail  # noqa: E402


def _ok():
    return CheckResult(passed=True, details=[])


@pytest.fixture
def tiny_registry(monkeypatch):
    """Replace the registry with a small one and run the REAL `main()`.

    The point of exercising `main()` rather than a helper: the skip and the floor
    are decisions `main()` makes, and a test that re-implemented them would assert
    only that the test agrees with itself — the shape this audit found in
    `TestRecurrenceThresholdAgainstFrozenPairs` and `TestGraphTestNodeCoverage`.
    """
    names = list(_cfg.CI_SKIP) + [f"c{i}" for i in range(6)]
    monkeypatch.setattr(validate, "_CHECKS",
                        [CheckSpec(name=n, description=n, func=_ok) for n in names],
                        raising=False)
    monkeypatch.setattr(validate._H, "ensure_lean_deps_fresh", lambda: (False, "stub"))
    return names


def _run(argv) -> tuple[int, str]:
    err = io.StringIO()
    with contextlib.redirect_stderr(err), contextlib.redirect_stdout(io.StringIO()):
        rc = validate.main(argv)
    return rc, err.getvalue()


class TestCiSkips:

    def test_the_regenerators_are_skipped(self, tiny_registry, monkeypatch):
        """SILENT ON CORRECT DATA — and the skip must be VISIBLE, not silent. An
        invisible exclusion is how a suite quietly shrinks."""
        monkeypatch.setattr(_cfg, "CI_MIN_CHECKS_RUN", 6)
        rc, err = _run(["--ci", "--no-archive"])
        assert rc == 0
        for name in _cfg.CI_SKIP:
            assert name in err, f"{name} was skipped SILENTLY under --ci"

    def test_nothing_is_skipped_without_the_flag(self, tiny_registry, monkeypatch):
        """The default path must be untouched. `--ci` is opt-in; a developer running
        `validate.py` locally still wants the regenerators to regenerate."""
        monkeypatch.setattr(_cfg, "CI_MIN_CHECKS_RUN", 6)
        rc, err = _run(["--no-archive"])
        assert "--ci: skipped" not in err

    def test_every_skipped_check_carries_a_REASON(self):
        """`CI_SKIP` is a dict, not a set, so an exclusion cannot be added without
        saying why. Every silent-scope defect this audit found — the `glob`s, the
        `d11_/d12_` filter, the `heading[:50]` — was a narrowing nobody had to
        justify in writing at the point of narrowing."""
        for name, why in _cfg.CI_SKIP.items():
            assert isinstance(why, str) and len(why) > 30, (
                f"CI_SKIP[{name!r}] has no substantive reason")

    def test_the_skipped_checks_are_REAL(self):
        """Runs against the live registry: an exclusion naming a check that no longer
        exists is silent scope creep in the other direction — the floor would then be
        satisfied by a smaller suite than intended."""
        registered = {s.name for s in validate._CHECKS}
        unknown = sorted(set(_cfg.CI_SKIP) - registered)
        assert not unknown, f"CI_SKIP names checks that are not registered: {unknown}"


class TestCoverageFloor:
    """The point of the mode."""

    def test_a_shrunken_suite_FAILS_even_though_every_check_passed(
            self, tiny_registry, monkeypatch):
        """FIRES ON THE SEEDED DEFECT, and this is the whole design.

        Every check in the fixture passes. The run still fails, because fewer ran
        than the floor. That is the inversion the mode exists for: on a runner
        without `lake`, the suite gets ~200 s faster and 10 checks quieter, and
        without this it exits 0.
        """
        monkeypatch.setattr(_cfg, "CI_MIN_CHECKS_RUN", 9)
        rc, err = _run(["--ci", "--no-archive"])
        assert rc == 1, (
            "6 checks ran against a floor of 9 and the run passed — a CI that gets "
            "SMALLER reports greener, which is the failure this audit is about")
        assert "COVERAGE FLOOR" in err

    def test_the_floor_does_not_apply_without_the_flag(self, tiny_registry, monkeypatch):
        """A local `--check` run or a plain run must not trip a CI-only guard."""
        monkeypatch.setattr(_cfg, "CI_MIN_CHECKS_RUN", 9)
        rc, _ = _run(["--no-archive"])
        assert rc == 0

    def test_the_floor_does_not_apply_to_a_single_check(self, tiny_registry, monkeypatch):
        """`--ci --check X` runs one check by construction; applying the floor there
        would make the flag combination permanently red and teach people to drop it."""
        monkeypatch.setattr(_cfg, "CI_MIN_CHECKS_RUN", 9)
        rc, _ = _run(["--ci", "--no-archive", "--check", "c1"])
        assert rc == 0

    def test_the_LIVE_floor_has_ZERO_headroom(self):
        """Measured against the real registry, in the house ratchet idiom: the floor
        must equal what a correctly-provisioned runner actually executes. Slack is a
        toolchain that can go missing without anyone noticing — the defect measured in
        `ledger_ids_resolve` (67 against 66) and in `recurrence_reopens_closures`
        (threshold above its own corpus maximum, three times)."""
        expected = len(validate._CHECKS) - len(_cfg.CI_SKIP)
        assert _cfg.CI_MIN_CHECKS_RUN == expected, (
            f"CI_MIN_CHECKS_RUN is {_cfg.CI_MIN_CHECKS_RUN} but a fully-provisioned "
            f"runner executes {expected} ({len(validate._CHECKS)} registered minus "
            f"{len(_cfg.CI_SKIP)} skipped). Update it in the same commit as the check.")

    @pytest.mark.slow
    def test_the_LIVE_floor_matches_what_a_REAL_run_MEASURES(self):
        """The half the assertion above cannot cover.

        `registered - skipped` is the DEFINITION of the floor, so comparing the floor to
        it can only catch an arithmetic slip. What it cannot see is a check that
        registers, is not skipped, and still contributes nothing — one that returns
        `measured=False` because a toolchain went missing. That is precisely the failure
        the floor exists to catch, and it needs the real registry EXECUTED, not counted.

        Slow by necessity: it runs the suite.
        """
        import validate as _v
        results = _v.run_checks(skip=_cfg.CI_SKIP)
        measured = [n for n, r in results.items() if r.measured]
        unmeasured = sorted(n for n, r in results.items() if not r.measured)
        assert len(measured) >= _cfg.CI_MIN_CHECKS_RUN, (
            f"a real run MEASURED {len(measured)} checks against a floor of "
            f"{_cfg.CI_MIN_CHECKS_RUN}. Unmeasured: {unmeasured}. Either the environment "
            f"is under-provisioned or a check silently stopped measuring — the floor "
            f"exists to make that visible rather than green.")


class TestACrashedCheckIsUNMEASURED:
    """⚠️ `run_checks`' exception handler sets `measured=False`, and NOTHING
    tested it.

    Deleting that keyword reverts a crashed check to counting as a full
    measurement, which defeats the `--ci` coverage floor — the exact defect the
    handler's own comment says it exists to fix. Measured: with the keyword
    removed, 185 tests across the nine plausible files stayed green.
    `tests/test_cannot_measure_baseline.py` is the closest guard and it is an AST
    scan of `validation/checks/*.py` return statements, so it never reaches
    `run_checks` at all; the only other caller in the suite runs the real registry,
    where nothing crashes."""

    def test_a_crashing_check_is_UNMEASURED_not_merely_failed(self, monkeypatch):
        import validate as _v

        def _boom():
            raise RuntimeError("seeded crash")

        spec = _v.CheckSpec("boom", "seeded", _boom)
        monkeypatch.setattr(_v, "_CHECKS", [spec])
        r = _v.run_checks()["boom"]
        assert r.passed is False, "a crash must not pass"
        assert r.measured is False, (
            "a check that raised measured nothing; counting it toward the "
            "coverage floor is what the floor exists to prevent")

    def test_a_healthy_check_stays_MEASURED(self, monkeypatch):
        """The silent direction — otherwise `measured=False` everywhere passes."""
        import validate as _v
        spec = _v.CheckSpec("fine", "seeded", lambda: _v.CheckResult(passed=True))
        monkeypatch.setattr(_v, "_CHECKS", [spec])
        assert _v.run_checks()["fine"].measured is True


class TestCiIsNotStrict:

    def test_ci_does_not_imply_strict(self, tiny_registry, monkeypatch):
        """⚠️ The deliberate negative, and it is load-bearing.

        `bundle_source_freshness` WARNs whenever a source paper moved after its last
        bundle lift — the NORMAL state of an in-progress bundle. Under `--strict`
        that is a hard fail, so a strict CI would go red on correct work in the middle
        of every wave. Invariant #12 scopes `--strict` to the Paper Submission Gate,
        which acquired its caller (`gate_precheck.py submission`) on 2026-08-05.
        """
        monkeypatch.setattr(_cfg, "CI_MIN_CHECKS_RUN", 6)
        _run(["--ci", "--no-archive"])
        assert _cfg.STRICT_MODE is False, (
            "--ci turned on --strict; that hard-fails on in-progress bundles whose "
            "sources legitimately moved, and the gate would be switched off within a "
            "wave")

    def test_ci_never_archives(self, tiny_registry, monkeypatch):
        """A CI run that writes a timestamped report dirties the tree and stops being
        idempotently re-runnable."""
        monkeypatch.setattr(_cfg, "CI_MIN_CHECKS_RUN", 6)
        called: list = []
        monkeypatch.setattr(validate, "archive_results",
                            lambda r: called.append(r) or Path("x"))
        _run(["--ci"])
        assert not called, "--ci archived a report"


class TestCommitGateCheckNamesAreReal:
    """⚠️ PR-review pass 2, R1. `scripts/pre-commit-sync.sh:96` hardcodes three
    check names and never validates them against the registry:

        for c in formula_grounding placeholder_not_cited native_decide_regression

    `run_check` maps an unknown name to **SKIP, which never blocks** (rc2 →
    "could not run — skipping, not blocking"). So renaming any of the three
    silently disarms the only gate that can hard-block `main`, and the commit
    output says "skipping" rather than "unknown check".

    `CI_SKIP` already has exactly this guard (`test_the_skipped_checks_are_REAL`).
    The commit gate — which is strictly more load-bearing, being the sole
    enforcing mechanical gate on `main` — did not.
    """

    def _gate_names(self):
        import re
        from pathlib import Path
        sh = (Path(__file__).resolve().parent.parent
              / "scripts" / "pre-commit-sync.sh").read_text()
        m = re.search(r"^for c in ([A-Za-z0-9_ ]+); do", sh, re.MULTILINE)
        assert m, ("could not find the check loop in pre-commit-sync.sh — if it "
                   "was restructured, re-point this guard rather than deleting it")
        return m.group(1).split()

    def test_the_scan_finds_the_loop(self):
        """Guard the seam: an empty name list makes the assertion below vacuous."""
        names = self._gate_names()
        assert len(names) >= 3, f"only found {names}"

    def test_every_commit_gate_check_is_registered(self):
        """FIRES ON A SEEDED DEFECT: rename any of the three in the registry (or
        in the hook) and this fails — instead of the hook silently skipping."""
        registered = {s.name for s in validate._CHECKS}
        unknown = [n for n in self._gate_names() if n not in registered]
        assert not unknown, (
            f"pre-commit-sync.sh runs check name(s) that are NOT registered: "
            f"{unknown}. `run_check` maps an unknown name to SKIP, which never "
            f"blocks — so the only mechanical gate on `main` is silently disarmed "
            f"for those checks.")


class TestScopeSubstrate:
    """`--scope substrate` — what BLOCKS a pure-Lean wave close.

    `gate_precheck s13` runs the full suite, so a Lean wave's Stage-13 dispatch was
    vetoed by paper-corpus state it never touched. The flag scopes the EXIT CODE only:
    every check still runs and every failure is still printed. A flag that hid failures
    would be the defect this suite exists to catch, wearing a convenience label.
    """

    def _registry(self, monkeypatch, failing_module_of):
        """Registry whose checks fail, each attributed to a chosen defining module."""
        specs = []
        for name, mod in failing_module_of.items():
            fn = (lambda: CheckResult(passed=False, details=[]))
            fn.__module__ = f"validation.checks.{mod}"
            specs.append(CheckSpec(name=name, description=name, func=fn))
        monkeypatch.setattr(validate, "_CHECKS", specs, raising=False)
        monkeypatch.setattr(validate._H, "ensure_lean_deps_fresh", lambda: (False, "stub"))

    def test_paper_only_failures_do_not_block(self, monkeypatch):
        self._registry(monkeypatch, {"p1": "papers_prose", "p2": "bundles_readiness"})
        rc, _ = _run(["--scope", "substrate", "--no-archive"])
        assert rc == 0

    def test_a_substrate_failure_STILL_blocks(self, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — the assertion that keeps the flag honest."""
        self._registry(monkeypatch, {"p1": "papers_prose", "s1": "lean_toolchain"})
        rc, _ = _run(["--scope", "substrate", "--no-archive"])
        assert rc == 1, "a substrate failure was masked by --scope substrate"

    def test_the_default_scope_is_unchanged(self, monkeypatch):
        self._registry(monkeypatch, {"p1": "papers_prose"})
        rc, _ = _run(["--no-archive"])
        assert rc == 1, "--scope defaults to `all`; paper failures must still block"

    def test_the_failures_are_still_REPORTED_when_not_blocking(self, monkeypatch):
        """Scoping what blocks must never scope what is measured or shown."""
        self._registry(monkeypatch, {"p1": "papers_prose"})
        rc, err = _run(["--scope", "substrate", "--no-archive"])
        assert rc == 0
        assert "paper-corpus" in err, (
            "exiting 0 without saying why turns a scoped gate into a silent one")


class TestScopePartitionIsTotal:
    """`--scope substrate` decides what BLOCKS. An unclassified check module would
    default to "substrate" and silently acquire the power to veto a Lean wave close —
    so the partition must be total, and a new module must fail rather than default.
    """

    def test_every_check_module_is_classified(self):
        mods = validate._check_modules()
        known = validate._PAPER_SIDE_MODULES | validate._SUBSTRATE_SIDE_MODULES
        assert not (mods - known), (
            f"check module(s) in neither side of the --scope partition: "
            f"{sorted(mods - known)}. Add each to _PAPER_SIDE_MODULES or "
            f"_SUBSTRATE_SIDE_MODULES in validate.py — defaulting is how a paper-side "
            f"check silently gains the power to block a pure-Lean wave.")

    def test_the_partition_names_no_module_that_does_not_exist(self):
        mods = validate._check_modules()
        known = validate._PAPER_SIDE_MODULES | validate._SUBSTRATE_SIDE_MODULES
        assert not (known - mods), (
            f"the partition names module(s) that own no registered check: "
            f"{sorted(known - mods)} — stale entries make the totality assertion above "
            f"weaker than it looks.")

    def test_the_two_sides_are_disjoint(self):
        assert not (validate._PAPER_SIDE_MODULES & validate._SUBSTRATE_SIDE_MODULES)

    def test_a_memoized_check_is_attributed_to_its_REAL_module(self):
        """`memoize_check` rebinds `__module__` to `_memo`. Attributing by the wrapper
        would classify every memoized check by where the DECORATOR lives."""
        assert validate._leaf_module_of("axiom_closure_allowlist") == "lean_toolchain", (
            "a memoized check is being attributed to the memo wrapper, not its own module")


class TestTheFloorCountsMEASUREDNotMERELYRAN:
    """The `--ci` floor must count MEASURED checks, not registry entries.

    ⚠️ The distinction IS the guard. `CI_MIN_CHECKS_RUN` exists so a run on a
    machine missing a toolchain cannot report a green tick over a shrunken
    suite — and a check that returned WITHOUT MEASURING (absent artifact, dead
    toolchain) is precisely that case wearing a pass.

    ⚠️ AND IT WAS COVERED BY NOTHING RUNNABLE. `test_the_LIVE_floor_has_ZERO_
    headroom` compares the constant to its own definition (`len(_CHECKS) -
    len(CI_SKIP)`), so it catches an arithmetic slip and nothing else.
    `test_the_LIVE_floor_matches_what_a_REAL_run_MEASURES` is `@pytest.mark.slow`
    AND re-implements the measured filter in its own body from `run_checks()` —
    it never calls `main()`, where the floor actually lives. A chunk reviewer
    replaced `validate.py`'s `measured = [n for n, r in results.items() if
    r.measured]` with `measured = list(results)` and 22 tests passed.

    These drive the REAL `main()` on a tiny registry, which is the only place the
    decision is made.
    """

    @staticmethod
    def _unmeasured():
        return CheckResult(passed=True, measured=False, details=[])

    def test_an_unmeasured_pass_does_not_count_toward_the_floor(
            self, tiny_registry, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — `measured = list(results)` reddens this."""
        # One of the six real checks measured nothing; the other five did.
        patched = []
        for s in validate._CHECKS:
            if s.name == "c0":
                patched.append(CheckSpec(name=s.name, description=s.description,
                                         func=self._unmeasured))
            else:
                patched.append(s)
        monkeypatch.setattr(validate, "_CHECKS", patched, raising=False)

        n_real = len(patched) - len(_cfg.CI_SKIP)
        monkeypatch.setattr(_cfg, "CI_MIN_CHECKS_RUN", n_real)

        rc, err = _run(["--ci", "--no-archive"])
        assert rc == 1, (
            "an UNMEASURED pass was counted toward the coverage floor — a run "
            "where a toolchain is absent now reports green over a shrunken suite, "
            "which is the exact failure CI_MIN_CHECKS_RUN exists to prevent")
        assert "WITHOUT MEASURING" in err and "c0" in err, (
            f"the unmeasured check was not named in the report: {err!r}")

    def test_all_measured_at_exactly_the_floor_passes(self, tiny_registry, monkeypatch):
        """SILENT ON CORRECT DATA — the complement, so the test above is not vacuous.

        Without this, a floor that rejected EVERYTHING would satisfy the sibling.
        """
        n_real = len(validate._CHECKS) - len(_cfg.CI_SKIP)
        monkeypatch.setattr(_cfg, "CI_MIN_CHECKS_RUN", n_real)
        rc, err = _run(["--ci", "--no-archive"])
        assert rc == 0, f"all checks measured at exactly the floor should pass: {err!r}"
        assert "WITHOUT MEASURING" not in err


class TestPrintResultsRendersTheThirdState:
    """`print_results` must show UNMEASURED. Guards a change of my own.

    ⚠️ Before this, `measured` was rendered NOWHERE on the default path: two
    `CheckResult`s differing only in `measured` produced BYTE-IDENTICAL output,
    on the exact command CLAUDE.md tells everyone to run. The axis this suite
    exists to establish was visible only in `--json`, the archive, and a stderr
    line inside `--ci`.

    ⚠️ AND THE FIX SHIPPED UNGUARDED. A reviewer reverted the whole `_unmeasured`
    block and 159 tests passed — no test drives `print_results` at all; the only
    reference in `tests/` stubs it out.
    """

    @staticmethod
    def _render(_mp=None, **kw):
        """Render through the REAL `print_results`.

        The per-check detail block only renders for names in `_CHECKS` —
        `print_results` iterates the registry, not the results dict — so a
        synthetic result must be accompanied by a registered spec or its details
        are silently invisible. (Discovered the hard way: the first draft of
        these tests asserted on detail lines that were never printed.)
        """
        buf = io.StringIO()
        if _mp is not None:
            _mp.setattr(validate, "_CHECKS",
                        [CheckSpec(name=n, description=n, func=_ok) for n in kw],
                        raising=False)
        with contextlib.redirect_stdout(buf):
            validate.print_results(kw)
        return buf.getvalue()

    def test_an_unmeasured_check_is_visibly_distinct(self):
        """FIRES ON THE SEEDED DEFECT — reverting the block reddens this."""
        d = [Detail("pop", True, "21 of 21")]
        measured = self._render(demo=CheckResult(passed=True, measured=True, details=d))
        unmeasured = self._render(demo=CheckResult(passed=True, measured=False, details=d))
        assert measured != unmeasured, (
            "a check that measured NOTHING renders identically to one that "
            "measured everything — the whole `measured` axis is invisible to "
            "the reader of the default report")
        assert "did NOT MEASURE" in unmeasured
        assert "demo" in unmeasured.split("did NOT MEASURE", 1)[1], (
            "the unmeasured check must be NAMED, not merely counted")

    def test_the_unqualified_all_clear_is_withheld(self):
        """An all-green run over an unreached population must not read as clean."""
        d = [Detail("pop", True, "ok")]
        clean = self._render(a=CheckResult(passed=True, measured=True, details=d))
        partial = self._render(a=CheckResult(passed=True, measured=True, details=d),
                               b=CheckResult(passed=True, measured=False, details=d))
        assert "ALL CHECKS PASSED" in clean and "UNMEASURED list" not in clean
        assert "but see the UNMEASURED list above" in partial, (
            "an unqualified ALL CHECKS PASSED was printed over a population that "
            "was not reached")

    def test_a_skipped_member_detail_is_marked(self, monkeypatch):
        """The per-member axis, not just the check-level one."""
        out = self._render(monkeypatch, a=CheckResult(passed=True, measured=True, details=[
            Detail("sized", True, "D1: 12 pp"),
            Detail("skipped", True, "D9: stale PDF", warning=True, measured=False)]))
        skipped_line = next(l for l in out.splitlines() if "D9" in l)
        sized_line = next(l for l in out.splitlines() if "D1" in l)
        assert skipped_line.lstrip().startswith("\033[33m?\033[0m"), (
            f"a skipped member carries no distinguishing glyph: {skipped_line!r}")
        assert not sized_line.lstrip().startswith("\033[33m?\033[0m")
