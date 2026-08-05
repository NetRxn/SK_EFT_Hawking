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
mostly about. A green tick over 48 of 59 is worse than no CI.

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
from validation._registry import CheckResult, CheckSpec  # noqa: E402


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
