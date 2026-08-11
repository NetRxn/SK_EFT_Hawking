"""`scripts/gate_precheck.py` — the stage-gate runner. Previously ZERO tests.

WHY THIS FILE EXISTS
--------------------
`gate_precheck.py` is what the wave-close skill actually invokes
(`.claude/plugins/skeft-qa/skills/wave-close/SKILL.md:34`), so it is the mechanism by
which the 14-stage protocol enforces anything at all. It had no tests, and two wrong
DEFAULTS survived in it:

* `s13` ran `validate.py` **without `--force-latex`**, so `paper_latex_compiles`
  returned PASS with detail *"SKIPPED (slow)"*. "Full green over Stages 1–12" was
  therefore achievable with a bundle draft that does not compile — and D3 does not,
  with 2 fatal errors, measured 2026-08-05. The "slow" premise was stale too: the
  forced run is **16.8 s**.
* Nothing anywhere passed `--strict`, so the six submission-gate legs never executed,
  despite `WAVE_EXECUTION_PIPELINE.md` Invariant #12 calling `--strict` *"mandatory at
  the Paper Submission Gate"*.

Neither is exotic — both are one missing flag — and both were invisible because the
runner that would have shown them was untested. These tests assert the FLAGS, because
the flags are the whole behaviour: this module's job is to decide what `validate.py`
gets asked.

They run the real `main()` with `subprocess.run` replaced by a recorder — no
`validate.py` invocation, so the file stays fast enough to sit in the default suite.
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT / "scripts"))

import gate_precheck as gp  # noqa: E402


class _Recorder:
    """Stands in for `subprocess.run`; records argv and returns a chosen rc."""

    def __init__(self, rc: int = 0):
        self.calls: list[list[str]] = []
        self.rc = rc

    def __call__(self, cmd, **kw):
        self.calls.append(list(cmd))
        outer = self

        class _R:
            returncode = outer.rc
        return _R()

    def flags(self) -> set[str]:
        return {a for c in self.calls for a in c if a.startswith("--")}


@pytest.fixture
def rec(monkeypatch):
    r = _Recorder()
    monkeypatch.setattr(gp.subprocess, "run", r)
    return r


class TestStageWiring:

    def test_an_unknown_stage_is_rejected(self, rec):
        """rc 2, and nothing dispatched. A gate that silently accepted a typo'd stage
        name would run zero checks and report success — `all([])` is `True`, the
        failure mode `validate.py`'s own CLI guards against."""
        assert gp.main(["s99"]) == 2
        assert rec.calls == []

    def test_no_stage_is_rejected(self, rec):
        assert gp.main([]) == 2
        assert rec.calls == []

    def test_every_declared_stage_dispatches_something(self, rec):
        """A stage present in the table but dispatching nothing would pass vacuously."""
        for stage in gp.STAGE_CHECKS:
            r = _Recorder()
            import subprocess as _sp
            orig, _sp.run = _sp.run, r
            gp.subprocess.run = r
            try:
                gp.main([stage])
            finally:
                _sp.run = orig
            assert r.calls, f"stage {stage} dispatched no command"

    def test_a_failing_check_fails_the_gate(self, monkeypatch):
        """The gate must propagate a non-zero rc — it exists to STOP an expensive
        reviewer dispatch, so swallowing a failure is the whole defect."""
        monkeypatch.setattr(gp.subprocess, "run", _Recorder(rc=1))
        assert gp.main(["s13"]) != 0

    def test_prechecks_never_archive(self, rec):
        """A precheck runs before every reviewer dispatch, so it must be
        side-effect-free; without `--no-archive` each run writes a timestamped report
        and dirties the tree."""
        for stage in gp.STAGE_CHECKS:
            r = _Recorder()
            monkey = gp.subprocess.run
            gp.subprocess.run = r
            try:
                gp.main([stage])
            finally:
                gp.subprocess.run = monkey
            assert "--no-archive" in r.flags(), f"{stage} archives"


class TestTheTwoDefaultsThatWereWrong:
    """These are the tests whose absence let the defaults ship."""

    def test_s13_forces_the_latex_compile(self, rec):
        """⚠️ Without `--force-latex`, `paper_latex_compiles` returns PASS with
        "SKIPPED (slow)" — so s13's "full green over Stages 1-12" was reachable with a
        non-compiling draft, and D3 does not compile (2 fatal errors, measured
        2026-08-05). Stage 13 dispatches an expensive adversarial review; sending it a
        draft that cannot be typeset is precisely what this gate exists to prevent."""
        gp.main(["s13"])
        assert "--force-latex" in rec.flags(), (
            "gate_precheck s13 no longer forces the LaTeX compile — the wave-close "
            "gate can pass with a bundle draft that does not compile")

    def test_the_submission_gate_runs_strict(self, rec):
        """⚠️ `WAVE_EXECUTION_PIPELINE.md` Invariant #12 calls `--strict` "mandatory at
        the Paper Submission Gate", and six checks carry a strict-only leg — but until
        2026-08-05 no caller passed it, so an invariant declared mandatory ran nowhere."""
        gp.main(["submission"])
        assert "--strict" in rec.flags(), (
            "the submission gate no longer passes --strict — the six strict legs "
            "(parameter_provenance human verification, provenance DOIs, bibitem titles, "
            "embedded citations, axiom allowlist, bundle source freshness) run nowhere")

    def test_the_submission_gate_is_a_superset_of_s13(self, monkeypatch):
        """Submission must not be able to pass on less than a wave close does."""
        subs, s13 = _Recorder(), _Recorder()
        monkeypatch.setattr(gp.subprocess, "run", subs); gp.main(["submission"])
        monkeypatch.setattr(gp.subprocess, "run", s13); gp.main(["s13"])
        assert s13.flags() - {"--no-archive"} <= subs.flags(), (
            f"s13 asks for {s13.flags()} which submission does not: "
            f"{s13.flags() - subs.flags()}")

    def test_wave_close_does_NOT_run_strict(self, rec):
        """The deliberate half of the split, and it is load-bearing.

        `bundle_source_freshness` WARNs whenever a source paper moved after the last
        lift — the NORMAL state of an in-progress bundle. Promoting that to a hard fail
        at every wave close would fire the gate on correct work, and a gate that fires
        on correct work gets switched off. ADR-009 §Deferred item 6 reached this split
        by measurement: `--strict` is a correctly-designed submission-time mode, and
        what was missing was a CALLER, not a change of default.
        """
        gp.main(["s13"])
        assert "--strict" not in rec.flags(), (
            "wave close now runs --strict; that hard-fails on in-progress bundles "
            "whose sources legitimately moved since their last lift")
