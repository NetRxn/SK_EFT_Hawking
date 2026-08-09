"""TODO-D27 / ADR-011 F-07 part 2: the Lean-module freshness trigger.

Nine bundles — D6, D7, D8, D9, D10, D11, D12, I2, I3 — declared only synthetic source
tokens naming no directory, so `bundle_source_freshness` reported UNMEASURABLE for all
nine and the Stage-C absorption trigger could not fire on any of them.

Three measured facts shape what is tested here, and each was a wrong first answer:

1. **The field name is the trap.** Probing `lean_modules` returns 0 of 21 and reads as
   "no data exists"; the field is `lean_modules_referenced` (ACCURACY_LEDGER V56).

2. **Registration alone would NOT have closed the nine.** D6 and D7 — the two most in
   need of a trigger — register ZERO modules. The population had to include the
   DERIVED apex closure, which is declared for all 21.

3. **Not mtime — commit time.** The audit proposed Lean-module mtimes. A `git checkout`,
   a worktree creation or a fresh clone rewrites every mtime in the tree, which would
   mark all nine stale at once for a reason unrelated to content.
"""
from __future__ import annotations

import json
import os
import pathlib
import sys
from datetime import datetime, timedelta, timezone

import pytest

REPO = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "scripts"))

import check_bundle_source_freshness as cf  # noqa: E402

SOURCELESS = ["D6", "D7", "D8", "D9", "D10", "D11", "D12", "I2", "I3"]

#: ⚠️ The derived half of the population comes from the apex closure, which needs
#: a built `lean/.lake`. Without one `_derived_lean_modules()` correctly returns
#: `None` and every bundle reports UNMEASURED — which is the fix working, not a
#: regression, but it makes the live-corpus tests below vacuous. They SKIP rather
#: than fail, because "the Lean build is absent" is a different fact from "the
#: trigger is wrong", and collapsing the two is the defect this file guards.
_CLOSURE_AVAILABLE = cf._derived_lean_modules() is not None
_needs_closure = pytest.mark.skipif(
    not _CLOSURE_AVAILABLE,
    reason="lean/.lake not built — the derived apex closure is unavailable, so "
           "the live-corpus population cannot be measured (run "
           "`cd lean && lake build SKEFTHawking.ExtractDeps`)")


@pytest.fixture(scope="module")
def findings():
    return cf.check()


@_needs_closure
class TestTheNineSourcelessBundlesAreNowMeasured:
    def test_no_bundle_is_wholly_unmeasurable(self, findings):
        """The state F-07 exists to end. `source-UNMEASURABLE, Lean-measured` is a
        different message and is allowed: the source population genuinely is not
        measurable, and saying so beside a real measurement is honest."""
        dead = [f["bundle"] for f in findings
                if f["message"].startswith("UNMEASURABLE:")]
        assert dead == [], f"still unmeasurable on both populations: {dead}"

    @pytest.mark.parametrize("bundle", SOURCELESS)
    def test_each_sourceless_bundle_has_a_lean_population(self, bundle):
        idx = cf._lean_module_index()
        derived = cf._derived_lean_modules().get(bundle)
        times, _unresolved = cf._lean_module_change_times(
            bundle, idx, cf._git_last_commit_times(), cf._dirty_lean_paths(), derived)
        assert times, f"{bundle} has no resolvable Lean module to trigger on"

    def test_registration_alone_would_not_have_sufficed(self):
        """⚠️ The load-bearing measurement. D6 and D7 register ZERO modules, so a
        trigger built only on `lean_modules_referenced` — which is what the TODO
        entry proposed — would have left the two neediest bundles UNMEASURABLE."""
        assert cf._registered_lean_modules("D6") == []
        assert cf._registered_lean_modules("D7") == []
        derived = cf._derived_lean_modules()
        assert derived.get("D6") and derived.get("D7"), \
            "the derived closure is what closes D6/D7; if it is empty the trigger is back"


@_needs_closure
class TestModuleResolution:
    def test_the_dotted_path_beats_a_shared_stem(self):
        """`Basic` names five files; `Resurgence.Basic` names one. A stem-only
        resolver picks whichever the walk saw first."""
        idx = cf._lean_module_index()
        p = cf._resolve_lean_module("Resurgence.Basic", idx)
        assert p is not None and p.parts[-2:] == ("Resurgence", "Basic.lean")

    @pytest.mark.parametrize("spelling", [
        "QuantumNetwork/FidelityBounds",          # slash-separated
        "QuantumNetwork.FidelityBounds",          # dotted
        "SKEFTHawking.QuantumNetwork.FidelityBounds",   # namespace-prefixed
        "FidelityBounds",                          # bare stem
    ])
    def test_all_four_spellings_resolve_to_one_file(self, spelling):
        """Names were typed by hand at lift time and arrive in all four shapes.
        Normalising them took corpus resolution from 328 to 357 of 384."""
        idx = cf._lean_module_index()
        p = cf._resolve_lean_module(spelling, idx)
        assert p is not None and p.stem == "FidelityBounds"

    def test_a_name_matching_no_file_is_reported_not_dropped(self):
        """27 registered names resolve to nothing — renamed or never created. They
        are neither declarations (probed against all 40 701 records: zero hits) nor
        files, and a trigger that silently skipped them would shrink its own
        population without saying so."""
        idx = cf._lean_module_index()
        assert cf._resolve_lean_module("WKBSpectrum", idx) is None
        unresolved_reports = [f for f in cf.check()
                              if "resolve to no file" in f["message"]]
        assert unresolved_reports, "unresolved names must be surfaced, not dropped"

    def test_one_file_reached_by_two_spellings_counts_once(self):
        """The closure emits `SKEFTHawking.EffectiveMediumBounds` and registration
        emits `EffectiveMediumBounds`. A name-keyed union counted D11 at 44 modules
        where 22 files exist, and printed the same module twice in the sample."""
        idx = cf._lean_module_index()
        times, _ = cf._lean_module_change_times(
            "D11", idx, cf._git_last_commit_times(), cf._dirty_lean_paths(),
            cf._derived_lean_modules().get("D11"))
        paths = {cf._resolve_lean_module(n, idx) for n in times}
        assert len(paths) == len(times), "population is not path-deduplicated"


class TestTheTriggerUsesCommitTimeNotMtime:
    def test_commit_times_are_available_for_the_lean_tree(self):
        commits = cf._git_last_commit_times()
        assert len(commits) > 100, "git log produced no usable map"
        assert all(isinstance(v, datetime) for v in commits.values())

    def test_a_clean_file_ignores_its_mtime(self, tmp_path):
        """The whole point. Touch nothing on disk: a file whose mtime is NOW but
        whose last commit is old must report the OLD time, or a checkout marks
        every bundle stale at once."""
        idx = cf._lean_module_index()
        path = cf._resolve_lean_module("SKEFTHawking.WKBConnection", idx)
        assert path is not None
        rel = str(path.relative_to(cf.PROJECT_ROOT))
        commits = cf._git_last_commit_times()
        assert rel in commits, "fixture module is untracked; pick another"
        now = datetime.now(timezone.utc)
        # D7 registers zero modules, so the only name in the population is the one
        # passed here and the label is unambiguous.
        times, _ = cf._lean_module_change_times(
            "D7", idx, commits, set(), {"SKEFTHawking.WKBConnection"})
        assert times["SKEFTHawking.WKBConnection"] < now - timedelta(days=1)

    def test_a_dirty_file_falls_back_to_mtime(self):
        """Uncommitted means changed-and-not-yet-history; the commit time would
        describe the version before the edit."""
        idx = cf._lean_module_index()
        path = cf._resolve_lean_module("SKEFTHawking.WKBConnection", idx)
        rel = str(path.relative_to(cf.PROJECT_ROOT))
        times, _ = cf._lean_module_change_times(
            "D7", idx, cf._git_last_commit_times(), {rel},
            {"SKEFTHawking.WKBConnection"})
        mtime = datetime.fromtimestamp(path.stat().st_mtime, timezone.utc)
        assert times["SKEFTHawking.WKBConnection"] == mtime


LIFT = datetime(2026, 6, 1, tzinfo=timezone.utc)


@pytest.fixture
def synthetic_bundle(tmp_path, monkeypatch):
    """A bundle corpus of exactly one bundle, `ZZ`, that this file OWNS.

    ⚠️ Everything here exists so the tests below can assert what `cf.check()`
    CONCLUDES. The previous verdict tests called `_lean_module_change_times`
    (which returns *times*, not a verdict) and then recomputed `t > last_lift`
    in the test body — so they asserted their own arithmetic, and replacing the
    production predicate with `False` left them green. A test that reimplements
    the predicate it is pinning cannot fail when the predicate is wrong.

    Returns a driver: `run(source_mtime=..., lean_at=..., write=...)` builds the
    corpus, runs the real `check()`, and hands back its findings plus whatever
    landed in the bundle's `bundle_metadata.json`.
    """
    import bundle_migration
    import sentence_state

    papers = tmp_path / "papers"
    (papers / "ZZ").mkdir(parents=True)
    (papers / "srcpaper").mkdir()
    mapping = tmp_path / "PAPER_DRAFT_MAPPING.md"
    mapping.write_text("(patched away; parse_mapping is stubbed)")

    monkeypatch.setattr(cf, "PAPERS_DIR", papers)
    monkeypatch.setattr(cf, "MAPPING_DOC", mapping)
    monkeypatch.setattr(bundle_migration, "parse_mapping",
                        lambda _text: {"srcpaper": {"bundle_destinations": ["ZZ"]}})
    monkeypatch.setattr(sentence_state, "_VALID_BUNDLE_TARGETS", {"ZZ"})

    md_path = papers / "ZZ" / "bundle_metadata.json"
    src = papers / "srcpaper" / "paper_draft.tex"

    def run(*, source_mtime: datetime, lean_at: datetime | None = None,
            write: bool = False):
        md_path.write_text(json.dumps({"last_lift": LIFT.isoformat()}, indent=2))
        src.write_text("body\n")
        ts = source_mtime.timestamp()
        os.utime(src, (ts, ts))

        if lean_at is None:
            # Isolate the source leg: one None input makes the Lean leg report
            # UNMEASURED for every bundle, which is its documented behaviour.
            monkeypatch.setattr(cf, "_git_last_commit_times", lambda: None)
        else:
            name = "SKEFTHawking.Synthetic"
            leanfile = tmp_path / "lean" / "SKEFTHawking" / "Synthetic.lean"
            leanfile.parent.mkdir(parents=True, exist_ok=True)
            leanfile.write_text("-- synthetic\n")
            rel = "lean/SKEFTHawking/Synthetic.lean"
            monkeypatch.setattr(cf, "_lean_module_index", lambda: {"Synthetic": leanfile})
            monkeypatch.setattr(cf, "_git_last_commit_times", lambda: {rel: lean_at})
            monkeypatch.setattr(cf, "_dirty_lean_paths", lambda: set())
            monkeypatch.setattr(cf, "_derived_lean_modules", lambda: {"ZZ": {name}})
            monkeypatch.setattr(cf, "PROJECT_ROOT", tmp_path)

        findings = cf.check(write_metadata=write)
        return findings, json.loads(md_path.read_text())

    return run


def _msgs(findings, prefix):
    return [f for f in findings if f["message"].startswith(prefix)]


class TestTheSourceStalenessVerdictItself:
    """⚠️ CHECK 22's ORIGINAL AND PRIMARY JOB, and it was entirely unpinned.

    Round 1 found the *Lean* leg's verdict untested and pinned it. The **source**
    leg had the identical defect and nobody looked: replacing `mt > last_lift`
    with `False` — which makes the check structurally incapable of ever reporting
    a source-stale bundle — left all 90 tests across this file and
    `test_d5_freshness.py` GREEN. `stale_sources` was never non-empty, the
    `freshness-stale:` finding was unreachable, and `freshness_stale=true` — the
    flag `LATE_PHASE6_ABSORPTION_PROTOCOL` Stage A keys on — was never written.

    Both directions, through the real `check()`."""

    def test_a_source_edited_after_the_lift_is_STALE(self, synthetic_bundle):
        findings, _ = synthetic_bundle(source_mtime=LIFT + timedelta(days=30))
        assert _msgs(findings, "freshness-stale"), (
            "a source paper modified 30 days AFTER last_lift must be reported "
            f"stale; got {[f['message'] for f in findings]}")

    def test_a_source_edited_before_the_lift_is_NOT_stale(self, synthetic_bundle):
        """The silent direction. A trigger that fires on everything tells the
        absorption protocol nothing about which bundle needs work."""
        findings, _ = synthetic_bundle(source_mtime=LIFT - timedelta(days=30))
        assert not _msgs(findings, "freshness-stale")
        assert _msgs(findings, "source-fresh")

    def test_the_STALE_verdict_reaches_the_metadata_flag(self, synthetic_bundle):
        """Stage A reads `freshness_stale` from the file, not the finding text.
        A verdict no consumer can see is the same defect as no verdict."""
        _, md = synthetic_bundle(source_mtime=LIFT + timedelta(days=30), write=True)
        assert md["freshness_stale"] is True

    def test_the_FRESH_verdict_clears_the_metadata_flag(self, synthetic_bundle):
        """⚠️ Both legs must be MEASURED for a clear. A fresh source beside a dark
        Lean leg leaves the flag untouched rather than writing False — absence of
        measurement is not evidence of freshness — so this drives a real (old)
        Lean time rather than the isolating `lean_at=None`."""
        _, md = synthetic_bundle(source_mtime=LIFT - timedelta(days=30),
                                 lean_at=LIFT - timedelta(days=30), write=True)
        assert md.get("freshness_stale") is False

    def test_an_UNMEASURED_lean_leg_does_NOT_write_a_fresh_flag(self, synthetic_bundle):
        """The gate itself. With the Lean leg dark, a source-fresh bundle must
        leave `freshness_stale` unwritten, not cleared."""
        _, md = synthetic_bundle(source_mtime=LIFT - timedelta(days=30), write=True)
        assert "freshness_stale" not in md


class TestTheLeanStalenessVerdictItself:
    """⚠️ THE VERDICT, not the population — now asserted through `check()`.

    Every other test in this file asserts properties of the *inputs*: that names
    resolve, that times exist, that commit-time beats mtime. Replacing the
    predicate `t > last_lift` with `False` left all 80 tests green. The first fix
    for that recomputed the predicate in the test body and was equally blind (the
    only test that fired was `.lake`-gated, so it SKIPPED in exactly the
    environment where the blindness was observed). These drive the real check
    over a synthetic corpus and need no Lean build at all."""

    def _lean(self, run, *, late: bool):
        # Source held fresh so the only thing that can move the verdict is Lean.
        return run(source_mtime=LIFT - timedelta(days=60),
                   lean_at=LIFT + timedelta(days=30 if late else -30))

    def test_a_module_changed_after_the_lift_is_STALE(self, synthetic_bundle):
        findings, _ = self._lean(synthetic_bundle, late=True)
        assert _msgs(findings, "lean-stale"), (
            "a module committed 30 days AFTER last_lift must be reported stale; "
            f"got {[f['message'] for f in findings]}")

    def test_a_module_changed_before_the_lift_is_NOT_stale(self, synthetic_bundle):
        """The silent direction."""
        findings, _ = self._lean(synthetic_bundle, late=False)
        assert not _msgs(findings, "lean-stale")

    def test_a_source_fresh_LEAN_STALE_bundle_still_flags(self, synthetic_bundle):
        """⚠️ The exact hole the round-2 silent-failure hunt found: the
        source-measurable branch cleared `freshness_stale` from `not
        stale_sources` alone, ignoring the Lean verdict. 12 real bundles were
        written `False` while the same run emitted `lean-stale` — D2 at 48 of 85
        modules, L2 at 42 of 45. Stage A then never fired for any of them."""
        _, md = synthetic_bundle(source_mtime=LIFT - timedelta(days=60),
                                 lean_at=LIFT + timedelta(days=30), write=True)
        assert md["freshness_stale"] is True, (
            "source-fresh + Lean-stale must still be stale overall")


class TestADegradedInputIsUNMEASUREDNotASmallerNumber:
    """⚠️ Each of the three Lean-leg inputs used to fall back silently, and each
    fell back in a direction that LOOKED like a measurement.

    Measured before the fix, by forcing each to its empty value:
      * `_derived_lean_modules() -> {}`  — D5's population 29 -> 18 and its stale
        count 7 -> 2, D9 97 -> 77 and 12 -> 7. Smaller numbers, no signal, and a
        bundle whose only staleness came through the closure reads FRESH. This is
        the `{}`-means-no-problem shape already removed from
        `bundle_readiness._blocked_p1_gates_by_paper`.
      * `_git_last_commit_times() -> {}` — every path takes the mtime branch, the
        signal this module's header rejects by name. E2 2/8 -> 8/8 lean-stale,
        I2 17/36 -> 36/36, L2 42/45 -> 45/45.
      * `_dirty_lean_paths() -> set()` — a just-rewritten module reads fresh,
        which is the exact failure the function exists to prevent, in the
        direction of clean.
    """

    @pytest.mark.parametrize("input_name", [
        "_git_last_commit_times", "_dirty_lean_paths", "_derived_lean_modules"])
    def test_a_failed_input_reports_UNMEASURED_for_every_bundle(
            self, input_name, monkeypatch):
        monkeypatch.setattr(cf, input_name, lambda: None)
        findings = cf.check()
        unmeasured = [f for f in findings if "UNMEASURED" in f["message"]]
        assert len(unmeasured) >= 21, (
            f"{input_name} failing produced only {len(unmeasured)} UNMEASURED "
            f"findings; every bundle's Lean leg is unmeasured when an input dies")

    @pytest.mark.parametrize("input_name", [
        "_git_last_commit_times", "_dirty_lean_paths", "_derived_lean_modules"])
    def test_a_failed_input_fabricates_NO_staleness_number(
            self, input_name, monkeypatch):
        """The sharp half. A degraded input must not yield a NUMBER, because a
        number is indistinguishable from a measurement."""
        monkeypatch.setattr(cf, input_name, lambda: None)
        findings = cf.check()
        assert not [f for f in findings if f["message"].startswith("lean-stale")], \
            f"{input_name} failing still produced a lean-stale count"

    @_needs_closure
    def test_the_healthy_path_still_measures(self):
        """SILENT ON CORRECT DATA — the guard must not make the leg unreachable."""
        findings = cf.check()
        assert [f for f in findings if f["message"].startswith("lean-stale")]

    def test_a_renamed_uncommitted_module_counts_as_dirty(self):
        r"""`git status --porcelain` renders a rename as `R  old -> new`. Parsing
        `line[3:]` whole yields `"old -> new"`, which matches no path on disk, so
        a renamed-but-uncommitted module was invisible to the dirty check."""
        import subprocess
        real = subprocess.run
        def fake(cmd, *a, **k):
            if cmd[:2] == ["git", "status"]:
                class R:
                    stdout = 'R  lean/SKEFTHawking/Old.lean -> lean/SKEFTHawking/New.lean\n'
                return R()
            return real(cmd, *a, **k)
        subprocess.run, saved = fake, subprocess.run
        try:
            assert cf._dirty_lean_paths() == {"lean/SKEFTHawking/New.lean"}
        finally:
            subprocess.run = saved


@_needs_closure
class TestPerPhaseAbsorptionRows:
    """F-09. D10, D11 and D12 each consolidated every one of their phases into a
    single `<X>_initial_draft` row, so the smallest unit of absorption was the whole
    bundle. ⚠️ The TODO entry named nine phases (6EA-6EE, 6CA/6CB/6CD/6CE); the true
    population is TWELVE — D10's 6BA/6BB/6BC carry the identical defect and were not
    listed."""

    EXPECTED = {
        "_phase6BA_lean_only": "D10", "_phase6BB_lean_only": "D10",
        "_phase6BC_lean_only": "D10",
        "_phase6CA_lean_only": "D11", "_phase6CB_lean_only": "D11",
        "_phase6CD_lean_only": "D11", "_phase6CE_lean_only": "D11",
        "_phase6ED_lean_only": "D11",
        "_phase6EA_lean_only": "D12", "_phase6EB_lean_only": "D12",
        "_phase6EC_lean_only": "D12", "_phase6EE_lean_only": "D12",
    }

    def _mapping(self):
        from bundle_migration import parse_mapping
        return parse_mapping((REPO / "docs" / "PAPER_DRAFT_MAPPING.md").read_text())

    @pytest.mark.parametrize("key,bundle", sorted(EXPECTED.items()))
    def test_each_phase_has_its_own_row(self, key, bundle):
        m = self._mapping()
        assert key in m, f"{key} has no mapping row — absorption is bundle-wide again"
        assert m[key]["bundle_destinations"] == [bundle]

    def test_6CC_has_no_row_because_it_never_shipped(self):
        """6CC is PARKED, gated on 5q.G. A row for a phase with no substrate would
        register an absorption unit that can never be absorbed."""
        assert "_phase6CC_lean_only" not in self._mapping()
