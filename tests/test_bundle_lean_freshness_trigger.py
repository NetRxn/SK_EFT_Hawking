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

import pathlib
import sys
from datetime import datetime, timedelta, timezone

import pytest

REPO = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "scripts"))

import check_bundle_source_freshness as cf  # noqa: E402

SOURCELESS = ["D6", "D7", "D8", "D9", "D10", "D11", "D12", "I2", "I3"]


@pytest.fixture(scope="module")
def findings():
    return cf.check()


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
