"""ADR-009 §Deferred item 0 — one `lean_deps.json` snapshot per full run.

WHAT THIS PROTECTS
------------------
Eight checks read `lean/lean_deps.json`. Measured against the live registry on
2026-08-04, they straddle the regenerator: `counts_fresh` is at position **29**,
with **five readers before it** (`tracked_hypothesis_ledger` 4,
`formula_grounding` 6, `vacuous_statement_audit` 7, `nogo_substrate_integrity` 8,
`native_decide_regression` 9) and **three after** (54, 55, 57).

Nothing refreshed the artifact before position 29, and
`validate_helpers.load_lean_deps()` reads it directly with no hash guard. So on a
run where a `.lean` source had changed — a wave close — the first five validated
the PREVIOUS extraction while the last three validated the fresh one, inside one
run. Among the five is the `native_decide_regression` ratchet, whose whole
purpose is to notice trust surface the CURRENT wave added.

`validate.main()` now calls `ensure_lean_deps_fresh()` once, up front, for a full
run. These tests hold both halves of that: it refreshes when stale, it does
nothing when fresh, and — the property most likely to be regressed by a future
"why not just refresh in the loader?" — it must NOT fire for a `--check` run.

WHY THE `--check` EXEMPTION IS LOAD-BEARING
--------------------------------------------
`scripts/pre-commit-sync.sh` runs `--check native_decide_regression` in the commit
gate, and says plainly (`:72-74`, and the file header) that the gate must NEVER
run the 30-minute ExtractDeps: *"never block a routine .lean commit (that would
stall the /goal loop)"*. Refreshing inside `load_lean_deps()` — the obvious fix —
would have done exactly that. `test_check_run_does_not_refresh` is what stops it
being reintroduced.

MUTATION-VERIFIED (2026-08-04), each direction independently:
  * delete the `if not args.check:` guard in `main()`  -> `test_check_run_does_not_refresh` FAILS
  * delete the `_H.ensure_lean_deps_fresh()` call      -> `test_full_run_refreshes` FAILS
  * make `ensure_lean_deps_fresh` unconditional        -> `test_no_extraction_when_fresh` FAILS
  * let `_run_extraction` propagate its exception      -> `test_refresh_failure_never_raises` FAILS
Clean negative control: unmutated tree, all pass.
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT / "scripts"))

import validate as v  # noqa: E402
import validate_helpers as _H  # noqa: E402


class TestEnsureLeanDepsFresh:
    """The pure-ish core: hash-guarded, best-effort, never raises."""

    def test_no_extraction_when_fresh(self, monkeypatch):
        """SILENT on correct data — a fresh hash must not trigger an extraction.

        This is the half that keeps the fix cheap. `_needs_refresh()` is 46 ms;
        `_run_extraction()` is up to 30 minutes.
        """
        import extract_lean_deps as eld
        called = []
        monkeypatch.setattr(eld, "_needs_refresh", lambda: False)
        monkeypatch.setattr(eld, "_run_extraction", lambda: called.append(1))

        refreshed, note = _H.ensure_lean_deps_fresh()

        assert refreshed is False
        assert not called, (
            "ensure_lean_deps_fresh() ran an extraction while the hash matched. "
            "The guard is what makes calling this on every full run affordable."
        )
        assert "fresh" in note.lower()

    def test_refreshes_when_stale(self, monkeypatch):
        """FIRES on a seeded defect — a hash mismatch must trigger the refresh."""
        import extract_lean_deps as eld
        called = []
        monkeypatch.setattr(eld, "_needs_refresh", lambda: True)
        monkeypatch.setattr(eld, "_run_extraction", lambda: called.append(1))

        refreshed, note = _H.ensure_lean_deps_fresh()

        assert refreshed is True
        assert called == [1], (
            "lean_deps.json was stale and no extraction ran. The five checks at "
            "registry positions 4-9 would then validate the previous extraction "
            "while those at 54-57 validate the fresh one."
        )
        assert "refresh" in note.lower()

    def test_refresh_failure_never_raises(self, monkeypatch):
        """A failed refresh is reported, never propagated.

        Each call site keeps its OWN missing/stale verdict (ADR-009 H4). This
        helper is a best-effort freshening, not a gate — if it raised, one
        unavailable toolchain would take down all 59 checks.
        """
        import extract_lean_deps as eld

        def _boom():
            raise RuntimeError("ExtractDeps failed")

        monkeypatch.setattr(eld, "_needs_refresh", lambda: True)
        monkeypatch.setattr(eld, "_run_extraction", _boom)

        refreshed, note = _H.ensure_lean_deps_fresh()

        assert refreshed is False
        assert "failed" in note.lower() and "ExtractDeps failed" in note

    def test_missing_extract_module_is_a_no_op(self, monkeypatch):
        """A partial checkout degrades to exactly the prior behaviour."""
        monkeypatch.setitem(sys.modules, "extract_lean_deps", None)
        refreshed, note = _H.ensure_lean_deps_fresh()
        assert refreshed is False
        assert "skipped" in note.lower() or "unavailable" in note.lower()


class TestMainWiring:
    """Where the call is made from — the part the commit gate depends on."""

    @staticmethod
    def _spy(monkeypatch):
        """Neutralise the 447-second run; record whether the refresh was asked for."""
        calls = []
        monkeypatch.setattr(_H, "ensure_lean_deps_fresh",
                            lambda: (calls.append(1), (False, "stub"))[1])
        monkeypatch.setattr(v, "run_checks", lambda check_filter=None, skip=None: {})
        monkeypatch.setattr(v, "print_results", lambda results: None)
        return calls

    def test_full_run_refreshes(self, monkeypatch):
        """A full run takes one snapshot before any check reads the artifact."""
        calls = self._spy(monkeypatch)
        v.main(["--no-archive"])
        assert calls == [1], (
            "a full validate.py run did not refresh lean_deps.json first, so its "
            "readers can still straddle counts_fresh (position 29) and observe two "
            "different extractions."
        )

    def test_check_run_does_not_refresh(self, monkeypatch):
        """⚠️ THE COMMIT-GATE GUARANTEE.

        `pre-commit-sync.sh` runs `--check native_decide_regression` and must never
        trigger ExtractDeps (`:72-74`). If this fails, routine `.lean` commits can
        block for up to 30 minutes.
        """
        calls = self._spy(monkeypatch)
        v.main(["--check", "native_decide_regression", "--no-archive"])
        assert calls == [], (
            "a --check run attempted a lean_deps refresh. scripts/pre-commit-sync.sh "
            "runs --check native_decide_regression in the commit gate and states it "
            "must NEVER run the 30-minute ExtractDeps."
        )

    @pytest.mark.parametrize("argv", [["--list"], ["--check", "nonexistent_check"]])
    def test_non_running_invocations_do_not_refresh(self, monkeypatch, argv):
        """`--list` and an unknown `--check` return before any work; neither
        should pay for a hash walk."""
        calls = self._spy(monkeypatch)
        v.main(argv)
        assert calls == []
