"""ADR-009 §Deferred item 1 — the native_decide ratchet measures live substrate.

`native_decide_regression` read `docs/counts.json`. The metric is a pure function
of `lean_deps.json`; `update_counts.py` merely records it. Reading the recording
had two failure modes:

* full run — the check sits at canonical position ~9 and `counts_fresh` rewrites
  `counts.json` at ~29, so the ratchet compared a snapshot taken before the
  current wave's Lean changes;
* **commit gate** — it is one of only three checks invoked, in ISOLATION, so
  `counts_fresh` never runs at all. That is the one moment the ratchet can
  hard-block `main`, and no ordering of the suite reaches it.

Measured when the fix landed: `counts.json` was already stale
("lean_deps.json newer than counts.json"). The recorded and live values happened
to agree at 546, so the defect had not yet produced a wrong verdict — which is
precisely why it survived.

D5: both directions. The seeded defect is a declaration that newly depends on a
`native_decide` axiom; the correct-data case is a substrate at or under the ceiling.
Both run against the pure core with synthetic declaration records, so the tests do
not depend on the live 70 MB file or on the ceiling's current value.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT / "scripts"))

import validate_helpers as _H  # noqa: E402
from update_counts import is_native_decide_axiom, native_decide_decls  # noqa: E402
from validation.checks import lean_toolchain as lt  # noqa: E402


def _decl(name: str, *, nd: bool = False, core=None, module="SKEFTHawking.X"):
    return {
        "name": name, "module": module, "kind": "theorem",
        "axiom_deps_project": (["SKEFTHawking.foo._native.native_decide.ax_1"] if nd else []),
        "axiom_deps_core": core or ["propext"],
    }


class TestPredicate:
    """One definition, shared by the generator and two checks."""

    @pytest.mark.parametrize("ax", [
        "SKEFTHawking.foo._native.native_decide.ax_1",
        "Lean.ofReduceBool",
        "Lean.trustCompiler",
    ])
    def test_recognises_compiler_trust_axioms(self, ax):
        assert is_native_decide_axiom(ax) is True

    @pytest.mark.parametrize("ax", ["propext", "Classical.choice", "Quot.sound"])
    def test_kernel_axioms_are_not_native_decide(self, ax):
        """The other direction — a predicate that flags `propext` would put the
        whole library in the trust surface."""
        assert is_native_decide_axiom(ax) is False


class TestClosurePopulation:
    def test_counts_only_declarations_touching_a_native_decide_axiom(self):
        data = [_decl("a"), _decl("b", nd=True), _decl("c"), _decl("d", nd=True)]
        assert len(native_decide_decls(data)) == 2

    def test_detects_it_via_the_core_axiom_list_too(self):
        """`Lean.ofReduceBool` arrives in `axiom_deps_core`, not `_project` — a
        filter that looked only at project axioms would under-count the surface."""
        data = [_decl("a", core=["propext", "Lean.ofReduceBool"])]
        assert len(native_decide_decls(data)) == 1

    def test_a_clean_substrate_has_an_empty_closure(self):
        assert native_decide_decls([_decl("a"), _decl("b")]) == []


class TestRatchetVerdict:
    def _run(self, monkeypatch, data, ceiling, recorded=None):
        monkeypatch.setattr(_H, "load_lean_deps", lambda: data)
        monkeypatch.setattr(_H, "lean_deps_present", lambda: True)
        monkeypatch.setitem(__import__("src.core.constants", fromlist=["x"]).__dict__,
                            "NATIVE_DECIDE_DECL_CLOSURE_CEILING", ceiling)
        if recorded is not None:
            tmp = Path(monkeypatch.__dict__.setdefault("_tmp", Path("/tmp")))
            f = tmp / "counts_probe.json"
            f.write_text(json.dumps({"lean": {"native_decide_decl_closure": recorded}}))
            monkeypatch.setattr(_H, "COUNTS_JSON_PATH", f)
        return lt.check_native_decide_regression()

    def test_at_the_ceiling_passes(self, monkeypatch):
        """SILENT ON CORRECT DATA."""
        data = [_decl("a", nd=True), _decl("b", nd=True)]
        assert self._run(monkeypatch, data, 2).passed is True

    def test_above_the_ceiling_fails(self, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — one new declaration in the trust surface."""
        data = [_decl("a", nd=True), _decl("b", nd=True), _decl("c", nd=True)]
        r = self._run(monkeypatch, data, 2)
        assert r.passed is False, "the native_decide ratchet no longer catches growth"
        assert any(d.name == "ceiling" and not d.passed for d in r.details)

    def test_below_the_ceiling_passes_with_a_lower_it_hint(self, monkeypatch):
        r = self._run(monkeypatch, [_decl("a", nd=True)], 5)
        assert r.passed is True
        assert any("lowering the ceiling" in (d.message or "") for d in r.details)

    def test_measures_live_substrate_not_the_recording(self, monkeypatch):
        """THE POINT OF THE FIX. counts.json says the surface is at the ceiling;
        the substrate says it grew. The ratchet must follow the substrate."""
        data = [_decl(f"d{i}", nd=True) for i in range(5)]
        r = self._run(monkeypatch, data, 3, recorded=3)
        assert r.passed is False, (
            "the ratchet trusted a stale counts.json over the live substrate — the "
            "exact defect ADR-009 §Deferred item 1 describes")

    def test_a_stale_recording_is_surfaced_not_swallowed(self, monkeypatch):
        data = [_decl(f"d{i}", nd=True) for i in range(2)]
        r = self._run(monkeypatch, data, 5, recorded=99)
        assert r.passed is True
        assert any(d.name == "counts_drift" for d in r.details), (
            "a counts.json disagreeing with the substrate must be reported")

    def test_missing_lean_deps_fails_rather_than_passing(self, monkeypatch):
        """'I could not find the substrate' is not evidence the surface did not
        grow — and this check hard-blocks main."""
        monkeypatch.setattr(_H, "lean_deps_present", lambda: False)
        assert lt.check_native_decide_regression().passed is False
