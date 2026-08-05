"""The change-scoping caches — `validation/_memo.py` and the `paper_latex_compiles`
per-draft cache (2026-08-05).

WHAT THESE CACHES ARE FOR
-------------------------
Measured on this branch: the 55-check suite costs **332.6 s**, and **43 checks
finish in under one second**. The cost is three:

    axiom_closure_allowlist     145.4 s
    lean_docstring_refs_resolve  52.8 s
    paper_latex_compiles         16.6 s

Measured over all 5,814 commits on `main` since 2026-03-01, `lean/` moved in
**78 %** and `notebooks/` in **0.84 %**. So on a Lean wave the memo correctly
re-measures and saves nothing; what it saves is the REPEAT — a `/goal` loop runs
`validate.py`, fixes a doc/paper/count issue, runs it again — plus paper- and
doc-side waves. (⚠️ Do not re-derive this from an infra branch; an earlier draft
read "47 %" off 400 commits of this one, which is not how the repo normally works.)
Meanwhile `paper_latex_compiles` responded to its own cost by *skipping by
default*, which is how a plain `validate.py` reported it green while D3 carried two
fatal compile errors.

WHY THIS FILE IS MOSTLY ABOUT THE KEY
-------------------------------------
A memoized check reports PASS **without measuring anything**. That is exactly
"absence of measurement rendered as success" — the defect class this audit exists
to close — and it is sound *only* if the key covers every input. A key missing an
input is worse than no cache at all: it manufactures a green tick that survives
the very change it should have caught.

So the load-bearing tests here are the **production-seeded** ones: each declared
input is really changed, in the real tree, and the key must move. Per QI-30, a
mutation caught against a patched fixture establishes nothing about production —
that is the whole reason these mutate `lean/SKEFTHawking/*.lean` and
`src/core/constants.py` themselves and restore them in `finally`.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT / "scripts"))
sys.path.insert(0, str(SK_ROOT))

import validate  # noqa: E402
from validation import _config as _cfg  # noqa: E402
from validation import _memo  # noqa: E402
from validation._registry import CheckResult, Detail  # noqa: E402


@pytest.fixture
def live_memo(monkeypatch, tmp_path):
    """Re-enable the memo (conftest disables it suite-wide) against a throwaway
    cache file, so these tests exercise the real code paths without touching the
    developer's cache."""
    monkeypatch.delenv("SKEFT_VALIDATION_NO_MEMO", raising=False)
    monkeypatch.setattr(_cfg, "NO_MEMO", False)
    monkeypatch.setattr(_cfg, "STRICT_MODE", False)
    monkeypatch.setattr(_memo, "_cache_path", lambda: tmp_path / "memo.json")
    return tmp_path / "memo.json"


def _ok():
    return CheckResult(passed=True, details=[Detail("x", True, "measured")])


def _bad():
    return CheckResult(passed=False, details=[Detail("x", False, "broken")])


# ══════════════════════════════════════════════════════════════════════════
# The key — production-seeded
# ══════════════════════════════════════════════════════════════════════════

def _seeded(path: Path, addition: bytes, key_fn):
    """Compute `key_fn()`, really change `path` in the production tree, recompute,
    restore. Returns (before, after)."""
    original = path.read_bytes()
    before = key_fn()
    try:
        path.write_bytes(original + addition)
        after = key_fn()
    finally:
        path.write_bytes(original)
    assert path.read_bytes() == original, f"failed to restore {path}"
    return before, after


class TestKeyCoversItsInputs:
    """FIRES ON A SEEDED DEFECT, in the production tree. Each of these mutates a
    real declared input; a key that did not move would mean the check can be
    skipped across that exact change."""

    def test_a_lean_source_edit_moves_the_key(self):
        victim = sorted((SK_ROOT / "lean" / "SKEFTHawking").glob("*.lean"))[0]
        before, after = _seeded(victim, b"\n-- memo key probe\n",
                                _memo.lean_source_fingerprint)
        assert before != after, (
            f"editing {victim.name} did not move the Lean fingerprint. Both "
            "axiom_closure_allowlist and lean_docstring_refs_resolve would return "
            "a cached PASS across a substrate change — the single worst outcome "
            "this cache can produce.")

    def test_a_toolchain_pin_edit_moves_the_key(self):
        before, after = _seeded(SK_ROOT / "lean" / "lakefile.toml",
                                b"\n# memo key probe\n",
                                _memo.toolchain_pin_fingerprint)
        assert before != after, (
            "a lakefile.toml edit did not move the pin fingerprint; a Mathlib bump "
            "would leave both Lean checks frozen at the old Mathlib's verdict.")

    def test_a_lake_manifest_change_moves_the_key(self):
        """The declared pins alone would miss a `lake update` that re-resolves a
        transitive dependency without anyone editing `lakefile.toml`."""
        before, after = _seeded(SK_ROOT / "lean" / "lake-manifest.json",
                                b"\n", _memo.toolchain_pin_fingerprint)
        assert before != after

    def test_an_axiom_metadata_edit_moves_the_key(self):
        """`AXIOM_METADATA` IS the allow-list `axiom_closure_allowlist` checks
        against — a cache surviving an edit to it caches the wrong question."""
        constants = SK_ROOT / "src" / "core" / "constants.py"
        before, after = _seeded(
            constants, b"\n# memo key probe\n",
            lambda: _memo.files_fingerprint([constants]))
        assert before != after

    def test_absent_hashes_differently_from_empty(self, tmp_path):
        """Creating a missing input must invalidate. If absence hashed as nothing,
        a key computed while a file was missing would still match once it existed."""
        target = tmp_path / "later.txt"
        absent = _memo.files_fingerprint([target])
        target.write_text("")
        empty = _memo.files_fingerprint([target])
        assert absent != empty

    def test_the_body_source_is_folded_in_automatically(self, live_memo):
        """Guard 1, and it must hold WITHOUT the caller opting in — `memoized`
        adds it, so a new memoized check cannot forget it.

        Same `key` string, two different bodies: the second must still run."""
        _memo.memoized("c", "same-key", _ok, "inputs")
        ran = []

        def other_body():
            ran.append(1)
            return _ok()

        _memo.memoized("c", "same-key", other_body, "inputs")
        assert ran, (
            "a changed check body reused the cached verdict of the previous one. "
            "Editing a check would then not invalidate its own cache.")


# ══════════════════════════════════════════════════════════════════════════
# Cache semantics
# ══════════════════════════════════════════════════════════════════════════

class TestMemoSemantics:

    def test_a_hit_skips_the_body_and_says_so(self, live_memo):
        calls = []

        def body():
            calls.append(1)
            return _ok()

        _memo.memoized("c", "k", body, "the inputs")
        r = _memo.memoized("c", "k", body, "the inputs")
        assert len(calls) == 1, "the cached run re-executed the body"
        assert any("SKIPPED (cached)" in (d.message or "") for d in r.details), (
            "the memo hit is INVISIBLE. An unannounced skip is how a suite "
            "silently shrinks — the reader cannot tell a measured PASS from a "
            "remembered one.")
        assert any("the inputs" in (d.message or "") for d in r.details), (
            "the skip message does not name what the cached verdict is "
            "conditional on")

    def test_a_cached_hit_replays_the_original_warnings(self, live_memo):
        """FIRES ON THE SEEDED DEFECT — and this one was found by reading a real
        report, not by writing a test.

        `axiom_closure_allowlist` PASSES non-strict while emitting ⚠ "N
        declaration(s) carry a non-allow-listed axiom". A memo that cached only the
        verdict deleted that warning from every run after the first: the suite goes
        on saying PASS and stops saying *why it is a qualified pass*. That is the
        cache silently narrowing what gets reported."""
        def body():
            return CheckResult(passed=True, details=[
                Detail("native_decide", True, "3 declaration(s) use native_decide",
                       warning=True),
                Detail("allowlist_size", True, "17 allow-listed axioms")])

        _memo.memoized("c", "k", body, "i")
        r = _memo.memoized("c", "k", body, "i")
        warned = [d for d in r.details if d.warning]
        assert warned, (
            "the cached run dropped the check's ⚠ warnings. A qualified PASS "
            "became a bare PASS — the trust-surface signal disappears on every "
            "run after the first.")
        assert warned[0].message == "3 declaration(s) use native_decide"
        assert any(d.name == "allowlist_size" for d in r.details)

    def test_a_failure_is_never_cached(self, live_memo):
        calls = []

        def body():
            calls.append(1)
            return _bad()

        _memo.memoized("c", "k", body, "i")
        _memo.memoized("c", "k", body, "i")
        assert len(calls) == 2, (
            "a FAILING check was memoized. It would then report the same failure "
            "forever without re-running, and a fix would not clear it.")

    def test_a_failure_evicts_an_earlier_pass(self, live_memo):
        """The dangerous ordering: PASS cached, then the check starts failing under
        the SAME key (an input the key does not cover, or a flag change). The stale
        green must not survive the failure."""
        _memo.memoized("c", "k", _ok, "i")
        assert json.loads(live_memo.read_text())["entries"].get("c") is not None
        _memo.memoized("c", "k", _bad, "i")
        assert "c" not in json.loads(live_memo.read_text())["entries"]

    def test_a_legacy_entry_shape_is_ignored_rather_than_trusted(self, live_memo):
        """The stored entry became a dict (key + replayed details) after starting as
        a bare key string. An old-shape entry must MISS, not crash and not match —
        the schema bump covers a deliberate migration, this covers a stray file."""
        live_memo.write_text(json.dumps(
            {"schema": _memo.MEMO_SCHEMA, "entries": {"c": "some-old-bare-key"}}))
        calls = []
        _memo.memoized("c", "k", lambda: calls.append(1) or _ok(), "i")
        assert calls

    def test_strict_mode_bypasses(self, live_memo, monkeypatch):
        """⚠️ The deliberate asymmetry. `--strict` is the Paper Submission Gate
        (Invariant #12) — the one irreversible consumer, and the one place where
        re-measuring from scratch beats any cache."""
        _memo.memoized("c", "k", _ok, "i")
        monkeypatch.setattr(_cfg, "STRICT_MODE", True)
        calls = []
        _memo.memoized("c", "k", lambda: calls.append(1) or _ok(), "i")
        assert calls, "--strict read a cached verdict at the submission gate"

    def test_no_memo_bypasses(self, live_memo, monkeypatch):
        _memo.memoized("c", "k", _ok, "i")
        monkeypatch.setattr(_cfg, "NO_MEMO", True)
        calls = []
        _memo.memoized("c", "k", lambda: calls.append(1) or _ok(), "i")
        assert calls

    def test_a_corrupt_cache_computes_rather_than_skips(self, live_memo):
        """FAIL-SAFE DIRECTION. Every error path must fall through to the real
        check, so a broken cache makes a run slower and never greener."""
        live_memo.write_text("{ not json at all")
        calls = []
        _memo.memoized("c", "k", lambda: calls.append(1) or _ok(), "i")
        assert calls

    def test_a_schema_bump_invalidates_everything(self, live_memo, monkeypatch):
        _memo.memoized("c", "k", _ok, "i")
        monkeypatch.setattr(_memo, "MEMO_SCHEMA", _memo.MEMO_SCHEMA + 1)
        calls = []
        _memo.memoized("c", "k", lambda: calls.append(1) or _ok(), "i")
        assert calls


# ══════════════════════════════════════════════════════════════════════════
# Which checks are memoized — a ratchet, not an open door
# ══════════════════════════════════════════════════════════════════════════

class TestMemoizedSetIsFrozen:

    #: Every check wrapped in `_memo.memoize_check`. FROZEN: each entry is a
    #: decision that this check's key provably covers its inputs. Adding one
    #: without a matching production-seeded key test above is how a cache starts
    #: reporting green over a change it cannot see.
    EXPECTED = {"axiom_closure_allowlist", "lean_docstring_refs_resolve"}

    def _memoized_names(self) -> set[str]:
        return {s.name for s in validate._CHECKS
                if hasattr(s.func, "__memo_body__")}

    def test_exactly_the_frozen_set_is_memoized(self):
        assert self._memoized_names() == self.EXPECTED, (
            f"the memoized set is {sorted(self._memoized_names())}, expected "
            f"{sorted(self.EXPECTED)}. Adding a check here means it can report "
            "PASS without running — justify the key in "
            "TestKeyCoversItsInputs, in the same commit.")

    def test_unwrap_reaches_the_real_body(self):
        """Several guards resolve a check by name and then INSPECT it
        (`test_validate_flag_propagation` reads `co_names` for `_cfg`). Against a
        bare wrapper they would inspect the wrong function and pass vacuously."""
        for spec in validate._CHECKS:
            if spec.name in self.EXPECTED:
                body = _memo.unwrap(spec.func)
                assert body is not spec.func
                assert "_H" in body.__code__.co_names or "_cfg" in body.__code__.co_names

    def test_unwrap_is_a_no_op_for_a_plain_check(self):
        plain = next(s.func for s in validate._CHECKS if s.name == "identities")
        assert _memo.unwrap(plain) is plain


# ══════════════════════════════════════════════════════════════════════════
# `paper_latex_compiles` — the per-draft cache
# ══════════════════════════════════════════════════════════════════════════

from validation.checks import papers_prose as pp  # noqa: E402
from bundle_registry import BUNDLE_CODES  # noqa: E402


@pytest.fixture
def latex_env(monkeypatch, tmp_path):
    """Point the cache at a temp file and stub pdflatex. The stub writes no log,
    which the check reads as a clean compile — so a `subprocess.run` call means
    'this draft was compiled', and its absence means 'cached'."""
    # The latex cache now honours the same bypass set as _memo (R4-I1), and
    # conftest sets SKEFT_VALIDATION_NO_MEMO=1 suite-wide — so without this the
    # cache is permanently bypassed and every "is it cached?" assertion is vacuous.
    monkeypatch.delenv("SKEFT_VALIDATION_NO_MEMO", raising=False)
    monkeypatch.setattr(_cfg, "NO_MEMO", False)
    monkeypatch.setattr(_cfg, "STRICT_MODE", False)
    monkeypatch.setattr(pp.shutil, "which", lambda _: "/usr/bin/pdflatex")
    monkeypatch.setattr(pp, "LATEX_COMPILE_CACHE", str(tmp_path.name) + "/c.json")
    monkeypatch.setattr(pp._H, "PROJECT_ROOT", tmp_path.parent, raising=False)
    calls: list = []
    monkeypatch.setattr(pp.subprocess, "run",
                        lambda *a, **k: calls.append(a) or None)
    return calls, tmp_path.parent / (str(tmp_path.name) + "/c.json")


class TestLatexCompileCache:

    def test_the_input_closure_follows_input_directives(self):
        """PRODUCTION FIXTURE, not an invented one: every bundle draft
        `\\input{../../docs/counts.tex}`, so the shared counts macros must be in
        the closure. If they were not, regenerating counts.tex could break every
        draft and no draft would recompile."""
        tex = SK_ROOT / "papers" / "D1" / "paper_draft.tex"
        if not tex.is_file():
            pytest.skip("D1 draft absent")
        closure = pp._draft_input_closure(tex)
        assert tex in closure
        assert any(p.name == "counts.tex" for p in closure), (
            f"the input closure of D1 is {[p.name for p in closure]} — it does "
            "not include counts.tex, which the draft \\input{}s. A counts "
            "regeneration would then not invalidate any draft.")

    def test_editing_a_draft_moves_its_closure_hash(self):
        tex = SK_ROOT / "papers" / "D1" / "paper_draft.tex"
        if not tex.is_file():
            pytest.skip("D1 draft absent")
        before, after = _seeded(
            tex, b"\n% memo probe\n",
            lambda: _memo.files_fingerprint(pp._draft_input_closure(tex)))
        assert before != after

    def test_an_unchanged_draft_is_not_recompiled(self, latex_env, monkeypatch):
        """The point of the cache: 16.6 s for 21 drafts becomes ~0 s when nothing
        moved, which is what let the slow-gate (and its false PASS) be removed."""
        calls, cache = latex_env
        monkeypatch.setattr(_cfg, "FORCE_LATEX", False)
        pp.check_paper_latex_compiles()          # cold — compiles everything
        assert len(calls) > 0, "the cold run compiled nothing; the stub is not wired"
        cold = len(calls)
        pp.check_paper_latex_compiles()          # warm — should compile nothing
        assert len(calls) == cold, (
            f"the warm run compiled {len(calls) - cold} draft(s) again despite no "
            "input changing")

    def test_force_latex_recompiles_everything(self, latex_env, monkeypatch):
        calls, _ = latex_env
        monkeypatch.setattr(_cfg, "FORCE_LATEX", False)
        pp.check_paper_latex_compiles()
        cold = len(calls)
        monkeypatch.setattr(_cfg, "FORCE_LATEX", True)
        pp.check_paper_latex_compiles()
        assert len(calls) - cold == cold, (
            "--force-latex did not bypass the cache; there would be no way to "
            "force a recompile after a toolchain change")

    def test_a_failing_draft_recompiles_every_run(self, latex_env, monkeypatch):
        """FIRES ON THE SEEDED DEFECT. A draft with fatal errors must never
        acquire a cache key — otherwise D3's two fatal errors would be recorded
        once and then skipped forever."""
        calls, cache = latex_env
        monkeypatch.setattr(_cfg, "FORCE_LATEX", False)

        def fatal_run(*a, **k):
            calls.append(a)
            out = next(x.split("=", 1)[1] for x in a[0] if x.startswith("-output-directory="))
            (Path(out) / "paper_draft.log").write_text("! Undefined control sequence.\n")

        monkeypatch.setattr(pp.subprocess, "run", fatal_run)
        r1 = pp.check_paper_latex_compiles()
        first = len(calls)
        assert r1.passed is False
        r2 = pp.check_paper_latex_compiles()
        assert len(calls) == 2 * first, (
            "a draft with fatal compile errors was cached as clean")
        assert r2.passed is False

    def test_the_cache_records_only_real_bundle_codes(self, latex_env, monkeypatch):
        calls, cache = latex_env
        monkeypatch.setattr(_cfg, "FORCE_LATEX", False)
        pp.check_paper_latex_compiles()
        recorded = set(json.loads(cache.read_text())["clean"])
        assert recorded <= set(BUNDLE_CODES)
        assert recorded, "nothing was recorded, so the warm-run test is vacuous"


# ══════════════════════════════════════════════════════════════════════════
# The tests PR-review pass 2 proved were missing
# ══════════════════════════════════════════════════════════════════════════

class TestCheckKeysSpanTheirInputs:
    """⚠️ THIS CLASS EXISTS BECAUSE `TestKeyCoversItsInputs` ABOVE DOES NOT DO
    WHAT IT SAYS.

    Reviewer R2 (PR-review pass 2) deleted `lean_source_fingerprint()` from
    `axiom_closure_allowlist`'s `key_fn` **in production** — producing precisely
    the outcome this file's own docstring calls *"the single worst outcome this
    cache can produce"* — and the suite returned **24 passed**. The class above
    seeds the fingerprint HELPERS and asserts they move. Nothing asserted that any
    check's key actually CALLS them.

    That is QI-30's criterion violated inside the tests written to satisfy it: a
    mutation caught one level away from the artifact proves nothing about the
    artifact. These tests seed through `__memo_key_fn__` — the real key of the
    real registered check.
    """

    def _key_fn(self, name):
        """The COMPLETE key. ⚠️ `__memo_key_fn__` alone is NOT it — `memoized`
        folds in the module and body digests — so seeding through it would miss
        precisely the inputs guard 1 covers. My first draft of this class did
        exactly that and the module-constant probe read UNCHANGED."""
        fn = next(s.func for s in validate._CHECKS if s.name == name)
        kf = getattr(fn, "__memo_full_key__", None)
        assert kf is not None, f"{name} is memoized but exposes no __memo_full_key__"
        return kf

    @pytest.mark.parametrize("check", ["axiom_closure_allowlist",
                                       "lean_docstring_refs_resolve"])
    def test_a_real_lean_edit_moves_THIS_CHECKS_key(self, check):
        """FIRES ON A PRODUCTION SEED. Both memoized checks answer questions about
        the Lean substrate; if a `.lean` edit does not move their key, each returns
        a cached verdict across a substrate change."""
        victim = sorted((SK_ROOT / "lean" / "SKEFTHawking").glob("*.lean"))[0]
        before, after = _seeded(victim, b"\n-- key-span probe\n", self._key_fn(check))
        assert before != after, (
            f"editing {victim.name} did not move {check}'s OWN key. The check can "
            f"return a cached PASS across a Lean substrate change.")

    @pytest.mark.parametrize("check", ["axiom_closure_allowlist",
                                       "lean_docstring_refs_resolve"])
    def test_the_ROOT_AGGREGATE_moves_THIS_CHECKS_key(self, check):
        """`lean/SKEFTHawking.lean` is a SIBLING of `lean/SKEFTHawking/`, so the
        directory glob missed it (reviewer R6). It is the file whose `import` lines
        decide which modules are in the environment `AxiomAudit` walks — 5,226
        lines that were outside the key."""
        root = SK_ROOT / "lean" / "SKEFTHawking.lean"
        if not root.is_file():
            pytest.skip("root aggregate absent")
        before, after = _seeded(root, b"\n-- key-span probe\n", self._key_fn(check))
        assert before != after, (
            f"editing the root aggregate did not move {check}'s key; adding or "
            f"removing an `import` changes the verified surface invisibly.")

    def test_AXIOM_METADATA_moves_the_axiom_checks_key(self):
        """`AXIOM_METADATA` *is* the allow-list the check compares against."""
        before, after = _seeded(SK_ROOT / "src" / "core" / "constants.py",
                                b"\n# key-span probe\n",
                                self._key_fn("axiom_closure_allowlist"))
        assert before != after

    def test_a_module_level_constant_moves_the_key(self):
        """Reviewer R1: `source_fingerprint` hashed only the `def`'s own text, so
        module-level constants — including `_DOCSTRING_STRICT_FAMILIES`, the
        FAIL-vs-advisory switch — sat outside the key. Seeded in place so line
        numbers do not shift (a line-count change moves the digest for an unrelated
        reason, which is how the lead's first reproduction wrongly cleared it)."""
        mod = SK_ROOT / "scripts" / "validation" / "checks" / "lean_toolchain.py"
        orig = mod.read_bytes()
        kf = self._key_fn("lean_docstring_refs_resolve")
        before = kf()
        try:
            txt = orig.decode()
            mutated = txt.replace('_DOCSTRING_STRICT_FAMILIES = (',
                                  '_DOCSTRING_STRICT_FAMILIES = ("ZZZ",', 1)
            assert mutated.count("\n") == txt.count("\n"), "probe changed line count"
            mod.write_text(mutated)
            after = kf()
        finally:
            mod.write_bytes(orig)
        assert mod.read_bytes() == orig
        assert before != after, (
            "a module-level constant edit left the key unchanged — flipping a "
            "check's fail-vs-warn switch would not invalidate its cached verdict")


class TestNonMeasurementIsNeverCached:
    """The hole five reviewers found: a fail-open SKIP *is* a PASS, so guard 3
    ('only PASS is cached') stored it and replayed it after the cause was fixed."""

    def _skip(self):
        return CheckResult(passed=True, measured=False,
                           details=[Detail("lake", True, "SKIPPED — lake not found")])

    def test_a_cannot_measure_pass_is_not_stored(self, live_memo):
        _memo.memoized("c", "k", self._skip, "i")
        stored = json.loads(live_memo.read_text())["entries"] if live_memo.exists() else {}
        assert not stored, (
            "a check that returned PASS WITHOUT MEASURING was cached. Restoring "
            "the toolchain would then replay the skip instead of measuring.")

    def test_it_runs_again_next_time(self, live_memo):
        calls = []
        body = lambda: calls.append(1) or self._skip()   # noqa: E731
        _memo.memoized("c", "k", body, "i")
        _memo.memoized("c", "k", body, "i")
        assert len(calls) == 2

    def test_a_cannot_measure_result_EVICTS_an_earlier_real_pass(self, live_memo):
        """The dangerous ordering: measured PASS cached, then the toolchain goes
        away under the SAME key. The stale green must not survive."""
        _memo.memoized("c", "k", _ok, "i")
        assert json.loads(live_memo.read_text())["entries"].get("c")
        _memo.memoized("c", "k", self._skip, "i")
        assert "c" not in json.loads(live_memo.read_text())["entries"]

    def test_the_real_check_declares_non_measurement(self):
        """PRODUCTION, not a fixture: with no toolchain, the live check must report
        `measured=False`. If it reports True the memo will cache it again."""
        import os as _os
        from validation.checks import lean_toolchain as lt
        env = dict(LEAN_PROJECT_DIR="/nonexistent", LAKE_PATH="/nonexistent")
        old = {k: _os.environ.get(k) for k in env}
        try:
            _os.environ.update(env)
            r = _memo.unwrap(lt.check_axiom_closure_allowlist)()
        finally:
            for k, v in old.items():
                _os.environ.pop(k, None) if v is None else _os.environ.__setitem__(k, v)
        assert r.passed is True, "unexpected: absence should stay fail-open"
        assert r.measured is False, (
            "the live check returned PASS and claimed it MEASURED, with no Lean "
            "toolchain present — the memo will cache a non-measurement again")
