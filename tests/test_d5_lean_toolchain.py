"""D5 both-directions tests for `validation/checks/lean_toolchain.py` — audit QI-27.

Six checks: `theorems`, `lean_source`, `lean_build`, `axiom_closure_allowlist`,
`elaboration_knob_watchlist`, `lean_docstring_refs_resolve`.
(`native_decide_regression` was already mutation-verified by
`tests/test_native_decide_ratchet.py` under ADR-009 §Deferred item 1.)

Also closes the **QI-11 residue**: the lake-resolution block that sat verbatim in both
`check_lean_build` and `check_axiom_closure_allowlist`. The audit deferred it here on
purpose — extracting it changes two checks' early-return path, and ADR-009 D4 forbids
mixing that into a mechanical pass. `TestLakeResolution` is the proof the paths are
unchanged.

MUTATION-VERIFIED 2026-08-04 — 11 mutations, all CAUGHT, clean negative control.
"""
from __future__ import annotations

import ast
import json
import sys
from pathlib import Path

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT / "scripts"))
sys.path.insert(0, str(SK_ROOT))

import validate_helpers as _H  # noqa: E402
from src.core import constants as _c  # noqa: E402
from validation import _config as _cfg  # noqa: E402
from validation.checks import lean_toolchain as lt  # noqa: E402


class _Proc:
    """Stand-in for `subprocess.run`."""

    def __init__(self, returncode=0, stdout="", stderr="", raises=None):
        self.rc, self.out, self.err, self.raises = returncode, stdout, stderr, raises
        self.calls = []

    def __call__(self, cmd, **kw):
        self.calls.append(cmd)
        if self.raises:
            raise self.raises
        outer = self

        class _R:
            returncode, stdout, stderr = outer.rc, outer.out, outer.err
        return _R()


def _lean_tree(tmp_path: Path, files: dict[str, str]) -> Path:
    root = tmp_path / "lean" / "SKEFTHawking"
    root.mkdir(parents=True, exist_ok=True)
    for rel, body in files.items():
        p = root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(body)
    return root


class TestTheoremCount:
    """The Aristotle registry resolves against the Lean substrate.

    ⚠️ **This class replaces one that pinned three hardcoded copies of `322`.** That
    was treating a symptom: audit QI-30 established that all three legs of the old
    check were VACUOUS — two unreachable (constants.py asserts the count at import,
    so a wrong value raises before the check body runs) and one a tautology
    (`TOTAL_THEOREMS` IS `len(ARISTOTLE_THEOREMS)` by definition). Asserting that
    three copies of an unreachable literal agree with each other is a test of nothing.

    ⚠️ **And my earlier mutations on it were misleading.** They were CAUGHT — but only
    because the tests monkeypatched `TOTAL_THEOREMS`/`ARISTOTLE_THEOREMS`, which
    bypasses the import-time assert. They proved the arithmetic responded to inputs
    the check could never actually receive. *A mutation caught against a patched
    fixture does not establish that the check can fail in production.*
    """

    def _run(self, tmp_path, monkeypatch, *, registry, decls, ceiling=14):
        p = tmp_path / "lean_deps.json"
        p.write_text(json.dumps([{"name": n, "type": "P", "kind": "theorem"}
                                 for n in decls]))
        monkeypatch.setattr(_H, "LEAN_DEPS_PATH", p)
        monkeypatch.setattr(_c, "ARISTOTLE_THEOREMS", {k: "run" for k in registry})
        monkeypatch.setattr(_c, "ARISTOTLE_REGISTRY_UNRESOLVED_CEILING", ceiling)
        return lt.check_theorem_count()

    def test_a_fully_resolving_registry_passes(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA."""
        r = self._run(tmp_path, monkeypatch, registry=["thm_a", "thm_b"],
                      decls=["SKEFTHawking.M.thm_a", "SKEFTHawking.M.thm_b"], ceiling=0)
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]
        assert any("every Aristotle registry entry resolves" in (d.message or "")
                   for d in r.details)

    def test_a_stale_entry_past_the_ceiling_fails(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — and this is the defect that matters:
        `check_formulas_to_theorems` unions these KEYS into its valid-Lean-name set,
        so a stale key launders a nonexistent theorem into it and a formula grounded
        on that theorem is reported as verified."""
        r = self._run(tmp_path, monkeypatch, registry=["thm_a", "ghost_thm"],
                      decls=["SKEFTHawking.M.thm_a"], ceiling=0)
        assert r.passed is False, (
            "a registry entry naming no Lean declaration passed — it is laundered "
            "into `formulas`' valid-name set")
        assert any(d.name == "unresolved" and "ghost_thm" in (d.message or "")
                   for d in r.details)

    def test_frozen_debt_at_the_ceiling_passes_but_stays_visible(self, tmp_path, monkeypatch):
        """The ratchet, not a walk-back. Existing debt is reported as a warning so it
        cannot quietly become permanent; only GROWTH fails."""
        r = self._run(tmp_path, monkeypatch, registry=["ghost_thm"], decls=[], ceiling=1)
        assert r.passed is True
        d = next(d for d in r.details if d.name == "unresolved")
        assert d.warning and "frozen debt" in (d.message or "")

    def test_repairing_an_entry_asks_for_the_ceiling_to_be_LOWERED(self, tmp_path, monkeypatch):
        """A ceiling above the population is headroom in which a new stale entry hides
        — the exact defect found in `ledger_ids_resolve` (67 against 66). The check
        must ASK to be tightened rather than silently accept the slack."""
        # ONE stale entry against a ceiling of 3 — i.e. two were repaired since the
        # freeze. The nudge only makes sense while debt remains; a fully-clean registry
        # takes the "every entry resolves" branch instead.
        r = self._run(tmp_path, monkeypatch, registry=["thm_a", "ghost_thm"],
                      decls=["SKEFTHawking.M.thm_a"], ceiling=3)
        assert r.passed is True
        assert any(d.name == "ratchet" and "lower" in (d.message or "").lower()
                   for d in r.details)

    def test_a_fully_qualified_registry_key_also_resolves(self, tmp_path, monkeypatch):
        """Keys are short names today, but a fully-qualified one must not read as
        stale — that would flag a correct entry."""
        r = self._run(tmp_path, monkeypatch, registry=["SKEFTHawking.M.thm_a"],
                      decls=["SKEFTHawking.M.thm_a"], ceiling=0)
        assert r.passed is True

    def test_a_missing_lean_deps_FAILS(self, tmp_path, monkeypatch):
        """Cannot-measure is not success. Matches `native_decide_regression`, the
        suite's other ratchet: not finding the substrate is not evidence the registry
        is clean."""
        monkeypatch.setattr(_H, "LEAN_DEPS_PATH", tmp_path / "absent.json")
        r = lt.check_theorem_count()
        assert r.passed is False
        assert any("UNVERIFIED" in (d.message or "") for d in r.details)

    def test_the_count_invariant_is_owned_by_constants_not_duplicated_here(self):
        """QI-30's structural half. The count assertion lives in `constants.py` as an
        import-time `assert`, which is STRICTER than a check (it makes the module
        unimportable). Restating it in the check body was duplication with no owner
        and, because the import fires first, was unreachable.

        This asserts the duplication has not crept back. It targets COMPARISONS
        against an integer literal, not every integer in the body — display slices
        like `unresolved[:8]` are formatting, not assertions, and a scan that flagged
        them would be a guard firing on correct code.
        """
        import ast as _ast
        src = Path(lt.__file__).read_text()
        fn = next(n for n in _ast.walk(_ast.parse(src))
                  if isinstance(n, _ast.FunctionDef) and n.name == "check_theorem_count")
        compared = [c.value for node in _ast.walk(fn) if isinstance(node, _ast.Compare)
                    for c in node.comparators
                    if isinstance(c, _ast.Constant) and isinstance(c.value, int)
                    and not isinstance(c.value, bool) and c.value > 1]
        assert not compared, (
            f"check_theorem_count compares against hardcoded integer literal(s) "
            f"{compared}. The count invariant is owned by src/core/constants.py's "
            f"import-time assert; a copy here is UNREACHABLE (the import raises first) "
            f"and is what made all three of this check's original legs vacuous — QI-30. "
            f"A threshold belongs in a named constant, not in the comparison.")


class TestLeanSource:
    """Spot-check theorem names still resolve in the Lean source."""

    #: ⚠️ A LITERAL CONTRACT, deliberately NOT lifted from the production body.
    #: This used to AST-parse `spot_checks` out of `check_lean_source` and build the
    #: fixture from whatever it found, so the test could never disagree with
    #: production: replacing all five names with fictional ones left it GREEN. A
    #: test whose expectation is read from the code under test asserts only that
    #: the code equals itself.
    #:
    #: Transcribed 2026-08-10. If production changes, this list must be updated
    #: DELIBERATELY — that edit is the review surface, and
    #: `test_the_literal_contract_matches_production` below is what forces it.
    _SPOT_NAMES = sorted({
        "dampingRate_eq_zero_iff",
        "dispersive_correction_bound",
        "firstOrder_correction_zero_iff",
        "acousticMetric_det",
        "secondOrder_count",
        "fracton_exceeds_standard_general",
        "binomial_strict_mono",
        "dof_gap_positive_2_through_8",
        "evading_one_breaks_nogo",
        "ep_distinguishes_phases",
        "obstructions_individually_sufficient",
    })

    @staticmethod
    def _spot_names() -> list[str]:
        return list(TestLeanSource._SPOT_NAMES)

    def test_the_literal_contract_matches_production(self):
        """The pin above must equal what `check_lean_source` actually spot-checks.

        This is the ONE place the production body may be read — to detect drift,
        never to define the expectation. If this fails, production changed its
        spot-check set and the literal above needs a deliberate, reviewed update.
        """
        src = Path(lt.__file__).read_text()
        fn = next(n for n in ast.walk(ast.parse(src))
                  if isinstance(n, ast.FunctionDef) and n.name == "check_lean_source")
        live = None
        for node in ast.walk(fn):
            if isinstance(node, ast.Assign) and \
                    any(getattr(t, "id", None) == "spot_checks" for t in node.targets):
                live = sorted(set(ast.literal_eval(node.value).values()))
        assert live is not None, "check_lean_source no longer assigns a literal spot_checks"
        assert live == self._SPOT_NAMES, (
            f"spot-check drift.\n  production: {live}\n  pinned:     {self._SPOT_NAMES}\n"
            f"Update the literal deliberately; do NOT re-derive it from the source.")

    def test_all_names_present_passes(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA."""
        body = "\n".join(f"theorem {n} : True := trivial" for n in self._spot_names())
        monkeypatch.setattr(_H, "LEAN_DIR", _lean_tree(tmp_path, {"All.lean": body}))
        r = lt.check_lean_source()
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_a_missing_name_fails(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — a rename that left the registry behind."""
        names = self._spot_names()[1:]
        body = "\n".join(f"theorem {n} : True := trivial" for n in names)
        monkeypatch.setattr(_H, "LEAN_DIR", _lean_tree(tmp_path, {"All.lean": body}))
        r = lt.check_lean_source()
        assert r.passed is False
        assert any("NOT found" in (d.message or "") for d in r.details)

    def test_a_name_in_a_subdirectory_is_found(self, tmp_path, monkeypatch):
        """QI-01 at this call site. Under the non-recursive form this check saw 1,373
        of ~2,040 files and 7,695 declared identifiers were invisible — a spot-check
        name that moved into a package would report NOT found while existing."""
        body = "\n".join(f"theorem {n} : True := trivial" for n in self._spot_names())
        monkeypatch.setattr(_H, "LEAN_DIR",
                            _lean_tree(tmp_path, {"Pkg/Deep/All.lean": body}))
        assert lt.check_lean_source().passed is True, (
            "spot-check names in a SUBDIRECTORY were not found — the identifier scan "
            "is non-recursive again (audit QI-01)")

    def test_a_missing_lean_dir_fails_rather_than_passes(self, tmp_path, monkeypatch):
        monkeypatch.setattr(_H, "LEAN_DIR", tmp_path / "nonexistent")
        assert lt.check_lean_source().passed is False


class TestLakeResolution:
    """QI-11 residue, closed. The extraction must not change either caller's
    early-return path — that is the whole reason it was deferred to W-D."""

    def test_lake_path_env_wins(self, monkeypatch):
        monkeypatch.setenv("LAKE_PATH", "/custom/lake")
        assert lt._resolve_lake() == "/custom/lake"

    def test_absent_lake_resolves_to_none(self, monkeypatch):
        monkeypatch.delenv("LAKE_PATH", raising=False)
        monkeypatch.setattr(lt.Path, "home", staticmethod(lambda: Path("/nonexistent")))
        monkeypatch.setattr("shutil.which", lambda _: None)
        assert lt._resolve_lake() is None

    def test_lean_project_dir_env_wins(self, monkeypatch):
        monkeypatch.setenv("LEAN_PROJECT_DIR", "/custom/lean")
        assert lt._resolve_lean_root() == Path("/custom/lean")

    def test_lean_root_defaults_under_the_project_anchor(self, monkeypatch):
        """The default resolves to a REAL Lean project, anchored on PROJECT_ROOT.

        ⚠️ This asserted `lt._resolve_lean_root() == _H.PROJECT_ROOT / "lean"`, which
        IS the production expression verbatim — the test restated the implementation
        and so could not fail. Rewriting `_resolve_lean_root` as a `Path(__file__)`
        parent-walk, the exact ADR-009 H1 violation this module's header pins, left
        it GREEN.

        Assert observable properties instead: the resolved directory must actually
        BE a Lean project on disk (it carries a `lakefile.toml` and the
        `SKEFTHawking` source tree), and it must be anchored on `_H.PROJECT_ROOT`
        rather than on the resolver's own file location — which is what makes a
        parent-walk implementation detectable.
        """
        monkeypatch.delenv("LEAN_PROJECT_DIR", raising=False)
        root = lt._resolve_lean_root()

        assert (root / "lakefile.toml").is_file(), (
            f"{root} is not a Lean project — no lakefile.toml. A resolver that "
            f"returns a path-shaped value pointing at nothing is not resolving.")
        assert (root / "SKEFTHawking").is_dir(), (
            f"{root} carries no SKEFTHawking source tree")
        assert root.parent == _H.PROJECT_ROOT, (
            f"lean root must hang off the PROJECT_ROOT anchor, got parent "
            f"{root.parent} (ADR-009 H1: no Path(__file__) parent-walks)")
        assert root.is_absolute(), "callers cd elsewhere; a relative root is a bug"

    def test_lean_root_is_DERIVED_from_the_anchor_not_from__file__(self):
        """ADR-009 H1: the resolver must not parent-walk from its own location.

        ⚠️ THIS CANNOT BE TESTED BEHAVIOURALLY, and the previous attempt to do so
        was mis-proven. `validate_helpers.py:73` sets
        `PROJECT_ROOT = SCRIPT_DIR.parent`, so a FAITHFUL parent-walk from
        `scripts/validation/checks/` —
        `Path(__file__).resolve().parent.parent.parent.parent / "lean"` — returns
        the byte-identical path. Every assertion about the RESULT (including
        `root.parent == _H.PROJECT_ROOT`) is satisfied by it. The mutation I
        originally used to "prove" the sibling test walked the WRONG NUMBER of
        levels, which is a typo, not the architectural violation, so the proof was
        invalid. A fresh-context reviewer caught it by seeding the correct walk and
        watching the test stay green.

        The property is about DERIVATION, not value, so the source is the only
        place it is visible. Behaviour is still covered by the sibling test above,
        which catches wrong-depth walks; this one catches faithful ones.
        """
        src = Path(lt.__file__).read_text()
        fn = next(n for n in ast.walk(ast.parse(src))
                  if isinstance(n, ast.FunctionDef) and n.name == "_resolve_lean_root")
        body = ast.unparse(fn)

        assert "__file__" not in body, (
            "`_resolve_lean_root` derives its path from `__file__`. ADR-009 H1 "
            "requires the shared `validate_helpers.PROJECT_ROOT` anchor: a "
            "parent-walk silently returns the WRONG root the moment this file "
            "moves between directories, and — because PROJECT_ROOT is itself one "
            "level up from scripts/ — it returns the RIGHT path today, so no "
            "behavioural test can catch it.\n\n" + body)
        assert "PROJECT_ROOT" in body, (
            "`_resolve_lean_root` no longer references the PROJECT_ROOT anchor:\n"
            + body)

    def test_the_two_callers_keep_DIFFERENT_skip_messages(self, monkeypatch):
        """⚠️ THE POINT OF THE EXTRACTION, and its limit. Only the RESOLUTION is
        shared; each check keeps its own SKIP text and its own early return, because
        what lake's absence MEANS belongs to the check (ADR-009 H4's policy line).

        A helper that also returned the `CheckResult` would have unified two checks'
        behaviour in one commit — the 'semantic change wearing a mechanical disguise'
        H4 exists to prevent. This asserts the messages stayed distinct.
        """
        monkeypatch.delenv("LAKE_PATH", raising=False)
        monkeypatch.setattr(lt, "_resolve_lake", lambda: None)
        build = lt.check_lean_build()
        axiom = lt.check_axiom_closure_allowlist()
        assert build.passed is True and axiom.passed is True
        bm = build.details[0].message
        am = axiom.details[0].message
        assert bm != am, "the two SKIP messages were unified — H4 violation"
        assert "github.com/leanprover/elan" in bm
        assert "github.com/leanprover/elan" not in am


class TestLeanBuild:
    def _run(self, tmp_path, monkeypatch, proc, *, lakefile=True):
        monkeypatch.setattr(lt, "_resolve_lake", lambda: "/bin/lake")
        root = tmp_path / "lean"
        root.mkdir(parents=True, exist_ok=True)
        if lakefile:
            (root / "lakefile.toml").write_text("name = 'x'")
        monkeypatch.setattr(lt, "_resolve_lean_root", lambda: root)
        monkeypatch.setattr(lt.subprocess, "run", proc)
        return lt.check_lean_build()

    def test_a_successful_build_passes(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA."""
        r = self._run(tmp_path, monkeypatch,
                      _Proc(0, stdout="Build completed successfully (2254 jobs)."))
        assert r.passed is True
        assert any("2254 jobs" in (d.message or "") for d in r.details)

    def test_a_failing_build_fails(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT."""
        r = self._run(tmp_path, monkeypatch, _Proc(1, stderr="error: unknown identifier"))
        assert r.passed is False, "a non-zero `lake build` reported PASS"
        assert any("unknown identifier" in (d.message or "") for d in r.details)

    def test_a_timeout_fails_rather_than_passes(self, tmp_path, monkeypatch):
        """A build that never finished is unverified, not clean."""
        import subprocess as sp
        r = self._run(tmp_path, monkeypatch,
                      _Proc(raises=sp.TimeoutExpired(cmd="lake", timeout=600)))
        assert r.passed is False

    def test_no_lakefile_skips_and_passes(self, tmp_path, monkeypatch):
        """Optional-toolchain-absent — one of the five ADR-009 item-4 sites kept as a
        deliberate PASS. Failing a build because Lean is not installed is its own
        defect."""
        r = self._run(tmp_path, monkeypatch, _Proc(0), lakefile=False)
        assert r.passed is True
        assert "SKIPPED" in (r.details[0].message or "")


class TestAxiomClosureAllowlist:
    """Invariant #15 backstop. WARN-first by default; hard-fails under `--strict`."""

    def _run(self, tmp_path, monkeypatch, closures, *, strict=False, metadata=None,
             rc=0, raw=None):
        monkeypatch.setattr(lt, "_resolve_lake", lambda: "/bin/lake")
        root = tmp_path / "lean"
        (root / "SKEFTHawking").mkdir(parents=True, exist_ok=True)
        (root / "SKEFTHawking" / "AxiomAudit.lean").write_text("-- audit")
        monkeypatch.setattr(lt, "_resolve_lean_root", lambda: root)
        monkeypatch.setattr(_c, "AXIOM_METADATA", metadata or {})
        monkeypatch.setattr(_cfg, "STRICT_MODE", strict)
        out = raw if raw is not None else json.dumps(closures)
        monkeypatch.setattr(lt.subprocess, "run", _Proc(rc, stdout=out))
        return lt.check_axiom_closure_allowlist()

    KERNEL_ONLY = {"SKEFTHawking.M.thm": ["propext", "Quot.sound"]}
    ROGUE = {"SKEFTHawking.M.thm": ["propext", "SKEFTHawking.my_axiom"]}

    def test_kernel_only_closures_pass(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA."""
        r = self._run(tmp_path, monkeypatch, self.KERNEL_ONLY)
        assert r.passed is True
        assert any(d.name == "allowlist" and d.passed for d in r.details)

    def test_a_rogue_axiom_warns_by_default(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — as a WARN, which is the documented
        retrofit posture, not an oversight."""
        r = self._run(tmp_path, monkeypatch, self.ROGUE)
        assert r.passed is True
        d = next(d for d in r.details if d.name == "unexpected_axioms")
        assert d.warning and "my_axiom" in (d.message or "")

    def test_a_rogue_axiom_fails_under_strict(self, tmp_path, monkeypatch):
        """The submission gate. STRICT_MODE is read by ATTRIBUTE — by value it would
        freeze at import and `--strict` would silently stop gating (H5)."""
        r = self._run(tmp_path, monkeypatch, self.ROGUE, strict=True)
        assert r.passed is False, (
            "--strict did not promote a non-allow-listed axiom to a FAIL — either the "
            "promotion is gone or STRICT_MODE is bound by value (H5)")

    def test_an_axiom_in_the_metadata_allowlist_is_accepted(self, tmp_path, monkeypatch):
        """The escape is DISCLOSURE: a declared axiom with metadata is allowed, which
        is why the check is a backstop rather than a ban."""
        r = self._run(tmp_path, monkeypatch, self.ROGUE, strict=True,
                      metadata={"SKEFTHawking.my_axiom": {"reason": "documented"}})
        assert r.passed is True

    def test_native_decide_is_a_separate_accepted_category(self, tmp_path, monkeypatch):
        """`counts.json` reports `Axioms: 0` because these are not declared `axiom`s.
        The check surfaces the genuine trust surface anyway — reported, not failed."""
        r = self._run(tmp_path, monkeypatch,
                      {"SKEFTHawking.M.thm":
                       ["propext", "SKEFTHawking.M.thm._native.native_decide.ax_1"]},
                      strict=True)
        assert r.passed is True
        assert any(d.name == "native_decide" and d.warning for d in r.details)

    def test_unparseable_output_skips_rather_than_crashing(self, tmp_path, monkeypatch):
        """One of the five deliberate optional-toolchain PASS sites (item 4)."""
        r = self._run(tmp_path, monkeypatch, {}, raw="not json")
        assert r.passed is True
        assert any(d.warning for d in r.details)


class TestElaborationKnobWatchlist:
    """ADVISORY BY DESIGN — the best-reasoned advisory in the suite. These are
    ELABORATION-time knobs; the kernel re-checks the final term and never reads them,
    so they add nothing to the axiom closure. Both directions are on the WARNING."""

    def test_it_stays_advisory(self, tmp_path, monkeypatch):
        monkeypatch.setattr(_H, "LEAN_DIR", _lean_tree(
            tmp_path, {"M.lean": "set_option maxRecDepth 4000 in\ntheorem t : True := trivial\n"}))
        monkeypatch.setattr(_H, "PROJECT_ROOT", tmp_path)
        assert lt.check_elaboration_knob_watchlist().passed is True, (
            "elaboration_knob_watchlist started failing — ADR-009 item 3 keeps it "
            "advisory because these knobs are kernel-irrelevant; update the ADR too")

    def test_a_knob_is_reported(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT (as a warning)."""
        monkeypatch.setattr(_H, "LEAN_DIR", _lean_tree(
            tmp_path, {"M.lean": "set_option synthInstance.maxSize 400 in\n"}))
        monkeypatch.setattr(_H, "PROJECT_ROOT", tmp_path)
        r = lt.check_elaboration_knob_watchlist()
        assert any("synthInstance.maxSize 400" in (d.message or "") for d in r.details)
        assert r.details[0].warning

    def test_a_clean_tree_reports_zero(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA."""
        monkeypatch.setattr(_H, "LEAN_DIR",
                            _lean_tree(tmp_path, {"M.lean": "theorem t : True := trivial\n"}))
        monkeypatch.setattr(_H, "PROJECT_ROOT", tmp_path)
        r = lt.check_elaboration_knob_watchlist()
        assert not r.details[0].warning
        assert "0 proof-body" in (r.details[0].message or "")

    def test_maxHeartbeats_in_a_proof_body_is_now_ENFORCED(self, tmp_path, monkeypatch):
        """⚠️ THIS TEST IS THE INVERSE OF THE ONE IT REPLACES, AND THAT IS THE POINT.

        It read `test_maxHeartbeats_is_deliberately_not_watched_here`, asserting
        `"0 proof-body"`, and its docstring said: *"Invariant #10 forbids
        `maxHeartbeats` in a proof body OUTRIGHT and is enforced elsewhere."*

        **It was enforced nowhere.** `rg maxHeartbeats scripts/` returned only this
        check's own docstring and its exclusion list, while the substrate carried
        22 live violations. So the branch shipped a GREEN TEST whose docstring told
        the next reader the gap was correct — the strongest form of this audit's
        central defect, and closing the gap required breaking a passing test.

        Found by reviewer R5 (PR-review pass 2, R5-MAJ3).
        """
        monkeypatch.setattr(_H, "LEAN_DIR", _lean_tree(
            tmp_path, {"M.lean": "set_option maxHeartbeats 400000 in\n"
                                 "theorem t : True := by trivial\n"}))
        monkeypatch.setattr(_H, "PROJECT_ROOT", tmp_path)
        monkeypatch.setattr(lt, "MAXHEARTBEATS_PROOF_BODY_CEILING", 0)
        r = lt.check_elaboration_knob_watchlist()
        assert r.passed is False, (
            "a proof-body `maxHeartbeats` above the ceiling did not fail the check "
            "— Invariant #10 is unenforced again")
        inv = next(d for d in r.details if d.name == "invariant_10")
        assert "1 `maxHeartbeats` site" in inv.message

    def test_a_file_level_set_option_is_not_counted_as_a_proof_body(
            self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA. The predicate is "attached to a
        theorem/lemma/example", so a bare file-level `set_option` with no
        declaration under it must not count — otherwise the ratchet drifts on
        something Invariant #10 does not name."""
        monkeypatch.setattr(_H, "LEAN_DIR", _lean_tree(
            tmp_path, {"M.lean": "set_option maxHeartbeats 400000\n\n-- nothing\n"}))
        monkeypatch.setattr(_H, "PROJECT_ROOT", tmp_path)
        monkeypatch.setattr(lt, "MAXHEARTBEATS_PROOF_BODY_CEILING", 0)
        r = lt.check_elaboration_knob_watchlist()
        assert r.passed is True

    def test_the_ceiling_has_ZERO_HEADROOM_against_the_live_tree(self):
        """House ratchet idiom, measured against production: slack is a ratchet
        that cannot fire. ⚠️ This number was measured three times during pass 2 and
        the lead was wrong twice — see the constant's docstring."""
        r = lt.check_elaboration_knob_watchlist()
        inv = next(d for d in r.details if d.name == "invariant_10")
        n = int(inv.message.split()[0])
        assert n == lt.MAXHEARTBEATS_PROOF_BODY_CEILING, (
            f"{n} live violation(s) against a ceiling of "
            f"{lt.MAXHEARTBEATS_PROOF_BODY_CEILING}. If it dropped, LOWER the "
            f"ceiling in the same commit; if it rose, decompose into `have` "
            f"sub-lemmas — raising the ceiling is a decision, not a fix.")


class TestLeanDocstringRefsResolve:
    """Rename drift inside Lean docstrings — the class that produced BLOCKER 1.1 of
    the Phase-6EA review and fired the same day a lead rename landed."""

    def _run(self, tmp_path, monkeypatch, files, deps_names=("real_theorem",)):
        p = tmp_path / "lean_deps.json"
        p.write_text(json.dumps(
            [{"name": f"SKEFTHawking.Detection.{n}", "type": "P", "kind": "theorem"}
             for n in deps_names]))
        monkeypatch.setattr(_H, "LEAN_DEPS_PATH", p)
        monkeypatch.setattr(_H, "LEAN_DIR", _lean_tree(tmp_path, files))
        monkeypatch.setattr(_H, "PROJECT_ROOT", tmp_path)
        return lt.check_lean_docstring_refs_resolve()

    def test_a_resolving_reference_passes(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA."""
        r = self._run(tmp_path, monkeypatch,
                      {"Detection/M.lean": "/-- Uses `real_theorem`. -/\n"})
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_a_drifted_reference_in_a_strict_family_fails(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT."""
        r = self._run(tmp_path, monkeypatch,
                      {"Detection/M.lean": "/-- Uses `renamed_away_theorem`. -/\n"})
        assert r.passed is False, (
            "a docstring naming a nonexistent declaration passed inside a STRICT "
            "family — this is Phase-6EA BLOCKER 1.1 reopened")

    def test_the_same_drift_outside_a_strict_family_is_advisory(self, tmp_path, monkeypatch):
        """The legacy backlog is reported without blocking — that is what makes the
        strict families enforceable at all."""
        r = self._run(tmp_path, monkeypatch,
                      {"Legacy/M.lean": "/-- Uses `renamed_away_theorem`. -/\n"})
        assert r.passed is True
        assert any(d.name.startswith("drift-advisory") for d in r.details)

    def test_a_disclaimed_absent_name_is_exempt(self, tmp_path, monkeypatch):
        """A docstring may deliberately name something that does NOT exist — recording
        a rejected route. That is the OPPOSITE of drift: it is the record that keeps
        someone from re-adding it."""
        r = self._run(tmp_path, monkeypatch, {"Detection/M.lean":
            "/-- `renamed_away_theorem` was REJECTED and deliberately not shipped. -/\n"})
        assert r.passed is True

    def test_a_plain_block_comment_header_is_scanned(self, tmp_path, monkeypatch):
        """A load-bearing reference sat in a `/- … -/` MODULE HEADER through five
        adversarial reviews because only `/-- … -/` was scanned."""
        r = self._run(tmp_path, monkeypatch,
                      {"Detection/M.lean": "/- Header cites `renamed_away_theorem`. -/\n"})
        assert r.passed is False, (
            "a plain `/- … -/` module header was not scanned — that is the gap that "
            "hid `combined_floor_add_strictly_sharper` through five reviews")

    def test_short_and_non_snake_tokens_are_ignored(self, tmp_path, monkeypatch):
        """Noise control: a backticked token needs an underscore, 6+ chars and a
        lowercase letter to be a candidate. Without this the check would flag every
        tactic name and local binder in the library."""
        r = self._run(tmp_path, monkeypatch,
                      {"Detection/M.lean": "/-- See `h`, `foo`, `ABC_DEF`. -/\n"})
        assert r.passed is True

    def test_a_missing_lean_deps_passes_WITH_A_WARNING(self, tmp_path, monkeypatch):
        """⚠️ A THIRD distinct H4 policy: absence here is PASS-with-warning, where five
        loaders pass silently and two fail. ADR-009 §Deferred item 4 DECLINED unifying
        these; pinned so a future sweep is a deliberate act."""
        monkeypatch.setattr(_H, "LEAN_DEPS_PATH", tmp_path / "absent.json")
        r = lt.check_lean_docstring_refs_resolve()
        assert r.passed is True
        assert r.details[0].warning


class TestLeanModulesInBuildGraph:
    """`lean_modules_in_build_graph` — the filesystem/import-graph join.

    A module on disk that no import reaches is compiled by nothing, indexed by nothing
    and guarded by nothing, so its content is invisible to every other check in the
    suite. This is the one check whose failure means the population all the others
    measure is a proper subset of the project.
    """

    def _tree(self, tmp_path, monkeypatch, modules, root_imports, lakefile=""):
        src = tmp_path / "lean" / "SKEFTHawking"
        src.mkdir(parents=True)
        for m in modules:
            p = src / (m.replace(".", "/") + ".lean")
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text("-- test module\n")
        (tmp_path / "lean" / "SKEFTHawking.lean").write_text(
            "".join(f"import SKEFTHawking.{m}\n" for m in root_imports))
        (tmp_path / "lean" / "lakefile.toml").write_text(lakefile)
        monkeypatch.setattr(_H, "PROJECT_ROOT", tmp_path)
        return src

    def test_an_unreachable_module_FAILS(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT."""
        self._tree(tmp_path, monkeypatch, ["A", "B"], ["A"])
        monkeypatch.setattr(lt, "UNREACHABLE_MODULE_EXCEPTIONS", {})
        r = lt.check_lean_modules_in_build_graph()
        assert r.passed is False
        assert any(d.name == "orphans" and not d.passed for d in r.details)

    def test_full_coverage_is_SILENT(self, tmp_path, monkeypatch):
        self._tree(tmp_path, monkeypatch, ["A", "B"], ["A", "B"])
        monkeypatch.setattr(lt, "UNREACHABLE_MODULE_EXCEPTIONS", {})
        assert lt.check_lean_modules_in_build_graph().passed is True

    def test_transitive_imports_count_as_reachable(self, tmp_path, monkeypatch):
        """`B` reached only via `A` is reachable — the closure, not the direct list."""
        src = self._tree(tmp_path, monkeypatch, ["A", "B"], ["A"])
        (src / "A.lean").write_text("import SKEFTHawking.B\n")
        monkeypatch.setattr(lt, "UNREACHABLE_MODULE_EXCEPTIONS", {})
        assert lt.check_lean_modules_in_build_graph().passed is True

    def test_exe_roots_are_DERIVED_from_the_lakefile(self, tmp_path, monkeypatch):
        """An exe root is legitimately outside the library, and the allowlist must come
        from `lakefile.toml` — a hardcoded list goes stale the moment a root is added."""
        self._tree(tmp_path, monkeypatch, ["A", "Tool"], ["A"],
                   lakefile='[[lean_exe]]\nname = "tool"\nroot = "SKEFTHawking.Tool"\n')
        monkeypatch.setattr(lt, "UNREACHABLE_MODULE_EXCEPTIONS", {})
        assert lt.check_lean_modules_in_build_graph().passed is True
        # ...and the same tree WITHOUT the declaration must fail, or the allowlist is
        # not actually being read.
        (tmp_path / "lean" / "lakefile.toml").write_text("")
        assert lt.check_lean_modules_in_build_graph().passed is False

    def test_an_absent_source_dir_is_UNMEASURABLE_not_passing(self, tmp_path, monkeypatch):
        monkeypatch.setattr(_H, "PROJECT_ROOT", tmp_path)
        r = lt.check_lean_modules_in_build_graph()
        assert r.passed is False and r.measured is False

    def test_the_LIVE_tree_agrees_with_its_import_graph(self):
        """PRODUCTION-SEEDED (QI-30). Runs against the real tree: a fixture proves the
        predicate, not that the corpus satisfies it. Mutation-verified by deleting
        `import SKEFTHawking.AtlasAttr` (a true leaf) from the real root aggregate — red,
        and green on restore. NOTE a non-leaf is a bad probe: removing a module that
        another module imports leaves it transitively reachable and correctly stays green.
        """
        r = lt.check_lean_modules_in_build_graph()
        assert r.passed, [d.message for d in r.details if not d.passed]
