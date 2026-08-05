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
    """The registry-count check. Its expected value is HARDCODED in three places —
    see `test_the_expected_count_is_hardcoded_in_three_places` for why that matters."""

    def test_a_consistent_registry_passes(self, monkeypatch):
        """SILENT ON CORRECT DATA."""
        expected = self._expected()
        monkeypatch.setattr(_c, "TOTAL_THEOREMS", expected)
        monkeypatch.setattr(_c, "ARISTOTLE_THEOREMS", {f"t{i}": {} for i in range(expected)})
        r = lt.check_theorem_count()
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_a_count_below_the_expected_value_fails(self, monkeypatch):
        """FIRES ON THE SEEDED DEFECT."""
        expected = self._expected()
        monkeypatch.setattr(_c, "TOTAL_THEOREMS", expected - 1)
        monkeypatch.setattr(_c, "ARISTOTLE_THEOREMS",
                            {f"t{i}": {} for i in range(expected - 1)})
        assert lt.check_theorem_count().passed is False

    def test_a_registry_inconsistent_with_its_total_fails(self, monkeypatch):
        """The `consistency` leg: `TOTAL_THEOREMS` and the dict must agree with each
        other, not merely each with the literal."""
        expected = self._expected()
        monkeypatch.setattr(_c, "TOTAL_THEOREMS", expected)
        monkeypatch.setattr(_c, "ARISTOTLE_THEOREMS",
                            {f"t{i}": {} for i in range(expected - 1)})
        r = lt.check_theorem_count()
        assert r.passed is False
        assert any(d.name == "consistency" and not d.passed for d in r.details)

    @staticmethod
    def _expected() -> int:
        src = Path(lt.__file__).read_text()
        fn = next(n for n in ast.walk(ast.parse(src))
                  if isinstance(n, ast.FunctionDef) and n.name == "check_theorem_count")
        lits = sorted({n.value for n in ast.walk(fn)
                       if isinstance(n, ast.Constant) and isinstance(n.value, int)
                       and n.value > 1})
        assert len(lits) == 1, (
            f"expected exactly one integer literal in check_theorem_count, found {lits}")
        return lits[0]

    def test_the_expected_count_is_hardcoded_in_three_places(self):
        """⚠️ PINS A KNOWN RESIDUAL, not a desired design (audit §4, also noted in
        RESUME_STATE): the expected theorem count is a hand-typed literal appearing in
        the registered DESCRIPTION and in two dict entries. Nothing derives it from
        `docs/counts.json`, so bumping the substrate means editing three strings and
        the check silently measures the old target if you miss one.

        This test asserts they still AGREE. It deliberately does not assert a value —
        that would be a fourth copy. Deriving the count from `counts.json` is the real
        fix and is out of this audit's scope.
        """
        src = Path(lt.__file__).read_text()
        tree = ast.parse(src)
        fn = next(n for n in ast.walk(tree)
                  if isinstance(n, ast.FunctionDef) and n.name == "check_theorem_count")
        body_lits = [n.value for n in ast.walk(fn)
                     if isinstance(n, ast.Constant) and isinstance(n.value, int)
                     and n.value > 1]
        assert len(body_lits) == 2 and body_lits[0] == body_lits[1], (
            f"check_theorem_count's two expected-count literals disagree: {body_lits}")
        desc = next(s.description for s in __import__("validate")._CHECKS
                    if s.name == "theorems")
        assert str(body_lits[0]) in desc, (
            f"the registered description says {desc!r} but the body checks "
            f"{body_lits[0]} — the third copy has drifted, and `--list` now advertises "
            f"a target the check does not enforce")


class TestLeanSource:
    """Spot-check theorem names still resolve in the Lean source."""

    @staticmethod
    def _spot_names() -> list[str]:
        src = Path(lt.__file__).read_text()
        fn = next(n for n in ast.walk(ast.parse(src))
                  if isinstance(n, ast.FunctionDef) and n.name == "check_lean_source")
        for node in ast.walk(fn):
            if isinstance(node, ast.Assign) and \
                    any(getattr(t, "id", None) == "spot_checks" for t in node.targets):
                return sorted(set(ast.literal_eval(node.value).values()))
        raise AssertionError("check_lean_source no longer assigns a literal spot_checks")

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
        of 2,039 files and 7,695 declared identifiers were invisible — a spot-check
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
        monkeypatch.delenv("LEAN_PROJECT_DIR", raising=False)
        assert lt._resolve_lean_root() == _H.PROJECT_ROOT / "lean"

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

    def test_maxHeartbeats_is_deliberately_not_watched_here(self, tmp_path, monkeypatch):
        """Invariant #10 forbids `maxHeartbeats` in a proof body OUTRIGHT and is
        enforced elsewhere. Listing it here would double-report it as advisory, which
        would read as 'allowed with a warning'."""
        monkeypatch.setattr(_H, "LEAN_DIR", _lean_tree(
            tmp_path, {"M.lean": "set_option maxHeartbeats 400000 in\n"}))
        monkeypatch.setattr(_H, "PROJECT_ROOT", tmp_path)
        r = lt.check_elaboration_knob_watchlist()
        assert "0 proof-body" in (r.details[0].message or "")


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
