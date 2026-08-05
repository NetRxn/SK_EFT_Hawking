"""D5 both-directions tests for `validation/checks/physics.py` — audit QI-27.

Seven checks: `numerical`, `identities`, `paper_table`, `cgl_fdr`, `physical_bounds`,
`cross_path_consistency`, `quantum_network`. (`d1_hierarchy_table` and
`f_hierarchy_claims` already had genuine both-directions tests; those live in
`test_d1_hierarchy_table.py` / `test_f_hierarchy_claims.py`, reinforced under QI-27
with isolated-defect legs after three verdict-propagation mutations came back MISSED.)

WHAT WAS THERE BEFORE
---------------------
`tests/test_cross_validation.py` covers `numerical`, `identities` and `paper_table` —
and is the exact shape ADR-009 §Context measured as *"eleven assert only
`result.passed` on the live tree"*. Every one of its assertions is satisfied by a check
rewritten to `return CheckResult(passed=True, details=[])`. It is a useful smoke test
of the live tree and it is **not** protection, so it is kept and supplemented rather
than replaced.

HOW A DEFECT IS SEEDED HERE
---------------------------
These checks compare the physics modules against hardcoded reference values, so the
seam is the DATA SOURCE, not a path. Each check imports its source inside its own body
(`from src.core.constants import get_all_experiments`, `from src.wkb.spectrum import
…`), which means monkeypatching the attribute on the source module reaches it at call
time — the same by-attribute discipline ADR-009 H5 requires for runtime flags.

`TestNumericalConsistency` and `TestPaperTable` read each check's own reference table
out of the AST rather than restating it, for the reason `test_d5_lean_substrate` does:
a hand-copied constant silently describes a different experiment the day the table is
edited.

MUTATION-VERIFIED 2026-08-04 — 9 mutations, all CAUGHT, clean negative control.
AST-scoped; restored with bytecode invalidation (see the §4b `.pyc` lesson — a
same-length mutation restored inside one second survives a source restore).

  | mutation                                                     | caught by |
  |---|---|
  | `numerical`: `ok = rel_err <= tolerance` -> `ok = True`       | `…perturbed…` |
  | `identities`: `if not ok: all_pass = False` -> `pass`         | `…wrong_identity…` |
  | `paper_table`: `ok = rel_err <= tolerance` -> `ok = True`     | `…drifted…` |
  | `cgl_fdr`: `if not ok: all_pass = False` (einstein) -> `pass` | `…einstein…` |
  | `cgl_fdr`: `ok = counts == {…}` -> `ok = True`                | `…noise_count…` |
  | `physical_bounds`: `if not passed: all_pass = False` -> `pass`| `…negative_temperature…` |
  | `cross_path_consistency`: `ok = rel_diff < 0.005` -> `True`   | `…paths_drift…` |
  | `quantum_network`: `if not cond: all_pass = False` -> `pass`  | `…identity_broken…` |
  | `quantum_network`: `rglob` -> `glob`                          | `…subdirectory…` (QI-01) |
"""
from __future__ import annotations

import ast
import sys
from pathlib import Path
from types import SimpleNamespace

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT / "scripts"))
sys.path.insert(0, str(SK_ROOT))

import validate_helpers as _H  # noqa: E402
from validation.checks import physics as ph  # noqa: E402


def _literal_in_check(func_name: str, var: str):
    """Read a literal assignment out of a check's body via the AST.

    Same idiom (and same reason) as `test_d5_lean_substrate`: the reference tables
    below are function-local, and a copy in this file would go stale silently the
    day someone corrects an experimental value.
    """
    src = Path(ph.__file__).read_text()
    fn = next(n for n in ast.walk(ast.parse(src))
              if isinstance(n, ast.FunctionDef) and n.name == func_name)
    for node in ast.walk(fn):
        if isinstance(node, ast.Assign) and \
                any(getattr(t, "id", None) == var for t in node.targets):
            return ast.literal_eval(node.value)
    raise AssertionError(f"{func_name} no longer assigns a literal `{var}`")


class _Override:
    """Read-only attribute override by delegation.

    `PlatformParams.T_H` is a computed property with no setter, so a defect cannot
    be seeded by assignment. Delegating rather than subclassing keeps the rest of
    the platform's real behaviour — the point is to perturb ONE quantity and leave
    everything the check reads downstream genuinely computed.
    """

    def __init__(self, base, **over):
        object.__setattr__(self, "_over", over)
        object.__setattr__(self, "_base", base)

    def __getattr__(self, name):
        over = object.__getattribute__(self, "_over")
        if name in over:
            return over[name]
        return getattr(object.__getattribute__(self, "_base"), name)


def _fake_experiments(table: dict, *, scale: dict | None = None) -> dict:
    """Build a `get_all_experiments()` return value from a reference table.

    `scale` multiplies chosen `platform.param` entries, which is how a defect is
    seeded: a value outside the check's declared 5 % tolerance.
    """
    scale = scale or {}
    out = {}
    for name, vals in table.items():
        v = {k: vals[k] * scale.get(f"{name}.{k}", 1.0) for k in vals}
        out[name] = (
            SimpleNamespace(sound_speed_upstream=v["c_s"], healing_length=v["xi"]),
            SimpleNamespace(surface_gravity=v["kappa"], hawking_temp=v["T_H"]),
        )
    return out


class TestNumericalConsistency:
    """Experimental parameters agree with the published reference values within 5 %."""

    def _patch(self, monkeypatch, **kw):
        from src.core import constants
        table = _literal_in_check("check_numerical_consistency", "expected")
        monkeypatch.setattr(constants, "get_all_experiments",
                            lambda: _fake_experiments(table, **kw))
        return table

    def test_matching_values_pass(self, monkeypatch):
        """SILENT ON CORRECT DATA."""
        self._patch(monkeypatch)
        r = ph.check_numerical_consistency()
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]
        assert r.details, "the check reported success having compared nothing"

    def test_a_perturbed_parameter_fails(self, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — one parameter moved 20 %, four times the
        declared 5 % tolerance."""
        self._patch(monkeypatch, scale={"Steinhauer.c_s": 1.20})
        r = ph.check_numerical_consistency()
        assert r.passed is False, (
            "a 20 % drift in the Steinhauer sound speed reported PASS — the "
            "parameter comparison no longer reaches the verdict")
        assert {d.name for d in r.details if not d.passed} == {"Steinhauer.c_s"}

    def test_a_drift_just_inside_tolerance_passes(self, monkeypatch):
        """The tolerance is a declared 5 %, not decoration. 4 % must pass and 6 %
        must fail, or the constant is doing nothing."""
        self._patch(monkeypatch, scale={"Trento.kappa": 1.04})
        assert ph.check_numerical_consistency().passed is True
        self._patch(monkeypatch, scale={"Trento.kappa": 1.06})
        assert ph.check_numerical_consistency().passed is False

    def test_a_raising_source_fails_rather_than_passes(self, monkeypatch):
        from src.core import constants

        def _boom():
            raise RuntimeError("solver unavailable")
        monkeypatch.setattr(constants, "get_all_experiments", _boom)
        assert ph.check_numerical_consistency().passed is False


class TestFormulaIdentities:
    """Boundary conditions that must hold exactly: `disp(0)==0`, the acoustic-mode
    vanishing, the coefficient counts."""

    def test_the_live_identities_hold(self):
        """SILENT ON CORRECT DATA. This one legitimately runs against the real
        formulas — the identities are exact, so there is no corpus to drift."""
        r = ph.check_formula_identities()
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_a_wrong_identity_fails(self, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — `dispersive_correction(0)` must be 0."""
        from src.core import formulas
        monkeypatch.setattr(formulas, "dispersive_correction", lambda *a, **k: 1.0)
        r = ph.check_formula_identities()
        assert r.passed is False, (
            "dispersive_correction(0) returned 1.0 and the identity check passed")
        assert any(d.name == "disp(0)==0" and not d.passed for d in r.details)

    def test_a_raising_formula_fails_rather_than_erroring_out(self, monkeypatch):
        """Each identity is individually guarded, so one broken formula must be
        reported as a failing DETAIL rather than aborting the check."""
        from src.core import formulas

        def _boom(*a, **k):
            raise ValueError("domain error")
        monkeypatch.setattr(formulas, "count_coefficients", _boom)
        r = ph.check_formula_identities()
        assert r.passed is False
        assert any("domain error" in (d.message or "") for d in r.details)

    def test_the_acoustic_mode_vanishing_is_load_bearing(self, monkeypatch):
        """δ⁽²⁾ must vanish for the acoustic mode with γ₂₂ = −γ₂₁. This is the one
        identity in the list that is physics rather than arithmetic."""
        from src.core import formulas
        monkeypatch.setattr(formulas, "second_order_correction", lambda *a, **k: 1e-3)
        r = ph.check_formula_identities()
        assert r.passed is False
        assert any(d.name == "delta2_acoustic_vanishes" and not d.passed
                   for d in r.details)


class TestPaperTableConsistency:
    """Paper 1's Table 1 against solver output. Note the table's Steinhauer κ/T_H are
    MODEL values (tanh profile), deliberately not the published step-potential ones."""

    def _patch(self, tmp_path, monkeypatch, **kw):
        from src.core import constants
        d = tmp_path / "paper1_first_order"
        d.mkdir(parents=True, exist_ok=True)
        (d / "paper_draft.tex").write_text("draft")
        monkeypatch.setattr(_H, "PAPERS_DIR", tmp_path)
        table = _literal_in_check("check_paper_table_consistency", "paper_table")
        monkeypatch.setattr(constants, "get_all_experiments",
                            lambda: _fake_experiments(table, **kw))

    def test_matching_values_pass(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA."""
        self._patch(tmp_path, monkeypatch)
        r = ph.check_paper_table_consistency()
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]
        assert r.details

    def test_a_drifted_table_value_fails(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — the published table and the code disagree,
        which is the entire purpose of the check."""
        self._patch(tmp_path, monkeypatch, scale={"Heidelberg.T_H": 1.5})
        r = ph.check_paper_table_consistency()
        assert r.passed is False
        assert {d.name for d in r.details if not d.passed} == {"Heidelberg.T_H"}

    def test_a_missing_draft_fails_rather_than_passing(self, tmp_path, monkeypatch):
        """Cannot-measure is not success. This check already gets it right — pinned
        so it is not 'softened' into a skip."""
        monkeypatch.setattr(_H, "PAPERS_DIR", tmp_path / "nonexistent")
        r = ph.check_paper_table_consistency()
        assert r.passed is False
        assert "not found" in (r.error or "")


class TestCglFdr:
    """The CGL dynamical-KMS derivation of the fluctuation-dissipation relation."""

    def test_the_live_derivation_holds(self):
        """SILENT ON CORRECT DATA."""
        r = ph.check_cgl_fdr()
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_a_failing_einstein_relation_fails(self, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — σ = γ/β₀ is the base case the rest builds on."""
        from src.second_order import cgl_derivation
        monkeypatch.setattr(cgl_derivation, "verify_einstein_relation", lambda: False)
        r = ph.check_cgl_fdr()
        assert r.passed is False, (
            "the Einstein relation reported False and the check still passed")
        assert any(d.name == "einstein_relation" and not d.passed for d in r.details)

    def test_a_wrong_noise_count_pattern_fails(self, monkeypatch):
        """The noise-count pattern {0:1, 1:0, 2:2, 3:0, 4:3} encodes that noise
        kernels appear only at EVEN orders — the structural claim of the derivation,
        not a numerical coincidence."""
        from src.second_order import cgl_derivation
        monkeypatch.setattr(cgl_derivation, "derive_fdr_fourier",
                            lambda n: {N: {"noise": [0] * N} for N in range(n + 1)})
        r = ph.check_cgl_fdr()
        assert r.passed is False
        assert any(d.name == "noise_count_pattern" and not d.passed for d in r.details)

    def test_each_verifier_is_wired_independently(self, monkeypatch):
        """Four verifiers, four separate details. If they shared a code path, one
        of these would not move the verdict on its own."""
        from src.second_order import cgl_derivation
        for fn, detail in (("verify_first_order_bec", "first_order_bec"),
                           ("verify_second_order_fdr", "second_order_real")):
            mp = monkeypatch.__class__()
            mp.setattr(cgl_derivation, fn, lambda: False)
            r = ph.check_cgl_fdr()
            mp.undo()
            assert r.passed is False, f"{fn} returning False did not fail the check"
            assert any(d.name == detail and not d.passed for d in r.details)


class TestPhysicalBounds:
    """Invariant #5: every computed quantity carries bounds. Catches absurdities —
    negative temperatures, perturbative corrections above 1."""

    def test_the_live_spectra_are_in_bounds(self):
        """SILENT ON CORRECT DATA."""
        r = ph.check_physical_bounds()
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_a_negative_temperature_fails(self, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — the headline absurdity the check names."""
        from src.wkb import spectrum
        real = spectrum.steinhauer_platform
        monkeypatch.setattr(spectrum, "steinhauer_platform",
                            lambda: _Override(real(), T_H=-1.0))
        r = ph.check_physical_bounds()
        assert r.passed is False, (
            "a negative Hawking temperature passed the physical-bounds check")
        assert any("T_H > 0" in d.name and not d.passed for d in r.details)

    def test_a_perturbative_correction_above_one_fails(self, monkeypatch):
        """δ_diss ≥ 1 means the perturbative expansion has broken down — reporting
        it as a valid spectrum is the failure mode this check exists for."""
        from src.wkb import spectrum
        real = spectrum.spectrum_summary
        monkeypatch.setattr(spectrum, "spectrum_summary",
                            lambda s: {**real(s), "delta_diss_at_T_H": 1.5})
        r = ph.check_physical_bounds()
        assert r.passed is False
        assert any("0 < delta_diss < 1" in d.name and not d.passed for d in r.details)

    def test_the_shot_count_floor_only_applies_to_tiny_corrections(self, monkeypatch):
        """The conditional leg: a sub-0.1 % correction needs > 10⁴ shots to resolve.
        Asserting it unconditionally would flag correct large-correction platforms."""
        from src.wkb import spectrum
        real = spectrum.spectrum_summary
        monkeypatch.setattr(spectrum, "spectrum_summary",
                            lambda s: {**real(s), "delta_diss_at_T_H": 1e-6,
                                       "shots_needed": 10})
        r = ph.check_physical_bounds()
        assert r.passed is False
        assert any("shots > 10^4" in d.name and not d.passed for d in r.details)


class TestCrossPathConsistency:
    """Duplicate implementations that drift apart. The check compares δ_diss and the
    decoherence parameter computed two ways, within 0.5 %."""

    def test_the_live_paths_agree(self):
        """SILENT ON CORRECT DATA."""
        r = ph.check_cross_path_consistency()
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]
        assert r.details, "the check compared nothing and reported agreement"

    def test_drifted_paths_fail(self, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — `spectrum_summary` and the direct formula
        disagree by 10 %, twenty times the declared tolerance."""
        from src.wkb import spectrum
        real = spectrum.spectrum_summary
        monkeypatch.setattr(spectrum, "spectrum_summary",
                            lambda s: {**real(s),
                                       "delta_diss_at_T_H": real(s)["delta_diss_at_T_H"] * 1.10})
        r = ph.check_cross_path_consistency()
        assert r.passed is False, (
            "two code paths disagreeing by 10 % reported agreement — this check is "
            "the only thing standing between a duplicated formula and silent drift")

    def test_the_decoherence_path_is_wired_independently(self, monkeypatch):
        """Two comparisons, two paths. Moving only the decoherence value must fail,
        or the second comparison is riding on the first."""
        from src.wkb import spectrum
        real = spectrum.spectrum_summary
        monkeypatch.setattr(spectrum, "spectrum_summary",
                            lambda s: {**real(s),
                                       "delta_k_at_T_H": real(s)["delta_k_at_T_H"] * 1.10})
        r = ph.check_cross_path_consistency()
        assert r.passed is False
        assert any("decoherence" in d.name and not d.passed for d in r.details)


class TestQuantumNetwork:
    """The QN Python mirror against the identities proven in
    `lean/SKEFTHawking/QuantumNetwork/*.lean` (Phases 6AA–6AD)."""

    def test_the_live_mirror_satisfies_every_identity(self):
        """SILENT ON CORRECT DATA."""
        r = ph.check_quantum_network()
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_a_broken_identity_fails(self, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — Horodecki's F_avg = (2F+1)/3 is a closed
        form, so any deviation is a Python/Lean divergence."""
        from src.core import formulas
        monkeypatch.setattr(formulas, "teleport_avg_fidelity", lambda F: 0.5)
        r = ph.check_quantum_network()
        assert r.passed is False, (
            "the teleportation fidelity stopped matching the proven closed form and "
            "the cross-validation passed")
        assert any(d.name == "teleport_horodecki_formula" and not d.passed
                   for d in r.details)

    def test_a_missing_lean_theorem_fails(self, tmp_path, monkeypatch):
        """The roster leg: the check names twelve QN theorems explicitly and must
        fail if one disappears from the Lean source."""
        qn = tmp_path / "QuantumNetwork"
        qn.mkdir(parents=True)
        (qn / "Partial.lean").write_text("theorem wernerParam_swap : True := trivial\n")
        monkeypatch.setattr(_H, "LEAN_DIR", tmp_path)
        r = ph.check_quantum_network()
        assert r.passed is False
        d = next(d for d in r.details if d.name == "qn_lean_theorems_exist")
        assert not d.passed and "missing:" in (d.message or "")

    def test_a_theorem_in_a_subdirectory_is_found(self, tmp_path, monkeypatch):
        """QI-01 at the SIXTH site — the one the manual grep sweep missed because
        its receiver is named `qn_dir`. `QuantumNetwork/` is flat today, so this is
        latent; but the check FAILS on a theorem it cannot find, so the day a package
        lands here the non-recursive form would report real theorems missing."""
        expected = _literal_in_check("check_quantum_network", "expected")
        qn = tmp_path / "QuantumNetwork" / "Sub" / "Deeper"
        qn.mkdir(parents=True)
        (qn / "All.lean").write_text(
            "\n".join(f"theorem {n} : True := trivial" for n in expected))
        monkeypatch.setattr(_H, "LEAN_DIR", tmp_path)
        d = next(d for d in ph.check_quantum_network().details
                 if d.name == "qn_lean_theorems_exist")
        assert d.passed, (
            f"QN theorems in a subdirectory were not found ({d.message}) — the scan "
            f"is non-recursive again (audit QI-01)")

    def test_a_missing_quantum_network_dir_fails(self, tmp_path, monkeypatch):
        """Cannot-measure is not success."""
        monkeypatch.setattr(_H, "LEAN_DIR", tmp_path / "nonexistent")
        r = ph.check_quantum_network()
        assert r.passed is False
        assert any(d.name == "qn_lean_theorems_exist" and not d.passed
                   for d in r.details)
