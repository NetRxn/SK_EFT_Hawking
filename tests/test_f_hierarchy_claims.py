"""Tests for the ``f_hierarchy_claims`` validate.py gate (finding B-01,
flagship residual).

Sibling of ``d1_hierarchy_table``: the flagship ``papers/F`` quotes the
BEC corrections inline (prose), not as a table, so the gate targets the
specific Heidelberg sentences by anchored regex and compares each value to
the same canonical evaluator (Heidelberg row) within 0.5 %.

Coverage:
    - registration + description
    - PASS smoke on the live repo
    - FAIL on a synthetic draft carrying F's historical stale magnitudes
      (δ_diss ~26 %, δ_disp ~10 %, spectral floor ~2 T_H) — each anchor
      must be missing/mismatched
    - PASS on a synthetic draft with the corrected sentences
    - the polariton (−19 %) / graphene (−2.8 %) values are NOT matched
      against the Heidelberg row (no false positive)
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT))
sys.path.insert(0, str(SK_ROOT / "scripts"))

import validate as v
import validate_helpers as _H  # noqa: E402
from validate import check_f_hierarchy_claims  # noqa: E402


# ── historical stale flagship text (exactly what the residual flagged) ──
_STALE_F = r"""
modulo the parity sector. The dissipative correction $\delta_{\mathrm{diss}}$
to the Hawking spectrum picks up a second-order contribution that
shifts the spectrum by $\sim 26\%$ at the Heidelberg parameters; the
sign and magnitude are substrate predictions.

\item \textbf{Spectral floor at $\omega \sim 2 T_H$ for Heidelberg.}
  The exact-WKB closure produces a spectral-density floor at low
  frequencies that quantitatively matches the Heidelberg observation.

analog-Hawking systems. On the BEC platform (Heidelberg), the
dispersive correction $\delta_{\mathrm{disp}}$ contributes $\sim 10\%$
at the natural microscopic point, while $\delta_{\mathrm{diss}}$
contributes $\sim 26\%$ (the sign opposite). On the polariton
platform, the corresponding values are $\delta_{\mathrm{disp}} \approx
-19\%$, $\delta_{\mathrm{diss}}$ subdominant.
"""

# ── corrected flagship text (matches the live regenerated F) ────────────
_FIXED_F = r"""
modulo the parity sector. The dissipative correction $\delta_{\mathrm{diss}}$
to the Hawking spectrum is $\delta_{\mathrm{diss}} \approx 1.59\times10^{-3}$
($0.16\%$) at the Heidelberg parameters, with the second-order
contribution further suppressed by $\xi/c_s$; its sign and magnitude
are substrate predictions.

\item \textbf{Spectral floor at $\omega_\times \simeq 6.44\,T_{\rm eff}$ for Heidelberg.}
  The exact-WKB closure produces a spectral-density floor onto which
  the thermal Hawking tail settles once the thermal occupation
  $\left(e^{\omega/T_{\rm eff}(\omega)}-1\right)^{-1}$ falls to the FDR floor at zero environment temperature. That floor
  is $\delta_{\mathrm{diss}}$, not $\delta_{\mathrm{diss}}/2$: the
  factor of two is already taken inside
  $n_{\mathrm{noise}} = \delta_k/2 = (2\Gamma_H/\kappa)/2 = \Gamma_H/\kappa
  = \delta_{\mathrm{diss}}$
  (\texttt{WKBConnection.noise\_floor\_eq\_delta\_diss}). The thermal scale is
  $T_{\rm eff}(\omega) = \kappa_{\rm eff}(\omega)/(2\pi)$, distinct from
  the bare scale $T_H = \kappa/(2\pi)$ used for the ultraviolet cutoff.
  Here $T_{\rm eff}$ refers to the thermal component, rather than a
  temperature fitted to the total occupation including noise. The crossover is
  therefore
  $\omega_\times = T_{\rm eff}(\omega_\times) \ln\!\left(1 + 1/\delta_{\mathrm{diss}}\right)
  \approx 6.44\, T_{\rm eff}(\omega_\times)$ for Heidelberg.
  The frequency dependence of $\kappa_{\rm eff}$ makes this an implicit
  equation for $\omega_\times$.

analog-Hawking systems. On the BEC platform (Heidelberg), the
dispersive correction is $\delta_{\mathrm{disp}} \approx -7.32\times10^{-5}$
at the natural microscopic point, while the dissipative correction
$\delta_{\mathrm{diss}} \approx 1.59\times10^{-3}$ (opposite sign)
dominates it by a factor $\sim 22$. On the polariton
platform, the corresponding values are $\delta_{\mathrm{disp}} \approx
-19\%$, $\delta_{\mathrm{diss}}$ subdominant.
"""


def _write_F(tmp_path: Path, body: str) -> Path:
    fdir = tmp_path / "F"
    fdir.mkdir(parents=True, exist_ok=True)
    (fdir / "paper_draft.tex").write_text(body, encoding="utf-8")
    return tmp_path


class TestRegistration:
    def test_registered(self):
        assert "f_hierarchy_claims" in {s.name for s in v._CHECKS}

    def test_description_nonempty(self):
        spec = next(s for s in v._CHECKS if s.name == "f_hierarchy_claims")
        assert spec.description.strip()


class TestGatePasses:
    def test_smoke_live_repo(self):
        result = check_f_hierarchy_claims()
        assert result.passed, [(d.name, d.message)
                               for d in result.details if not d.passed]

    def test_passes_on_fixed_synthetic(self, tmp_path, monkeypatch):
        monkeypatch.setattr(_H, "PAPERS_DIR", _write_F(tmp_path, _FIXED_F))
        result = check_f_hierarchy_claims()
        assert result.passed, [(d.name, d.message)
                               for d in result.details if not d.passed]
        assert all(d.passed for d in result.details)


class TestOneWrongValueAloneCarriesTheVerdict:
    """D5 REINFORCEMENT (audit QI-27). `_STALE_F` is stale in four ways at once —
    all three Heidelberg claims plus the crossover — and each fails via the
    *anchor-not-found* path, never via the value comparison. So the value
    comparison's contribution to the verdict was untested.

    Measured 2026-08-04: `all_pass = all_pass and ok` -> `all_pass = all_pass`
    was **MISSED** by the whole file. Every quoted magnitude could have stopped
    affecting the verdict while the tests stayed green — on the flagship paper.

    This corrupts ONE value in the otherwise-correct draft, so the anchor still
    matches and the verdict can only travel through `_rel_ok`.
    """

    def test_a_single_wrong_disp_value_fails(self, tmp_path, monkeypatch):
        body = _FIXED_F.replace(r"-7.32\times10^{-5}", r"-9.99\times10^{-3}")
        assert body != _FIXED_F, "value substitution did not apply"
        monkeypatch.setattr(_H, "PAPERS_DIR", _write_F(tmp_path, body))
        result = check_f_hierarchy_claims()
        assert not result.passed, (
            "a wrong δ_disp value, with the anchor intact and everything else "
            "canonical, did not move the verdict — the value comparison no "
            "longer reaches `all_pass`")
        failed = {d.name for d in result.details if not d.passed}
        assert failed == {"heidelberg.delta_disp.hierarchy"}, (
            f"expected exactly one failing detail, got {sorted(failed)}")

    def test_a_single_wrong_crossover_coefficient_fails(self, tmp_path, monkeypatch):
        body = _FIXED_F.replace(r"\approx 6.44\, T_{\rm eff}", r"\approx 2.00\, T_{\rm eff}")
        assert body != _FIXED_F, "coefficient substitution did not apply"
        monkeypatch.setattr(_H, "PAPERS_DIR", _write_F(tmp_path, body))
        result = check_f_hierarchy_claims()
        assert not result.passed
        assert {d.name for d in result.details if not d.passed} == {"heidelberg.crossover"}


class TestGateFailsOnStale:
    def test_fails_on_stale(self, tmp_path, monkeypatch):
        monkeypatch.setattr(_H, "PAPERS_DIR", _write_F(tmp_path, _STALE_F))
        result = check_f_hierarchy_claims()
        assert not result.passed
        failed = {d.name for d in result.details if not d.passed}
        # every Heidelberg claim + crossover must be caught as stale/missing
        assert "heidelberg.delta_diss.second_order" in failed
        assert "heidelberg.delta_disp.hierarchy" in failed
        assert "heidelberg.delta_diss.hierarchy" in failed
        assert "heidelberg.crossover" in failed

    def test_polariton_not_matched_as_heidelberg(self, tmp_path, monkeypatch):
        # A draft with ONLY the polariton delta_disp claim must not
        # false-positive the Heidelberg hierarchy delta_disp anchor.
        body = (r"the corresponding values are $\delta_{\mathrm{disp}} "
                r"\approx -19\%$, subdominant.")
        monkeypatch.setattr(_H, "PAPERS_DIR", _write_F(tmp_path, body))
        result = check_f_hierarchy_claims()
        # not found -> fails (as expected), but never as a -19% PASS
        assert not result.passed
        disp = next(d for d in result.details
                    if d.name == "heidelberg.delta_disp.hierarchy")
        assert not disp.passed
        assert "not found" in disp.message


def _replace_one(body, old, new):
    assert body.count(old) == 1, (old, body.count(old))
    return body.replace(old, new)


class TestThermalCrossoverContract:
    """R1: numeric proximity must not make mixed thermal/bare scales pass."""

    @pytest.mark.parametrize("old,new,ground", [
        (r"e^{\omega/T_{\rm eff}(\omega)}", r"e^{\omega/T_H}", "heidelberg.planck"),
        (r"\omega_\times = T_{\rm eff}(\omega_\times)",
         r"\omega_\times = T_H", "heidelberg.crossover"),
        (r"\approx 6.44\, T_{\rm eff}(\omega_\times)",
         r"\approx 6.44\, T_H", "heidelberg.crossover"),
        # The true bare coefficient is numerically within the unchanged 0.5%
        # tolerance of the thermal one. The unit, not closeness, must decide.
        (r"\approx 6.44\, T_{\rm eff}(\omega_\times)",
         r"\approx 6.43426\, T_H", "heidelberg.crossover"),
        (r"\kappa_{\rm eff}(\omega)/(2\pi)", r"\kappa/(2\pi)",
         "heidelberg.thermal_scale"),
        (r"$T_H = \kappa/(2\pi)$", r"$T_H = \kappa_{\rm eff}(\omega)/(2\pi)$",
         "heidelberg.bare_scale"),
        ("= \\Gamma_H/\\kappa\n  = \\delta_{\\mathrm{diss}}$",
         "= \\Gamma_H/\\kappa\n  = \\delta_{\\mathrm{diss}}/2$", "heidelberg.noise_floor"),
    ])
    def test_wrong_scale_alone_fails(self, tmp_path, monkeypatch, old, new, ground):
        body = _replace_one(_FIXED_F, old, new)
        monkeypatch.setattr(_H, "PAPERS_DIR", _write_F(tmp_path, body))
        result = check_f_hierarchy_claims()
        assert not result.passed
        assert ground in {d.name for d in result.details if not d.passed}

    def test_wrong_logarithmic_law_fails_even_with_correct_coefficient(self, tmp_path, monkeypatch):
        body = _replace_one(_FIXED_F, r"1 + 1/\delta_{\mathrm{diss}}", r"2/\delta_{\mathrm{diss}}")
        monkeypatch.setattr(_H, "PAPERS_DIR", _write_F(tmp_path, body))
        result = check_f_hierarchy_claims()
        assert not result.passed
        assert "heidelberg.crossover" in {d.name for d in result.details if not d.passed}

    def test_wrong_heading_unit_fails(self, tmp_path, monkeypatch):
        body = _replace_one(_FIXED_F, r"\simeq 6.44\,T_{\rm eff}", r"\simeq 6.44\,T_H")
        monkeypatch.setattr(_H, "PAPERS_DIR", _write_F(tmp_path, body))
        result = check_f_hierarchy_claims()
        assert not result.passed
        assert "heidelberg.crossover_heading" in {d.name for d in result.details if not d.passed}

    def test_wrong_heading_coefficient_alone_fails(self, tmp_path, monkeypatch):
        body = _replace_one(_FIXED_F, r"\simeq 6.44\,T_{\rm eff}", r"\simeq 7.14\,T_{\rm eff}")
        monkeypatch.setattr(_H, "PAPERS_DIR", _write_F(tmp_path, body))
        result = check_f_hierarchy_claims()
        assert not result.passed
        assert {d.name for d in result.details if not d.passed} == {"heidelberg.crossover_heading"}

    def test_correct_law_in_comment_cannot_mask_wrong_live_law(self, tmp_path, monkeypatch):
        good = (r"$\omega_\times = T_{\rm eff}(\omega_\times) "
                r"\ln\!\left(1 + 1/\delta_{\mathrm{diss}}\right) "
                r"\approx 6.44\, T_{\rm eff}(\omega_\times)$")
        body = _replace_one(_FIXED_F, r"\omega_\times = T_{\rm eff}(\omega_\times)",
                            r"\omega_\times = T_H")
        body = body.replace("  therefore\n", "  therefore\n% " + good + "\n")
        assert "% " + good in body
        monkeypatch.setattr(_H, "PAPERS_DIR", _write_F(tmp_path, body))
        assert not check_f_hierarchy_claims().passed

    def test_correct_law_in_another_item_cannot_mask_wrong_floor_item(self, tmp_path, monkeypatch):
        body = _replace_one(_FIXED_F, r"\omega_\times = T_{\rm eff}(\omega_\times)",
                            r"\omega_\times = T_H")
        body += (r"\item Another context: $\omega_\times = T_{\rm eff}(\omega_\times) "
                 r"\ln\!\left(1 + 1/\delta_{\mathrm{diss}}\right) "
                 r"\approx 6.44\, T_{\rm eff}(\omega_\times)$.")
        monkeypatch.setattr(_H, "PAPERS_DIR", _write_F(tmp_path, body))
        assert not check_f_hierarchy_claims().passed

    def test_missing_floor_item_cannot_pass(self, tmp_path, monkeypatch):
        start = _FIXED_F.index(r"\item \textbf{Spectral floor at")
        end = _FIXED_F.index("analog-Hawking systems.", start)
        body = _FIXED_F[:start] + _FIXED_F[end:]
        monkeypatch.setattr(_H, "PAPERS_DIR", _write_F(tmp_path, body))
        assert not check_f_hierarchy_claims().passed

    def test_missing_F_is_not_success(self, tmp_path, monkeypatch):
        monkeypatch.setattr(_H, "PAPERS_DIR", tmp_path)
        result = check_f_hierarchy_claims()
        assert not result.passed
        assert result.error
