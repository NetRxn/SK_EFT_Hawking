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

\item \textbf{Spectral floor at $\omega \sim 7 T_H$ for Heidelberg.}
  The exact-WKB closure produces a spectral-density floor onto which
  the thermal Hawking tail settles once $\exp(-\omega/T_H)$ falls to the
  FDR floor $\delta_{\mathrm{diss}}/2$; for Heidelberg this crossover
  sits at $\omega_\times = T_H \ln(2/\delta_{\mathrm{diss}}) \approx 7.14\, T_H$.

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
        body = _FIXED_F.replace(r"\approx 7.14\, T_H", r"\approx 2.00\, T_H")
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
