"""Tests for the ``d1_hierarchy_table`` validate.py gate (finding B-01).

The gate parses D1's rendered BEC correction-hierarchy table and the
numeric spectral-floor crossover sentences from
``papers/D1/paper_draft.tex`` and compares every value against the single
canonical evaluator ``scripts/gen_d1_hierarchy_table.compute_bec_hierarchy``
within 0.5 % relative tolerance.

Coverage:
    - registration + description
    - the ``_parse_latex_number`` core (scientific, pure-power, percent,
      unparseable) — the discriminator that makes stale *formats* fail
    - PASS on a draft rendered by the generator (round-trip, drift-proof)
    - PASS smoke against the live repo
    - FAIL on a synthetic draft carrying the historical stale magnitudes
      (δ_disp −2.7 %, δ_diss 26 %/10⁻¹/10⁻⁵, crossover ≈ 2.0 T_H)
    - generator idempotency
"""
from __future__ import annotations

import math
import sys
from pathlib import Path

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT))
sys.path.insert(0, str(SK_ROOT / "scripts"))

import validate as v
import validate_helpers as _H  # noqa: E402
from validate import _parse_latex_number, check_d1_hierarchy_table  # noqa: E402
from scripts.gen_d1_hierarchy_table import (  # noqa: E402
    compute_bec_hierarchy,
    fmt_sci_latex,
    render_latex_rows,
)


TABULAR_HEAD = (
    r"\label{tab:hierarchy}" "\n"
    r"\begin{tabular}{lcccc}\toprule" "\n"
    r"Platform & $T_H$ & $\delta_\text{disp}$ & $\delta_\text{diss}$ & dominance \\\midrule"
    "\n"
)
TABULAR_TAIL = "\n" r"\bottomrule" "\n" r"\end{tabular}"


def _write_draft(tmp_path: Path, body: str) -> Path:
    d1 = tmp_path / "D1"
    d1.mkdir(parents=True, exist_ok=True)
    (d1 / "paper_draft.tex").write_text(body, encoding="utf-8")
    return tmp_path


def _generated_draft_body() -> str:
    """A minimal D1 draft whose table + crossover come from the generator."""
    heid = compute_bec_hierarchy()["Heidelberg"]
    diss_tex = fmt_sci_latex(heid["delta_diss"]).strip("$")
    # ⚠️ This fixture previously emitted `ω_× ≈ T_H ln(2/X) ≈ Y T_H`, matching a
    # check that required that shape. Both encoded the WRONG physics: the FDR
    # floor is δ_diss, not δ_diss/2 (the halving is inside
    # `noise_floor_eq_delta_diss`), so the crossover is `ln(1 + 1/δ_diss)` and
    # the old form ran high by exactly ln 2. Because the fixture, the check and
    # the draft all agreed with each other, the gate was green while the physics
    # was wrong — and correcting the paper would have turned it red. Three
    # Stage-13 passes flagged the discrepancy and none could close it.
    #
    # The coefficient is taken from the evaluator (`omega_cross_over_TH`), never
    # recomputed here: a fixture that restates the formula under test proves only
    # that two copies of the same mistake agree.
    crossover = (
        r"$\delta_{\rm diss} = " + diss_tex + r"$ gives "
        r"$\omega_\times \simeq " + f"{heid['omega_cross_over_TH']:.2f}"
        + r"\,T_{\rm eff}$"
    )
    return (
        TABULAR_HEAD + render_latex_rows() + TABULAR_TAIL
        + "\n\nSpectral floor. " + crossover + "\n"
    )


# ── historical stale draft (exactly what B-01 flagged) ──────────────────
_STALE_BODY = (
    TABULAR_HEAD
    + r"$^{87}$Rb BEC (Steinhauer/de~Nova) & $\sim 0.35$\,nK & $-2.7\%$ & $10^{-5}$ & disp \\"
    + "\n"
    + r"$^{39}$K BEC (Heidelberg, projected) & $\sim 1$\,nK & $-1.2\%$ & $\sim 26\%$ & \textbf{diss} \\"
    + "\n"
    + r"spin-sonic BEC (Trento)    & $\sim 1$\,nK & $-0.5\%$ & $10^{-1}$ & comparable \\"
    + TABULAR_TAIL
    + "\n\n" + r"$\omega_\times \approx T_H \ln(2/0.26) \approx 2.0\, T_H$" + "\n"
)


class TestRegistration:
    def test_registered(self):
        names = {spec.name for spec in v._CHECKS}
        assert "d1_hierarchy_table" in names

    def test_description_nonempty(self):
        spec = next(s for s in v._CHECKS if s.name == "d1_hierarchy_table")
        assert spec.description.strip()


class TestParseLatexNumber:
    def test_scientific(self):
        assert _parse_latex_number(r"$-8.53\times10^{-5}$") == -8.53e-5
        assert _parse_latex_number(r"$1.59\times10^{-3}$") == 1.59e-3

    def test_pure_power(self):
        assert _parse_latex_number(r"$10^{-5}$") == 1e-5
        assert _parse_latex_number(r"$10^{-1}$") == 0.1

    def test_percent(self):
        assert math.isclose(_parse_latex_number(r"$-2.7\%$"), -0.027, rel_tol=1e-9)
        assert math.isclose(_parse_latex_number(r"$\sim 26\%$"), 0.26, rel_tol=1e-9)

    def test_unparseable(self):
        assert _parse_latex_number(r"$\delta_\text{diss}$") is None
        assert _parse_latex_number("disp") is None


class TestGatePasses:
    def test_passes_on_generated_draft(self, tmp_path, monkeypatch):
        root = _write_draft(tmp_path, _generated_draft_body())
        monkeypatch.setattr(_H, "PAPERS_DIR", root)
        result = check_d1_hierarchy_table()
        assert result.passed, [d for d in result.details if not d.passed]
        # every sub-detail green
        assert all(d.passed for d in result.details)

    def test_smoke_live_repo(self):
        result = check_d1_hierarchy_table()
        assert result.passed, [(d.name, d.message)
                               for d in result.details if not d.passed]


class TestGateFailsOnStale:
    def test_fails_on_stale_draft(self, tmp_path, monkeypatch):
        root = _write_draft(tmp_path, _STALE_BODY)
        monkeypatch.setattr(_H, "PAPERS_DIR", root)
        result = check_d1_hierarchy_table()
        assert not result.passed
        failed = {d.name for d in result.details if not d.passed}
        # the three BEC magnitude columns must all be caught
        assert "Steinhauer.delta_disp" in failed
        assert "Heidelberg.delta_diss" in failed
        assert "Trento.delta_diss" in failed
        # the flipped Trento dominance label must be caught
        assert "Trento.dominance" in failed
        # the stale crossover (X=0.26 matches no δ_diss) must be caught
        assert any(n.startswith("crossover") for n in failed)


def _corrupt_cell(body: str, platform: str, idx: int, new: str) -> str:
    """Replace exactly one `&`-separated cell of one platform's table row.

    The point is ISOLATION: everything else in the draft stays canonical, so the
    verdict can only move through the cell being corrupted.
    """
    out = []
    for chunk in body.split(r"\\"):
        if platform in chunk and "&" in chunk:
            cells = chunk.split("&")
            cells[idx] = f" {new} "
            chunk = "&".join(cells)
        out.append(chunk)
    return r"\\".join(out)


class TestEachFailureGroundCarriesTheVerdictAlone:
    """D5 REINFORCEMENT (audit QI-27). `TestGateFailsOnStale` above uses the
    historical stale draft, which is wrong in FOUR independent ways at once —
    magnitudes, dominance label, and crossover. That makes it a good regression
    fixture and a poor mutation target: killing any single ground's contribution
    to `all_pass` leaves the verdict `False` via the other three.

    Measured 2026-08-04: `all_pass = all_pass and ok` -> `all_pass = all_pass`
    was **MISSED** by the whole file, in both the table loop and the crossover
    loop. The magnitude comparisons could have stopped affecting the verdict
    entirely while every test stayed green.

    Each test below corrupts exactly ONE thing in an otherwise-canonical draft,
    so the verdict has a single path to travel and the mutation is load-bearing.
    """

    def test_a_wrong_magnitude_alone_fails(self, tmp_path, monkeypatch):
        body = _corrupt_cell(_generated_draft_body(), "Steinhauer", 2,
                             r"$-9.99\times10^{-3}$")
        monkeypatch.setattr(_H, "PAPERS_DIR", _write_draft(tmp_path, body))
        result = check_d1_hierarchy_table()
        assert not result.passed, (
            "a wrong δ_disp magnitude, with everything else canonical, did not "
            "move the verdict — the table comparison no longer reaches `all_pass`")
        failed = {d.name for d in result.details if not d.passed}
        assert failed == {"Steinhauer.delta_disp"}, (
            f"expected exactly one failing detail, got {sorted(failed)} — the "
            f"fixture is no longer isolating a single ground")

    def test_a_wrong_crossover_coefficient_alone_fails(self, tmp_path, monkeypatch):
        """Only the quoted `Y` in `≈ Y T_H` is wrong; the ln-argument still
        matches a canonical δ_diss, so `crossover[i].delta_diss_match` passes and
        the verdict must travel through the coefficient comparison alone."""
        heid = compute_bec_hierarchy()["Heidelberg"]
        diss_tex = fmt_sci_latex(heid["delta_diss"]).strip("$")
        # Seeds the defect in the CURRENT sentence form. The δ_diss is left
        # canonical so `delta_diss_match` stays green and the verdict has to
        # travel through the coefficient comparison alone; only the quoted
        # coefficient is corrupted.
        good = (r"$\omega_\times \simeq "
                + f"{heid['omega_cross_over_TH']:.2f}" + r"\,T_{\rm eff}$")
        bad = (r"$\omega_\times \simeq "
               + f"{heid['omega_cross_over_TH'] * 2:.2f}" + r"\,T_{\rm eff}$")
        body = _generated_draft_body().replace(good, bad)
        assert body != _generated_draft_body(), "crossover substitution did not apply"
        monkeypatch.setattr(_H, "PAPERS_DIR", _write_draft(tmp_path, body))
        result = check_d1_hierarchy_table()
        assert not result.passed, (
            "a wrong crossover coefficient alone did not move the verdict")
        failed = {d.name for d in result.details if not d.passed}
        assert failed == {"crossover[0].coefficient"}, sorted(failed)


class TestGenerator:
    def test_idempotent(self):
        assert compute_bec_hierarchy() == compute_bec_hierarchy()

    def test_horizon_values_match_expected(self):
        h = compute_bec_hierarchy()
        # Heidelberg is the sole dissipation-dominated platform
        assert h["Heidelberg"]["dominance"] == "diss"
        assert h["Steinhauer"]["dominance"] == "disp"
        assert h["Trento"]["dominance"] == "disp"
        # ratio survives at ~22
        assert math.isclose(h["Heidelberg"]["ratio"], 21.76, rel_tol=1e-2)
        # all three crossovers sit below the dispersive UV cutoff
        for name in ("Steinhauer", "Heidelberg", "Trento"):
            assert h[name]["cross_below_cutoff"]
