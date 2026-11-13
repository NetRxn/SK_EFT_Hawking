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
import json
import os
import re
import subprocess
import sys
from pathlib import Path

import pytest

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
    r"\begin{table*}" "\n"
    r"\label{tab:hierarchy}" "\n"
    r"\begin{tabular}{lcccc}\toprule" "\n"
    r"Platform & $T_H$ & $\delta_\text{disp}$ & $\delta_\text{diss}$ & dominance \\\midrule"
    "\n"
)
TABULAR_TAIL = "\n" r"\bottomrule" "\n" r"\end{tabular}" "\n" r"\end{table*}"


def _write_draft(tmp_path: Path, body: str) -> Path:
    d1 = tmp_path / "D1"
    d1.mkdir(parents=True, exist_ok=True)
    (d1 / "paper_draft.tex").write_text(body, encoding="utf-8")
    return tmp_path


def _generated_draft_body() -> str:
    """A minimal D1 draft whose table + crossover come from the generator."""
    heid = compute_bec_hierarchy()["Heidelberg"]
    diss_tex = fmt_sci_latex(heid["delta_diss"]).strip("$")
    # ⚠️ The coefficient is taken from the evaluator (`omega_cross_over_TH`), never
    # recomputed here and never written as a `ln(...)` shape. A fixture that restates
    # the formula under test proves only that two copies of the same mistake agree —
    # and when fixture, check and draft all carry one formula, the gate reports green
    # on wrong physics and turns RED when someone corrects the paper.
    # The physics: the FDR floor is δ_diss, not δ_diss/2 (the halving is already inside
    # `noise_floor_eq_delta_diss`), so the crossover is `ln(1 + 1/δ_diss)`.
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


_HIERARCHY_LABEL = rb"\label{tab:hierarchy}"
_HIERARCHY_INPUT = rb"\input{tables/platform_hierarchy.tex}"
_HIERARCHY_PROLOGUE = (
    r"\begin{table*}[!t]" "\n"
    r"\centering" "\n"
    r"\caption{Ratios at $\omega=\kappa$ from Eq.~\eqref{eq:{nested}}.}" "\n"
)


def _direct_hierarchy_draft(draft: str, tabular: str, source: str) -> str:
    return (draft.replace(r"\begin{table*}" "\n", _HIERARCHY_PROLOGUE, 1)
            .replace(tabular, source, 1))


class TestHierarchySourceBinding:
    @pytest.mark.parametrize("suffix", ("", ".tex"))
    def test_direct_generated_input_passes(self, tmp_path, monkeypatch, suffix):
        draft = _generated_draft_body()
        tabular = re.search(r"\\begin\{tabular\}.*?\\end\{tabular\}", draft, re.S)
        assert tabular is not None
        source = f"\\input{{tables/platform_hierarchy{suffix}}}"
        root = _write_draft(tmp_path, _direct_hierarchy_draft(draft, tabular[0], source))
        table = root / "D1/tables/platform_hierarchy.tex"
        table.parent.mkdir()
        table.write_text(tabular[0])
        monkeypatch.setattr(_H, "PAPERS_DIR", root)
        result = check_d1_hierarchy_table()
        assert result.passed, result

    @pytest.mark.parametrize("source", (
        r"\include{tables/platform_hierarchy}",
        r"\input{tables/status.tex}",
        r"\input{tables/../tables/platform_hierarchy.tex}",
        r"\input{tables/platform_hierarchy}" "\n" r"\input{tables/platform_hierarchy.tex}",
        r"\input{tables/platform_hierarchy}" "\n" r"\begin{tabular}{l}noise\\\end{tabular}",
        r"% \input{tables/platform_hierarchy}",
    ))
    def test_invalid_binding_cannot_read_a_later_table(self, tmp_path, monkeypatch, source):
        valid = _generated_draft_body()
        tabular = re.search(r"\\begin\{tabular\}.*?\\end\{tabular\}", valid, re.S)
        assert tabular is not None
        tables = tmp_path / "D1/tables"
        tables.mkdir(parents=True)
        for name in ("platform_hierarchy.tex", "status.tex"):
            (tables / name).write_text(tabular[0])
        later = valid.replace(r"\label{tab:hierarchy}", r"\label{tab:other}")
        body = (r"\begin{table}" "\n" r"\label{tab:hierarchy}" "\n"
                + source + "\n" r"\end{table}" "\n" + later)
        monkeypatch.setattr(_H, "PAPERS_DIR", _write_draft(tmp_path, body))
        assert not check_d1_hierarchy_table().passed

    @pytest.mark.parametrize("bad_artifact", (None, r"\input{nested}", "before tabular"))
    def test_missing_or_nonstandalone_generated_table_fails(
            self, tmp_path, monkeypatch, bad_artifact):
        draft = _generated_draft_body()
        tabular = re.search(r"\\begin\{tabular\}.*?\\end\{tabular\}", draft, re.S)
        assert tabular is not None
        root = _write_draft(
            tmp_path, _direct_hierarchy_draft(draft, tabular[0], r"\input{tables/platform_hierarchy}"))
        if bad_artifact is not None:
            table = root / "D1/tables/platform_hierarchy.tex"
            table.parent.mkdir()
            if bad_artifact.startswith(r"\input"):
                table.write_text(tabular[0].replace(r"\end{tabular}",
                                                    bad_artifact + "\n" + r"\end{tabular}"))
            else:
                table.write_text(bad_artifact + "\n" + tabular[0])
        monkeypatch.setattr(_H, "PAPERS_DIR", root)
        result = check_d1_hierarchy_table()
        assert not result.passed
        expected = "cannot read canonical" if bad_artifact is None else "expected one standalone"
        assert expected in result.error

    def test_generated_table_cannot_escape_d1_through_symlink(self, tmp_path, monkeypatch):
        draft = _generated_draft_body()
        tabular = re.search(r"\\begin\{tabular\}.*?\\end\{tabular\}", draft, re.S)
        assert tabular is not None
        root = _write_draft(
            tmp_path, _direct_hierarchy_draft(draft, tabular[0], r"\input{tables/platform_hierarchy}"))
        external = root / "external"
        external.mkdir()
        (external / "platform_hierarchy.tex").write_text(tabular[0])
        (root / "D1/tables").symlink_to(external, target_is_directory=True)
        monkeypatch.setattr(_H, "PAPERS_DIR", root)
        assert not check_d1_hierarchy_table().passed

    @pytest.mark.parametrize(("needle", "replacement"), (
        (_HIERARCHY_INPUT, rb"\iffalse " + _HIERARCHY_INPUT + rb"\fi"),
        (_HIERARCHY_INPUT, rb"\newcommand{\unusedHierarchy}{" + _HIERARCHY_INPUT + b"}"),
        (_HIERARCHY_INPUT, rb"\leavevmode" + b"\\" + _HIERARCHY_INPUT),
        (_HIERARCHY_LABEL + b"\n" + _HIERARCHY_INPUT,
         rb"\iffalse " + _HIERARCHY_LABEL + b"\n" + _HIERARCHY_INPUT + rb"\fi"),
        (_HIERARCHY_LABEL, rb"\expandafter\def\csname input\endcsname#1{}"
         + _HIERARCHY_LABEL),
        (b"for the condensate rows.}", b"for the condensate rows. "
         + rb"\expandafter\def\csname input\endcsname#1{}}"),
        (b"for the condensate rows.}", b"for the condensate rows. "
         b"^^5cexpandafter^^5cdef^^5ccsname input^^5cendcsname#1{}}"),
    ), ids=("post-label-inactive", "post-label-unused-macro", "post-label-escaped",
            "pre-label-inactive", "pre-label-shadow", "caption-shadow",
            "caption-encoded-shadow"))
    def test_live_generated_binding_rejects_inactive_input(self, needle, replacement):
        from seed_journal import seeded_mutation

        draft = _H.PAPERS_DIR / "D1/paper_draft.tex"
        original = draft.read_bytes()
        if _HIERARCHY_INPUT not in original:
            pytest.skip("generated-input control requires the composed table migration")
        assert original.count(needle) == 1
        assert check_d1_hierarchy_table().passed
        with seeded_mutation(draft, original.replace(needle, replacement, 1),
                             reason="D1 generated hierarchy must bind directly"):
            result = check_d1_hierarchy_table()
            assert not result.passed
            assert "expected one direct canonical" in result.error
        assert draft.read_bytes() == original
        assert check_d1_hierarchy_table().passed

    def test_live_hierarchy_cell_mutation_changes_verdict(self):
        from seed_journal import seeded_mutation

        # The same regression test covers the deployed form. The composed
        # candidate consumes the generated file. The inline draft still
        # exercises the existing legacy path.
        draft = _H.PAPERS_DIR / "D1/paper_draft.tex"
        manuscript = draft.read_text()
        target = (draft.parent / "tables/platform_hierarchy.tex"
                  if r"\input{tables/platform_hierarchy" in manuscript else draft)
        original = target.read_bytes()
        assert check_d1_hierarchy_table().passed
        rows = [line for line in original.splitlines()
                if b"Steinhauer/de~Nova" in line and line.count(b"&") == 4]
        assert len(rows) == 1
        cells = rows[0].split(b"&")
        cells[2] = rb" $-9.99\times10^{-3}$ "
        seeded = original.replace(rows[0], b"&".join(cells), 1)
        with seeded_mutation(target, seeded, reason="D1 rendered BEC cell must affect the verdict"):
            result = check_d1_hierarchy_table()
            assert not result.passed
            assert {d.name for d in result.details if not d.passed} == {"Steinhauer.delta_disp"}
        assert target.read_bytes() == original
        assert check_d1_hierarchy_table().passed


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


# Finding 1.1: use the actual occupation producer as an independent numerical
# witness. Repeating log(1 + 1/d) here would let a shared factor-two error pass.
from src.wkb import spectrum as _spectrum  # noqa: E402
from src.wkb.connection_formula import exact_connection_formula  # noqa: E402
from src.wkb.bogoliubov import modified_bogoliubov_coefficients  # noqa: E402

_BEC_FACTORIES = {
    "Steinhauer": _spectrum.steinhauer_platform,
    "Heidelberg": _spectrum.heidelberg_platform,
    "Trento": _spectrum.trento_platform,
}


def _occupation(platform, omega):
    conn = exact_connection_formula(
        omega, platform.kappa, platform.c_s, platform.xi,
        platform.gamma_1, platform.gamma_2,
        platform.gamma_2_1, platform.gamma_2_2,
        platform.gamma_3_1, platform.gamma_3_2, platform.gamma_3_3,
    )
    return conn, modified_bogoliubov_coefficients(conn, T_env=0.0)


def _physical_crossing(platform):
    """Bracket the actual Hawking/floor equality, without a logarithmic formula."""
    lo, hi = 0.1 * platform.T_H, 20.0 * platform.T_H
    assert _occupation(platform, lo)[1].n_hawking > _occupation(platform, lo)[1].n_noise
    assert _occupation(platform, hi)[1].n_hawking < _occupation(platform, hi)[1].n_noise
    for _ in range(60):
        mid = (lo + hi) / 2
        _, bog = _occupation(platform, mid)
        if bog.n_hawking > bog.n_noise:
            lo = mid
        else:
            hi = mid
    omega = (lo + hi) / 2
    conn, bog = _occupation(platform, omega)
    return omega, conn, bog


def _generator_cli(*flags):
    env = dict(os.environ, PYTHONPATH=str(SK_ROOT), PYTHONDONTWRITEBYTECODE="1")
    result = subprocess.run(
        [sys.executable, "-B", str(SK_ROOT / "scripts/gen_d1_hierarchy_table.py"), *flags],
        cwd=SK_ROOT, env=env, capture_output=True, text=True, timeout=30,
    )
    assert result.returncode == 0, (result.returncode, result.stdout, result.stderr)
    return result.stdout


class TestFinding11PhysicalContract:
    @pytest.mark.parametrize("name", _BEC_FACTORIES)
    def test_actual_occupation_crosses_reported_floor_at_reported_coefficient(self, name):
        platform = _BEC_FACTORIES[name]()
        row = compute_bec_hierarchy()[name]
        omega, conn, bog = _physical_crossing(platform)
        thermal_temperature = conn.kappa_eff.kappa_eff / (2 * math.pi)
        assert conn.uv_suppression == 1.0
        assert 0 < bog.delta_k < 1
        assert math.isclose(row["spectral_floor"], bog.n_noise, rel_tol=1e-12)
        assert math.isclose(bog.n_noise, conn.turning_point.Gamma_H / platform.kappa,
                            rel_tol=1e-12)
        assert math.isclose(bog.n_hawking, bog.n_noise, rel_tol=1e-12)
        assert math.isclose(row["omega_cross_over_TH"], omega / thermal_temperature,
                            rel_tol=1e-12)
        assert row["ln_arg"] == row["omega_cross_over_TH"]
        # Nominal T_H and the temperature fitted to TOTAL occupation are each
        # different from the thermal temperature entering the Planck component.
        assert not math.isclose(thermal_temperature, platform.T_H, rel_tol=1e-8)
        assert not math.isclose(thermal_temperature, bog.T_eff, rel_tol=1e-8)
        assert row["cross_below_cutoff"] == (omega < platform.omega_max)
        assert _occupation(platform, 0.99 * omega)[1].n_hawking > bog.n_noise
        assert _occupation(platform, 1.01 * omega)[1].n_hawking < bog.n_noise

    def test_json_cli_is_complete_and_preserves_numeric_schema(self):
        rows = json.loads(_generator_cli("--json"))
        assert set(rows) == set(_BEC_FACTORIES)
        assert rows == compute_bec_hierarchy()
        for row in rows.values():
            assert type(row["cross_below_cutoff"]) is bool
            assert all(math.isfinite(row[key]) for key in (
                "D", "delta_disp", "delta_diss", "ratio", "ln_arg",
                "omega_cross_over_TH", "omega_max_over_TH", "spectral_floor"))

    def test_human_cli_reports_all_platforms_with_correct_thermal_units(self):
        text = _generator_cli()
        header = text.splitlines()[0]
        assert "wx/T_eff" in header and "wmax/T_H" in header
        assert "T_eff = kappa_eff(omega_x)/(2*pi)" in text
        assert "T_H = kappa/(2*pi)" in text
        rows = compute_bec_hierarchy()
        for name, row in rows.items():
            line = next(line for line in text.splitlines() if line.startswith(name + " "))
            cells = line.split()
            assert math.isclose(float(cells[6]), row["omega_cross_over_TH"], rel_tol=1e-5)
            assert math.isclose(float(cells[8]), row["spectral_floor"], rel_tol=1e-4)
            sentence = next(line for line in text.splitlines() if line.startswith("  " + name + ":"))
            assert "omega_x = T_eff ln(1+1/delta_diss)" in sentence
            coefficient = re.search(r"~ ([0-9.]+) T_eff", sentence)
            assert coefficient
            assert math.isclose(float(coefficient[1]), row["omega_cross_over_TH"], rel_tol=0.0008)

    def test_latex_cli_preserves_all_platform_corrections_and_nominal_labels(self):
        text = _generator_cli("--latex")
        assert len(text.splitlines()) == len(_BEC_FACTORIES)
        for name, row in compute_bec_hierarchy().items():
            cells = next(line for line in text.splitlines() if name in line).split("&")
            assert cells[1].strip() == row["T_H_nominal_label"]
            for idx, key in ((2, "delta_disp"), (3, "delta_diss")):
                assert math.isclose(_parse_latex_number(cells[idx]), row[key], rel_tol=0.005)

    def test_manuscript_all_platform_floor_crossover_and_scale_context(self):
        text = (SK_ROOT / "papers/D1/paper_draft.tex").read_text()
        # Bound the scientific comparison to the hierarchy's explicit platform
        # sequence; the existing live gate independently checks all table cells.
        section = text.split(r"\label{sec:hier-heidelberg}", 1)[1].split(r"\subsection", 1)[0]
        comparison = section.split("All three sit", 1)[0]
        coefficients = re.findall(r"([\d.]+)\\,T_\{\\rm eff\}", comparison)
        assert len(coefficients) == 3
        floors = re.findall(r"([\d.]+)\\times10\^\{(-?\d+)\}", section)
        assert len(floors) == 3
        for name, coefficient, floor in zip(
                ("Heidelberg", "Steinhauer", "Trento"), coefficients, floors, strict=True):
            row = compute_bec_hierarchy()[name]
            assert math.isclose(float(coefficient), row["omega_cross_over_TH"], rel_tol=0.0008)
            assert math.isclose(float(floor[0]) * 10 ** int(floor[1]), row["spectral_floor"], rel_tol=0.005)
        # Also check every repeated numeric crossover in the actual abstract,
        # crossover section and conclusion, rather than only the table vicinity.
        all_coefficients = re.findall(r"([\d.]+)\\,T_\{\\rm eff\}", text)
        assert len(all_coefficients) >= 3
        expected = [row["omega_cross_over_TH"] for row in compute_bec_hierarchy().values()]
        assert all(any(math.isclose(float(c), want, rel_tol=0.0008) for want in expected)
                   for c in all_coefficients)
        abstract = text.split(r"\begin{abstract}", 1)[1].split(r"\end{abstract}", 1)[0]
        crossover_section = text.split(r"\label{sec:wkb-crossover}", 1)[1].split(r"\figuredeferred", 1)[0]
        conclusion = text.split("The condensate delivers the crossover frequency", 1)[1].split(
            "The Dirac fluid delivers", 1)[0]
        for context, names in ((abstract, ("Heidelberg", "Steinhauer")),
                               (crossover_section, ("Heidelberg", "Steinhauer")),
                               (conclusion, ("Heidelberg",))):
            claims = re.findall(r"([\d.]+)\\,T_\{\\rm eff\}", context)
            assert len(claims) == len(names), "missing or wrong-unit crossover claim"
            for coefficient, name in zip(claims, names, strict=True):
                assert math.isclose(float(coefficient), compute_bec_hierarchy()[name]["omega_cross_over_TH"],
                                    rel_tol=0.0008)
        cutoffs = re.search(
            r"\\omega_\{\\rm max\} = ([\d.]+)\\,T_H\$, \$([\d.]+)\\,T_H\$ and \$([\d.]+)\\,T_H",
            section)
        assert cutoffs, "missing bare-T_H cutoff comparison"
        for name, cutoff in zip(("Heidelberg", "Steinhauer", "Trento"), cutoffs.groups(), strict=True):
            platform = _BEC_FACTORIES[name]()
            assert math.isclose(float(cutoff), platform.omega_max / platform.T_H, rel_tol=0.005)
        assert check_d1_hierarchy_table().passed

    def test_charter_binds_each_crossover_to_its_platform_and_thermal_scale(self):
        text = (SK_ROOT / "docs/PAPER_STRATEGY.md").read_text()
        d1_content = next(line for line in text.splitlines()
                          if line.startswith("Content: SK-EFT corrections"))
        for name, row in compute_bec_hierarchy().items():
            claim = re.search(r"" + name + r"[^;()]*?([\d.]+) T_eff", d1_content)
            assert claim, f"missing platform-specific thermal crossover: {name}"
            assert math.isclose(float(claim[1]), row["omega_cross_over_TH"], rel_tol=0.0008)
        assert "T_eff = kappa_eff(omega_x)/(2*pi)" in d1_content
        assert "T_H = kappa/(2*pi)" in d1_content
