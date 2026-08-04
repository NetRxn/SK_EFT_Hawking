"""Physics and paper-numeric checks — ADR-009 Phase 2.

Experimental-parameter agreement, formula identities, physical bounds,
cross-path agreement between modules, the CGL FDR derivation, the D1/F BEC
hierarchy tables against their canonical evaluator, and the quantum-network
Python ↔ Lean cross-validation.

MOVED VERBATIM from `scripts/validate.py` — extracted by script from AST-verified
line ranges, not retyped. No body edited, no policy unified, no threshold
retuned (ADR-009 D4: Phases 1-2 are provably behaviour-preserving or they are
nothing).

SIX OF THIS MODULE'S NAMES ARE IN THE FROZEN EXTERNAL SURFACE
--------------------------------------------------------------
`check_numerical_consistency`, `check_formula_identities`,
`check_paper_table_consistency`, `check_d1_hierarchy_table`,
`check_f_hierarchy_claims` and `_parse_latex_number` are imported BY NAME from
`validate` by `tests/test_cross_validation.py`, `test_d1_hierarchy_table.py` and
`test_f_hierarchy_claims.py`. `validate` therefore re-exports them; see ADR-009
D2 item 8 and `tests/test_validate_public_surface.py`, which freezes the list.

Import rules (identical in every module here — see `checks/notebooks.py`):
framework from `validation._registry`; paths from `validate_helpers`, NEVER from
`__file__` (it resolves to `scripts/validation/checks/`, so `parent.parent` is
`scripts/validation` and every lookup silently misses — H1); runtime flags by
attribute on `validation._config`. No check in this module reads a flag.

Execution order is owned by `validate._CANONICAL_ORDER`, not by where this module
sits in any import list (H3).
"""
from __future__ import annotations

from typing import List

import validate_helpers as _H
from validation._registry import CheckResult, Detail, register_check

# ⚠️ NO LOCAL PATH ALIASES IN A CHECK MODULE. `_H.PAPERS_DIR = _H.PAPERS_DIR` binds a
# COPY at import time — the same shape as `from validate import STRICT_MODE`, which
# H5 forbids for flags. Paths are never reassigned in production, so the copy is
# harmless there; it is NOT harmless for the tests that monkeypatch a temp tree to
# seed a defect. `test_f_hierarchy_claims` patches `_H.PAPERS_DIR` and asserts the check
# FAILS on a stale draft — against a local alias the patch does not reach the check,
# the real (correct) draft is read, and the test passes while its seeded defect is
# never seen. It only failed loudly here because it asserts `not passed`; a positive
# control would have gone silently vacuous.
#
# So: reach `_H.<NAME>` at each use. One owner, resolved at call time, patchable in
# exactly one place. Enforced by
# `test_validate_public_surface.py::test_no_check_module_aliases_a_path`.


# ═══════════════════════════════════════════════════════════════════════
# CHECK 2: Numerical consistency
# ═══════════════════════════════════════════════════════════════════════

@register_check("numerical", "Experimental parameters match reference values")
def check_numerical_consistency() -> CheckResult:
    from src.core.constants import get_all_experiments, HBAR

    expected = {
        'Steinhauer': {'c_s': 5.476e-4, 'xi': 1.334e-6, 'kappa': 4.8, 'T_H': 5.78e-12},
        'Heidelberg': {'c_s': 3.919e-3, 'xi': 4.159e-7, 'kappa': 101.9, 'T_H': 1.24e-10},
        'Trento':     {'c_s': 2.185e-3, 'xi': 1.264e-6, 'kappa': 21.4, 'T_H': 2.6e-11},
    }

    tolerance = 0.05
    details = []
    all_pass = True

    try:
        experiments = get_all_experiments()
    except Exception as e:
        return CheckResult(passed=False, error=str(e))

    for name, (params, bg) in experiments.items():
        if name not in expected:
            continue

        actuals = {
            'c_s': params.sound_speed_upstream,
            'xi': params.healing_length,
            'kappa': bg.surface_gravity,
            'T_H': bg.hawking_temp,
        }

        for param, exp_val in expected[name].items():
            actual = actuals[param]
            rel_err = abs(actual - exp_val) / abs(exp_val)
            ok = rel_err <= tolerance
            details.append(Detail(
                f"{name}.{param}",
                ok,
                f"expected={exp_val:.3e}, actual={actual:.3e}, err={rel_err*100:.1f}%"
            ))
            if not ok:
                all_pass = False

    return CheckResult(passed=all_pass, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 3: Formula identities
# ═══════════════════════════════════════════════════════════════════════

@register_check("identities", "Mathematical identities and boundary conditions hold")
def check_formula_identities() -> CheckResult:
    from src.core import formulas

    details = []
    all_pass = True

    tests = [
        ("count(1)==2", lambda: formulas.count_coefficients(1) == 2),
        ("count(2)==2", lambda: formulas.count_coefficients(2) == 2),
        ("count(3)==3", lambda: formulas.count_coefficients(3) == 3),
        ("disp(0)==0", lambda: formulas.dispersive_correction(0) == 0),
        ("1st_order(0,kappa)==0", lambda: formulas.first_order_correction(0, 1.0) == 0),
        ("Gamma(k,w,cs,0,0,0,0)==0", lambda: formulas.damping_rate(1.0, 2.0, 0.5, 0, 0, 0, 0) == 0),
    ]

    for name, fn in tests:
        try:
            ok = fn()
            details.append(Detail(name, ok))
            if not ok:
                all_pass = False
        except Exception as e:
            details.append(Detail(name, False, str(e)))
            all_pass = False

    # Acoustic-mode vanishing: k=w/cs with gamma_22=-gamma_21
    try:
        c_s, omega, kappa = 1.0, 100.0, 50.0
        k = omega / c_s
        g21 = 0.5
        result = formulas.second_order_correction(k, omega, c_s, g21, -g21, kappa)
        ok = abs(result) < 1e-10
        details.append(Detail("delta2_acoustic_vanishes", ok, f"value={result:.3e}"))
        if not ok:
            all_pass = False
    except Exception as e:
        details.append(Detail("delta2_acoustic_vanishes", False, str(e)))
        all_pass = False

    return CheckResult(passed=all_pass, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 4: Paper 1 Table 1 consistency
# ═══════════════════════════════════════════════════════════════════════

@register_check("paper_table", "Paper 1 Table 1 values match solver output")
def check_paper_table_consistency() -> CheckResult:
    from src.core.constants import get_all_experiments

    paper_path = _H.PAPERS_DIR / "paper1_first_order" / "paper_draft.tex"
    if not paper_path.exists():
        return CheckResult(passed=False, error=f"Paper not found: {paper_path}")

    # Reference values from the corrected table (solver output)
    # NOTE: Steinhauer kappa/T_H here are MODEL values (tanh profile).
    # Published values (kappa=290, T_H=0.35nK) come from the actual
    # step potential, not our smooth model. See backreaction.py steinhauer_si().
    paper_table = {
        'Steinhauer': {'c_s': 5.476e-4, 'xi': 1.334e-6, 'kappa': 4.8, 'T_H': 0.006e-9},
        'Heidelberg': {'c_s': 3.919e-3, 'xi': 4.159e-7, 'kappa': 101.9, 'T_H': 0.124e-9},
        'Trento':     {'c_s': 2.185e-3, 'xi': 1.264e-6, 'kappa': 21.4, 'T_H': 0.026e-9},
    }

    tolerance = 0.05
    details = []
    all_pass = True

    try:
        experiments = get_all_experiments()
    except Exception as e:
        return CheckResult(passed=False, error=str(e))

    for name, paper_vals in paper_table.items():
        if name not in experiments:
            continue
        params, bg = experiments[name]
        actuals = {
            'c_s': params.sound_speed_upstream,
            'xi': params.healing_length,
            'kappa': bg.surface_gravity,
            'T_H': bg.hawking_temp,
        }
        for param, pval in paper_vals.items():
            actual = actuals[param]
            rel_err = abs(actual - pval) / abs(pval)
            ok = rel_err <= tolerance
            details.append(Detail(f"{name}.{param}", ok,
                                  f"paper={pval:.3e}, code={actual:.3e}"))
            if not ok:
                all_pass = False

    return CheckResult(passed=all_pass, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 4b: D1 hierarchy table + crossover ↔ canonical evaluator (finding B-01)
# ═══════════════════════════════════════════════════════════════════════

def _parse_latex_number(cell: str):
    """Parse a LaTeX numeric table/prose cell into a float, or None.

    Handles the forms that appear in D1's hierarchy table and crossover
    sentences, so the check FAILS on the stale hand-authored formats
    (``$-2.7\\%$``, ``$\\sim 26\\%$``, ``$10^{-1}$``) as well as on wrong
    scientific-notation values:

        ``$-8.53\\times10^{-5}$``  -> -8.53e-5
        ``$1.41\\times10^{-5}$``   -> 1.41e-5
        ``$10^{-5}$``              -> 1e-5
        ``$-2.7\\%$`` / ``$\\sim 26\\%$``  -> -0.027 / 0.26
        bare float / ``1.59\\times10^{-3}`` (no ``$``)
    """
    import re as _re
    s = cell.strip()
    s = s.replace("\\textbf{", "").rstrip("}")
    s = s.replace("$", "").replace("\\sim", "").replace("\\approx", "").strip()
    # mantissa × 10^{exp}
    m = _re.search(r"(-?\d+\.?\d*)\s*\\times\s*10\^\{?(-?\d+)\}?", s)
    if m:
        return float(m.group(1)) * 10.0 ** int(m.group(2))
    # pure power ±10^{exp}
    m = _re.fullmatch(r"(-?)10\^\{?(-?\d+)\}?", s)
    if m:
        return (-1.0 if m.group(1) == "-" else 1.0) * 10.0 ** int(m.group(2))
    # percentage
    m = _re.match(r"(-?\d+\.?\d*)\s*\\%", s)
    if m:
        return float(m.group(1)) / 100.0
    try:
        return float(s)
    except ValueError:
        return None


@register_check("d1_hierarchy_table",
                "D1 BEC hierarchy table + crossover match the canonical evaluator")
def check_d1_hierarchy_table() -> CheckResult:
    """Parse D1's rendered hierarchy table (three BEC rows) and the
    spectral-floor crossover sentences from ``papers/D1/paper_draft.tex``
    and compare every numeric against the SINGLE canonical evaluator
    ``scripts/gen_d1_hierarchy_table.compute_bec_hierarchy()`` within a
    declared 0.5 % relative tolerance (the table cells carry 3 significant
    figures, so 3-sig-fig rounding is < 0.5 %).

    Closes finding B-01. The pre-existing ``paper_provenance`` /
    ``paper_table`` checks parse no D1 numerics, so the stale
    hand-authored magnitudes (δ_disp −2.7/−1.2/−0.5 %, δ_diss
    26 %/10⁻¹/10⁻⁵, crossover ≈ 2.0 T_H) were never caught. This check
    FAILS on those (wrong value *and* wrong format) and PASSES only once
    the rows are regenerated from the pipeline.
    """
    import re as _re
    import math as _math

    paper_path = _H.PAPERS_DIR / "D1" / "paper_draft.tex"
    if not paper_path.exists():
        return CheckResult(passed=False, error=f"Paper not found: {paper_path}")

    try:
        from scripts.gen_d1_hierarchy_table import compute_bec_hierarchy
    except Exception as e:  # pragma: no cover - import guard
        return CheckResult(passed=False, error=f"cannot import evaluator: {e}")

    hier = compute_bec_hierarchy()
    text = paper_path.read_text(encoding="utf-8")
    TOL = 0.005  # 0.5 % relative

    details: List[Detail] = []
    all_pass = True

    def _rel_ok(got, want) -> tuple:
        if got is None:
            return False, "unparseable / wrong format"
        if want == 0:
            return abs(got) <= TOL, f"paper={got:.4g}, canon=0"
        rel = abs(got - want) / abs(want)
        return rel <= TOL, f"paper={got:.4g}, canon={want:.4g}, rel={rel:.2%}"

    # --- (1) The three BEC table rows -----------------------------------
    tbl = _re.search(
        r"\\label\{tab:hierarchy\}.*?\\begin\{tabular\}(.*?)\\end\{tabular\}",
        text, _re.DOTALL)
    if not tbl:
        return CheckResult(passed=False,
                           error="tab:hierarchy tabular block not found in D1 draft")
    body = tbl.group(1)
    rows = [r for r in body.split(r"\\") if "&" in r]

    for plat in ("Steinhauer", "Heidelberg", "Trento"):
        canon = hier[plat]
        row = next((r for r in rows
                    if _re.search(r"^[^&]*" + plat, r.strip())), None)
        if row is None:
            details.append(Detail(f"{plat}.row", False, "table row not found"))
            all_pass = False
            continue
        cells = [c.strip() for c in row.split("&")]
        if len(cells) < 5:
            details.append(Detail(f"{plat}.row", False,
                                  f"expected 5 cells, got {len(cells)}"))
            all_pass = False
            continue
        # cells: [label, T_H, delta_disp, delta_diss, dominance]
        for idx, key in ((2, "delta_disp"), (3, "delta_diss")):
            ok, msg = _rel_ok(_parse_latex_number(cells[idx]), canon[key])
            details.append(Detail(f"{plat}.{key}", ok, msg))
            all_pass = all_pass and ok
        dom_cell = cells[4].replace("\\textbf{", "").replace("}", "").strip()
        dom_ok = dom_cell.startswith(canon["dominance"])
        details.append(Detail(f"{plat}.dominance", dom_ok,
                              f"paper={dom_cell!r}, canon={canon['dominance']!r}"))
        all_pass = all_pass and dom_ok

    # --- (2) Numeric crossover sentences ω_× ≈ T_H ln(2/X) ≈ Y T_H -------
    # Only the *numeric* sentences match (the symbolic abstract/display
    # forms use `=`, `\;\approx\;` or `\cdot` and are excluded by shape).
    cross_re = _re.compile(
        r"\\omega_\\times\s*\\approx\s*T_H\s*\\ln\(2/([^)]+)\)\s*"
        r"\\approx\s*([\d.]+)\\,\s*T_H", _re.DOTALL)
    matches = list(cross_re.finditer(text))
    if not matches:
        details.append(Detail("crossover.present", False,
                              "no numeric ω_× ≈ T_H ln(2/X) ≈ Y T_H sentence found"))
        all_pass = False
    diss_values = [h["delta_diss"] for h in hier.values()]
    for i, m in enumerate(matches):
        X = _parse_latex_number(m.group(1))
        Y = float(m.group(2))
        # (a) the ln-argument X must be one of the canonical δ_diss values
        if X is None:
            details.append(Detail(f"crossover[{i}].arg", False,
                                  f"unparseable ln argument {m.group(1)!r}"))
            all_pass = False
            continue
        best = min((abs(X - d) / abs(d)) for d in diss_values)
        arg_ok = best <= TOL
        details.append(Detail(f"crossover[{i}].delta_diss_match", arg_ok,
                              f"ln-arg={X:.4g}, nearest canon δ_diss rel={best:.2%}"))
        # (b) the quoted coefficient Y must equal ln(2/X)
        y_ok, y_msg = _rel_ok(Y, _math.log(2.0 / X))
        details.append(Detail(f"crossover[{i}].coefficient", y_ok, y_msg))
        all_pass = all_pass and arg_ok and y_ok

    return CheckResult(passed=all_pass, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 4c: Flagship (F) inline BEC hierarchy claims ↔ canonical evaluator
# ═══════════════════════════════════════════════════════════════════════

@register_check("f_hierarchy_claims",
                "Flagship F inline Heidelberg BEC corrections match the canonical evaluator")
def check_f_hierarchy_claims() -> CheckResult:
    """Sibling of ``d1_hierarchy_table`` for the flagship ``papers/F``.

    F quotes the BEC corrections inline (prose), not as a table, so this
    check targets the specific Heidelberg sentences by anchored regex and
    compares each quoted value against the SAME canonical evaluator
    ``scripts/gen_d1_hierarchy_table.compute_bec_hierarchy()`` (Heidelberg
    row) within 0.5 % relative. Each claim is REQUIRED to be present in the
    expected form: a missing/rephrased-stale anchor is a failure, so the
    historical magnitudes (δ_diss ~26 %, δ_disp ~10 %, spectral floor
    ~2 T_H) — none of which match the anchored numeric form — FAIL, and the
    corrected sentences PASS. The polariton (−19 %) and graphene (−2.8 %)
    values are deliberately NOT matched here: they belong to other
    platforms/modules and would false-positive against the Heidelberg row.
    """
    import re as _re
    import math as _math

    paper_path = _H.PAPERS_DIR / "F" / "paper_draft.tex"
    if not paper_path.exists():
        return CheckResult(passed=False, error=f"Paper not found: {paper_path}")

    try:
        from scripts.gen_d1_hierarchy_table import compute_bec_hierarchy
    except Exception as e:  # pragma: no cover - import guard
        return CheckResult(passed=False, error=f"cannot import evaluator: {e}")

    heid = compute_bec_hierarchy()["Heidelberg"]
    text = paper_path.read_text(encoding="utf-8")
    TOL = 0.005  # 0.5 % relative

    details: List[Detail] = []
    all_pass = True

    def _rel_ok(got, want) -> tuple:
        if got is None:
            return False, "unparseable / wrong format"
        if want == 0:
            return abs(got) <= TOL, f"paper={got:.4g}, canon=0"
        rel = abs(got - want) / abs(want)
        return rel <= TOL, f"paper={got:.4g}, canon={want:.4g}, rel={rel:.2%}"

    # (label, anchored regex capturing the LaTeX value, canonical key)
    claims = [
        ("heidelberg.delta_diss.second_order",
         r"\\delta_\{\\mathrm\{diss\}\}\s*\\approx\s*([^$]+?)\$.*?Heidelberg parameters",
         "delta_diss"),
        ("heidelberg.delta_disp.hierarchy",
         r"dispersive correction is \$\\delta_\{\\mathrm\{disp\}\}\s*\\approx\s*([^$]+?)\$",
         "delta_disp"),
        ("heidelberg.delta_diss.hierarchy",
         r"dissipative correction\s*\$?\\delta_\{\\mathrm\{diss\}\}\s*\\approx\s*([^$]+?)\$",
         "delta_diss"),
    ]
    for label, pat, key in claims:
        m = _re.search(pat, text, _re.DOTALL)
        if not m:
            details.append(Detail(label, False,
                                  "expected Heidelberg claim not found (missing or stale form)"))
            all_pass = False
            continue
        ok, msg = _rel_ok(_parse_latex_number(m.group(1)), heid[key])
        details.append(Detail(label, ok, msg))
        all_pass = all_pass and ok

    # Crossover sentence: ω_× = T_H ln(2/δ_diss) ≈ Y T_H (symbolic ln-arg;
    # the coefficient Y must equal ln(2 / canonical δ_diss)).
    cm = _re.search(
        r"\\ln\(2/\\delta_\{\\mathrm\{diss\}\}\)\s*\\approx\s*([\d.]+)\\,\s*T_H", text)
    if not cm:
        details.append(Detail("heidelberg.crossover", False,
                              "expected ω_× = T_H ln(2/δ_diss) ≈ Y T_H sentence not found"))
        all_pass = False
    else:
        y_ok, y_msg = _rel_ok(float(cm.group(1)), _math.log(2.0 / heid["delta_diss"]))
        details.append(Detail("heidelberg.crossover", y_ok, y_msg))
        all_pass = all_pass and y_ok

    return CheckResult(passed=all_pass, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 8: CGL FDR derivation consistency
# ═══════════════════════════════════════════════════════════════════════

@register_check("cgl_fdr", "CGL FDR derivation produces correct results")
def check_cgl_fdr() -> CheckResult:
    """Verify the CGL dynamical KMS derivation of the FDR."""
    from src.second_order.cgl_derivation import (
        verify_einstein_relation,
        verify_first_order_bec,
        verify_second_order_fdr,
        derive_fdr_fourier,
    )

    details = []
    all_pass = True

    # Einstein relation
    ok = verify_einstein_relation()
    details.append(Detail("einstein_relation", ok,
                          "σ = γ/β₀ for Brownian particle"))
    if not ok:
        all_pass = False

    # First-order BEC FDR
    ok = verify_first_order_bec()
    details.append(Detail("first_order_bec", ok,
                          "K_N = 2Γ/β₀ for BEC with damping"))
    if not ok:
        all_pass = False

    # Second-order noise reality
    ok = verify_second_order_fdr()
    details.append(Detail("second_order_real", ok,
                          "Second-order noise kernel is real"))
    if not ok:
        all_pass = False

    # General pattern: noise count at even orders
    try:
        results = derive_fdr_fourier(4)
        counts = {N: len(data['noise']) for N, data in results.items()}
        ok = counts == {0: 1, 1: 0, 2: 2, 3: 0, 4: 3}
        details.append(Detail("noise_count_pattern", ok,
                              f"Noise counts: {counts}"))
        if not ok:
            all_pass = False
    except Exception as e:
        details.append(Detail("noise_count_pattern", False, str(e)))
        all_pass = False

    return CheckResult(passed=all_pass, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 12: Physical bounds validation
# ═══════════════════════════════════════════════════════════════════════

@register_check("physical_bounds", "All computed quantities within physical bounds")
def check_physical_bounds() -> CheckResult:
    """Verify computed physics values are physically reasonable.

    Catches absurdities like negative temperatures, perturbative corrections > 1,
    or shot counts that are impossibly small for tiny corrections.
    """
    from src.wkb.spectrum import (
        steinhauer_platform, heidelberg_platform, trento_platform,
        compute_spectrum, spectrum_summary,
    )

    details = []
    all_pass = True

    platforms = {
        'steinhauer': steinhauer_platform(),
        'heidelberg': heidelberg_platform(),
        'trento': trento_platform(),
    }

    for name, platform in platforms.items():
        spectrum = compute_spectrum(platform)
        summ = spectrum_summary(spectrum)

        checks = [
            ('T_H > 0', platform.T_H > 0),
            ('kappa > 0', platform.kappa > 0),
            ('0 < D < 1', 0 < platform.D < 1),
            ('0 < delta_diss < 1', 0 < summ['delta_diss_at_T_H'] < 1),
            ('n_noise >= 0', summ['n_noise_at_T_H'] >= 0),
        ]

        # Shot count sanity: if correction is sub-percent, need many shots
        delta_diss = summ['delta_diss_at_T_H']
        shots = summ['shots_needed']
        if delta_diss < 1e-3:
            checks.append((
                f'shots > 10^4 (delta={delta_diss:.1e})',
                shots > 1e4
            ))

        for check_name, passed in checks:
            if not passed:
                all_pass = False
            details.append(Detail(f"{name}/{check_name}", passed,
                                  f"{'OK' if passed else 'FAILED'}"))

    return CheckResult(passed=all_pass, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 13: Cross-path consistency
# ═══════════════════════════════════════════════════════════════════════

@register_check("cross_path_consistency",
                "Different code paths agree within 0.5%/1% tolerance")
def check_cross_path_consistency() -> CheckResult:
    """Verify quantities computed by different modules agree.

    Catches duplicate implementations that drift apart.
    """
    from src.core.formulas import decoherence_parameter
    from src.core.transonic_background import steinhauer_Rb87, solve_transonic_background
    from src.core.constants import EXPERIMENTS
    from src.wkb.spectrum import steinhauer_platform, compute_spectrum, spectrum_summary

    details = []
    all_pass = True

    # --- Compare delta_diss: direct formula vs spectrum_summary ---
    platform = steinhauer_platform()
    spectrum = compute_spectrum(platform)
    summ = spectrum_summary(spectrum)
    delta_diss_spectrum = summ['delta_diss_at_T_H']

    gamma_eff = platform.gamma_1 + platform.gamma_2
    delta_diss_direct = gamma_eff * (platform.T_H / platform.c_s)**2 / platform.kappa

    if delta_diss_spectrum > 0 and delta_diss_direct > 0:
        rel_diff = abs(delta_diss_spectrum - delta_diss_direct) / delta_diss_spectrum
        ok = rel_diff < 0.005
        details.append(Detail(
            "delta_diss: spectrum vs direct",
            ok,
            f"spectrum={delta_diss_spectrum:.4e}, direct={delta_diss_direct:.4e}, "
            f"rel_diff={rel_diff:.4f}"
        ))
        if not ok:
            all_pass = False

    # --- Compare decoherence: spectrum_summary vs formulas.py ---
    dk_spectrum = summ['delta_k_at_T_H']
    Gamma_H = gamma_eff * (platform.T_H / platform.c_s)**2
    dk_formulas = decoherence_parameter(Gamma_H, platform.kappa)

    if dk_spectrum > 0 and dk_formulas > 0:
        rel_diff = abs(dk_spectrum - dk_formulas) / dk_spectrum
        ok = rel_diff < 0.005
        details.append(Detail(
            "decoherence: spectrum vs formulas",
            ok,
            f"spectrum={dk_spectrum:.4e}, formulas={dk_formulas:.4e}, "
            f"rel_diff={rel_diff:.4f}"
        ))
        if not ok:
            all_pass = False

    # Note: WKB platform uses natural units (c_s=1, kappa=1) while
    # BECParameters uses SI. Dimensionless ratios (delta_diss, decoherence)
    # are unit-independent and compared above. Dimensional quantities
    # (c_s, T_H) cannot be directly compared across unit systems.

    return CheckResult(passed=all_pass, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK: Quantum-network substrate Python ↔ Lean cross-validation
# ═══════════════════════════════════════════════════════════════════════

@register_check("quantum_network",
                "QN Python formulas satisfy the QuantumNetwork Lean theorem identities")
def check_quantum_network() -> CheckResult:
    """Cross-checks the `src/core/formulas.py` quantum-network mirror against the
    closed-form identities/bounds proven in `lean/SKEFTHawking/QuantumNetwork/*.lean`
    (Phases 6AA–6AD), and confirms the referenced Lean theorem names exist in that
    subdirectory.

    ⚠️ The parenthetical here used to read "CHECK 1 only globs the top-level
    package", which was this check's stated reason for re-scanning `QuantumNetwork/`
    itself. That is no longer true — `check_formulas_to_theorems` scans the whole
    tree as of 2026-08-04 (audit QI-01). The QN-specific name assertions below are
    still worth keeping (they pin an explicit expected roster rather than a
    resolution set), but they are no longer compensating for a blind CHECK 1."""
    from src.core import formulas as F

    details: List[Detail] = []
    all_pass = True

    def check(name: str, cond: bool, msg: str = ""):
        nonlocal all_pass
        details.append(Detail(name, cond, msg))
        if not cond:
            all_pass = False

    # Werner swap multiplicative in the Werner parameter (wernerParam_swap)
    F1, F2 = 0.83, 0.71
    check("wernerParam_swap_multiplicative",
          abs(F.werner_param(F.werner_swap_fidelity(F1, F2))
              - F.werner_param(F1) * F.werner_param(F2)) < 1e-12)

    # End-to-end one-more-link recurrence (endToEndFidelity_succ)
    check("endToEndFidelity_succ",
          all(abs(F.end_to_end_fidelity(0.9, k + 1)
                  - F.werner_swap_fidelity(F.end_to_end_fidelity(0.9, k), 0.9)) < 1e-12
              for k in range(6)))

    # Envelope ∈ [1/4,1] (swapChain_fidelity_envelope)
    check("swapChain_fidelity_envelope",
          all(0.25 - 1e-12 <= F.end_to_end_fidelity(Fl, k) <= 1.0 + 1e-12
              for Fl in (0.25, 0.5, 0.9, 1.0) for k in range(9)))

    # BBPSSW strict increase on (1/2,1) (bbpsswRecurrence_gt)
    check("bbpsswRecurrence_gt",
          all(F.bbpssw_recurrence(Fl) > Fl for Fl in (0.51, 0.6, 0.75, 0.9, 0.99)))

    # DEJMPS phase-flip-only increase + verified single-step decrease witness
    check("dejmps_increase_phaseFlipOnly",
          all(F.dejmps_out_a(A, (1 - A) / 2, (1 - A) / 2, 0.0) > A for A in (0.55, 0.7, 0.9)))
    check("dejmps_single_step_can_decrease",
          abs(F.dejmps_out_a(0.6, 0, 0, 0.4) - 13 / 25) < 1e-12
          and F.dejmps_out_a(0.6, 0, 0, 0.4) < 0.6)

    # Fortescue–Lo finite-round yield (fortescueLoYield_gt_two_thirds, _lt_one)
    check("fortescueLoYield_gt_two_thirds",
          all(2 / 3 < F.fortescue_lo_yield(D) < 1.0 for D in (3, 5, 12)))

    # BB84 crossover proven, not hardcoded (bb84_crossover_exists, strictAntiOn)
    check("bb84KeyRate_zero", abs(F.bb84_key_rate(0.0) - 1.0) < 1e-12)
    check("bb84_crossover_sign_change",
          F.bb84_key_rate(0.10) > 0.0 and F.bb84_key_rate(0.12) < 0.0)

    # H₂(1/3) < 1 (w3_asymptotic_specified_lt_one)
    check("w3_asymptotic_specified_lt_one", 0.0 < F.bin_entropy_bit(1 / 3) < 1.0)

    # Horodecki teleportation (teleportAvgFidelity_horodecki, teleport_beats_classical_iff)
    check("teleport_horodecki_formula",
          all(abs(F.teleport_avg_fidelity(Fl) - (2 * Fl + 1) / 3) < 1e-12
              for Fl in (0.5, 0.7, 1.0)))
    check("teleport_beats_classical_iff",
          F.teleport_avg_fidelity(0.6) > 2 / 3 and F.teleport_avg_fidelity(0.4) < 2 / 3)
    check("haarPauliConstant_eq_third", abs(F.HAAR_PAULI_CONSTANT - 1 / 3) < 1e-15)

    # Tier-1 anchors (bsmSuccessProb_*, linkRate_*)
    check("bsmSuccessProb_bounds",
          F.bsm_success_prob(2) == 0.5 and F.bsm_success_prob(4) == 1.0)
    check("linkRate_monotonicity",
          F.link_rate(1000, 2e8, 0.5) > F.link_rate(1000, 2e8, 0.9)
          and F.link_rate(2000, 2e8, 0.5) > F.link_rate(1000, 2e8, 0.5))

    # Referenced QN Lean theorem names exist in the QuantumNetwork subdirectory
    qn_dir = _H.LEAN_DIR / "QuantumNetwork"     # was Path(__file__) — ADR-009 H1
    expected = [
        "wernerParam_swap", "endToEndFidelity_succ", "swapChain_fidelity_envelope",
        "bbpsswRecurrence_gt", "dejmps_increase_phaseFlipOnly", "dejmps_single_step_can_decrease",
        "fortescueLoYield_gt_two_thirds", "bb84_crossover_exists",
        "teleportAvgFidelity_horodecki_unconditional", "haarPauliZSqAverage_eq",
        "bsmSuccessProb_le_half_of_linearOptics", "linkRate_antitone_success",
    ]
    if qn_dir.exists():
        names = set()
        # rglob for the same reason as every other Lean scan (audit QI-01).
        # `QuantumNetwork/` is flat today (104 files, no subdirectories), so this is
        # a no-op right now — but this check FAILS on a theorem it cannot find, so
        # the day someone adds a package here the non-recursive form would report
        # real theorems missing. Found by the structural leg of
        # `tests/test_lean_scan_coverage.py`, not by the manual sweep.
        for lf in qn_dir.rglob("*.lean"):
            for line in lf.read_text().splitlines():
                s = line.strip()
                if s.startswith("theorem ") or s.startswith("lemma "):
                    names.add(s.split()[1].split("(")[0].split(":")[0].strip())
        missing = [t for t in expected if t not in names]
        check("qn_lean_theorems_exist", not missing,
              f"missing: {missing}" if missing else f"{len(expected)} QN theorems found")
    else:
        check("qn_lean_theorems_exist", False, "QuantumNetwork dir not found")

    return CheckResult(passed=all_pass, details=details)
