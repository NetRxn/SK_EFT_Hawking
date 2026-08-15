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

#: `papers/paper1_first_order/tables.py` renders exactly these five rows via
#: `scripts/paper_tables/sources.platform_rows`. Each entry maps the row's
#: LaTeX label marker to (a) the display unit the renderer prints in and (b) the
#: CANONICAL quantity, recomputed here from `constants`/`formulas` rather than
#: read back from the renderer — a table can only be checked against something
#: that did not produce it.
_PAPER1_TABLE_ROWS = (
    (r"$c_s$",                       "mm/s",            1e3),
    (r"$\xi$",                       r"$\mu$m",         1e6),
    (r"$\kappa$",                    r"s$^{-1}$",       1.0),
    (r"$T_H$",                       "nK",              1e9),
    (r"\delta_{\mathrm{diss}}",      "(dimensionless)", 1.0),
)

#: The rendered artifact the draft `\input`s, relative to the paper directory.
_PAPER1_TABLE_STEM = "tables/table1_experimental_params"


def _parse_latex_tabular(tex: str) -> list[list[str]]:
    """Split the first ``tabular`` environment in ``tex`` into rows of cells.

    Structural rules only — `\\hline`, comments and blank rows are dropped, and
    each surviving row is split on unescaped ``&`` and stripped. Returns ``[]``
    when there is no `tabular`, which is the SHIPPED-EMPTY signal the caller
    must treat as a failure (see `check_paper_table_consistency`).
    """
    import re as _re
    m = _re.search(r"\\begin\{tabular\}.*?\n(.*?)\\end\{tabular\}", tex, _re.S)
    if not m:
        return []
    rows: list[list[str]] = []
    for raw in m.group(1).split(r"\\"):
        line = _re.sub(r"(?<!\\)%[^\n]*", "", raw)
        line = line.replace(r"\hline", "").strip()
        if not line:
            continue
        rows.append([c.strip() for c in _re.split(r"(?<!\\)&", line)])
    return rows


def _displayed_tolerance(cell: str) -> float:
    """One unit in the cell's LAST PRINTED PLACE, in the cell's own units.

    The cells are autogenerated at a fixed precision (`:.2f`, `:.1f`, `:.3f`,
    one-digit mantissa), so "does the shipped digit string still represent the
    canonical value" is the question with an answer — a 5 % relative tolerance
    would pass a table three regenerations stale. Returns `inf` when the format
    is unrecognised so an unparsed cell never manufactures a failure; the cell's
    VALUE is separately required to parse.
    """
    import re as _re
    s = cell.replace("$", "").replace(r"\textbf{", "").rstrip("}").strip()
    m = _re.search(r"(-?\d+)(?:\.(\d+))?\s*\\times\s*10\^\{?(-?\d+)\}?", s)
    if m:
        return 10.0 ** (-len(m.group(2) or "")) * 10.0 ** int(m.group(3))
    m = _re.fullmatch(r"-?\d+(?:\.(\d+))?", s)
    if m:
        return 10.0 ** (-len(m.group(1) or ""))
    return float("inf")


@register_check("paper_table",
                "Paper 1's SHIPPED Table 1 cells match the canonical solver output")
def check_paper_table_consistency() -> CheckResult:
    """CHECK: parse `papers/paper1_first_order/tables/table1_experimental_params.tex`
    — the artifact `paper_draft.tex` actually `\\input`s — and hold every cell to
    the canonical evaluator at the cell's own displayed precision.

    ⚠️ REWRITTEN 2026-08-05 (audit finding QI-31). This check opened
    `paper_draft.tex` and then used it **only for `.exists()`**: the "paper" side
    of the comparison was a dict hardcoded in this file, 11 of whose 12 cells were
    byte-identical to `check_numerical_consistency`'s `expected`. So it compared
    the solver to a second copy of `numerical`'s reference values and reported it
    as a paper-agreement result. It could not fail on any edit to the paper,
    because it never read one. Sampled back to 2026-05-01, it never had.

    What it now reads is the RENDERED table, which is where the real failure mode
    lives: `tables_fresh` regenerates on mtime and `\\input`-ing a stale or empty
    table leaves the draft compiling cleanly with wrong numbers. That is not
    hypothetical — `papers/paper15_methodology/tables/table2_checks.tex` shipped
    with rules and **zero rows** for 40+ commits while the paper `\\input`-ed it
    (fixed in this same audit). Leg A below is the guard that class needed.

    Three legs:

    * **A — the artifact is real and non-empty.** The draft must `\\input` the
      table, the table must exist, parse to a `tabular`, and carry the expected
      platform columns and data rows. An empty or orphaned table fails here.
    * **B — every cell agrees with the canonical evaluator**, recomputed from
      `constants.get_all_experiments()` and `formulas` (Invariants #1/#2), never
      read back from `paper_tables.sources` — a renderer cannot be the reference
      for its own output. Tolerance is ONE unit in the cell's last printed place.
    * **C — the rows are the ones declared.** A row silently dropped from the
      spec would otherwise shrink leg B's population to nothing and pass.
    """
    from src.core.constants import get_all_experiments

    details: List[Detail] = []
    all_pass = True

    paper_dir = _H.PAPERS_DIR / "paper1_first_order"
    paper_path = paper_dir / "paper_draft.tex"
    if not paper_path.exists():
        return CheckResult(passed=False, error=f"Paper not found: {paper_path}")

    # ── Leg A: the draft \input{}s this table, and the table has content ──
    draft = paper_path.read_text()
    # LaTeX accepts `\input{x}` and `\input{x.tex}` interchangeably; the draft
    # currently writes the second. Accept both — the point is that the paper
    # ships THIS file, not which of two equivalent spellings it used.
    if not any(f"\\input{{{_PAPER1_TABLE_STEM}{ext}}}" in draft
               for ext in ("", ".tex")):
        return CheckResult(passed=False, details=[Detail(
            "input_wiring", False,
            f"paper_draft.tex does not \\input{{{_PAPER1_TABLE_STEM}}} — this check "
            f"would be auditing a file the paper does not ship")])

    table_path = paper_dir / (_PAPER1_TABLE_STEM + ".tex")
    if not table_path.exists():
        return CheckResult(passed=False, details=[Detail(
            "table_present", False, f"missing rendered table: {table_path}")])

    rows = _parse_latex_tabular(table_path.read_text())
    if len(rows) < 2:
        return CheckResult(passed=False, details=[Detail(
            "table_present", False,
            f"{table_path.name} parsed to {len(rows)} row(s) — a table shipped with "
            f"rules and no data still \\input{{}}s and still compiles")])

    header, data_rows = rows[0], rows[1:]
    # Platform key = the leading word of each column heading ("Steinhauer
    # ($^{87}$Rb)" -> "Steinhauer"), so the column ORDER is read from the table
    # rather than assumed — a reordered spec must not silently transpose cells.
    try:
        experiments = get_all_experiments()
    except Exception as e:
        return CheckResult(passed=False, error=str(e))

    columns: list[tuple[int, str]] = []
    for idx, cell in enumerate(header):
        key = cell.split()[0].strip() if cell.split() else ""
        if key in experiments:
            columns.append((idx, key))
    if not columns:
        return CheckResult(passed=False, details=[Detail(
            "columns", False,
            f"no header column resolves to a known platform; header={header!r}. "
            f"Known: {sorted(experiments)}")])
    details.append(Detail("columns", True,
                          f"{len(columns)} platform column(s): "
                          f"{[k for _, k in columns]}"))

    # ── Leg B/C: canonical values, recomputed here ──
    canonical: dict[str, dict[str, float]] = {}
    for name, (params, bg) in experiments.items():
        canonical[name] = {
            r"$c_s$":    params.sound_speed_upstream,
            r"$\xi$":    params.healing_length,
            r"$\kappa$": bg.surface_gravity,
            r"$T_H$":    bg.hawking_temp,
        }
    try:
        import src.core.transonic_background as tb
        from src.core.formulas import beliaev_transport_coefficients
        for name, (params, bg) in experiments.items():
            tc = beliaev_transport_coefficients(
                n_1D=params.density_upstream,
                a_s=params.scattering_length,
                kappa=bg.surface_gravity,
                c_s=params.sound_speed_upstream,
                xi=params.healing_length,
            )
            canonical[name][r"\delta_{\mathrm{diss}}"] = tb.compute_dissipative_correction(
                bg, params, tc["gamma_1"], tc["gamma_2"])["delta_diss"]
    except Exception as e:      # pragma: no cover - canonical import failure
        return CheckResult(passed=False, error=f"canonical evaluator failed: {e}")

    seen_markers: set = set()
    for row in data_rows:
        if not row:
            continue
        label = row[0]
        marker = next((mk for mk, _u, _s in _PAPER1_TABLE_ROWS if mk in label), None)
        if marker is None:
            continue
        seen_markers.add(marker)
        scale = next(s for mk, _u, s in _PAPER1_TABLE_ROWS if mk == marker)
        for idx, plat in columns:
            if idx >= len(row):
                all_pass = False
                details.append(Detail(f"{plat}.{marker}", False,
                                      f"row {label!r} has no cell for column {idx}"))
                continue
            cell = row[idx]
            shipped = _parse_latex_number(cell)
            if shipped is None:
                all_pass = False
                details.append(Detail(f"{plat}.{marker}", False,
                                      f"unparseable cell {cell!r} in row {label!r}"))
                continue
            expected = canonical[plat][marker] * scale
            tol = _displayed_tolerance(cell)
            ok = abs(shipped - expected) <= tol
            if not ok:
                all_pass = False
            details.append(Detail(
                f"{plat}.{marker}", ok,
                f"shipped={shipped:.6g}, canonical={expected:.6g}, "
                f"|diff|={abs(shipped - expected):.3g} vs 1 ulp={tol:.3g}"))

    # Leg C — every declared row must have been found. Without this, deleting a
    # row from the spec shrinks leg B's population silently and the check passes
    # on fewer and fewer cells.
    missing_rows = [mk for mk, _u, _s in _PAPER1_TABLE_ROWS if mk not in seen_markers]
    if missing_rows:
        all_pass = False
        details.append(Detail(
            "rows_declared", False,
            f"{len(missing_rows)} declared row(s) absent from the shipped table: "
            f"{missing_rows}"))
    else:
        details.append(Detail("rows_declared", True,
                              f"all {len(_PAPER1_TABLE_ROWS)} declared rows present"))

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

    # --- (2) Numeric crossover sentences: δ_diss = X gives ω_× ≃ Y T_eff ---
    #
    # ⚠️ THIS CHECK USED TO PIN THE WRONG PHYSICS, AND THAT IS WHY THE WRONG
    # PHYSICS SURVIVED THREE REVIEW CYCLES. It required the prose to read
    # `ω_× ≈ T_H ln(2/X)` and then asserted the coefficient against a
    # re-derived `log(2.0 / X)`. The floor is δ_diss, not δ_diss/2 — the
    # halving is already inside `noise_floor_eq_delta_diss`
    # (`noiseFloor p = p.Gamma_H / p.kappa`) — so the crossover is
    # `ln(1 + 1/δ_diss)`. A Stage-13 REQUIRED flagged the ln 2 discrepancy in
    # May 2026 and it was carried forward three times unclosed, because
    # CORRECTING THE PAPER WOULD HAVE TURNED THIS GATE RED. The guard was
    # holding the defect in place.
    #
    # The coefficient is now compared against the canonical evaluator's own
    # `omega_cross_over_TH` rather than against a formula restated here. A
    # check that re-states the physics it is checking asserts nothing about
    # the physics and drifts from it silently — the same reasoning that moved
    # `test_node_shape` onto `build_graph.SEVERITY_VALUES` under ADR-009.
    # There is now exactly one place the crossover formula lives.
    #
    # Matches the numeric sentences only: `δ_diss = X gives ω_× ≃ Y T_eff`.
    # The symbolic abstract/display forms carry no numerals and are excluded
    # by shape.
    cross_re = _re.compile(
        r"\\delta_\{?\\rm\s+diss\}?\s*=\s*([^$]+?)\s*\$?\s*gives\s*"
        r"\$?\\omega_\\times\s*\\simeq\s*([\d.]+)\\,\s*T_\{?\\rm\s+eff\}?",
        _re.DOTALL)
    matches = list(cross_re.finditer(text))
    if not matches:
        details.append(Detail(
            "crossover.present", False,
            "no numeric 'δ_diss = X gives ω_× ≃ Y T_eff' sentence found. NOTE: "
            "this check previously required the ln(2/X) form, which is the "
            "SUPERSEDED and incorrect expression; if the draft still carries "
            "it, the draft is what must change."))
        all_pass = False
    # Canonical (δ_diss -> crossover) pairs, straight from the evaluator.
    canon_cross = {h["delta_diss"]: h["omega_cross_over_TH"] for h in hier.values()}
    for i, m in enumerate(matches):
        X = _parse_latex_number(m.group(1))
        Y = float(m.group(2))
        if X is None:
            details.append(Detail(f"crossover[{i}].arg", False,
                                  f"unparseable δ_diss {m.group(1)!r}"))
            all_pass = False
            continue
        # (a) the quoted δ_diss must be one of the canonical values
        nearest = min(canon_cross, key=lambda d: abs(X - d) / abs(d))
        best = abs(X - nearest) / abs(nearest)
        arg_ok = best <= TOL
        details.append(Detail(f"crossover[{i}].delta_diss_match", arg_ok,
                              f"δ_diss={X:.4g}, nearest canon rel={best:.2%}"))
        # (b) the quoted coefficient must equal the EVALUATOR's crossover for
        #     that δ_diss — not a formula restated inside this check.
        y_ok, y_msg = _rel_ok(Y, canon_cross[nearest])
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

    # Crossover sentence: ω_× = T_H ln(1 + 1/δ_diss) ≈ Y T_H.
    #
    # ⚠️ SUPERSEDED FORM: this required `ln(2/δ_diss)` and asserted Y against a
    # re-derived `log(2.0 / δ_diss)`. Both were wrong by exactly ln 2 — the FDR
    # floor is δ_diss, not δ_diss/2, because the halving is already inside
    # `WKBConnection.noise_floor_eq_delta_diss` (`noiseFloor p = Gamma_H/kappa`).
    # The sibling `d1_hierarchy_table` carried the identical defect, so the two
    # gates corroborated each other while both were wrong, and a Stage-13
    # REQUIRED that flagged it in May 2026 went unclosed three times because
    # fixing the papers would have turned both gates red.
    #
    # Y is now compared against the evaluator's own `omega_cross_over_TH`, so
    # the formula lives in exactly one place and this check cannot drift from it.
    cm = _re.search(
        r"\\ln\\!?\s*\\left\(\s*1\s*\+\s*1/\\delta_\{\\mathrm\{diss\}\}\s*\\right\)"
        r"\s*\\approx\s*([\d.]+)\\,\s*T_H", text)
    if not cm:
        details.append(Detail(
            "heidelberg.crossover", False,
            "expected ω_× = T_H ln(1 + 1/δ_diss) ≈ Y T_H sentence not found. NOTE: "
            "the ln(2/δ_diss) form is SUPERSEDED and incorrect; if the draft still "
            "carries it, the draft is what must change."))
        all_pass = False
    else:
        y_ok, y_msg = _rel_ok(float(cm.group(1)), heid["omega_cross_over_TH"])
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

    # ── GRAPHENE LEG ──────────────────────────────────────────────────────
    # ⚠️ This check bounded only the three BEC platforms. The Γ_H repair raised
    # graphene `δ_diss` by ~12 orders and NOTHING bounded the result, so Pipeline
    # Invariant 5 ("every computed quantity has bounds") was unmet for the exact
    # quantity that wave changed. Two of four platforms land outside EFT validity
    # (Monolayer_50nm D=1.51; PN_junction_10nm D=7.64 with δ_disp=-30.55, a
    # "correction" of -3055 %) and shipped silently while every narrative in the
    # repo was scoped to the Dean device.
    #
    # The bound is on DISCLOSURE, not on the values: a platform outside validity
    # is fine so long as the RESULT SAYS SO. Forcing the numbers into range, or
    # dropping the platforms, would be the re-charter this suite exists to stop.
    from src.core.constants import GRAPHENE_PLATFORMS
    from src.graphene.hawking_predictions import graphene_hawking_prediction

    n_valid = n_flagged = 0
    for _name in sorted(GRAPHENE_PLATFORMS):
        r = graphene_hawking_prediction(_name)
        if "eft_valid" not in r:
            details.append(Detail(f"graphene:{_name}", False,
                                  "result carries no `eft_valid` key — an "
                                  "out-of-validity value would ship as a bare number"))
            all_pass = False
            continue
        in_range = (r["D"] < 1.0 and abs(r["delta_disp"]) < 1.0
                    and 0.0 < r["delta_diss"] < 1.0)
        if r["eft_valid"] != in_range:
            details.append(Detail(f"graphene:{_name}", False,
                                  f"`eft_valid`={r['eft_valid']} contradicts measured "
                                  f"D={r['D']:.3g}, δ_disp={r['delta_disp']:.3g}, "
                                  f"δ_diss={r['delta_diss']:.3g}"))
            all_pass = False
        elif in_range:
            n_valid += 1
            details.append(Detail(f"graphene:{_name}", True,
                                  f"D={r['D']:.3g}, δ_diss={r['delta_diss']:.3g}, "
                                  f"δ_disp={r['delta_disp']:.3g} — within EFT validity"))
        else:
            n_flagged += 1
            details.append(Detail(f"graphene:{_name}", True,
                                  f"OUTSIDE EFT validity, correctly flagged: "
                                  f"D={r['D']:.3g}, δ_disp={r['delta_disp']:.3g}",
                                  warning=True))
    details.append(Detail(
        "graphene_summary", True,
        f"{len(GRAPHENE_PLATFORMS)} graphene platform(s) bounded — {n_valid} within "
        f"EFT validity, {n_flagged} outside and DISCLOSED", warning=bool(n_flagged)))

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

    # --- Decoherence: the DEFINITIONAL factor-of-2 relation ---
    #
    # ⚠️ REWRITTEN 2026-08-05 (PR-review pass 2, R4-I1). This leg used to read
    # "decoherence: spectrum vs formulas" and compare `delta_k_at_T_H` against
    # `decoherence_parameter(Gamma_H, kappa)`. It could NEVER disagree with the leg
    # above it, and the mechanism is exact rather than approximate:
    #
    #   decoherence_parameter(G, k) = 2G/k          (formulas.py)
    #   delta_k_at_T_H              = 2 * delta_diss_at_T_H
    #
    # so BOTH sides of this comparison were exactly 2x both sides of the first, and
    # `|a-b|/a` is scale-invariant. Measured: both legs produced rel_diff =
    # 4.127685699545415e-06, **bit-identical**. Two details, one assertion — read by
    # a reviewer as two independent cross-path confirmations.
    #
    # What it can honestly test is the factor-of-2 relation ITSELF, which is a real
    # invariant (`delta_k = 2 * delta_diss`) and would catch a spectrum that
    # computed the two inconsistently. That is what it now asserts. A genuinely
    # independent second path for `delta_k` would be better still and is NOT
    # invented here — see the pass-2 register.
    dk_spectrum = summ['delta_k_at_T_H']
    dd_spectrum = summ['delta_diss_at_T_H']

    if dk_spectrum > 0 and dd_spectrum > 0:
        ratio = dk_spectrum / dd_spectrum
        ok = abs(ratio - 2.0) < 0.005
        details.append(Detail(
            "decoherence: delta_k = 2 x delta_diss (definitional)",
            ok,
            f"delta_k={dk_spectrum:.4e}, delta_diss={dd_spectrum:.4e}, "
            f"ratio={ratio:.6f} (expected 2.0)"
        ))
        if not ok:
            all_pass = False
    else:
        # Absence is not agreement: a spectrum reporting zero for either quantity
        # means this relation was NOT tested (the old leg skipped silently here).
        details.append(Detail(
            "decoherence: delta_k = 2 x delta_diss (definitional)", False,
            f"NOT TESTED — delta_k={dk_spectrum:.4e}, delta_diss={dd_spectrum:.4e}; "
            f"a non-positive value means the relation was never evaluated"))
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
        # `QuantumNetwork/` is flat today (no subdirectories), so this is
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
