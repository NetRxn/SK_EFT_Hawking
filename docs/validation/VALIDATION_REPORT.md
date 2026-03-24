# Cross-Layer Validation Report: SK-EFT Hawking Project

## Purpose

This report documents the automated verification of consistency between the four layers of the SK-EFT Hawking project: Python source code, Lean 4 formal proofs, Jupyter notebooks, and LaTeX paper drafts. It is designed for inclusion as a paper appendix or supplementary material.

## Validation Architecture

The validation suite (`scripts/validate.py`) performs 8 independent checks that together cover the full consistency surface of the project. Each check is a pure-Python function with no external dependencies beyond the project's own `src.core` modules.

### Check Summary

| # | Check | What it validates | Sub-checks |
|---|-------|-------------------|------------|
| 1 | `formulas` | Each Python physics function references a Lean theorem name that exists in the Aristotle registry | 7 functions |
| 2 | `numerical` | `get_all_experiments()` solver output matches published reference values (5% tolerance) | 12 parameters |
| 3 | `identities` | Mathematical boundary conditions and identities hold (counting formula, zero-limits, acoustic-mode vanishing) | 7 identities |
| 4 | `paper_table` | Paper 1 Table 1 LaTeX values are reproducible from the transonic solver | 12 entries |
| 5 | `theorems` | The Aristotle theorem registry has exactly 35 entries and is self-consistent | 3 consistency checks |
| 6 | `notebooks` | All 4 Jupyter notebooks import physics from `src.core` rather than redefining it inline | 4 notebooks, 9 forbidden function patterns |
| 7 | `lean_source` | Key theorem identifiers from the registry appear in the Lean 4 source files | 5 spot checks with name mapping |
| 8 | `lean_build` | `lake build` completes without sorry (skipped if `lake` not available) | 1 build check |

## Reference Values

The following are the canonical experimental parameters computed from `src.core.transonic_background.solve_transonic_background()` using quasi-1D BEC physics (g_1D = 2 hbar^2 a_s / (m a_perp^2)).

| Parameter | Steinhauer (87Rb) | Heidelberg (39K) | Trento (23Na) |
|-----------|-------------------|------------------|---------------|
| c_s (mm/s) | 1.151 | 3.919 | 2.185 |
| xi (um) | 0.635 | 0.416 | 1.264 |
| kappa (s^-1) | 21.9 | 101.9 | 21.4 |
| D | 0.0134 | 0.0118 | 0.0137 |
| T_H (nK) | 0.027 | 0.124 | 0.026 |
| delta_diss | 5.9e-05 | 1.6e-03 | 1.4e-05 |

## Formula-to-Proof Traceability

Each function in `src/core/formulas.py` carries a docstring that names the Lean theorem(s) it implements. The Aristotle automated prover generated the proofs across 7 runs (run IDs stored in `src/core/constants.py:ARISTOTLE_THEOREMS`).

| Python function | Lean theorem(s) | Aristotle run |
|----------------|-----------------|---------------|
| `count_coefficients` | secondOrder_count, counting_formula_N2, counting_formula_N3 | d61290fd |
| `enumerate_monomials` | spatial_parity_eliminates_second_order, parity_null_test | 3eedcabb |
| `damping_rate` | dampingRate_eq_zero_iff | 518636d7 |
| `dispersive_correction` | dispersive_bound, dispersive_bound_tight | a87f425a, 3eedcabb |
| `first_order_correction` | firstOrder_correction_zero_iff | 518636d7 |
| `second_order_correction` | (secondOrderCorrection — Lean definition) | 518636d7 |
| `effective_temperature_ratio` | effective_temperature_well_defined | 518636d7 |
| `turning_point_shift` | turning_point_shift_nonzero, turning_point_shift_nonzero_strengthened | 518636d7 |

## Single Source of Truth Architecture

The project enforces a strict data flow to prevent the kind of cascading errors that motivated this validation:

```
src/core/constants.py          ← physical constants, experiment configs, theorem registry
src/core/formulas.py           ← every formula, with Lean theorem docstrings
src/core/transonic_background.py ← numerical solver (BECParameters → TransonicBackground)
     │
     ├── notebooks/*.ipynb     ← import only, no inline physics
     ├── papers/*.tex          ← table values match solver output
     └── tests/test_*.py       ← pytest against the same functions
```

Notebooks are forbidden from defining any of the 9 core physics functions. This is enforced by check #6 and can be verified at any time via `python scripts/validate.py --check notebooks`.

## How to Run

```bash
# All checks (human-readable):
python scripts/validate.py

# JSON output for CI pipelines:
python scripts/validate.py --json

# Archive a timestamped report to docs/validation/reports/:
python scripts/validate.py --archive

# Single check:
python scripts/validate.py --check formulas

# List available checks:
python scripts/validate.py --list
```

## Extending the Validation

New checks are added by decorating a function:

```python
@register_check("my_check", "Description of what it validates")
def check_my_thing() -> CheckResult:
    details = []
    # ... perform sub-checks, append Detail(name, passed, message) ...
    return CheckResult(passed=all_ok, details=details)
```

The function is automatically registered, included in `--list`, runnable individually via `--check my_check`, and included in archival output.

## Validation History

Timestamped results are archived in `docs/validation/reports/` as paired JSON + text files. Each run is named `validation_YYYYMMDDTHHMMSSZ.{json,txt}`. The JSON files can be diffed programmatically to detect drift over time.
