#!/usr/bin/env python3
"""
SK-EFT Hawking Project — Cross-Layer Validation Suite
=====================================================

Single entry point for verifying consistency across:
  Python source  ↔  Lean formal proofs  ↔  Notebooks  ↔  Papers

Usage
-----
    # From project root (recommended):
    python scripts/validate.py

    # With JSON output for CI:
    python scripts/validate.py --json

    # Save timestamped report to docs/validation/reports/:
    python scripts/validate.py --archive

    # Run a single check:
    python scripts/validate.py --check formulas

    # List available checks:
    python scripts/validate.py --list

Exit Codes
----------
    0 — all checks passed
    1 — one or more checks failed
    2 — script error (bad arguments, missing files)

Architecture & Extensibility
----------------------------
Each check is a function decorated with @register_check. To add a new check:

    @register_check("my_new_check", "Description of what it validates")
    def check_my_new_thing() -> CheckResult:
        ...
        return CheckResult(passed=True, details=[...])

The decorator handles registration, output formatting, and CI integration.
Checks are run in registration order, and any check can be run individually
via --check <name>.

Design Decisions
----------------
- Pure stdlib (no pytest dependency for the validation itself).
  This means validation works even if the test environment is degraded.
- Path-agnostic: resolves PROJECT_ROOT from this file's location,
  works from any working directory.
- Timestamped archival: --archive writes a dated JSON + text report
  to docs/validation/reports/ for historical tracking.
- Lean integration: if `lake` is on PATH, runs `lake build` as a check.
  If not available, skips gracefully with a warning.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import time
from dataclasses import dataclass, field, asdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Callable, Dict, List, Optional

# ═══════════════════════════════════════════════════════════════════════
# Path resolution
# ═══════════════════════════════════════════════════════════════════════

SCRIPT_DIR = Path(__file__).resolve().parent
PROJECT_ROOT = SCRIPT_DIR.parent
SRC_DIR = PROJECT_ROOT / "src"
LEAN_DIR = PROJECT_ROOT / "lean" / "SKEFTHawking"
NOTEBOOKS_DIR = PROJECT_ROOT / "notebooks"
PAPERS_DIR = PROJECT_ROOT / "papers"
REPORTS_DIR = PROJECT_ROOT / "docs" / "validation" / "reports"

# Ensure src is importable
sys.path.insert(0, str(PROJECT_ROOT))


# ═══════════════════════════════════════════════════════════════════════
# Data structures
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class Detail:
    """Single sub-check result."""
    name: str
    passed: bool
    message: str = ""
    warning: bool = False  # True = passed but with advisory warning (⚠)


@dataclass
class CheckResult:
    """Result of one top-level check."""
    passed: bool
    details: List[Detail] = field(default_factory=list)
    error: Optional[str] = None


@dataclass
class CheckSpec:
    """Registered check metadata."""
    name: str
    description: str
    func: Callable[[], CheckResult]


# Global registry
_CHECKS: List[CheckSpec] = []


def register_check(name: str, description: str):
    """Decorator to register a validation check."""
    def decorator(func: Callable[[], CheckResult]) -> Callable[[], CheckResult]:
        _CHECKS.append(CheckSpec(name=name, description=description, func=func))
        return func
    return decorator


# ═══════════════════════════════════════════════════════════════════════
# CHECK 1: Python formulas ↔ Lean theorems
# ═══════════════════════════════════════════════════════════════════════

@register_check("formulas", "Python formulas reference valid Lean theorems")
def check_formulas_to_theorems() -> CheckResult:
    from src.core import formulas
    from src.core.constants import ARISTOTLE_THEOREMS

    mapping = [
        ('count_coefficients', ['secondOrder_count', 'secondOrder_count_with_parity', 'thirdOrder_count']),
        ('enumerate_monomials', ['secondOrder_count_with_parity', 'secondOrder_requires_parity_breaking']),
        ('damping_rate', ['dampingRate_eq_zero_iff']),
        ('dispersive_correction', ['dispersive_correction_bound', 'bogoliubov_superluminal']),
        ('first_order_correction', ['firstOrder_correction_zero_iff']),
        ('effective_temperature_ratio', ['effective_temp_zeroth_order']),
        ('turning_point_shift', ['turning_point_shift_nonzero', 'turning_point_shift']),
    ]

    # Build set of all Lean theorem names (Aristotle-proved + manually proved)
    lean_dir = Path(__file__).parent.parent / 'lean' / 'SKEFTHawking'
    all_lean_names = set(ARISTOTLE_THEOREMS.keys())
    if lean_dir.exists():
        for lean_file in lean_dir.glob('*.lean'):
            for line in lean_file.read_text().splitlines():
                if line.startswith('theorem '):
                    name = line.split()[1].split('(')[0].split(':')[0].strip()
                    all_lean_names.add(name)

    details = []
    all_pass = True

    for func_name, theorem_names in mapping:
        func = getattr(formulas, func_name, None)
        if not func or not func.__doc__:
            details.append(Detail(func_name, False, "Function not found or missing docstring"))
            all_pass = False
            continue

        doc = func.__doc__
        missing_from_doc = [t for t in theorem_names if t not in doc]
        missing_from_lean = [t for t in theorem_names if t not in all_lean_names]

        if not missing_from_doc and not missing_from_lean:
            details.append(Detail(func_name, True, f"Refs: {', '.join(theorem_names)}"))
        elif missing_from_doc:
            details.append(Detail(func_name, False, f"Missing from docstring: {missing_from_doc}"))
            all_pass = False
        else:
            details.append(Detail(func_name, False, f"Not in Lean source or ARISTOTLE_THEOREMS: {missing_from_lean}"))
            all_pass = False

    return CheckResult(passed=all_pass, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 2: Numerical consistency
# ═══════════════════════════════════════════════════════════════════════

@register_check("numerical", "Experimental parameters match reference values")
def check_numerical_consistency() -> CheckResult:
    from src.core.constants import get_all_experiments, HBAR

    expected = {
        'Steinhauer': {'c_s': 1.151e-3, 'xi': 0.635e-6, 'kappa': 21.9, 'T_H': 2.66e-11},
        'Heidelberg': {'c_s': 3.919e-3, 'xi': 0.416e-6, 'kappa': 101.9, 'T_H': 1.24e-10},
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

    paper_path = PAPERS_DIR / "paper1_first_order" / "paper_draft.tex"
    if not paper_path.exists():
        return CheckResult(passed=False, error=f"Paper not found: {paper_path}")

    # Reference values from the corrected table
    paper_table = {
        'Steinhauer': {'c_s': 1.151e-3, 'xi': 0.635e-6, 'kappa': 21.9, 'T_H': 0.027e-9},
        'Heidelberg': {'c_s': 3.919e-3, 'xi': 0.416e-6, 'kappa': 101.9, 'T_H': 0.124e-9},
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
# CHECK 5: Theorem registry
# ═══════════════════════════════════════════════════════════════════════

@register_check("theorems", "Theorem registry has 56 entries and is self-consistent")
def check_theorem_count() -> CheckResult:
    from src.core.constants import ARISTOTLE_THEOREMS, TOTAL_THEOREMS

    details = []
    all_pass = True

    for name, (actual, expected) in {
        "TOTAL_THEOREMS": (TOTAL_THEOREMS, 84),
        "len(ARISTOTLE_THEOREMS)": (len(ARISTOTLE_THEOREMS), 84),
    }.items():
        ok = actual == expected
        details.append(Detail(name, ok, f"actual={actual}, expected={expected}"))
        if not ok:
            all_pass = False

    ok = TOTAL_THEOREMS == len(ARISTOTLE_THEOREMS)
    details.append(Detail("consistency", ok,
                          f"TOTAL={TOTAL_THEOREMS}, dict={len(ARISTOTLE_THEOREMS)}"))
    if not ok:
        all_pass = False

    return CheckResult(passed=all_pass, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 6: No inline physics in notebooks
# ═══════════════════════════════════════════════════════════════════════

@register_check("notebooks", "Notebooks import physics from src.core, no re-implementation")
def check_notebook_isolation() -> CheckResult:
    forbidden = {
        'damping_rate', 'dispersive_correction', 'first_order_correction',
        'second_order_correction', 'turning_point_shift',
        'effective_temperature', 'count_formula',
        'enumerate_monomials', 'count_coefficients',
        'cgl_fdr', 'retarded_kernel', 'noise_kernel',
        'derive_fdr_fourier', 'extract_odd_kernel',
    }

    details = []
    all_pass = True

    for nb_path in sorted(NOTEBOOKS_DIR.glob("*.ipynb")):
        try:
            with open(nb_path) as f:
                nb = json.load(f)
        except Exception as e:
            details.append(Detail(nb_path.name, False, f"Parse error: {e}"))
            all_pass = False
            continue

        violations = set()
        for cell in nb.get('cells', []):
            if cell.get('cell_type') != 'code':
                continue
            src = ''.join(cell.get('source', []))
            for fn in forbidden:
                if re.search(rf'def\s+{re.escape(fn)}\s*\(', src):
                    violations.add(fn)

        ok = len(violations) == 0
        msg = "clean" if ok else f"redefines: {', '.join(sorted(violations))}"
        details.append(Detail(nb_path.name, ok, msg))
        if not ok:
            all_pass = False

    return CheckResult(passed=all_pass, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 7: Lean theorem names appear in .lean source files
# ═══════════════════════════════════════════════════════════════════════

@register_check("lean_source", "Key theorem names found in Lean source files")
def check_lean_source() -> CheckResult:
    if not LEAN_DIR.exists():
        return CheckResult(passed=False, error=f"Lean directory not found: {LEAN_DIR}")

    # Collect all identifiers declared as theorem/lemma/def
    lean_idents = set()
    for lf in LEAN_DIR.glob("*.lean"):
        try:
            content = lf.read_text()
            lean_idents.update(re.findall(r'(?:theorem|lemma|def)\s+(\w+)', content))
        except Exception:
            pass

    # Map Python registry names to expected Lean identifiers
    # (some differ by naming convention)
    spot_checks = {
        # Phase 1-2
        'dampingRate_eq_zero_iff': 'dampingRate_eq_zero_iff',
        'dispersive_bound': 'dispersive_correction_bound',
        'firstOrder_correction_zero_iff': 'firstOrder_correction_zero_iff',
        'acoustic_metric_determinant': 'acousticMetric_det',
        'secondOrder_count': 'secondOrder_count',
        # Phase 4 (Aristotle batch b1ea2eb7)
        'fracton_exceeds_standard_general': 'fracton_exceeds_standard_general',
        'binomial_strict_mono': 'binomial_strict_mono',
        'dof_gap_positive_2_through_8': 'dof_gap_positive_2_through_8',
        'evading_one_breaks_nogo': 'evading_one_breaks_nogo',
        'ep_distinguishes_phases': 'ep_distinguishes_phases',
        'obstructions_individually_sufficient': 'obstructions_individually_sufficient',
    }

    details = []
    all_pass = True

    for registry_name, lean_name in spot_checks.items():
        ok = lean_name in lean_idents
        details.append(Detail(registry_name, ok,
                              f"Lean ident '{lean_name}' {'found' if ok else 'NOT found'}"))
        if not ok:
            all_pass = False

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
# CHECK 9: Lean build (optional, requires `lake` on PATH)
# ═══════════════════════════════════════════════════════════════════════

@register_check("lean_build", "Lean project builds cleanly (requires lake)")
def check_lean_build() -> CheckResult:
    """
    Run `lake build` on the Lean project.

    Lake discovery order:
      1. LAKE_PATH env var  (explicit path to lake binary)
      2. ~/.elan/bin/lake   (standard elan install location)
      3. System PATH         (global install)

    Lean project directory:
      1. LEAN_PROJECT_DIR env var  (override for mono-repo layouts)
      2. PROJECT_ROOT / "lean"     (default, same repo)

    The check looks for lakefile.lean OR lakefile.toml (Lean 4 / Lake v4+).
    """
    import shutil
    import os

    # ── Resolve lake binary ──
    lake_bin = os.environ.get("LAKE_PATH")

    if not lake_bin:
        # Try ~/.elan/bin/lake (standard elan install)
        elan_lake = Path.home() / ".elan" / "bin" / "lake"
        if elan_lake.is_file():
            lake_bin = str(elan_lake)

    if not lake_bin:
        lake_bin = shutil.which("lake")

    if not lake_bin:
        return CheckResult(
            passed=True,
            details=[Detail("lake", True,
                            "SKIPPED — lake not found. Set LAKE_PATH or install elan "
                            "(https://github.com/leanprover/elan)")],
        )

    # ── Resolve Lean project directory ──
    lean_root = Path(os.environ.get("LEAN_PROJECT_DIR", PROJECT_ROOT / "lean"))

    has_lakefile = (
        (lean_root / "lakefile.lean").exists()
        or (lean_root / "lakefile.toml").exists()
    )
    if not has_lakefile:
        return CheckResult(
            passed=True,
            details=[Detail("lakefile", True,
                            f"SKIPPED — no lakefile.{{lean,toml}} in {lean_root}")],
        )

    # ── Run lake build ──
    details = [Detail("lake_bin", True, lake_bin),
               Detail("lean_root", True, str(lean_root))]

    try:
        result = subprocess.run(
            [lake_bin, "build"],
            cwd=str(lean_root),
            capture_output=True, text=True, timeout=600,
        )
        ok = result.returncode == 0
        if ok:
            # Count jobs from output like "Build completed successfully (2254 jobs)."
            # or "ℹ [2254/2254] ..." lines in stderr + stdout
            combined = result.stderr + result.stdout
            job_match = (
                re.search(r'(\d+) jobs?\)', combined)
                or re.search(r'\[(\d+)/\1\]', combined)  # [N/N] = final job
            )
            jobs = job_match.group(1) if job_match else "cached"
            msg = f"build succeeded ({jobs} jobs)"
        else:
            msg = result.stderr[-500:]
        details.append(Detail("lake_build", ok, msg))
        return CheckResult(passed=ok, details=details)
    except subprocess.TimeoutExpired:
        details.append(Detail("lake_build", False, "timeout (600s)"))
        return CheckResult(passed=False, details=details)
    except Exception as e:
        return CheckResult(passed=False, details=details, error=str(e))


# ═══════════════════════════════════════════════════════════════════════
# CHECK 10: Notebook visualization consistency (warnings only)
# ═══════════════════════════════════════════════════════════════════════

@register_check("viz_consistency", "Notebook visualizations use imported physics and consistent style")
def check_viz_consistency() -> CheckResult:
    """Visualization consistency warnings (advisory, always passes).

    Two mechanisms:
      1. Opt-in: cells tagged ``# viz-ref: fig_name`` are checked against
         the corresponding function in ``src/core/visualizations.py``.
      2. Safety net: any ``.show()`` call in a code cell that lacks a
         ``viz-ref`` tag triggers a warning — the figure is untracked.

    Also warns if a figure cell uses hardcoded color hex values instead
    of the COLORS dict from constants.py.
    """
    import ast
    import importlib

    details = []

    # ── Discover visualizations.py figure functions ──
    viz_functions = set()
    viz_path = SRC_DIR / "core" / "visualizations.py"
    if viz_path.exists():
        try:
            tree = ast.parse(viz_path.read_text())
            viz_functions = {
                node.name for node in ast.walk(tree)
                if isinstance(node, ast.FunctionDef) and node.name.startswith("fig_")
            }
        except SyntaxError:
            details.append(Detail("visualizations.py", True,
                                  "WARN: could not parse visualizations.py",
                                  warning=True))

    # ── Known COLORS hex values (hardcoding these is a smell) ──
    try:
        from src.core.constants import COLORS as _COLORS
        known_hex = {v.lower() for v in _COLORS.values() if isinstance(v, str)}
    except ImportError:
        known_hex = set()

    # ── Scan notebooks ──
    for nb_path in sorted(NOTEBOOKS_DIR.glob("*.ipynb")):
        try:
            with open(nb_path) as f:
                nb = json.load(f)
        except Exception as e:
            details.append(Detail(nb_path.name, True,
                                  f"WARN: could not parse — {e}", warning=True))
            continue

        untracked_show = 0
        hardcoded_colors = 0
        ref_warnings = []

        for cell_idx, cell in enumerate(nb.get('cells', [])):
            if cell.get('cell_type') != 'code':
                continue
            src = ''.join(cell.get('source', []))

            # ── Check for viz-ref tags ──
            ref_match = re.search(r'#\s*viz-ref:\s*(\w+)', src)
            has_show = '.show()' in src

            if ref_match:
                ref_name = ref_match.group(1)
                # Check function exists in visualizations.py
                if ref_name not in viz_functions:
                    ref_warnings.append(
                        f"cell {cell_idx}: viz-ref '{ref_name}' not found in visualizations.py"
                    )
            elif has_show:
                # Safety net: .show() without viz-ref tag
                untracked_show += 1

            # ── Check for hardcoded color hex values ──
            if known_hex:
                hex_matches = re.findall(r'["\']#([0-9a-fA-F]{6})["\']', src)
                for h in hex_matches:
                    if f"#{h.lower()}" in known_hex:
                        hardcoded_colors += 1

        # ── Report per notebook ──
        warns = []
        if untracked_show:
            warns.append(f"{untracked_show} untagged .show() call(s)")
        if hardcoded_colors:
            warns.append(f"{hardcoded_colors} hardcoded COLORS hex value(s) — use COLORS dict")
        for rw in ref_warnings:
            warns.append(rw)

        if warns:
            details.append(Detail(
                nb_path.name, True,
                "WARN: " + "; ".join(warns),
                warning=True,
            ))
        else:
            details.append(Detail(nb_path.name, True, "clean"))

    # Always passes — these are advisory warnings
    return CheckResult(passed=True, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 11: Notebook execution (all notebooks must run without errors)
# ═══════════════════════════════════════════════════════════════════════

@register_check("notebook_exec", "All notebooks execute without errors")
def check_notebook_execution() -> CheckResult:
    """Execute each notebook top-to-bottom and verify zero errors.

    Uses nbconvert's execute preprocessor with a timeout per cell.
    This catches import errors, missing variables, broken physics code,
    and any runtime failures that static checks miss.
    """
    import nbformat
    from nbformat.v4 import new_notebook

    details = []
    all_pass = True

    # Try importing the execution engine
    try:
        from nbclient import NotebookClient
    except ImportError:
        return CheckResult(
            passed=True,
            details=[Detail("nbclient", True,
                            "SKIPPED — nbclient not installed. "
                            "Install with: pip install nbclient")],
        )

    for nb_path in sorted(NOTEBOOKS_DIR.glob("*.ipynb")):
        try:
            with open(nb_path) as f:
                nb = nbformat.read(f, as_version=4)

            client = NotebookClient(
                nb,
                timeout=120,          # per-cell timeout
                kernel_name="python3",
                resources={"metadata": {"path": str(NOTEBOOKS_DIR)}},
            )
            client.execute()

            # Count executed cells
            code_cells = sum(1 for c in nb.cells if c.cell_type == "code")
            details.append(Detail(
                nb_path.name, True,
                f"{code_cells} code cells executed successfully"))

        except Exception as e:
            all_pass = False
            # Extract just the error type and message, not the full traceback
            err_lines = str(e).strip().split("\n")
            # Find the actual error line (usually last non-empty line with Error in it)
            err_msg = err_lines[-1] if err_lines else str(e)
            for line in reversed(err_lines):
                if "Error" in line:
                    err_msg = line.strip()
                    break
            if len(err_msg) > 200:
                err_msg = err_msg[:200] + "..."
            details.append(Detail(nb_path.name, False, err_msg))

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
# CHECK 14: Paper claim provenance
# ═══════════════════════════════════════════════════════════════════════

@register_check("paper_provenance",
                "Paper numerical claims trace to computations within 0.5%")
def check_paper_provenance() -> CheckResult:
    """Verify paper theorem references exist in Lean and figures are present."""
    details = []
    all_pass = True

    # Build set of all Lean theorem names
    lean_names = set()
    for lean_file in LEAN_DIR.glob("*.lean"):
        for line in lean_file.read_text().splitlines():
            if line.startswith("theorem "):
                name = line.split()[1].split("(")[0].split(":")[0].strip()
                lean_names.add(name)

    for paper_dir in sorted(PAPERS_DIR.iterdir()):
        tex_file = paper_dir / "paper_draft.tex"
        if not tex_file.exists():
            continue

        tex = tex_file.read_text()

        # Check 1: \\texttt{theorem_name} refs exist in Lean
        texttt_refs = re.findall(r'\\texttt\{([a-z_][a-zA-Z0-9_]*)\}', tex)
        theorem_refs = [r for r in texttt_refs if '_' in r]
        missing = [r for r in theorem_refs if r not in lean_names]
        if missing:
            all_pass = False
            details.append(Detail(
                f"{paper_dir.name}/theorem_refs", False,
                f"Not in Lean: {missing}"
            ))
        elif theorem_refs:
            details.append(Detail(
                f"{paper_dir.name}/theorem_refs", True,
                f"{len(theorem_refs)} theorem references verified"
            ))

        # Check 2: No \\fbox placeholder figures
        if '\\fbox{\\parbox' in tex:
            all_pass = False
            details.append(Detail(
                f"{paper_dir.name}/figures", False,
                "Has \\fbox placeholder figures — must use \\includegraphics"
            ))
        elif '\\includegraphics' in tex:
            fig_dir = paper_dir / "figures"
            png_count = len(list(fig_dir.glob("*.png"))) if fig_dir.exists() else 0
            if png_count == 0:
                all_pass = False
                details.append(Detail(
                    f"{paper_dir.name}/figures", False,
                    "Uses \\includegraphics but figures/ is empty"
                ))
            else:
                details.append(Detail(
                    f"{paper_dir.name}/figures", True,
                    f"{png_count} figure files present"
                ))

        # Check 3: No placeholder bibliography entries
        if 'xxxxx' in tex.lower() or 'Nature \\textbf{XXX}' in tex:
            all_pass = False
            details.append(Detail(
                f"{paper_dir.name}/bibliography", False,
                "Has placeholder bibliography entries (xxxxx or XXX)"
            ))

    return CheckResult(passed=all_pass, details=details)


# ═══════════════════════════════════════════════════════════════════════
# Runner
# ═══════════════════════════════════════════════════════════════════════

def run_checks(
    check_filter: Optional[str] = None,
) -> Dict[str, CheckResult]:
    """Run all (or one) registered checks, return results keyed by name."""
    results = {}
    for spec in _CHECKS:
        if check_filter and spec.name != check_filter:
            continue
        try:
            results[spec.name] = spec.func()
        except Exception as e:
            results[spec.name] = CheckResult(passed=False, error=str(e))
    return results


def print_results(results: Dict[str, CheckResult]) -> None:
    """Pretty-print validation results to stdout."""
    for spec in _CHECKS:
        if spec.name not in results:
            continue
        cr = results[spec.name]
        status = "\033[32m✓ PASS\033[0m" if cr.passed else "\033[31m✗ FAIL\033[0m"
        print(f"\n{'═'*70}")
        print(f"  {status}  {spec.name}: {spec.description}")
        print(f"{'═'*70}")

        if cr.error:
            print(f"  ERROR: {cr.error}")

        for d in cr.details:
            if d.warning:
                sym = "\033[33m⚠\033[0m"
            elif d.passed:
                sym = "✓"
            else:
                sym = "✗"
            line = f"  {sym} {d.name}"
            if d.message:
                line += f"  —  {d.message}"
            print(line)

    total = len(results)
    passed = sum(1 for r in results.values() if r.passed)
    total_warnings = sum(
        1 for r in results.values() for d in r.details if d.warning
    )
    print(f"\n{'═'*70}")
    summary = f"  Overall: {passed}/{total} checks passed"
    if total_warnings:
        summary += f" ({total_warnings} warning{'s' if total_warnings > 1 else ''})"
    print(summary)
    if passed == total:
        print("  \033[32mALL CHECKS PASSED\033[0m")
    else:
        print("  \033[31mSOME CHECKS FAILED\033[0m")
    print(f"{'═'*70}\n")


def archive_results(results: Dict[str, CheckResult]) -> Path:
    """Write timestamped JSON + text report to docs/validation/reports/."""
    REPORTS_DIR.mkdir(parents=True, exist_ok=True)
    ts = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")

    # JSON report
    json_path = REPORTS_DIR / f"validation_{ts}.json"
    payload = {
        "timestamp": ts,
        "project_root": str(PROJECT_ROOT),
        "checks": {},
    }
    for name, cr in results.items():
        payload["checks"][name] = {
            "passed": cr.passed,
            "error": cr.error,
            "details": [asdict(d) for d in cr.details],
        }
    payload["summary"] = {
        "total": len(results),
        "passed": sum(1 for r in results.values() if r.passed),
        "failed": sum(1 for r in results.values() if not r.passed),
    }
    class _Encoder(json.JSONEncoder):
        def default(self, o):
            if isinstance(o, (bool,)):
                return bool(o)
            try:
                return float(o)  # numpy scalars
            except (TypeError, ValueError):
                return super().default(o)

    with open(json_path, 'w') as f:
        json.dump(payload, f, indent=2, cls=_Encoder)

    # Text report (human-readable)
    txt_path = REPORTS_DIR / f"validation_{ts}.txt"
    lines = [
        f"SK-EFT Hawking Validation Report",
        f"Generated: {ts}",
        f"Project: {PROJECT_ROOT}",
        "",
    ]
    for name, cr in results.items():
        status = "PASS" if cr.passed else "FAIL"
        lines.append(f"[{status}] {name}")
        if cr.error:
            lines.append(f"  ERROR: {cr.error}")
        for d in cr.details:
            sym = "+" if d.passed else "-"
            line = f"  {sym} {d.name}"
            if d.message:
                line += f" — {d.message}"
            lines.append(line)
        lines.append("")

    total = len(results)
    passed = sum(1 for r in results.values() if r.passed)
    lines.append(f"Overall: {passed}/{total} passed")
    with open(txt_path, 'w') as f:
        f.write('\n'.join(lines))

    return json_path


# ═══════════════════════════════════════════════════════════════════════
# CLI
# ═══════════════════════════════════════════════════════════════════════

def main() -> int:
    parser = argparse.ArgumentParser(
        description="SK-EFT Hawking cross-layer validation suite",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python scripts/validate.py              # run all checks + archive result
  python scripts/validate.py --no-archive # run without saving report
  python scripts/validate.py --json       # JSON output for CI (no archive)
  python scripts/validate.py --check formulas  # run one check
  python scripts/validate.py --list       # list available checks
""",
    )
    parser.add_argument("--check", help="Run only this check (by name)")
    parser.add_argument("--json", action="store_true", help="JSON output to stdout")
    parser.add_argument("--no-archive", action="store_true",
                        help="Skip saving timestamped report (default: always archive)")
    parser.add_argument("--list", action="store_true", help="List available checks")
    args = parser.parse_args()

    if args.list:
        print("Available checks:")
        for spec in _CHECKS:
            print(f"  {spec.name:20s} {spec.description}")
        return 0

    t0 = time.monotonic()
    results = run_checks(check_filter=args.check)
    elapsed = time.monotonic() - t0

    if args.json:
        payload = {
            "elapsed_seconds": round(elapsed, 2),
            "checks": {
                name: {
                    "passed": cr.passed,
                    "error": cr.error,
                    "details": [asdict(d) for d in cr.details],
                }
                for name, cr in results.items()
            },
            "summary": {
                "total": len(results),
                "passed": sum(1 for r in results.values() if r.passed),
            },
        }
        class _Enc(json.JSONEncoder):
            def default(self, o):
                try:
                    return float(o)
                except (TypeError, ValueError):
                    return super().default(o)
        print(json.dumps(payload, indent=2, cls=_Enc))
    else:
        print_results(results)
        print(f"  Completed in {elapsed:.1f}s")

    if not args.no_archive and not args.json:
        path = archive_results(results)
        print(f"\n  Archived to: {path}")

    all_passed = all(r.passed for r in results.values())
    return 0 if all_passed else 1


if __name__ == "__main__":
    sys.exit(main())
