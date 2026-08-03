"""Notebook checks — ADR-009 Phase 2.

`notebooks` (no re-implemented physics), `viz_consistency` (figure-tracking
advisories) and `notebook_exec` (every notebook runs clean, behind a content-hash
skip-cache).

MOVED VERBATIM from `scripts/validate.py`. Phases 1–2 are provably
behaviour-preserving or they are nothing (ADR-009 D4): no body was edited, no
policy unified, no threshold retuned, no always-pass flipped. The only changes are
the import rewrites below.

THE THREE IMPORT RULES for every module in this package
-------------------------------------------------------
* **Framework** from `validation._registry`, never from `validate` — `validate`
  imports these modules for their registration side-effect, so importing it back
  is a cycle.
* **Paths** from `validate_helpers`, never derived from `__file__`. `__file__`
  here resolves to `scripts/validation/checks/`, so `parent.parent` is
  `scripts/validation` and every artifact lookup silently misses (ADR-009 H1).
  `tests/test_validate_public_surface.py::test_no_check_derives_a_path_from___file__`
  enforces this.
* **Runtime flags** by ATTRIBUTE on `validation._config` (`_cfg.FORCE_NOTEBOOK_REEXEC`),
  never `from ... import FORCE_NOTEBOOK_REEXEC` — an imported copy freezes at import
  time and the flag silently becomes a no-op (ADR-009 H5).

`NOTEBOOK_EXEC_CACHE` lives here because `notebook_exec` is its only consumer. It
is re-exported from `validate` anyway, since the migration contract preserves the
module's external surface rather than reasoning case-by-case about who might be
reading what (ADR-009 D2 item 8).

Registration order is NOT set by this file's position in any import list —
`validate._CANONICAL_ORDER` owns execution order (H3).
"""
from __future__ import annotations

import hashlib
import json
import re
from typing import Dict, List

import validate_helpers as _H
from validation import _config as _cfg
from validation._registry import CheckResult, Detail, register_check

# NO LOCAL PATH ALIASES — reach `_H.<NAME>` at each use. See the note in
# `checks/physics.py` for the defect a module-level copy causes under monkeypatch.

#: Local (git-ignored) skip-cache for the notebook-execution check: maps each
#: vetted notebook to a content hash so unchanged, previously-passed notebooks are
#: not re-executed. Mirrors the Lean `extract_lean_deps.py` hash-skip.
NOTEBOOK_EXEC_CACHE = _H.NOTEBOOKS_DIR / ".notebook_exec_cache.json"


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

    for nb_path in sorted(_H.NOTEBOOKS_DIR.glob("*.ipynb")):
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
    viz_path = _H.SRC_DIR / "core" / "visualizations.py"
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
    for nb_path in sorted(_H.NOTEBOOKS_DIR.glob("*.ipynb")):
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

def _src_core_fingerprint() -> str:
    """SHA-256 (16 hex) of all ``src/core/*.py`` — the physics the notebooks
    import. Any change invalidates the whole CHECK 11 skip-cache, forcing a
    full re-vet (a formulas/constants edit can change notebook outcomes without
    changing notebook content)."""
    hasher = hashlib.sha256()
    src_core = _H.SRC_DIR / "core"
    if src_core.is_dir():
        for fp in sorted(src_core.glob("*.py")):
            hasher.update(fp.read_bytes())
    return hasher.hexdigest()[:16]


def _notebook_code_hash(nb) -> str:
    """SHA-256 (16 hex) of a notebook's code-cell sources. Ignores outputs and
    execution_count (which change on every run) so the hash is stable for an
    otherwise-unchanged notebook."""
    hasher = hashlib.sha256()
    for cell in nb.cells:
        if cell.cell_type == "code":
            hasher.update(cell.source.encode("utf-8"))
    return hasher.hexdigest()[:16]


@register_check("notebook_exec", "All notebooks execute without errors")
def check_notebook_execution() -> CheckResult:
    """Execute each notebook top-to-bottom and verify zero errors.

    Uses nbclient's execute engine with a per-cell timeout. Catches import
    errors, missing variables, broken physics code, and runtime failures that
    static checks miss.

    **Skip-cache (2026-05-28):** unchanged, previously-passed notebooks are
    skipped via a content hash recorded in ``NOTEBOOK_EXEC_CACHE`` (keyed on a
    ``src/core`` fingerprint), mirroring the Lean ``extract_lean_deps.py``
    hash-skip. Without it this check re-executes all ~89 notebooks every run
    (~25 min) — the dominant ``validate.py`` slowness. Pass ``--force-notebooks``
    to bypass the cache and re-execute everything (e.g. after a kernel /
    dependency upgrade that changes outcomes without changing content).
    """
    import nbformat

    details: List[Detail] = []
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

    # Load the skip-cache. A src/core fingerprint mismatch discards it (re-vet
    # all); --force-notebooks ignores it entirely.
    src_fp = _src_core_fingerprint()
    prev_passed: Dict[str, str] = {}
    if NOTEBOOK_EXEC_CACHE.is_file() and not _cfg.FORCE_NOTEBOOK_REEXEC:
        try:
            loaded = json.loads(NOTEBOOK_EXEC_CACHE.read_text())
            if isinstance(loaded, dict) and loaded.get("src_fingerprint") == src_fp:
                prev_passed = loaded.get("passed", {}) or {}
        except (json.JSONDecodeError, OSError):
            prev_passed = {}

    new_passed: Dict[str, str] = {}
    n_skipped = 0

    for nb_path in sorted(_H.NOTEBOOKS_DIR.glob("*.ipynb")):
        try:
            with open(nb_path) as f:
                nb = nbformat.read(f, as_version=4)
        except Exception as e:
            all_pass = False
            details.append(Detail(nb_path.name, False, f"unreadable: {e}"))
            continue

        code_hash = _notebook_code_hash(nb)

        # Skip unchanged, previously-vetted notebooks.
        if not _cfg.FORCE_NOTEBOOK_REEXEC and prev_passed.get(nb_path.name) == code_hash:
            n_skipped += 1
            new_passed[nb_path.name] = code_hash
            details.append(Detail(nb_path.name, True,
                                  "SKIPPED — unchanged, previously vetted"))
            continue

        try:
            client = NotebookClient(
                nb,
                timeout=120,          # per-cell timeout
                kernel_name="python3",
                resources={"metadata": {"path": str(_H.NOTEBOOKS_DIR)}},
            )
            client.execute()

            # Count executed cells
            code_cells = sum(1 for c in nb.cells if c.cell_type == "code")
            details.append(Detail(
                nb_path.name, True,
                f"{code_cells} code cells executed successfully"))
            new_passed[nb_path.name] = code_hash  # record vetted state

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
            # Do NOT record — a failed notebook re-runs next time.

    # Persist the updated cache (only currently-existing, vetted notebooks).
    try:
        NOTEBOOK_EXEC_CACHE.write_text(json.dumps(
            {"src_fingerprint": src_fp, "passed": new_passed},
            indent=2, sort_keys=True))
    except OSError:
        pass

    if n_skipped:
        details.insert(0, Detail(
            "skip_cache", True,
            f"{n_skipped} notebook(s) skipped (unchanged, previously vetted); "
            f"--force-notebooks re-runs all"))

    return CheckResult(passed=all_pass, details=details)
