#!/usr/bin/env python3
"""
Generate counts.json — the single source of truth for all project counts.

Reads from:
  - lean/lean_deps.json (Lean environment extraction via ExtractDeps.lean)
  - src/ directory tree (Python modules)
  - tests/ directory tree (test files)
  - notebooks/ directory (notebooks)
  - papers/ directory (papers)
  - src/core/visualizations.py (figures)
  - src/core/constants.py (Aristotle registry)

Writes to:
  - docs/counts.json (single source of truth)
  - docs/counts.tex (LaTeX macros for papers)

All documentation, dashboards, and validation checks should read from
docs/counts.json instead of hardcoding counts.

Usage:
    # From project root:
    uv run python scripts/update_counts.py

    # Regenerate lean_deps.json first (if Lean files changed):
    cd lean && lake env lean --run SKEFTHawking/ExtractDeps.lean > lean_deps.json
    cd .. && uv run python scripts/update_counts.py
"""

import json
import subprocess
import sys
from datetime import datetime
from pathlib import Path

PROJECT_ROOT = Path(__file__).parent.parent
LEAN_DIR = PROJECT_ROOT / "lean"
LEAN_DEPS = LEAN_DIR / "lean_deps.json"


def regenerate_lean_deps():
    """Regenerate lean_deps.json from the Lean environment.

    Runs ExtractDeps.lean in interpreted mode (no native linking required).
    The olean is built by `lake build` since ExtractDeps imports the root module.
    """
    print("Regenerating lean_deps.json from Lean environment...")
    tmp_path = Path("/tmp/lean_deps_new.json")
    result = subprocess.run(
        ["lake", "env", "lean", "--run", "SKEFTHawking/ExtractDeps.lean"],
        capture_output=True, text=True, cwd=LEAN_DIR, timeout=600,
    )
    if result.returncode != 0:
        print(f"ERROR: ExtractDeps failed:\n{result.stderr[:500]}")
        print("Hint: run `lake build` first to ensure oleans are current.")
        return False

    # Write to temp then copy (atomic)
    tmp_path.write_text(result.stdout)
    if tmp_path.stat().st_size < 100:
        print(f"ERROR: ExtractDeps produced {tmp_path.stat().st_size} bytes (expected >100KB)")
        return False

    import shutil
    shutil.copy2(tmp_path, LEAN_DEPS)
    print(f"  lean_deps.json regenerated: {LEAN_DEPS.stat().st_size:,} bytes")
    return True
SRC_DIR = PROJECT_ROOT / "src"
TESTS_DIR = PROJECT_ROOT / "tests"
NOTEBOOKS_DIR = PROJECT_ROOT / "notebooks"
PAPERS_DIR = PROJECT_ROOT / "papers"
VIZ_FILE = SRC_DIR / "core" / "visualizations.py"
OUTPUT_JSON = PROJECT_ROOT / "docs" / "counts.json"
OUTPUT_TEX = PROJECT_ROOT / "docs" / "counts.tex"


def count_lean(deps_path: Path) -> dict:
    """Extract Lean counts from lean_deps.json (authoritative, environment-based)."""
    if not deps_path.exists():
        print(f"WARNING: {deps_path} not found. Run ExtractDeps.lean first.")
        return {"error": "lean_deps.json not found"}

    with open(deps_path) as f:
        data = json.load(f)

    theorems = [d for d in data if d["kind"] == "theorem"]
    # Standalone placeholders: theorems whose type is exactly `True`
    # Note: structure field projections like `GappedInterfaceConjecture.gap_exists`
    # also have type containing True but are intentional structure fields, not placeholders.
    # We only count standalone `theorem foo : True := trivial` patterns.
    placeholders = [d for d in theorems if d.get("type") == "True"]
    axioms = [d for d in data if d["kind"] == "axiom"]
    modules = sorted(set(d["module"] for d in data))

    # Sorry detection: declarations whose core axiom deps include sorry-like markers
    # In Lean 4, sorry is an axiom — check axiom_deps_core for 'sorry'
    sorry_deps = [
        d for d in data
        if any("sorry" in str(a).lower() for a in d.get("axiom_deps_core", []))
    ]
    # Also count theorems that directly use sorry (kind == "theorem" with sorry dep)
    sorry_theorems = [d for d in sorry_deps if d["kind"] == "theorem"]

    return {
        "total_declarations": len(data),
        "theorems_total": len(theorems),
        "theorems_substantive": len(theorems) - len(placeholders),
        "theorems_placeholder": len(placeholders),
        "axioms": len(axioms),
        "axiom_names": [a["name"] for a in axioms],
        "sorry_declarations": len(sorry_deps),
        "sorry_theorems": len(sorry_theorems),
        "modules": len(modules),
        "module_names": modules,
        "definitions": len([d for d in data if d["kind"] == "def"]),
        "structures": len([d for d in data if d["kind"] == "structure"]),
        "instances": len([d for d in data if d["kind"] == "instance"]),
        "inductives": len([d for d in data if d["kind"] == "inductive"]),
    }


def count_python() -> dict:
    """Count Python source modules, test files, figures."""
    src_modules = list(SRC_DIR.rglob("*.py"))
    src_modules = [f for f in src_modules if f.name != "__init__.py"]

    test_files = list(TESTS_DIR.glob("test_*.py"))

    notebooks = list(NOTEBOOKS_DIR.glob("*.ipynb")) if NOTEBOOKS_DIR.exists() else []

    papers = list(PAPERS_DIR.glob("paper*/paper_draft.tex")) if PAPERS_DIR.exists() else []

    # Count figure functions
    fig_count = 0
    if VIZ_FILE.exists():
        for line in VIZ_FILE.read_text().splitlines():
            if line.startswith("def fig_"):
                fig_count += 1

    return {
        "python_modules": len(src_modules),
        "test_files": len(test_files),
        "notebooks": len(notebooks),
        "papers": len(papers),
        "figures": fig_count,
    }


def count_aristotle() -> dict:
    """Count Aristotle-proved theorems from the registry."""
    try:
        sys.path.insert(0, str(PROJECT_ROOT))
        from src.core.constants import ARISTOTLE_THEOREMS
        # ARISTOTLE_THEOREMS maps theorem_name -> aristotle_run_id (str)
        # The count of entries IS the count of Aristotle-proved theorems.
        run_ids = set(ARISTOTLE_THEOREMS.values())
        return {
            "aristotle_proved": len(ARISTOTLE_THEOREMS),
            "aristotle_runs": len(run_ids),
        }
    except ImportError:
        return {"aristotle_proved": 0, "aristotle_runs": 0}


def generate_tex(counts: dict, path: Path):
    """Generate LaTeX macros for paper inclusion."""
    lean = counts.get("lean", {})
    python = counts.get("python", {})
    aristotle = counts.get("aristotle", {})

    lines = [
        f"% Auto-generated by update_counts.py — {counts['generated']}",
        f"% Do not edit manually. Run: uv run python scripts/update_counts.py",
        f"\\newcommand{{\\totaltheorems}}{{{lean.get('theorems_total', '?')}}}",
        f"\\newcommand{{\\substantivetheorems}}{{{lean.get('theorems_substantive', '?')}}}",
        f"\\newcommand{{\\placeholdertheorems}}{{{lean.get('theorems_placeholder', '?')}}}",
        f"\\newcommand{{\\axiomcount}}{{{lean.get('axioms', '?')}}}",
        f"\\newcommand{{\\sorrycount}}{{{lean.get('sorry_declarations', '?')}}}",
        f"\\newcommand{{\\leanmodules}}{{{lean.get('modules', '?')}}}",
        f"\\newcommand{{\\pythonmodules}}{{{python.get('python_modules', '?')}}}",
        f"\\newcommand{{\\testfiles}}{{{python.get('test_files', '?')}}}",
        f"\\newcommand{{\\figurecount}}{{{python.get('figures', '?')}}}",
        f"\\newcommand{{\\notebookcount}}{{{python.get('notebooks', '?')}}}",
        f"\\newcommand{{\\papercount}}{{{python.get('papers', '?')}}}",
        f"\\newcommand{{\\aristotleproved}}{{{aristotle.get('aristotle_proved', '?')}}}",
    ]
    path.write_text("\n".join(lines) + "\n")


def main():
    # Regenerate lean_deps.json if stale or missing
    if not LEAN_DEPS.exists() or LEAN_DEPS.stat().st_size < 100:
        if not regenerate_lean_deps():
            print("Proceeding with stale/missing lean_deps.json")
    else:
        # Check if any .lean file is newer than lean_deps.json
        lean_deps_mtime = LEAN_DEPS.stat().st_mtime
        lean_files = list((LEAN_DIR / "SKEFTHawking").glob("*.lean"))
        newest_lean = max(f.stat().st_mtime for f in lean_files) if lean_files else 0
        if newest_lean > lean_deps_mtime:
            print("Lean files changed since last extraction.")
            regenerate_lean_deps()

    lean_counts = count_lean(LEAN_DEPS)
    python_counts = count_python()
    aristotle_counts = count_aristotle()

    counts = {
        "generated": datetime.now().isoformat(),
        "lean_deps_source": str(LEAN_DEPS),
        "lean": lean_counts,
        "python": python_counts,
        "aristotle": aristotle_counts,
    }

    # Write JSON
    OUTPUT_JSON.parent.mkdir(parents=True, exist_ok=True)
    with open(OUTPUT_JSON, "w") as f:
        json.dump(counts, f, indent=2)
    print(f"Counts written to {OUTPUT_JSON}")

    # Write LaTeX
    generate_tex(counts, OUTPUT_TEX)
    print(f"LaTeX macros written to {OUTPUT_TEX}")

    # Summary
    lean = lean_counts
    print(f"\n{'='*50}")
    print(f"PROJECT COUNTS (from Lean environment)")
    print(f"{'='*50}")
    if "error" not in lean:
        print(f"  Theorems: {lean['theorems_total']} ({lean['theorems_substantive']} substantive + {lean['theorems_placeholder']} placeholder)")
        print(f"  Axioms: {lean['axioms']}")
        print(f"  Sorry: {lean['sorry_declarations']} ({lean['sorry_theorems']} theorems + {lean['sorry_declarations'] - lean['sorry_theorems']} defs)")
        print(f"  Modules: {lean['modules']}")
        print(f"  Definitions: {lean['definitions']}")
    print(f"  Python modules: {python_counts['python_modules']}")
    print(f"  Test files: {python_counts['test_files']}")
    print(f"  Figures: {python_counts['figures']}")
    print(f"  Notebooks: {python_counts['notebooks']}")
    print(f"  Papers: {python_counts['papers']}")
    print(f"  Aristotle-proved: {aristotle_counts['aristotle_proved']}")


if __name__ == "__main__":
    main()
