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
    """Count Python source modules, test files, pytest cases, figures."""
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

    # Pytest collection: total individual test cases (not just file count).
    # Uses --collect-only -q which is much faster than execution.
    pytest_cases = 0
    try:
        result = subprocess.run(
            ["uv", "run", "python", "-m", "pytest", "tests/",
             "--collect-only", "-q", "--no-header"],
            cwd=PROJECT_ROOT, capture_output=True, text=True, timeout=120,
        )
        # pytest -q --collect-only ends with a line like "N tests collected in X.YZs"
        import re
        m = re.search(r"(\d+)\s+tests?\s+collected", result.stdout or result.stderr)
        if m:
            pytest_cases = int(m.group(1))
    except Exception:
        # Keep graceful degradation; 0 indicates "not collected this run"
        pytest_cases = 0

    return {
        "python_modules": len(src_modules),
        "test_files": len(test_files),
        "pytest_cases": pytest_cases,
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


def count_per_section_theorems(lean_path: Path) -> dict:
    """Parse a single Lean file and count `^theorem` declarations per
    `/-! ### Section <label>` block. Returns dict mapping section
    label (string, e.g. "1", "3b", "19") to theorem count. Uses string
    keys so sub-sections like "3b" are distinct from "3".

    Matches the section-header convention
    ``/-! ### Section <label>[.<text>]...`` where ``<label>`` is the
    regex ``\\w+`` (digits + optional letter suffix).
    """
    import re
    if not lean_path.exists():
        return {}
    text = lean_path.read_text()
    section_pat = re.compile(r"^/-!\s*###\s*Section\s+(\w+)", re.MULTILINE)
    matches = list(section_pat.finditer(text))
    per_section: dict = {}
    for i, m in enumerate(matches):
        start = m.end()
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        block = text[start:end]
        label = m.group(1)
        per_section[label] = sum(
            1 for line in block.split("\n") if line.startswith("theorem ")
        )
    per_section["_total"] = sum(1 for line in text.split("\n")
                                if line.startswith("theorem "))
    return per_section


def generate_tex(counts: dict, path: Path):
    """Generate LaTeX macros for paper inclusion."""
    lean = counts.get("lean", {})
    python = counts.get("python", {})
    aristotle = counts.get("aristotle", {})

    # Derived: gap rate as a printable percentage with one decimal
    total_thm = lean.get('theorems_total', 0) or 0
    sorry_cnt = lean.get('sorry_declarations', 0) or 0
    sorry_pct = f"{(100 * sorry_cnt / total_thm):.1f}" if total_thm else "?"

    lines = [
        f"% Auto-generated by update_counts.py — {counts['generated']}",
        f"% Do not edit manually. Run: uv run python scripts/update_counts.py",
        f"\\newcommand{{\\totaltheorems}}{{{lean.get('theorems_total', '?')}}}",
        f"\\newcommand{{\\substantivetheorems}}{{{lean.get('theorems_substantive', '?')}}}",
        f"\\newcommand{{\\placeholdertheorems}}{{{lean.get('theorems_placeholder', '?')}}}",
        f"\\newcommand{{\\axiomcount}}{{{lean.get('axioms', '?')}}}",
        f"\\newcommand{{\\sorrycount}}{{{lean.get('sorry_declarations', '?')}}}",
        f"\\newcommand{{\\sorrypercent}}{{{sorry_pct}}}",
        f"\\newcommand{{\\leanmodules}}{{{lean.get('modules', '?')}}}",
        f"\\newcommand{{\\leandefinitions}}{{{lean.get('definitions', '?')}}}",
        f"\\newcommand{{\\pythonmodules}}{{{python.get('python_modules', '?')}}}",
        f"\\newcommand{{\\testfiles}}{{{python.get('test_files', '?')}}}",
        f"\\newcommand{{\\totaltests}}{{{python.get('pytest_cases', '?')}}}",
        f"\\newcommand{{\\figurecount}}{{{python.get('figures', '?')}}}",
        f"\\newcommand{{\\notebookcount}}{{{python.get('notebooks', '?')}}}",
        f"\\newcommand{{\\papercount}}{{{python.get('papers', '?')}}}",
        f"\\newcommand{{\\aristotleproved}}{{{aristotle.get('aristotle_proved', '?')}}}",
        f"\\newcommand{{\\aristotleruns}}{{{aristotle.get('aristotle_runs', '?')}}}",
    ]

    # --- Per-module macros for papers that cite per-section totals ---
    # FermiHubbardDimer.lean (Phase 5t / Paper 18)
    # Wave groupings (from paper18_doublon_gate/paper_draft.tex Table 1):
    #   W2 Layer-1  (sections 1-4): core defs + T1-T10c + trace corollaries
    #   W3          (section 3b):    symmetry-adapted basis matrix-action
    #   W4 spectrum (sections 5-9):  charpoly, brights, U=0 spectrum
    #   W5 BDI      (sections 10-11): Γ H Γ = -H + projectors
    #   W6A-C       (sections 12-14): EuclideanSpace, OrthoBasis, Householder
    #   W6r2+def    (sections 15, 18): scalar-mult + 6x6 lift
    #   W7+r2       (sections 16-17): Vieta + Lipschitz + superexch bound
    #   W8          (section 19):     Berry-phase sign flip
    fhd_path = LEAN_DIR / "SKEFTHawking" / "FermiHubbardDimer.lean"
    fhd_sec = count_per_section_theorems(fhd_path)
    if fhd_sec:
        lines.append("% --- Paper 18 / Phase 5t per-section counts (FermiHubbardDimer.lean) ---")
        lines.append(f"\\newcommand{{\\fhdTotal}}{{{fhd_sec.get('_total', '?')}}}")
        fhd_w2 = sum(fhd_sec.get(s, 0) for s in ("1", "2", "3", "4"))
        fhd_w3 = fhd_sec.get("3b", 0)
        fhd_w4 = sum(fhd_sec.get(s, 0) for s in ("5", "6", "7", "8", "9"))
        fhd_w5 = sum(fhd_sec.get(s, 0) for s in ("10", "11"))
        fhd_w6abc = sum(fhd_sec.get(s, 0) for s in ("12", "13", "14"))
        fhd_w6_extra = sum(fhd_sec.get(s, 0) for s in ("15", "18"))
        fhd_w7 = sum(fhd_sec.get(s, 0) for s in ("16", "17"))
        fhd_w8 = fhd_sec.get("19", 0)
        lines.append(f"\\newcommand{{\\fhdWaveTwo}}{{{fhd_w2}}}")
        lines.append(f"\\newcommand{{\\fhdWaveThree}}{{{fhd_w3}}}")
        lines.append(f"\\newcommand{{\\fhdWaveFour}}{{{fhd_w4}}}")
        lines.append(f"\\newcommand{{\\fhdWaveFive}}{{{fhd_w5}}}")
        lines.append(f"\\newcommand{{\\fhdWaveSixABC}}{{{fhd_w6abc}}}")
        lines.append(f"\\newcommand{{\\fhdWaveSixExtra}}{{{fhd_w6_extra}}}")
        lines.append(f"\\newcommand{{\\fhdWaveSeven}}{{{fhd_w7}}}")
        lines.append(f"\\newcommand{{\\fhdWaveEight}}{{{fhd_w8}}}")

    # Per-module simple totals for Phase 6a Track C papers (paper26 + paper27).
    # These avoid the "USES MACROS but N count-literal matches" warning for the
    # per-module `N theorems` references in those papers' Lean Formalization
    # sections + abstracts + conclusions.
    def _module_thm_count(rel_path: str) -> int | None:
        p = LEAN_DIR / "SKEFTHawking" / rel_path
        if not p.exists():
            return None
        n = 0
        for ln in p.read_text().splitlines():
            s = ln.lstrip()
            if s.startswith("theorem ") or s.startswith("lemma "):
                n += 1
        return n

    bh_entropy_n = _module_thm_count("BHEntropyMicroscopic.lean")
    bh_thermo_n = _module_thm_count("BHThermodynamicsFourLaws.lean")
    if bh_entropy_n is not None or bh_thermo_n is not None:
        lines.append(
            "% --- Paper 26 / 27 per-module counts (BH entropy + four laws) ---"
        )
        if bh_entropy_n is not None:
            lines.append(
                f"\\newcommand{{\\bhEntropyTotal}}{{{bh_entropy_n}}}"
            )
        if bh_thermo_n is not None:
            lines.append(
                f"\\newcommand{{\\bhThermoTotal}}{{{bh_thermo_n}}}"
            )

    # Per-module + per-test counts for Phase 6 papers (paper32, paper34,
    # paper35, paper36, paper37, paper38, note_rt_ch_bounds). Each paper
    # cites its module's substantive theorem count + the companion
    # pytest case count; macroising them avoids the count-literal drift
    # the claims-reviewer flagged.
    def _module_thm_count_strict(rel_path: str) -> int | None:
        """Count `theorem ` / `lemma ` declarations at column 0 only.

        The lstrip-based variant `_module_thm_count` above can over-count
        because docstring prose containing the word "lemma" at any indent
        matches. For paper-claim macros we want the exact declaration
        count, so anchor to BOL — and skip `/- ... -/` block-comment
        spans so a word-wrapped docstring continuation that happens to
        start with "theorem" / "lemma" at column 0 cannot false-positive
        (caught by claims-reviewer 2026-04-29-0100 on
        EquivalencePrinciple.lean line 538).
        """
        p = LEAN_DIR / "SKEFTHawking" / rel_path
        if not p.exists():
            return None
        n = 0
        in_block = False
        for ln in p.read_text().splitlines():
            stripped = ln.lstrip()
            if in_block:
                if "-/" in ln:
                    in_block = False
                continue
            if stripped.startswith("/-"):
                if "-/" not in stripped[2:]:
                    in_block = True
                continue
            if ln.startswith("theorem ") or ln.startswith("lemma "):
                n += 1
        return n

    def _pytest_count(rel_path: str) -> int | None:
        p = PROJECT_ROOT / "tests" / rel_path
        if not p.exists():
            return None
        n = 0
        for ln in p.read_text().splitlines():
            s = ln.lstrip()
            if s.startswith("def test_"):
                n += 1
        return n

    phase6_modules = [
        # (macro_prefix, lean_module, test_module)
        ("strongCpDe",  "StrongCPTopologicalDE.lean",   "test_strong_cp_de.py"),
        ("ep",          "EquivalencePrinciple.lean",    "test_equivalence_principle.py"),
        ("qecHolography","QECHolographyBridge.lean",    "test_qec_holography.py"),
        ("centerSymm",  "CenterSymmetryConfinement.lean","test_center_symmetry.py"),
        ("chiralSsb",   "ChiralSSB_QCD.lean",           "test_chiral_ssb.py"),
        ("cfl",         "CFLChiralLagrangian.lean",     "test_cfl.py"),
        ("rtCh",        "RTCasiniHuertaBounds.lean",    "test_rt_ch_bounds.py"),
        ("heatKernel",      "HeatKernelExpansion.lean",       "test_heat_kernel.py"),
        ("higherCurvature", "HigherCurvatureStructure.lean",  "test_higher_curvature.py"),
        ("diffInvariance",  "NonlinearDiffInvariance.lean",   "test_diff_invariance.py"),
        ("nonlinearEFE",    "NonlinearEFE.lean",              "test_nonlinear_efe.py"),
        ("microscopicCoefficientMatch", "MicroscopicCoefficientMatch.lean", "test_micro_macro_match.py"),
        ("einsteinCartanExtension", "EinsteinCartanExtension.lean", "test_einstein_cartan.py"),
    ]
    phase6_lines = []
    for prefix, lean_mod, test_mod in phase6_modules:
        thms = _module_thm_count_strict(lean_mod)
        tests_n = _pytest_count(test_mod)
        if thms is not None:
            phase6_lines.append(f"\\newcommand{{\\{prefix}Thms}}{{{thms}}}")
        if tests_n is not None:
            phase6_lines.append(f"\\newcommand{{\\{prefix}Tests}}{{{tests_n}}}")
    if phase6_lines:
        lines.append(
            "% --- Phase 6 per-module + pytest counts "
            "(paper32 / paper34-38 / note_rt_ch_bounds) ---"
        )
        lines.extend(phase6_lines)

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
