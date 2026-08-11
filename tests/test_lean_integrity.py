"""Verify the Lean project structure and sorry-gap registry integrity.

Replaces the old SK_EFT_Phase2/tests/test_phase1_bridge.py — no more
cross-repo importlib hacks needed.
"""

import re
import pytest
from pathlib import Path


# Project root is one level up from tests/
PROJECT_ROOT = Path(__file__).parent.parent
LEAN_DIR = PROJECT_ROOT / "lean"


def test_lean_phase1_modules_exist():
    """Verify Phase 1 Lean modules are present."""
    expected = [
        "SKEFTHawking/Basic.lean",
        "SKEFTHawking/AcousticMetric.lean",
        "SKEFTHawking/SKDoubling.lean",
        "SKEFTHawking/HawkingUniversality.lean",
    ]
    for module in expected:
        path = LEAN_DIR / module
        assert path.exists(), f"Missing Phase 1 Lean module: {path}"


def test_lean_phase2_modules_exist():
    """Verify Phase 2 Lean modules are present."""
    expected = [
        "SKEFTHawking/SecondOrderSK.lean",
        "SKEFTHawking/WKBAnalysis.lean",
    ]
    for module in expected:
        path = LEAN_DIR / module
        assert path.exists(), f"Missing Phase 2 Lean module: {path}"


def test_lean_phase3_modules_exist():
    """Verify Phase 3 Lean modules are present."""
    expected = [
        "SKEFTHawking/ThirdOrderSK.lean",
        "SKEFTHawking/GaugeErasure.lean",
        "SKEFTHawking/WKBConnection.lean",
        "SKEFTHawking/ADWMechanism.lean",
    ]
    for module in expected:
        path = LEAN_DIR / module
        assert path.exists(), f"Missing Phase 3 Lean module: {path}"


def test_lean_phase4_modules_exist():
    """Verify Phase 4 Lean modules are present."""
    expected = [
        "SKEFTHawking/ChiralityWall.lean",
        "SKEFTHawking/VestigialGravity.lean",
        "SKEFTHawking/FractonHydro.lean",
        "SKEFTHawking/FractonGravity.lean",
        "SKEFTHawking/FractonNonAbelian.lean",
    ]
    for module in expected:
        path = LEAN_DIR / module
        assert path.exists(), f"Missing Phase 4 Lean module: {path}"


def test_lean_root_imports_all_modules():
    """Verify the root SKEFTHawking.lean imports all 16 modules."""
    root = LEAN_DIR / "SKEFTHawking.lean"
    assert root.exists(), "Missing root Lean file"
    content = root.read_text()
    expected_imports = [
        "import SKEFTHawking.Basic",
        "import SKEFTHawking.AcousticMetric",
        "import SKEFTHawking.SKDoubling",
        "import SKEFTHawking.SecondOrderSK",
        "import SKEFTHawking.HawkingUniversality",
        "import SKEFTHawking.WKBAnalysis",
        "import SKEFTHawking.CGLTransform",
        "import SKEFTHawking.ThirdOrderSK",
        "import SKEFTHawking.GaugeErasure",
        "import SKEFTHawking.WKBConnection",
        "import SKEFTHawking.ADWMechanism",
        "import SKEFTHawking.ChiralityWall",
        "import SKEFTHawking.VestigialGravity",
        "import SKEFTHawking.FractonHydro",
        "import SKEFTHawking.FractonGravity",
        "import SKEFTHawking.FractonNonAbelian",
    ]
    for imp in expected_imports:
        assert imp in content, f"Root Lean file missing: {imp}"


def test_lakefile_exists():
    """Verify lakefile.toml exists with correct project name."""
    lakefile = LEAN_DIR / "lakefile.toml"
    assert lakefile.exists(), "Missing lakefile.toml"
    content = lakefile.read_text()
    assert "sk-eft-hawking" in content


def test_lean_toolchain():
    """lean-toolchain is well-formed and IN LOCKSTEP with the REPL dep's tag.

    Bumped to v4.32.0 on 2026-07-28 (from v4.29.1) together with Mathlib and
    PhysLib — the three move as one matched set.

    This used to assert a hardcoded version literal, which recorded a number
    without enforcing anything: it had to be hand-edited on every bump, and it
    passed happily while a dep drifted out of lockstep. CLAUDE.md states the
    actual invariant — "if the toolchain bumps, the REPL dep's `rev` must bump
    too" (the REPL is a thin protocol wrapper built against a specific Lean).
    So check THAT, and let the version follow the lakefile instead of a literal.

    Mathlib/PhysLib are pinned by SHA, not tag, so they cannot be compared
    textually here; `lake build` is what enforces their compatibility.
    """
    toolchain = LEAN_DIR / "lean-toolchain"
    assert toolchain.exists(), "Missing lean-toolchain"
    content = toolchain.read_text().strip()
    m = re.fullmatch(r"leanprover/lean4:(v\d+\.\d+\.\d+(?:-rc\d+)?)", content)
    assert m, f"malformed lean-toolchain: {content!r}"
    version = m.group(1)

    lakefile = (LEAN_DIR / "lakefile.toml").read_text()
    repl = re.search(
        r'name\s*=\s*"repl".*?rev\s*=\s*"([^"]+)"', lakefile, re.DOTALL
    )
    assert repl, "no repl [[require]] found in lakefile.toml"
    repl_rev = repl.group(1)
    # The REPL repo has skipped tags before (it went v4.29.0 -> v4.30.0-rc1 with
    # no v4.29.1), so a documented mismatch is allowed — but it must be spelled
    # out in the lakefile comment rather than silently drifting.
    if repl_rev != version:
        assert "skipped" in lakefile or "patch-level compatible" in lakefile, (
            f"lean-toolchain is {version} but the repl dep is pinned to {repl_rev}, "
            "and the lakefile does not document why they differ"
        )


def test_no_active_sorry():
    """Verify no active sorry statements in Lean modules except known stubs.

    Checks for 'sorry' outside of line comments (--) and block comments
    (/- ... -/). This is a heuristic check — `lake build` is the
    definitive test.

    Files in SORRY_ALLOWED are awaiting Aristotle proof-filling and are
    expected to contain sorry stubs. Remove from this set as proofs are filled.
    """
    # All previous sorry stubs were closed during 2026-04-14 Tranche E wrap-up
    # (Uqsl2AffineHopf 12→0, Uqsl3Hopf 3→0, CenterFunctor 2→0). Project was
    # 0-sorry as of 2026-04-15. Any future sorry must either be added here
    # (with tracking rationale) or immediately closed.
    #
    # 2026-07-13 audit (first fast-suite run on main in a while — the June arcs
    # introduced two unregistered stubs; a third, the orphaned never-imported
    # SingularOpenDualityMVConnSquareCore.lean WIP scratch, was deleted):
    SORRY_ALLOWED: set[str] = {
        # Live L2 (Phase-5qF) partial work, parked at a documented resume point
        # (cap-Leibniz Route B; remaining V-link + χ-correction @CrossReal).
        # NOT consumed by any 5q.H module.
        "SingularConnSquareCrossReal.lean",
        # Documented blueprint+sorry (see the module/aggregator docstring):
        # algebraic identities formalized; PDE well-posedness/asymptotics left
        # as flagged stubs queued for Aristotle proof-filling.
        "TetradGapEquation.lean",
    }

    lean_dir = LEAN_DIR / "SKEFTHawking"
    # rglob, not glob (2026-08-06). The non-recursive form scanned 1 372 of 2 038
    # modules — every namespace subdirectory (QuantumNetwork/, GloriosoLiu/,
    # CrooksAnalogHawking/, Resurgence/, …) was unscanned while the test's name
    # promised the whole substrate. Exactly the defect `compute_lean_hash`'s
    # docstring records fixing for the extraction cache; this call site was missed.
    # Widening cost nothing: measured 0 active sorries in the 666 newly-covered
    # files, so the population grew and the verdict did not move.
    lean_files = sorted(lean_dir.rglob("*.lean"))
    assert len(lean_files) > 1500, (
        f"only {len(lean_files)} .lean files found under {lean_dir} — the scan has "
        "silently narrowed, and a scan that matches nothing passes vacuously"
    )
    for lean_file in lean_files:
        # Matched on bare NAME, so an allow-listed file is exempt wherever it sits.
        # Both current entries are top-level and unique; revisit if a subdirectory
        # ever introduces a same-named module.
        if lean_file.name in SORRY_ALLOWED:
            continue
        content = lean_file.read_text()
        in_block_comment = 0  # nesting depth
        for i, line in enumerate(content.splitlines(), 1):
            stripped = line.strip()

            # Track block comment nesting: any line that starts inside
            # a block comment or opens/closes one is skipped
            was_in_block = in_block_comment > 0
            in_block_comment += line.count("/-") - line.count("-/")
            if was_in_block or in_block_comment > 0:
                continue

            # Skip line comments
            if stripped.startswith("--"):
                continue

            if "sorry" in stripped:
                # Only consider text before any inline comment
                code_part = stripped.split("--")[0]
                if "sorry" not in code_part:
                    continue
                # Allow 'sorry' in string literals
                if '"sorry"' in code_part or "'sorry'" in code_part:
                    continue
                pytest.fail(
                    f"Active sorry found in {lean_file.name}:{i}: {stripped}"
                )


def test_sorry_gap_registry():
    """Verify the Aristotle sorry-gap registry state.

    All sorry gaps closed during 2026-04-14 Tranche E wrap-up. The registry
    is retained as historical provenance (run IDs, strategy hints) but no
    entry should remain unfilled. Any future sorry should be registered here
    with `filled=False` until closed.
    """
    from src.core.aristotle_interface import SORRY_GAPS
    unfilled = [g for g in SORRY_GAPS if not g.filled]
    assert unfilled == [], (
        f"Expected 0 unfilled sorry gaps (project is 0-sorry as of 2026-04-15), "
        f"got {len(unfilled)}: {[g.name for g in unfilled]}"
    )
    # Registry still expected to hold >= 45 historical entries as provenance.
    assert len(SORRY_GAPS) >= 45, (
        f"Expected ≥45 sorry gaps in registry (historical), got {len(SORRY_GAPS)}"
    )
