"""Verify the Lean project structure and sorry-gap registry integrity.

Replaces the old SK_EFT_Phase2/tests/test_phase1_bridge.py — no more
cross-repo importlib hacks needed.
"""

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
    """Verify lean-toolchain specifies v4.28.0."""
    toolchain = LEAN_DIR / "lean-toolchain"
    assert toolchain.exists(), "Missing lean-toolchain"
    content = toolchain.read_text().strip()
    assert "v4.28.0" in content


def test_no_active_sorry():
    """Verify no active sorry statements in Lean modules except known stubs.

    Checks for 'sorry' outside of line comments (--) and block comments
    (/- ... -/). This is a heuristic check — `lake build` is the
    definitive test.

    Files in SORRY_ALLOWED are awaiting Aristotle proof-filling and are
    expected to contain sorry stubs. Remove from this set as proofs are filled.
    """
    # Sorry stubs pending Aristotle proof-filling (17 sorry across 3 files)
    # Aristotle 6dbc9447 in flight targeting these.
    SORRY_ALLOWED = {
        "Uqsl2AffineHopf.lean",   # 12 sorry (RingQuot typeclass workaround needed)
        "Uqsl3Hopf.lean",         # 3 sorry (same RingQuot pattern)
        "CenterFunctor.lean",     # 2 sorry (needs actual functor construction)
    }

    lean_dir = LEAN_DIR / "SKEFTHawking"
    for lean_file in lean_dir.glob("*.lean"):
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

    17 sorry across 3 files (Uqsl2AffineHopf 12, Uqsl3Hopf 3, CenterFunctor 2).
    Registry tracks 9 unfilled gap GROUPS (some groups contain multiple sorry).
    Aristotle 6dbc9447 in flight targeting all of these.
    """
    from src.core.aristotle_interface import SORRY_GAPS
    unfilled = [g for g in SORRY_GAPS if not g.filled]
    # 9 unfilled sorry gap groups as of April 8, 2026
    # Phase 5d-5f (carried forward):
    #   affine_hopf_relation_respect (12 sorry in Uqsl2AffineHopf)
    #   stimulated_hawking_analysis, rep_uq_fusion_algebraic
    #   center_functor_equivalence, emergent_gravity_coupling_bounds
    # Phase 5i (Uqsl3Hopf):
    #   comulFreeAlg3_respects_rel, counitFreeAlg3_respects_rel
    #   antipodeFreeAlg3_respects_rel, uq3_antipode_squared
    expected_unfilled = {
        "affine_hopf_relation_respect",
        "stimulated_hawking_analysis",
        "rep_uq_fusion_algebraic",
        "center_functor_equivalence",
        "emergent_gravity_coupling_bounds",
        "comulFreeAlg3_respects_rel",
        "counitFreeAlg3_respects_rel",
        "antipodeFreeAlg3_respects_rel",
        "uq3_antipode_squared",
    }
    actual_unfilled = {g.name for g in unfilled}
    assert actual_unfilled == expected_unfilled, (
        f"Unexpected unfilled sorry gaps: "
        f"expected={expected_unfilled}, got={actual_unfilled}"
    )
    assert len(SORRY_GAPS) >= 45, (
        f"Expected ≥45 sorry gaps in registry, got {len(SORRY_GAPS)}"
    )
