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


def test_lean_root_imports_all_modules():
    """Verify the root SKEFTHawking.lean imports all 6 modules."""
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
    """Verify no active sorry statements in Lean modules.

    Grep for 'sorry' that is NOT inside a comment (--) or docstring (/-! ... -/).
    This is a heuristic check — `lake build` is the definitive test.
    """
    lean_dir = LEAN_DIR / "SKEFTHawking"
    for lean_file in lean_dir.glob("*.lean"):
        content = lean_file.read_text()
        for i, line in enumerate(content.splitlines(), 1):
            stripped = line.strip()
            # Skip comment lines
            if stripped.startswith("--") or stripped.startswith("/-"):
                continue
            # Skip lines inside block comments (heuristic: contains sorry
            # but also contains -- before it)
            if "sorry" in stripped:
                before_sorry = stripped[:stripped.index("sorry")]
                if "--" in before_sorry:
                    continue
                # Check if this looks like an active sorry
                # (not in a string or comment)
                if stripped == "sorry" or "sorry" in stripped.split("--")[0]:
                    # Allow 'sorry' in string literals
                    if '"sorry"' in stripped or "'sorry'" in stripped:
                        continue
                    pytest.fail(
                        f"Active sorry found in {lean_file.name}:{i}: {stripped}"
                    )


def test_sorry_gap_registry():
    """Verify the Aristotle sorry-gap registry reports 35/35 filled."""
    from src.core.aristotle_interface import SORRY_GAPS
    unfilled = [g for g in SORRY_GAPS if not g.filled]
    assert len(unfilled) == 0, (
        f"{len(unfilled)} unfilled sorry gaps: "
        f"{[g.name for g in unfilled]}"
    )
    assert len(SORRY_GAPS) >= 35, (
        f"Expected ≥35 sorry gaps in registry, got {len(SORRY_GAPS)}"
    )
