"""
Regression tests for Wave 6v.1 — Williamson-Yoder gauging-QEC formalization.

These tests pin:
- The CITATION_REGISTRY entry + primary-source cache file are present
  (Pipeline Invariant #11).
- The substrate-level overhead arithmetic matches the Lean encoding
  (Python sanity-check on `W * (Nat.log 2 W + 1)` for representative
  values of W).

The companion Lean theorems live in
`lean/SKEFTHawking/FaultTolerance/GaugingQEC.lean`:
- `gaugingQEC_auxQubit_overhead_le`
- `williamsonYoder_beats_quadratic_for_W_ge_two`
- `quadraticOverhead_not_linear`
- `gaugingQEC_strictly_improves_over_quadratic_at_large_W`
- `wave_6v_1_substantive_closure`
"""

import math
import os
import pytest

from src.core.citations import CITATION_REGISTRY


BIBKEY = "WilliamsonYoder2026GaugingLogicalOperators"


# ─── Citation registry ─────────────────────────────────────────────────


def test_williamson_yoder_bibkey_present():
    bib = CITATION_REGISTRY.get(BIBKEY)
    assert bib is not None, (
        f"Bibkey {BIBKEY} must be in CITATION_REGISTRY (Wave 6v.1)."
    )
    assert bib["arxiv"] == "2410.02213"
    assert bib["doi"] == "10.1038/s41567-026-03220-8"
    assert bib["year"] == 2026
    assert bib["journal"] == "Nat. Phys."


def test_williamson_yoder_primary_source_cache_file_exists():
    """Pipeline Invariant #11."""
    bib = CITATION_REGISTRY[BIBKEY]
    workspace_root = os.path.dirname(
        os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    )
    path = os.path.join(workspace_root, bib["primary_source_path"])
    assert os.path.exists(path), (
        f"Primary source cache file missing at {path}. "
        "Run: curl -sL -o <path> https://arxiv.org/pdf/2410.02213"
    )
    assert os.path.getsize(path) > 100_000, (
        f"Primary source file too small at {path} (<100KB); likely "
        "truncated download."
    )


# ─── Substrate arithmetic sanity (Python cross-check on Lean encoding) ─


def williamson_yoder_aux_qubits(W: int) -> int:
    """Python mirror of Lean `williamsonYoderAuxQubits W := W * (Nat.log 2 W + 1)`.
    Returns the Williamson-Yoder protocol's auxiliary-qubit count for a
    logical operator of weight `W`."""
    if W <= 0:
        return 0
    log2_W = int(math.log2(W))  # ⌊log₂ W⌋ (matches Nat.log 2 W for positive W)
    return W * (log2_W + 1)


def naive_quadratic_aux_qubits(W: int) -> int:
    """Python mirror of Lean `naiveQuadraticAuxQubits W := W * W`."""
    return W * W


@pytest.mark.parametrize(
    "W, expected_wy, expected_naive",
    [
        (1,   1 * 1,   1 * 1),       # log₂ 1 = 0, so W-Y = W * 1 = 1
        (2,   2 * 2,   2 * 2),       # log₂ 2 = 1, so W-Y = 2 * 2 = 4
        (4,   4 * 3,  4 * 4),       # log₂ 4 = 2, so W-Y = 4 * 3 = 12; naive 16
        (8,   8 * 4,   8 * 8),       # log₂ 8 = 3, so W-Y = 8 * 4 = 32; naive 64
        (16, 16 * 5, 16 * 16),       # log₂ 16 = 4, so W-Y = 16 * 5 = 80; naive 256
        (100, 100 * 7, 100 * 100),   # log₂ 100 ≈ 6.64 → ⌊·⌋ = 6, W-Y = 100*7 = 700
    ],
)
def test_williamson_yoder_overhead_matches_lean_encoding(
    W, expected_wy, expected_naive
):
    assert williamson_yoder_aux_qubits(W) == expected_wy
    assert naive_quadratic_aux_qubits(W) == expected_naive


def test_williamson_yoder_beats_quadratic_for_W_ge_three():
    """Substantive contrast: W-Y < naive for W ≥ 3 (the strict-improvement
    regime). The Lean theorem
    `gaugingQEC_strictly_improves_over_quadratic_at_large_W` pins this at
    W = 4 (12 < 16); we extend the regression to more values."""
    for W in [3, 4, 8, 16, 100, 1000, 10000]:
        wy = williamson_yoder_aux_qubits(W)
        naive = naive_quadratic_aux_qubits(W)
        assert wy < naive, f"W={W}: W-Y={wy} should be < naive={naive}"


def test_williamson_yoder_strict_improvement_factor_grows_with_W():
    """The improvement factor naive/W-Y grows logarithmically — at W=1000
    the W-Y overhead is ~90× smaller than naive."""
    factors = {}
    for W in [4, 16, 100, 1000, 10000]:
        wy = williamson_yoder_aux_qubits(W)
        naive = naive_quadratic_aux_qubits(W)
        factors[W] = naive / wy
    # Improvement factors at representative W:
    # W=4: 16/12 = 1.33
    # W=100: 10000/700 ≈ 14.3
    # W=10000: 10^8/(10^4*14) ≈ 714
    assert factors[4] < factors[100] < factors[1000] < factors[10000]
    assert factors[10000] > 500.0


def test_williamson_yoder_at_W_one_is_one():
    """Edge case: at W=1, Nat.log 2 1 = 0, so W-Y = 1 * 1 = 1."""
    assert williamson_yoder_aux_qubits(1) == 1


def test_naive_quadratic_grows_quadratically():
    """Sanity: naive(2W) = 4 * naive(W) — quadratic growth."""
    for W in [1, 2, 3, 10, 100]:
        assert naive_quadratic_aux_qubits(2 * W) == 4 * naive_quadratic_aux_qubits(W)
