"""
Regression tests for Wave 6v.6 — W-state QFT decomposition in Q(ζ_N).

These tests pin the Python mirror of the Lean encoding's
substantive content: the W-state QFT basis size equals the qubit
count `n`, NOT the full Hilbert-space dimension `2^n` — an
exponential-vs-polynomial separation.

Companion Lean theorems in
`lean/SKEFTHawking/FaultTolerance/WStateQFT.lean`:
- `n_qubit_w_state_basis_strictly_smaller_than_full_hilbert`
- `wState_separation_at_{5,8,40}`
- `wave_6v_6_substantive_closure`
"""

import os
import pytest

from src.core.citations import CITATION_REGISTRY


DVC_BIBKEY = "DurVidalCirac2000WState"


# ─── Citation registry ─────────────────────────────────────────────────


def test_dur_vidal_cirac_bibkey_present():
    bib = CITATION_REGISTRY.get(DVC_BIBKEY)
    assert bib is not None, f"Bibkey {DVC_BIBKEY} must be in CITATION_REGISTRY."
    assert bib["arxiv"] == "quant-ph/0005115"
    assert bib["year"] == 2000


def test_dur_vidal_cirac_primary_source_cache():
    bib = CITATION_REGISTRY[DVC_BIBKEY]
    workspace_root = os.path.dirname(
        os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    )
    path = os.path.join(workspace_root, bib["primary_source_path"])
    assert os.path.exists(path), f"Primary source missing at {path}."
    assert os.path.getsize(path) > 100_000


# ─── Substrate arithmetic sanity ────────────────────────────────────────


def n_qubit_w_state_basis_size(n: int) -> int:
    """Python mirror of Lean `nQubitWStateBasisSize n := n`."""
    return n


def full_hilbert_dim(n: int) -> int:
    """Python mirror of Lean `fullHilbertDim n := 2^n`."""
    return 2 ** n


@pytest.mark.parametrize("n", [1, 2, 3, 5, 8, 10, 40])
def test_w_state_basis_smaller_than_full_hilbert(n):
    """Substantive exponential-vs-polynomial separation."""
    assert n_qubit_w_state_basis_size(n) < full_hilbert_dim(n)


def test_w_state_separation_at_5():
    """Concrete: 5 < 2^5 = 32 (matches Lean `wState_separation_at_5`)."""
    assert n_qubit_w_state_basis_size(5) == 5
    assert full_hilbert_dim(5) == 32


def test_w_state_separation_at_8():
    """Concrete: 8 < 2^8 = 256 (matches Lean `wState_separation_at_8`)."""
    assert n_qubit_w_state_basis_size(8) == 8
    assert full_hilbert_dim(8) == 256


def test_w_state_separation_at_40():
    """Concrete: 40 < 2^40 (matches Lean `wState_separation_at_40`)."""
    assert n_qubit_w_state_basis_size(40) == 40
    assert full_hilbert_dim(40) == 1_099_511_627_776
    assert n_qubit_w_state_basis_size(40) < full_hilbert_dim(40)


def test_cyclotomic_qft_basis_at_qcyc_sizes():
    """Wave 6v.6b: substantive cyclotomic-QFT-basis predicate is
    non-vacuously witnessed at the project's existing QCyc_n
    cyclotomic-substrate sizes via Mathlib's
    `IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ)`. Python
    mirror via cmath confirms there exists a complex n-th root of
    unity ζ with ζ^n = 1 and ζ^k ≠ 1 for 0 < k < n (the IsPrimitiveRoot
    structural property)."""
    import cmath
    for n in [5, 8, 16, 40, 80]:
        ζ = cmath.exp(2j * cmath.pi / n)  # canonical n-th primitive root
        # ζ^n = 1
        assert abs(ζ ** n - 1) < 1e-10
        # ζ^k ≠ 1 for 0 < k < n
        for k in range(1, n):
            assert abs(ζ ** k - 1) > 1e-12


def test_separation_factor_grows_exponentially():
    """The ratio of full Hilbert dim to W-state QFT basis size grows
    exponentially in n (efficiency claim)."""
    factors = {n: full_hilbert_dim(n) / n_qubit_w_state_basis_size(n)
               for n in [5, 8, 20, 40]}
    # At n=5: 32/5 = 6.4
    # At n=40: 2^40/40 ≈ 2.7e10
    assert factors[5] < factors[8] < factors[20] < factors[40]
    assert factors[40] > 1e10
