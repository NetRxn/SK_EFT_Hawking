"""
Regression tests for Wave 6v.5 — APM-LDPC rate substrate + hashing bound.

These tests pin the Python mirror of the Lean encoding's substantive
content: the QuEra-Harvard-MIT [[1152, 580, ≤12]] code's rate is
strictly above 1/2 by a concrete integer margin, and the substrate-
level hashing-bound predicate is non-vacuously witnessable at the
representative Komoto-Kasai threshold.

Companion Lean theorems in
`lean/SKEFTHawking/FaultTolerance/APMLdpcHashingBound.lean`:
- `apmLdpc_quEraHarvard_rate_above_half`
- `exactlyHalfRateCode_not_above_half`
- `apmLdpc_quEraHarvard_approaches_hashing_bound`
- `wave_6v_5_substantive_closure`
"""

import os
import pytest
from fractions import Fraction

from src.core.citations import CITATION_REGISTRY


KK_BIBKEY = "KomotoKasai2025APMLDPCHashingBound"


# ─── Citation registry ─────────────────────────────────────────────────


def test_komoto_kasai_bibkey_present():
    bib = CITATION_REGISTRY.get(KK_BIBKEY)
    assert bib is not None, f"Bibkey {KK_BIBKEY} must be in CITATION_REGISTRY."
    assert bib["arxiv"] == "2412.21171"
    assert bib["doi"] == "10.1038/s41534-025-01090-1"
    assert bib["journal"] == "npj Quantum Information"


def test_komoto_kasai_primary_source_cache():
    bib = CITATION_REGISTRY[KK_BIBKEY]
    workspace_root = os.path.dirname(
        os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    )
    path = os.path.join(workspace_root, bib["primary_source_path"])
    assert os.path.exists(path), f"Primary source missing at {path}."
    assert os.path.getsize(path) > 100_000


# ─── QuEra-Harvard-MIT [[1152, 580, ≤12]] rate ─────────────────────────


# Python mirror of the Lean `quEraHarvardMITCode` parameters.
QHM_N_PHYS = 1152
QHM_K_LOG = 580
QHM_D_MIN = 12


def test_quera_harvard_mit_code_rate_above_half():
    """QHM code rate 580/1152 > 1/2 (matches Lean
    `apmLdpc_quEraHarvard_rate_above_half`)."""
    rate = Fraction(QHM_K_LOG, QHM_N_PHYS)
    assert rate > Fraction(1, 2)


def test_quera_harvard_mit_code_rate_concrete_margin():
    """Concrete substantive margin: 580 - ⌊1152/2⌋ = 580 - 576 = 4
    logical qubits above the floor threshold."""
    floor_threshold = QHM_N_PHYS // 2
    margin = QHM_K_LOG - floor_threshold
    assert margin == 4


def test_quera_harvard_mit_code_rate_approximate_value():
    """The rate is approximately 0.5035 (matches the strategy-synthesis
    `≈ 0.5035` text)."""
    rate = QHM_K_LOG / QHM_N_PHYS
    assert 0.503 < rate < 0.504


# ─── Exactly-1/2 falsifier-class ───────────────────────────────────────


@pytest.mark.parametrize("k", [1, 2, 10, 100, 1_000])
def test_exactly_half_rate_code_not_above_half(k):
    """The [[2k, k]] code has rate exactly 1/2 — NOT > 1/2 (matches
    Lean `exactlyHalfRateCode_not_above_half`)."""
    rate = Fraction(k, 2 * k)
    assert rate == Fraction(1, 2)
    assert not (rate > Fraction(1, 2))


# ─── Hashing-bound witness at Komoto-Kasai threshold ───────────────────


def test_quera_harvard_mit_below_komoto_kasai_threshold():
    """The QHM code's rate 580/1152 is at most the representative
    Komoto-Kasai threshold 53/100 (matches Lean
    `apmLdpc_quEraHarvard_approaches_hashing_bound`)."""
    rate = Fraction(QHM_K_LOG, QHM_N_PHYS)
    threshold = Fraction(53, 100)
    assert rate <= threshold


def test_h_2_at_endpoints_and_midpoint():
    """Wave 6v.5b: Python mirror of Lean H_2 = binEntropy / log 2.
    H_2(0) = 0, H_2(1) = 0, H_2(1/2) = 1 (max-entropy point)."""
    import math

    def h_2(p: float) -> float:
        if p == 0 or p == 1:
            return 0.0
        return (-p * math.log(p) - (1 - p) * math.log(1 - p)) / math.log(2)

    assert h_2(0.0) == 0.0
    assert h_2(1.0) == 0.0
    assert abs(h_2(0.5) - 1.0) < 1e-10  # max-entropy point
    assert 0.0 <= h_2(0.1) <= 1.0
    assert 0.0 <= h_2(0.25) <= 1.0


def test_h_2_at_p_one_tenth_substantively_below_capacity_margin():
    """Substantive Komoto-Kasai claim: 1 - H_2(0.1) ≈ 0.531 > 580/1152 ≈ 0.5035."""
    import math

    def h_2(p):
        return (-p * math.log(p) - (1 - p) * math.log(1 - p)) / math.log(2)

    bound_at_p_one_tenth = 1 - h_2(0.1)
    qhm_rate = 580 / 1152
    assert bound_at_p_one_tenth > qhm_rate
    # Concrete margin: bound ≈ 0.531, QHM rate ≈ 0.5035, gap ≈ 0.028
    assert (bound_at_p_one_tenth - qhm_rate) > 0.025


def test_qhm_not_achievable_at_max_entropy_noise():
    """Substantive falsifier (matches Lean `apmLdpc_quEraHarvard_not_achievable_at_one_half_noise`):
    at p=1/2 (maximum-entropy depolarizing noise), the hashing-bound capacity
    1 - H_2(1/2) = 0 strictly excludes any positive-rate code."""
    import math

    def h_2(p):
        if p == 0 or p == 1:
            return 0.0
        return (-p * math.log(p) - (1 - p) * math.log(1 - p)) / math.log(2)

    bound_at_one_half = 1 - h_2(0.5)
    qhm_rate = 580 / 1152
    assert abs(bound_at_one_half) < 1e-10  # capacity vanishes at max-entropy
    assert qhm_rate > bound_at_one_half  # QHM rate strictly exceeds → NOT achievable


def test_komoto_kasai_threshold_substantively_exceeds_qhm_rate():
    """The 53/100 threshold strictly exceeds the QHM rate, so the
    hashing-bound predicate is non-vacuously witnessed."""
    rate = float(Fraction(QHM_K_LOG, QHM_N_PHYS))
    threshold = 0.53
    assert threshold > rate
    # Concrete substantive margin: ~0.0265 below the threshold.
    assert threshold - rate > 0.025
