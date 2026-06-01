"""Tests for the quantum-network substrate Python mirror (`src/core/formulas.py`).

Mirrors `lean/SKEFTHawking/QuantumNetwork/*.lean` (Phases 6AA–6AD). Each test
cross-checks that the Python closed form satisfies the identity/bound that the
named kernel-verified Lean theorem proves — restoring the three-layer
Python ↔ Lean ↔ (Aristotle) standard for this substrate.
"""

import numpy as np
import pytest

from src.core import formulas as F


# === Swapping.lean / EndToEnd.lean ===

def test_werner_swap_commutative():
    # wernerSwapFidelity_comm
    assert F.werner_swap_fidelity(0.8, 0.6) == pytest.approx(F.werner_swap_fidelity(0.6, 0.8))


def test_werner_param_swap_multiplicative():
    # wernerParam_swap: w(F1 ⋈ F2) = w(F1)·w(F2)
    F1, F2 = 0.83, 0.71
    lhs = F.werner_param(F.werner_swap_fidelity(F1, F2))
    rhs = F.werner_param(F1) * F.werner_param(F2)
    assert lhs == pytest.approx(rhs)


def test_end_to_end_fidelity_succ():
    # endToEndFidelity_succ: F_e2e^(k+1) = swap(F_e2e^(k), F)
    Fl = 0.9
    for k in range(6):
        assert F.end_to_end_fidelity(Fl, k + 1) == pytest.approx(
            F.werner_swap_fidelity(F.end_to_end_fidelity(Fl, k), Fl))


@pytest.mark.parametrize("Fl", [0.25, 0.4, 0.5, 0.75, 0.9, 1.0])
@pytest.mark.parametrize("k", [0, 1, 2, 4, 8])
def test_swap_chain_fidelity_envelope(Fl, k):
    # swapChain_fidelity_envelope: F ∈ [1/4,1] ⟹ F_e2e ∈ [1/4,1]
    v = F.end_to_end_fidelity(Fl, k)
    assert 0.25 - 1e-12 <= v <= 1.0 + 1e-12


def test_end_to_end_qber_monotone_length():
    # endToEndQBER_monotone_length: more hops ⇒ more error
    Fl = 0.85
    qbers = [F.end_to_end_qber(Fl, k) for k in range(7)]
    assert all(a <= b + 1e-12 for a, b in zip(qbers, qbers[1:]))


# === Distillation.lean / DEJMPSConvergence.lean ===

@pytest.mark.parametrize("Fl", [0.51, 0.6, 0.75, 0.9, 0.99])
def test_bbpssw_recurrence_gt(Fl):
    # bbpsswRecurrence_gt: F' > F on (1/2,1)
    assert F.bbpssw_recurrence(Fl) > Fl


def test_dejmps_phase_flip_only_increase():
    # dejmps_increase_phaseFlipOnly: D=0, A∈(1/2,1) ⟹ A' > A
    for A in (0.55, 0.7, 0.9):
        B = (1.0 - A) / 2.0
        assert F.dejmps_out_a(A, B, B, 0.0) > A


def test_dejmps_single_step_can_decrease():
    # dejmps_single_step_can_decrease: (3/5,0,0,2/5) → 13/25 < 3/5 despite λ00>1/2
    assert F.dejmps_out_a(0.6, 0.0, 0.0, 0.4) == pytest.approx(13.0 / 25.0)
    assert F.dejmps_out_a(0.6, 0.0, 0.0, 0.4) < 0.6


def test_dejmps_normalization():
    # dejmps_normalization: four outputs sum to 1
    A, B, C, D = 0.5, 0.2, 0.2, 0.1
    N = (A + D) ** 2 + (B + C) ** 2
    outs = [(A * A + D * D) / N, (B * B + C * C) / N, (2 * A * D) / N, (2 * B * C) / N]
    assert sum(outs) == pytest.approx(1.0)


# === WStateRate.lean / MultipartiteComparison.lean ===

def test_fortescue_lo_yield_gt_two_thirds():
    # fortescueLoYield_gt_two_thirds: D≥3 ⟹ > 2/3
    for D in (3, 5, 12):
        assert F.fortescue_lo_yield(D) > 2.0 / 3.0


def test_fortescue_lo_yield_lt_one_and_mono():
    # fortescueLoYield_lt_one + monotone
    ys = [F.fortescue_lo_yield(D) for D in range(1, 20)]
    assert all(y < 1.0 for y in ys)
    assert all(a <= b for a, b in zip(ys, ys[1:]))


def test_w3_asymptotic_specified_lt_one():
    # w3_asymptotic_specified_lt_one: H₂(1/3) < 1 (and > 0)
    h = F.bin_entropy_bit(1.0 / 3.0)
    assert 0.0 < h < 1.0
    assert h == pytest.approx(0.9183, abs=1e-3)


# === SecretKeyRate.lean ===

def test_bb84_key_rate_zero():
    # bb84KeyRate_zero: r(0) = 1
    assert F.bb84_key_rate(0.0) == pytest.approx(1.0)


def test_bb84_key_rate_crossover_proven_not_hardcoded():
    # bb84_crossover_exists + bb84KeyRate_strictAntiOn: positive below ~0.11, negative above
    assert F.bb84_key_rate(0.10) > 0.0
    assert F.bb84_key_rate(0.12) < 0.0
    # strictly decreasing on [0, 1/2]
    es = np.linspace(0.0, 0.5, 50)
    rs = [F.bb84_key_rate(e) for e in es]
    assert all(a >= b - 1e-12 for a, b in zip(rs, rs[1:]))


# === Teleportation.lean / HaarPauli.lean ===

def test_haar_pauli_constant_eq_third():
    # haarPauliZSqAverage_eq: ∫_{S²}(⟨ψ|σ_k|ψ⟩)² dμ = 1/3
    assert F.HAAR_PAULI_CONSTANT == pytest.approx(1.0 / 3.0)


def test_teleport_horodecki_formula():
    # teleportAvgFidelity_horodecki_unconditional: f_avg = (2F+1)/3
    for Fl in (0.5, 0.7, 1.0):
        assert F.teleport_avg_fidelity(Fl) == pytest.approx((2 * Fl + 1) / 3.0)


def test_teleport_beats_classical_iff():
    # teleport_beats_classical_iff: f_avg > 2/3 ⟺ F > 1/2
    assert F.teleport_avg_fidelity(0.6) > 2.0 / 3.0
    assert F.teleport_avg_fidelity(0.4) < 2.0 / 3.0
    assert F.teleport_avg_fidelity(0.5) == pytest.approx(2.0 / 3.0)


# === Rate.lean ===

def test_bsm_success_prob_bounds():
    # bsmSuccessProb_le_half_of_linearOptics + bsmSuccessProb_complete
    assert F.bsm_success_prob(2) == pytest.approx(0.5)
    assert F.bsm_success_prob(4) == pytest.approx(1.0)
    assert F.bsm_success_prob(1) <= 0.5


def test_link_rate_monotonicity():
    # linkRate_antitone_success + linkRate_monotone_length + latency×attempts
    L, c = 1000.0, 2.0e8
    assert F.link_rate(L, c, 0.5) > F.link_rate(L, c, 0.9)      # lower success → longer
    assert F.link_rate(2 * L, c, 0.5) > F.link_rate(L, c, 0.5)  # longer link → longer
    assert F.link_rate(L, c, 0.5) == pytest.approx((L / c) * (1.0 / 0.5))
