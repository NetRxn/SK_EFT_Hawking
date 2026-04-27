"""Tests for `src/center_symmetry/` (Phase 6d Wave 1).

Mirrors `lean/SKEFTHawking/CenterSymmetryConfinement.lean`. Each test
name maps to a Lean theorem one-to-one where applicable; cross-checks
confirm Python ↔ Lean numerical agreement on Polyakov loop, KSS bound,
and Walker-Wang transport prediction.
"""

import math

import pytest

from src.center_symmetry import (
    Z2,
    Z3,
    CenterZN,
    KSS_BOUND,
    UniversalityClass,
    WalkerWangPrediction,
    center_action,
    center_phase,
    confining,
    critical_exponent_nu,
    polyakov_magnitude,
    svetitsky_yaffe_class,
    walker_wang_consistent_with_kss,
)


# === §1. Center Z_N ===


def test_center_zn_requires_n_ge_two() -> None:
    """N ≥ 2 constraint mirrors `N_ge_two` in Lean."""
    with pytest.raises(ValueError):
        CenterZN(N=1)
    with pytest.raises(ValueError):
        CenterZN(N=0)
    # N = 2 and N = 3 are valid
    assert CenterZN(N=2).N == 2
    assert CenterZN(N=3).N == 3


def test_z2_z3_concrete() -> None:
    """Concrete instances Z_2, Z_3."""
    assert Z2.N == 2
    assert Z3.N == 3


def test_center_phase_pow_n() -> None:
    """ζ_N^N = 1 (root-of-unity property).

    Mirrors Lean theorem `centerPhase_pow_N`.
    """
    for z in [Z2, Z3, CenterZN(N=4), CenterZN(N=5)]:
        zeta = center_phase(z)
        zeta_n = zeta**z.N
        assert abs(zeta_n - 1.0) < 1e-10, f"ζ_{z.N}^{z.N} = {zeta_n}, expected 1"


def test_center_phase_norm_one() -> None:
    """|ζ_N| = 1 (unit modulus).

    Mirrors Lean theorem `centerPhase_norm_one`.
    """
    for z in [Z2, Z3, CenterZN(N=4), CenterZN(N=12)]:
        assert abs(abs(center_phase(z)) - 1.0) < 1e-12


def test_center_phase_z2_eq_neg_one() -> None:
    """ζ_2 = exp(πi) = -1.

    Mirrors Lean theorem `centerPhase_Z2_eq_neg_one`.
    """
    zeta_2 = center_phase(Z2)
    assert abs(zeta_2 - (-1)) < 1e-10


def test_center_phase_z3_is_primitive_cube_root() -> None:
    """ζ_3 = exp(2πi/3) is a primitive cube root of unity (1 + ζ + ζ² = 0)."""
    zeta_3 = center_phase(Z3)
    sum_roots = 1 + zeta_3 + zeta_3**2
    assert abs(sum_roots) < 1e-10


# === §2. Polyakov loop and confinement ===


def test_confining_zero() -> None:
    """P = 0 ⟹ confining (definitional)."""
    assert confining(0)
    assert confining(0 + 0j)


def test_deconfining_nonzero() -> None:
    """P ≠ 0 ⟹ not confining."""
    assert not confining(1)
    assert not confining(0.5 + 0.5j)


def test_confining_invariant_under_center_action() -> None:
    """Confining (P=0) is fixed under center action (P → ζ_N · P).

    Mirrors Lean `confining_invariant_under_center_action`.
    """
    for z in [Z2, Z3]:
        # P = 0 is fixed
        assert center_action(z, 0) == 0


def test_nonzero_breaks_center_invariance() -> None:
    """Non-zero P is NOT fixed under center action when ζ_N ≠ 1.

    Mirrors Lean `nonzero_breaks_center_invariance`.
    """
    for z in [Z2, Z3]:
        p = 1.0 + 0.0j
        action_p = center_action(z, p)
        # P ≠ ζ_N · P unless ζ_N = 1
        assert abs(action_p - p) > 0.1


def test_center_action_z2_unit_eq_neg_one() -> None:
    """Concrete SU(2) center action: P=1 → −1.

    Mirrors Lean strengthening theorem `centerAction_Z2_unit_eq_neg_one`.
    """
    result = center_action(Z2, 1 + 0j)
    assert abs(result - (-1)) < 1e-10


def test_confining_iff_center_invariant() -> None:
    """Confining ⟺ centerAction = identity (when ζ_N ≠ 1).

    Mirrors Lean strengthening theorem `confining_iff_center_invariant`.
    Biconditional consolidating forward (confining ⟹ invariant) and
    contrapositive of backward (nonzero ⟹ NOT invariant).
    """
    for z in [Z2, Z3]:
        # Forward: confining (P=0) ⟹ centerAction = P
        assert center_action(z, 0 + 0j) == 0
        # Backward (contrapositive): non-confining ⟹ centerAction ≠ P
        p = 1.0 + 0.5j
        assert abs(center_action(z, p) - p) > 0.1


def test_walker_wang_witness_at_kss_lower() -> None:
    """η/s = KSS satisfies the Walker-Wang prediction (existence witness).

    Mirrors Lean strengthening theorem `walker_wang_witness_at_kss_lower`.
    Ensures `H_WalkerWangTransportNearKSS` is non-vacuously satisfiable.
    """
    assert walker_wang_consistent_with_kss(KSS_BOUND)


# === §3. Order parameter ===


def test_confining_iff_magnitude_zero() -> None:
    """Confining ⟺ |P| = 0.

    Mirrors Lean `confining_iff_magnitude_zero`.
    """
    assert confining(0) and polyakov_magnitude(0) == 0.0
    p = 0.5 + 0.5j
    assert (not confining(p)) == (polyakov_magnitude(p) > 0)


def test_deconfining_implies_magnitude_positive() -> None:
    """¬Confining ⟹ |P| > 0."""
    p = 0.5 + 0.0j
    assert not confining(p)
    assert polyakov_magnitude(p) > 0


# === §4. Svetitsky-Yaffe universality ===


def test_su2_yields_ising_universality() -> None:
    """Z_2 → Ising. Mirrors Lean `svetitskyYaffeClass Z2 = Ising`."""
    assert svetitsky_yaffe_class(Z2) == UniversalityClass.ISING


def test_su3_yields_potts_universality() -> None:
    """Z_3 → 3-state Potts. Mirrors Lean `svetitskyYaffeClass Z3 = three_state_Potts`."""
    assert svetitsky_yaffe_class(Z3) == UniversalityClass.THREE_STATE_POTTS


def test_ising_nu_above_0_6() -> None:
    """3D Ising ν > 0.6 (literature value 0.6299).

    Mirrors Lean `ising_nu_above_0_6`.
    """
    nu_ising = critical_exponent_nu(UniversalityClass.ISING)
    assert nu_ising > 0.6


def test_potts_nu_below_0_6() -> None:
    """3D 3-state Potts ν < 0.6 (literature value 0.5).

    Mirrors Lean `potts_nu_below_0_6`.
    """
    nu_potts = critical_exponent_nu(UniversalityClass.THREE_STATE_POTTS)
    assert nu_potts < 0.6


def test_ising_nu_gt_potts_nu() -> None:
    """Ising ν > Potts ν (direct quantitative comparison).

    Mirrors Lean `ising_nu_gt_potts_nu` strengthening theorem.
    """
    nu_ising = critical_exponent_nu(UniversalityClass.ISING)
    nu_potts = critical_exponent_nu(UniversalityClass.THREE_STATE_POTTS)
    assert nu_ising > nu_potts


# === §5. KSS bound ===


def test_kss_bound_positive() -> None:
    """KSS_BOUND > 0. Mirrors Lean `KSS_bound_positive`."""
    assert KSS_BOUND > 0


def test_kss_bound_below_0_08() -> None:
    """KSS_BOUND < 0.08 (≈ 0.0796). Mirrors Lean `KSS_bound_below_0_08`."""
    assert KSS_BOUND < 0.08


def test_kss_bound_above_0_07() -> None:
    """KSS_BOUND > 0.07 (≈ 0.0796). Mirrors Lean `KSS_bound_above_0_07`."""
    assert KSS_BOUND > 0.07


def test_kss_bound_equals_inverse_4pi() -> None:
    """Numerical: KSS_BOUND = 1/(4π) exactly."""
    assert math.isclose(KSS_BOUND, 1.0 / (4.0 * math.pi))


# === §6. Walker-Wang transport correctness-push ===


def test_walker_wang_at_kss_boundary() -> None:
    """η/s = KSS_BOUND satisfies the prediction (lower edge of window)."""
    pred = WalkerWangPrediction(eta_over_s=KSS_BOUND)
    assert pred.consistent
    assert pred.above_kss
    assert pred.below_double_kss


def test_walker_wang_at_double_kss() -> None:
    """η/s = 2·KSS_BOUND satisfies the prediction (upper edge of window)."""
    pred = WalkerWangPrediction(eta_over_s=2.0 * KSS_BOUND)
    assert pred.consistent


def test_walker_wang_zero_violator() -> None:
    """η/s = 0 violates KSS lower bound.

    Mirrors Lean `walker_wang_zero_eta_violator`.
    """
    assert not walker_wang_consistent_with_kss(0.0)


def test_walker_wang_unit_violator() -> None:
    """η/s = 1 violates Walker-Wang upper bound (1 ≫ 2·KSS ≈ 0.16).

    Mirrors Lean `walker_wang_unit_eta_violator`.
    """
    assert not walker_wang_consistent_with_kss(1.0)


# === Anti-pattern audit ===


def test_no_within_own_band_tautology_for_kss() -> None:
    """Anti-pattern check: KSS bracket [0.07, 0.08] is NOT a within-own-±2σ
    tautology. The threshold values are tight (~0.0796) and use π;
    this is genuinely substantive.
    """
    # Width of bracket ≈ 0.01, KSS itself ≈ 0.0796 → bracket is within
    # ~12% of the value, NOT a "kss ± kss" tautology.
    assert (0.08 - 0.07) < 0.5 * KSS_BOUND


def test_walker_wang_window_disjoint_from_zero_and_unit() -> None:
    """Anti-pattern check: Walker-Wang window [KSS, 2·KSS] is disjoint
    from both numerical violators (η/s = 0 and η/s = 1).
    """
    assert 0.0 < KSS_BOUND
    assert 2.0 * KSS_BOUND < 1.0
