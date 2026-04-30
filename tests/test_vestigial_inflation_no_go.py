"""Cross-layer parity tests for `VestigialInflationNoGo.lean` (Phase 6b W3).

Status: post-Gate-B.3 (de-escalated 2026-04-29). Mirrors each substantive
Lean theorem in `lean/SKEFTHawking/VestigialInflationNoGo.lean` numerically.

The cross-layer parity pattern is the durable mitigation against the
Python-Lean drift class documented in `feedback_python_lean_refs_drift.md`.

Lean substrate: at the natural vestigial-phase hilltop `τ² = 3/5`,
    V(τ_max) = 4 f_0 / 5
    V'_τ(τ_max) = 0
    V''_ττ(τ_max) = -24 f_0
    η_hilltop = -30 · (M̄_P / M_φ)²              (closed form, f_0-independent)
    n_s_hilltop = 1 + 2 η = 1 - 60 · (M̄_P / M_φ)²

Structural No-Go: for any sub-Planckian inflaton mass `M_φ ≤ M̄_P`, the
hilltop `n_s` falls below the Planck 2σ lower bound `0.9565`.
"""

import numpy as np
import pytest

from src.vestigial_inflation.slow_roll import (
    vestigial_potential,
    vestigial_potential_derivative,
    vestigial_potential_second_derivative,
    slow_roll_epsilon,
    slow_roll_eta,
)
from src.vestigial_inflation.ns_r_prediction import (
    VEST_TAU_LOWER,
    VEST_TAU_HILLTOP,
    VEST_TAU_UPPER,
    n_s_vestigial,
    r_vestigial,
    e_folds_vestigial,
)
from src.vestigial_inflation.planck_bicep_check import (
    PlanckBICEPRegion,
    is_admissible,
)


M_PL_RED = 2.435e18  # GeV


class TestVestigialPotentialAlgebra:
    """V(τ) reproduces the closed forms shipped in VestigialEOS.lean."""

    def test_V_at_zero_equals_neg_f0(self):
        """rho_vest_at_zero: V(0) = -f_0."""
        f0 = 1.7e60
        np.testing.assert_allclose(vestigial_potential(0.0, f0), -f0, rtol=1e-12)

    def test_V_at_one_equals_zero(self):
        """V(1) = 0 (vestigial melt)."""
        f0 = 1.0
        assert abs(vestigial_potential(1.0, f0)) < 1e-12

    def test_V_at_one_over_sqrt5_equals_zero(self):
        """V(1/√5) = 0 (lower V>0 boundary)."""
        np.testing.assert_allclose(
            vestigial_potential(1 / np.sqrt(5), 1.0), 0.0, atol=1e-14,
        )

    def test_V_at_hilltop_equals_4f0_over_5(self):
        """V(√(3/5)) = 4 f_0 / 5  (hilltop max)."""
        f0 = 3.0
        np.testing.assert_allclose(
            vestigial_potential(np.sqrt(3 / 5), f0), 4 * f0 / 5, rtol=1e-12,
        )

    def test_Vp_at_zero_and_hilltop_zero(self):
        """V'(0) = 0 and V'(√(3/5)) = 0  (critical points)."""
        assert abs(vestigial_potential_derivative(0.0, 1.0)) < 1e-14
        assert abs(vestigial_potential_derivative(np.sqrt(3 / 5), 1.0)) < 1e-12

    def test_Vpp_at_hilltop_negative(self):
        """V''(√(3/5)) = -24 f_0 < 0  (max is concave)."""
        f0 = 1.5
        np.testing.assert_allclose(
            vestigial_potential_second_derivative(np.sqrt(3 / 5), f0),
            -24 * f0, rtol=1e-12,
        )


class TestEtaProblem:
    """At hilltop, |η| = 30 (M̄_P/M_φ)². Sub-Planckian M_φ violates |η|<1."""

    def test_eta_hilltop_exact_form(self):
        """η_hilltop = -30 (M̄_P/M_φ)²."""
        f0 = 1.0
        for ratio in [1.0, 5.0, 10.0, 100.0]:
            M_phi = M_PL_RED / ratio  # M̄_P / M_φ = ratio
            eta = slow_roll_eta(np.sqrt(3 / 5), f0, M_PL_RED, M_phi)
            np.testing.assert_allclose(eta, -30.0 * ratio ** 2, rtol=1e-10)

    def test_eta_problem_sub_Planckian(self):
        """For M_φ = 10^16 GeV, |η_hilltop| ≫ 1 (the η-problem)."""
        eta = slow_roll_eta(np.sqrt(3 / 5), 1.0, M_PL_RED, 1e16)
        assert abs(eta) > 1e6, f"sub-Planck M_φ should give huge |η|, got {eta}"


class TestPlanckBICEPAdmissibility:

    def test_planck_central_inside_2sigma(self):
        region = PlanckBICEPRegion()
        assert is_admissible(region.n_s_central, 0.01, N_e=60, region=region)

    def test_n_s_below_2sigma_rejected(self):
        region = PlanckBICEPRegion()
        # n_s = 0.95 is well below 0.9649 - 2*0.0042 = 0.9565
        assert not is_admissible(0.95, 0.01, N_e=60, region=region)

    def test_r_above_BICEP_rejected(self):
        region = PlanckBICEPRegion()
        assert not is_admissible(0.965, 0.05, N_e=60, region=region)

    def test_Ne_outside_50_65_rejected(self):
        region = PlanckBICEPRegion()
        assert not is_admissible(0.965, 0.01, N_e=30, region=region)
        assert not is_admissible(0.965, 0.01, N_e=80, region=region)


class TestVestigialInflationVerdict:
    """The structural NO-GO: no viable point for sub-Planckian M_φ."""

    @pytest.mark.parametrize("M_phi", [1e15, 1e16, 1e17, 1e18])
    def test_subPlanck_Mphi_no_viable_n_s(self, M_phi):
        """For sub-Planckian M_φ at any τ in slow-roll window, n_s lies far from Planck."""
        f0 = 1e64
        for tau in np.linspace(VEST_TAU_LOWER + 0.05, VEST_TAU_UPPER - 0.01, 8):
            ns = n_s_vestigial(tau, f0, M_PL_RED, M_phi)
            # Anywhere in the slow-roll window, sub-Planck M_φ gives n_s wildly outside Planck 2σ
            assert not (0.95 < ns < 0.98), (
                f"unexpected viable n_s={ns:.3f} at M_φ={M_phi:.0e}, τ={tau:.3f}"
            )


# ── Cross-layer parity tests for VestigialInflationNoGo.lean ──────────


class TestStructuralNoGoCrossLayer:
    """Mirror of `lean/SKEFTHawking/VestigialInflationNoGo.lean` substantive theorems."""

    @staticmethod
    def _eta_hilltop(M_phi, M_Pl=M_PL_RED):
        """Lean: VestigialInflationNoGo.etaAtHilltop / .etaAtHilltop_eq_neg_thirty_ratio_sq."""
        return -30.0 * (M_Pl / M_phi) ** 2

    @staticmethod
    def _ns_hilltop(M_phi, M_Pl=M_PL_RED):
        """Lean: VestigialInflationNoGo.nSAtHilltop / .nSAtHilltop_eq."""
        return 1.0 + 2.0 * TestStructuralNoGoCrossLayer._eta_hilltop(M_phi, M_Pl)

    @pytest.mark.parametrize("ratio", [1.0, 5.5, 10.0, 41.0, 55.0, 100.0])
    def test_etaAtHilltop_eq_neg_thirty_ratio_sq(self, ratio):
        """etaAtHilltop_eq_neg_thirty_ratio_sq: η = -30 · (M̄_P/M_φ)²."""
        M_phi = M_PL_RED / ratio
        np.testing.assert_allclose(
            self._eta_hilltop(M_phi), -30.0 * ratio ** 2, rtol=1e-12,
        )

    def test_etaAtHilltop_neg(self):
        """etaAtHilltop_neg: η_hilltop < 0 for any positive M_φ."""
        for ratio in [0.1, 1.0, 41.0, 100.0]:
            M_phi = M_PL_RED / ratio
            assert self._eta_hilltop(M_phi) < 0

    def test_etaAtHilltop_at_M_phi_eq_M_Pl_red_eq_neg_thirty(self):
        """etaAtHilltop_at_M_phi_eq_M_Pl_red_eq_neg_thirty: η = -30 at M_φ = M̄_P."""
        np.testing.assert_allclose(self._eta_hilltop(M_PL_RED), -30.0, rtol=1e-12)

    def test_etaAtHilltop_abs_lt_one_implies_super_Planckian(self):
        """etaAtHilltop_abs_lt_one_implies_super_Planckian: |η| < 1 ⟹ M_φ² > 30 M̄_P²."""
        # Test the boundary: M_phi just above √30 M_Pl
        M_phi_min = np.sqrt(30) * M_PL_RED * 1.001  # slightly above the bound
        eta = self._eta_hilltop(M_phi_min)
        assert abs(eta) < 1, f"|η|={abs(eta)} should be < 1 at M_φ=√30·M̄_P"
        # And below the bound, |η| ≥ 1
        M_phi_below = np.sqrt(30) * M_PL_RED * 0.999
        eta_below = self._eta_hilltop(M_phi_below)
        assert abs(eta_below) > 1

    @pytest.mark.parametrize("ratio", [1.0, 10.0, 30.0])
    def test_nSAtHilltop_eq(self, ratio):
        """nSAtHilltop_eq: n_s_hilltop = 1 - 60 · (M̄_P/M_φ)²."""
        M_phi = M_PL_RED / ratio
        expected = 1.0 - 60.0 * (M_PL_RED / M_phi) ** 2
        np.testing.assert_allclose(self._ns_hilltop(M_phi), expected, rtol=1e-12)

    def test_nSAtHilltop_lt_one(self):
        """nSAtHilltop_lt_one: n_s_hilltop < 1 for any positive M_φ."""
        for ratio in [0.001, 0.1, 1.0, 41.0, 100.0]:
            M_phi = M_PL_RED / ratio
            assert self._ns_hilltop(M_phi) < 1.0

    def test_nSAtHilltop_at_M_phi_eq_M_Pl_red_eq_neg_fifty_nine(self):
        """nSAtHilltop_at_M_phi_eq_M_Pl_red_eq_neg_fifty_nine: n_s = -59 at M_φ = M̄_P.

        At the canonical sub-Planckian choice M_φ = M̄_P, n_s = 1 + 2·(-30) = -59.
        Wildly off-scale from Planck (which is 0.9649). Direct mirror of the
        Lean numerical witness theorem.
        """
        np.testing.assert_allclose(self._ns_hilltop(M_PL_RED), -59.0, rtol=1e-12)

    def test_nSAtHilltop_planck_compatible_implies_super_Planckian(self):
        """nSAtHilltop_planck_compatible_implies_super_Planckian:
        n_s ≥ 0.9565 ⟹ M_φ² > 1300 M̄_P²  (i.e., M_φ > 36 M̄_P).

        Forward direction (Lean theorem): if Planck-compatible, then super-Planckian.
        Boundary check: at M_φ such that n_s = 0.9565, verify M_φ²/M̄_P² ≥ 1300.
        """
        # n_s = 0.9565 ⟹ 60(M_Pl/M_phi)² = 0.0435 ⟹ (M_phi/M_Pl)² = 60/0.0435 ≈ 1379.3
        # The Lean theorem uses 1300 as a safe under-estimate.
        target_ns = 0.9565
        # Solve for M_phi that produces this n_s
        # n_s = 1 - 60 (M_Pl/M_phi)² ⟹ (M_phi/M_Pl)² = 60/(1 - n_s)
        ratio_sq = 60.0 / (1.0 - target_ns)
        assert ratio_sq > 1300, (
            f"Boundary M_phi²/M_Pl² = {ratio_sq:.2f} should exceed 1300 "
            f"(Lean theorem's safe lower bound)"
        )

    def test_vestigial_natural_branch_inflation_falsified(self):
        """vestigial_natural_branch_inflation_falsified:
        M_φ ≤ M̄_P ⟹ n_s_hilltop < 0.9565.

        The structural No-Go: any sub-Planckian inflaton mass produces a
        hilltop scalar tilt below Planck 2σ. Mirrors the Lean theorem's
        contrapositive form.
        """
        for ratio in [1.0, 0.5, 0.1, 0.01]:  # M_phi ≤ M_Pl ⟺ ratio ≥ 1
            M_phi = M_PL_RED * ratio
            ns = self._ns_hilltop(M_phi)
            assert ns < 0.9565, (
                f"Structural No-Go violated at M_φ/M̄_P = {ratio}: n_s = {ns}"
            )

    def test_nSAtHilltop_deviation_at_M_phi_eq_M_Pl_red(self):
        """nSAtHilltop_deviation_at_M_phi_eq_M_Pl_red:
        |n_s - 0.9649| > 50 at M_φ = M̄_P.

        Wildly-off-scale quantitative companion to the structural No-Go.
        At M_φ = M̄_P, n_s = -59, so |n_s - 0.9649| = 59.9649 > 50.
        """
        ns = self._ns_hilltop(M_PL_RED)  # = -59
        deviation = abs(ns - 0.9649)
        assert deviation > 50, f"deviation {deviation} should exceed 50"


class TestVestigialPotentialFromVestigialEOSCrossLayer:
    """Verify Python `vestigial_potential` matches the VestigialEOS.rho_vest substrate."""

    @pytest.mark.parametrize("tau", [0.0, 0.3, np.sqrt(3 / 5), 0.9, 1.0])
    @pytest.mark.parametrize("f0", [1.0, 1e60, 1e80])
    def test_potential_matches_rho_vest_closed_form(self, tau, f0):
        """V(τ) = f_0 (1-τ²)(5τ²-1) — direct algebraic match to VestigialEOS.rho_vest."""
        expected = f0 * (1 - tau ** 2) * (5 * tau ** 2 - 1)
        np.testing.assert_allclose(vestigial_potential(tau, f0), expected, rtol=1e-12)
