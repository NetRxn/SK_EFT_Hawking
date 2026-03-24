"""Tests for the second-order SK-EFT analysis modules.

Validates:
1. Transport coefficient counting (matches Lean proofs)
2. Coefficient data structures and constraints
3. WKB connection formula reproduces known limits
"""

import numpy as np
import pytest
from src.second_order.enumeration import analyze_order, DerivIndex
from src.second_order.coefficients import (
    FirstOrderCoeffs,
    SecondOrderCoeffs,
    FullCoeffs,
    hawking_correction_first_order,
    hawking_correction_second_order,
)
from src.second_order.wkb_analysis import (
    TransonicProfile,
    WKBParameters,
    connection_formula,
    steinhauer_params,
)


class TestEnumeration:
    """Test transport coefficient counting against Lean proofs."""

    def test_first_order_gives_two(self):
        """count(1) = 2 — validated by Lean firstOrder_uniqueness."""
        r = analyze_order(1, verbose=False)
        assert r.n_transport_no_parity == 2

    def test_second_order_gives_two(self):
        """count(2) = 2 new — validated by Lean secondOrder_count."""
        r = analyze_order(2, verbose=False)
        assert r.n_transport_no_parity == 2

    def test_second_order_parity_gives_zero(self):
        """count(2, parity) = 0 — validated by Lean secondOrder_count_with_parity."""
        r = analyze_order(2, verbose=False)
        assert r.n_transport_with_parity == 0

    def test_third_order_gives_three(self):
        """count(3) = 3 — validated by Lean thirdOrder_count."""
        r = analyze_order(3, verbose=False)
        assert r.n_transport_no_parity == 3

    def test_general_formula(self):
        """count(N) = floor((N+1)/2) + 1 for N = 1..6."""
        for N in range(1, 7):
            r = analyze_order(N, verbose=False)
            expected = (N + 1) // 2 + 1
            assert r.n_transport_no_parity == expected, (
                f"count({N}) = {r.n_transport_no_parity}, expected {expected}"
            )


class TestCoefficients:
    """Test coefficient data structures and action constructors."""

    def test_first_order_positivity(self):
        """gamma_1, gamma_2 must be non-negative."""
        with pytest.raises(ValueError):
            FirstOrderCoeffs(gamma_1=-1.0, gamma_2=0.5)
        with pytest.raises(ValueError):
            FirstOrderCoeffs(gamma_1=0.5, gamma_2=-1.0)

    def test_correction_vanishes_without_dissipation(self):
        """δ_diss = 0 when γ₁ = γ₂ = 0."""
        delta = hawking_correction_first_order(0.0, 0.0, kappa=1.0, c_s=1.0)
        assert delta == 0.0

    def test_correction_positive(self):
        """δ_diss > 0 for positive transport coefficients."""
        delta = hawking_correction_first_order(0.01, 0.01, kappa=1.0, c_s=1.0)
        assert delta > 0.0

    def test_second_order_frequency_dependent(self):
        """Second-order correction should vary with ω."""
        coeffs = FullCoeffs(
            first=FirstOrderCoeffs(0.01, 0.01),
            second=SecondOrderCoeffs(0.001, 0.001),
        )
        omega_low = 0.1
        omega_high = 1.0
        d_low = hawking_correction_second_order(
            omega_low, coeffs, kappa=1.0, c_s=1.0, v_gradient=1.0)
        d_high = hawking_correction_second_order(
            omega_high, coeffs, kappa=1.0, c_s=1.0, v_gradient=1.0)
        assert abs(d_high) > abs(d_low), "Second-order correction should grow with ω"


class TestWKB:
    """Test WKB connection formula."""

    def test_undamped_gives_hawking_temp(self):
        """Without dissipation, T_eff should equal T_H."""
        profile = TransonicProfile(kappa=1.0, c_s=1.0, xi=0.001)
        params = WKBParameters(profile=profile)  # all gammas = 0
        result = connection_formula(omega=0.5, params=params)
        # T_eff should be close to T_H = κ/(2π)
        T_H = profile.T_H
        assert abs(result.T_eff / T_H - 1.0) < 0.01, (
            f"T_eff/T_H = {result.T_eff/T_H:.4f}, expected ≈ 1.0"
        )

    def test_dissipation_increases_temperature(self):
        """Dissipation should increase T_eff above T_H."""
        profile = TransonicProfile(kappa=1.0, c_s=1.0, xi=0.001)
        params_diss = WKBParameters(profile=profile, gamma_1=0.01, gamma_2=0.01)
        result = connection_formula(omega=0.5, params=params_diss)
        T_H = profile.T_H
        assert result.T_eff > T_H, "Dissipation should increase T_eff"

    def test_steinhauer_preset_loads(self):
        """Steinhauer preset should return valid WKB parameters."""
        params = steinhauer_params()
        assert params.profile.kappa > 0
        assert params.profile.c_s > 0
        assert params.profile.D < 0.5  # adiabatic regime
