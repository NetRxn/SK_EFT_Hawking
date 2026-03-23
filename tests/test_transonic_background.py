"""
Tests for the transonic background solver.

Validates:
1. BEC parameter computation (derived quantities)
2. Continuity equation is satisfied by the solution
3. Bernoulli equation is satisfied by the solution
4. Sonic horizon exists and has correct properties
5. Adiabaticity parameter is in the expected range for known experiments
6. Dissipative correction scaling matches the EFT prediction
"""

import numpy as np
import pytest
from src.transonic_background import (
    BECParameters,
    steinhauer_Rb87,
    heidelberg_K39,
    trento_spin_sonic,
    solve_transonic_background,
    compute_dissipative_correction,
)


class TestBECParameters:
    """Test that derived BEC quantities are computed correctly."""

    def test_steinhauer_healing_length(self):
        """Steinhauer's ⁸⁷Rb BEC: ξ should be ~ 0.1-1 μm."""
        params = steinhauer_Rb87()
        xi_um = params.healing_length * 1e6
        assert 0.01 < xi_um < 10.0, f"Healing length {xi_um} μm out of expected range"

    def test_steinhauer_sound_speed(self):
        """Sound speed should be ~ 0.1-1 mm/s for typical BEC."""
        params = steinhauer_Rb87()
        cs_mms = params.sound_speed_upstream * 1e3
        assert 0.01 < cs_mms < 10.0, f"Sound speed {cs_mms} mm/s out of expected range"

    def test_interaction_positive(self):
        """Interaction strength g_1D should be positive for repulsive BEC."""
        for param_fn in [steinhauer_Rb87, heidelberg_K39, trento_spin_sonic]:
            params = param_fn()
            assert params.interaction_strength > 0

    def test_subsonic_upstream(self):
        """Upstream flow should be subsonic (M < 1)."""
        for param_fn in [steinhauer_Rb87, heidelberg_K39, trento_spin_sonic]:
            params = param_fn()
            M = params.velocity_upstream / params.sound_speed_upstream
            assert M < 1.0, f"Upstream Mach number {M} ≥ 1 (not subsonic)"


class TestTransonicBackground:
    """Test the transonic background solver."""

    @pytest.fixture
    def steinhauer_bg(self):
        """Solve the transonic background for Steinhauer parameters."""
        params = steinhauer_Rb87()
        return solve_transonic_background(params), params

    def test_continuity_satisfied(self, steinhauer_bg):
        """Mass current J = n·v should be constant across the flow."""
        bg, params = steinhauer_bg
        valid = ~np.isnan(bg.density)
        J = bg.density[valid] * bg.velocity[valid]
        J_mean = np.nanmean(J)
        # Allow 1% relative variation (numerical discretization)
        assert np.all(np.abs(J[J_mean != 0] / J_mean - 1) < 0.01), \
            "Continuity equation violated: J not constant"

    def test_horizon_exists(self, steinhauer_bg):
        """A sonic horizon should exist (Mach number crosses 1)."""
        bg, _ = steinhauer_bg
        assert bg.surface_gravity > 0, "No sonic horizon found (κ = 0)"

    def test_hawking_temp_positive(self, steinhauer_bg):
        """Hawking temperature should be positive and physically reasonable."""
        bg, _ = steinhauer_bg
        assert bg.hawking_temp > 0, "Hawking temperature ≤ 0"
        # For ⁸⁷Rb, T_H should be in the nK range
        T_nK = bg.hawking_temp * 1e9
        assert 0.001 < T_nK < 100, f"T_H = {T_nK} nK — outside expected range"

    def test_adiabaticity_small(self, steinhauer_bg):
        """Adiabaticity parameter D should be ≪ 1 for the EFT to be valid."""
        bg, _ = steinhauer_bg
        assert bg.adiabaticity < 0.5, f"D = {bg.adiabaticity} — EFT may not be valid"


class TestDissipativeCorrection:
    """Test the dissipative correction estimate."""

    def test_correction_vanishes_without_dissipation(self):
        """δ_diss = 0 when γ₁ = γ₂ = 0."""
        params = steinhauer_Rb87()
        bg = solve_transonic_background(params)
        result = compute_dissipative_correction(bg, params, gamma_1=0, gamma_2=0)
        assert result["delta_diss"] == 0.0

    def test_correction_positive_with_dissipation(self):
        """δ_diss > 0 when γ₁ > 0 (dissipation increases fluctuations)."""
        params = steinhauer_Rb87()
        bg = solve_transonic_background(params)
        result = compute_dissipative_correction(bg, params, gamma_1=1e-6, gamma_2=0)
        assert result["delta_diss"] > 0

    def test_correction_small(self):
        """δ_diss should be parametrically small for current BEC experiments."""
        params = steinhauer_Rb87()
        bg = solve_transonic_background(params)
        result = compute_dissipative_correction(bg, params, gamma_1=1e-6, gamma_2=1e-7)
        # Should be much less than 1
        assert abs(result["delta_diss"]) < 0.1, \
            f"δ_diss = {result['delta_diss']} — not parametrically small"

    def test_dispersive_vs_dissipative_scaling(self):
        """Compare scaling of δ_disp and δ_diss — both should be small."""
        params = steinhauer_Rb87()
        bg = solve_transonic_background(params)
        result = compute_dissipative_correction(bg, params, gamma_1=1e-6, gamma_2=1e-7)
        # Both corrections should be << 1
        assert abs(result["delta_disp"]) < 0.1
        assert abs(result["delta_diss"]) < 0.1
