"""Tests for Dirac fluid analog metric (Phase 5w Wave 2).

Tests cover:
- Sound speed: c_s = v_F/√2 (conformal EOS)
- 3×3 metric: symmetry, signature, horizon condition
- Block-diagonal structure: (t,x) block recovers BEC form
- Hawking temperature: matches geometry estimates
- Dissipation window: ω_H/Γ_mr ratios
- Cross-validation with constants.py platform parameters
"""

import numpy as np
import pytest

from src.core.formulas import (
    dirac_fluid_sound_speed,
    dirac_fluid_metric_3d,
    dirac_fluid_metric_det,
    dirac_fluid_horizon_velocity,
    dirac_fluid_hawking_temperature,
    dirac_fluid_hawking_from_geometry,
    dirac_fluid_dissipation_window,
)
from src.core.constants import (
    HBAR, K_B, V_FERMI_GRAPHENE, GRAPHENE_PLATFORMS,
)


class TestDiracFluidSoundSpeed:
    """Sound speed from conformal EOS: c_s = v_F/√2."""

    def test_monolayer_value(self):
        c_s = dirac_fluid_sound_speed(1.0e6)
        assert abs(c_s - 1.0e6 / np.sqrt(2)) < 1.0

    def test_proportional_to_vF(self):
        """c_s scales linearly with v_F."""
        c_s_1 = dirac_fluid_sound_speed(1.0e6)
        c_s_2 = dirac_fluid_sound_speed(2.0e6)
        assert abs(c_s_2 / c_s_1 - 2.0) < 1e-10

    def test_positive(self):
        assert dirac_fluid_sound_speed(1.0e6) > 0

    def test_less_than_vF(self):
        """c_s < v_F always (subluminal sound)."""
        v_F = 1.0e6
        assert dirac_fluid_sound_speed(v_F) < v_F


class TestDiracFluidMetric3D:
    """3×3 acoustic metric properties."""

    def test_symmetric(self):
        """G_μν = G_νμ."""
        g = dirac_fluid_metric_3d(1e5, 1e6, w=1.0, n=1.0)
        np.testing.assert_array_almost_equal(g, g.T)

    def test_shape(self):
        g = dirac_fluid_metric_3d(1e5, 1e6, w=1.0, n=1.0)
        assert g.shape == (3, 3)

    def test_gtt_vanishes_at_horizon(self):
        """At v = c_s, g_tt = 0."""
        v_F = 1.0e6
        c_s = v_F / np.sqrt(2)
        g = dirac_fluid_metric_3d(c_s, v_F, w=1.0, n=1.0)
        assert abs(g[0, 0]) < 1e-10

    def test_gtt_negative_subsonic(self):
        """For v < c_s, g_tt < 0 (timelike)."""
        v_F = 1.0e6
        c_s = v_F / np.sqrt(2)
        g = dirac_fluid_metric_3d(0.5 * c_s, v_F, w=1.0, n=1.0)
        assert g[0, 0] < 0

    def test_gtt_positive_supersonic(self):
        """For v > c_s, g_tt > 0 (spacelike — inside horizon)."""
        v_F = 1.0e6
        c_s = v_F / np.sqrt(2)
        g = dirac_fluid_metric_3d(1.2 * c_s, v_F, w=1.0, n=1.0)
        assert g[0, 0] > 0

    def test_block_diagonal_y_offdiag(self):
        """g_{ty} = g_{xy} = 0 for quasi-1D flow."""
        g = dirac_fluid_metric_3d(1e5, 1e6, w=1.0, n=1.0)
        assert g[0, 2] == 0.0
        assert g[2, 0] == 0.0
        assert g[1, 2] == 0.0
        assert g[2, 1] == 0.0

    def test_gyy_equals_omega_sq(self):
        """g_yy = Ω² (the conformal factor)."""
        v_F = 1e6
        w = 2.0
        n = 3.0
        c_s = v_F / np.sqrt(2)
        omega_sq = (n / (w * c_s)) ** 2
        g = dirac_fluid_metric_3d(1e5, v_F, w=w, n=n)
        assert abs(g[2, 2] - omega_sq) < 1e-20

    def test_lorentzian_signature_subsonic(self):
        """det(G) < 0 for subsonic flow (Lorentzian signature)."""
        det = dirac_fluid_metric_det(v=1e5, v_F=1e6, w=1.0, n=1.0)
        assert det < 0


class TestHorizonVelocity:
    """v_horizon = c_s = v_F/√2."""

    def test_equals_sound_speed(self):
        v_F = 1e6
        assert abs(dirac_fluid_horizon_velocity(v_F) -
                    dirac_fluid_sound_speed(v_F)) < 1.0

    def test_less_than_vF(self):
        """The horizon is at c_s, NOT at v_F."""
        v_F = 1e6
        assert dirac_fluid_horizon_velocity(v_F) < v_F


class TestHawkingTemperature:
    """Analog Hawking temperature for Dirac fluid."""

    def test_positive(self):
        T_H = dirac_fluid_hawking_temperature(1e12)
        assert T_H > 0

    def test_proportional_to_gradient(self):
        """T_H ∝ |dv/dx|."""
        T1 = dirac_fluid_hawking_temperature(1e12)
        T2 = dirac_fluid_hawking_temperature(2e12)
        assert abs(T2 / T1 - 2.0) < 1e-10

    def test_formula(self):
        """T_H = ℏ|dv/dx|/(2πk_B)."""
        dv_dx = 1e12
        T_H = dirac_fluid_hawking_temperature(dv_dx)
        expected = HBAR * dv_dx / (2 * np.pi * K_B)
        assert abs(T_H - expected) < 1e-10

    def test_dean_nozzle_order_of_magnitude(self):
        """Dean bilayer nozzle: T_H ~ few K."""
        T_H = dirac_fluid_hawking_from_geometry(200e-9, v_F=1e6)
        assert 1.0 < T_H < 20.0  # should be ~4 K for monolayer

    def test_much_larger_than_bec(self):
        """Graphene T_H >> BEC T_H (by ~9 orders of magnitude)."""
        T_graphene = dirac_fluid_hawking_from_geometry(200e-9)
        T_bec = HBAR * 100 / (2 * np.pi * K_B)  # BEC: |dv/dx| ~ 100 s⁻¹
        assert T_graphene / T_bec > 1e7


class TestDissipationWindow:
    """ω_H/Γ_mr: dissipation window for Hawking detection."""

    def test_dean_nozzle_marginal(self):
        """Dean nozzle (T_H ~ 2.4 K, l_mr ~ 5 μm): ratio ~ 1-3."""
        ratio = dirac_fluid_dissipation_window(2.4, 5e-6)
        assert 0.5 < ratio < 5.0

    def test_cleaner_sample_better(self):
        """Cleaner samples (l_mr ~ 15 μm) give larger window."""
        r1 = dirac_fluid_dissipation_window(2.4, 5e-6)
        r2 = dirac_fluid_dissipation_window(2.4, 15e-6)
        assert r2 > r1

    def test_higher_TH_better(self):
        """Higher T_H (monolayer, shorter constriction) gives larger window."""
        r1 = dirac_fluid_dissipation_window(2.4, 5e-6)
        r2 = dirac_fluid_dissipation_window(17.0, 5e-6)
        assert r2 > r1


class TestPlatformCrossValidation:
    """Cross-validate formulas.py against constants.py derived parameters."""

    def test_dean_T_H_consistency(self):
        """T_H from formula matches constants.py value."""
        plat = GRAPHENE_PLATFORMS['Dean_bilayer_nozzle']
        T_H_formula = dirac_fluid_hawking_temperature(plat['gradient_s1'])
        T_H_stored = plat['T_H_K']
        # Allow 10% tolerance (stored value is rounded)
        assert abs(T_H_formula - T_H_stored) / T_H_stored < 0.1

    def test_monolayer_c_s(self):
        """Monolayer c_s matches v_F/√2."""
        plat = GRAPHENE_PLATFORMS['Monolayer_100nm']
        expected_c_s = dirac_fluid_sound_speed(plat['v_F'])
        assert abs(plat['c_s'] - expected_c_s) / expected_c_s < 0.01

    def test_all_platforms_have_required_keys(self):
        """Every platform has the required keys."""
        required = {'v_F', 'c_s', 'T_H_K', 'nozzle_throat_nm', 'dispersion_type'}
        for name, plat in GRAPHENE_PLATFORMS.items():
            for key in required:
                assert key in plat, f"{name} missing key {key}"

    def test_all_subluminal(self):
        """All graphene platforms have subluminal dispersion."""
        for name, plat in GRAPHENE_PLATFORMS.items():
            assert plat['dispersion_type'] == 'subluminal', f"{name} not subluminal"
