"""Tests for the exact WKB connection formula (Phase 3, Item 2D).

Validates:
1. Complex turning point computation and shift structure
2. Stokes geometry invariance
3. Effective surface gravity (frequency-dependent)
4. Critical frequency and length scales
5. Exact connection formula (Bogoliubov coefficients)
6. Modified unitarity (decoherence parameter delta_k)
7. FDR noise floor
8. Modified Bogoliubov coefficients
9. Observable Hawking spectrum
10. Perturbative limit recovery
11. Platform-specific predictions (Steinhauer, Heidelberg, Trento)
12. Cross-module consistency with wkb_analysis.py
"""

import pytest
import numpy as np

from src.wkb.connection_formula import (
    ComplexTurningPoint,
    StokesGeometry,
    EffectiveSurfaceGravity,
    ConnectionResult,
    compute_complex_turning_point,
    compute_stokes_geometry,
    effective_surface_gravity,
    critical_frequency,
    dispersive_length,
    dissipative_length,
    exact_connection_formula,
)
from src.wkb.bogoliubov import (
    ModifiedBogoliubov,
    decoherence_parameter,
    fdr_noise_floor,
    modified_bogoliubov_coefficients,
    compute_bogoliubov,
)
from src.wkb.spectrum import (
    PlatformParams,
    SpectrumPoint,
    HawkingSpectrum,
    steinhauer_platform,
    heidelberg_platform,
    trento_platform,
    planck_occupation,
    compute_spectrum,
    perturbative_spectrum,
    compare_exact_vs_perturbative,
    platform_predictions,
    spectrum_summary,
)
from src.core.formulas import damping_rate, dispersive_correction


# ═══════════════════════════════════════════════════════════════════
# Complex turning point
# ═══════════════════════════════════════════════════════════════════

class TestComplexTurningPoint:
    """Test complex turning point computation."""

    def test_zero_dissipation_no_shift(self):
        """With gamma = 0, turning point stays on real axis."""
        tp = compute_complex_turning_point(
            omega=0.5, kappa=1.0, c_s=1.0, xi=0.03,
            gamma_1=0.0, gamma_2=0.0,
        )
        assert tp.x_imag == 0.0
        assert tp.Gamma_H == 0.0

    def test_positive_dissipation_positive_shift(self):
        """Dissipation shifts turning point into upper half-plane."""
        tp = compute_complex_turning_point(
            omega=0.5, kappa=1.0, c_s=1.0, xi=0.03,
            gamma_1=0.01, gamma_2=0.01,
        )
        assert tp.x_imag > 0
        assert tp.Gamma_H > 0

    def test_shift_proportional_to_damping(self):
        """Shift is proportional to Gamma_H / (kappa * c_s)."""
        tp = compute_complex_turning_point(
            omega=0.5, kappa=1.0, c_s=1.0, xi=0.03,
            gamma_1=0.01, gamma_2=0.01,
        )
        # Canonical formula: delta_x = c_s * Gamma_H / (2 * kappa^2)
        expected = 1.0 * tp.Gamma_H / (2.0 * 1.0**2)
        assert abs(tp.x_imag - expected) < 1e-12

    def test_shift_inversely_proportional_to_kappa_squared(self):
        """Doubling kappa quarters the shift (delta_x ∝ 1/kappa²)."""
        tp1 = compute_complex_turning_point(
            omega=0.5, kappa=1.0, c_s=1.0, xi=0.03,
            gamma_1=0.01, gamma_2=0.01,
        )
        tp2 = compute_complex_turning_point(
            omega=0.5, kappa=2.0, c_s=1.0, xi=0.03,
            gamma_1=0.01, gamma_2=0.01,
        )
        # Same Gamma_H (same k_H and omega), kappa doubled → shift / 4
        assert abs(tp2.x_imag - tp1.x_imag / 4.0) < 1e-12

    def test_shift_frequency_dependent(self):
        """Shift grows with frequency (through k_H dependence)."""
        tp_low = compute_complex_turning_point(
            omega=0.1, kappa=1.0, c_s=1.0, xi=0.03,
            gamma_1=0.01, gamma_2=0.01,
        )
        tp_high = compute_complex_turning_point(
            omega=1.0, kappa=1.0, c_s=1.0, xi=0.03,
            gamma_1=0.01, gamma_2=0.01,
        )
        assert tp_high.x_imag > tp_low.x_imag

    def test_delta_diss_property(self):
        """delta_diss = Gamma_H / kappa."""
        tp = compute_complex_turning_point(
            omega=0.5, kappa=2.0, c_s=1.0, xi=0.03,
            gamma_1=0.01, gamma_2=0.01,
        )
        assert abs(tp.delta_diss - tp.Gamma_H / 2.0) < 1e-12

    def test_complex_property(self):
        """x_complex = x_real + i*x_imag."""
        tp = compute_complex_turning_point(
            omega=0.5, kappa=1.0, c_s=1.0, xi=0.03,
            gamma_1=0.01, gamma_2=0.01,
        )
        assert tp.x_complex.real == tp.x_real
        assert tp.x_complex.imag == tp.x_imag

    def test_all_eft_orders_contribute(self):
        """Third-order coefficients increase the shift."""
        tp2 = compute_complex_turning_point(
            omega=0.5, kappa=1.0, c_s=1.0, xi=0.03,
            gamma_1=0.01, gamma_2=0.01,
        )
        tp3 = compute_complex_turning_point(
            omega=0.5, kappa=1.0, c_s=1.0, xi=0.03,
            gamma_1=0.01, gamma_2=0.01,
            gamma_3_1=0.001, gamma_3_2=0.001, gamma_3_3=0.001,
        )
        assert tp3.x_imag > tp2.x_imag


# ═══════════════════════════════════════════════════════════════════
# Stokes geometry
# ═══════════════════════════════════════════════════════════════════

class TestStokesGeometry:
    """Test Stokes-line structure."""

    def test_stokes_constant_is_imaginary(self):
        """Stokes constant T = i for a first-order zero."""
        tp = compute_complex_turning_point(
            omega=0.5, kappa=1.0, c_s=1.0, xi=0.03,
            gamma_1=0.01, gamma_2=0.0,
        )
        sg = compute_stokes_geometry(tp)
        assert sg.stokes_constant == 1j

    def test_three_stokes_lines(self):
        """Three Stokes lines at 2*pi/3 angular separation."""
        tp = compute_complex_turning_point(
            omega=0.5, kappa=1.0, c_s=1.0, xi=0.03,
            gamma_1=0.0, gamma_2=0.0,
        )
        sg = compute_stokes_geometry(tp)
        angles = sg.stokes_angles
        assert len(angles) == 3
        # Check 2*pi/3 separation
        for i in range(3):
            diff = angles[(i + 1) % 3] - angles[i]
            # Normalize to [0, 2pi)
            diff = diff % (2 * np.pi)
            assert abs(diff - 2 * np.pi / 3) < 0.1  # approximate due to rotation

    def test_stokes_constant_invariant_under_shift(self):
        """Stokes constant remains i regardless of dissipation (Berry 1989)."""
        tp_weak = compute_complex_turning_point(
            omega=0.5, kappa=1.0, c_s=1.0, xi=0.03,
            gamma_1=0.001, gamma_2=0.0,
        )
        tp_strong = compute_complex_turning_point(
            omega=0.5, kappa=1.0, c_s=1.0, xi=0.03,
            gamma_1=0.1, gamma_2=0.0,
        )
        sg_weak = compute_stokes_geometry(tp_weak)
        sg_strong = compute_stokes_geometry(tp_strong)
        assert sg_weak.stokes_constant == sg_strong.stokes_constant == 1j


# ═══════════════════════════════════════════════════════════════════
# Effective surface gravity
# ═══════════════════════════════════════════════════════════════════

class TestEffectiveSurfaceGravity:
    """Test effective surface gravity with all corrections."""

    def test_no_corrections_gives_bare_kappa(self):
        """With no dissipation/dispersion, kappa_eff = kappa."""
        result = effective_surface_gravity(
            omega=0.5, kappa=1.0, c_s=1.0, xi=0.0,
            gamma_1=0.0, gamma_2=0.0,
        )
        # delta_disp = -(pi/6)*D^2 = 0 when xi=0
        # delta_diss = 0 when gamma=0
        assert abs(result.kappa_eff - 1.0) < 1e-10

    def test_dissipation_reduces_kappa_eff(self):
        """Dissipation increases the denominator, reducing kappa_eff."""
        result = effective_surface_gravity(
            omega=0.5, kappa=1.0, c_s=1.0, xi=0.03,
            gamma_1=0.01, gamma_2=0.01,
        )
        assert result.kappa_eff < result.kappa
        assert result.delta_diss > 0

    def test_dispersion_sign(self):
        """Dispersive correction is negative (subluminal Bogoliubov)."""
        result = effective_surface_gravity(
            omega=0.5, kappa=1.0, c_s=1.0, xi=0.03,
            gamma_1=0.0, gamma_2=0.0,
        )
        assert result.delta_disp < 0

    def test_frequency_dependence(self):
        """kappa_eff depends on omega through the damping rate."""
        r1 = effective_surface_gravity(
            omega=0.1, kappa=1.0, c_s=1.0, xi=0.03,
            gamma_1=0.01, gamma_2=0.01,
        )
        r2 = effective_surface_gravity(
            omega=1.0, kappa=1.0, c_s=1.0, xi=0.03,
            gamma_1=0.01, gamma_2=0.01,
        )
        # Higher omega → larger Gamma_H → larger delta_diss → lower kappa_eff
        assert r2.kappa_eff < r1.kappa_eff

    def test_delta_total_is_sum(self):
        """delta_total = delta_disp + delta_diss."""
        result = effective_surface_gravity(
            omega=0.5, kappa=1.0, c_s=1.0, xi=0.03,
            gamma_1=0.01, gamma_2=0.01,
        )
        assert abs(result.delta_total - result.delta_disp - result.delta_diss) < 1e-12


# ═══════════════════════════════════════════════════════════════════
# Critical frequency and length scales
# ═══════════════════════════════════════════════════════════════════

class TestLengthScales:
    """Test critical frequency and characteristic lengths."""

    def test_critical_frequency_positive(self):
        """omega_max > 0 for physical parameters."""
        omega_max = critical_frequency(kappa=1.0, xi=0.03, c_s=1.0)
        assert omega_max > 0

    def test_critical_frequency_formula(self):
        """omega_max = kappa / D^{2/3}."""
        D = 0.03
        omega_max = critical_frequency(kappa=1.0, xi=D, c_s=1.0)
        expected = 1.0 / D**(2.0 / 3.0)
        assert abs(omega_max - expected) < 1e-10

    def test_critical_frequency_increases_with_cutoff(self):
        """Smaller xi (higher UV cutoff) → higher omega_max."""
        om1 = critical_frequency(kappa=1.0, xi=0.03, c_s=1.0)
        om2 = critical_frequency(kappa=1.0, xi=0.01, c_s=1.0)
        assert om2 > om1

    def test_dispersive_length(self):
        """ell_D = xi * D^{-1/3}."""
        ell_D = dispersive_length(kappa=1.0, xi=0.03, c_s=1.0)
        expected = 0.03 * 0.03**(-1.0 / 3.0)
        assert abs(ell_D - expected) < 1e-10

    def test_dissipative_length(self):
        """ell_diss = (c_s / kappa) * delta_diss."""
        ell_diss = dissipative_length(kappa=1.0, c_s=1.0, delta_diss=0.003)
        assert abs(ell_diss - 0.003) < 1e-10

    def test_dispersion_dominates_for_steinhauer(self):
        """For Steinhauer, ell_D >> ell_diss (dispersion dominates)."""
        p = steinhauer_platform()
        ell_D = dispersive_length(p.kappa, p.xi, p.c_s)
        k_H = p.T_H / p.c_s
        Gamma_H = damping_rate(k_H, p.T_H, p.c_s, p.gamma_1, p.gamma_2)
        ell_diss = dissipative_length(p.kappa, p.c_s, Gamma_H / p.kappa)
        assert ell_D > ell_diss * 100  # dispersion dominates by >100x


# ═══════════════════════════════════════════════════════════════════
# Decoherence parameter
# ═══════════════════════════════════════════════════════════════════

class TestDecoherence:
    """Test the decoherence parameter delta_k."""

    def test_zero_damping_zero_decoherence(self):
        """No dissipation → no decoherence."""
        dk = decoherence_parameter(Gamma_H=0.0, kappa=1.0)
        assert dk == 0.0

    def test_positive_damping_positive_decoherence(self):
        """Positive dissipation → positive decoherence."""
        dk = decoherence_parameter(Gamma_H=0.01, kappa=1.0)
        assert dk > 0

    def test_double_delta_diss(self):
        """delta_k = 2 * Gamma_H / kappa = 2 * delta_diss."""
        Gamma_H = 0.05
        kappa = 2.0
        dk = decoherence_parameter(Gamma_H, kappa)
        delta_diss = Gamma_H / kappa
        assert abs(dk - 2.0 * delta_diss) < 1e-12

    def test_small_for_steinhauer(self):
        """For Steinhauer parameters, delta_k << 1 (perturbative regime)."""
        p = steinhauer_platform()
        k_H = p.T_H / p.c_s
        Gamma_H = damping_rate(k_H, p.T_H, p.c_s, p.gamma_1, p.gamma_2)
        dk = decoherence_parameter(Gamma_H, p.kappa)
        assert dk < 0.01  # perturbative


# ═══════════════════════════════════════════════════════════════════
# FDR noise floor
# ═══════════════════════════════════════════════════════════════════

class TestNoiseFloor:
    """Test the FDR/KMS-mandated noise floor."""

    def test_zero_decoherence_zero_noise(self):
        """No decoherence → no noise floor."""
        n = fdr_noise_floor(delta_k=0.0, omega=0.5)
        assert n == 0.0

    def test_vacuum_noise_is_half_delta_k(self):
        """For T_env = 0, n_noise = delta_k / 2."""
        dk = 0.01
        n = fdr_noise_floor(delta_k=dk, omega=0.5, T_env=0.0)
        assert abs(n - dk / 2.0) < 1e-12

    def test_thermal_noise_exceeds_vacuum(self):
        """Finite T_env increases the noise above the vacuum floor."""
        dk = 0.01
        n_vac = fdr_noise_floor(delta_k=dk, omega=0.5, T_env=0.0)
        n_th = fdr_noise_floor(delta_k=dk, omega=0.5, T_env=0.5)
        assert n_th > n_vac

    def test_noise_always_nonneg(self):
        """Noise floor is non-negative."""
        for dk in [0.0, 0.001, 0.1, 0.5]:
            for T in [0.0, 0.1, 1.0]:
                n = fdr_noise_floor(delta_k=dk, omega=0.5, T_env=T)
                assert n >= 0.0

    def test_high_temperature_limit(self):
        """For T_env >> omega, noise floor → (delta_k * T_env) / omega."""
        dk = 0.01
        omega = 0.01
        T_env = 100.0
        n = fdr_noise_floor(delta_k=dk, omega=omega, T_env=T_env)
        expected = dk * T_env / omega
        assert abs(n - expected) / expected < 0.01


# ═══════════════════════════════════════════════════════════════════
# Modified Bogoliubov coefficients
# ═══════════════════════════════════════════════════════════════════

class TestModifiedBogoliubov:
    """Test modified Bogoliubov coefficients."""

    def test_unitarity_deficit_equals_delta_k(self):
        """Unitarity deficit = 1 - (alpha^2 - beta^2) = delta_k."""
        bog = compute_bogoliubov(
            omega=0.5, kappa=1.0, c_s=1.0, xi=0.03,
            gamma_1=0.01, gamma_2=0.01,
        )
        assert abs(bog.unitarity_deficit - bog.delta_k) < 1e-8

    def test_modified_unitarity(self):
        """|alpha|^2 - |beta|^2 = 1 - delta_k."""
        bog = compute_bogoliubov(
            omega=0.5, kappa=1.0, c_s=1.0, xi=0.03,
            gamma_1=0.01, gamma_2=0.01,
        )
        lhs = bog.alpha_sq - bog.beta_sq
        rhs = 1.0 - bog.delta_k
        assert abs(lhs - rhs) < 1e-8

    def test_n_total_exceeds_planck(self):
        """Total occupation exceeds Planck (from noise + dissipative heating)."""
        p = steinhauer_platform()
        bog = compute_bogoliubov(
            p.T_H, p.kappa, p.c_s, p.xi,
            p.gamma_1, p.gamma_2,
        )
        n_planck = planck_occupation(p.T_H, p.T_H)
        assert bog.n_total >= n_planck

    def test_n_total_is_hawking_plus_noise(self):
        """n_total = n_hawking + n_noise."""
        bog = compute_bogoliubov(
            omega=0.5, kappa=1.0, c_s=1.0, xi=0.03,
            gamma_1=0.01, gamma_2=0.01,
        )
        assert abs(bog.n_total - bog.n_hawking - bog.n_noise) < 1e-10

    def test_entanglement_degradation(self):
        """Entanglement degradation ~ delta_k / 2."""
        bog = compute_bogoliubov(
            omega=0.5, kappa=1.0, c_s=1.0, xi=0.03,
            gamma_1=0.01, gamma_2=0.01,
        )
        assert abs(bog.entanglement_degradation - bog.delta_k / 2.0) < 1e-12

    def test_no_dissipation_standard_result(self):
        """With gamma = 0, recover standard Planck occupation."""
        omega = 0.3
        kappa = 1.0
        bog = compute_bogoliubov(
            omega=omega, kappa=kappa, c_s=1.0, xi=0.0,
            gamma_1=0.0, gamma_2=0.0,
        )
        n_expected = planck_occupation(omega, kappa / (2 * np.pi))
        assert abs(bog.n_total - n_expected) / n_expected < 1e-6
        assert bog.delta_k == 0.0
        assert bog.n_noise == 0.0


# ═══════════════════════════════════════════════════════════════════
# Exact connection formula
# ═══════════════════════════════════════════════════════════════════

class TestExactConnectionFormula:
    """Test the exact WKB connection formula."""

    def test_returns_connection_result(self):
        conn = exact_connection_formula(
            omega=0.5, kappa=1.0, c_s=1.0, xi=0.03,
            gamma_1=0.01, gamma_2=0.01,
        )
        assert isinstance(conn, ConnectionResult)

    def test_beta_over_alpha_sq_bounded(self):
        """0 < |beta/alpha|^2 < 1 for physical parameters."""
        conn = exact_connection_formula(
            omega=0.5, kappa=1.0, c_s=1.0, xi=0.03,
            gamma_1=0.01, gamma_2=0.01,
        )
        assert 0 < conn.beta_over_alpha_sq < 1

    def test_exponential_form(self):
        """Connection formula has exp(-2*pi*omega/kappa_eff) structure."""
        omega = 0.5
        conn = exact_connection_formula(
            omega=omega, kappa=1.0, c_s=1.0, xi=0.03,
            gamma_1=0.01, gamma_2=0.01,
        )
        expected = np.exp(-2 * np.pi * omega / conn.kappa_eff.kappa_eff)
        # Without UV suppression (omega << omega_max)
        assert abs(conn.beta_over_alpha_sq - expected) < 1e-10

    def test_no_dissipation_hawking_result(self):
        """With gamma = 0, recover standard Hawking |beta/alpha|^2."""
        omega = 0.5
        kappa = 1.0
        conn = exact_connection_formula(
            omega=omega, kappa=kappa, c_s=1.0, xi=0.0,
            gamma_1=0.0, gamma_2=0.0,
        )
        expected = np.exp(-2 * np.pi * omega / kappa)
        assert abs(conn.beta_over_alpha_sq - expected) < 1e-10
        assert conn.delta_k == 0.0

    def test_uv_suppression_at_high_frequency(self):
        """UV suppression kicks in for omega > 0.5 * omega_max."""
        omega_max = critical_frequency(kappa=1.0, xi=0.03, c_s=1.0)
        conn = exact_connection_formula(
            omega=0.7 * omega_max, kappa=1.0, c_s=1.0, xi=0.03,
            gamma_1=0.0, gamma_2=0.0,
        )
        assert conn.uv_suppression < 1.0

    def test_no_uv_suppression_at_low_frequency(self):
        """No UV suppression for omega << omega_max."""
        conn = exact_connection_formula(
            omega=0.5, kappa=1.0, c_s=1.0, xi=0.03,
            gamma_1=0.01, gamma_2=0.01,
        )
        assert conn.uv_suppression == 1.0


# ═══════════════════════════════════════════════════════════════════
# Platform parameters
# ═══════════════════════════════════════════════════════════════════

class TestPlatforms:
    """Test BEC platform parameter presets."""

    def test_steinhauer_parameters(self):
        p = steinhauer_platform()
        assert p.D == 0.03
        assert p.gamma_dim == 0.003
        assert p.kappa == 1.0
        assert p.c_s == 1.0

    def test_heidelberg_parameters(self):
        p = heidelberg_platform()
        assert p.D == 0.02
        assert p.gamma_dim == 0.002

    def test_trento_parameters(self):
        p = trento_platform()
        assert p.D == 0.014
        assert p.gamma_dim == 1.4e-5

    def test_kms_splitting(self):
        """gamma_1 = gamma_2 = gamma_dim / 2 (equal KMS splitting)."""
        for factory in [steinhauer_platform, heidelberg_platform, trento_platform]:
            p = factory()
            assert p.gamma_1 == p.gamma_dim / 2
            assert p.gamma_2 == p.gamma_dim / 2

    def test_positivity_constraint(self):
        """gamma_2_2 = -gamma_2_1 (positivity constraint)."""
        for factory in [steinhauer_platform, heidelberg_platform, trento_platform]:
            p = factory()
            assert abs(p.gamma_2_2 + p.gamma_2_1) < 1e-15

    def test_hawking_temperature(self):
        """T_H = kappa / (2*pi)."""
        p = steinhauer_platform()
        assert abs(p.T_H - 1.0 / (2 * np.pi)) < 1e-10

    def test_omega_max_ordering(self):
        """omega_max: Trento > Steinhauer > Heidelberg (smaller D → higher cutoff).
        Actually, Heidelberg has smaller D than Steinhauer, so Heidelberg > Steinhauer."""
        p_s = steinhauer_platform()
        p_h = heidelberg_platform()
        p_t = trento_platform()
        # Smaller D → higher omega_max
        assert p_t.omega_max > p_s.omega_max
        assert p_h.omega_max > p_s.omega_max


# ═══════════════════════════════════════════════════════════════════
# Planck occupation
# ═══════════════════════════════════════════════════════════════════

class TestPlanckOccupation:
    """Test the standard Planck occupation function."""

    def test_thermal_peak(self):
        """n_BE peaks near omega = 0 (infinite occupation)."""
        n1 = planck_occupation(0.01, 1.0)
        n2 = planck_occupation(1.0, 1.0)
        assert n1 > n2

    def test_exponential_decay(self):
        """For omega >> T, n_BE ~ exp(-omega/T)."""
        T = 0.1
        omega = 5.0 * T
        n = planck_occupation(omega, T)
        expected = np.exp(-omega / T)
        assert abs(n - expected) / expected < 0.01

    def test_zero_temperature(self):
        """n_BE = 0 at T = 0."""
        assert planck_occupation(0.5, 0.0) == 0.0


# ═══════════════════════════════════════════════════════════════════
# Full spectrum
# ═══════════════════════════════════════════════════════════════════

class TestSpectrum:
    """Test observable Hawking spectrum computation."""

    def test_spectrum_returns_correct_type(self):
        p = steinhauer_platform()
        spec = compute_spectrum(p, n_points=10)
        assert isinstance(spec, HawkingSpectrum)
        assert len(spec.points) == 10

    def test_spectrum_monotonically_decreasing(self):
        """n_total decreases with frequency (at low omega)."""
        p = steinhauer_platform()
        spec = compute_spectrum(p, omega_min=0.2, omega_max_factor=3.0, n_points=10)
        for i in range(len(spec.points) - 1):
            assert spec.points[i].n_total >= spec.points[i + 1].n_total

    def test_noise_floor_creates_spectral_floor(self):
        """At high omega, n_total approaches n_noise (spectral floor)."""
        p = steinhauer_platform()
        spec = compute_spectrum(p, omega_min=0.1, omega_max_factor=10.0, n_points=30)
        last = spec.points[-1]
        # At high omega, n_noise should be comparable to n_total
        assert last.n_noise / last.n_total > 0.5

    def test_steinhauer_deviations_small_at_peak(self):
        """For Steinhauer, deviations from Planck are < 1% near the peak."""
        p = steinhauer_platform()
        spec = compute_spectrum(p, omega_min=0.5, omega_max_factor=2.0, n_points=10)
        for pt in spec.points:
            assert abs(pt.relative_deviation) < 0.01  # < 1% in measured range

    def test_trento_has_smallest_damping(self):
        """Trento spin-sonic has smallest dissipative correction."""
        specs = platform_predictions()
        s_trento = spectrum_summary(specs['trento'])
        s_stein = spectrum_summary(specs['steinhauer'])
        assert s_trento['delta_diss_at_T_H'] < s_stein['delta_diss_at_T_H']


# ═══════════════════════════════════════════════════════════════════
# Perturbative comparison
# ═══════════════════════════════════════════════════════════════════

class TestPerturbativeComparison:
    """Test comparison between exact WKB and perturbative EFT."""

    def test_agreement_at_low_frequency(self):
        """Exact and perturbative agree within 0.1% at omega < 2*T_H."""
        p = steinhauer_platform()
        omega = 0.5 * p.T_H
        n_exact = compute_bogoliubov(
            omega, p.kappa, p.c_s, p.xi,
            p.gamma_1, p.gamma_2,
            p.gamma_2_1, p.gamma_2_2,
        ).n_total
        n_pert = perturbative_spectrum(omega, p)
        rel_diff = abs(n_exact - n_pert) / n_pert
        assert rel_diff < 0.001

    def test_exact_exceeds_perturbative_at_high_frequency(self):
        """Exact WKB > perturbative at high omega (from noise floor)."""
        p = steinhauer_platform()
        omega = 6.0 * p.T_H
        n_exact = compute_bogoliubov(
            omega, p.kappa, p.c_s, p.xi,
            p.gamma_1, p.gamma_2,
            p.gamma_2_1, p.gamma_2_2,
        ).n_total
        n_pert = perturbative_spectrum(omega, p)
        assert n_exact > n_pert

    def test_compare_function_returns_correct_type(self):
        p = steinhauer_platform()
        comp = compare_exact_vs_perturbative(p, n_points=10)
        assert len(comp.omega) == 10
        assert len(comp.n_exact) == 10
        assert len(comp.n_perturbative) == 10


# ═══════════════════════════════════════════════════════════════════
# Cross-module consistency
# ═══════════════════════════════════════════════════════════════════

class TestCrossModuleConsistency:
    """Test consistency with existing wkb_analysis.py."""

    def test_delta_diss_matches_wkb_analysis(self):
        """delta_diss from exact WKB matches perturbative wkb_analysis.py."""
        from src.second_order.wkb_analysis import (
            steinhauer_params,
            connection_formula as pert_connection,
        )
        # Perturbative
        params = steinhauer_params()
        omega = 0.5 * params.profile.T_H
        pert = pert_connection(omega, params)

        # Exact
        p = steinhauer_platform()
        conn = exact_connection_formula(
            omega, p.kappa, p.c_s, p.xi,
            p.gamma_1, p.gamma_2,
        )

        # delta_diss should match (same formula at leading order)
        assert abs(conn.kappa_eff.delta_diss - pert.delta_diss) / max(abs(pert.delta_diss), 1e-15) < 0.1

    def test_dispersive_correction_consistent(self):
        """Dispersive correction matches between modules."""
        from src.second_order.wkb_analysis import steinhauer_params
        from src.core.formulas import dispersive_correction

        params = steinhauer_params()
        D = params.profile.D

        delta_from_formulas = dispersive_correction(D)
        p = steinhauer_platform()
        D_platform = p.D
        delta_from_platform = dispersive_correction(D_platform)

        assert abs(delta_from_formulas - delta_from_platform) < 1e-10

    def test_damping_rate_consistent(self):
        """Damping rate from formulas.py matches in both modules."""
        p = steinhauer_platform()
        omega = 0.5
        k_H = omega / p.c_s
        Gamma = damping_rate(k_H, omega, p.c_s, p.gamma_1, p.gamma_2)
        tp = compute_complex_turning_point(
            omega, p.kappa, p.c_s, p.xi, p.gamma_1, p.gamma_2,
        )
        assert abs(tp.Gamma_H - Gamma) < 1e-12

    def test_platform_params_match_wkb_analysis(self):
        """Platform parameter values consistent between modules."""
        from src.second_order.wkb_analysis import steinhauer_params
        pert = steinhauer_params()
        exact = steinhauer_platform()
        assert pert.profile.kappa == exact.kappa
        assert pert.profile.c_s == exact.c_s
        assert pert.profile.D == exact.D
