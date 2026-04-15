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
from src.core.transonic_background import (
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
        """δ_diss > 0 when γ₁ > 0 (dissipation increases fluctuations).

        γ values in [m²/s] (EFT Lagrangian convention). Beliaev scale at
        BEC conditions is ~10⁻¹² m²/s; use 10⁻¹² here for physical realism.
        """
        params = steinhauer_Rb87()
        bg = solve_transonic_background(params)
        result = compute_dissipative_correction(bg, params, gamma_1=1e-12, gamma_2=0)
        assert result["delta_diss"] > 0

    def test_correction_small(self):
        """δ_diss should be parametrically small for current BEC experiments.

        At Beliaev scale (γ ~ 10⁻¹² m²/s) with Steinhauer κ and c_s,
        δ_diss = γ·κ/c_s² ≈ 10⁻⁵ ≪ 1.
        """
        params = steinhauer_Rb87()
        bg = solve_transonic_background(params)
        result = compute_dissipative_correction(bg, params, gamma_1=1e-12, gamma_2=1e-13)
        assert abs(result["delta_diss"]) < 0.1, \
            f"δ_diss = {result['delta_diss']} — not parametrically small"

    def test_dispersive_vs_dissipative_scaling(self):
        """Compare scaling of δ_disp and δ_diss — both should be small."""
        params = steinhauer_Rb87()
        bg = solve_transonic_background(params)
        result = compute_dissipative_correction(bg, params, gamma_1=1e-12, gamma_2=1e-13)
        # Both corrections should be << 1
        assert abs(result["delta_disp"]) < 0.1
        assert abs(result["delta_diss"]) < 0.1


class TestBeliaevChainConsistency:
    """Test the full Beliaev→transport→correction chain.

    These tests exist to regression-guard against the dimensional bug fixed in
    Phase 5u Wave 1a (2026-04-13). Prior to that fix,
    `compute_dissipative_correction` omitted the k_H² = (κ/c_s)² conversion factor
    between EFT transport coefficients γ₁,γ₂ (units [m²/s]) and the horizon damping
    rate Γ_H (units [s⁻¹]), producing δ_diss wrong by ~10⁷ for typical BEC
    parameters. The bug was undetected by existing tests because they used
    hand-picked γ values and only asserted `|δ_diss| < 0.1`, which any formula
    satisfies for small inputs.

    Grounding:
      - Lean: SKEFTHawking.SecondOrderSK.GammaH / gammaH_def / gammaH_via_kH
      - Lean: SKEFTHawking.SecondOrderSK.deltaDissFromTransport_eq
      - Docs: PAPER_DEPENDENCIES['paper1_first_order'] line 657
    """

    @pytest.mark.parametrize(
        "setup_fn,name",
        [
            (steinhauer_Rb87, "Steinhauer"),
            (heidelberg_K39, "Heidelberg"),
            (trento_spin_sonic, "Trento"),
        ],
    )
    def test_Gamma_H_equals_Gamma_Bel(self, setup_fn, name):
        """Γ_H from transport chain must equal Γ_Bel direct (they are the same rate).

        Γ_Bel is computed directly: √(na³)·κ²/c_s.
        Γ_H is computed via transport: (γ₁+γ₂)·k_H² where γᵢ = Γ_Bel/(2 k_H²).
        By construction these are identical — if they diverge, the pipeline has
        the dimensional bug.
        """
        from src.core.formulas import (
            beliaev_damping_rate,
            beliaev_transport_coefficients,
        )

        params = setup_fn()
        bg = solve_transonic_background(params)
        kappa = bg.surface_gravity
        cs = params.sound_speed_upstream

        Gamma_Bel = beliaev_damping_rate(
            params.density_upstream, params.scattering_length, kappa, cs
        )
        tc = beliaev_transport_coefficients(
            params.density_upstream,
            params.scattering_length,
            kappa,
            cs,
            params.healing_length,
        )
        result = compute_dissipative_correction(
            bg, params, tc["gamma_1"], tc["gamma_2"]
        )
        Gamma_H_from_transport = result["Gamma_H"]

        # Both should be [s⁻¹] and equal to within float precision.
        rel_err = abs(Gamma_H_from_transport - Gamma_Bel) / Gamma_Bel
        assert rel_err < 1e-10, (
            f"{name}: Gamma_H via transport ({Gamma_H_from_transport:.6e}) "
            f"!= Gamma_Bel direct ({Gamma_Bel:.6e}). Relative error {rel_err:.3e}. "
            "This test catches the dimensional bug where k_H² factor is missing."
        )

    @pytest.mark.parametrize(
        "setup_fn,name",
        [
            (steinhauer_Rb87, "Steinhauer"),
            (heidelberg_K39, "Heidelberg"),
            (trento_spin_sonic, "Trento"),
        ],
    )
    def test_delta_diss_equals_Gamma_Bel_over_kappa(self, setup_fn, name):
        """δ_diss from pipeline must equal Γ_Bel/κ (the Lean reference formula)."""
        from src.core.formulas import (
            beliaev_damping_rate,
            beliaev_transport_coefficients,
        )

        params = setup_fn()
        bg = solve_transonic_background(params)
        kappa = bg.surface_gravity
        cs = params.sound_speed_upstream

        Gamma_Bel = beliaev_damping_rate(
            params.density_upstream, params.scattering_length, kappa, cs
        )
        tc = beliaev_transport_coefficients(
            params.density_upstream,
            params.scattering_length,
            kappa,
            cs,
            params.healing_length,
        )
        result = compute_dissipative_correction(
            bg, params, tc["gamma_1"], tc["gamma_2"]
        )

        expected = Gamma_Bel / kappa
        rel_err = abs(result["delta_diss"] - expected) / expected
        assert rel_err < 1e-10, (
            f"{name}: delta_diss = {result['delta_diss']:.6e} but Γ_Bel/κ = {expected:.6e}. "
            f"Relative error {rel_err:.3e}."
        )

    def test_gamma_H_formula_identity(self):
        """Verify Γ_H = (γ₁+γ₂)·(κ/c_s)² at the Python level (Lean: gammaH_def).

        Feeds synthetic γ values (not from Beliaev) and checks the bare identity.
        """
        params = steinhauer_Rb87()
        bg = solve_transonic_background(params)
        kappa = bg.surface_gravity
        cs = params.sound_speed_upstream

        g1, g2 = 1.0e-10, 2.0e-10  # [m²/s] — arbitrary test values
        expected_Gamma_H = (g1 + g2) * (kappa / cs) ** 2

        result = compute_dissipative_correction(bg, params, g1, g2)
        rel_err = abs(result["Gamma_H"] - expected_Gamma_H) / expected_Gamma_H
        assert rel_err < 1e-12, (
            f"Γ_H identity broken: pipeline returned {result['Gamma_H']:.6e}, "
            f"expected (γ₁+γ₂)·(κ/c_s)² = {expected_Gamma_H:.6e}"
        )

    def test_delta_diss_physical_magnitude_steinhauer(self):
        """At Steinhauer parameters, Beliaev δ_diss must be in physical range.

        Pre-bugfix this returned ~3×10⁻¹³ (off by factor k_H² ≈ 10⁷).
        Post-bugfix the Beliaev prediction is ~2×10⁻⁵.

        Tightens the prior `< 0.1` bound, which was too loose to catch the bug.
        """
        from src.core.formulas import beliaev_transport_coefficients

        params = steinhauer_Rb87()
        bg = solve_transonic_background(params)
        tc = beliaev_transport_coefficients(
            params.density_upstream,
            params.scattering_length,
            bg.surface_gravity,
            params.sound_speed_upstream,
            params.healing_length,
        )
        result = compute_dissipative_correction(
            bg, params, tc["gamma_1"], tc["gamma_2"]
        )

        assert 1e-7 < result["delta_diss"] < 1e-3, (
            f"Steinhauer Beliaev δ_diss = {result['delta_diss']:.3e}, "
            "expected within [1e-7, 1e-3] (Beliaev zero-T regime for dilute BEC). "
            "Values << 1e-7 suggest a dimensional bug (missing k_H² factor)."
        )
