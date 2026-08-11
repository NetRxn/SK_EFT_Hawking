"""Tests for graphene Hawking temperature predictions (Phase 5w Wave 3).

Tests cover:
- Surface gravity and adiabaticity parameter
- Dissipative correction negligibility (key finding: 11 orders below dispersive)
- Effective temperature with corrections
- EFT validity bounds (D < 1)
- Noise spectrum shape
- Cross-validation with existing BEC correction formulas
"""

import numpy as np
import pytest

from src.graphene.hawking_predictions import (
    graphene_surface_gravity,
    graphene_adiabaticity,
    graphene_damping_rate_horizon,
    graphene_hawking_prediction,
    graphene_noise_spectrum,
    all_platform_predictions,
)
from src.core.formulas import (
    hawking_temperature,
    dispersive_correction,
    first_order_correction,
)
from src.core.constants import GRAPHENE_PLATFORMS


class TestSurfaceGravity:
    def test_dean_positive(self):
        kappa = graphene_surface_gravity('Dean_bilayer_nozzle')
        assert kappa > 0

    def test_dean_order_of_magnitude(self):
        kappa = graphene_surface_gravity('Dean_bilayer_nozzle')
        assert 1e11 < kappa < 1e13


class TestAdiabaticity:
    def test_dean_perturbative(self):
        """Dean nozzle D < 1: EFT is valid."""
        D = graphene_adiabaticity('Dean_bilayer_nozzle')
        assert 0 < D < 1

    def test_monolayer_50nm_nonperturbative(self):
        """50nm monolayer D > 1: EFT breaks down."""
        D = graphene_adiabaticity('Monolayer_50nm')
        assert D > 1


class TestDampingRate:
    def test_positive(self):
        Gamma_H = graphene_damping_rate_horizon('Dean_bilayer_nozzle')
        assert Gamma_H > 0

    def test_perturbative_but_not_negligible(self):
        """δ_diss = Γ_H/κ is a percent-level correction at the Dean device.

        Replaces a test that asserted Γ_H/κ < 1e-10 — which held only because
        `graphene_damping_rate_horizon` omitted the velocity² and returned a
        quantity in [s·m⁻²]. The band below is wide enough to survive the ζ/η
        bilayer uncertainty (≲10 %) and the c_s²-vs-v_F² factor of 2, and
        narrow enough to fail if the velocity² is dropped again (that defect
        lands at 1.7e-13) or double-counted (that lands above 1).
        """
        Gamma_H = graphene_damping_rate_horizon('Dean_bilayer_nozzle')
        kappa = graphene_surface_gravity('Dean_bilayer_nozzle')
        assert 0.01 < Gamma_H / kappa < 0.25

    def test_damping_rate_matches_phase5w_order_of_magnitude(self):
        """Γ_H is within two decades of Phase-5w's Γ_sound ~ (η/w)k² ~ 10¹⁰ s⁻¹.

        The survey quotes that rate for the same fluid at comparable ω and T.
        The pre-2026-08-09 code returned 0.335 s⁻¹ — eleven orders below its
        own cited source, which no test caught because none compared them.
        """
        Gamma_H = graphene_damping_rate_horizon('Dean_bilayer_nozzle')
        assert 1e9 < Gamma_H < 1e13

    def test_conformal_velocity_forms_agree_on_monolayer(self):
        """ν = 2(η/sT)c_s² and (η/sT)v_F² coincide where c_s = v_F/√2.

        This is the identity that dissolves the c_s²/v_F² question. It must
        hold on the monolayer (conformal) and must NOT be assumed on the
        bilayer, whose measured c_s does not satisfy c_s = v_F/√2.
        """
        from src.core.constants import GRAPHENE_PLATFORMS
        from src.graphene.hawking_predictions import (
            graphene_eta_over_sT, graphene_kinematic_viscosity,
        )
        plat = GRAPHENE_PLATFORMS['Monolayer_100nm']
        v_F_form = graphene_eta_over_sT('Monolayer_100nm') * plat['v_F'] ** 2
        # rel=2e-2, not exact: the stored monolayer c_s = 7.1e5 m/s is
        # v_F/√2 = 7.0711e5 rounded to two significant figures, so the two
        # forms agree to ~0.8 % in ν (the rounding enters squared). The gap is
        # the constant's precision, not a physics gap — at exact conformality
        # the identity is exact, which is what the Lean theorem states.
        assert graphene_kinematic_viscosity('Monolayer_100nm') == pytest.approx(
            v_F_form, rel=2e-2)
        assert plat['c_s'] == pytest.approx(plat['v_F'] / np.sqrt(2), rel=5e-3)

        bilayer = GRAPHENE_PLATFORMS['Dean_bilayer_nozzle']
        assert bilayer['c_s'] < bilayer['v_F'] / np.sqrt(2) * 0.9


class TestHawkingPrediction:
    def test_dean_T_H_positive(self):
        pred = graphene_hawking_prediction('Dean_bilayer_nozzle')
        assert pred['T_H_K'] > 0

    def test_dean_T_eff_positive(self):
        pred = graphene_hawking_prediction('Dean_bilayer_nozzle')
        assert pred['T_eff_K'] > 0

    def test_dean_correction_small(self):
        """Total correction < 5% for Dean nozzle."""
        pred = graphene_hawking_prediction('Dean_bilayer_nozzle')
        assert abs(pred['correction_pct']) < 5.0

    def test_dissipative_dominates_dispersive(self):
        """Key finding, INVERTED 2026-08-09: δ_diss exceeds |δ_disp| at Dean.

        The superseded assertion was `δ_diss < |δ_disp| × 1e-8`, i.e. the
        "eleven orders below" headline. With ν carrying its velocity², the
        dissipative term is the larger of the two and the corrections have
        opposite signs, so they partially cancel rather than one vanishing.
        """
        pred = graphene_hawking_prediction('Dean_bilayer_nozzle')
        assert pred['delta_diss'] > abs(pred['delta_disp'])
        assert pred['delta_diss'] * pred['delta_disp'] < 0, 'opposite signs'

    def test_dispersive_correction_negative(self):
        """Dispersive correction is negative (cooling)."""
        pred = graphene_hawking_prediction('Dean_bilayer_nozzle')
        assert pred['delta_disp'] < 0

    def test_T_eff_exceeds_T_H(self):
        """T_eff > T_H at Dean: the dissipative term outweighs the dispersive.

        Was `T_eff < T_H`, which followed from δ_disp being the only
        non-negligible correction. It no longer is.
        """
        pred = graphene_hawking_prediction('Dean_bilayer_nozzle')
        assert pred['T_eff_K'] > pred['T_H_K']

    def test_monolayer_50nm_breaks_eft(self):
        """50nm monolayer: the perturbative expansion fails.

        The breakdown signal is |δ| > 1 in either channel, not T_eff < 0.
        T_eff < 0 was a proxy that worked only while δ_diss was negligible —
        with a positive δ_diss of the same order the sum can stay positive
        (here 8.4 K) while both terms are individually non-perturbative, which
        is a *worse* regime, not a safer one. Asserting on the terms rather
        than on their sum is what makes the test detect that.
        """
        pred = graphene_hawking_prediction('Monolayer_50nm')
        assert pred['D'] > 1
        assert abs(pred['delta_disp']) > 1.0
        assert max(abs(pred['delta_disp']), abs(pred['delta_diss'])) > 0.5

    def test_dean_is_the_only_perturbative_platform(self):
        """Both corrections stay well below 1 only at the Dean device.

        This is the claim E2's device table rests on after the Γ_H repair, and
        it inverts the draft's framing of monolayer constrictions as an
        improvement path: shrinking L raises δ_diss ∝ κ and δ_disp ∝ κ², so
        the perturbative window closes rather than opens.
        """
        dean = graphene_hawking_prediction('Dean_bilayer_nozzle')
        assert max(abs(dean['delta_disp']), abs(dean['delta_diss'])) < 0.15
        for tighter in ('Monolayer_100nm', 'Monolayer_50nm'):
            pred = graphene_hawking_prediction(tighter)
            assert max(abs(pred['delta_disp']), abs(pred['delta_diss'])) > 0.25


class TestNoiseSpectrum:
    def test_returns_arrays(self):
        spec = graphene_noise_spectrum('Dean_bilayer_nozzle')
        assert 'omega' in spec
        assert 'n_hawking' in spec
        assert len(spec['omega']) == 200

    def test_hawking_occupation_decreasing(self):
        """n_Hawking decreases with frequency (thermal spectrum)."""
        spec = graphene_noise_spectrum('Dean_bilayer_nozzle')
        # Check monotonically decreasing after peak
        n = spec['n_hawking']
        peak_idx = np.argmax(n)
        assert np.all(np.diff(n[peak_idx:]) <= 0)

    def test_thermal_dominates_hawking(self):
        """At T_ambient >> T_H, thermal noise dominates Hawking signal."""
        spec = graphene_noise_spectrum('Dean_bilayer_nozzle')
        # Near ω_H, thermal occupation >> Hawking occupation
        mid = len(spec['omega']) // 2
        assert spec['n_thermal'][mid] > spec['n_hawking'][mid]


class TestAllPlatforms:
    def test_three_acoustic_platforms(self):
        """Three platforms (excluding p-n junction) produce predictions."""
        preds = all_platform_predictions()
        assert len(preds) == 3

    def test_all_have_required_keys(self):
        preds = all_platform_predictions()
        required = {'T_H_K', 'T_eff_K', 'delta_disp', 'delta_diss', 'D',
                     'Gamma_H_s1', 'kappa_s1'}
        for name, pred in preds.items():
            for key in required:
                assert key in pred, f"{name} missing {key}"


class TestCrossValidation:
    def test_T_H_matches_generic_formula(self):
        """T_H from graphene module matches generic hawking_temperature()."""
        pred = graphene_hawking_prediction('Dean_bilayer_nozzle')
        T_H_generic = hawking_temperature(pred['kappa_s1'])
        assert abs(pred['T_H_K'] - T_H_generic) / T_H_generic < 1e-10

    def test_delta_disp_matches_generic(self):
        """δ_disp from graphene module matches generic dispersive_correction()."""
        pred = graphene_hawking_prediction('Dean_bilayer_nozzle')
        delta_generic = dispersive_correction(pred['D'])
        assert abs(pred['delta_disp'] - delta_generic) < 1e-15

    def test_delta_diss_matches_generic(self):
        """δ_diss from graphene module matches generic first_order_correction()."""
        pred = graphene_hawking_prediction('Dean_bilayer_nozzle')
        delta_generic = first_order_correction(pred['Gamma_H_s1'], pred['kappa_s1'])
        assert abs(pred['delta_diss'] - delta_generic) < 1e-20
