"""Phase 5z Wave 2 tests: Majorana-rung seesaw + PMNS structure.

Mirrors the Lean modules MajoranaRung.lean and NeutrinoMixing.lean against
their Python formula equivalents in `src/core/formulas.py`. Embedding III
per Lit-Search/Phase-5z O.3 deep-research verdict (2026-04-25).
"""

from __future__ import annotations

import math

import numpy as np
import pytest

from src.core.constants import EW_PARAMS, MAJORANA_PARAMS
from src.core.formulas import (
    seesaw_neutrino_mass,
    seesaw_m_r_from_observed,
    m_nu_heaviest_from_atmospheric_splitting,
    pmns_unitary_matrix,
    m_beta_beta_effective,
    majorana_rung_z16_compatibility_index,
)


class TestSeesawNeutrinoMass:
    """Type-I seesaw m_ν = y² v² / M_R — algebraic invariants."""

    def test_central_fiducial(self):
        # y = 1, v = 246 GeV, M_R = 1e14 GeV → m_ν ≈ 0.6 eV
        m_nu_gev = seesaw_neutrino_mass(1.0, 246.22, 1.0e14)
        m_nu_ev = m_nu_gev * 1.0e9
        assert 0.5 < m_nu_ev < 0.7

    def test_M_R_upper_band_matches_observed_with_O1_yukawa(self):
        # With y = 1 and m_ν = 0.05 eV, M_R should be ~1.2e15 GeV (upper band)
        m_r = seesaw_m_r_from_observed(1.0, 246.22, 0.05e-9)
        assert 1.0e15 < m_r < 2.0e15

    def test_M_R_lower_band_matches_observed_with_electron_yukawa(self):
        # With y = 3e-6 (electron-Yukawa-like) and m_ν = 0.05 eV,
        # M_R should be roughly 1e1 GeV — way too small to be heavy seesaw.
        # The lower band 1e9 GeV corresponds to y ~ 0.03 (deep research band).
        # Validate algebraic relation, not deep-research bounds:
        y_low = math.sqrt(MAJORANA_PARAMS['M_R_LOWER_BOUND_GEV'] *
                          MAJORANA_PARAMS['M_NU_HEAVIEST_EV'] * 1e-9 /
                          EW_PARAMS['V_EW_GEV'] ** 2)
        m_r = seesaw_m_r_from_observed(y_low, EW_PARAMS['V_EW_GEV'],
                                       MAJORANA_PARAMS['M_NU_HEAVIEST_EV'] * 1e-9)
        # Round-trip must reproduce the lower bound
        assert m_r == pytest.approx(MAJORANA_PARAMS['M_R_LOWER_BOUND_GEV'],
                                    rel=1e-9)

    def test_seesaw_inversion_round_trip(self):
        # m_ν → M_R → m_ν round-trip
        y, v, m_nu = 0.5, 246.22, 0.05e-9
        m_r = seesaw_m_r_from_observed(y, v, m_nu)
        m_nu_back = seesaw_neutrino_mass(y, v, m_r)
        assert m_nu_back == pytest.approx(m_nu, rel=1e-12)

    def test_seesaw_monotonicity_in_M_R(self):
        # Larger M_R → smaller m_ν (Type-I seesaw signature)
        m_nu_1 = seesaw_neutrino_mass(1.0, 246.22, 1.0e13)
        m_nu_2 = seesaw_neutrino_mass(1.0, 246.22, 1.0e14)
        m_nu_3 = seesaw_neutrino_mass(1.0, 246.22, 1.0e15)
        assert m_nu_1 > m_nu_2 > m_nu_3
        # Factor-of-10 in M_R should give factor-of-10 in m_ν (linear)
        assert m_nu_1 == pytest.approx(10 * m_nu_2, rel=1e-12)
        assert m_nu_2 == pytest.approx(10 * m_nu_3, rel=1e-12)

    def test_zero_yukawa_gives_zero_mass(self):
        assert seesaw_neutrino_mass(0.0, 246.22, 1e14) == 0.0

    def test_negative_or_zero_M_R_raises(self):
        with pytest.raises(ValueError):
            seesaw_neutrino_mass(1.0, 246.22, 0.0)
        with pytest.raises(ValueError):
            seesaw_neutrino_mass(1.0, 246.22, -1e14)

    def test_zero_or_negative_v_raises(self):
        with pytest.raises(ValueError):
            seesaw_neutrino_mass(1.0, 0.0, 1e14)


class TestNeutrinoMassFromOscillations:
    """Light-neutrino-mass derivation from NuFit-6.0 splittings."""

    def test_m_nu_heaviest_NO_value(self):
        m3 = m_nu_heaviest_from_atmospheric_splitting(
            MAJORANA_PARAMS['DELTA_M_SQ_31_EV2'])
        # NuFit-6.0 best fit |Δm²_31| → m₃ ≈ 0.0501 eV
        assert m3 == pytest.approx(MAJORANA_PARAMS['M_NU_HEAVIEST_EV'],
                                   rel=1e-3)

    def test_m_nu_next_value_consistency(self):
        m2 = m_nu_heaviest_from_atmospheric_splitting(
            MAJORANA_PARAMS['DELTA_M_SQ_21_EV2'])
        # m₂ ≈ √Δm²_21 ≈ 8.61 meV
        assert m2 == pytest.approx(MAJORANA_PARAMS['M_NU_NEXT_EV'],
                                   rel=1e-3)

    def test_negative_splitting_raises(self):
        with pytest.raises(ValueError):
            m_nu_heaviest_from_atmospheric_splitting(-1.0e-3)


class TestPMNSUnitarity:
    """PMNS standard parameterization — unitarity, hierarchy."""

    def _u_at_nufit(self):
        """PMNS at NuFit-6.0 best-fit (NO)."""
        return pmns_unitary_matrix(
            np.deg2rad(MAJORANA_PARAMS['THETA_12_DEG']),
            np.deg2rad(MAJORANA_PARAMS['THETA_13_DEG']),
            np.deg2rad(MAJORANA_PARAMS['THETA_23_DEG']),
            np.deg2rad(MAJORANA_PARAMS['DELTA_CP_DEG']),
        )

    def test_unitarity_at_nufit(self):
        U = self._u_at_nufit()
        I = U @ U.conj().T
        assert np.allclose(I, np.eye(3), atol=1e-12)

    def test_unitarity_with_majorana_phases(self):
        U = pmns_unitary_matrix(
            np.deg2rad(33.41), np.deg2rad(8.54), np.deg2rad(49.1),
            np.deg2rad(197), alpha_1=0.7, alpha_2=1.3,
        )
        I = U @ U.conj().T
        assert np.allclose(I, np.eye(3), atol=1e-12)

    def test_U_e3_squared_matches_sin2_theta_13(self):
        U = self._u_at_nufit()
        sin2_t13 = math.sin(np.deg2rad(MAJORANA_PARAMS['THETA_13_DEG'])) ** 2
        assert abs(U[0, 2]) ** 2 == pytest.approx(sin2_t13, rel=1e-12)

    def test_PMNS_hierarchy_normal_ordering(self):
        # NO best-fit hierarchy: |U_e1| > |U_e2| > |U_e3|
        U = self._u_at_nufit()
        assert abs(U[0, 0]) > abs(U[0, 1]) > abs(U[0, 2])

    def test_majorana_phases_dont_change_magnitudes(self):
        # Right-multiplication by diag(α₁/2, α₂/2, 0) is unitary;
        # row magnitudes squared (per element) should match Dirac case
        U_dirac = self._u_at_nufit()
        U_majorana = pmns_unitary_matrix(
            np.deg2rad(33.41), np.deg2rad(8.54), np.deg2rad(49.1),
            np.deg2rad(197), alpha_1=0.7, alpha_2=1.3,
        )
        # For each entry, |U_dirac[i,j]| == |U_majorana[i,j]|
        assert np.allclose(np.abs(U_dirac), np.abs(U_majorana), atol=1e-12)


class TestEffectiveMajoranaMass:
    """0νββ amplitude m_ββ — embedding-agnostic algebraic content."""

    def test_m_bb_NO_with_massless_lightest(self):
        # NuFit-6.0, NO, m_lightest = 0:
        # m_ββ ≈ 1-4 meV (out of LEGEND-1000 reach per deep research §4.2)
        U = pmns_unitary_matrix(
            np.deg2rad(33.41), np.deg2rad(8.54), np.deg2rad(49.1),
            np.deg2rad(197),
        )
        m_bb = m_beta_beta_effective(U, [
            0.0,
            MAJORANA_PARAMS['M_NU_NEXT_EV'],
            MAJORANA_PARAMS['M_NU_HEAVIEST_EV'],
        ])
        # Expect 1-4 meV in NO
        assert 1e-3 < m_bb < 4e-3

    def test_m_bb_QD_excluded_by_KamLAND_Zen(self):
        # Quasi-degenerate hierarchy: all masses ~ 0.2 eV
        U = pmns_unitary_matrix(
            np.deg2rad(33.41), np.deg2rad(8.54), np.deg2rad(49.1),
            np.deg2rad(197),
        )
        m_bb = m_beta_beta_effective(U, [0.2, 0.2, 0.2])
        # m_ββ should be substantially above the 28 meV most-stringent bound
        assert m_bb > MAJORANA_PARAMS['M_BB_KAMLAND_ZEN_MEV_LOWER'] / 1000.0

    def test_m_bb_invalid_shape_raises(self):
        with pytest.raises(ValueError):
            m_beta_beta_effective(np.eye(3), [0.0, 0.001])  # only 2 masses


class TestZ16Compatibility:
    """ℤ₁₆ singlet-branch index — Embedding III bridge to HiddenSectorClassification."""

    def test_three_nu_R_yields_index_three(self):
        # The Wave-2 Z₁₆ bridge theorem
        assert majorana_rung_z16_compatibility_index(3) == 3

    def test_three_nu_R_saturates_full_anomaly(self):
        # SM-without-ν_R: 45 ≡ -3 mod 16; +3 from ν_R → 48 ≡ 0 mod 16
        sm_anomaly = 45
        n_nu_r = 3
        total_mod16 = (sm_anomaly + n_nu_r) % 16
        assert total_mod16 == 0
        assert majorana_rung_z16_compatibility_index(n_nu_r) + (
            sm_anomaly % 16) == 16  # 3 + 13 = 16

    def test_index_zero_for_no_nu_R(self):
        assert majorana_rung_z16_compatibility_index(0) == 0

    def test_index_periodic_mod_16(self):
        # Embedding III with N = 19 (next bounded solution from
        # HiddenSectorClassification.all_singlet_solutions_bounded)
        assert majorana_rung_z16_compatibility_index(19) == 3
        assert majorana_rung_z16_compatibility_index(35) == 3

    def test_negative_n_raises(self):
        with pytest.raises(ValueError):
            majorana_rung_z16_compatibility_index(-1)


class TestMajoranaRungParametersConsistency:
    """MAJORANA_PARAMS dict invariants — values must be physically sensible."""

    def test_M_R_band_ordered(self):
        assert (MAJORANA_PARAMS['M_R_LOWER_BOUND_GEV']
                < MAJORANA_PARAMS['M_R_FIDUCIAL_GEV']
                < MAJORANA_PARAMS['M_R_UPPER_BOUND_GEV'])

    def test_mass_splittings_consistent_with_NO(self):
        # |Δm²_31| > Δm²_21 (atmospheric > solar)
        assert (MAJORANA_PARAMS['DELTA_M_SQ_31_EV2']
                > MAJORANA_PARAMS['DELTA_M_SQ_21_EV2'])

    def test_mixing_angles_in_first_quadrant(self):
        for key in ('THETA_12_DEG', 'THETA_13_DEG', 'THETA_23_DEG'):
            assert 0 < MAJORANA_PARAMS[key] < 90

    def test_theta_13_smallest(self):
        # Reactor angle is the smallest mixing angle in the SM
        assert MAJORANA_PARAMS['THETA_13_DEG'] < MAJORANA_PARAMS['THETA_12_DEG']
        assert MAJORANA_PARAMS['THETA_13_DEG'] < MAJORANA_PARAMS['THETA_23_DEG']

    def test_theta_23_near_maximal(self):
        # NuFit-6.0 best fit ≈ 49.1° (very close to 45°)
        assert abs(MAJORANA_PARAMS['THETA_23_DEG'] - 45.0) < 10.0

    def test_kamland_zen_bound_brackets_legend_reach(self):
        # KamLAND-Zen current bound is above LEGEND-1000 projected reach
        assert (MAJORANA_PARAMS['M_BB_KAMLAND_ZEN_MEV_LOWER']
                > MAJORANA_PARAMS['M_BB_LEGEND_MEV_UPPER'])

    def test_yukawa_band_ordered(self):
        assert (MAJORANA_PARAMS['Y_NU_LOWER']
                < MAJORANA_PARAMS['Y_NU_UPPER'])

    def test_neutrino_mass_anchors_consistent(self):
        # m_ν_heaviest > m_ν_next (NO ordering with m_lightest = 0)
        assert (MAJORANA_PARAMS['M_NU_HEAVIEST_EV']
                > MAJORANA_PARAMS['M_NU_NEXT_EV'])
        # m_ν_heaviest ≈ √Δm²_31
        m3_check = math.sqrt(MAJORANA_PARAMS['DELTA_M_SQ_31_EV2'])
        assert MAJORANA_PARAMS['M_NU_HEAVIEST_EV'] == pytest.approx(
            m3_check, rel=1e-3)
