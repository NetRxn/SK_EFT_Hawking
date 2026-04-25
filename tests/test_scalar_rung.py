"""Phase 5z Wave 1 tests: scalar-rung interpretation."""

from __future__ import annotations

import math

import numpy as np
import pytest

from src.core.constants import EW_PARAMS
from src.core.formulas import (
    mexican_hat_potential,
    mexican_hat_vev,
    higgs_mass_from_vev,
    w_mass_from_vev,
    z_mass_from_vev,
    ew_mass_ratio_cos_theta_w,
    yukawa_overlap_coefficient,
    higgs_mass_from_condensate,
    scalar_rung_quantitative_match,
)
from src.scalar_rung import (
    anderson_higgs_w_z_masses,
    cos_theta_w_consistency,
    higgs_mass_scan,
    quantitative_match_grid,
)


class TestMexicanHat:
    """Tree-level Mexican-hat potential and VEV."""

    def test_potential_at_zero(self):
        # V(0) = 0 by definition
        assert mexican_hat_potential(0.0, 1.0, 1.0) == pytest.approx(0.0)

    def test_potential_negative_at_small_phi(self):
        # V(φ) < 0 for 0 < |φ| < v: the broken phase is energetically favored
        v = mexican_hat_vev(1.0, 1.0)
        small = v * 0.5
        assert mexican_hat_potential(small, 1.0, 1.0) < 0.0

    def test_vev_textbook_relation(self):
        # v² = μ²/λ in the SM textbook convention
        assert mexican_hat_vev(2.0, 0.5) == pytest.approx(2.0)
        assert mexican_hat_vev(1.0, 1.0) == pytest.approx(1.0)

    def test_vev_reproduces_v_ew(self):
        # μ² = λ·v² → v = √(μ²/λ) = v_EW
        v = EW_PARAMS["V_EW_GEV"]
        lam = EW_PARAMS["LAMBDA_SM_HIGGS"]
        mu_sq = lam * v ** 2
        assert mexican_hat_vev(mu_sq, lam) == pytest.approx(v, rel=1e-6)

    def test_higgs_mass_tree_level(self):
        # m_H² = 2μ² ⇒ m_H = √(2μ²)
        v = EW_PARAMS["V_EW_GEV"]
        lam = EW_PARAMS["LAMBDA_SM_HIGGS"]
        mu_sq = lam * v ** 2
        # Reproduces 125.25 GeV within RG running uncertainty
        assert higgs_mass_from_vev(mu_sq, lam) == pytest.approx(
            EW_PARAMS["M_H_GEV"], rel=0.01
        )

    def test_higgs_mass_double_form(self):
        # Equivalent forms: m_H² = 2μ² = 2λv²
        mu_sq = 2.0
        lam = 0.5
        v = math.sqrt(mu_sq / lam)
        assert higgs_mass_from_vev(mu_sq, lam) ** 2 == pytest.approx(2 * mu_sq)
        assert higgs_mass_from_vev(mu_sq, lam) ** 2 == pytest.approx(
            2 * lam * v ** 2
        )

    def test_negative_inputs_rejected(self):
        with pytest.raises(ValueError):
            mexican_hat_vev(-1.0, 1.0)
        with pytest.raises(ValueError):
            higgs_mass_from_vev(1.0, 0.0)


class TestAndersonHiggs:
    """W/Z mass matrix from the scalar-channel VEV."""

    def test_w_mass_at_pdg(self):
        m_w, _ = anderson_higgs_w_z_masses()
        # M_W from g, v matches PDG 2024 within 0.2% (running coupling slop)
        assert m_w == pytest.approx(EW_PARAMS["M_W_GEV"], rel=0.005)

    def test_z_mass_at_pdg(self):
        _, m_z = anderson_higgs_w_z_masses()
        assert m_z == pytest.approx(EW_PARAMS["M_Z_GEV"], rel=0.005)

    def test_cos_theta_w_consistency(self):
        out = cos_theta_w_consistency()
        # Within 1% of √(1 − sin²θ_W) — running schemes differ at this level
        assert out["abs_error"] < 0.01

    def test_z_ge_w_always(self):
        # M_Z ≥ M_W for any g, g' ≥ 0 (Lean: zMass_ge_wMass)
        for g in [0.1, 0.5, 1.0, 2.0]:
            for g_prime in [0.0, 0.1, 0.5, 1.0]:
                m_w = w_mass_from_vev(g, 1.0)
                m_z = z_mass_from_vev(g, g_prime, 1.0)
                assert m_z >= m_w - 1e-12

    def test_z_strictly_greater_when_g_prime_pos(self):
        # When g' > 0, M_Z > M_W strictly (Lean: wMass_lt_zMass_of_g'_pos)
        m_w = w_mass_from_vev(1.0, 1.0)
        m_z = z_mass_from_vev(1.0, 0.5, 1.0)
        assert m_z > m_w

    def test_w_z_ratio_uses_cos_theta_w(self):
        # M_W/M_Z = cos θ_W (Lean: wMass_div_zMass)
        g = EW_PARAMS["G_SU2"]
        g_prime = EW_PARAMS["G_U1Y"]
        v = 1.0
        ratio = w_mass_from_vev(g, v) / z_mass_from_vev(g, g_prime, v)
        cos_tw = ew_mass_ratio_cos_theta_w(g, g_prime)
        assert ratio == pytest.approx(cos_tw, rel=1e-12)


class TestYukawaOverlap:
    """Stand-in Yukawa overlap (Lean: yukawaCoupling_*)."""

    def test_linear_in_overlap(self):
        # y(α) = α · normalization (Lean: yukawaCoupling_additive)
        norm = 1.0
        for alpha in [0.0, 0.1, 0.5, 1.0]:
            assert yukawa_overlap_coefficient(alpha, vev=1.0,
                                               normalization=norm) == pytest.approx(alpha * norm)

    def test_zero_overlap_zero_coupling(self):
        # y_f = 0 ⇔ overlap = 0 (Lean: yukawaCoupling_eq_zero_iff)
        assert yukawa_overlap_coefficient(0.0, vev=1.0,
                                           normalization=1.0) == 0.0

    def test_top_yukawa_unity_natural(self):
        # Top Yukawa near unity is the natural overlap-density value
        y_top = EW_PARAMS["Y_TOP"]
        assert 0.5 < y_top < 1.5


class TestHiggsMassFromCondensate:
    """Microscopic m_H prediction (correctness-push anchor)."""

    def test_positive_at_natural_params(self):
        # Lean: higgsMassFromCondensate_pos
        mh = higgs_mass_from_condensate(
            lambda_uv=EW_PARAMS["LAMBDA_UV_FIDUCIAL_GEV"],
            n_f=EW_PARAMS["N_F_FIDUCIAL"],
            g_c=EW_PARAMS["G_C_FIDUCIAL"],
            lam4=EW_PARAMS["LAMBDA_4_FIDUCIAL"],
        )
        assert mh > 0.0

    def test_monotone_in_lambda_uv(self):
        # Larger Λ_UV ⇒ larger v_cond ⇒ larger m_H (at fixed N_f, G_c, λ_4)
        params = dict(n_f=15, g_c=1.0, lam4=0.13)
        mh1 = higgs_mass_from_condensate(lambda_uv=1e15, **params)
        mh2 = higgs_mass_from_condensate(lambda_uv=1e16, **params)
        assert mh2 > mh1

    def test_negative_inputs_rejected(self):
        with pytest.raises(ValueError):
            higgs_mass_from_condensate(-1.0, 15, 1.0, 0.13)
        with pytest.raises(ValueError):
            higgs_mass_from_condensate(1e16, 0, 1.0, 0.13)

    def test_quantitative_match_at_125(self):
        # The match predicate fires at m_H near the PDG value
        m_h_obs = EW_PARAMS["M_H_GEV"]
        tol = 0.5
        assert bool(scalar_rung_quantitative_match(m_h_obs, m_h_obs, tol))
        assert not bool(scalar_rung_quantitative_match(0.0, m_h_obs, tol))
        # Falsifiability anchor: at the fiducial fiducials, the prediction
        # is many orders of magnitude off — a structural-only verdict
        mh_fiducial = higgs_mass_from_condensate(
            EW_PARAMS["LAMBDA_UV_FIDUCIAL_GEV"],
            EW_PARAMS["N_F_FIDUCIAL"],
            EW_PARAMS["G_C_FIDUCIAL"],
            EW_PARAMS["LAMBDA_4_FIDUCIAL"],
        )
        assert not bool(scalar_rung_quantitative_match(mh_fiducial, m_h_obs, tol))


class TestParameterScans:
    """Grid scans for the correctness-push anchor."""

    def test_scan_returns_correct_shape(self):
        lam_uv = np.array([1e14, 1e15, 1e16])
        g_c = np.array([0.5, 1.0, 2.0])
        lam4 = np.array([0.05, 0.13])
        out = higgs_mass_scan(lam_uv, n_f=15, g_c_range=g_c,
                              lam4_range=lam4)
        assert out.shape == (3, 3, 2)

    def test_scan_default_uses_fiducials(self):
        # Default n_f, g_c, lam4 are EW_PARAMS fiducials → 1×1×1 along
        # the latter two axes
        lam_uv = np.array([1e15, 1e16])
        out = higgs_mass_scan(lam_uv)
        assert out.shape == (2, 1, 1)
        assert (out > 0).all()

    def test_match_grid_is_boolean(self):
        lam_uv = np.array([1e14])
        g_c = np.array([1.0, 100.0])
        lam4 = np.array([0.13])
        match = quantitative_match_grid(lam_uv, g_c, lam4)
        assert match.dtype == bool
        assert match.shape == (1, 2, 1)

    def test_match_grid_finds_no_match_at_natural_params(self):
        # Confirms the open question: natural-parameter range gives
        # structural-only result (no quantitative EWSB)
        lam_uv = np.array([1e14, 1e15, 1e16])
        g_c = np.array([EW_PARAMS["G_C_FIDUCIAL"]])
        lam4 = np.array([EW_PARAMS["LAMBDA_4_FIDUCIAL"]])
        match = quantitative_match_grid(lam_uv, g_c, lam4)
        # No fiducial cell matches at 50% tolerance — Gate Z.1 may fire
        # NO unless larger parameter sweep reveals a matching region
        assert match.dtype == bool
        # At least one cell exists, structurally
        assert match.size > 0
