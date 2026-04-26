"""Phase 5z Wave 1b tests: BHL gauge-embedding numerics.

Tests for the concrete BHL leading-order Higgs mass formula, the BHL gap
problem demonstration, and the Hill 2025 bilocal correction recovering
m_H = 125 GeV.
"""

from __future__ import annotations

import math

import numpy as np
import pytest

from src.core.formulas import (
    bhl_higgs_mass,
    bhl_minimal_overshoot_factor,
    bilocal_correction_factor,
    bilocal_corrected_higgs_mass,
    pagels_stokar_vev_sq,
)
from src.scalar_rung import (
    bhl_minimal_prediction,
    bhl_gap_against_pdg,
    bilocal_correction_required,
    bilocal_correction_scan,
    bhl_pagels_stokar_vev_check,
)


class TestBHLLeadingOrder:
    """BHL leading-order m_H = sqrt(2) * m_t (Nambu sum rule)."""

    def test_bhl_higgs_mass_at_top_220(self):
        m_h = bhl_higgs_mass(220.0)
        assert m_h == pytest.approx(311.13, abs=0.01)

    def test_bhl_higgs_mass_ratio_is_sqrt2(self):
        m_t = 173.0
        ratio = bhl_higgs_mass(m_t) / m_t
        assert ratio == pytest.approx(math.sqrt(2.0), rel=1e-12)

    def test_bhl_higgs_mass_positive(self):
        for m_t in [50.0, 100.0, 173.0, 220.0, 500.0]:
            assert bhl_higgs_mass(m_t) > 0

    def test_bhl_higgs_mass_rejects_nonpositive(self):
        with pytest.raises(ValueError):
            bhl_higgs_mass(0.0)
        with pytest.raises(ValueError):
            bhl_higgs_mass(-1.0)


class TestBHLGapProblem:
    """The BHL minimal prediction overshoots PDG m_H by ~2.5×."""

    def test_overshoot_factor_at_pdg(self):
        factor = bhl_minimal_overshoot_factor()
        # m_H_BHL ≈ 311 / 125.20 ≈ 2.485
        assert factor == pytest.approx(2.485, abs=0.01)

    def test_gap_against_pdg_positive(self):
        gap = bhl_gap_against_pdg()
        assert gap["m_H_BHL_GeV"] > gap["m_H_PDG_GeV"]
        assert gap["overshoot_factor"] > 2.0
        assert gap["gap_GeV"] > 150.0

    def test_minimal_prediction_includes_sqrt2(self):
        pred = bhl_minimal_prediction()
        assert pred["m_t_GeV"] == 220.0
        assert pred["m_H_over_m_t"] == pytest.approx(math.sqrt(2.0))


class TestBilocalCorrection:
    """Hill 2025 bilocal correction recovering m_H = 125 GeV."""

    def test_dilution_factor_basic(self):
        d = bilocal_correction_factor(0.5, 1.0)
        assert d == pytest.approx(0.5)

    def test_dilution_pointlike_limit(self):
        # Equal phi → dilution = 1 (BHL minimal limit)
        d = bilocal_correction_factor(1.0, 1.0)
        assert d == pytest.approx(1.0)

    def test_dilution_rejects_nonpositive(self):
        with pytest.raises(ValueError):
            bilocal_correction_factor(-1.0, 1.0)
        with pytest.raises(ValueError):
            bilocal_correction_factor(1.0, 0.0)

    def test_corrected_mass_at_pointlike_recovers_bhl(self):
        m_t = 220.0
        corrected = bilocal_corrected_higgs_mass(1.0, m_t)
        bhl = bhl_higgs_mass(m_t)
        assert corrected == pytest.approx(bhl, rel=1e-12)

    def test_corrected_mass_at_dilution_402_matches_pdg(self):
        # Hill 2025 natural value: dilution ≈ 0.402 → m_H ≈ 125 GeV
        m_h = bilocal_corrected_higgs_mass(0.402, 220.0)
        assert m_h == pytest.approx(125.07, abs=0.5)

    def test_required_dilution_for_pdg(self):
        d = bilocal_correction_required(125.20, 220.0)
        # At m_t = 220, m_H_BHL ≈ 311, so dilution = 125.20/311.13 ≈ 0.402
        assert d == pytest.approx(0.4024, abs=0.001)
        assert 0 < d < 1

    def test_corrected_mass_rejects_nonpositive(self):
        with pytest.raises(ValueError):
            bilocal_corrected_higgs_mass(0.0, 220.0)
        with pytest.raises(ValueError):
            bilocal_corrected_higgs_mass(0.5, 0.0)


class TestBilocalScan:
    """Scan-style utilities for figure generation."""

    def test_scan_monotonic_in_dilution(self):
        # Higher dilution → higher corrected m_H (linear relationship)
        dilutions = np.linspace(0.1, 1.0, 10)
        masses = bilocal_correction_scan(dilutions)
        assert masses.shape == (10,)
        # Strictly monotonic increasing
        assert np.all(np.diff(masses) > 0)

    def test_scan_endpoints_match_formulas(self):
        # At dilution = 1.0 → BHL minimal; at 0.402 → PDG
        masses = bilocal_correction_scan(np.array([0.402, 1.0]))
        assert masses[0] == pytest.approx(125.07, abs=0.5)
        assert masses[1] == pytest.approx(bhl_higgs_mass(220.0), rel=1e-12)


class TestPagelsStokar:
    """Pagels-Stokar EW VEV formula sanity."""

    def test_vev_sq_positive_at_sm_benchmark(self):
        # SM: N_c = 3, m_t = 173, Λ = M_Pl ≈ 1.22e19
        v_sq = pagels_stokar_vev_sq(3, 173.0, 1.22e19)
        assert v_sq > 0

    def test_vev_sq_check_wraps_correctly(self):
        v_sq_a = pagels_stokar_vev_sq(3, 173.0, 1.22e19)
        v_sq_b = bhl_pagels_stokar_vev_check()
        assert v_sq_a == pytest.approx(v_sq_b, rel=1e-12)

    def test_vev_sq_rejects_nonpositive(self):
        with pytest.raises(ValueError):
            pagels_stokar_vev_sq(0, 173.0, 1e19)
        with pytest.raises(ValueError):
            pagels_stokar_vev_sq(3, 0.0, 1e19)
        # Λ ≤ m_t fails (no log)
        with pytest.raises(ValueError):
            pagels_stokar_vev_sq(3, 173.0, 100.0)

    def test_vev_sq_grows_with_log_lambda(self):
        # Larger UV cutoff → larger ln(Λ²/m_t²) → larger v²
        v1 = pagels_stokar_vev_sq(3, 173.0, 1e15)
        v2 = pagels_stokar_vev_sq(3, 173.0, 1e19)
        assert v2 > v1


class TestBHLLeanCrossReferences:
    """Validates Lean-side identities at numerical level."""

    def test_lean_thm_bhl_higgs_mass_eq_sqrt2(self):
        # Lean: bhlHiggsMass_eq_sqrt2_times_top
        for m_t in [50.0, 100.0, 173.0, 220.0]:
            assert bhl_higgs_mass(m_t) == pytest.approx(
                math.sqrt(2.0) * m_t, rel=1e-12
            )

    def test_lean_thm_bhl_higgs_mass_sq(self):
        # Lean: bhlHiggsMass_sq states (bhlHiggsMass m_t)^2 = 2 * m_t^2
        for m_t in [50.0, 173.0, 220.0]:
            m_h = bhl_higgs_mass(m_t)
            assert m_h ** 2 == pytest.approx(2 * m_t ** 2, rel=1e-12)

    def test_lean_thm_bhl_minimal_overshoots_250(self):
        # Lean: bhl_minimal_overshoots_pdg states 250 < bhlMinimalHiggsMass
        # Numerical: bhlMinimalHiggsMass = sqrt(2) * 220 ≈ 311.13 > 250 ✓
        bhl_minimal = bhl_higgs_mass(220.0)
        assert bhl_minimal > 250.0

    def test_lean_thm_bilocal_correction_can_match_pdg(self):
        # Lean: bilocal_correction_can_match_pdg uses dilution = 0.402,
        # phi_inf = 1, m_t = 220. Matches |m_H - 125| < 1.
        m_h = bilocal_corrected_higgs_mass(0.402, 220.0)
        assert abs(m_h - 125.0) < 1.0
