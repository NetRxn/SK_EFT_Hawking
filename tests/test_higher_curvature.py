"""Tests for Phase 6e Wave 2: Higher-curvature structure.

Verifies the Python mirror of ``HigherCurvatureStructure.lean`` against
its declared Lean theorems plus standard 4D differential-geometry
sanity tests (de Sitter, Schwarzschild vacuum, basis-change identity).
"""

from __future__ import annotations
import math
import random

import pytest

from src.core.formulas import (
    higher_curvature_R_sq_coefficient,
    higher_curvature_Ricci_sq_coefficient,
    higher_curvature_Riemann_sq_coefficient,
    gauss_bonnet_4D_identity,
    weyl_squared_4D,
    higher_curvature_predicted_in_observational_band,
)
from src.higher_curvature import (
    StelleBasisCoefficients,
    stelle_basis_coefficients,
    a4_density,
    a4_density_in_RC2GB_basis,
    weyl_squared_4D as wsq_pkg,
    gauss_bonnet_4D as gb_pkg,
    gauss_bonnet_combination_check,
    weyl_squared_de_sitter_zero,
    weyl_squared_schwarzschild_vacuum,
    HC_OBS_BOUNDS,
    largest_predicted_coefficient,
    predictions_below_bound,
    pulsar_correctness_push_passes,
)
from src.core.constants import (
    HEAT_KERNEL_PARAMS,
    HIGHER_CURVATURE_PARAMS,
)


# ════════════════════════════════════════════════════════════════════
# Christensen-Duff a_4 closed forms
# ════════════════════════════════════════════════════════════════════

class TestA4Closed_Forms:
    """Wave 1 a_4 coefficients with the (4π)⁻² factor included."""

    def test_a4_R_sq_at_unit_Nf(self):
        v = higher_curvature_R_sq_coefficient(1.0)
        expected = -5.0 / (12.0 * 180.0) / HEAT_KERNEL_PARAMS['FOUR_PI_SQ']
        assert math.isclose(v, expected, rel_tol=1e-12)

    def test_a4_Ricci_sq_at_unit_Nf(self):
        v = higher_curvature_Ricci_sq_coefficient(1.0)
        expected = 7.0 / (12.0 * 180.0) / HEAT_KERNEL_PARAMS['FOUR_PI_SQ']
        assert math.isclose(v, expected, rel_tol=1e-12)

    def test_a4_Riemann_sq_at_unit_Nf(self):
        v = higher_curvature_Riemann_sq_coefficient(1.0)
        expected = -12.0 / (12.0 * 180.0) / HEAT_KERNEL_PARAMS['FOUR_PI_SQ']
        assert math.isclose(v, expected, rel_tol=1e-12)

    def test_signs_at_positive_Nf(self):
        for n in (1.0, 5.0, 24.0, 27.0, 100.0):
            assert higher_curvature_R_sq_coefficient(n) < 0
            assert higher_curvature_Ricci_sq_coefficient(n) > 0
            assert higher_curvature_Riemann_sq_coefficient(n) < 0

    def test_linearity_in_Nf(self):
        c1 = higher_curvature_Riemann_sq_coefficient(1.0)
        c100 = higher_curvature_Riemann_sq_coefficient(100.0)
        assert math.isclose(c100, 100.0 * c1, rel_tol=1e-12)


# ════════════════════════════════════════════════════════════════════
# Gauss-Bonnet identity (4D)
# ════════════════════════════════════════════════════════════════════

class TestGaussBonnet4D:

    def test_definition(self):
        # GB = R² - 4 Ricci² + Riemann²
        assert math.isclose(gauss_bonnet_4D_identity(1.0, 0.0, 0.0), 1.0)
        assert math.isclose(gauss_bonnet_4D_identity(0.0, 1.0, 0.0), -4.0)
        assert math.isclose(gauss_bonnet_4D_identity(0.0, 0.0, 1.0), 1.0)

    def test_de_sitter_value(self):
        # de Sitter at H=1: R²=144, Ricci²=36, Riem²=24 → GB = 144-144+24 = 24
        assert math.isclose(gauss_bonnet_4D_identity(144.0, 36.0, 24.0),
                              24.0, rel_tol=1e-12)

    def test_schwarzschild_vacuum(self):
        # Vacuum (R=Ricci=0): GB reduces to Riemann² alone
        Riemann = 48.0 / 64.0  # 48 M²/r⁶ at M=1, r=2
        assert math.isclose(gauss_bonnet_4D_identity(0.0, 0.0, Riemann),
                              Riemann, rel_tol=1e-12)

    def test_package_consistency(self):
        # src.higher_curvature.gauss_bonnet_4D == formulas.gauss_bonnet_4D_identity
        for R, Ricci, Riem in [(1.0, 2.0, 3.0), (10.0, -5.0, 8.0)]:
            assert math.isclose(
                gb_pkg(R, Ricci, Riem),
                gauss_bonnet_4D_identity(R, Ricci, Riem),
                rel_tol=1e-15,
            )


# ════════════════════════════════════════════════════════════════════
# Weyl-squared (4D)
# ════════════════════════════════════════════════════════════════════

class TestWeylSquared4D:

    def test_definition(self):
        # C² = Riemann² - 2 Ricci² + (1/3) R²
        assert math.isclose(weyl_squared_4D(3.0, 0.0, 0.0), 1.0)
        assert math.isclose(weyl_squared_4D(0.0, 1.0, 0.0), -2.0)
        assert math.isclose(weyl_squared_4D(0.0, 0.0, 1.0), 1.0)

    def test_de_sitter_zero(self):
        # de Sitter at H=1: C² = 0 (conformally flat)
        v = weyl_squared_4D(144.0, 36.0, 24.0)
        assert abs(v) < 1e-9

    def test_schwarzschild_vacuum_eq_riemann(self):
        # In any vacuum (R=Ricci=0): C² = Riemann²
        for Riem in (0.5, 1.0, 100.0):
            assert math.isclose(weyl_squared_4D(0.0, 0.0, Riem), Riem,
                                  rel_tol=1e-12)

    def test_de_sitter_at_various_H(self):
        for H in (0.5, 1.0, 2.0, 10.0):
            assert weyl_squared_de_sitter_zero(H, tol=1e-9)

    def test_schwarzschild_check(self):
        for M, r in [(1.0, 2.0), (5.0, 10.0), (0.5, 1.5)]:
            assert weyl_squared_schwarzschild_vacuum(M, r, tol=1e-9)


# ════════════════════════════════════════════════════════════════════
# Stelle basis-change algebra
# ════════════════════════════════════════════════════════════════════

class TestStelleBasis:
    """Sign-definite (α, β, γ) plus basis-change identity."""

    def test_alpha_beta_gamma_signs(self):
        for n in (1.0, 5.0, 24.0, 27.0, 100.0):
            c = stelle_basis_coefficients(n)
            assert c.alpha < 0   # α(N_f) < 0
            assert c.beta < 0    # β(N_f) < 0
            assert 0 < c.gamma   # γ(N_f) > 0  (topological sign-definite)

    def test_alpha_closed_form_at_unit_Nf(self):
        c = stelle_basis_coefficients(1.0)
        expected_alpha = -1.0 / 324.0 / HEAT_KERNEL_PARAMS['FOUR_PI_SQ']
        assert math.isclose(c.alpha, expected_alpha, rel_tol=1e-12)

    def test_beta_closed_form_at_unit_Nf(self):
        c = stelle_basis_coefficients(1.0)
        expected_beta = -41.0 / 4320.0 / HEAT_KERNEL_PARAMS['FOUR_PI_SQ']
        assert math.isclose(c.beta, expected_beta, rel_tol=1e-12)

    def test_gamma_closed_form_at_unit_Nf(self):
        c = stelle_basis_coefficients(1.0)
        expected_gamma = 17.0 / 4320.0 / HEAT_KERNEL_PARAMS['FOUR_PI_SQ']
        assert math.isclose(c.gamma, expected_gamma, rel_tol=1e-12)

    def test_basis_change_identity_random(self):
        """Lean: a4_density_eq_a4_density_in_RC2GB_basis."""
        random.seed(2026_04_29)
        for _ in range(50):
            N_f = random.uniform(1.0, 100.0)
            R = random.uniform(-100.0, 100.0)
            Ricci = random.uniform(-100.0, 100.0)
            Riem = random.uniform(-100.0, 100.0)
            a = a4_density(N_f, R, Ricci, Riem)
            b = a4_density_in_RC2GB_basis(N_f, R, Ricci, Riem)
            # absolute residual (denominators are O(1e-3); use abs tol)
            assert abs(a - b) < 1e-12

    def test_basis_change_at_de_sitter(self):
        # de Sitter at H=1
        for n in (24.0, 27.0):
            a = a4_density(n, 144.0, 36.0, 24.0)
            b = a4_density_in_RC2GB_basis(n, 144.0, 36.0, 24.0)
            assert abs(a - b) < 1e-12


# ════════════════════════════════════════════════════════════════════
# Gauss-Bonnet ↔ Weyl algebraic identity
# ════════════════════════════════════════════════════════════════════

class TestGBMinusWeylIdentity:
    """Lean: gaussBonnet_minus_weyl_eq_R_minus_Ricci_combination."""

    def test_identity_random(self):
        random.seed(101)
        for _ in range(20):
            R, Ricci, Riem = (random.uniform(-100.0, 100.0) for _ in range(3))
            assert gauss_bonnet_combination_check(R, Ricci, Riem)

    def test_identity_at_de_sitter(self):
        # GB - C² = (2/3) R² - 2 Ricci²
        # At de Sitter: GB=24, C²=0; (2/3)(144)-2(36) = 96-72 = 24 ✓
        assert gauss_bonnet_combination_check(144.0, 36.0, 24.0)

    def test_identity_at_schwarzschild(self):
        # Vacuum: GB = Riem², C² = Riem², so LHS = 0; RHS = 0 - 0 = 0 ✓
        assert gauss_bonnet_combination_check(0.0, 0.0, 1.0)


# ════════════════════════════════════════════════════════════════════
# Observational-bound correctness-push
# ════════════════════════════════════════════════════════════════════

class TestObservationalBounds:

    def test_pulsar_is_tightest(self):
        # Hulse-Taylor pulsar ≪ LIGO, Cassini, SRG
        assert HC_OBS_BOUNDS['pulsar_C_sq'] < HC_OBS_BOUNDS['LIGO_C_sq']
        assert HC_OBS_BOUNDS['pulsar_C_sq'] < HC_OBS_BOUNDS['cassini_C_sq']
        assert HC_OBS_BOUNDS['pulsar_C_sq'] < HC_OBS_BOUNDS['SRG_R_sq']

    def test_largest_predicted_at_SM(self):
        # |c_Riemann²(N_f=24)| ≈ 24 / (180 · (4π)²) ≈ 8.4e-4
        v = largest_predicted_coefficient(24.0)
        assert v < 1e-2
        assert v > 1e-5

    def test_predictions_below_pulsar_bound_at_SM(self):
        assert predictions_below_bound(24.0, HC_OBS_BOUNDS['pulsar_C_sq'])
        assert predictions_below_bound(27.0, HC_OBS_BOUNDS['pulsar_C_sq'])

    def test_predictions_below_pulsar_bound_at_high_Nf(self):
        # Even at unrealistically high N_f = 100, predictions below pulsar
        assert predictions_below_bound(100.0,
                                          HC_OBS_BOUNDS['pulsar_C_sq'])

    def test_correctness_push_passes_default(self):
        # Lean: higher_curvature_below_pulsar_bound (instantiated at SM)
        assert pulsar_correctness_push_passes()

    def test_correctness_push_at_SM_plus_nu_R(self):
        assert pulsar_correctness_push_passes(N_f=27.0)

    def test_predictions_NOT_below_artificial_zero(self):
        # Falsifier: predictions strictly positive (Lean:
        # higher_curvature_predictions_strictly_positive).
        # An artificial bound at 1e-10 should fail since |c_Riemann²(24)|
        # ≈ 8e-4.
        assert not predictions_below_bound(24.0, 1e-10)


# ════════════════════════════════════════════════════════════════════
# Constants consistency
# ════════════════════════════════════════════════════════════════════

class TestConstantsConsistency:

    def test_higher_curvature_params_keys(self):
        for k in ('A4_R_SQ_PER_NF', 'A4_RICCI_SQ_PER_NF',
                  'A4_RIEMANN_SQ_PER_NF',
                  'GB_R_SQ_COEF', 'GB_RICCI_SQ_COEF', 'GB_RIEMANN_SQ_COEF',
                  'WEYL_SQ_FROM_RIEMANN_SQ', 'WEYL_SQ_FROM_RICCI_SQ',
                  'WEYL_SQ_FROM_R_SQ', 'N_F_STANDARD_MODEL',
                  'N_F_STANDARD_MODEL_NU_R',
                  'HC_BOUND_LIGO_C_SQ', 'HC_BOUND_PULSAR_C_SQ',
                  'HC_BOUND_SRG_R_SQ', 'HC_BOUND_CASSINI_C_SQ',
                  'HC_PASS_BAND_FACTOR'):
            assert k in HIGHER_CURVATURE_PARAMS

    def test_HC_PARAMS_GB_coefficients(self):
        # 𝒢 = R² - 4 R_μν² + R_μνρσ²
        assert HIGHER_CURVATURE_PARAMS['GB_R_SQ_COEF'] == 1.0
        assert HIGHER_CURVATURE_PARAMS['GB_RICCI_SQ_COEF'] == -4.0
        assert HIGHER_CURVATURE_PARAMS['GB_RIEMANN_SQ_COEF'] == 1.0

    def test_HC_PARAMS_Weyl_coefficients(self):
        # C² = R_μνρσ² - 2 R_μν² + (1/3) R²
        assert HIGHER_CURVATURE_PARAMS['WEYL_SQ_FROM_RIEMANN_SQ'] == 1.0
        assert HIGHER_CURVATURE_PARAMS['WEYL_SQ_FROM_RICCI_SQ'] == -2.0
        assert math.isclose(HIGHER_CURVATURE_PARAMS['WEYL_SQ_FROM_R_SQ'],
                              1.0 / 3.0, rel_tol=1e-12)

    def test_HC_PARAMS_a4_per_Nf_match_HEAT_KERNEL_PARAMS(self):
        # The a_4 coefficient rationals must duplicate exactly from
        # Wave 1 (HEAT_KERNEL_PARAMS).
        assert (HIGHER_CURVATURE_PARAMS['A4_R_SQ_PER_NF']
                == HEAT_KERNEL_PARAMS['A4_DIRAC_R_SQ_COEF'])
        assert (HIGHER_CURVATURE_PARAMS['A4_RICCI_SQ_PER_NF']
                == HEAT_KERNEL_PARAMS['A4_DIRAC_RICCI_SQ_COEF'])
        assert (HIGHER_CURVATURE_PARAMS['A4_RIEMANN_SQ_PER_NF']
                == HEAT_KERNEL_PARAMS['A4_DIRAC_RIEMANN_SQ_COEF'])

    def test_observational_bounds_positive(self):
        for k in ('HC_BOUND_LIGO_C_SQ', 'HC_BOUND_PULSAR_C_SQ',
                  'HC_BOUND_SRG_R_SQ', 'HC_BOUND_CASSINI_C_SQ'):
            assert HIGHER_CURVATURE_PARAMS[k] > 0

    def test_pulsar_tightest_in_constants(self):
        assert (HIGHER_CURVATURE_PARAMS['HC_BOUND_PULSAR_C_SQ']
                < HIGHER_CURVATURE_PARAMS['HC_BOUND_LIGO_C_SQ'])
        assert (HIGHER_CURVATURE_PARAMS['HC_BOUND_PULSAR_C_SQ']
                < HIGHER_CURVATURE_PARAMS['HC_BOUND_CASSINI_C_SQ'])

    def test_N_f_SM_values(self):
        assert HIGHER_CURVATURE_PARAMS['N_F_STANDARD_MODEL'] == 24
        assert HIGHER_CURVATURE_PARAMS['N_F_STANDARD_MODEL_NU_R'] == 27


# ════════════════════════════════════════════════════════════════════
# Cross-bridge to formulas.higher_curvature_predicted_in_observational_band
# ════════════════════════════════════════════════════════════════════

class TestObservationalBandFormula:

    def test_passes_at_LIGO_bound(self):
        assert higher_curvature_predicted_in_observational_band(
            24.0, HIGHER_CURVATURE_PARAMS['HC_BOUND_LIGO_C_SQ'])

    def test_passes_at_pulsar_bound(self):
        assert higher_curvature_predicted_in_observational_band(
            27.0, HIGHER_CURVATURE_PARAMS['HC_BOUND_PULSAR_C_SQ'])

    def test_fails_at_artificially_tight_bound(self):
        # |c_Riemann²(24)| ≈ 8.4e-4 — should NOT be ≤ 1e-10
        assert not higher_curvature_predicted_in_observational_band(
            24.0, 1.0e-10)

    def test_observational_band_anchor_value_at_Nf_27(self):
        """Golden test: pin the load-bearing largest-coefficient value
        consumed by `higher_curvature_predicted_in_observational_band`
        at SM-with-νᴿ count N_f=27. The Riemann² coefficient dominates
        the max:

            |c_Riem(27)| = 27 / (180 (4π)²) ≈ 9.498861×10⁻⁴

        This is the explicit ``9.49×10⁻⁴`` numerical anchor cited in
        paper40 §5 ("Anchoring the '62 orders below' claim"). The
        ratio against the tightest observational ceiling
        HC_BOUND_PULSAR_C_SQ = 10⁵⁹ then sits at ≈ 1.054×10⁻⁶² — the
        "~62 orders of magnitude below" feasibility headline.

        Test_kind: golden (math.isclose). Pairs the boolean-shape
        bounds tests above with a numeric-shape pin so Gate 4
        (ComputationCorrectness) sees a substantive verification of
        the formula's load-bearing internal value, not just the
        boolean output. Phase 6i Wave 2 Stage 13 Finding 4.1 fix.
        """
        largest = max(
            abs(higher_curvature_R_sq_coefficient(27)),
            abs(higher_curvature_Ricci_sq_coefficient(27)),
            abs(higher_curvature_Riemann_sq_coefficient(27)),
        )
        # Closed form: -N_f / (180 (4π)²) at N_f=27.
        expected = 27.0 / (180.0 * (4.0 * math.pi) ** 2)
        assert math.isclose(largest, expected, rel_tol=1e-12)
        # Cross-pin against the paper40 §5 stated anchor (4 sig fig):
        assert math.isclose(largest, 9.498861e-4, rel_tol=1e-6)
        # Confirm the formula consumed by paper40 returns True at the
        # tightest published ceiling:
        assert higher_curvature_predicted_in_observational_band(
            27, HIGHER_CURVATURE_PARAMS['HC_BOUND_PULSAR_C_SQ'])
