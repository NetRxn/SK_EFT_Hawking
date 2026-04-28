"""Tests for Phase 6e Wave 3 — Nonlinear Diffeomorphism Invariance.

Mirrors the Lean theorems in
``lean/SKEFTHawking/NonlinearDiffInvariance.lean`` at the numerical
level.  All tests assert path-b residuals are at machine precision for
the Christensen-Duff Dirac bundle and detectably nonzero for the
perturbed bundle (falsifier).
"""

import math
import numpy as np
import pytest

from src.core.constants import (
    DIFF_INVARIANCE_PARAMS,
    HEAT_KERNEL_PARAMS,
    HIGHER_CURVATURE_PARAMS,
)
from src.core.formulas import (
    diff_invariance_anomaly_residual_a0,
    diff_invariance_anomaly_residual_a2,
    diff_invariance_anomaly_residual_a4,
    diff_invariance_holds_at_order,
    diff_invariance_holds_order_by_order,
)
from src.diff_invariance import (
    EffectiveLagrangianBundle,
    dirac_coefficient_bundle,
    perturbed_coefficient_bundle,
    pathB_residual_at_order,
    diff_invariant_at_order,
    diff_invariant_order_by_order,
    parameter_grid_scan_a4,
    max_residual_over_grid,
    anomaly_hunt_dirac_passes,
    anomaly_hunt_perturbed_fails,
)
from src.diff_invariance.anomaly_hunt import report_anomaly_hunt


TOL = float(DIFF_INVARIANCE_PARAMS['PATH_B_RESIDUAL_TOLERANCE'])


# ════════════════════════════════════════════════════════════════════
# Class 1: Wave 3 constants are well-formed
# ════════════════════════════════════════════════════════════════════

class TestDiffInvarianceConstants:
    def test_order_list_canonical(self):
        assert DIFF_INVARIANCE_PARAMS['ORDER_LIST'] == (0, 2, 4)

    def test_residual_tolerance_is_positive_machine_epsilon(self):
        tol = DIFF_INVARIANCE_PARAMS['PATH_B_RESIDUAL_TOLERANCE']
        assert 0 < tol < 1e-10  # at machine precision band

    def test_grid_ranges_well_ordered(self):
        for key in ('TEST_GRID_RICCI_SQ_RANGE',
                     'TEST_GRID_RIEMANN_SQ_RANGE'):
            low, high = DIFF_INVARIANCE_PARAMS[key]
            assert low <= high, f"{key} reversed"

    def test_admissible_basis_cardinality(self):
        # |{1, R, R², R_μν², R_μνρσ²}| = 5
        assert DIFF_INVARIANCE_PARAMS['ADMISSIBLE_BASIS_CARDINALITY'] == 5

    def test_anomaly_probe_offset_positive(self):
        assert DIFF_INVARIANCE_PARAMS['ANOMALY_PROBE_OFFSET'] > 0

    def test_parameter_scan_points_sufficient(self):
        # at least 8 points to detect orientation drift
        assert DIFF_INVARIANCE_PARAMS['PARAMETER_SCAN_POINTS'] >= 8


# ════════════════════════════════════════════════════════════════════
# Class 2: Order-0 + Order-2 residuals are definitionally zero
# ════════════════════════════════════════════════════════════════════

class TestOrderZeroAndTwoZero:
    @pytest.mark.parametrize("N_f", [1.0, 5.0, 24.0, 27.0, 100.0])
    def test_a0_residual_is_zero(self, N_f):
        # Lean: pathB_residual_a0_eq_zero (definitional)
        assert diff_invariance_anomaly_residual_a0(N_f) == 0.0

    @pytest.mark.parametrize("N_f, R", [
        (1.0, 0.0), (24.0, 10.0), (27.0, 1.0e3), (100.0, -5.0),
    ])
    def test_a2_residual_is_zero(self, N_f, R):
        # Lean: pathB_residual_a2_eq_zero (definitional)
        assert diff_invariance_anomaly_residual_a2(N_f, R) == 0.0

    @pytest.mark.parametrize("N_f", [1.0, 24.0, 27.0])
    def test_subpackage_a0_a2_zero(self, N_f):
        b = dirac_coefficient_bundle(N_f)
        # zero-args at orders 0/2 (R is exercised but residual is 0)
        assert pathB_residual_at_order(0, b, N_f, 0.0, 0.0, 0.0, 0.0) == 0.0
        assert pathB_residual_at_order(2, b, N_f, 5.0, 0.0, 0.0, 0.0) == 0.0


# ════════════════════════════════════════════════════════════════════
# Class 3: Order-4 residual vanishes for the Dirac bundle (Wave 2 ↔ Wave 3)
# ════════════════════════════════════════════════════════════════════

class TestOrderFourDiracZero:
    """Lean: pathB_residual_a4_dirac_eq_zero — load-bearing Wave 2↔3 cross-bridge."""

    @pytest.mark.parametrize("N_f, R_sq, Ricci_sq, Riemann_sq", [
        (1.0,   1.0,   0.0,    0.0),
        (24.0, 100.0, 50.0,   25.0),
        (27.0,   1.5,  3.7,    2.1),
        (100.0, 0.01, 0.001,   0.0001),
        (1.0,  1.0e6, 5.0e5,  2.5e5),  # large-curvature regime
    ])
    def test_dirac_a4_residual_at_machine_eps(
            self, N_f, R_sq, Ricci_sq, Riemann_sq):
        b = dirac_coefficient_bundle(N_f)
        residual = pathB_residual_at_order(
            4, b, N_f, 0.0, R_sq, Ricci_sq, Riemann_sq)
        # bound by max(input)·machine_eps with a small buffer
        scale = max(abs(R_sq), abs(Ricci_sq), abs(Riemann_sq), 1.0)
        assert abs(residual) < scale * 1e-12

    @pytest.mark.parametrize("N_f", [1.0, 5.0, 24.0, 27.0, 100.0])
    def test_dirac_at_unit_R_sq(self, N_f):
        b = dirac_coefficient_bundle(N_f)
        residual = pathB_residual_at_order(4, b, N_f, 0.0, 1.0, 0.0, 0.0)
        assert abs(residual) < TOL

    def test_formulas_a4_residual_at_machine_eps(self):
        # formulas.py wrapper agrees
        residual = diff_invariance_anomaly_residual_a4(
            24.0, 0.0, 100.0, 50.0, 25.0)
        assert abs(residual) < 1e-12


# ════════════════════════════════════════════════════════════════════
# Class 4: Order-4 residual is detectably nonzero for the perturbed bundle
# ════════════════════════════════════════════════════════════════════

class TestPerturbedFalsifier:
    """Lean: perturbed_pathB_residual_a4_at_unit_R_sq — falsifier."""

    @pytest.mark.parametrize("delta", [1e-6, 1e-3, 1.0, -2.5])
    def test_residual_equals_delta_at_unit_R_sq(self, delta):
        # Lean: perturbed_pathB_residual_a4_at_unit_R_sq states
        #   residual = delta exactly.
        b = perturbed_coefficient_bundle(24.0, delta)
        residual = pathB_residual_at_order(4, b, 24.0, 0.0, 1.0, 0.0, 0.0)
        assert math.isclose(residual, float(delta), rel_tol=1e-12,
                              abs_tol=1e-15)

    @pytest.mark.parametrize("delta", [1e-9, 1e-6, 1e-3])
    def test_perturbed_falsifier_detected(self, delta):
        b = perturbed_coefficient_bundle(24.0, delta)
        # at unit R_sq the residual is exactly delta — well above TOL for delta > 1e-12
        residual = abs(pathB_residual_at_order(
            4, b, 24.0, 0.0, 1.0, 0.0, 0.0))
        assert residual > TOL or delta < TOL

    def test_perturbed_with_zero_delta_is_dirac(self):
        # delta=0 ⇒ perturbed bundle == Dirac bundle ⇒ residual at machine eps
        b = perturbed_coefficient_bundle(24.0, 0.0)
        residual = pathB_residual_at_order(
            4, b, 24.0, 0.0, 100.0, 50.0, 25.0)
        assert abs(residual) < 1e-12


# ════════════════════════════════════════════════════════════════════
# Class 5: Order-by-order diff invariance witnesses
# ════════════════════════════════════════════════════════════════════

class TestDiffInvariantOrderByOrder:
    """Lean: dirac_diffInvariantAt_zero/two/four + dirac_H_NonlinearDiffInvariance."""

    @pytest.mark.parametrize("N_f", [1.0, 5.0, 24.0, 27.0])
    @pytest.mark.parametrize("order", [0, 2, 4])
    def test_dirac_diff_invariant_at_each_order(self, N_f, order):
        b = dirac_coefficient_bundle(N_f)
        assert diff_invariant_at_order(
            order, b, N_f, 1.0, 100.0, 50.0, 25.0)

    @pytest.mark.parametrize("N_f", [1.0, 5.0, 24.0, 27.0])
    def test_dirac_diff_invariant_order_by_order(self, N_f):
        b = dirac_coefficient_bundle(N_f)
        assert diff_invariant_order_by_order(
            b, N_f, 1.0, 100.0, 50.0, 25.0)

    def test_perturbed_NOT_diff_invariant_at_order_4(self):
        b = perturbed_coefficient_bundle(24.0, 1e-3)
        assert not diff_invariant_at_order(
            4, b, 24.0, 0.0, 1.0, 0.0, 0.0)

    def test_perturbed_NOT_diff_invariant_order_by_order(self):
        b = perturbed_coefficient_bundle(24.0, 1e-3)
        assert not diff_invariant_order_by_order(
            b, 24.0, 0.0, 1.0, 0.0, 0.0)

    def test_invalid_order_raises(self):
        b = dirac_coefficient_bundle(24.0)
        with pytest.raises(ValueError):
            pathB_residual_at_order(6, b, 24.0, 0.0, 1.0, 0.0, 0.0)
        with pytest.raises(ValueError):
            diff_invariance_holds_at_order(6, 24.0, 0.0, 1.0, 0.0, 0.0)


# ════════════════════════════════════════════════════════════════════
# Class 6: Anomaly-hunt parameter scan
# ════════════════════════════════════════════════════════════════════

class TestAnomalyHunt:
    """Wave 3 correctness-push at the parameter-grid level."""

    def test_dirac_grid_scan_residual_at_machine_eps(self):
        # All grid points should have |residual| at machine epsilon
        max_res = max_residual_over_grid(24.0, 'dirac')
        assert max_res < 1e-10  # generous margin over machine ε

    def test_perturbed_grid_scan_residual_above_tolerance(self):
        # Single nonzero δ should produce detectable residual
        max_res = max_residual_over_grid(
            24.0, 'perturbed',
            delta=DIFF_INVARIANCE_PARAMS['ANOMALY_PROBE_OFFSET'])
        assert max_res > TOL

    @pytest.mark.parametrize("N_f", [1.0, 24.0, 27.0])
    def test_anomaly_hunt_dirac_always_passes(self, N_f):
        # Lean: dirac_diffInvariantAt_four (load-bearing Wave 2 cross-bridge)
        assert anomaly_hunt_dirac_passes(N_f)

    @pytest.mark.parametrize("N_f", [1.0, 24.0, 27.0])
    def test_anomaly_hunt_perturbed_always_fails(self, N_f):
        # Lean: perturbed_not_diffInvariantAt_four
        assert anomaly_hunt_perturbed_fails(N_f)

    def test_grid_scan_has_canonical_size(self):
        n_pts = DIFF_INVARIANCE_PARAMS['PARAMETER_SCAN_POINTS']
        R_sq, Ricci_sq, Riem_sq, residual = parameter_grid_scan_a4(24.0)
        assert R_sq.shape == Ricci_sq.shape == Riem_sq.shape == \
            residual.shape == (n_pts,)

    def test_report_anomaly_hunt_decisions(self):
        rep = report_anomaly_hunt(24.0)
        assert rep['dirac_passes'] is True
        assert rep['perturbed_fails'] is True
        assert rep['dirac_max_residual'] < TOL
        assert rep['perturbed_max_residual'] > TOL


# ════════════════════════════════════════════════════════════════════
# Class 7: Cross-module consistency (Wave 1 + Wave 2 + Wave 3)
# ════════════════════════════════════════════════════════════════════

class TestCrossModuleConsistency:
    """Wave 3 reuses Wave 1 + Wave 2 by named call — drift-protection."""

    def test_dirac_bundle_a0_matches_wave1(self):
        from src.core.formulas import seeley_dewitt_a0
        b = dirac_coefficient_bundle(24.0)
        assert b.a0 == pytest.approx(float(seeley_dewitt_a0(24.0)),
                                       rel=1e-15)

    def test_dirac_bundle_a2_R_matches_wave1(self):
        from src.core.formulas import seeley_dewitt_a2_R_coefficient
        b = dirac_coefficient_bundle(24.0)
        assert b.a2_R == pytest.approx(
            float(seeley_dewitt_a2_R_coefficient(24.0)), rel=1e-15)

    def test_dirac_bundle_a4_R_sq_matches_wave2(self):
        from src.core.formulas import higher_curvature_R_sq_coefficient
        b = dirac_coefficient_bundle(24.0)
        assert b.a4_R_sq == pytest.approx(
            float(higher_curvature_R_sq_coefficient(24.0)), rel=1e-15)

    def test_dirac_bundle_a4_Ricci_sq_matches_wave2(self):
        from src.core.formulas import higher_curvature_Ricci_sq_coefficient
        b = dirac_coefficient_bundle(24.0)
        assert b.a4_Ricci_sq == pytest.approx(
            float(higher_curvature_Ricci_sq_coefficient(24.0)), rel=1e-15)

    def test_dirac_bundle_a4_Riemann_sq_matches_wave2(self):
        from src.core.formulas import higher_curvature_Riemann_sq_coefficient
        b = dirac_coefficient_bundle(24.0)
        assert b.a4_Riemann_sq == pytest.approx(
            float(higher_curvature_Riemann_sq_coefficient(24.0)), rel=1e-15)

    def test_density_a4_matches_wave2_a4_density(self):
        # Lean: diracCoefBundle_density_a4_eq_wave2_a4_density
        from src.higher_curvature.curvature_basis import a4_density
        b = dirac_coefficient_bundle(24.0)
        assert b.density_a4(100.0, 50.0, 25.0) == pytest.approx(
            a4_density(24.0, 100.0, 50.0, 25.0), rel=1e-15)


# ════════════════════════════════════════════════════════════════════
# Class 8: formulas.py wrappers behave as advertised
# ════════════════════════════════════════════════════════════════════

class TestFormulasWrappers:
    @pytest.mark.parametrize("order", [0, 2, 4])
    def test_formulas_diff_invariance_holds_at_order_dirac(self, order):
        # All orders pass for the Dirac bundle (formulas.py wrappers)
        assert diff_invariance_holds_at_order(
            order, 24.0, 1.0, 100.0, 50.0, 25.0)

    def test_formulas_diff_invariance_order_by_order_dirac(self):
        assert diff_invariance_holds_order_by_order(
            24.0, 1.0, 100.0, 50.0, 25.0)


# ════════════════════════════════════════════════════════════════════
# Class 9: Linearity of perturbed-bundle residual in delta (substantive
# — falsifier is non-tautological)
# ════════════════════════════════════════════════════════════════════

class TestLinearityOfFalsifierResidual:
    """Lean: perturbed_pathB_residual_a4_at_unit_R_sq states residual = δ.
    Numerically verify linearity over a range of δ."""

    def test_residual_is_linear_in_delta(self):
        deltas = np.array([1e-6, 1e-3, 0.5, 1.0, 5.0])
        residuals = np.array([
            pathB_residual_at_order(
                4, perturbed_coefficient_bundle(24.0, d),
                24.0, 0.0, 1.0, 0.0, 0.0)
            for d in deltas
        ])
        # residual(δ) = δ at unit R_sq
        np.testing.assert_allclose(residuals, deltas, rtol=1e-12,
                                     atol=1e-15)

    def test_residual_scales_with_R_sq_at_fixed_delta(self):
        # residual = δ · R_sq when only R_sq is nonzero (since perturbation
        # is the R²-channel coefficient)
        delta = 1e-3
        b = perturbed_coefficient_bundle(24.0, delta)
        for R_sq in [0.5, 1.0, 10.0, 100.0]:
            residual = pathB_residual_at_order(
                4, b, 24.0, 0.0, R_sq, 0.0, 0.0)
            assert math.isclose(residual, delta * R_sq, rel_tol=1e-12,
                                  abs_tol=1e-15)
