"""Phase 5z Wave 3 tests: EW phase transition on the scalar rung.

Tests for the finite-T effective potential, transition-order classifier,
and EW baryogenesis viability marker.
"""

from __future__ import annotations

import math

import numpy as np
import pytest

from src.core.formulas import (
    ew_finite_t_potential,
    ew_thermal_mass_sq,
    ew_critical_temperature,
    ew_latent_heat,
)
from src.ew_phase_transition import (
    finite_t_potential,
    thermal_mass_sq,
    critical_temperature,
    latent_heat,
    is_first_order_ew,
    is_crossover_ew,
    transition_order_grid,
    is_baryogenesis_viable,
    sphaleron_decoupling_threshold,
)


# Standard SM benchmark: mu^2 = (88 GeV)^2, lam = 0.13, c_T = 0.4, E = 0.01
SM_BENCHMARK = {
    "mu_sq": 88.0 ** 2,    # 7744 GeV^2
    "lam": 0.13,
    "c_T": 0.4,
    "E": 0.01,
}


class TestFiniteTPotential:
    """The high-T expansion V_T(phi, T)."""

    def test_potential_at_origin_is_zero(self):
        for T in [0.0, 50.0, 100.0, 150.0]:
            v = ew_finite_t_potential(0.0, T, **SM_BENCHMARK)
            assert v == pytest.approx(0.0, abs=1e-12)

    def test_zero_T_recovers_mexican_hat(self):
        # At T = 0: V = -(1/2) mu^2 phi^2 + (1/4) lam phi^4
        phi = 100.0
        v = ew_finite_t_potential(phi, 0.0, **SM_BENCHMARK)
        expected = -0.5 * SM_BENCHMARK["mu_sq"] * phi ** 2 + \
                    0.25 * SM_BENCHMARK["lam"] * phi ** 4
        assert v == pytest.approx(expected, rel=1e-12)

    def test_potential_finite_at_phi_T(self):
        v = ew_finite_t_potential(150.0, 200.0, **SM_BENCHMARK)
        assert math.isfinite(v)

    def test_thermal_mass_sq_zero_at_T_c(self):
        T_c = ew_critical_temperature(SM_BENCHMARK["mu_sq"], SM_BENCHMARK["c_T"])
        m_sq = ew_thermal_mass_sq(T_c, SM_BENCHMARK["mu_sq"], SM_BENCHMARK["c_T"])
        assert m_sq == pytest.approx(0.0, abs=1e-9)

    def test_thermal_mass_sq_negative_below_T_c(self):
        T_c = ew_critical_temperature(SM_BENCHMARK["mu_sq"], SM_BENCHMARK["c_T"])
        m_sq = ew_thermal_mass_sq(0.5 * T_c, SM_BENCHMARK["mu_sq"], SM_BENCHMARK["c_T"])
        assert m_sq < 0

    def test_thermal_mass_sq_positive_above_T_c(self):
        T_c = ew_critical_temperature(SM_BENCHMARK["mu_sq"], SM_BENCHMARK["c_T"])
        m_sq = ew_thermal_mass_sq(2.0 * T_c, SM_BENCHMARK["mu_sq"], SM_BENCHMARK["c_T"])
        assert m_sq > 0


class TestCriticalTemperature:
    """Critical temperature `T_c = sqrt(mu^2 / c_T)`."""

    def test_positive(self):
        T_c = ew_critical_temperature(SM_BENCHMARK["mu_sq"], SM_BENCHMARK["c_T"])
        assert T_c > 0

    def test_value_at_sm_benchmark(self):
        T_c = ew_critical_temperature(SM_BENCHMARK["mu_sq"], SM_BENCHMARK["c_T"])
        # T_c = 88 / sqrt(0.4) ≈ 139.13 GeV (consistent with SM EWPT lit)
        assert T_c == pytest.approx(139.13, abs=0.5)

    def test_rejects_nonpositive(self):
        with pytest.raises(ValueError):
            ew_critical_temperature(0.0, 0.4)
        with pytest.raises(ValueError):
            ew_critical_temperature(7744.0, -0.1)

    def test_scales_with_sqrt_mu(self):
        # T_c ~ sqrt(mu^2) → if mu_sq doubles, T_c grows by sqrt(2)
        T_c1 = ew_critical_temperature(7744.0, 0.4)
        T_c2 = ew_critical_temperature(2 * 7744.0, 0.4)
        assert T_c2 / T_c1 == pytest.approx(math.sqrt(2.0), rel=1e-12)


class TestLatentHeat:
    """Latent heat: L = E^2 T_c^2 / (2 lam)."""

    def test_zero_for_crossover(self):
        L = ew_latent_heat(0.0, SM_BENCHMARK["mu_sq"], SM_BENCHMARK["lam"],
                           SM_BENCHMARK["c_T"])
        assert L == pytest.approx(0.0, abs=1e-12)

    def test_positive_for_first_order(self):
        L = ew_latent_heat(SM_BENCHMARK["E"], SM_BENCHMARK["mu_sq"],
                           SM_BENCHMARK["lam"], SM_BENCHMARK["c_T"])
        assert L > 0

    def test_quadratic_in_E(self):
        # L ~ E^2: doubling E should quadruple L
        L1 = ew_latent_heat(0.01, SM_BENCHMARK["mu_sq"], SM_BENCHMARK["lam"],
                            SM_BENCHMARK["c_T"])
        L2 = ew_latent_heat(0.02, SM_BENCHMARK["mu_sq"], SM_BENCHMARK["lam"],
                            SM_BENCHMARK["c_T"])
        assert L2 / L1 == pytest.approx(4.0, rel=1e-12)

    def test_rejects_nonpositive(self):
        with pytest.raises(ValueError):
            ew_latent_heat(0.01, 0.0, 0.13, 0.4)


class TestTransitionOrderClassifier:
    """First-order vs crossover predicates."""

    def test_first_order_at_positive_E(self):
        assert is_first_order_ew(0.01) is True
        assert is_first_order_ew(0.5) is True
        assert is_first_order_ew(1e-10) is True

    def test_crossover_at_zero_E(self):
        assert is_crossover_ew(0.0) is True

    def test_disjoint(self):
        for E in [0.01, 0.1, 1.0]:
            assert not (is_first_order_ew(E) and is_crossover_ew(E))

    def test_grid_classifier(self):
        E_range = np.array([0.0, 0.005, 0.01, 0.05, 0.1])
        result = transition_order_grid(E_range)
        # Only E > 0 are first-order
        assert result.tolist() == [False, True, True, True, True]

    def test_grid_with_threshold(self):
        E_range = np.array([0.001, 0.01, 0.1])
        result = transition_order_grid(E_range, threshold=0.05)
        # Only E > 0.05 returns True
        assert result.tolist() == [False, False, True]


class TestBaryogenesisViability:
    """Baryogenesis viability marker (sphaleron decoupling)."""

    def test_threshold_value(self):
        assert sphaleron_decoupling_threshold() == 1.0

    def test_crossover_excludes_baryogenesis(self):
        # E = 0 → not viable
        assert is_baryogenesis_viable(0.0, **{k: v for k, v in SM_BENCHMARK.items()
                                              if k != "E"}) is False

    def test_negative_E_excluded(self):
        # Defensively reject negative E (not physical at LO)
        assert is_baryogenesis_viable(-0.01, **{k: v for k, v in SM_BENCHMARK.items()
                                                if k != "E"}) is False

    def test_sm_benchmark_E_001_below_threshold(self):
        # SM-like E = 0.01 is well below the lambda * T_c ~ 0.13 * 139 ~ 18 threshold
        viable = is_baryogenesis_viable(0.01, **{k: v for k, v in SM_BENCHMARK.items()
                                                  if k != "E"})
        assert viable is False  # canonical SM crossover

    def test_strong_first_order_viable(self):
        # E sufficiently large → above threshold
        # threshold is 1 * lam * T_c = 1 * 0.13 * 139.13 ≈ 18.09
        # so need E > 18.09
        viable = is_baryogenesis_viable(20.0, **{k: v for k, v in SM_BENCHMARK.items()
                                                  if k != "E"})
        assert viable is True

    def test_baryogenesis_threshold_override(self):
        # Lower threshold → more permissive
        viable = is_baryogenesis_viable(0.5, **{k: v for k, v in SM_BENCHMARK.items()
                                                 if k != "E"}, threshold=0.01)
        # threshold 0.01 * 0.13 * 139 ~ 0.18, E = 0.5 > 0.18
        assert viable is True


class TestLeanCrossReferences:
    """Cross-validate Lean theorems against numerics."""

    def test_lean_thm_critical_temperature_pos(self):
        # Lean: criticalTemperature_pos
        T_c = ew_critical_temperature(SM_BENCHMARK["mu_sq"], SM_BENCHMARK["c_T"])
        assert T_c > 0

    def test_lean_thm_thermalMassSq_at_T_c(self):
        # Lean: thermalMassSq_at_T_c
        T_c = ew_critical_temperature(SM_BENCHMARK["mu_sq"], SM_BENCHMARK["c_T"])
        m_sq = ew_thermal_mass_sq(T_c, SM_BENCHMARK["mu_sq"], SM_BENCHMARK["c_T"])
        assert abs(m_sq) < 1e-9

    def test_lean_thm_thermalMassSq_neg_below_T_c(self):
        # Lean: thermalMassSq_neg_below_T_c
        T_c = ew_critical_temperature(SM_BENCHMARK["mu_sq"], SM_BENCHMARK["c_T"])
        for ratio in [0.1, 0.5, 0.99]:
            m_sq = ew_thermal_mass_sq(ratio * T_c, SM_BENCHMARK["mu_sq"],
                                       SM_BENCHMARK["c_T"])
            assert m_sq < 0

    def test_lean_thm_first_order_and_crossover_disjoint(self):
        # Lean: first_order_and_crossover_disjoint
        for E in [0.0, 1e-10, 0.001, 1.0]:
            assert not (is_first_order_ew(E) and is_crossover_ew(E))

    def test_lean_thm_crossover_has_zero_latent_heat(self):
        # Lean: crossover_has_zero_latent_heat
        L = ew_latent_heat(0.0, SM_BENCHMARK["mu_sq"], SM_BENCHMARK["lam"],
                           SM_BENCHMARK["c_T"])
        assert L == 0.0

    def test_lean_thm_first_order_has_positive_latent_heat(self):
        # Lean: first_order_has_positive_latent_heat
        for E in [0.001, 0.01, 0.1, 1.0]:
            L = ew_latent_heat(E, SM_BENCHMARK["mu_sq"], SM_BENCHMARK["lam"],
                               SM_BENCHMARK["c_T"])
            assert L > 0

    def test_lean_thm_crossover_excludes_baryogenesis(self):
        # Lean: crossover_excludes_baryogenesis
        # E = 0 + any threshold → not viable
        assert is_baryogenesis_viable(0.0, **{k: v for k, v in SM_BENCHMARK.items()
                                              if k != "E"}, threshold=0.01) is False
        assert is_baryogenesis_viable(0.0, **{k: v for k, v in SM_BENCHMARK.items()
                                              if k != "E"}, threshold=10.0) is False


class TestModuleWrappers:
    """Sanity checks for the src/ew_phase_transition/ wrappers."""

    def test_potential_wrapper_matches_canonical(self):
        v_canonical = ew_finite_t_potential(100.0, 100.0, **SM_BENCHMARK)
        v_wrapper = finite_t_potential(100.0, 100.0, **SM_BENCHMARK)
        assert v_canonical == pytest.approx(v_wrapper, rel=1e-12)

    def test_thermal_mass_wrapper_matches_canonical(self):
        m_canonical = ew_thermal_mass_sq(100.0, SM_BENCHMARK["mu_sq"],
                                          SM_BENCHMARK["c_T"])
        m_wrapper = thermal_mass_sq(100.0, SM_BENCHMARK["mu_sq"], SM_BENCHMARK["c_T"])
        assert m_canonical == m_wrapper

    def test_critical_temp_wrapper_matches_canonical(self):
        T_canonical = ew_critical_temperature(SM_BENCHMARK["mu_sq"], SM_BENCHMARK["c_T"])
        T_wrapper = critical_temperature(SM_BENCHMARK["mu_sq"], SM_BENCHMARK["c_T"])
        assert T_canonical == T_wrapper

    def test_latent_heat_wrapper_matches_canonical(self):
        L_canonical = ew_latent_heat(SM_BENCHMARK["E"], SM_BENCHMARK["mu_sq"],
                                      SM_BENCHMARK["lam"], SM_BENCHMARK["c_T"])
        L_wrapper = latent_heat(SM_BENCHMARK["E"], SM_BENCHMARK["mu_sq"],
                                 SM_BENCHMARK["lam"], SM_BENCHMARK["c_T"])
        assert L_canonical == L_wrapper
