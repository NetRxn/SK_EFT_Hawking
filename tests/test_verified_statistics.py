"""
Tests for verified statistical estimators (formulas.py) and RHMC analysis.

Corresponds to VerifiedJackknife.lean and VerifiedStatistics.lean.
"""

import numpy as np
import pytest
from src.core.formulas import (
    jackknife_variance,
    autocovariance,
    integrated_autocorrelation_time,
    effective_sample_size,
    bootstrap_confidence_interval,
)


# ── Jackknife variance ──────────────────────────────────────────────

class TestJackknifeVariance:
    def test_constant_data(self):
        """Jackknife variance of constant data is 0."""
        data = np.ones(20)
        est, var = jackknife_variance(data)
        assert est == pytest.approx(1.0)
        assert var == pytest.approx(0.0, abs=1e-15)

    def test_nonnegative(self):
        """Jackknife variance is non-negative (Lean: jackknifeVariance_nonneg)."""
        rng = np.random.default_rng(42)
        for _ in range(10):
            data = rng.normal(0, 1, size=50)
            _, var = jackknife_variance(data)
            assert var >= 0

    def test_mean_case(self):
        """For f=mean, JK variance = s^2/n (Lean: jackknife_mean_case)."""
        rng = np.random.default_rng(123)
        data = rng.normal(5.0, 2.0, size=100)
        _, jk_var = jackknife_variance(data, observable=np.mean)
        s2 = np.var(data, ddof=1)
        expected = s2 / len(data)
        assert jk_var == pytest.approx(expected, rel=1e-10)

    def test_custom_observable(self):
        """Jackknife works with a custom observable."""
        data = np.array([1.0, 2.0, 3.0, 4.0, 5.0])
        est, var = jackknife_variance(data, observable=np.var)
        assert est == pytest.approx(np.var(data))
        assert var >= 0

    def test_minimum_samples(self):
        """Needs at least 2 samples."""
        with pytest.raises(ValueError):
            jackknife_variance(np.array([1.0]))


# ── Autocovariance ──────────────────────────────────────────────────

class TestAutocovariance:
    def test_lag_zero_nonneg(self):
        """C(0) >= 0 (Lean: autocovariance_zero_nonneg)."""
        rng = np.random.default_rng(42)
        data = rng.normal(0, 1, size=100)
        C = autocovariance(data)
        assert C[0] >= 0

    def test_constant_data(self):
        """C(t) = 0 for constant data."""
        data = np.ones(50)
        C = autocovariance(data, max_lag=10)
        assert all(abs(c) < 1e-15 for c in C)

    def test_cauchy_schwarz(self):
        """C(t)^2 <= C(0)^2 (Lean: autocovariance_bounded)."""
        rng = np.random.default_rng(42)
        data = rng.normal(0, 1, size=200)
        C = autocovariance(data, max_lag=50)
        for t in range(1, len(C)):
            assert C[t] ** 2 <= C[0] ** 2 + 1e-10

    def test_shape(self):
        """Returns max_lag + 1 values."""
        data = np.random.default_rng(42).normal(size=100)
        C = autocovariance(data, max_lag=20)
        assert len(C) == 21


# ── Integrated autocorrelation time ─────────────────────────────────

class TestIntegratedAutocorrelationTime:
    def test_uncorrelated(self):
        """tau_int = 0.5 for uncorrelated data (Lean: intAutocorrTime_uncorrelated)."""
        rng = np.random.default_rng(42)
        data = rng.normal(0, 1, size=10000)
        tau, W = integrated_autocorrelation_time(data)
        assert tau == pytest.approx(0.5, abs=0.1)

    def test_ge_half(self):
        """tau_int >= 0.5 (Lean: intAutocorrTime_ge_half)."""
        rng = np.random.default_rng(42)
        for _ in range(10):
            data = rng.normal(0, 1, size=200)
            tau, _ = integrated_autocorrelation_time(data)
            assert tau >= 0.5 - 1e-10

    def test_correlated_data(self):
        """Correlated data has tau_int > 0.5."""
        rng = np.random.default_rng(42)
        # Create correlated data via AR(1)
        n = 5000
        data = np.empty(n)
        data[0] = rng.normal()
        rho = 0.9
        for i in range(1, n):
            data[i] = rho * data[i - 1] + np.sqrt(1 - rho**2) * rng.normal()
        tau, _ = integrated_autocorrelation_time(data)
        assert tau > 2.0  # Should be ~(1+rho)/(1-rho)/2 = 9.5


# ── Effective sample size ───────────────────────────────────────────

class TestEffectiveSampleSize:
    def test_le_n(self):
        """N_eff <= N (Lean: effectiveSampleSize_le_n)."""
        rng = np.random.default_rng(42)
        data = rng.normal(0, 1, size=500)
        n_eff, _, _ = effective_sample_size(data)
        assert n_eff <= len(data) + 1e-10

    def test_uncorrelated_near_n(self):
        """For uncorrelated data, N_eff ~ N."""
        rng = np.random.default_rng(42)
        data = rng.normal(0, 1, size=5000)
        n_eff, tau, _ = effective_sample_size(data)
        assert n_eff > len(data) * 0.7  # Should be close to N

    def test_correlated_much_less(self):
        """For correlated data, N_eff << N."""
        rng = np.random.default_rng(42)
        n = 5000
        data = np.empty(n)
        data[0] = rng.normal()
        for i in range(1, n):
            data[i] = 0.95 * data[i - 1] + np.sqrt(1 - 0.95**2) * rng.normal()
        n_eff, _, _ = effective_sample_size(data)
        assert n_eff < n * 0.2  # Much less than N


# ── Bootstrap CI ────────────────────────────────────────────────────

class TestBootstrapCI:
    def test_contains_true_mean(self):
        """95% CI should contain the sample mean."""
        rng = np.random.default_rng(42)
        data = rng.normal(5.0, 1.0, size=100)
        est, ci_low, ci_high = bootstrap_confidence_interval(data)
        assert ci_low <= est <= ci_high

    def test_ci_width_scales(self):
        """CI should narrow with more data."""
        rng = np.random.default_rng(42)
        data_small = rng.normal(0, 1, size=20)
        data_large = rng.normal(0, 1, size=2000)
        _, lo_s, hi_s = bootstrap_confidence_interval(data_small)
        _, lo_l, hi_l = bootstrap_confidence_interval(data_large)
        width_small = hi_s - lo_s
        width_large = hi_l - lo_l
        assert width_large < width_small

    def test_custom_observable(self):
        """Bootstrap works with custom observables."""
        data = np.random.default_rng(42).normal(0, 1, size=100)
        est, lo, hi = bootstrap_confidence_interval(data, observable=np.std)
        assert lo <= est <= hi
        assert lo > 0  # std should be positive
