"""Unit tests for the RHMC early-stop verdict logic.

Each test constructs a synthetic npz-like coupling record that isolates one
branch of `assess_coupling`, guarding the calibration against regression
(a false alarm or a false GREEN is worse than no monitor).
"""
import numpy as np
import pytest

from src.vestigial.rhmc_diagnostics import (
    StopThresholds, assess_coupling, aggregate_status, integrated_autocorr_time,
)

L = 4
V = L ** 4          # 256
N = 500
THERM = 150
NMEAS = N - THERM   # 350


def _record(tet_mean, tet_std, *, hsq=1.0, dh_mean=0.0, acc=1.0,
            ar1=None, n=N, seed=1):
    """Build a synthetic coupling record. floor = 16*hsq/V.

    ar1=φ builds a stationary AR(1) tetrad history (variance tet_std²,
    integrated autocorr τ≈(1+φ)/2(1−φ)) for the critical-slowing branch;
    otherwise the history is iid (τ≈0.5)."""
    rng = np.random.default_rng(seed)
    if ar1 == "ramp":                  # monotonic ramp ⟹ τ near the estimator
        x = np.arange(n) / n - 0.5     # ceiling (N/6); critical-slowing regime
        tet = tet_mean + tet_std * x
    elif ar1 is not None:
        x = np.empty(n)
        x[0] = rng.standard_normal()
        noise = rng.standard_normal(n) * np.sqrt(1 - ar1 ** 2)
        for t in range(1, n):
            x[t] = ar1 * x[t - 1] + noise[t]
        tet = tet_mean + tet_std * x
    else:                              # iid ⟹ τ ≈ 0.5
        tet = tet_mean + tet_std * rng.standard_normal(n)
    return {
        "g": np.float64(2.0),
        "L": np.int64(L),
        "mass": np.float64(0.1),
        "h_sq_history": np.full(n, hsq),
        "tet_m2_history": tet,
        "tr_q2_history": np.abs(rng.standard_normal(n)) * 0.1,
        "delta_h_history": dh_mean + 0.01 * rng.standard_normal(n),
        "h_final": rng.standard_normal(V * 16),   # iid ⟹ no nematic order
        "acceptance_rate": np.float64(acc),
    }


THR = StopThresholds()
FLOOR = 16.0 * 1.0 / V    # 0.0625


def test_green_on_clear_tetrad_signal():
    # mean well above floor, tiny error ⟹ many σ
    v = assess_coupling(_record(FLOOR + 0.05, 0.01), THR, np.random.default_rng(0))
    assert v.status == "GREEN"
    assert v.tet_sig > THR.sig


def test_red_null_on_resolved_floor():
    # mean == floor, small error ⟹ resolved, no excess
    v = assess_coupling(_record(FLOOR, 0.01), THR, np.random.default_rng(0))
    assert v.status == "RED_NULL"


def test_yellow_on_positive_hint():
    # ~2.5σ positive excess (between null_sig and sig). Use a long iid chain so
    # τ≈0.5 reliably ⟹ N_eff≈N_meas and err≈std/√N_meas is predictable.
    n = 3000
    std = 0.05
    err = std / np.sqrt(n - THERM)        # τ≈0.5 ⟹ N_eff≈N_meas
    v = assess_coupling(_record(FLOOR + 2.5 * err, std, n=n), THR, np.random.default_rng(0))
    assert THR.null_sig < v.tet_sig < THR.sig
    assert v.status == "YELLOW"


def test_red_bias_on_creutz_drift():
    # ⟨e^-ΔH⟩ ≈ e^0.3 ≈ 1.35 ≫ 1  ⟹ biased force
    v = assess_coupling(_record(FLOOR, 0.01, dh_mean=-0.3), THR, np.random.default_rng(0))
    assert v.status == "RED_BIAS"
    assert v.creutz > 1.2


def test_red_bias_on_low_acceptance():
    v = assess_coupling(_record(FLOOR, 0.01, acc=0.3), THR, np.random.default_rng(0))
    assert v.status == "RED_BIAS"


def test_red_slow_on_critical_slowing():
    # monotonic ramp ⟹ τ≈59 > 0.15·350=52.5 (N_eff≈3) ⟹ method-limited.
    v = assess_coupling(_record(FLOOR, 0.02, ar1="ramp"), THR, np.random.default_rng(0))
    assert max(v.tau_tet, v.tau_met) > THR.slow_frac * v.n_meas
    assert v.status == "RED_SLOW"


def test_yellow_on_thin_stats():
    # AR(1) φ=0.99 ⟹ measured τ≈25, N_eff≈7 < 10 ⟹ thin stats (not RED_SLOW,
    # not a proven null) → more statistics productive.
    v = assess_coupling(_record(FLOOR, 0.05, ar1=0.99), THR, np.random.default_rng(0))
    assert v.neff < THR.neff_min
    assert v.status == "YELLOW"


def test_small_g_creutz_excess_is_not_flagged():
    # the exp estimator skews ~7% high at small g for HEALTHY chains; must NOT fire
    v = assess_coupling(_record(FLOOR, 0.01, dh_mean=-0.067), THR, np.random.default_rng(0))
    assert v.status != "RED_BIAS"
    assert 1.05 < v.creutz < 1.10


def test_aggregate_stop_null_when_all_null():
    rng = np.random.default_rng(0)
    vs = [assess_coupling(_record(FLOOR, 0.01, seed=s), THR, rng) for s in range(5)]
    assert all(v.status == "RED_NULL" for v in vs)
    agg, _ = aggregate_status(vs)
    assert agg == "STOP-NULL"


def test_aggregate_keep_going_when_any_green():
    rng = np.random.default_rng(0)
    vs = [assess_coupling(_record(FLOOR, 0.01, seed=1), THR, rng),
          assess_coupling(_record(FLOOR + 0.05, 0.01, seed=2), THR, rng)]
    agg, _ = aggregate_status(vs)
    assert agg == "KEEP-GOING"


def test_aggregate_stop_fix_dominates():
    rng = np.random.default_rng(0)
    vs = [assess_coupling(_record(FLOOR, 0.01, seed=1), THR, rng),
          assess_coupling(_record(FLOOR, 0.01, dh_mean=-0.3, seed=2), THR, rng)]
    agg, _ = aggregate_status(vs)
    assert agg == "STOP-FIX"


def test_iat_iid_is_small():
    assert integrated_autocorr_time(np.random.default_rng(0).standard_normal(2000)) < 1.5


def test_eff_threshold_controls_resolution():
    # at floor with err≈0.008 (std=0.15): err < 0.25·floor (=0.0156, resolved →
    # RED_NULL) but err > 0.05·floor (=0.0031, unresolved → YELLOW).
    rec = _record(FLOOR, 0.15)
    v_loose = assess_coupling(rec, StopThresholds(eff_threshold=0.25), np.random.default_rng(0))
    v_tight = assess_coupling(rec, StopThresholds(eff_threshold=0.05), np.random.default_rng(0))
    assert v_loose.status == "RED_NULL"
    assert v_tight.status == "YELLOW"


if __name__ == "__main__":
    raise SystemExit(pytest.main([__file__, "-v"]))
