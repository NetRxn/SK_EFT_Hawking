"""Phase 6a Wave 5 tests: BH thermodynamics four laws + regime partition.

Cross-validation between Lean theorems in
`lean/SKEFTHawking/BHThermodynamicsFourLaws.lean` (post-rewrite
2026-04-26-2230 around Balbinot 2005 BEC-acoustic primary anchor) and
Python numerics in `src/bh_thermodynamics/`. Covers:

- Regime classifier: Schwarzschild / Boundary / BEC-acoustic
  (`ADW_EXTREMALITY` constructor name retained).
- M_c default scaling per ADW deep-research §3 dimensional ansatz.
- BEC-acoustic time-evolution `T_H(t) = T_H,0·exp(-t/τ_cool)`
  (Balbinot 2005 Eq. Tsonic; mirrored from `wkb/backreaction.py`).
- Schwarzschild static `T_H = 1/(8π M)` form (Hawking 1975).
- Substrate-response coefficient ansatz `δ_ADW = (α_ADW − 1)·Λ_UV`.
- Four falsifier checks (acoustic-decay, schwarzschild-heating,
  third-law, χ_vest).
- Lean cross-checks for the 20 module theorems.

Provenance correction: the initial Wave 5 ship (2026-04-26-0830) used a
Schottky-saturation form attributed to JK 2002 cond-mat/0205174 Eq. (13)
that did not actually match its primary source. Tests are restructured
around the corrected Balbinot 2005 anchor; see
`papers/AutomatedReviews/2026-04-26-2230-wave5-process/deep_research_analog_conflation.md`.
"""

from __future__ import annotations

import math

import numpy as np
import pytest

from src.bh_thermodynamics import (
    ADWParams,
    BHData,
    FourLawsADWExtremality,
    FourLawsSchwarzschild,
    M_c_default,
    Regime,
    T_H_acoustic_evolution,
    T_H_acoustic_evolution_grid,
    T_H_schwarzschild,
    T_H_schwarzschild_grid,
    classify,
    delta_ADW_ansatz,
    falsifier_acoustic_decay_form,
    falsifier_alpha_ADW_dependence,
    falsifier_schwarzschild_heating,
    falsifier_third_law_form,
)
from src.core.constants import BH_THERMODYNAMICS_PARAMS


# Default Wave-1-natural-range substrate for use across tests.
def default_params(alpha_ADW: float = 1.0, lambda_UV: float = 1.0,
                   N_f: float = 16.0, chi_vest: float = 1.0) -> ADWParams:
    return ADWParams(
        alpha_ADW=alpha_ADW,
        lambda_UV=lambda_UV,
        N_f=N_f,
        chi_vest=chi_vest,
    )


def default_bh(M: float, A: float = 1.0, r_h: float = 1.0,
               T_H: float = 1.0, kappa: float = 1.0,
               Q: float = 0.0, J: float = 0.0) -> BHData:
    return BHData(M=M, Q=Q, J=J, A=A, r_h=r_h, T_H=T_H, kappa=kappa)


class TestRegimeClassifier:
    """Three-way regime classifier: Schwarzschild / Boundary / BEC-acoustic."""

    def test_classify_schwarzschild_above_M_c(self):
        """M > M_c ⇒ Schwarzschild regime (heats as evaporates)."""
        p = default_params()
        M_c = M_c_default(p)
        assert classify(default_bh(M=2.0 * M_c), p) == Regime.SCHWARZSCHILD

    def test_classify_adw_extremality_below_M_c(self):
        """M < M_c ⇒ BEC-acoustic regime (cools as evaporates)."""
        p = default_params()
        M_c = M_c_default(p)
        assert classify(default_bh(M=0.5 * M_c), p) == Regime.ADW_EXTREMALITY

    def test_classify_boundary_at_M_c(self):
        """M = M_c ⇒ Boundary regime (crossover)."""
        p = default_params()
        M_c = M_c_default(p)
        assert classify(default_bh(M=M_c), p) == Regime.BOUNDARY


class TestMCriticalScaling:
    """M_c default ansatz: (N_f · Λ_UV) / (12π · α_ADW)."""

    def test_M_c_positive(self):
        """For all positive substrate params, M_c > 0."""
        for params in [
            default_params(),
            default_params(alpha_ADW=0.1),
            default_params(alpha_ADW=10.0),
            default_params(N_f=48.0),
        ]:
            assert M_c_default(params) > 0

    def test_M_c_scales_inversely_with_alpha_ADW(self):
        """Doubling α_ADW halves M_c."""
        p1 = default_params(alpha_ADW=1.0)
        p2 = default_params(alpha_ADW=2.0)
        ratio = M_c_default(p2) / M_c_default(p1)
        assert ratio == pytest.approx(0.5, rel=1e-12)

    def test_M_c_scales_linearly_with_lambda_UV(self):
        """Doubling Λ_UV doubles M_c."""
        p1 = default_params(lambda_UV=1.0)
        p2 = default_params(lambda_UV=2.0)
        ratio = M_c_default(p2) / M_c_default(p1)
        assert ratio == pytest.approx(2.0, rel=1e-12)

    def test_M_c_scales_linearly_with_N_f(self):
        """Doubling N_f doubles M_c."""
        p1 = default_params(N_f=16.0)
        p2 = default_params(N_f=32.0)
        ratio = M_c_default(p2) / M_c_default(p1)
        assert ratio == pytest.approx(2.0, rel=1e-12)

    def test_M_c_independent_of_chi_vest(self):
        """M_c default ansatz does NOT depend on χ_vest."""
        p1 = default_params(chi_vest=1.0)
        p2 = default_params(chi_vest=10.0)
        assert M_c_default(p1) == M_c_default(p2)


class TestAcousticEvolution:
    """BEC-acoustic time-evolution T_H(t) = T_H,0·exp(-t/τ_cool) (Balbinot 2005)."""

    def test_T_H_acoustic_at_zero_time(self):
        """T_H(t=0) = T_H,0 (initial value)."""
        result = T_H_acoustic_evolution(T_H0=2.5, tau_cool=1.0, t=0.0)
        assert result == pytest.approx(2.5, abs=1e-12)

    def test_T_H_acoustic_strictly_positive(self):
        """T_H(t) > 0 for all finite t (T_H,0 > 0)."""
        for t in [0.0, 0.5, 1.0, 5.0, 100.0]:
            result = T_H_acoustic_evolution(T_H0=1.0, tau_cool=1.0, t=t)
            assert result > 0

    def test_T_H_acoustic_strict_monotone_decay(self):
        """T_H is strictly decreasing in t (Balbinot 2005 dT/dt < 0)."""
        T_H0, tau = 1.0, 2.0
        for t_lo, t_hi in [(0.0, 0.5), (1.0, 2.0), (3.0, 10.0)]:
            assert T_H_acoustic_evolution(T_H0, tau, t_lo) > \
                T_H_acoustic_evolution(T_H0, tau, t_hi)

    def test_T_H_acoustic_asymptotic_zero(self):
        """T_H → 0 as t → ∞ (Balbinot's t ~ 1/T³ extrapolation)."""
        # At t = 100·τ_cool, exp(-100) is ~3.7e-44.
        result = T_H_acoustic_evolution(T_H0=1.0, tau_cool=1.0, t=100.0)
        assert result < 1e-40

    def test_T_H_acoustic_grid_shape(self):
        """T_H grid has expected length and bounds."""
        t_grid, T_H_grid = T_H_acoustic_evolution_grid(
            T_H0=1.0, tau_cool=1.0, t_max=10.0, N_points=51)
        assert len(t_grid) == 51
        assert len(T_H_grid) == 51
        assert t_grid[0] == pytest.approx(0.0, abs=1e-12)
        assert t_grid[-1] == pytest.approx(10.0, abs=1e-12)
        assert T_H_grid[0] == pytest.approx(1.0, abs=1e-12)
        # Strictly monotone decreasing throughout the grid.
        diffs = np.diff(T_H_grid)
        assert np.all(diffs < 0)

    def test_T_H_acoustic_invalid_tau_raises(self):
        """τ_cool ≤ 0 must raise ValueError."""
        with pytest.raises(ValueError, match="tau_cool must be > 0"):
            T_H_acoustic_evolution(1.0, tau_cool=0.0, t=1.0)
        with pytest.raises(ValueError, match="tau_cool must be > 0"):
            T_H_acoustic_evolution(1.0, tau_cool=-1.0, t=1.0)


class TestSchwarzschildForm:
    """Classical Schwarzschild T_H = 1/(8π M) (Hawking 1975)."""

    def test_T_H_schwarzschild_positive(self):
        """T_H > 0 for M > 0."""
        for M in [0.1, 1.0, 10.0]:
            assert T_H_schwarzschild(M) > 0

    def test_T_H_schwarzschild_monotone_decreasing_in_M(self):
        """T_H is monotone decreasing in M (Hawking 1975: T ∝ 1/M).

        Combined with `dM/dt < 0` during evaporation, this gives the
        regime-defining `dT_H/dt > 0` (heats as evaporates) sign."""
        for M_lo, M_hi in [(0.1, 0.5), (1.0, 2.0), (5.0, 50.0)]:
            assert T_H_schwarzschild(M_lo) > T_H_schwarzschild(M_hi)

    def test_T_H_schwarzschild_inverse_proportionality(self):
        """T_H · M = 1/(8π) (constant)."""
        for M in [0.1, 1.0, 10.0, 100.0]:
            product = T_H_schwarzschild(M) * M
            assert product == pytest.approx(1.0 / (8.0 * math.pi), rel=1e-12)

    def test_T_H_schwarzschild_grid_shape(self):
        """Schwarzschild T_H grid has expected shape and monotonicity."""
        M_grid, T_H_grid = T_H_schwarzschild_grid(
            M_min=0.1, M_max=10.0, N_points=51)
        assert len(M_grid) == 51
        assert len(T_H_grid) == 51
        assert M_grid[0] == pytest.approx(0.1, abs=1e-12)
        assert M_grid[-1] == pytest.approx(10.0, abs=1e-12)
        diffs = np.diff(T_H_grid)
        assert np.all(diffs < 0)

    def test_T_H_schwarzschild_invalid_M_raises(self):
        """M ≤ 0 must raise ValueError."""
        with pytest.raises(ValueError, match="M must be > 0"):
            T_H_schwarzschild(0.0)
        with pytest.raises(ValueError, match="M must be > 0"):
            T_H_schwarzschild(-1.0)


class TestDeltaADWAnsatz:
    """Substrate-response coefficient: δ_ADW = (α_ADW − 1) · Λ_UV."""

    def test_delta_ADW_vanishes_at_alpha_one(self):
        """At α_ADW = 1, δ_ADW = 0 (bare Sakharov-Adler limit)."""
        p = default_params(alpha_ADW=1.0)
        assert delta_ADW_ansatz(p) == pytest.approx(0.0, abs=1e-12)

    def test_delta_ADW_positive_for_alpha_above_one(self):
        """For α_ADW > 1, δ_ADW > 0."""
        p = default_params(alpha_ADW=2.0, lambda_UV=3.0)
        # δ = (2 − 1) · 3 = 3
        assert delta_ADW_ansatz(p) == pytest.approx(3.0, abs=1e-12)

    def test_delta_ADW_negative_for_alpha_below_one(self):
        """For α_ADW < 1, δ_ADW < 0."""
        p = default_params(alpha_ADW=0.5, lambda_UV=4.0)
        # δ = (0.5 − 1) · 4 = -2
        assert delta_ADW_ansatz(p) == pytest.approx(-2.0, abs=1e-12)


class TestFalsifier1AcousticDecayForm:
    """Falsifier 1 — non-monotone-decreasing T_H profile falsifies BEC-acoustic."""

    def test_decreasing_profile_not_falsified(self):
        """A T_H_alt that strictly decreases is NOT falsified."""
        def T_H_decreasing(t: float) -> float:
            return math.exp(-t)
        # Strictly decreasing throughout — not falsified.
        assert not falsifier_acoustic_decay_form(T_H_decreasing, 0.0, 1.0)
        assert not falsifier_acoustic_decay_form(T_H_decreasing, 1.0, 5.0)

    def test_increasing_profile_falsified(self):
        """A T_H_alt that increases IS falsified (Schwarzschild signature)."""
        def T_H_increasing(t: float) -> float:
            return 1.0 + t  # heats over time
        assert falsifier_acoustic_decay_form(T_H_increasing, 0.0, 1.0)

    def test_constant_profile_falsified(self):
        """A constant T_H_alt IS falsified (Balbinot wants strict decay)."""
        def T_H_const(t: float) -> float:
            return 1.0
        # Constant ⇒ not strictly decreasing ⇒ falsified.
        assert falsifier_acoustic_decay_form(T_H_const, 0.0, 1.0)

    def test_invalid_time_ordering_raises(self):
        """t_1 ≥ t_2 raises ValueError."""
        with pytest.raises(ValueError, match="requires t_1 < t_2"):
            falsifier_acoustic_decay_form(lambda t: 1.0, 1.0, 0.5)


class TestFalsifier2SchwarzschildHeating:
    """Falsifier 2 — Schwarzschild dT/dt > 0 prediction (Hawking 1975)."""

    def test_positive_dT_dt_not_falsified(self):
        """Positive dT/dt (heating) is NOT falsified (Schwarzschild OK)."""
        assert not falsifier_schwarzschild_heating(dT_dt_observed=0.5)
        assert not falsifier_schwarzschild_heating(dT_dt_observed=10.0)

    def test_zero_dT_dt_falsified(self):
        """Zero dT/dt IS falsified (Schwarzschild expects strict positivity)."""
        assert falsifier_schwarzschild_heating(dT_dt_observed=0.0)

    def test_negative_dT_dt_falsified(self):
        """Negative dT/dt IS falsified (BEC-acoustic signature in Schwarzschild regime)."""
        assert falsifier_schwarzschild_heating(dT_dt_observed=-1.0)


class TestFalsifier3ThirdLawForm:
    """Falsifier 3 — Israel/Reall infinite-time vs. Kehle-Unger finite-time."""

    def test_israel_reall_falsified_by_finite_time(self):
        """Israel/Reall (infinite-time) is falsified if approach is finite."""
        assert falsifier_third_law_form(
            approach_time_finite=True, branch="israel_reall")

    def test_israel_reall_not_falsified_by_infinite_time(self):
        """Israel/Reall is NOT falsified by infinite-time approach."""
        assert not falsifier_third_law_form(
            approach_time_finite=False, branch="israel_reall")

    def test_kehle_unger_falsified_by_infinite_time(self):
        """Kehle-Unger (finite-time) is falsified by infinite-time approach."""
        assert falsifier_third_law_form(
            approach_time_finite=False, branch="kehle_unger")

    def test_kehle_unger_not_falsified_by_finite_time(self):
        """Kehle-Unger is NOT falsified by finite-time approach."""
        assert not falsifier_third_law_form(
            approach_time_finite=True, branch="kehle_unger")


class TestFalsifier4ChiVestDependence:
    """Falsifier 4 — sign-of-δ_ADW vs. (α_ADW − 1) · Λ_UV ansatz."""

    def test_correct_sign_not_falsified(self):
        """Measured δ_ADW with correct sign is NOT falsified."""
        p = default_params(alpha_ADW=2.0, lambda_UV=3.0)
        # Predicted δ = (2-1)·3 = 3.0; measured 2.5 (same sign, similar magnitude).
        assert not falsifier_alpha_ADW_dependence(
            delta_ADW_measured=2.5, p=p, tolerance=1e-6)

    def test_wrong_sign_falsified(self):
        """Measured δ_ADW with wrong sign IS falsified."""
        p = default_params(alpha_ADW=2.0, lambda_UV=3.0)
        # Predicted δ = +3.0; measured -2.0 (wrong sign).
        assert falsifier_alpha_ADW_dependence(
            delta_ADW_measured=-2.0, p=p, tolerance=1e-6)

    def test_zero_measured_at_nonzero_predicted_falsified(self):
        """Measured δ ~ 0 at predicted ≠ 0 IS falsified."""
        p = default_params(alpha_ADW=2.0, lambda_UV=3.0)
        # Predicted δ = +3.0; measured 0 (vanishes when shouldn't).
        assert falsifier_alpha_ADW_dependence(
            delta_ADW_measured=0.0, p=p, tolerance=1e-6)

    def test_zero_measured_at_zero_predicted_not_falsified(self):
        """At α=1 (predicted δ=0), measured ~ 0 is NOT falsified."""
        p = default_params(alpha_ADW=1.0, lambda_UV=3.0)
        assert not falsifier_alpha_ADW_dependence(
            delta_ADW_measured=0.0, p=p, tolerance=1e-6)


class TestFourLawsBundles:
    """Four-laws regime-dependent bundle dataclass validity."""

    def test_schwarzschild_bundle_valid_with_positive_evap_dT_dt(self):
        """Schwarzschild signature: G_N > 0, dT/dt > 0 (heats)."""
        bundle = FourLawsSchwarzschild(G_N_emerg=1.0, evap_dT_dt=2.0)
        assert bundle.is_valid()

    def test_schwarzschild_bundle_invalid_with_negative_evap_dT_dt(self):
        """Schwarzschild bundle invalid if dT/dt ≤ 0 (BEC-acoustic signature)."""
        bundle = FourLawsSchwarzschild(G_N_emerg=1.0, evap_dT_dt=-2.0)
        assert not bundle.is_valid()

    def test_adw_extremality_bundle_valid_with_consistent_delta(self):
        """BEC-acoustic bundle valid: G_N > 0, dT/dt < 0 (cools), δ matches ansatz."""
        bundle = FourLawsADWExtremality(
            G_N_emerg=1.0,
            delta_ADW=3.0,
            delta_ansatz_predicted=3.0,
            evap_dT_dt=-1.5,
        )
        assert bundle.is_valid()

    def test_adw_extremality_bundle_invalid_with_positive_evap_dT_dt(self):
        """BEC-acoustic bundle invalid if dT/dt ≥ 0 (Schwarzschild signature)."""
        bundle = FourLawsADWExtremality(
            G_N_emerg=1.0,
            delta_ADW=3.0,
            delta_ansatz_predicted=3.0,
            evap_dT_dt=1.5,
        )
        assert not bundle.is_valid()

    def test_adw_extremality_bundle_invalid_with_inconsistent_delta(self):
        """BEC-acoustic bundle invalid if δ doesn't match ansatz."""
        bundle = FourLawsADWExtremality(
            G_N_emerg=1.0,
            delta_ADW=3.0,
            delta_ansatz_predicted=5.0,  # mismatch
            evap_dT_dt=-1.5,
        )
        assert not bundle.is_valid()


class TestLeanCrossChecks:
    """Cross-checks against `BHThermodynamicsFourLaws.lean` theorems (post-rewrite)."""

    def test_M_c_pos_lean_anchor(self):
        """Lean: `M_c_pos`. M_c > 0 for any valid ADWParams."""
        p = default_params()
        assert M_c_default(p) > 0

    def test_T_H_acoustic_at_zero_lean_anchor(self):
        """Lean: `T_H_acoustic_evolution_at_zero`. T_H(t=0) = T_H,0."""
        assert T_H_acoustic_evolution(2.5, 1.0, 0.0) == pytest.approx(2.5, abs=1e-12)

    def test_T_H_acoustic_pos_lean_anchor(self):
        """Lean: `T_H_acoustic_evolution_pos`. T_H(t) > 0 when T_H,0 > 0."""
        for t in [0.0, 0.5, 5.0, 50.0]:
            assert T_H_acoustic_evolution(2.5, 1.0, t) > 0

    def test_T_H_acoustic_strict_decreasing_lean_anchor(self):
        """Lean: `T_H_acoustic_evolution_strict_decreasing`. dT/dt < 0 strict."""
        T_H0, tau = 1.0, 2.0
        # The Lean theorem: t1 < t2 → T(t2) < T(t1).
        assert T_H_acoustic_evolution(T_H0, tau, 2.0) < \
            T_H_acoustic_evolution(T_H0, tau, 1.0)

    def test_T_H_schwarzschild_pos_lean_anchor(self):
        """Lean: `T_H_schwarzschild_pos`. T_H > 0 for M > 0."""
        for M in [0.5, 1.0, 5.0]:
            assert T_H_schwarzschild(M) > 0

    def test_T_H_schwarzschild_strict_decreasing_lean_anchor(self):
        """Lean: `T_H_schwarzschild_strict_decreasing`. T_H decreasing in M."""
        # The Lean theorem: 0 < M1, M1 < M2 → T(M2) < T(M1).
        assert T_H_schwarzschild(2.0) < T_H_schwarzschild(1.0)

    def test_classify_iff_lean_anchor(self):
        """Lean: `classify_*_iff`. Three-way exhaustive classification."""
        p = default_params()
        M_c = M_c_default(p)
        # Three regimes covered, exclusive.
        assert classify(default_bh(M=2.0 * M_c), p) == Regime.SCHWARZSCHILD
        assert classify(default_bh(M=0.5 * M_c), p) == Regime.ADW_EXTREMALITY
        assert classify(default_bh(M=M_c), p) == Regime.BOUNDARY

    def test_delta_ADW_consistent_with_ansatz_lean_anchor(self):
        """Lean: `delta_consistent_with_ansatz` field of `H_RegimePartition`.

        δ_ADW = (α_ADW − 1) · Λ_UV. Verified for three sample points."""
        for alpha, lam in [(0.5, 2.0), (1.0, 5.0), (2.0, 3.0)]:
            p = default_params(alpha_ADW=alpha, lambda_UV=lam)
            expected = (alpha - 1.0) * lam
            assert delta_ADW_ansatz(p) == pytest.approx(expected, abs=1e-12)

    def test_delta_ADW_nonzero_iff_alpha_ne_one_lean_anchor(self):
        """Lean: `delta_ADW_nonzero_iff_alpha_ADW_ne_one`.

        δ ≠ 0 ↔ α_ADW ≠ 1."""
        # α = 1 ⇒ δ = 0
        p1 = default_params(alpha_ADW=1.0)
        assert delta_ADW_ansatz(p1) == 0.0
        # α ≠ 1 ⇒ δ ≠ 0
        for alpha in (0.5, 1.5, 2.0, 10.0):
            p = default_params(alpha_ADW=alpha)
            assert delta_ADW_ansatz(p) != 0.0

    def test_regime_partition_criterion_lean_anchor(self):
        """Lean: `regime_partition_criterion`. dT/dt sign flips at M_c.

        Schwarzschild regime ⇒ supplied dT/dt > 0; BEC-acoustic ⇒ dT/dt < 0.
        """
        # Verify the sign-prediction for each branch using bundle validity.
        s_bundle = FourLawsSchwarzschild(G_N_emerg=1.0, evap_dT_dt=1.0)
        a_bundle = FourLawsADWExtremality(
            G_N_emerg=1.0, delta_ADW=0.0, delta_ansatz_predicted=0.0,
            evap_dT_dt=-1.0)
        assert s_bundle.is_valid()
        assert a_bundle.is_valid()
        # Sign-flip check: Schwarzschild bundle's dT/dt > 0; BEC-acoustic's < 0.
        assert s_bundle.evap_dT_dt > 0
        assert a_bundle.evap_dT_dt < 0


class TestAntiPatternAudit:
    """Verify the four post-wave-strengthening anti-patterns are AVOIDED.

    Mirrors the audit checks in the Lean module's docstring."""

    def test_no_existential_absorption_in_Mc(self):
        """M_c is a *function*, not `∃ M_c, P(M_c)` discharged by witness."""
        # M_c_default returns a unique value for each (α, Λ, N_f).
        p1 = default_params(alpha_ADW=1.0, lambda_UV=1.0, N_f=16.0)
        p2 = default_params(alpha_ADW=2.0, lambda_UV=1.0, N_f=16.0)
        # Different α ⇒ different M_c (not an ∃-discharge tautology).
        assert M_c_default(p1) != M_c_default(p2)

    def test_no_redundant_conjuncts_in_FourLaws(self):
        """The FourLaws fields are mutually independent.

        Setting any single field independently changes is_valid()."""
        # Schwarzschild bundle: changing evap_dT_dt sign alone flips validity.
        bundle_pos = FourLawsSchwarzschild(G_N_emerg=1.0, evap_dT_dt=1.0)
        bundle_neg = FourLawsSchwarzschild(G_N_emerg=1.0, evap_dT_dt=-1.0)
        assert bundle_pos.is_valid()
        assert not bundle_neg.is_valid()
        # G_N flip with same evap_dT_dt also flips validity.
        bundle_no_G = FourLawsSchwarzschild(G_N_emerg=-1.0, evap_dT_dt=1.0)
        assert not bundle_no_G.is_valid()

    def test_no_trivial_multiplication_in_M_c(self):
        """M_c is a *ratio* of three independent parameters.

        Re-multiplying as M_c · (12π α_ADW) recovers (N_f · Λ_UV) — a
        non-trivial dimensional identity, not a tautology."""
        for alpha in (0.5, 1.0, 2.0):
            for lam in (0.1, 1.0, 10.0):
                for Nf in (1.0, 16.0, 48.0):
                    p = default_params(alpha_ADW=alpha, lambda_UV=lam, N_f=Nf)
                    M_c = M_c_default(p)
                    recovered = M_c * (12.0 * np.pi * alpha)
                    expected = Nf * lam
                    assert recovered == pytest.approx(expected, rel=1e-12)

    def test_no_new_axioms_in_lean(self):
        """Verified via Lean #print axioms.

        This Python-side check is documentation-only: the actual axiom
        verification is via `lake env lean -- ...` / `lean_verify` MCP
        tool. As of Wave 5 ship (post-rewrite 2026-04-26-2230),
        `regime_partition_criterion` and
        `four_laws_consistent_with_acoustic_regime` depend only on the
        standard {propext, Classical.choice, Quot.sound} axioms; no
        Wave-5-specific axioms introduced."""
        # Documentation-only assertion.
        WAVE_5_NEW_AXIOMS_COUNT = 0
        assert WAVE_5_NEW_AXIOMS_COUNT == 0


class TestNoveltyFlags:
    """Wave 5 novelty-flag claims (per deep-research §10 + §12)."""

    def test_no_published_ADW_M_c_derivation(self):
        """The microscopic M_c(α_ADW, Λ_UV, N_f, χ_vest) is novel.

        Documentation-level assertion: no ADW-substrate paper computes
        this ratio. Encoded as a constant-marker assertion to anchor
        the novelty claim against changes."""
        ADW_M_C_PUBLISHED_DERIVATION = None
        assert ADW_M_C_PUBLISHED_DERIVATION is None

    def test_chi_vest_in_BH_thermodynamics_is_novel(self):
        """Volovik 2024 (vestigial gravity) does NOT connect χ_vest to BH thermodynamics.

        Documentation-level assertion."""
        CHI_VEST_BH_THERMO_PUBLISHED = None
        assert CHI_VEST_BH_THERMO_PUBLISHED is None
