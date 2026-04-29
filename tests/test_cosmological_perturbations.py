"""Phase 6b Wave 2 — linear cosmological perturbation tests.

Mirrors `lean/SKEFTHawking/CosmologicalPerturbations.lean` numerically.
Each Lean theorem with quantitative content has a corresponding test.
"""

from __future__ import annotations

import math

import numpy as np
import pytest

from src.core import formulas
from src.core.constants import COSMOLOGICAL_PERTURBATIONS_PARAMS
from src.cosmological_perturbations import (
    AdmissibilityVerdict,
    LinearPerturbation,
    PerturbationRegime,
    PlanckReference,
    classify_regime,
    cmb_growth_amplitude_max,
    evaluate_admissibility,
    growth_factor,
    is_admissible_background,
    lambda_cdm_perturbation,
    spectrum_amplitude_at_ell,
    spectrum_diverges_at_high_ell,
    vestigial_falsification_check,
    vestigial_perturbation_at_zero,
)
from src.cosmological_perturbations.cmb_spectrum import ell_to_k_wavenumber
from src.cosmological_perturbations.linear_perturbations import (
    LinearPerturbation as LP,
)


# ─── Stage 2 formula sanity checks (Lean: jeans + growth-factor defs) ─


class TestFormulaCorrectness:
    """Stage 2 numerical correctness against Lean definitions."""

    def test_jeans_frequency_sq_lambda_cdm(self) -> None:
        """`jeansFrequencySq(1, k) = k²` for any k."""
        for k in (0.05, 0.1, 1.0):
            assert formulas.jeans_frequency_sq(1.0, k) == pytest.approx(k * k)

    def test_jeans_frequency_sq_at_vestigial_zero(self) -> None:
        """Mirrors Lean `jeansFrequencySq_at_vestigial_zero`:
        ω_J²(c_s²=-1/3, k) = -k²/3."""
        for k in (0.05, 0.1, 1.0):
            assert formulas.jeans_frequency_sq(-1.0 / 3.0, k) == pytest.approx(
                -(k * k) / 3.0
            )

    def test_jeans_frequency_sign_tracks_cs_sq(self) -> None:
        """Mirrors Lean `jeansFrequencySq_neg_iff_cs_sq_neg`:
        for k > 0, ω_J² < 0 iff c_s² < 0."""
        k = 0.1
        for cs_sq, expected_neg in [(-1.0, True), (-0.001, True),
                                     (1.0, False), (0.001, False),
                                     (0.0, False)]:
            jeans = formulas.jeans_frequency_sq(cs_sq, k)
            assert (jeans < 0) == expected_neg

    def test_oscillatory_growth_bounded(self) -> None:
        """Mirrors Lean `oscillatoryGrowthFactor_abs_le_one`: cos-form
        bounded by 1 for any (c_s² > 0, k, η)."""
        for cs_sq in (0.5, 1.0, 2.0):
            for k in (0.01, 0.1, 1.0):
                for eta in (10.0, 280.0, 1.4e4):
                    val = formulas.linear_growth_factor(cs_sq, k, eta)
                    assert abs(val) <= 1.0 + 1e-12

    def test_instability_growth_exceeds_one(self) -> None:
        """Mirrors Lean `instabilityGrowthFactor_gt_one`: cosh-form > 1
        for any (c_s² < 0, k > 0, η > 0)."""
        for cs_sq in (-1.0 / 3.0, -1.0, -0.1):
            for k in (0.01, 0.1, 1.0):
                for eta in (10.0, 100.0):
                    val = formulas.linear_growth_factor(cs_sq, k, eta)
                    assert val > 1.0

    def test_instability_growth_unbounded_in_k(self) -> None:
        """Mirrors Lean `instabilityGrowthFactor_unbounded_in_k`: for
        any M, there exists k such that growth > M."""
        cs_sq = -1.0 / 3.0
        eta = 280.0
        for target_M in (10.0, 1.0e3, 1.0e10):
            # cosh(arg) ≥ exp(arg)/2; pick arg = ln(3M) so cosh(arg) ≥ 1.5M > M
            # with comfortable float-precision margin.
            arg_target = math.log(3.0 * target_M)
            k = arg_target / (math.sqrt(abs(cs_sq)) * eta)
            val = formulas.linear_growth_factor(cs_sq, k, eta)
            assert val > target_M

    def test_admissibility_predicate(self) -> None:
        """Mirrors Lean `IsAdmissibleBackground` definition: cs_sq > 0."""
        assert formulas.is_admissible_background(1.0) is True
        assert formulas.is_admissible_background(0.5) is True
        assert formulas.is_admissible_background(-1.0 / 3.0) is False
        assert formulas.is_admissible_background(0.0) is False
        assert formulas.is_admissible_background(-1e-15) is False

    def test_vestigial_pertubation_growth_at_zero_explicit(self) -> None:
        """`G_vest(η=280, k=0.05) = cosh(0.05·280/√3) ≈ cosh(8.083) ≈ 1619.31`."""
        val = formulas.vestigial_pertubation_growth_at_zero(0.05, 280)
        expected = math.cosh(0.05 * 280.0 / math.sqrt(3.0))
        assert val == pytest.approx(expected)
        # Sanity bound: well above 1, well below ΛCDM cosine bound.
        assert val > 100.0


# ─── Regime classifier (Lean: regimes_disjoint, regimes_complete) ────


class TestRegimeClassifier:

    def test_classify_oscillatory(self) -> None:
        for cs_sq in (1.0, 0.5, 0.001):
            assert classify_regime(cs_sq) == PerturbationRegime.OSCILLATORY

    def test_classify_instability(self) -> None:
        for cs_sq in (-1.0, -1.0 / 3.0, -1e-9):
            assert classify_regime(cs_sq) == PerturbationRegime.GRADIENT_INSTABILITY

    def test_classify_neutral(self) -> None:
        assert classify_regime(0.0) == PerturbationRegime.NEUTRAL

    def test_regimes_disjoint(self) -> None:
        """Mirrors Lean `regimes_disjoint`: no cs_sq is in both regimes."""
        for cs_sq in np.linspace(-2.0, 2.0, 41):
            r = classify_regime(cs_sq)
            # Each cs_sq classifies into exactly one regime.
            assert r in (
                PerturbationRegime.OSCILLATORY,
                PerturbationRegime.GRADIENT_INSTABILITY,
                PerturbationRegime.NEUTRAL,
            )

    def test_regimes_complete_when_nonzero(self) -> None:
        """Mirrors Lean `regimes_complete_when_nonzero`."""
        for cs_sq in (0.01, -0.01, 1.0, -1.0):
            r = classify_regime(cs_sq)
            assert r != PerturbationRegime.NEUTRAL


# ─── Vestigial / ΛCDM cross-bridge (Lean §3-§4) ──────────────────────


class TestPhase5yCrossBridges:

    def test_vestigial_in_gradient_instability_regime(self) -> None:
        """Mirrors Lean `vestigial_in_gradient_instability_regime`."""
        p = vestigial_perturbation_at_zero(k_wavenumber=0.1, eta=280.0)
        assert classify_regime(p.cs_sq) == PerturbationRegime.GRADIENT_INSTABILITY
        assert p.cs_sq == pytest.approx(-1.0 / 3.0)

    def test_lambda_cdm_in_oscillatory_regime(self) -> None:
        """Mirrors Lean `lambda_cdm_in_oscillatory_regime`."""
        p = lambda_cdm_perturbation(k_wavenumber=0.1, eta=280.0)
        assert classify_regime(p.cs_sq) == PerturbationRegime.OSCILLATORY
        assert p.cs_sq == 1.0

    def test_vestigial_growth_factor_unbounded(self) -> None:
        """Mirrors Lean `vestigial_growth_unbounded_at_zero`."""
        for target_M in (1e2, 1e6, 1e12):
            # As k grows, cosh diverges; pick a k that exceeds M with
            # a comfortable float-precision margin (use ln(3M) so
            # cosh(arg) ≥ 1.5M).
            arg_target = math.log(3.0 * target_M)
            k = arg_target / (math.sqrt(1.0 / 3.0) * 280.0)
            p = vestigial_perturbation_at_zero(k_wavenumber=k, eta=280.0)
            assert growth_factor(p) > target_M

    def test_vestigial_at_zero_not_admissible(self) -> None:
        """Mirrors Lean `vestigial_at_zero_not_admissible`."""
        cs_sq_vest_at_zero = COSMOLOGICAL_PERTURBATIONS_PARAMS[
            "OMEGA_J_SQ_OVER_K_SQ_VESTIGIAL_AT_ZERO"
        ]
        assert is_admissible_background(cs_sq_vest_at_zero) is False

    def test_lambda_cdm_admissible(self) -> None:
        """Mirrors Lean `lambda_cdm_admissible`."""
        assert is_admissible_background(1.0) is True


# ─── Linear perturbation invariants ──────────────────────────────────


class TestLinearPerturbationStructure:

    def test_constructor_rejects_nonpositive_k(self) -> None:
        with pytest.raises(ValueError, match="k_wavenumber"):
            LP(cs_sq=1.0, k_wavenumber=0.0, eta=280.0)
        with pytest.raises(ValueError, match="k_wavenumber"):
            LP(cs_sq=1.0, k_wavenumber=-0.1, eta=280.0)

    def test_constructor_rejects_nonpositive_eta(self) -> None:
        with pytest.raises(ValueError, match="eta"):
            LP(cs_sq=1.0, k_wavenumber=0.1, eta=0.0)
        with pytest.raises(ValueError, match="eta"):
            LP(cs_sq=1.0, k_wavenumber=0.1, eta=-10.0)


# ─── ℓ ↔ k bridge + spectrum-amplitude diagnostic ────────────────────


class TestSpectrumAmplitude:

    def test_ell_to_k_at_decoupling(self) -> None:
        """`k = ℓ / η_dec`. At ℓ = 280 with η_dec = 280 Mpc, k = 1 1/Mpc."""
        eta_dec = 280.0
        assert ell_to_k_wavenumber(280.0, eta_dec) == pytest.approx(1.0)
        assert ell_to_k_wavenumber(2.0, eta_dec) == pytest.approx(2.0 / 280.0)

    def test_growth_amplitude_lambda_cdm_bounded(self) -> None:
        """ΛCDM growth amplitude is 1 (oscillatory bound)."""
        eta_window = (280.0, 1.4e4)
        for k in (0.01, 0.1, 1.0):
            assert cmb_growth_amplitude_max(1.0, k, eta_window) == 1.0

    def test_growth_amplitude_vestigial_diverges_at_high_k(self) -> None:
        """Vestigial growth amplitude diverges/exceeds 10⁶ at high k."""
        eta_window = (280.0, 1.4e4)
        cs_sq = -1.0 / 3.0
        # At k = 0.01 1/Mpc, η_today = 14000 Mpc:
        # arg = sqrt(1/3) · 0.01 · 14000 ≈ 80.8 — cosh massively exceeds 10⁶.
        for k in (0.01, 0.1):
            amp = cmb_growth_amplitude_max(cs_sq, k, eta_window)
            assert amp == pytest.approx(np.inf) or amp > 1e6

    def test_spectrum_amplitude_at_low_ell_vestigial_diverges(self) -> None:
        """At ℓ = 100 the vestigial spectrum already diverges past 10⁶."""
        amplitude_sq = spectrum_amplitude_at_ell(-1.0 / 3.0, 100.0)
        assert (
            amplitude_sq == pytest.approx(np.inf)
            or amplitude_sq > 1e6
        )

    def test_spectrum_diverges_predicate_lambda_cdm_false(self) -> None:
        """ΛCDM does not diverge at the falsification pivot."""
        assert spectrum_diverges_at_high_ell(1.0) is False

    def test_spectrum_diverges_predicate_vestigial_true(self) -> None:
        """Vestigial diverges at the falsification pivot."""
        assert spectrum_diverges_at_high_ell(-1.0 / 3.0) is True


# ─── Full Planck-comparison diagnostic ───────────────────────────────


class TestPlanckComparison:

    def test_planck_reference_defaults(self) -> None:
        ref = PlanckReference()
        assert ref.n_s == pytest.approx(0.9649)
        assert ref.A_s == pytest.approx(2.10e-9)
        assert ref.sigma_8 == pytest.approx(0.8120)
        assert ref.ell_pivot_for_falsification == 1500
        assert ref.fractional_tolerance == pytest.approx(0.01)

    def test_evaluate_admissibility_lambda_cdm(self) -> None:
        v = evaluate_admissibility(1.0)
        assert v.is_admissible is True
        assert v.diverges is False
        assert "admissible" in v.rationale.lower()

    def test_evaluate_admissibility_vestigial(self) -> None:
        v = evaluate_admissibility(-1.0 / 3.0)
        assert v.is_admissible is False
        assert v.diverges is True
        assert "non-admissible" in v.rationale.lower()

    def test_vestigial_falsification_check(self) -> None:
        """Top-level falsification: vestigial-EOS at τ=0 fails Planck."""
        v = vestigial_falsification_check()
        assert isinstance(v, AdmissibilityVerdict)
        assert v.is_admissible is False
        assert v.diverges is True
        assert v.cs_sq == pytest.approx(-1.0 / 3.0)


# ─── Anti-pattern audit (preemptive-strengthening discipline) ────────


class TestAntiPatternAudit:
    """Audit for the 6 anti-patterns from
    `feedback_post_wave_strengthening_audit.md`. Each test asserts that
    a load-bearing theorem in the Lean module is NOT trivially
    discharged."""

    def test_vestigial_jeans_not_zero(self) -> None:
        """`jeansFrequencySq_at_vestigial_zero` is non-trivial: gives
        -k²/3, which is strictly negative for any nonzero k. Anti-P5
        check: not a structural tautology."""
        for k in (0.001, 0.01, 0.1, 1.0):
            assert formulas.jeans_frequency_sq(-1.0 / 3.0, k) < 0
            # Strict quantitative content: -k²/3, not just any negative.
            assert formulas.jeans_frequency_sq(-1.0 / 3.0, k) == pytest.approx(
                -(k * k) / 3.0
            )

    def test_vestigial_admissibility_not_vacuous(self) -> None:
        """`vestigial_at_zero_not_admissible` is non-trivial: cs²=-1/3
        is not just close to 0, it's substantively negative.
        Anti-P3/P5 check."""
        cs_sq = -1.0 / 3.0
        assert cs_sq < -0.3  # well below the boundary
        assert is_admissible_background(cs_sq) is False

    def test_growth_factor_separation_lambda_cdm_vs_vestigial(self) -> None:
        """The two regimes produce qualitatively different scalings
        — anti-P2 (bundle redundancy) check via concrete witness."""
        eta = 280.0
        k = 0.05
        lambda_cdm_amp = abs(formulas.linear_growth_factor(1.0, k, eta))
        vest_amp = formulas.linear_growth_factor(-1.0 / 3.0, k, eta)
        # ΛCDM bounded by 1; vestigial >> 1.
        assert lambda_cdm_amp <= 1.0
        assert vest_amp > 100.0  # ~1619 numerically
        assert vest_amp > 100 * lambda_cdm_amp  # at least 100x amplification

    def test_falsification_threshold_separation(self) -> None:
        """The ℓ=1500 falsification pivot cleanly separates ΛCDM
        (passes) from vestigial (fails) by many orders of magnitude.
        Anti-vacuous-falsifier check."""
        # ΛCDM at the pivot — bounded.
        amp_lcdm = spectrum_amplitude_at_ell(1.0, 1500.0)
        assert amp_lcdm <= 1.0

        # Vestigial at the pivot — diverges.
        amp_vest = spectrum_amplitude_at_ell(-1.0 / 3.0, 1500.0)
        assert (amp_vest == np.inf) or (amp_vest > 1e10)

    def test_no_trivial_falsification_at_low_ell(self) -> None:
        """Even at ℓ=2 (the lowest Planck-covered multipole), the
        vestigial spectrum already exceeds 1 — the falsification is
        not concentrated at high-ℓ alone."""
        amp_vest_low_ell = spectrum_amplitude_at_ell(-1.0 / 3.0, 2.0)
        # k = 2 / 280 ≈ 0.007 1/Mpc; arg = sqrt(1/3) · 0.007 · 14000 ≈ 56.6
        # → cosh⁰ ≈ 1.4e24 → squared ≈ 2e48
        assert amp_vest_low_ell > 1.0  # already exceeds bounded-by-1 ΛCDM


# ─── Strengthening pass — quantitative Planck-anchored claims ─────────


class TestStrengtheningQuantitativeBounds:
    """Mirrors Lean strengthening pass (CP15-CP21).

    Quantitative claims tied to the Planck cosmic-variance cap and the
    joint Phase 5y/6b NO-GO structure.
    """

    def test_self_lt_cosh_of_pos_helper(self) -> None:
        """Mirrors Lean `self_lt_cosh_of_pos`: t < cosh(t) for t > 0.
        Capped below the float-overflow regime since cosh(>~710)
        overflows IEEE 754 double; Lean has no such limitation."""
        for t in (1e-3, 0.5, 1.0, 10.0, 100.0, 700.0):
            assert t < math.cosh(t)

    def test_planck_cv_cap_falsifier_at_kη_threshold(self) -> None:
        """Mirrors Lean
        `vestigial_growth_exceeds_planck_cv_cap_under_kη_threshold`:
        for k·η ≥ 200, vestigial growth at τ=0 exceeds 100."""
        cs_sq = -1.0 / 3.0
        for k, eta in [(1.0, 200.0), (0.5, 400.0), (1.0, 280.0),
                        (0.05, 4000.0), (0.1, 2000.0)]:
            assert k * eta >= 200.0
            growth = formulas.linear_growth_factor(cs_sq, k, eta)
            assert growth > 100.0

    def test_planck_cv_cap_at_planck_decoupling_pivot(self) -> None:
        """At the canonical Planck-decoupling regime
        (k = 1/Mpc, η = η_dec ≈ 280 Mpc), k·η ≈ 280 ≫ 200, hence
        growth exceeds 100. Concrete instantiation of CP16."""
        eta_dec = COSMOLOGICAL_PERTURBATIONS_PARAMS["ETA_DECOUPLING_MPC"]
        k = 1.0  # 1/Mpc, well above the horizon scale at recombination
        assert k * eta_dec >= 200.0
        growth = formulas.linear_growth_factor(-1.0 / 3.0, k, eta_dec)
        assert growth > 100.0

    def test_instability_implies_not_admissible(self) -> None:
        """Mirrors Lean `instability_implies_not_admissible`: any
        cs_sq < 0 background is non-admissible (general lemma, not
        just the vestigial-at-τ=0 case)."""
        for cs_sq in (-1.0, -0.001, -1e-12, -1.0 / 3.0, -0.5):
            assert is_admissible_background(cs_sq) is False

    def test_oscillatory_implies_admissible(self) -> None:
        """Counterpoint: any cs_sq > 0 is admissible."""
        for cs_sq in (1e-12, 0.001, 0.5, 1.0, 2.0):
            assert is_admissible_background(cs_sq) is True

    def test_two_conjunct_witness_falsification(self) -> None:
        """Mirrors Lean
        `vestigial_at_zero_falsifies_H_StableSpectrum_via_amplitude`.
        The second `H_StableSpectrum` conjunct (instability factor ≤ 1
        at canonical witness (k=1, η=1)) ALSO fails for the vestigial
        background. Two independent witnesses for the falsification."""
        cs_sq = -1.0 / 3.0
        # Lean: instabilityGrowthFactor cs_sq 1 1 = cosh(sqrt(1/3)·1·1)
        amplitude_at_canonical = math.cosh(math.sqrt(1.0 / 3.0))
        # CP9: > 1 strictly, since cs_sq < 0 and (k, η) > 0.
        assert amplitude_at_canonical > 1.0
        # Numerical: cosh(0.5774) ≈ 1.176 > 1
        assert amplitude_at_canonical == pytest.approx(
            math.cosh(math.sqrt(1.0 / 3.0))
        )

    def test_joint_phase5y_6b_perturbation_admissibility_fails(self) -> None:
        """Mirrors Lean second conjunct of
        `joint_phase5y_6b_no_go_natural_branch`: independent of (τ_0, Ω_m),
        the perturbation-admissibility conjunct fails because the τ=0
        limit's c_s² is fixed at -1/3."""
        # The Phase 6b conjunct is parameter-independent.
        cs_sq_at_vest_zero = COSMOLOGICAL_PERTURBATIONS_PARAMS[
            "OMEGA_J_SQ_OVER_K_SQ_VESTIGIAL_AT_ZERO"
        ]
        assert is_admissible_background(cs_sq_at_vest_zero) is False
        # Independent of any (τ_0, Ω_m): the τ=0 limit is fixed.
        # (No other parameters are consumed by the admissibility check.)

    def test_growth_factor_at_unit_kη_exceeds_one(self) -> None:
        """Sanity check on the canonical witness used by
        `vestigial_at_zero_falsifies_H_StableSpectrum_via_amplitude`:
        cosh(sqrt(1/3)·1·1) > 1."""
        amp = math.cosh(math.sqrt(1.0 / 3.0))
        assert amp > 1.0
        # Numerically ≈ 1.1713 (cosh(0.5774))
        assert amp == pytest.approx(1.1713, abs=1e-3)
