"""Tests for the D11 / D12 bundle formula layer (`src/core/formulas.py`).

Stage-13 raised a BLOCKER on both bundles: all 40 D11/D12 functions had zero
test coverage. `validate.py --check formula_grounding` reported green because it
resolves Lean *names*, not *values* — so nothing checked that the Python mirrors
what the kernel proved.

Two numbers made the cost concrete. `papers/D12/paper_draft.tex` asserts a
crossover at ``N_a = 51.40`` and that the Mills ratio exceeds 1 for
``z <~ 0.37``. Neither appears in the Lean, and neither appeared in any test —
they were computed once, written into prose, and never guarded. Both are pinned
below.

Every assertion here compares against a value the Lean substrate certifies (the
theorem is named in the docstring or comment), or against a closed form that a
certified identity implies. A failure means the Python layer has drifted from
the kernel and is a bug in `formulas.py`, not a discovery.
"""

import math

import numpy as np
import pytest

from src.core import formulas as F


# ══════════════════════════════════════════════════════════════════════════
# D11 — topological band theory & metamaterials
# ══════════════════════════════════════════════════════════════════════════


class TestPhononicBandGap:
    """Lean: phononic_band_gap_exists, branchMinus_at_pi, branchPlus_at_pi,
    acoustic_le_one, optical_ge_two, band_gap_falsifier."""

    def test_gap_edges_attained_at_pi(self):
        # branchMinus_at_pi = 1 and branchPlus_at_pi = 2, EXACTLY.
        lo, hi = F.diatomic_branches(1.0, 2.0, 1.0, math.pi)
        assert lo == pytest.approx(1.0, abs=1e-12)
        assert hi == pytest.approx(2.0, abs=1e-12)

    def test_certified_gap_edges(self):
        assert F.phononic_gap_edges() == (1.0, 2.0)

    def test_global_branch_bounds(self):
        # acoustic_le_one / optical_ge_two, over the whole Brillouin zone.
        ks = np.linspace(-math.pi, math.pi, 4001)
        br = np.array([F.diatomic_branches(1.0, 2.0, 1.0, k) for k in ks])
        assert br[:, 0].max() <= 1.0 + 1e-12
        assert br[:, 1].min() >= 2.0 - 1e-12

    def test_falsifier_no_state_strictly_inside_gap(self):
        # band_gap_falsifier: any omega strictly inside (1,2) yields False.
        lo, hi = F.phononic_gap_edges()
        ks = np.linspace(-math.pi, math.pi, 4001)
        for k in ks:
            a, b = F.diatomic_branches(1.0, 2.0, 1.0, k)
            assert not (lo + 1e-12 < a < hi - 1e-12)
            assert not (lo + 1e-12 < b < hi - 1e-12)

    def test_rational_enclosure_is_an_inner_bracket(self):
        # band_gap_rational_enclosure: 1 < 141/100 <= sqrt(2).
        enc_lo, enc_hi = F.phononic_gap_rational_enclosure()
        assert enc_lo == 1.0
        assert enc_hi == pytest.approx(1.41, abs=1e-12)
        assert enc_hi <= math.sqrt(2.0)

    def test_branches_at_zero(self):
        lo, hi = F.diatomic_branches(1.0, 2.0, 1.0, 0.0)
        assert lo == pytest.approx(0.0, abs=1e-12)
        assert hi == pytest.approx(3.0, abs=1e-12)


class TestPTExceptionalPoint:
    """Lean: pt_symmetric_real_spectrum_iff, ep_splitting_at_ep,
    ep_proximity_enclosure."""

    def test_splitting_vanishes_at_the_exceptional_point(self):
        assert F.pt_eigenvalue_splitting(1.0) == 0.0

    def test_proximity_enclosure_is_tight(self):
        # 99/100 <= g^2 <= 1  =>  Delta <= 1/5, with EQUALITY at the endpoint.
        at_endpoint = F.pt_eigenvalue_splitting(math.sqrt(0.99))
        assert at_endpoint == pytest.approx(0.2, abs=1e-12)
        worst = max(F.pt_eigenvalue_splitting(math.sqrt(x))
                    for x in np.linspace(0.99, 1.0, 500))
        assert worst <= 0.2 + 1e-12

    def test_splitting_closed_form(self):
        for g in (0.0, 0.25, 0.5, 0.9):
            assert F.pt_eigenvalue_splitting(g) == pytest.approx(
                2.0 * math.sqrt(1.0 - g ** 2), abs=1e-12)


class TestEffectiveMedium:
    """Lean: effectiveMedium_hashinShtrikman_enclosure,
    effectiveMedium_constituent_bounds, voigt_sub_reuss_eq,
    maxwellGarnett_host_recovery."""

    def test_certified_point(self):
        assert F.maxwell_garnett(1.0, 4.0, 0.5) == pytest.approx(2.0, abs=1e-12)

    def test_host_recovery_at_zero_fill(self):
        assert F.maxwell_garnett(1.0, 4.0, 0.0) == pytest.approx(1.0, abs=1e-12)

    def test_constituent_bounds_non_strict(self):
        # Bounds are NON-strict and attained at f = 0 and f = 1.
        for f in np.linspace(0.0, 1.0, 501):
            eps = F.maxwell_garnett(1.0, 4.0, float(f))
            assert 1.0 - 1e-12 <= eps <= 4.0 + 1e-12
        assert F.maxwell_garnett(1.0, 4.0, 1.0) == pytest.approx(4.0, abs=1e-9)

    def test_voigt_reuss_gap_is_an_exact_identity(self):
        # voigt_sub_reuss_eq is an EQUALITY, not merely >= 0.
        for f in np.linspace(0.0, 1.0, 501):
            f = float(f)
            lhs = F.voigt_modulus(1.0, 4.0, f) - F.reuss_modulus(1.0, 4.0, f)
            assert lhs == pytest.approx(F.voigt_reuss_gap(1.0, 4.0, f), abs=1e-12)

    def test_voigt_reuss_ordering(self):
        for f in np.linspace(0.0, 1.0, 201):
            f = float(f)
            assert F.reuss_modulus(1.0, 4.0, f) <= F.voigt_modulus(1.0, 4.0, f) + 1e-12

    def test_gap_at_two_thirds_is_exactly_one(self):
        # Follows from the certified identity; the figure marks this point.
        assert F.voigt_reuss_gap(1.0, 4.0, 2.0 / 3.0) == pytest.approx(1.0, abs=1e-12)


class TestGrapheneAndHaldane:
    """Lean: haldaneFrame_latticeChern_eq_neg_one, haldane_window_bounds,
    haldane_mass_inversion_iff, structureFactor, linearForm_norm,
    fermiVelocity, bernal_fullGapSq_eq."""

    def test_inversion_window_is_three_root_three(self):
        w = F.haldane_mass_inversion_window(1.0, math.pi / 2)
        assert w == pytest.approx(3.0 * math.sqrt(3.0), abs=1e-12)
        assert w == pytest.approx(5.196152422706632, abs=1e-12)

    def test_dirac_masses_are_opposite_at_the_two_cones(self):
        # This opposition IS the Haldane mechanism.
        mk, mkp = F.haldane_dirac_masses(0.0, 1.0, math.pi / 2)
        assert mk == pytest.approx(-mkp, abs=1e-12)

    def test_m5_is_inside_the_window_yet_certifies_C_zero(self):
        # haldane_massInversion_not_sufficient_at_N4: mass inversion is NOT
        # sufficient at fixed grid size. m=5 sits inside the analytic window.
        w = F.haldane_mass_inversion_window(1.0, math.pi / 2)
        assert abs(5.0) < w
        mk, mkp = F.haldane_dirac_masses(5.0, 1.0, math.pi / 2)
        assert mk * mkp < 0     # masses genuinely inverted ...
        # ... yet the certified 4x4 invariant at m=5 is 0 (Lean), so the
        # analytic window alone cannot predict the lattice invariant.

    def test_m6_is_outside_the_window(self):
        w = F.haldane_mass_inversion_window(1.0, math.pi / 2)
        assert abs(6.0) > w
        mk, mkp = F.haldane_dirac_masses(6.0, 1.0, math.pi / 2)
        assert mk * mkp > 0     # same sign — not inverted

    def test_haldane_nnn_at_dirac_points(self):
        # haldaneNNN_diracK = 3*sqrt(3)/2, haldaneNNN_diracK' = -3*sqrt(3)/2.
        expect = 3.0 * math.sqrt(3.0) / 2.0
        assert F.haldane_nnn(2 * math.pi / 3, 4 * math.pi / 3) == pytest.approx(
            expect, abs=1e-12)
        assert F.haldane_nnn(4 * math.pi / 3, 2 * math.pi / 3) == pytest.approx(
            -expect, abs=1e-12)

    def test_structure_factor_vanishes_at_dirac_points(self):
        # structureFactor_eq_zero_iff / honeycomb_gapless_at_diracK.
        for th in ((2 * math.pi / 3, 4 * math.pi / 3),
                   (4 * math.pi / 3, 2 * math.pi / 3)):
            assert abs(F.honeycomb_structure_factor(*th)) == pytest.approx(0.0, abs=1e-12)

    def test_structure_factor_witnesses(self):
        # structureFactor_gamma = 3, structureFactor_mPoint = 1.
        assert abs(F.honeycomb_structure_factor(0.0, 0.0)) == pytest.approx(3.0, abs=1e-12)
        assert abs(F.honeycomb_structure_factor(math.pi, 0.0)) == pytest.approx(1.0, abs=1e-12)

    def test_dirac_linear_form_norm(self):
        assert F.dirac_linear_form_norm(1.0, 0.0) == pytest.approx(1.0, abs=1e-12)
        assert F.dirac_linear_form_norm(1.0, 1.0) == pytest.approx(1.0, abs=1e-12)

    def test_fermi_velocity_closed_form(self):
        assert F.fermi_velocity(1.0, 1.0, 1.0) == pytest.approx(1.5, abs=1e-12)

    def test_bernal_full_gap_matches_mccann_form(self):
        # bernal_fullGapSq_eq: U^2 gamma^2 / (gamma^2 + U^2) with U = 2u.
        u, g = 0.5, 1.0
        U = 2.0 * u
        assert F.bernal_full_gap_sq(u, g) == pytest.approx(
            U ** 2 * g ** 2 / (g ** 2 + U ** 2), abs=1e-12)


# ══════════════════════════════════════════════════════════════════════════
# D12 — detector & readout metrology
# ══════════════════════════════════════════════════════════════════════════


class TestPoissonDiscriminationFloors:
    """Lean: poisson_avgError_floor, poissonBhattacharyya_eq,
    poisson_darkBaseline_miss_optimum, folkloreGap_split."""

    def test_bhattacharyya_closed_form(self):
        for na, nb in ((0.0, 1.0), (5.0, 10.0), (50.0, 60.0)):
            assert F.poisson_bhattacharyya_coefficient(na, nb) == pytest.approx(
                math.exp(-((math.sqrt(na) - math.sqrt(nb)) ** 2) / 2.0), abs=1e-14)

    def test_le_cam_floor_is_quarter_bc_squared(self):
        for na, nb in ((5.0, 10.0), (50.0, 60.0)):
            bc = F.poisson_bhattacharyya_coefficient(na, nb)
            assert F.poisson_avg_error_floor(na, nb) == pytest.approx(
                0.25 * bc ** 2, abs=1e-14)

    def test_coincident_rates_give_quarter(self):
        # The Le Cam CONSTANT gives 1/4 at coincident rates; Lean's
        # poisson_avgError_equalRates_eq_half proves the true value is 1/2,
        # which is exactly the factor-2 slack the paper reports.
        assert F.poisson_avg_error_floor(7.0, 7.0) == pytest.approx(0.25, abs=1e-14)

    def test_dark_baseline_optimum(self):
        assert F.poisson_dark_baseline_miss_optimum(10.0) == pytest.approx(
            math.exp(-10.0), abs=1e-14)

    def test_folklore_gap_split_identity(self):
        # folkloreGap_split: (Na-Nb) - (sqrt Na - sqrt Nb)^2 = 2 sqrt Nb (sqrt Na - sqrt Nb)
        for nb in (1.0, 5.0, 50.0):
            for na in np.linspace(nb, nb + 40.0, 200):
                na = float(na)
                lhs = (na - nb) - (math.sqrt(na) - math.sqrt(nb)) ** 2
                assert lhs == pytest.approx(F.folklore_gap_exponent(na, nb), abs=1e-9)


class TestFolkloreRefutation:
    """The bundle's headline: the folklore floor fails in TWO distinct
    directions. Lean: folklore_miss_floor_false,
    folklore_missFloor_beaten_148fold, folklore_avgFloor_unsound_of_bright,
    folklore_avgFloor_unsound_factor1000, brightGap_5060."""

    def test_direction_A_false_strict_as_a_miss_bound(self):
        # The realizable unit-threshold counter beats the folklore value by
        # exactly exp(N_b), for EVERY bright baseline.
        for nb in (1.0, 5.0, 20.0):
            for na in (nb + 1.0, nb + 5.0, nb + 20.0):
                realizable = F.poisson_dark_baseline_miss_optimum(na)
                folklore = F.folklore_miss_floor(na, nb)
                assert realizable < folklore
                assert folklore / realizable == pytest.approx(math.exp(nb), rel=1e-12)

    def test_direction_A_certified_148_fold(self):
        # folklore_missFloor_beaten_148fold at (N_b, N_a) = (5, 10).
        ratio = F.folklore_miss_floor(10.0, 5.0) / F.poisson_dark_baseline_miss_optimum(10.0)
        assert ratio >= 148.0
        assert ratio == pytest.approx(math.exp(5.0), rel=1e-12)   # 148.413...

    def test_direction_B_fail_open_certified_witness(self):
        # folklore_avgFloor_unsound_factor1000 at (50, 60): the TRUE floor
        # strictly EXCEEDS the folklore value by more than 1000x.
        true_floor = F.poisson_avg_error_floor(60.0, 50.0)
        folklore = F.folklore_miss_floor(60.0, 50.0)
        assert true_floor > folklore
        assert true_floor / folklore > 1000.0

    def test_direction_B_bright_gap_5060(self):
        # brightGap_5060: 9.54 < 2 sqrt(50) (sqrt 60 - sqrt 50).
        gap = F.folklore_gap_exponent(60.0, 50.0)
        assert gap > 9.54
        assert gap == pytest.approx(9.544511501, abs=1e-6)

    def test_direction_B_threshold_is_log_four(self):
        # folklore_avgFloor_unsound_of_bright fires exactly when the gap
        # exponent exceeds log 4.
        nb = 50.0
        for na in (51.0, 52.0, 60.0, 70.0):
            gap = F.folklore_gap_exponent(na, nb)
            fails_open = F.poisson_avg_error_floor(na, nb) > F.folklore_miss_floor(na, nb)
            assert fails_open == (gap > math.log(4.0))

    def test_paper_asserted_crossover_value(self):
        """`papers/D12/paper_draft.tex` asserts the crossover at N_a = 51.40.

        This number is in NEITHER the Lean NOR (before this test) any test —
        Stage-13 BLOCKER 2.1. It is the N_a at which the gap exponent reaches
        log 4, i.e. where the folklore form crosses from conservative to
        fail-open. Pinned here so the prose cannot drift from the arithmetic.
        """
        nb = 50.0
        crossover = ((math.log(4.0) / (2.0 * math.sqrt(nb))) + math.sqrt(nb)) ** 2
        assert crossover == pytest.approx(51.3959, abs=1e-3)
        assert round(crossover, 2) == 51.40      # the value printed in the paper
        assert F.folklore_gap_exponent(crossover, nb) == pytest.approx(
            math.log(4.0), abs=1e-9)


class TestGaussianThresholdFloors:
    """Lean: gaussianQ, gaussianTail_chernoff, gaussianTail_mills,
    gaussianTail_birnbaum, avgError_ge_gaussianQ_sharp,
    gaussianQ_two_le_rational, gaussianQ_two_ge_rational."""

    def test_gaussian_q_known_values(self):
        assert F.gaussian_q(0.0) == pytest.approx(0.5, abs=1e-12)
        assert F.gaussian_q(2.0) == pytest.approx(0.02275013, abs=1e-7)

    def test_rational_brackets_hold(self):
        q2 = F.gaussian_q(2.0)
        assert q2 <= 1.0 / 37.0      # gaussianQ_two_le_rational
        assert q2 >= 1.0 / 125.0     # gaussianQ_two_ge_rational

    def test_two_sided_tail_sandwich(self):
        for z in np.linspace(0.05, 3.5, 400):
            z = float(z)
            q = F.gaussian_q(z)
            assert F.gaussian_tail_birnbaum_lower(z) <= q + 1e-15
            assert q <= F.gaussian_tail_chernoff_upper(z) + 1e-15
            assert q <= F.gaussian_tail_mills_upper(z) + 1e-15

    def test_chernoff_is_a_factor_two_sharpening(self):
        # The paper's central novelty carve-out: ours is (1/2)exp(-z^2/2),
        # Mathlib's sub-Gaussian bound is exp(-z^2/2) at c = 1.
        for z in (0.5, 1.0, 2.0, 3.0):
            mathlib_form = math.exp(-(z ** 2) / 2.0)
            assert F.gaussian_tail_chernoff_upper(z) == pytest.approx(
                0.5 * mathlib_form, abs=1e-14)

    def test_paper_asserted_mills_vacuity_root(self):
        """`papers/D12/paper_draft.tex` asserts the Mills ratio exceeds 1 for
        z <~ 0.37. Like the crossover, this number is in neither the Lean nor
        (before this test) any test — Stage-13 BLOCKER 2.1.
        """
        root = 0.3722389
        assert F.gaussian_tail_mills_upper(root) == pytest.approx(1.0, abs=1e-5)
        assert F.gaussian_tail_mills_upper(0.30) > 1.0      # vacuous below
        assert F.gaussian_tail_mills_upper(0.45) < 1.0      # informative above
        assert root == pytest.approx(0.37, abs=0.005)       # the printed value

    def test_threshold_floor_is_midpoint_q(self):
        # avgError_ge_gaussianQ_sharp, attained at the midpoint.
        assert F.gaussian_threshold_error_floor(0.0, 4.0, 1.0) == pytest.approx(
            F.gaussian_q(2.0), abs=1e-14)


class TestFilteredReadoutFloors:
    """Lean: enbw_mul_window_ge_half, enbw_mul_window_isLeast, enbw_boxcar,
    enbw_ramp_gt_half, matchedBudget, snrChain_le_window_ceiling,
    nep_quadrature_two."""

    def test_boxcar_saturates_the_floor_at_every_window(self):
        for T in (0.25, 1.0, 2.0, 10.0):
            assert F.enbw_boxcar(T) * T == pytest.approx(0.5, abs=1e-14)

    def test_ramp_is_strictly_above_the_floor(self):
        for T in (0.25, 1.0, 2.0, 10.0):
            assert F.enbw_ramp(T) * T == pytest.approx(2.0 / 3.0, abs=1e-14)
            assert F.enbw_ramp(T) * T > F.enbw_window_product_floor()

    def test_floor_constant(self):
        assert F.enbw_window_product_floor() == 0.5

    def test_matched_budget_closed_form(self):
        assert F.matched_budget(2.0, 4.0) == pytest.approx(2.0, abs=1e-12)

    def test_snr_ceiling_closed_form(self):
        assert F.snr_chain_window_ceiling(3.0, 2.0, 1.5) == pytest.approx(
            3.0 * math.sqrt(4.0) / 1.5, abs=1e-12)

    def test_quadrature_composition(self):
        assert F.nep_quadrature(3.0, 4.0) == pytest.approx(5.0, abs=1e-12)


class TestElectrothermal:
    """Lean: loopGain, loopGain_eq_irwinHilton, etf_stable_iff,
    effectiveTimeConstant_eq_div, johnsonNEP_eq_abs_one_sub_loopGain_mul_naive,
    absLoopGain_criterion_unsound, phononPSD, johnsonCurrentPSD."""

    def test_loop_gain_closed_form(self):
        assert F.etf_loop_gain(2.0, -0.5, 1.0, 1.0) == pytest.approx(-2.0, abs=1e-12)

    def test_stability_dichotomy_boundary(self):
        assert F.etf_is_stable(-0.999) is True
        assert F.etf_is_stable(-1.0) is False
        assert F.etf_is_stable(-1.001) is False

    def test_abs_loop_gain_does_not_determine_stability(self):
        # absLoopGain_criterion_unsound: |L| = 2 on both sides of the boundary.
        assert F.etf_is_stable(2.0) is True
        assert F.etf_is_stable(-2.0) is False

    def test_tau_eff_is_negative_on_the_unstable_branch(self):
        # Reading it through |.| inverts the physics.
        assert F.etf_effective_time_constant(1.0, 1.0, -2.0) < 0.0
        assert F.etf_effective_time_constant(1.0, 1.0, 3.0) == pytest.approx(0.25, abs=1e-12)

    def test_effective_conductance(self):
        assert F.etf_effective_conductance(2.0, 3.0) == pytest.approx(8.0, abs=1e-12)

    def test_johnson_factor_is_two_at_loop_gain_three(self):
        # THE load-bearing one: |1 - L|, NOT |1 + L|. A post-review physics
        # BLOCKER once already (speedupWitness_johnsonNEP_double).
        assert F.johnson_nep_correction_factor(3.0) == pytest.approx(2.0, abs=1e-12)
        assert F.johnson_nep_correction_factor(3.0) != 4.0

    def test_johnson_factor_is_stability_blind(self):
        # johnsonNEP_correction_magnitude_loses_stability_information.
        assert F.johnson_nep_correction_factor(5.0) == pytest.approx(4.0, abs=1e-12)
        assert F.johnson_nep_correction_factor(-3.0) == pytest.approx(4.0, abs=1e-12)
        assert F.etf_is_stable(5.0) is True
        assert F.etf_is_stable(-3.0) is False

    def test_naive_overstates_between_zero_and_two(self):
        # johnsonNEPNaive_lt_johnsonNEP_iff boundary: |1-L| < 1 iff 0 < L < 2.
        for L in (0.5, 1.0, 1.5):
            assert F.johnson_nep_correction_factor(L) < 1.0
        for L in (-0.5, 2.5):
            assert F.johnson_nep_correction_factor(L) > 1.0

    def test_noise_psd_closed_forms(self):
        assert F.phonon_psd(1.0, 2.0, 3.0) == pytest.approx(48.0, abs=1e-12)
        assert F.johnson_current_psd(1.0, 2.0, 4.0) == pytest.approx(2.0, abs=1e-12)


class TestPhononGradientFactor:
    """The thermal-link gradient factor gamma (F_link).

    Lean: phononPSDGamma, phononPSD_eq_phononPSDGamma_one,
          phononPSDGamma_lt_phononPSD, phononPSDGamma_le_phononPSD,
          gammaOne_phononFloor_overstates.
    Provenance: Mather (1982), Appl. Opt. 21, 1125.

    These pin the DIRECTION of the correction. Until 2026-07-31 the tree carried
    two theorems hypothesizing gamma > 1 and concluded the shipped gamma = 1 form
    was an optimistic bound; gamma is bounded ABOVE by 1, so it overstates. A
    regression that reintroduces gamma > 1 fails here.
    """

    def test_isothermal_limit_is_exactly_one(self):
        # Lean: phononPSD_eq_phononPSDGamma_one.
        assert F.phonon_psd_gradient_factor(1.0, 4.0) == 1.0

    def test_isothermal_limit_is_continuous(self):
        # Approaching r = 1 from above must approach 1, not jump to it.
        assert F.phonon_psd_gradient_factor(1.0001, 4.0) == pytest.approx(1.0, abs=1e-3)

    def test_paper_asserted_gradient_factor_at_r2_n4(self):
        # The value quoted in the provenance note and the Lean docstring.
        assert F.phonon_psd_gradient_factor(2.0, 4.0) == pytest.approx(0.4731, abs=5e-4)

    def test_gamma_never_exceeds_one(self):
        # The whole point: gamma can only REDUCE the phonon noise.
        for r in (1.0, 1.01, 1.1, 1.5, 2.0, 3.0, 5.0):
            for n in (3.0, 4.0, 5.0):
                assert 0.0 < F.phonon_psd_gradient_factor(r, n) <= 1.0

    def test_gamma_asymptote_is_n_over_2n_plus_1_not_one_half(self):
        # CORRECTED 2026-07-31 (D12 Stage-13 rounds 3-4). This test formerly asserted
        # "TES literature quotes F_link in [1/2, 1]" while silently loosening its own
        # bound to 0.47 to keep passing -- i.e. it encoded a claim its own assertion
        # already contradicted. The true asymptote is n/(2n+1), and gamma drops BELOW
        # 1/2 at ordinary loading, so [1/2, 1] does not bound this expression.
        for n in (3.0, 4.0, 5.0, 10.0):
            asymptote = n / (2 * n + 1)
            assert F.phonon_psd_gradient_factor(1e6, n) == pytest.approx(asymptote, rel=1e-6)
            # approached from above, and never violated
            for r in (1.01, 1.5, 2.0, 5.0, 100.0):
                assert asymptote <= F.phonon_psd_gradient_factor(r, n) <= 1.0
        # the specific value the paper and the Lean docstrings quote
        assert F.phonon_psd_gradient_factor(2.0, 4.0) == pytest.approx(0.4731, abs=5e-4)
        assert F.phonon_psd_gradient_factor(2.0, 4.0) < 0.5  # below the folk [1/2,1] band

    def test_psd_and_amplitude_readings_of_gamma(self):
        # gamma multiplies the POWER spectral density, so 1-gamma is a PSD reduction
        # and 1-sqrt(gamma) an amplitude one. At the paper's operating point the two
        # readings are 53% and 31%, which is why Mather's unit-free "as much as 30%"
        # cannot be compared without fixing a convention.
        #
        # RENAMED AND REWRITTEN 2026-07-31 (D12 Stage-13 round-6 BLOCKER 2.1). The old
        # name asserted the conclusion -- "test_mather_30_percent_is_an_amplitude_figure"
        # -- and the old comment carried the proposition round 5 blocked: "No PSD
        # reduction available from the closed form is near 30%". That is FALSE, and the
        # counterexample is pinned below. A round-5 commit message claimed this file was
        # fixed; it was never touched.
        g = F.phonon_psd_gradient_factor(2.0, 4.0)
        assert 1.0 - g == pytest.approx(0.527, abs=5e-3)              # PSD reading
        assert 1.0 - math.sqrt(g) == pytest.approx(0.312, abs=5e-3)   # amplitude reading

    def test_a_thirty_percent_psd_reduction_IS_attainable(self):
        # The counterexample that refutes the round-4/5 claim, pinned so it cannot be
        # re-asserted: gamma is continuous and strictly decreasing from 1 toward
        # n/(2n+1), so EVERY PSD reduction in [0, 1-n/(2n+1)) is attained -- 30%
        # exactly at r = 1.19135 for n = 4, an ordinary operating point.
        r_star = 1.19135
        assert 1.0 - F.phonon_psd_gradient_factor(r_star, 4.0) == pytest.approx(0.30, abs=1e-3)
        # and the maxima, which are SUPREMA -- approached as r -> infinity, never
        # attained. Checked at r = 10, where the gap (4.3e-4 at n=3) is comfortably
        # above float noise; by r = 1e6 it has converged to the asymptote within
        # double precision and the strict inequality is no longer testable.
        for n in (3.0, 4.0, 5.0):
            sup_psd = 1.0 - n / (2 * n + 1)
            assert F.phonon_psd_gradient_factor(10.0, n) > n / (2 * n + 1)
            assert 1.0 - F.phonon_psd_gradient_factor(10.0, n) < sup_psd
        # the maximum-reading comparison the paper offers as suggestive, not decisive:
        # max amplitude reduction 33% at n=4 is closer to Mather's 30% than max PSD 56%
        assert 1.0 - math.sqrt(4.0 / 9.0) == pytest.approx(0.333, abs=1e-3)
        assert 1.0 - 4.0 / 9.0 == pytest.approx(0.556, abs=1e-3)

    def test_bolometer_referred_gamma_equals_bath_referred_F_link(self):
        # The identity D12's draft cites. Our gamma(r,n) is the bolometer-referred
        # form; the TES literature writes the bath-referred F_link(t,n). Substituting
        # t = 1/r must make them equal -- the trailing r^-(n+1) is exactly the
        # bookkeeping difference. Checked against an INDEPENDENT implementation over a
        # grid, so the paper's "verified as an identity" names an artifact rather than
        # a claim (round-5 finding 1.2 / round-6 finding 2.2).
        for n in (3.0, 4.0, 5.0, 6.0):
            for r in (1.05, 1.19135, 1.5, 2.0, 3.0, 5.0, 10.0):
                ours = F.phonon_psd_gradient_factor(r, n)
                theirs = F.f_link_bath_referred(1.0 / r, n)
                assert ours == pytest.approx(theirs, rel=1e-12), (r, n, ours, theirs)
        # and both degenerate to 1 in the isothermal limit
        assert F.phonon_psd_gradient_factor(1.0, 4.0) == 1.0
        assert F.f_link_bath_referred(1.0, 4.0) == 1.0

    def test_gamma_one_recovers_the_shipped_psd(self):
        assert F.phonon_psd_gamma(1.0, 2.0, 3.0, 1.0) == F.phonon_psd(1.0, 2.0, 3.0)

    def test_gamma_below_one_strictly_reduces_the_psd(self):
        # Lean: phononPSDGamma_lt_phononPSD.
        assert F.phonon_psd_gamma(1.0, 2.0, 3.0, 0.5) < F.phonon_psd(1.0, 2.0, 3.0)

    def test_shipped_psd_overstates_for_a_gradient_loaded_link(self):
        # Lean: phononPSDGamma_lt_phononPSD (bundled as gammaOne_phononPSD_overstates).
        # RETARGETED 2026-07-31: this comment named gammaOne_phononFloor_overstates,
        # but that theorem was rewritten in round 3 to state the FLOOR inequality --
        # this assertion is a PSD comparison, which is the PSD-vs-floor conflation the
        # round-3 blocker was about. The floor mirror is the next test.
        gamma = F.phonon_psd_gradient_factor(2.0, 4.0)
        assert F.phonon_psd_gamma(1.0, 2.0, 3.0, gamma) < F.phonon_psd(1.0, 2.0, 3.0)

    def test_lower_psd_gives_a_larger_matched_budget_and_a_lower_floor(self):
        # Lean: matchedBudget_gamma_ge + gammaOne_phononFloor_overstates. The numerical
        # mirror of the chain built to close round-3 BLOCKER 3.1, which previously had
        # no mirror at all: lower noise PSD => larger matched budget => smaller
        # Gaussian tail => lower floor.
        gamma = F.phonon_psd_gradient_factor(2.0, 4.0)
        psd_1 = F.phonon_psd(1.0, 2.0, 3.0)
        psd_g = F.phonon_psd_gamma(1.0, 2.0, 3.0, gamma)
        assert psd_g < psd_1
        # matchedBudget S T s = sqrt(2 * int_0^T s^2 / S); template energy fixed
        energy = 5.0
        budget = lambda S: math.sqrt(2.0 * energy / S)
        assert budget(psd_g) > budget(psd_1)          # lower PSD -> larger budget
        Q = lambda z: 0.5 * math.erfc(z / math.sqrt(2.0))
        assert Q(budget(psd_g) / 2) < Q(budget(psd_1) / 2)   # -> lower floor


class TestControlAndCeilings:
    """Lean: assignmentFidelity, bsAntiderivative_norm_le."""

    def test_assignment_fidelity_is_the_complement(self):
        assert F.assignment_fidelity(0.1, 0.3) == pytest.approx(0.8, abs=1e-12)
        assert F.assignment_fidelity(0.0, 0.0) == 1.0

    def test_a_floor_on_error_is_a_ceiling_on_fidelity(self):
        floor = F.poisson_avg_error_floor(60.0, 50.0)
        assert F.assignment_fidelity(floor, floor) == pytest.approx(1.0 - floor, abs=1e-12)

    def test_bloch_siegert_scale(self):
        assert F.bloch_siegert_scale(1.0, 10.0) == pytest.approx(0.2, abs=1e-12)


class TestHaldaneLatticeChern:
    """Lean: blochLatticeChern, latticeChern, haldaneFrameTopo,
    haldaneFrameTrivial, haldaneFrame5, haldane_massInversion_not_sufficient_at_N4.

    Added 2026-07-31 (D11 Stage-13 round-7 finding 5.7). The flip location
    |m| ≈ 3.3177 lived only as a `fig.add_vline` literal and two docstrings;
    nothing computed it and nothing pinned it. These tests pin the Python port
    against the three masses the Lean side certifies, and pin the bisection
    against the number the paper and the figure quote.
    """

    def test_port_reproduces_the_three_lean_certified_invariants(self):
        # haldaneFrameTopo (m = 1), haldaneFrame5 (m = 5), haldaneFrameTrivial (m = 6),
        # all at N = 4, t = t₂ = 1, φ = π/2.
        assert F.haldane_lattice_chern(1.0, 4) == -1
        assert F.haldane_lattice_chern(5.0, 4) == 0
        assert F.haldane_lattice_chern(6.0, 4) == 0

    def test_m_equals_5_is_inside_the_window_yet_reads_zero(self):
        # This is the whole content of the retraction: mass inversion is not
        # sufficient for a nonzero invariant at fixed grid size.
        window = F.haldane_mass_inversion_window(1.0, math.pi / 2)
        assert 5.0 < window                      # inside the analytic window
        assert F.haldane_lattice_chern(5.0, 4) == 0

    def test_flip_location_is_the_number_the_paper_quotes(self):
        m_star = F.haldane_flip_location(4)
        assert m_star == pytest.approx(3.3177, abs=5e-5)
        # …and it is a genuine flip: the invariant differs across it.
        assert F.haldane_lattice_chern(m_star - 1e-4, 4) == -1
        assert F.haldane_lattice_chern(m_star + 1e-4, 4) == 0

    def test_roughly_a_third_of_the_window_is_misclassified(self):
        window = F.haldane_mass_inversion_window(1.0, math.pi / 2)
        frac = (window - F.haldane_flip_location(4)) / window
        # "roughly a third" / "about 36 %" in the paper and HaldaneWitness.lean.
        assert 0.35 < frac < 0.37

    def test_bisection_rejects_a_bracket_with_no_flip(self):
        with pytest.raises(ValueError, match="does not straddle"):
            F.haldane_flip_location(4, bracket=(6.0, 8.0))

    def test_grids_divisible_by_three_are_refused(self):
        # D11 round-7 finding 6.1: at 3 | N the sampling hits the Dirac points, the
        # north-pole condition of blochFrameOfD fails EXACTLY, and the Lean frame does
        # not exist. The port used to return -1 anyway, silently.
        for n in (3, 6, 9, 12):
            with pytest.raises(ValueError, match="divisible by 3"):
                F.haldane_lattice_chern(1.0, n)

    def test_the_condition_that_fails_is_exactly_the_north_pole_one(self):
        # Not just "we refuse 3 | N" — the reason must be true. Measure it.
        import numpy as np
        for n in (6, 9):
            worst = min(
                (lambda d: float(np.sqrt(d @ d)) + d[2])(
                    np.array([
                        1.0 + np.cos(2 * np.pi * a / n) + np.cos(2 * np.pi * b / n),
                        -(np.sin(2 * np.pi * a / n) + np.sin(2 * np.pi * b / n)),
                        1.0 - 2.0 * (np.sin(2 * np.pi * a / n)
                                     + np.sin(2 * np.pi * (b - a) / n)
                                     - np.sin(2 * np.pi * b / n)),
                    ]))
                for a in range(n) for b in range(n))
            assert worst == pytest.approx(0.0, abs=1e-12)
        # …and on admissible grids it is strictly positive, so the guard is not vacuous.
        for n in (4, 5, 7):
            F.haldane_lattice_chern(1.0, n)   # does not raise


class TestBirnbaumGoldenValues:
    """Lean: gaussianQ_one_ge_rational (Detection/GaussianThreshold.lean).

    Added 2026-07-31 (D12 Stage-13 round-11 finding 2.2). `gaussian_tail_birnbaum_lower`
    is the source of the paper's 76 % / 95 % tightness figures, and Gate 4 had never
    examined it because it was outside a hand-curated four-formula list. Its coverage was
    bounds-only — no test pinned a value — so a coefficient error would have survived.
    """

    def test_birnbaum_golden_at_z_one_and_two(self):
        phi = lambda z: math.exp(-z * z / 2) / math.sqrt(2 * math.pi)
        # Birnbaum (1942): Q(z) >= phi(z) * z / (1 + z^2)
        assert F.gaussian_tail_birnbaum_lower(1.0) == pytest.approx(
            phi(1.0) * 1.0 / 2.0, rel=1e-15)
        assert F.gaussian_tail_birnbaum_lower(1.0) == pytest.approx(
            0.12098536225957168, rel=1e-15)
        assert F.gaussian_tail_birnbaum_lower(2.0) == pytest.approx(
            phi(2.0) * 2.0 / 5.0, rel=1e-15)
        assert F.gaussian_tail_birnbaum_lower(2.0) == pytest.approx(
            0.021596386605275228, rel=1e-15)

    def test_birnbaum_is_a_lower_bound_and_mills_an_upper(self):
        Q = lambda z: 0.5 * math.erfc(z / math.sqrt(2.0))
        for z in (0.5, 1.0, 2.0, 3.0, 5.0):
            assert F.gaussian_tail_birnbaum_lower(z) <= Q(z) <= F.gaussian_tail_mills_upper(z)

    def test_the_papers_tightness_figures_are_what_the_ratio_gives(self):
        Q = lambda z: 0.5 * math.erfc(z / math.sqrt(2.0))
        assert F.gaussian_tail_birnbaum_lower(1.0) / Q(1.0) == pytest.approx(0.76, abs=5e-3)
        # z = 2, not 3: paper_draft.tex:572 reads "76 % of the true Q(1) = 0.15866,
        # against 95 % at z = 2". I first wrote 3.0 here from memory and the test caught
        # it — the ratio at z = 3 is 0.9849.
        assert F.gaussian_tail_birnbaum_lower(2.0) / Q(2.0) == pytest.approx(0.95, abs=5e-3)
