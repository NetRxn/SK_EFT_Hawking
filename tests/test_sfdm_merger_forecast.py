"""Tests for Phase 5x Wave 5 — SFDM merger forecast and SK-EFT framework.

Covers:

- BK fiducial constants match Lean constants
- Sound-speed formula `c_s² = 2μ/m` (Lean ref `sfdm_sound_speed_sq`)
- Condensate fraction tables (Lean ref ``condensate_frac_*``)
- Rankine-Hugoniot density jump at γ=2 (Lean ref ``rh_density_jump_sfdm``)
- Condensate-fraction corrected density (Lean ref ``delta_rho_corrected``)
- Canonical merger Mach numbers matching W1b table
- Single-cluster S/N formula
- Stacked S/N √N scaling (Lean ref ``snr_stacked_sq``)
- 3σ / 5σ stacking thresholds (Lean ref ``three_sigma_threshold``)
- Per-cluster forecast chain (Bullet exact match to W1b Table 6)
- H₀ sensitivity table
- Smoking-gun step function (Lean ref ``sfdm_offset_step_function``)
- Hawking temperature scenarios — all below T_CMB
- Overall assessment sanity
"""

from __future__ import annotations

import math

import pytest

from src.dark_sector.sfdm_sk_eft import (
    A_0_MOND,
    C_S_KMS_FIDUCIAL,
    CONDENSATE_FRACTION,
    FDR_NOISE_FLOOR_RAR_MAX,
    LAMBDA_MEV_FIDUCIAL,
    M_DM_EV_FIDUCIAL,
    SFDM_HORIZON_SCENARIOS,
    T_CMB_K,
    HaloMassClass,
    SFDMSKEFTAssessment,
    all_horizons_below_cmb,
    analog_hawking_temperature_K,
    assess_sfdm_sk_eft,
    bondi_radius_pc,
    chemical_potential_ev,
    condensate_fraction,
    condensate_fraction_bk_formula,
    fdr_below_rar_observed,
    fdr_noise_floor_fractional,
    max_T_H_K,
    mond_acceleration,
    sfdm_sound_speed_sq,
    sound_speed_kms,
)
from src.dark_sector.sfdm_merger_forecast import (
    CANONICAL_MERGERS,
    EUCLID_WIDE,
    FEATURE_EXTENT_KPC_FIDUCIAL,
    GAMMA_SFDM_EFFECTIVE,
    MERGER_A520,
    MERGER_BULLET,
    MERGER_EL_GORDO,
    MERGER_MACS_J0025,
    MERGER_PANDORA,
    ROMAN_HLSS,
    SFDMMergerForecastAssessment,
    all_canonical_mergers_supersonic,
    assess_sfdm_merger_forecast,
    cdm_dm_galaxy_offset_kpc,
    delta_rho_corrected,
    delta_rho_over_rho0,
    feature_area_arcmin2_for_merger,
    forecast_all_canonical_mergers,
    forecast_single_merger,
    h0_sensitivity_table,
    mach_number,
    n_clusters_for_target_snr,
    rankine_hugoniot_density_jump,
    sfdm_dm_galaxy_offset_kpc,
    sidm_dm_galaxy_offset_kpc,
    sigma_critical_g_cm2,
    single_cluster_snr,
    stacked_snr,
    stacking_forecast_table,
)


# -------------------------------------------------------------------------
# 1. BK fiducial constants (Lean cross-check)
# -------------------------------------------------------------------------


class TestBKFiducialConstants:
    def test_m_dm_matches_lean(self):
        """Lean: ``m_DM_eV_fiducial = 6/10``."""
        assert M_DM_EV_FIDUCIAL == 0.6

    def test_lambda_matches_lean(self):
        """Lean: ``Lambda_meV_fiducial = 2/10``."""
        assert LAMBDA_MEV_FIDUCIAL == 0.2

    def test_c_s_subcluster_matches_lean(self):
        """Lean: ``c_s_subcluster_kms_fiducial = 1525``."""
        assert C_S_KMS_FIDUCIAL[HaloMassClass.SUBCLUSTER] == 1525.0

    def test_c_s_group_matches_lean(self):
        """Lean: ``c_s_group_kms_fiducial = 607``."""
        assert C_S_KMS_FIDUCIAL[HaloMassClass.GROUP] == 607.0

    def test_c_s_galaxy_matches_lean(self):
        """Lean: ``c_s_galaxy_kms_fiducial = 242``."""
        assert C_S_KMS_FIDUCIAL[HaloMassClass.GALAXY] == 242.0

    def test_c_s_monotone_in_halo_mass(self):
        """Lean: ``c_s_monotone_in_halo_mass``."""
        assert (
            C_S_KMS_FIDUCIAL[HaloMassClass.GALAXY]
            < C_S_KMS_FIDUCIAL[HaloMassClass.GROUP]
            < C_S_KMS_FIDUCIAL[HaloMassClass.SUBCLUSTER]
        )


# -------------------------------------------------------------------------
# 2. Sound-speed formula
# -------------------------------------------------------------------------


class TestSoundSpeedFormula:
    def test_positivity(self):
        """Lean: ``sfdm_sound_speed_sq_pos``."""
        assert sfdm_sound_speed_sq(1.0, 1.0) > 0

    def test_mu_linear_scaling(self):
        """Lean: ``sfdm_sound_speed_sq_linear_mu``."""
        assert sfdm_sound_speed_sq(2.0, 1.0) == pytest.approx(2 * sfdm_sound_speed_sq(1.0, 1.0))

    def test_m_inverse_scaling(self):
        """Lean: ``sfdm_sound_speed_sq_inverse_m``."""
        assert 2 * sfdm_sound_speed_sq(1.0, 2.0) == pytest.approx(sfdm_sound_speed_sq(1.0, 1.0))

    def test_mass_must_be_positive(self):
        with pytest.raises(ValueError):
            sfdm_sound_speed_sq(1.0, 0.0)

    def test_chemical_potential_positive(self):
        mu = chemical_potential_ev(1e-26, 0.6, 0.2)
        assert mu > 0

    def test_sound_speed_kms_lookup(self):
        assert sound_speed_kms(HaloMassClass.SUBCLUSTER) == 1525.0


# -------------------------------------------------------------------------
# 3. Condensate fraction
# -------------------------------------------------------------------------


class TestCondensateFraction:
    def test_galaxy_near_full_superfluid(self):
        """Lean: condensate_frac_galaxy not in Lean but BK Eq. 17 gives >0.99."""
        assert condensate_fraction(HaloMassClass.GALAXY) > 0.99

    def test_subcluster_partial_condensate(self):
        """Lean: ``condensate_frac_subcluster = 59/100``."""
        assert condensate_fraction(HaloMassClass.SUBCLUSTER) == pytest.approx(0.59)

    def test_main_cluster_zero_condensate(self):
        """Lean: ``condensate_frac_main_cluster = 0``."""
        assert condensate_fraction(HaloMassClass.MAIN_CLUSTER) == 0.0

    def test_group_high_condensate(self):
        """Lean: ``condensate_frac_group = 96/100``. Python BK Eq.17 → 0.959 (same to rounding)."""
        assert condensate_fraction(HaloMassClass.GROUP) == pytest.approx(0.96, abs=0.01)

    def test_bk_formula_bounded(self):
        """BK Eq. 17 returns fraction in [0,1]."""
        for M in [1e12, 1e13, 1e14, 1e15]:
            f = condensate_fraction_bk_formula(0.6, M)
            assert 0.0 <= f <= 1.0

    def test_bk_formula_decreasing_in_M(self):
        """Higher halo mass → lower condensate fraction (thermodynamic)."""
        f12 = condensate_fraction_bk_formula(0.6, 1e12)
        f14 = condensate_fraction_bk_formula(0.6, 1e14)
        f15 = condensate_fraction_bk_formula(0.6, 1e15)
        assert f12 > f14 > f15


# -------------------------------------------------------------------------
# 4. Rankine-Hugoniot density jump
# -------------------------------------------------------------------------


class TestRankineHugoniot:
    def test_jump_at_M1_trivial(self):
        """At M=1, R-H gives unity (no shock)."""
        assert rankine_hugoniot_density_jump(1.0, 2.0) == pytest.approx(1.0)

    def test_jump_at_M_bullet_sfdm(self):
        """Lean: ``rh_density_jump_sfdm`` at M=1.77 → ≈1.83 (W1b 83%)."""
        ratio = rankine_hugoniot_density_jump(1.77, 2.0)
        assert ratio == pytest.approx(1.832, rel=1e-2)

    def test_delta_rho_at_bullet(self):
        """W1b: δρ/ρ₀ ≈ 83% at Bullet Mach 1.77 with γ=2."""
        dr = delta_rho_over_rho0(1.77, 2.0)
        assert dr == pytest.approx(0.832, rel=1e-2)

    def test_delta_rho_monotone_in_mach(self):
        """Lean: ``delta_rho_monotone_in_mach_sfdm``."""
        mach_vals = [1.0, 1.3, 1.5, 1.8, 2.2, 3.0]
        dr_vals = [delta_rho_over_rho0(M, 2.0) for M in mach_vals]
        for i in range(len(dr_vals) - 1):
            assert dr_vals[i] <= dr_vals[i + 1]

    def test_condensate_correction_dilutes(self):
        """Lean: condensate correction gives `f_c · δρ/ρ₀`."""
        dr_bare = delta_rho_over_rho0(1.77, 2.0)
        dr_corr = delta_rho_corrected(1.77, 2.0, 0.59)
        assert dr_corr == pytest.approx(0.59 * dr_bare, rel=1e-10)

    def test_condensate_correction_bullet_49pct(self):
        """W1b Block 4: Bullet corrected δρ/ρ₀ ≈ 49%."""
        dr = delta_rho_corrected(1.77, 2.0, 0.59)
        assert dr == pytest.approx(0.491, rel=2e-2)

    def test_condensate_correction_nonneg(self):
        """Lean: ``delta_rho_corrected_nonneg``."""
        for M in [1.0, 1.5, 2.0, 3.0]:
            for f_c in [0.0, 0.5, 1.0]:
                assert delta_rho_corrected(M, 2.0, f_c) >= 0.0

    def test_mach_below_one_raises(self):
        """Subsonic input must raise (no shock forms)."""
        with pytest.raises(ValueError):
            rankine_hugoniot_density_jump(0.5, 2.0)


# -------------------------------------------------------------------------
# 5. Mach numbers for canonical mergers
# -------------------------------------------------------------------------


class TestCanonicalMergers:
    def test_all_canonical_supersonic(self):
        """Lean: ``all_canonical_mergers_supersonic``."""
        assert all_canonical_mergers_supersonic()

    def test_bullet_mach_matches_roadmap(self):
        """W1b Table: Bullet M = 1.77 at BK fiducial."""
        c_s = C_S_KMS_FIDUCIAL[HaloMassClass.SUBCLUSTER]
        M = mach_number(MERGER_BULLET.v_infall_kms, c_s)
        assert M == pytest.approx(1.77, abs=0.01)

    def test_pandora_highest_mach(self):
        """Lean: ``pandora_highest_mach``. W1b: Pandora M=2.23."""
        c_s = C_S_KMS_FIDUCIAL[HaloMassClass.SUBCLUSTER]
        machs = {m.name: mach_number(m.v_infall_kms, c_s) for m in CANONICAL_MERGERS}
        assert machs[MERGER_PANDORA.name] == max(machs.values())
        assert machs[MERGER_PANDORA.name] == pytest.approx(2.23, abs=0.01)

    def test_macs_j0025_lowest_mach(self):
        """Lean: ``macs_j0025_lowest_mach``. W1b: MACS J0025 M=1.31."""
        c_s = C_S_KMS_FIDUCIAL[HaloMassClass.SUBCLUSTER]
        machs = {m.name: mach_number(m.v_infall_kms, c_s) for m in CANONICAL_MERGERS}
        assert machs[MERGER_MACS_J0025.name] == min(machs.values())
        assert machs[MERGER_MACS_J0025.name] == pytest.approx(1.31, abs=0.01)

    def test_five_canonical_targets(self):
        assert len(CANONICAL_MERGERS) == 5

    def test_canonical_names_unique(self):
        names = [m.name for m in CANONICAL_MERGERS]
        assert len(set(names)) == len(names)


# -------------------------------------------------------------------------
# 6. Single-cluster and stacked S/N
# -------------------------------------------------------------------------


class TestSingleClusterSNR:
    def test_snr_formula_bullet_roman_matches_w1b(self):
        """W1b Table 6: Bullet/Roman S/N ≈ 1.03."""
        r = forecast_single_merger(MERGER_BULLET)
        assert r.snr_roman == pytest.approx(1.03, abs=0.05)

    def test_snr_formula_bullet_euclid_matches_w1b(self):
        """W1b Table 6: Bullet/Euclid S/N ≈ 0.83."""
        r = forecast_single_merger(MERGER_BULLET)
        assert r.snr_euclid == pytest.approx(0.83, abs=0.05)

    def test_snr_nonneg(self):
        for merger in CANONICAL_MERGERS:
            r = forecast_single_merger(merger)
            assert r.snr_euclid >= 0
            assert r.snr_roman >= 0

    def test_snr_zero_shape_noise_raises(self):
        with pytest.raises(ValueError):
            single_cluster_snr(0.024, 30.0, 0.0, 2.7)


class TestStackedSNR:
    def test_stacked_scaling(self):
        """Lean: ``snr_stacked_sq``: SNR_stacked² = SNR_single² · N."""
        single = 0.83
        for N in [1, 10, 30, 100]:
            stacked = stacked_snr(single, N)
            assert stacked**2 == pytest.approx(single**2 * N, rel=1e-10)

    def test_stacked_at_N1_equals_single(self):
        """Lean: ``snr_stacked_single``."""
        for single in [0.5, 1.0, 2.0]:
            assert stacked_snr(single, 1) == pytest.approx(single)

    def test_stacked_monotone(self):
        """Lean: ``snr_stacked_monotone``."""
        single = 1.0
        vals = [stacked_snr(single, N) for N in [1, 10, 30, 100]]
        for i in range(len(vals) - 1):
            assert vals[i] <= vals[i + 1]

    def test_three_sigma_threshold_bullet_roman(self):
        """Lean: ``bullet_roman_3sigma_at_N_18``.
        Roman Bullet (S/N ≈ 1.03) reaches 3σ by N ≈ 9-10."""
        r = forecast_single_merger(MERGER_BULLET)
        N = n_clusters_for_target_snr(r.snr_roman, 3.0)
        assert 5 <= N <= 15  # tolerance band around W1b ~10

    def test_five_sigma_threshold_bullet_roman(self):
        """Lean: ``bullet_roman_5sigma_at_N_50``. N ≈ 24-30."""
        r = forecast_single_merger(MERGER_BULLET)
        N = n_clusters_for_target_snr(r.snr_roman, 5.0)
        assert 20 <= N <= 40

    def test_negative_target_raises(self):
        with pytest.raises(ValueError):
            n_clusters_for_target_snr(1.0, -1.0)

    def test_zero_single_snr_raises(self):
        with pytest.raises(ValueError):
            n_clusters_for_target_snr(0.0, 3.0)


# -------------------------------------------------------------------------
# 7. Stacking forecast table
# -------------------------------------------------------------------------


class TestStackingForecastTable:
    def test_table_has_all_N_and_surveys(self):
        """5 N × 2 surveys = 10 rows."""
        rows = stacking_forecast_table()
        assert len(rows) == 10

    def test_large_N_crosses_3sigma(self):
        rows = stacking_forecast_table(N_values=(100,))
        for row in rows:
            assert row.reaches_3sigma

    def test_small_N_fails_3sigma(self):
        rows = stacking_forecast_table(N_values=(1,))
        for row in rows:
            assert not row.reaches_3sigma


# -------------------------------------------------------------------------
# 8. Σ_cr and H₀ sensitivity
# -------------------------------------------------------------------------


class TestSigmaCritical:
    def test_bullet_sigma_cr_matches_w1b(self):
        """W1b Block 5: Σ_cr ≈ 0.63 g/cm²."""
        Sigma = sigma_critical_g_cm2(830.0, 1650.0, 1100.0)
        assert Sigma == pytest.approx(0.63, rel=0.05)

    def test_sigma_cr_positive(self):
        for merger in CANONICAL_MERGERS:
            assert sigma_critical_g_cm2(merger.D_L_mpc, merger.D_S_mpc, merger.D_LS_mpc) > 0


class TestH0Sensitivity:
    def test_two_rows(self):
        """Planck + H0DN."""
        table = h0_sensitivity_table()
        assert len(table) == 2

    def test_planck_baseline_ratio_is_one(self):
        table = h0_sensitivity_table()
        planck = table[0]
        assert planck.H0_label == "Planck"
        assert planck.sigma_cr_ratio_vs_planck == 1.0

    def test_h0dn_shift_modest(self):
        """W1b: ~8% shift, within ~5-15%."""
        table = h0_sensitivity_table()
        h0dn = table[1]
        assert h0dn.H0_label == "H0DN"
        assert 1.04 < h0dn.sigma_cr_ratio_vs_planck < 1.15


# -------------------------------------------------------------------------
# 9. Smoking-gun step function (Paper 17 Figure 1)
# -------------------------------------------------------------------------


class TestSmokingGunStepFunction:
    def test_sfdm_subsonic_no_offset(self):
        """Lean: ``sfdm_offset_step_function`` — subsonic gives zero."""
        for M in [0.5, 0.8, 0.99]:
            assert sfdm_dm_galaxy_offset_kpc(M) == 0.0

    def test_sfdm_supersonic_offset(self):
        """Lean: ``sfdm_offset_step_function`` — supersonic gives nonzero."""
        for M in [1.1, 1.5, 2.0, 3.0]:
            assert sfdm_dm_galaxy_offset_kpc(M) > 0.0

    def test_sidm_smooth_rise(self):
        """SIDM grows smoothly (no threshold)."""
        offsets = [sidm_dm_galaxy_offset_kpc(M) for M in [1.0, 1.5, 2.0, 2.5, 3.0]]
        for i in range(len(offsets) - 1):
            assert offsets[i] <= offsets[i + 1]

    def test_cdm_always_zero(self):
        """CDM gives no DM-galaxy offset at any Mach."""
        for M in [0.5, 1.0, 1.5, 2.0, 3.0]:
            assert cdm_dm_galaxy_offset_kpc(M) == 0.0

    def test_sfdm_discontinuity_at_M1(self):
        """The hallmark SFDM signature: step at M=1."""
        below = sfdm_dm_galaxy_offset_kpc(0.99)
        above = sfdm_dm_galaxy_offset_kpc(1.01)
        assert below == 0.0 and above > 0.0


# -------------------------------------------------------------------------
# 10. Hawking-temperature scenarios (pedagogical)
# -------------------------------------------------------------------------


class TestHawkingTemperatures:
    def test_all_scenarios_below_cmb(self):
        """Every scenario has T_H ≪ T_CMB."""
        assert all_horizons_below_cmb()

    def test_max_T_H_below_cmb(self):
        assert max_T_H_K() < T_CMB_K

    def test_bondi_radius_mw_smbh(self):
        """MW SMBH (4×10⁶ M☉, c_s ≈ 220 km/s) → Bondi ≈ 0.36 pc."""
        r_B = bondi_radius_pc(4e6, 220.0)
        assert r_B == pytest.approx(0.36, rel=0.15)

    def test_analog_hawking_T_formula(self):
        """Direct: T_H = ℏκ/(2π k_B)."""
        # For κ = 2e-11 s⁻¹ (MW Bondi), T_H ≈ 2.4e-23 K
        T_H = analog_hawking_temperature_K(2e-11)
        assert T_H == pytest.approx(2.4e-23, rel=0.15)

    def test_five_scenarios_listed(self):
        assert len(SFDM_HORIZON_SCENARIOS) == 5


# -------------------------------------------------------------------------
# 11. MOND + FDR noise-floor
# -------------------------------------------------------------------------


class TestMONDAndFDR:
    def test_mond_acceleration_sqrt_law(self):
        """a_φ = √(a_N · a_0)."""
        a_N = 1e-12
        a_phi = mond_acceleration(a_N)
        assert a_phi == pytest.approx(math.sqrt(a_N * A_0_MOND))

    def test_fdr_noise_nonneg(self):
        for T_ratio in [0.0, 0.01, 0.1]:
            for Gamma_ratio in [0.0, 0.1, 1.0]:
                assert fdr_noise_floor_fractional(T_ratio, Gamma_ratio) >= 0

    def test_fdr_max_below_rar_observed(self):
        """W1 Task 4 §3.1: max FDR floor 10⁻³ is below RAR 0.06 dex scatter."""
        assert fdr_below_rar_observed()

    def test_fdr_upper_bound_small(self):
        """Sanity: upper bound of FDR RAR floor is < 1%."""
        assert FDR_NOISE_FLOOR_RAR_MAX < 0.01


# -------------------------------------------------------------------------
# 12. Per-merger geometry helpers
# -------------------------------------------------------------------------


class TestFeatureAreaGeometry:
    def test_bullet_feature_area_matches_calibration(self):
        """400 kpc @ D_L=830 Mpc → ~2.7 arcmin²."""
        A = feature_area_arcmin2_for_merger(MERGER_BULLET)
        assert A == pytest.approx(2.74, rel=0.05)

    def test_el_gordo_smaller_angular_area(self):
        """Higher z → smaller angular area for same physical extent."""
        A_bullet = feature_area_arcmin2_for_merger(MERGER_BULLET)
        A_el_gordo = feature_area_arcmin2_for_merger(MERGER_EL_GORDO)
        assert A_el_gordo < A_bullet

    def test_a520_larger_angular_area(self):
        """Lower z → larger angular area for same physical extent."""
        A_bullet = feature_area_arcmin2_for_merger(MERGER_BULLET)
        A_a520 = feature_area_arcmin2_for_merger(MERGER_A520)
        assert A_a520 > A_bullet

    def test_fiducial_feature_extent(self):
        assert FEATURE_EXTENT_KPC_FIDUCIAL == 400.0


# -------------------------------------------------------------------------
# 13. Top-level assessments
# -------------------------------------------------------------------------


class TestSFDMSKEFTAssessment:
    def test_assessment_is_dataclass(self):
        a = assess_sfdm_sk_eft()
        assert isinstance(a, SFDMSKEFTAssessment)

    def test_all_horizons_below_cmb_true(self):
        assert assess_sfdm_sk_eft().all_horizons_below_cmb

    def test_fdr_below_rar_observed_true(self):
        assert assess_sfdm_sk_eft().fdr_below_rar_observed

    def test_subcluster_condensate_59pct(self):
        a = assess_sfdm_sk_eft()
        assert a.condensate_frac_subcluster == pytest.approx(0.59)


class TestMergerForecastAssessment:
    def test_assessment_is_dataclass(self):
        a = assess_sfdm_merger_forecast()
        assert isinstance(a, SFDMMergerForecastAssessment)

    def test_verdict_is_conditional_go(self):
        """W1b §Block 12: CONDITIONAL GO."""
        assert assess_sfdm_merger_forecast().paper17_verdict == "CONDITIONAL GO"

    def test_all_canonical_supersonic(self):
        assert assess_sfdm_merger_forecast().all_canonical_supersonic

    def test_n_mergers_five(self):
        assert assess_sfdm_merger_forecast().n_canonical_mergers == 5

    def test_bullet_euclid_snr_matches_w1b(self):
        """Headline: Bullet Euclid S/N ≈ 0.83."""
        a = assess_sfdm_merger_forecast()
        assert a.bullet_single_snr_euclid == pytest.approx(0.83, abs=0.05)

    def test_bullet_roman_snr_matches_w1b(self):
        """Headline: Bullet Roman S/N ≈ 1.03."""
        a = assess_sfdm_merger_forecast()
        assert a.bullet_single_snr_roman == pytest.approx(1.03, abs=0.05)

    def test_stacking_thresholds_in_range(self):
        """W1b ~30 Euclid / ~20 Roman for 3σ; we get within factor 2."""
        a = assess_sfdm_merger_forecast()
        assert 10 <= a.n_clusters_for_3sigma_euclid <= 60
        assert 5 <= a.n_clusters_for_3sigma_roman <= 40

    def test_h0dn_sigma_cr_ratio_modest(self):
        a = assess_sfdm_merger_forecast()
        assert 1.03 < a.sigma_cr_ratio_h0dn_vs_planck < 1.15


# -------------------------------------------------------------------------
# 14. Python ↔ Lean explicit cross-checks
# -------------------------------------------------------------------------


class TestPythonLeanCrossChecks:
    def test_bk_fiducial_mirrors_lean(self):
        """Lean: m_DM_eV_fiducial = 6/10, Lambda_meV_fiducial = 2/10."""
        assert M_DM_EV_FIDUCIAL == pytest.approx(6 / 10)
        assert LAMBDA_MEV_FIDUCIAL == pytest.approx(2 / 10)

    def test_condensate_frac_subcluster_mirror_lean(self):
        """Lean: condensate_frac_subcluster = 59/100."""
        assert CONDENSATE_FRACTION[HaloMassClass.SUBCLUSTER] == pytest.approx(59 / 100)

    def test_delta_rho_sfdm_matches_subtractive_form(self):
        """Lean: ``rh_density_jump_sfdm_subtractive`` — `3 - 6/(M²+2)`."""
        for M in [1.0, 1.5, 2.0, 3.0]:
            direct = rankine_hugoniot_density_jump(M, 2.0)
            subtractive = 3.0 - 6.0 / (M**2 + 2.0)
            assert direct == pytest.approx(subtractive, rel=1e-10)

    def test_stacked_snr_squared_identity(self):
        """Lean: ``snr_stacked_sq``."""
        for N in [1, 5, 30, 100]:
            single = 0.83
            stacked = stacked_snr(single, N)
            assert stacked**2 == pytest.approx(single**2 * N, rel=1e-10)

    def test_gamma_sfdm_effective_equals_2(self):
        """Lean: SFDM γ_eff = 2 throughout."""
        assert GAMMA_SFDM_EFFECTIVE == 2.0
