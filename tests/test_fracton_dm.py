"""Tests for src/dark_sector/fracton_dm.py (Phase 5x Wave 7)."""

from __future__ import annotations

import math

import pytest

from src.dark_sector import fracton_dm as fdm
from src.dark_sector.fracton_dm import (
    ARRHENIUS_GAPPED_10MeV,
    ARRHENIUS_WINDOW_UPPER_MeV,
    CS_SQ_DIPOLE_BOUND,
    DRILLDOWN_PWAVE_1MeV,
    EOS_FRACTON_DUST,
    EXCLUDED_GAPPED_EV,
    FRACTON_GRAVITON_COUPLING_SIGN,
    FRACTON_IS_SM_SINGLET,
    FractonDMCandidate,
    FractonDMPhase,
    M_D_ARRHENIUS_BBN_MeV,
    MU_CONDENSATE_BBN_MeV,
    PWAVE_WINDOW_UPPER_MeV,
    SIGMA_BULLET_CLUSTER_CM2_PER_G,
    SIGMA_EFF_FRACTON_CM2_PER_G,
    T_BBN_MeV,
    Z_SUBDIFFUSION,
    arrhenius_lifetime,
    arrhenius_md_bbn_lower_bound_MeV,
    arrhenius_survives_bbn,
    assess_fracton_dm_status,
    bullet_cluster_passes,
    condensate_cold,
    condensate_lower_bound_at_epoch_MeV,
    fracton_dust_eos,
    fracton_gravity_attractive,
    fracton_subdiffusion_core_radius_estimate,
    fracton_viable_at_epoch,
    fracton_ww_bypass_applies,
    haah_superexponential_lifetime,
    hubble_radiation_era_inv_MeV,
    z4_subdiffusion_preserved_in_phase,
)


class TestModuleConstants:
    def test_bbn_temperature(self):
        assert T_BBN_MeV == pytest.approx(0.1)

    def test_arrhenius_floor_greater_than_condensate(self):
        assert M_D_ARRHENIUS_BBN_MeV > MU_CONDENSATE_BBN_MeV

    def test_arrhenius_window_ordered(self):
        assert M_D_ARRHENIUS_BBN_MeV < ARRHENIUS_WINDOW_UPPER_MeV
        # 4 decades (10 MeV → 100 GeV = 1e5 MeV)
        assert ARRHENIUS_WINDOW_UPPER_MeV / M_D_ARRHENIUS_BBN_MeV == pytest.approx(1e4)

    def test_pwave_window_ordered(self):
        assert MU_CONDENSATE_BBN_MeV < PWAVE_WINDOW_UPPER_MeV
        # Conservatively 7 decades (1 MeV → 10 TeV = 1e7 MeV)
        assert PWAVE_WINDOW_UPPER_MeV / MU_CONDENSATE_BBN_MeV == pytest.approx(1e7)

    def test_z_subdiffusion_is_four(self):
        assert Z_SUBDIFFUSION == 4

    def test_fracton_dust_is_pressureless(self):
        assert EOS_FRACTON_DUST == 0.0

    def test_sigma_eff_zero(self):
        assert SIGMA_EFF_FRACTON_CM2_PER_G == 0.0

    def test_sigma_eff_below_bullet_bound(self):
        assert SIGMA_EFF_FRACTON_CM2_PER_G < SIGMA_BULLET_CLUSTER_CM2_PER_G

    def test_graviton_sign_positive(self):
        assert FRACTON_GRAVITON_COUPLING_SIGN > 0

    def test_sm_singlet_flag(self):
        assert FRACTON_IS_SM_SINGLET is True

    def test_cs_sq_subluminal(self):
        assert 0 < CS_SQ_DIPOLE_BOUND < 1


class TestArrheniusLifetime:
    def test_lifetime_exceeds_tau0_for_positive_gap(self):
        assert arrhenius_lifetime(10.0, 0.1, tau_0_s=1.0) > 1.0

    def test_lifetime_monotone_in_Md(self):
        assert arrhenius_lifetime(1.0, 0.1) < arrhenius_lifetime(10.0, 0.1)

    def test_lifetime_monotone_decreasing_in_T(self):
        assert arrhenius_lifetime(1.0, 0.1) > arrhenius_lifetime(1.0, 1.0)

    def test_at_equal_md_and_T_gives_e(self):
        assert arrhenius_lifetime(1.0, 1.0, tau_0_s=1.0) == pytest.approx(math.e)

    def test_negative_inputs_rejected(self):
        with pytest.raises(ValueError):
            arrhenius_lifetime(-1.0, 0.1)
        with pytest.raises(ValueError):
            arrhenius_lifetime(1.0, 0.0)
        with pytest.raises(ValueError):
            arrhenius_lifetime(1.0, 0.1, tau_0_s=0.0)

    def test_haah_superexponential_exceeds_arrhenius(self):
        # Pick modest M_d/T so exp((M_d/T)²) stays finite in IEEE 754.
        # For M_d/T = 5: Arrhenius exp(5) ≈ 148, Haah exp(25) ≈ 7.2e10.
        M_d, T = 5.0, 1.0
        arr = arrhenius_lifetime(M_d, T)
        haah = haah_superexponential_lifetime(M_d, T, c=1.0)
        # Haah goes as exp((M_d/T)²), faster than exp(M_d/T) for M_d >> T
        assert haah > arr

    def test_haah_negative_inputs_rejected(self):
        with pytest.raises(ValueError):
            haah_superexponential_lifetime(0.0, 0.1)
        with pytest.raises(ValueError):
            haah_superexponential_lifetime(1.0, 0.1, c=0.0)


class TestBBNBounds:
    def test_arrhenius_md_bbn_lower_bound_near_10MeV(self):
        floor = arrhenius_md_bbn_lower_bound_MeV()
        # Deep research: ~10 MeV with default g_* = 10.75
        assert 10.0 < floor < 12.0

    def test_arrhenius_floor_invariants(self):
        # Lower T_BBN → lower floor
        floor_low = arrhenius_md_bbn_lower_bound_MeV(T_BBN_MeV_local=0.01)
        floor_std = arrhenius_md_bbn_lower_bound_MeV(T_BBN_MeV_local=0.1)
        assert floor_low < floor_std

    def test_arrhenius_survives_at_10MeV(self):
        assert arrhenius_survives_bbn(M_d_MeV=10.0) is False  # 10 < ~10.46
        assert arrhenius_survives_bbn(M_d_MeV=100.0) is True  # safely above

    def test_arrhenius_survives_monotone(self):
        # Passing the threshold flips the flag
        floor = arrhenius_md_bbn_lower_bound_MeV()
        assert arrhenius_survives_bbn(M_d_MeV=floor - 0.01) is False
        assert arrhenius_survives_bbn(M_d_MeV=floor + 0.01) is True

    def test_eV_scale_fails_arrhenius(self):
        # 1 eV = 1e-6 MeV — miles below 10 MeV floor
        assert arrhenius_survives_bbn(M_d_MeV=1e-6) is False

    def test_arrhenius_negative_inputs_rejected(self):
        with pytest.raises(ValueError):
            arrhenius_md_bbn_lower_bound_MeV(T_BBN_MeV_local=-0.1)
        with pytest.raises(ValueError):
            arrhenius_md_bbn_lower_bound_MeV(g_star=0.0)


class TestHubbleRadiationEra:
    def test_hubble_inv_positive(self):
        assert hubble_radiation_era_inv_MeV(T_MeV=0.1) > 0

    def test_hubble_inv_grows_as_T_decreases(self):
        # H(T) ~ T², so H⁻¹ ~ T⁻² — inverse Hubble grows at lower T
        inv_high_T = hubble_radiation_era_inv_MeV(T_MeV=100.0)
        inv_low_T = hubble_radiation_era_inv_MeV(T_MeV=0.1)
        assert inv_low_T > inv_high_T

    def test_hubble_g_star_effect(self):
        # More d.o.f. → faster expansion → smaller H⁻¹
        inv_small_g = hubble_radiation_era_inv_MeV(T_MeV=0.1, g_star=1.0)
        inv_big_g = hubble_radiation_era_inv_MeV(T_MeV=0.1, g_star=100.0)
        assert inv_small_g > inv_big_g

    def test_hubble_negative_inputs_rejected(self):
        with pytest.raises(ValueError):
            hubble_radiation_era_inv_MeV(T_MeV=0.0)
        with pytest.raises(ValueError):
            hubble_radiation_era_inv_MeV(T_MeV=1.0, g_star=-1.0)


class TestCondensateCondition:
    def test_cold_when_mu_gt_T(self):
        assert condensate_cold(mu_MeV=1.0, T_MeV=0.1) is True

    def test_not_cold_when_mu_le_T(self):
        assert condensate_cold(mu_MeV=0.1, T_MeV=0.1) is False
        assert condensate_cold(mu_MeV=0.05, T_MeV=0.1) is False

    def test_condensate_lower_bound_equals_T(self):
        assert condensate_lower_bound_at_epoch_MeV(0.1) == 0.1
        assert condensate_lower_bound_at_epoch_MeV(1000.0) == 1000.0

    def test_1MeV_cold_at_BBN(self):
        # Drilldown preferred case
        assert condensate_cold(MU_CONDENSATE_BBN_MeV, T_BBN_MeV) is True

    def test_condensate_negative_inputs_rejected(self):
        with pytest.raises(ValueError):
            condensate_cold(0.0, 0.1)
        with pytest.raises(ValueError):
            condensate_cold(1.0, -0.1)
        with pytest.raises(ValueError):
            condensate_lower_bound_at_epoch_MeV(0.0)


class TestPhenomenologicalSignatures:
    def test_bullet_passes(self):
        assert bullet_cluster_passes() is True

    def test_fracton_dust_eos_zero(self):
        assert fracton_dust_eos() == 0.0

    def test_gravity_always_attractive(self):
        assert fracton_gravity_attractive() is True

    def test_ww_bypasses_for_non_covariant(self):
        # Fracton EFT has non-covariant stress tensor → WW bypasses
        assert fracton_ww_bypass_applies(lorentz_covariant_stress_tensor=False) is True

    def test_ww_applies_for_covariant(self):
        # A Lorentz-covariant stress tensor would NOT bypass WW
        assert fracton_ww_bypass_applies(lorentz_covariant_stress_tensor=True) is False

    def test_z4_preserved_in_pwave(self):
        assert z4_subdiffusion_preserved_in_phase(FractonDMPhase.PWAVE_CONDENSATE)

    def test_z4_preserved_in_gapless_u1(self):
        assert z4_subdiffusion_preserved_in_phase(FractonDMPhase.GAPLESS_U1)

    def test_z4_not_preserved_in_gapped(self):
        assert not z4_subdiffusion_preserved_in_phase(FractonDMPhase.GAPPED_TOPO)

    def test_z4_not_preserved_in_swave(self):
        assert not z4_subdiffusion_preserved_in_phase(FractonDMPhase.SWAVE_CONDENSATE)


class TestSubdiffusionCore:
    def test_core_radius_scales_correctly(self):
        # For M_d / M_f ~ 1e-2, core radius should be nonzero and finite
        r_c = fracton_subdiffusion_core_radius_estimate(
            M_d_eV=1e-4, M_fracton_eV=1e-2,
            rho_c_MeV4=1e-50, G_Newton_invMeV2=1e-44,
        )
        assert r_c > 0
        assert math.isfinite(r_c)

    def test_core_radius_grows_with_Md(self):
        # Larger M_d → more resistance to infall → larger core
        r1 = fracton_subdiffusion_core_radius_estimate(
            M_d_eV=1e-4, M_fracton_eV=1e-2,
            rho_c_MeV4=1e-50, G_Newton_invMeV2=1e-44,
        )
        r2 = fracton_subdiffusion_core_radius_estimate(
            M_d_eV=1e-2, M_fracton_eV=1e-2,
            rho_c_MeV4=1e-50, G_Newton_invMeV2=1e-44,
        )
        assert r2 > r1

    def test_core_radius_negative_inputs_rejected(self):
        with pytest.raises(ValueError):
            fracton_subdiffusion_core_radius_estimate(
                M_d_eV=-1.0, M_fracton_eV=1.0,
                rho_c_MeV4=1.0, G_Newton_invMeV2=1.0,
            )
        with pytest.raises(ValueError):
            fracton_subdiffusion_core_radius_estimate(
                M_d_eV=1.0, M_fracton_eV=0.0,
                rho_c_MeV4=1.0, G_Newton_invMeV2=1.0,
            )


class TestViabilityClassifier:
    def test_pwave_1MeV_viable_at_bbn(self):
        assert fracton_viable_at_epoch(
            FractonDMPhase.PWAVE_CONDENSATE, 1.0, T_BBN_MeV
        ) is True

    def test_pwave_below_T_not_viable(self):
        assert fracton_viable_at_epoch(
            FractonDMPhase.PWAVE_CONDENSATE, 0.05, T_BBN_MeV
        ) is False

    def test_gapped_10MeV_viable_at_bbn(self):
        assert fracton_viable_at_epoch(
            FractonDMPhase.GAPPED_TOPO, 10.0, T_BBN_MeV
        ) is True

    def test_gapped_1MeV_not_viable_at_bbn(self):
        # Only 10× above T_BBN, not 100× — fails Arrhenius
        assert fracton_viable_at_epoch(
            FractonDMPhase.GAPPED_TOPO, 1.0, T_BBN_MeV
        ) is False

    def test_gapped_eV_not_viable(self):
        assert fracton_viable_at_epoch(
            FractonDMPhase.GAPPED_TOPO, 1e-6, T_BBN_MeV
        ) is False

    def test_swave_always_excluded(self):
        for scale in [0.1, 1.0, 100.0, 1e10]:
            assert fracton_viable_at_epoch(
                FractonDMPhase.SWAVE_CONDENSATE, scale, T_BBN_MeV
            ) is False

    def test_gapless_u1_behaves_like_gapped_arrhenius(self):
        # Same 100× Arrhenius rule
        assert fracton_viable_at_epoch(
            FractonDMPhase.GAPLESS_U1, 10.0, T_BBN_MeV
        ) is True
        assert fracton_viable_at_epoch(
            FractonDMPhase.GAPLESS_U1, 1.0, T_BBN_MeV
        ) is False

    def test_viable_negative_inputs_rejected(self):
        with pytest.raises(ValueError):
            fracton_viable_at_epoch(FractonDMPhase.PWAVE_CONDENSATE, 0.0, 0.1)
        with pytest.raises(ValueError):
            fracton_viable_at_epoch(FractonDMPhase.PWAVE_CONDENSATE, 1.0, -0.1)


class TestCanonicalWitnesses:
    def test_drilldown_witness_viable(self):
        assert DRILLDOWN_PWAVE_1MeV.viable_at(T_BBN_MeV) is True

    def test_drilldown_witness_phase_is_pwave(self):
        assert DRILLDOWN_PWAVE_1MeV.phase is FractonDMPhase.PWAVE_CONDENSATE

    def test_drilldown_witness_scale_is_1MeV(self):
        assert DRILLDOWN_PWAVE_1MeV.scale_MeV == MU_CONDENSATE_BBN_MeV

    def test_arrhenius_witness_viable(self):
        assert ARRHENIUS_GAPPED_10MeV.viable_at(T_BBN_MeV) is True

    def test_arrhenius_witness_scale_is_10MeV(self):
        assert ARRHENIUS_GAPPED_10MeV.scale_MeV == M_D_ARRHENIUS_BBN_MeV

    def test_excluded_witness_not_viable(self):
        assert EXCLUDED_GAPPED_EV.viable_at(T_BBN_MeV) is False

    def test_excluded_witness_scale_is_1eV(self):
        # 1 eV = 1e-6 MeV
        assert EXCLUDED_GAPPED_EV.scale_MeV == pytest.approx(1e-6)

    def test_candidate_labels_nonempty(self):
        for c in [DRILLDOWN_PWAVE_1MeV, ARRHENIUS_GAPPED_10MeV, EXCLUDED_GAPPED_EV]:
            assert isinstance(c.label, str)
            assert len(c.label) > 0


class TestFractonDMAssessment:
    def test_assessment_returns_struct(self):
        a = assess_fracton_dm_status()
        assert a.arrhenius_bbn_lower_MeV > 10.0
        assert a.condensate_bbn_lower_MeV == 1.0
        assert a.arrhenius_condensate_ratio > 10.0

    def test_assessment_viable_phases_present(self):
        a = assess_fracton_dm_status()
        assert any("PWave" in p for p in a.viable_phases_at_bbn)
        assert any("Gapless" in p for p in a.viable_phases_at_bbn)

    def test_assessment_swave_excluded(self):
        a = assess_fracton_dm_status()
        assert any("SWave" in p for p in a.excluded_phases_at_bbn)

    def test_assessment_signatures_all_true(self):
        # All phenomenological signatures should verify for the
        # Drilldown preferred scenario
        a = assess_fracton_dm_status()
        for key, value in a.signatures_verified.items():
            assert value is True, f"Signature {key} failed"

    def test_assessment_has_hooks(self):
        a = assess_fracton_dm_status()
        assert len(a.surviving_empirical_hooks) >= 5
        # Each hook should reference a concrete paper, theorem, or constraint
        combined = " ".join(a.surviving_empirical_hooks).lower()
        assert "bullet" in combined
        assert "subdiffusion" in combined or "core" in combined
        assert "singlet" in combined

    def test_assessment_gaps_list_nonempty(self):
        a = assess_fracton_dm_status()
        assert len(a.remaining_open_questions) >= 3
        # Production mechanism must be flagged as top gap (Drilldown §X)
        assert any(
            "production" in g.lower() for g in a.remaining_open_questions
        )

    def test_assessment_z_subdiffusion_is_four(self):
        a = assess_fracton_dm_status()
        assert a.z_subdiffusion == 4

    def test_assessment_sm_singlet_true(self):
        a = assess_fracton_dm_status()
        assert a.sm_singlet_from_lean is True

    def test_assessment_w_dust_zero(self):
        a = assess_fracton_dm_status()
        assert a.w_dust == 0.0


class TestLeanPythonCrossCheck:
    """Values that must match between the Lean module and the Python module.

    Prevents drift between ``FractonDarkMatter.lean`` and
    ``fracton_dm.py``.
    """

    def test_bbn_temperature_matches_lean(self):
        # Lean: T_BBN_MeV = 1/10
        assert T_BBN_MeV == pytest.approx(0.1)

    def test_arrhenius_floor_matches_lean(self):
        # Lean: M_d_bbn_arrhenius_MeV = 10
        assert M_D_ARRHENIUS_BBN_MeV == 10.0

    def test_condensate_floor_matches_lean(self):
        # Lean: mu_bbn_condensate_MeV = 1
        assert MU_CONDENSATE_BBN_MeV == 1.0

    def test_arrhenius_window_upper_matches_lean(self):
        # Lean: arrhenius_window_upper_MeV = 100000
        assert ARRHENIUS_WINDOW_UPPER_MeV == 1e5

    def test_pwave_window_upper_matches_lean(self):
        # Lean: pwave_window_upper_MeV = 10000000
        assert PWAVE_WINDOW_UPPER_MeV == 1e7

    def test_damping_order_matches_lean(self):
        # Lean: fracton_damping_order = damping_power 1 = 4
        assert Z_SUBDIFFUSION == 4

    def test_eos_matches_lean(self):
        # Lean: eos_fracton_dust = 0
        assert EOS_FRACTON_DUST == 0.0

    def test_sigma_eff_matches_lean(self):
        # Lean: sigma_eff_isolated_fracton = 0
        assert SIGMA_EFF_FRACTON_CM2_PER_G == 0.0

    def test_graviton_sign_matches_lean(self):
        # Lean: fracton_graviton_coupling_sign = 1
        assert FRACTON_GRAVITON_COUPLING_SIGN == 1

    def test_sm_singlet_matches_lean(self):
        # Lean: no_fracton_is_ym_compatible for all gauge types
        assert FRACTON_IS_SM_SINGLET is True

    def test_cs_sq_bound_matches_lean(self):
        # Lean: fracton_dipole_cs_sq_bound = 1/2
        assert CS_SQ_DIPOLE_BOUND == 0.5

    def test_pwave_wins_is_viable_at_epoch_lean_match(self):
        # Lean: dilldown_witness_viable, arrhenius_witness_viable,
        #       eV_scale_excluded_at_bbn, swave_always_excluded
        assert FractonDMCandidate(
            FractonDMPhase.PWAVE_CONDENSATE, 1.0, "test"
        ).viable_at(0.1) is True
        assert FractonDMCandidate(
            FractonDMPhase.GAPPED_TOPO, 10.0, "test"
        ).viable_at(0.1) is True
        assert FractonDMCandidate(
            FractonDMPhase.GAPPED_TOPO, 1e-6, "test"
        ).viable_at(0.1) is False
        assert FractonDMCandidate(
            FractonDMPhase.SWAVE_CONDENSATE, 1000.0, "test"
        ).viable_at(0.1) is False


class TestUsageExamples:
    """Documentation-style examples that must stay working."""

    def test_canonical_bbn_sweep(self):
        """Sweeping M_d across decades should hit Arrhenius threshold
        between 1 MeV and 100 MeV (deep research places it at ~10 MeV)."""
        below = arrhenius_survives_bbn(M_d_MeV=1.0)
        mid = arrhenius_survives_bbn(M_d_MeV=12.0)  # above 10.46 floor
        above = arrhenius_survives_bbn(M_d_MeV=100.0)
        assert below is False
        assert mid is True
        assert above is True

    def test_canonical_condensate_sweep(self):
        """μ=T marks the Drilldown condensate boundary."""
        assert not condensate_cold(0.05, 0.1)
        assert condensate_cold(0.11, 0.1)
        assert condensate_cold(10.0, 0.1)

    def test_core_size_sensitivity(self):
        """Deep-research §2.1: M_d/M_f ~ 1e-3 gives smaller core than 1e-1."""
        r_small = fracton_subdiffusion_core_radius_estimate(
            M_d_eV=1e-3, M_fracton_eV=1.0,
            rho_c_MeV4=1e-50, G_Newton_invMeV2=1e-44,
        )
        r_big = fracton_subdiffusion_core_radius_estimate(
            M_d_eV=1e-1, M_fracton_eV=1.0,
            rho_c_MeV4=1e-50, G_Newton_invMeV2=1e-44,
        )
        assert r_big > r_small

    def test_module_exports_match_all(self):
        # __all__ should include all public symbols
        assert "assess_fracton_dm_status" in fdm.__all__
        assert "FractonDMPhase" in fdm.__all__
        assert "DRILLDOWN_PWAVE_1MeV" in fdm.__all__
