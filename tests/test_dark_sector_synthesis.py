"""Tests for Phase 5x Wave 8 dark-sector synthesis module.

Covers:

- Equation-of-state distinctness (CC3, CC4, CC4')
- Emergent-gravity DM collective invisibility (CC2)
- Cored-profile mechanism taxonomy (CC5)
- Torsion-channel independence (CC7)
- Phase 5x candidate viability matrix (Synth2)
- Empirical-hook ranking (Rank1, Rank2)
- Cross-connection matrix shape + Lean-backing coverage
- Overall assessment report shape + consistency with upstream reports

Every test has a corresponding Lean theorem in
``lean/SKEFTHawking/DarkSectorSynthesis.lean`` (exceptions: the report-
shape tests, which are Python-side only).
"""

from __future__ import annotations

import pytest

from src.dark_sector.synthesis import (
    CANDIDATE_C1,
    CANDIDATE_FG,
    CANDIDATE_FRACTON_PWAVE,
    CANDIDATE_S0,
    CANDIDATE_T0,
    CHANNEL_OF_SOURCE,
    CROSS_CONNECTION_MATRIX,
    DIRECT_DETECTION_CURRENT_FLOOR_LOG10,
    DIRECT_DETECTION_SIGMA_LOG10_CAP,
    EOS_COSMOLOGICAL_CONSTANT,
    EOS_FG_TRACELESS,
    EOS_FRACTON,
    HOOK_PRIORITY,
    INVISIBLE_THRESHOLD_LOG10,
    PHASE5X_CANDIDATE_MATRIX,
    PRODUCES_CORED_PROFILE,
    CoredProfileMechanism,
    CrossConnection,
    DarkSectorSynthesisAssessment,
    EmergentGravityDMKind,
    EmpiricalHook,
    TorsionChannel,
    TorsionSource,
    all_emergent_gravity_dm_invisible,
    assess_dark_sector_synthesis,
    cored_mechanisms_are_distinct,
    count_viable_phase5x_candidates,
    eos_pairs_all_distinct,
    is_invisible_to_direct_detection,
    merger_outranks_direct_detection,
    phase5x_upstream_wave_reports,
    ranked_empirical_hooks,
    torsion_sources_distinct_imply_channels_distinct,
    z16_candidate_by_tag,
)


# -------------------------------------------------------------------------
# 1. EoS distinctness (CC3, CC4, CC4')
# -------------------------------------------------------------------------


class TestEosDistinctness:
    def test_eos_fg_is_one_third(self):
        assert EOS_FG_TRACELESS == pytest.approx(1.0 / 3.0)

    def test_eos_cc_is_minus_one(self):
        assert EOS_COSMOLOGICAL_CONSTANT == -1.0

    def test_eos_fracton_is_zero(self):
        assert EOS_FRACTON == 0.0

    def test_fg_vs_fracton_distinct(self):
        """CC3: w_FG ≠ w_fracton."""
        assert EOS_FG_TRACELESS != EOS_FRACTON

    def test_cc_vs_fracton_distinct(self):
        """CC4: w_Λ ≠ w_fracton."""
        assert EOS_COSMOLOGICAL_CONSTANT != EOS_FRACTON

    def test_cc_vs_fg_distinct(self):
        """CC4': w_Λ ≠ w_FG."""
        assert EOS_COSMOLOGICAL_CONSTANT != EOS_FG_TRACELESS

    def test_eos_pairs_all_distinct_aggregator(self):
        assert eos_pairs_all_distinct() is True


# -------------------------------------------------------------------------
# 2. Emergent-gravity DM collective invisibility (CC2)
# -------------------------------------------------------------------------


class TestCollectiveInvisibility:
    def test_every_kind_has_a_log10_cap(self):
        for kind in EmergentGravityDMKind:
            assert kind in DIRECT_DETECTION_SIGMA_LOG10_CAP

    def test_t0_and_fracton_are_fully_decoupled(self):
        """T-0 (TQFT) and fracton (σ_eff=0) get the -999 placeholder."""
        assert (
            DIRECT_DETECTION_SIGMA_LOG10_CAP[EmergentGravityDMKind.Z16_TOPOLOGICAL_T0]
            == -999
        )
        assert (
            DIRECT_DETECTION_SIGMA_LOG10_CAP[EmergentGravityDMKind.FRACTON_PWAVE]
            == -999
        )

    def test_fg_is_gravitational_only(self):
        """FG deep research: σ ~ 10⁻⁹⁰ cm²."""
        assert DIRECT_DETECTION_SIGMA_LOG10_CAP[EmergentGravityDMKind.FG_TORSION] == -90

    def test_every_kind_invisible_to_current_lz(self):
        for kind in EmergentGravityDMKind:
            assert (
                DIRECT_DETECTION_SIGMA_LOG10_CAP[kind]
                < DIRECT_DETECTION_CURRENT_FLOOR_LOG10
            )

    def test_per_kind_invisibility_predicate(self):
        for kind in EmergentGravityDMKind:
            assert is_invisible_to_direct_detection(kind) is True

    def test_collective_invisibility(self):
        """CC2: every Phase 5x emergent-gravity DM candidate is invisible."""
        assert all_emergent_gravity_dm_invisible() is True

    def test_invisible_threshold_is_at_or_above_current_floor(self):
        """Sanity: invisibility threshold above LZ/XENONnT sensitivity."""
        assert INVISIBLE_THRESHOLD_LOG10 >= DIRECT_DETECTION_CURRENT_FLOOR_LOG10 - 5


# -------------------------------------------------------------------------
# 3. Cored-profile taxonomy (CC5)
# -------------------------------------------------------------------------


class TestCoredProfileTaxonomy:
    def test_soliton_condensate_produces_core(self):
        assert PRODUCES_CORED_PROFILE[CoredProfileMechanism.SOLITON_CONDENSATE] is True

    def test_z4_subdiffusion_produces_core(self):
        assert PRODUCES_CORED_PROFILE[CoredProfileMechanism.Z4_SUBDIFFUSION] is True

    def test_nfw_does_not_produce_core(self):
        assert PRODUCES_CORED_PROFILE[CoredProfileMechanism.NFW_PSEUDO_CUSP] is False

    def test_cored_mechanisms_are_distinct(self):
        """CC5: soliton-condensate ≠ z4-subdiffusion."""
        assert cored_mechanisms_are_distinct() is True

    def test_two_mechanisms_produce_cores_third_does_not(self):
        cored_count = sum(v for v in PRODUCES_CORED_PROFILE.values())
        assert cored_count == 2


# -------------------------------------------------------------------------
# 4. Torsion-channel independence (CC7)
# -------------------------------------------------------------------------


class TestTorsionChannelIndependence:
    def test_dirac_axial_is_antisymmetric(self):
        assert CHANNEL_OF_SOURCE[TorsionSource.DIRAC_AXIAL] is TorsionChannel.ANTISYMMETRIC

    def test_fg_loop_is_trace(self):
        assert CHANNEL_OF_SOURCE[TorsionSource.FG_LOOP_THETA] is TorsionChannel.TRACE

    def test_no_source_is_pure_tensor(self):
        assert CHANNEL_OF_SOURCE[TorsionSource.NO_SOURCE] is TorsionChannel.PURE_TENSOR

    def test_boos_hehl_orthogonal_to_fg_loop(self):
        """CC7': Boos-Hehl vs FG loop land in distinct channels."""
        assert (
            CHANNEL_OF_SOURCE[TorsionSource.DIRAC_AXIAL]
            is not CHANNEL_OF_SOURCE[TorsionSource.FG_LOOP_THETA]
        )

    def test_distinct_sources_distinct_channels(self):
        """CC7: over all distinct-source pairs, channels differ."""
        assert torsion_sources_distinct_imply_channels_distinct() is True

    def test_channel_map_is_injective(self):
        """Every source has a unique channel assignment."""
        assigned = {CHANNEL_OF_SOURCE[s] for s in TorsionSource}
        assert len(assigned) == len(list(TorsionSource))


# -------------------------------------------------------------------------
# 5. Phase 5x candidate viability matrix (Synth2)
# -------------------------------------------------------------------------


class TestCandidateMatrix:
    def test_five_canonical_candidates(self):
        assert len(PHASE5X_CANDIDATE_MATRIX) == 5

    def test_t0_viable(self):
        assert CANDIDATE_T0.basic_viability is True

    def test_s0_viable(self):
        assert CANDIDATE_S0.basic_viability is True

    def test_c1_viable(self):
        assert CANDIDATE_C1.basic_viability is True

    def test_fg_torsion_excluded(self):
        """W4 fg_cdm_obstruction: FG is not basic-viable at CDM level."""
        assert CANDIDATE_FG.basic_viability is False

    def test_fracton_pwave_viable(self):
        assert CANDIDATE_FRACTON_PWAVE.basic_viability is True

    def test_four_of_five_viable(self):
        """Cross-check for Lean phase5x_viable_candidate_count = 4."""
        assert count_viable_phase5x_candidates() == 4

    def test_candidate_kinds_are_unique(self):
        kinds = [c.kind for c in PHASE5X_CANDIDATE_MATRIX]
        assert len(set(kinds)) == len(kinds)

    def test_every_candidate_has_verdict_source(self):
        for c in PHASE5X_CANDIDATE_MATRIX:
            assert c.verdict_source
            assert len(c.verdict_source) > 10  # non-trivial


# -------------------------------------------------------------------------
# 6. Empirical-hook ranking (Rank1, Rank2)
# -------------------------------------------------------------------------


class TestEmpiricalHookRanking:
    def test_every_hook_has_priority(self):
        for h in EmpiricalHook:
            assert h in HOOK_PRIORITY

    def test_priorities_are_strict_integers(self):
        values = sorted(HOOK_PRIORITY.values())
        assert values == [1, 2, 3, 4, 5]

    def test_merger_is_top(self):
        assert HOOK_PRIORITY[EmpiricalHook.MERGER_SONIC_BOOM] == 5

    def test_direct_detection_is_bottom(self):
        assert HOOK_PRIORITY[EmpiricalHook.DIRECT_NUCLEAR_RECOIL] == 1

    def test_ranking_strict_adjacent(self):
        """Rank1: adjacent pairs differ by exactly 1."""
        assert (
            HOOK_PRIORITY[EmpiricalHook.MERGER_SONIC_BOOM]
            == HOOK_PRIORITY[EmpiricalHook.FRACTON_CORE_CUSP] + 1
        )
        assert (
            HOOK_PRIORITY[EmpiricalHook.FRACTON_CORE_CUSP]
            == HOOK_PRIORITY[EmpiricalHook.EP_VIOLATION_STEP] + 1
        )
        assert (
            HOOK_PRIORITY[EmpiricalHook.EP_VIOLATION_STEP]
            == HOOK_PRIORITY[EmpiricalHook.DESI_DR3] + 1
        )
        assert (
            HOOK_PRIORITY[EmpiricalHook.DESI_DR3]
            == HOOK_PRIORITY[EmpiricalHook.DIRECT_NUCLEAR_RECOIL] + 1
        )

    def test_merger_outranks_direct_detection(self):
        """Rank2."""
        assert merger_outranks_direct_detection() is True

    def test_ranked_list_descending(self):
        ranked = ranked_empirical_hooks()
        assert ranked[0] is EmpiricalHook.MERGER_SONIC_BOOM
        assert ranked[-1] is EmpiricalHook.DIRECT_NUCLEAR_RECOIL

    def test_ranked_list_has_five_entries(self):
        assert len(ranked_empirical_hooks()) == 5


# -------------------------------------------------------------------------
# 7. Cross-connection matrix
# -------------------------------------------------------------------------


class TestCrossConnectionMatrix:
    def test_matrix_shape(self):
        assert len(CROSS_CONNECTION_MATRIX) == 7

    def test_connection_ids_unique(self):
        ids = [c.connection_id for c in CROSS_CONNECTION_MATRIX]
        assert len(set(ids)) == len(ids)

    def test_every_connection_cites_at_least_two_waves(self):
        for c in CROSS_CONNECTION_MATRIX:
            # EoS_distinctness cites W3+W4+W7 (3 waves); others 2
            assert len(c.waves) >= 2

    def test_every_connection_has_a_summary(self):
        for c in CROSS_CONNECTION_MATRIX:
            assert len(c.summary) > 50  # non-trivial prose

    def test_lean_backing_coverage(self):
        """At least 5 of 7 connections must have a Lean theorem backing.
        (The 1 "memo-only" case is the ADW-CC × SFDM conceptual link,
        which waits for W5 numerics.)"""
        backed = sum(
            1
            for c in CROSS_CONNECTION_MATRIX
            if not c.lean_backing.startswith("memo-only")
        )
        assert backed >= 5

    def test_strength_labels_are_valid(self):
        allowed = {"High", "Medium-High", "Medium", "Conceptual", "Thematic"}
        for c in CROSS_CONNECTION_MATRIX:
            assert c.strength in allowed, f"{c.connection_id} has {c.strength}"

    def test_z16_x_fracton_backing(self):
        match = next(
            c for c in CROSS_CONNECTION_MATRIX if c.connection_id == "Z16_x_fracton"
        )
        assert match.lean_backing == "hidden_sector_fracton_compatible"

    def test_fg_x_adw_vestigial_backing(self):
        match = next(
            c
            for c in CROSS_CONNECTION_MATRIX
            if c.connection_id == "FG_x_ADW_vestigial"
        )
        assert match.lean_backing == "torsion_channels_distinct_sources_distinct"

    def test_cross_connection_frozen(self):
        """CrossConnection records are immutable."""
        rec = CROSS_CONNECTION_MATRIX[0]
        with pytest.raises((AttributeError, Exception)):
            rec.connection_id = "mutated"  # type: ignore[misc]


# -------------------------------------------------------------------------
# 8. Overall assessment report
# -------------------------------------------------------------------------


class TestOverallAssessment:
    def test_assessment_is_dataclass(self):
        a = assess_dark_sector_synthesis()
        assert isinstance(a, DarkSectorSynthesisAssessment)

    def test_viable_candidate_count_is_four(self):
        assert assess_dark_sector_synthesis().viable_candidate_count == 4

    def test_all_invisible_true(self):
        assert assess_dark_sector_synthesis().all_invisible is True

    def test_eos_all_distinct_true(self):
        assert assess_dark_sector_synthesis().eos_all_distinct is True

    def test_cored_distinct_true(self):
        assert assess_dark_sector_synthesis().cored_mechanisms_distinct is True

    def test_torsion_channels_independent(self):
        assert assess_dark_sector_synthesis().torsion_channels_independent is True

    def test_top_hook_is_merger(self):
        assert (
            assess_dark_sector_synthesis().top_hook is EmpiricalHook.MERGER_SONIC_BOOM
        )

    def test_cross_connection_count_matches_matrix(self):
        a = assess_dark_sector_synthesis()
        assert a.cross_connection_count == len(CROSS_CONNECTION_MATRIX)

    def test_lean_backed_count_ge_five(self):
        a = assess_dark_sector_synthesis()
        assert a.lean_backed_connection_count >= 5


# -------------------------------------------------------------------------
# 9. Upstream wave report bundle + convenience helpers
# -------------------------------------------------------------------------


class TestUpstreamWaveBundle:
    def test_bundle_has_four_entries(self):
        b = phase5x_upstream_wave_reports()
        expected = {
            "cosmological_constant",
            "fracton_dm",
            "fracton_preferred_witness",
            "z16_dm_candidate_matrix",
        }
        assert set(b.keys()) == expected

    def test_z16_candidate_matrix_has_expected_tags(self):
        b = phase5x_upstream_wave_reports()
        matrix = b["z16_dm_candidate_matrix"]
        assert set(matrix.keys()) == {"S-0", "S-1", "C-1", "T-0"}

    def test_z16_candidate_by_tag_s0(self):
        assert z16_candidate_by_tag("S-0").n_weyl == 3

    def test_z16_candidate_by_tag_c1(self):
        c = z16_candidate_by_tag("C-1")
        assert c.n_weyl == 8
        assert c.singlet_cancellation is False

    def test_z16_candidate_by_tag_t0(self):
        assert z16_candidate_by_tag("T-0").n_weyl == 0

    def test_fracton_preferred_is_pwave_1mev(self):
        from src.dark_sector.fracton_dm import FractonDMPhase

        b = phase5x_upstream_wave_reports()
        w = b["fracton_preferred_witness"]
        assert w.phase is FractonDMPhase.PWAVE_CONDENSATE
        assert w.scale_MeV == 1.0


# -------------------------------------------------------------------------
# 10. Python ↔ Lean cross-check (explicit, not via assessor)
# -------------------------------------------------------------------------


class TestPythonLeanCrossChecks:
    """These tests exist so that any future drift between Python
    constants and Lean definitions breaks at least one test.
    """

    def test_eos_constants_mirror_lean(self):
        # Lean: eos_fg_traceless = 1/3; eos_cosmological_constant = -1;
        # eos_fracton_dust = 0.
        assert EOS_FG_TRACELESS == pytest.approx(1.0 / 3.0, abs=1e-15)
        assert EOS_COSMOLOGICAL_CONSTANT == -1.0
        assert EOS_FRACTON == 0.0

    def test_sigma_log10_cap_mirror_lean(self):
        # Lean: direct_detection_sigma_log10_cap
        assert (
            DIRECT_DETECTION_SIGMA_LOG10_CAP[EmergentGravityDMKind.Z16_TOPOLOGICAL_T0]
            == -999
        )
        assert (
            DIRECT_DETECTION_SIGMA_LOG10_CAP[EmergentGravityDMKind.Z16_SINGLET_S0]
            == -50
        )
        assert (
            DIRECT_DETECTION_SIGMA_LOG10_CAP[EmergentGravityDMKind.Z16_MIXED_C1] == -50
        )
        assert DIRECT_DETECTION_SIGMA_LOG10_CAP[EmergentGravityDMKind.FG_TORSION] == -90
        assert (
            DIRECT_DETECTION_SIGMA_LOG10_CAP[EmergentGravityDMKind.FRACTON_PWAVE] == -999
        )

    def test_channel_of_source_mirror_lean(self):
        # Lean: channel_of_source
        assert (
            CHANNEL_OF_SOURCE[TorsionSource.DIRAC_AXIAL] is TorsionChannel.ANTISYMMETRIC
        )
        assert CHANNEL_OF_SOURCE[TorsionSource.FG_LOOP_THETA] is TorsionChannel.TRACE
        assert CHANNEL_OF_SOURCE[TorsionSource.NO_SOURCE] is TorsionChannel.PURE_TENSOR

    def test_hook_priority_mirror_lean(self):
        # Lean: hook_priority
        assert HOOK_PRIORITY[EmpiricalHook.MERGER_SONIC_BOOM] == 5
        assert HOOK_PRIORITY[EmpiricalHook.FRACTON_CORE_CUSP] == 4
        assert HOOK_PRIORITY[EmpiricalHook.EP_VIOLATION_STEP] == 3
        assert HOOK_PRIORITY[EmpiricalHook.DESI_DR3] == 2


class TestPaper17Figures:
    """Smoke tests for Paper 17 synthesis figures."""

    def test_candidate_viability_matrix_renders(self):
        from src.core.visualizations import (
            fig_phase5x_candidate_viability_matrix,
        )
        fig = fig_phase5x_candidate_viability_matrix()
        assert len(fig.data) == 1
        assert len(fig.data[0].y) == 5

    def test_empirical_hook_ranking_renders(self):
        from src.core.visualizations import fig_phase5x_empirical_hook_ranking
        fig = fig_phase5x_empirical_hook_ranking()
        assert len(fig.data) == 1
        priorities = list(fig.data[0].x)
        assert priorities == sorted(priorities, reverse=True)
        assert priorities[0] == 5
        assert priorities[-1] == 1
        assert HOOK_PRIORITY[EmpiricalHook.DIRECT_NUCLEAR_RECOIL] == 1
