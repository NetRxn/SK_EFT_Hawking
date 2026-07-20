"""Tests for unified multi-platform comparison (Phase 5w Wave 8)."""

import numpy as np
import pytest

from src.graphene.platform_comparison import (
    bec_platform_summaries,
    polariton_platform_summaries,
    graphene_platform_summaries,
    all_platform_summaries,
    PlatformSummary,
)


class TestBECPlatforms:
    def test_three_bec_platforms(self):
        assert len(bec_platform_summaries()) == 3

    def test_steinhauer_realized(self):
        summaries = bec_platform_summaries()
        steinhauer = [s for s in summaries if 'Steinhauer' in s.name][0]
        assert steinhauer.horizon_realized is True

    def test_bec_superluminal(self):
        for s in bec_platform_summaries():
            assert s.dispersion_type == 'superluminal'

    def test_bec_1d(self):
        for s in bec_platform_summaries():
            assert s.dimensionality == '1+1D'


class TestPolaritonPlatforms:
    def test_three_polariton_platforms(self):
        # Wave 6v.4 (2026-05-26) added Penn_TMD_MoSe2 as the 4th platform.
        assert len(polariton_platform_summaries()) == 4

    def test_polariton_1d(self):
        for s in polariton_platform_summaries():
            assert s.dimensionality == '1+1D'


class TestGraphenePlatforms:
    def test_three_graphene_platforms(self):
        """Three acoustic platforms (excluding p-n junction)."""
        assert len(graphene_platform_summaries()) == 3

    def test_graphene_subluminal(self):
        for s in graphene_platform_summaries():
            assert s.dispersion_type == 'subluminal'

    def test_graphene_2d(self):
        for s in graphene_platform_summaries():
            assert s.dimensionality == '2+1D'

    def test_dean_realized(self):
        summaries = graphene_platform_summaries()
        dean = [s for s in summaries if 'Dean' in s.name][0]
        assert dean.horizon_realized is True


class TestUnifiedComparison:
    def test_total_nine_platforms(self):
        # Was 9 (3 BEC + 3 polariton + 3 graphene) through Phase 6q;
        # Wave 6v.4 added Penn_TMD_MoSe2 polariton → 10 total.
        assert len(all_platform_summaries()) == 10

    def test_graphene_TH_much_larger_than_bec(self):
        summaries = all_platform_summaries()
        bec = [s for s in summaries if s.platform_type == 'BEC']
        graphene = [s for s in summaries if s.platform_type == 'graphene']
        max_bec_TH = max(s.T_H_K for s in bec)
        min_graphene_TH = min(s.T_H_K for s in graphene)
        assert min_graphene_TH / max_bec_TH > 1e7

    def test_all_have_required_fields(self):
        for s in all_platform_summaries():
            assert isinstance(s, PlatformSummary)
            assert s.T_H_K > 0
            assert s.causal_speed_ms > 0

    def test_realized_horizons(self):
        """At least 2 realized horizons (Steinhauer + Dean)."""
        realized = [s for s in all_platform_summaries() if s.horizon_realized]
        assert len(realized) >= 2


class TestBECCanonicalCorrections:
    """R-09: BEC δ_disp/δ_diss are the canonical pipeline values, not the old
    hard-coded δ_diss = 0.01. Exact cross-check against the canonical evaluator
    (constants → transonic solver → Beliaev; B-05 horizon-calibrated,
    frequency-independent first-order δ_diss)."""

    _NAME_MAP = {'Steinhauer_Rb87': 'Steinhauer',
                 'Heidelberg_K39': 'Heidelberg',
                 'Trento_Na23': 'Trento'}

    def test_bec_corrections_match_canonical_evaluator(self):
        from scripts.gen_d1_hierarchy_table import compute_bec_hierarchy
        hier = compute_bec_hierarchy()
        for s in bec_platform_summaries():
            canon = hier[self._NAME_MAP[s.name]]
            assert s.delta_diss == pytest.approx(canon['delta_diss'], rel=1e-9), s.name
            assert s.delta_disp == pytest.approx(canon['delta_disp'], rel=1e-9), s.name

    def test_delta_diss_not_hardcoded_001(self):
        # The old bug pinned EVERY BEC δ_diss to 0.01; canonical values span
        # 1.41e-5 (Trento) … 1.59e-3 (Heidelberg), all far below 0.01.
        for s in bec_platform_summaries():
            assert s.delta_diss != pytest.approx(0.01)
            assert 1e-5 < s.delta_diss < 2e-3, s.name

    def test_delta_diss_exact_values(self):
        by = {s.name: s for s in bec_platform_summaries()}
        assert by['Steinhauer_Rb87'].delta_diss == pytest.approx(2.3772e-5, rel=1e-3)
        assert by['Heidelberg_K39'].delta_diss == pytest.approx(1.5925e-3, rel=1e-3)
        assert by['Trento_Na23'].delta_diss == pytest.approx(1.4130e-5, rel=1e-3)

    def test_heidelberg_diss_dominates_the_others(self):
        # Physical ordering the flat 0.01 erased: Heidelberg δ_diss ≫ the rest.
        by = {s.name: s for s in bec_platform_summaries()}
        assert by['Heidelberg_K39'].delta_diss > 10 * by['Steinhauer_Rb87'].delta_diss
        assert by['Heidelberg_K39'].delta_diss > 10 * by['Trento_Na23'].delta_diss

    def test_delta_disp_matches_canonical_formula(self):
        from src.core.formulas import dispersive_correction
        for s in bec_platform_summaries():
            assert s.delta_disp == pytest.approx(
                dispersive_correction(s.D_adiabaticity), rel=1e-12), s.name
