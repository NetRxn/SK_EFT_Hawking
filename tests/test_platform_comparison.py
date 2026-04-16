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
        assert len(polariton_platform_summaries()) == 3

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
        assert len(all_platform_summaries()) == 9

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
