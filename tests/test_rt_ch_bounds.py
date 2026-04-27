"""Tests for `src/rt_ch_bounds/` — Phase 6c Wave 5 mirrors.

Covers `rt_comparison.py` and `ch_bound_check.py`. Numerical anchors
verify the Lean theorems' structural content.
"""

from __future__ import annotations

import math

import pytest

from src.rt_ch_bounds import (
    SEN_KAUL_MAJUMDAR_COEFF_GAP,
    central_charge_from_saturation,
    ch_bound_holds,
    ch_log_bound,
    classical_rt_entropy,
    kaul_majumdar_entropy,
    rt_kaul_majumdar_gap,
    saturated_ch_entropy,
    sen_4d_log_coeff,
)


# ---------------------------------------------------------------------------
# §1 — Classical RT entropy (mirror of H_RT structural content)
# ---------------------------------------------------------------------------


class TestClassicalRT:
    """Mirrors `H_RT_Formula_Valid` field + `rt_entropy_pos`."""

    def test_classical_rt_at_canonical(self) -> None:
        # A = 4 G_N ⇒ S = 1
        assert classical_rt_entropy(4.0, 1.0) == pytest.approx(1.0)

    def test_classical_rt_at_double(self) -> None:
        # A = 8 G_N ⇒ S = 2
        assert classical_rt_entropy(8.0, 1.0) == pytest.approx(2.0)

    def test_classical_rt_pos(self) -> None:
        """Mirrors `rt_entropy_pos`."""
        for A, G_N in [(1.0, 1.0), (10.0, 0.5), (100.0, 2.0)]:
            assert classical_rt_entropy(A, G_N) > 0.0

    def test_classical_rt_proportional(self) -> None:
        # Doubling area doubles entropy
        S1 = classical_rt_entropy(4.0, 1.0)
        S2 = classical_rt_entropy(8.0, 1.0)
        assert S2 == pytest.approx(2.0 * S1)

    def test_classical_rt_negative_area_rejected(self) -> None:
        with pytest.raises(ValueError, match="positive"):
            classical_rt_entropy(-1.0, 1.0)

    def test_classical_rt_negative_G_rejected(self) -> None:
        with pytest.raises(ValueError, match="positive"):
            classical_rt_entropy(1.0, -1.0)


# ---------------------------------------------------------------------------
# §2 — Kaul-Majumdar entropy (mirror of W3 microscopic theorem)
# ---------------------------------------------------------------------------


class TestKaulMajumdar:
    """Mirrors `BHEntropyMicroscopic.kaulMajumdarS` use in W5."""

    def test_kaul_majumdar_at_reduced_area_one(self) -> None:
        # A = 4 G_N ⇒ reduced = 1 ⇒ log = 0 ⇒ S = 1 - 0 = 1 (matches RT)
        assert kaul_majumdar_entropy(4.0, 1.0) == pytest.approx(1.0)

    def test_kaul_majumdar_at_reduced_area_two(self) -> None:
        # A = 8 G_N ⇒ reduced = 2 ⇒ S = 2 - (3/2) log 2
        expected = 2.0 - 1.5 * math.log(2.0)
        assert kaul_majumdar_entropy(8.0, 1.0) == pytest.approx(expected)

    def test_kaul_majumdar_with_constant(self) -> None:
        # c0 added to the entropy
        assert kaul_majumdar_entropy(4.0, 1.0, c0=5.0) == pytest.approx(6.0)

    def test_kaul_majumdar_negative_area_rejected(self) -> None:
        with pytest.raises(ValueError):
            kaul_majumdar_entropy(-1.0, 1.0)


# ---------------------------------------------------------------------------
# §3 — RT vs Kaul-Majumdar gap (correctness-push numerical anchor)
# ---------------------------------------------------------------------------


class TestRTKaulMajumdarGap:
    """Mirrors `rt_kaulMajumdar_gap_at_reduced_area_two` +
    `rt_classical_inconsistent_with_kaul_majumdar`."""

    def test_gap_at_reduced_area_two(self) -> None:
        """Mirrors `rt_kaulMajumdar_gap_at_reduced_area_two`."""
        # A = 8 G_N ⇒ gap = (3/2) log 2 ≈ 1.040
        assert rt_kaul_majumdar_gap(8.0, 1.0) == pytest.approx(1.5 * math.log(2.0))

    def test_gap_at_reduced_area_one_vanishes(self) -> None:
        """Mirrors knife-edge case: `rt_eq_kaulMajumdar_iff_trivial_reduced_area`."""
        # A = 4 G_N ⇒ reduced = 1 ⇒ log = 0 ⇒ gap = 0
        assert rt_kaul_majumdar_gap(4.0, 1.0) == pytest.approx(0.0)

    def test_gap_positive_at_reduced_area_above_one(self) -> None:
        """Reduced area > 1 ⇒ positive log ⇒ positive gap."""
        for area, G_N in [(8.0, 1.0), (16.0, 1.0), (40.0, 5.0)]:
            assert rt_kaul_majumdar_gap(area, G_N) > 0.0

    def test_gap_negative_at_reduced_area_below_one(self) -> None:
        """Reduced area < 1 ⇒ negative log ⇒ negative gap."""
        # A = 2 G_N ⇒ reduced = 0.5 ⇒ log < 0 ⇒ gap < 0
        assert rt_kaul_majumdar_gap(2.0, 1.0) < 0.0

    def test_classical_inconsistent_at_canonical_double(self) -> None:
        """Mirrors `kaulMajumdar_not_H_RT`: at A=8 G_N, classical RT ≠ Kaul-Majumdar."""
        rt = classical_rt_entropy(8.0, 1.0)
        km = kaul_majumdar_entropy(8.0, 1.0)
        assert not math.isclose(rt, km)


# ---------------------------------------------------------------------------
# §4 — Sen 4D non-universality witness
# ---------------------------------------------------------------------------


class TestSenNonUniversality:
    """Cross-bridge to W3 `sen_4d_disagrees_with_kaul_majumdar`."""

    def test_sen_log_coeff_value(self) -> None:
        # 212/45 - 3 = 77/45 ≈ 1.711
        assert sen_4d_log_coeff() == pytest.approx(77.0 / 45.0)

    def test_sen_disagrees_with_kaul_majumdar(self) -> None:
        """Sen value ≠ -3/2 (W3 universality witness)."""
        assert not math.isclose(sen_4d_log_coeff(), -1.5)

    def test_sen_kaul_majumdar_gap_value(self) -> None:
        # Gap = 77/45 - (-3/2) = 289/90 ≈ 3.211
        assert SEN_KAUL_MAJUMDAR_COEFF_GAP == pytest.approx(289.0 / 90.0)

    def test_sen_kaul_majumdar_gap_consistent(self) -> None:
        # Computed gap matches formula
        assert SEN_KAUL_MAJUMDAR_COEFF_GAP == pytest.approx(
            sen_4d_log_coeff() - (-1.5)
        )


# ---------------------------------------------------------------------------
# §5 — Casini-Huerta bound (mirror of H_CH structural content)
# ---------------------------------------------------------------------------


class TestCHBound:
    """Mirrors `ch_log_bound_pos_at_log_pos` + `H_CasiniHuerta_Bound_Valid_witness_saturated`."""

    def test_saturated_ch_entropy_at_unit(self) -> None:
        # L = e * UV ⇒ log = 1 ⇒ S = c/3
        assert saturated_ch_entropy(math.e * 1e-6, 3.0, 1e-6) == pytest.approx(1.0)

    def test_ch_log_bound_pos_at_L_above_UV(self) -> None:
        """Mirrors `ch_log_bound_pos_at_log_pos`."""
        for c, L, UV in [(1.0, 1.0, 1e-3), (3.0, 10.0, 1e-2)]:
            assert ch_log_bound(L, c, UV) > 0.0

    def test_ch_bound_holds_at_saturation(self) -> None:
        """Saturated entropy meets the bound with equality."""
        S = saturated_ch_entropy(10.0, 3.0, 1e-3)
        assert ch_bound_holds(S, 10.0, 3.0, 1e-3)

    def test_ch_bound_holds_below_saturation(self) -> None:
        """Sub-saturated entropy still satisfies the bound."""
        S = 0.5 * saturated_ch_entropy(10.0, 3.0, 1e-3)
        assert ch_bound_holds(S, 10.0, 3.0, 1e-3)

    def test_ch_bound_violated_above_saturation(self) -> None:
        """Super-saturated entropy violates the bound."""
        S = 1.5 * saturated_ch_entropy(10.0, 3.0, 1e-3)
        assert not ch_bound_holds(S, 10.0, 3.0, 1e-3)

    def test_ch_negative_central_charge_rejected(self) -> None:
        with pytest.raises(ValueError, match="positive"):
            saturated_ch_entropy(10.0, -1.0, 1e-3)

    def test_ch_zero_uv_rejected(self) -> None:
        with pytest.raises(ValueError, match="UV cutoff"):
            saturated_ch_entropy(10.0, 1.0, 0.0)

    def test_ch_L_below_UV_rejected(self) -> None:
        with pytest.raises(ValueError, match="exceed UV"):
            saturated_ch_entropy(0.5, 1.0, 1.0)


# ---------------------------------------------------------------------------
# §6 — Central charge inversion (CFT cross-check helper)
# ---------------------------------------------------------------------------


class TestCentralChargeRecovery:
    """Helper: invert the saturated CH formula to recover central charge."""

    def test_recover_c_from_saturated(self) -> None:
        c_true = 3.0
        L, UV = 100.0, 1e-3
        S = saturated_ch_entropy(L, c_true, UV)
        recovered = central_charge_from_saturation(S, L, UV)
        assert recovered == pytest.approx(c_true)

    def test_recover_c_for_ising(self) -> None:
        # Ising 2D CFT has c = 1/2
        c_true = 0.5
        L, UV = 50.0, 1e-2
        S = saturated_ch_entropy(L, c_true, UV)
        assert central_charge_from_saturation(S, L, UV) == pytest.approx(c_true)
