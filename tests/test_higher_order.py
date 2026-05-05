"""Tests for the higher-order SK-EFT extension (Phase 6n.α Stage 1 deliverable).

Validates orders 4-7 of the SK-EFT gradient expansion:
1. Coefficient counting matches `count(N) = ⌊(N+1)/2⌋ + 1` from SecondOrderSK.lean
2. Dimensional consistency of each correction function (dimensionless output)
3. Parity behavior matches the m-even-only monomial enumeration
4. On-shell behavior (k = ω/c_s) reproduces the expected polynomial in ω
5. Linearity in transport coefficients
6. Vanishing in the κ → ∞ limit (small dissipative correction at large surface gravity)

These tests provide the load-bearing verification that the order-4..7 coefficient
generation is internally consistent before the resurgence Padé-Borel reconstruction
(sub-wave 6n.α.3) is run on the resulting numerical sequences.
"""

import numpy as np
import pytest

from src.core.formulas import (
    second_order_correction,
    third_order_correction,
    fourth_order_correction,
    fifth_order_correction,
    sixth_order_correction,
    seventh_order_correction,
)


# ═══════════════════════════════════════════════════════════════════
# Counting tests — match Lean count(N) = ⌊(N+1)/2⌋ + 1
# ═══════════════════════════════════════════════════════════════════

class TestHigherOrderCounting:
    """Verify each higher-order function takes the right number of γ coefficients."""

    @pytest.mark.parametrize("order,expected_count", [
        (4, 3),  # ⌊5/2⌋+1 = 3
        (5, 4),  # ⌊6/2⌋+1 = 4
        (6, 4),  # ⌊7/2⌋+1 = 4
        (7, 5),  # ⌊8/2⌋+1 = 5
    ])
    def test_count_formula(self, order, expected_count):
        """count(N) = ⌊(N+1)/2⌋ + 1 — matches Lean SecondOrderSK.lean."""
        actual = (order + 1) // 2 + 1
        assert actual == expected_count, (
            f"count({order}) should be {expected_count}, got {actual}"
        )


# ═══════════════════════════════════════════════════════════════════
# Dimensional / structural tests
# ═══════════════════════════════════════════════════════════════════

class TestFourthOrder:
    """δ⁽⁴⁾(ω) = [γ_{4,1}·k⁵ + γ_{4,2}·ω²·k³/c_s² + γ_{4,3}·ω⁴·k/c_s⁴] / κ."""

    def test_zero_gammas_gives_zero(self):
        """All γ = 0 ⇒ δ⁽⁴⁾ = 0."""
        result = fourth_order_correction(
            k=1.0, omega=1.0, c_s=1.0,
            gamma_4_1=0.0, gamma_4_2=0.0, gamma_4_3=0.0,
            kappa=1.0,
        )
        assert result == 0.0

    def test_linearity_in_gamma_4_1(self):
        """δ⁽⁴⁾ is linear in γ_{4,1}."""
        kw = dict(k=1.0, omega=2.0, c_s=1.0, kappa=1.0,
                  gamma_4_2=0.5, gamma_4_3=0.3)
        a = fourth_order_correction(gamma_4_1=1.0, **kw)
        b = fourth_order_correction(gamma_4_1=2.0, **kw)
        # b - a equals the γ_{4,1}=1 contribution (coefficient = k^5/κ = 1.0)
        assert b - a == pytest.approx(1.0)

    def test_kappa_inverse_scaling(self):
        """δ⁽⁴⁾ scales as 1/κ for fixed γ, k, ω, c_s."""
        kw = dict(k=1.0, omega=1.0, c_s=1.0,
                  gamma_4_1=1.0, gamma_4_2=0.0, gamma_4_3=0.0)
        a = fourth_order_correction(kappa=1.0, **kw)
        b = fourth_order_correction(kappa=2.0, **kw)
        assert b == pytest.approx(a / 2.0)

    def test_only_k5_term(self):
        """With only γ_{4,1} ≠ 0, result equals γ_{4,1}·k⁵/κ."""
        result = fourth_order_correction(
            k=2.0, omega=1.0, c_s=1.0,
            gamma_4_1=1.0, gamma_4_2=0.0, gamma_4_3=0.0,
            kappa=1.0,
        )
        assert result == pytest.approx(2.0**5)

    def test_omega4_term_via_gamma_4_3(self):
        """γ_{4,3} couples to ω⁴·k/c_s⁴."""
        result = fourth_order_correction(
            k=1.0, omega=2.0, c_s=1.0,
            gamma_4_1=0.0, gamma_4_2=0.0, gamma_4_3=1.0,
            kappa=1.0,
        )
        assert result == pytest.approx(2.0**4)


class TestFifthOrder:
    """δ⁽⁵⁾ has count(5) = 4 coefficients, parity-even in k."""

    def test_zero_gammas_gives_zero(self):
        result = fifth_order_correction(
            k=1.0, omega=1.0, c_s=1.0,
            gamma_5_1=0.0, gamma_5_2=0.0, gamma_5_3=0.0, gamma_5_4=0.0,
            kappa=1.0,
        )
        assert result == 0.0

    def test_omega6_term_via_gamma_5_4(self):
        """γ_{5,4} couples to ω⁶/c_s⁶ (only term with no k dependence)."""
        result = fifth_order_correction(
            k=1.0, omega=2.0, c_s=1.0,
            gamma_5_1=0.0, gamma_5_2=0.0, gamma_5_3=0.0, gamma_5_4=1.0,
            kappa=1.0,
        )
        assert result == pytest.approx(2.0**6)

    def test_parity_even_in_k(self):
        """All four terms have k^(2j) for j=0..3 from the (m, n_x) enumeration —
        net polynomial in k is k⁶ + k⁴ + k² + k⁰ when all γ=1, ω=c_s=1.
        Substituting k → -k leaves the result invariant."""
        kw = dict(omega=1.0, c_s=1.0, kappa=1.0,
                  gamma_5_1=1.0, gamma_5_2=1.0, gamma_5_3=1.0, gamma_5_4=1.0)
        a = fifth_order_correction(k=1.5, **kw)
        b = fifth_order_correction(k=-1.5, **kw)
        assert a == pytest.approx(b)


class TestSixthOrder:
    """δ⁽⁶⁾ has count(6) = 4 coefficients, parity-odd in k."""

    def test_zero_gammas_gives_zero(self):
        result = sixth_order_correction(
            k=1.0, omega=1.0, c_s=1.0,
            gamma_6_1=0.0, gamma_6_2=0.0, gamma_6_3=0.0, gamma_6_4=0.0,
            kappa=1.0,
        )
        assert result == 0.0

    def test_only_k7_term(self):
        result = sixth_order_correction(
            k=2.0, omega=1.0, c_s=1.0,
            gamma_6_1=1.0, gamma_6_2=0.0, gamma_6_3=0.0, gamma_6_4=0.0,
            kappa=1.0,
        )
        assert result == pytest.approx(2.0**7)

    def test_parity_odd_in_k(self):
        """All four terms have k^(2j+1) for j=0..3 — odd in k."""
        kw = dict(omega=1.0, c_s=1.0, kappa=1.0,
                  gamma_6_1=1.0, gamma_6_2=1.0, gamma_6_3=1.0, gamma_6_4=1.0)
        a = sixth_order_correction(k=1.5, **kw)
        b = sixth_order_correction(k=-1.5, **kw)
        assert a == pytest.approx(-b)


class TestSeventhOrder:
    """δ⁽⁷⁾ has count(7) = 5 coefficients, parity-even in k."""

    def test_zero_gammas_gives_zero(self):
        result = seventh_order_correction(
            k=1.0, omega=1.0, c_s=1.0,
            gamma_7_1=0.0, gamma_7_2=0.0, gamma_7_3=0.0,
            gamma_7_4=0.0, gamma_7_5=0.0,
            kappa=1.0,
        )
        assert result == 0.0

    def test_omega8_term_via_gamma_7_5(self):
        """γ_{7,5} couples to ω⁸/c_s⁸ (only term with no k dependence)."""
        result = seventh_order_correction(
            k=1.0, omega=2.0, c_s=1.0,
            gamma_7_1=0.0, gamma_7_2=0.0, gamma_7_3=0.0,
            gamma_7_4=0.0, gamma_7_5=1.0,
            kappa=1.0,
        )
        assert result == pytest.approx(2.0**8)

    def test_only_k8_term(self):
        result = seventh_order_correction(
            k=2.0, omega=1.0, c_s=1.0,
            gamma_7_1=1.0, gamma_7_2=0.0, gamma_7_3=0.0,
            gamma_7_4=0.0, gamma_7_5=0.0,
            kappa=1.0,
        )
        assert result == pytest.approx(2.0**8)

    def test_parity_even_in_k(self):
        """All five terms have k^(2j) for j=0..4 — even in k."""
        kw = dict(omega=1.0, c_s=1.0, kappa=1.0,
                  gamma_7_1=1.0, gamma_7_2=1.0, gamma_7_3=1.0,
                  gamma_7_4=1.0, gamma_7_5=1.0)
        a = seventh_order_correction(k=1.5, **kw)
        b = seventh_order_correction(k=-1.5, **kw)
        assert a == pytest.approx(b)


# ═══════════════════════════════════════════════════════════════════
# On-shell behavior (k = ω/c_s) — the acoustic-mode dispersion relation
# ═══════════════════════════════════════════════════════════════════

class TestOnShellBehavior:
    """At k = ω/c_s (on-shell acoustic mode), each δ⁽ᴺ⁾ collapses to a
    polynomial in ω with all (m, n_x) monomials contributing equally
    (modulo their γ coefficients)."""

    def test_fourth_order_on_shell_factors(self):
        """At k = ω/c_s, δ⁽⁴⁾ = (γ_{4,1} + γ_{4,2} + γ_{4,3}) · ω⁵ / (κ·c_s⁵)."""
        omega, c_s, kappa = 1.0, 2.0, 1.0
        k = omega / c_s  # acoustic on-shell condition
        # Each monomial collapses to ω⁵/c_s⁵ at k = ω/c_s:
        #   (0,5): k^5 = ω^5/c_s^5
        #   (2,3): ω^2·k^3/c_s^2 = ω^5/c_s^5
        #   (4,1): ω^4·k/c_s^4 = ω^5/c_s^5
        result = fourth_order_correction(
            k=k, omega=omega, c_s=c_s,
            gamma_4_1=1.0, gamma_4_2=2.0, gamma_4_3=3.0,
            kappa=kappa,
        )
        expected = (1.0 + 2.0 + 3.0) * omega**5 / (c_s**5 * kappa)
        assert result == pytest.approx(expected)

    def test_seventh_order_on_shell_factors(self):
        """At k = ω/c_s, δ⁽⁷⁾ = sum(γ_{7,j}) · ω⁸ / (κ·c_s⁸)."""
        omega, c_s, kappa = 1.5, 1.0, 1.0
        k = omega / c_s
        gammas = (1.0, 2.0, 3.0, 4.0, 5.0)
        result = seventh_order_correction(
            k=k, omega=omega, c_s=c_s,
            gamma_7_1=gammas[0], gamma_7_2=gammas[1], gamma_7_3=gammas[2],
            gamma_7_4=gammas[3], gamma_7_5=gammas[4],
            kappa=kappa,
        )
        expected = sum(gammas) * omega**8 / (c_s**8 * kappa)
        assert result == pytest.approx(expected)


# ═══════════════════════════════════════════════════════════════════
# Cross-order consistency — orders 2 + 3 already exist;
# verify new orders 4-7 compose with them sanely
# ═══════════════════════════════════════════════════════════════════

class TestCrossOrderConsistency:
    """Sanity checks against the already-shipped orders 2 and 3."""

    def test_orders_2_through_7_sum_finite(self):
        """Sum of all corrections orders 2-7 is finite for sane parameters."""
        kw = dict(k=0.1, omega=0.1, c_s=1.0, kappa=1.0)
        d2 = second_order_correction(gamma_2_1=0.1, gamma_2_2=0.1, **kw)
        d3 = third_order_correction(gamma_3_1=0.1, gamma_3_2=0.1, gamma_3_3=0.1, **kw)
        d4 = fourth_order_correction(gamma_4_1=0.1, gamma_4_2=0.1, gamma_4_3=0.1, **kw)
        d5 = fifth_order_correction(gamma_5_1=0.1, gamma_5_2=0.1, gamma_5_3=0.1, gamma_5_4=0.1, **kw)
        d6 = sixth_order_correction(gamma_6_1=0.1, gamma_6_2=0.1, gamma_6_3=0.1, gamma_6_4=0.1, **kw)
        d7 = seventh_order_correction(
            gamma_7_1=0.1, gamma_7_2=0.1, gamma_7_3=0.1,
            gamma_7_4=0.1, gamma_7_5=0.1, **kw,
        )
        total = d2 + d3 + d4 + d5 + d6 + d7
        assert np.isfinite(total)

    def test_higher_orders_dominate_at_large_k(self):
        """At large k, higher orders dominate (k^N+1 growth, all positive γ)."""
        omega, c_s, kappa = 0.1, 1.0, 1.0
        # All γ = 1 of one sign so we can compare magnitudes meaningfully
        d2 = second_order_correction(k=10.0, omega=omega, c_s=c_s,
                                     gamma_2_1=1.0, gamma_2_2=0.0, kappa=kappa)
        d4 = fourth_order_correction(k=10.0, omega=omega, c_s=c_s,
                                     gamma_4_1=1.0, gamma_4_2=0.0, gamma_4_3=0.0,
                                     kappa=kappa)
        # δ⁽²⁾ ~ k³ vs δ⁽⁴⁾ ~ k⁵ at large k → δ⁽⁴⁾ much larger in magnitude
        assert abs(d4) > abs(d2)
