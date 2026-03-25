"""Tests for the third-order SK-EFT extension (Phase 3, Item 1C).

Validates:
1. Transport coefficient counting at third order (matches Lean proofs)
2. Parity alternation theorem (systematic even/odd structure)
3. Third-order coefficient data structures and action constructors
4. Third-order correction formulas (frequency dependence, on-shell behavior)
5. Extended damping rate with all three orders
6. Consistency across enumeration, coefficients, and formulas modules
"""

import numpy as np
import pytest
from src.second_order.enumeration import (
    analyze_order,
    DerivIndex,
    parity_alternation,
    third_order_analysis,
    fdr_relations,
    count_imaginary_monomials,
)
from src.second_order.coefficients import (
    FirstOrderCoeffs,
    SecondOrderCoeffs,
    ThirdOrderCoeffs,
    FullCoeffs,
    FullCoeffsThrough3,
    third_order_action_re,
    hawking_correction_third_order,
)
from src.core.formulas import (
    count_coefficients,
    enumerate_monomials,
    damping_rate,
    third_order_correction,
)


# ═══════════════════════════════════════════════════════════════════
# Counting tests (match Lean proofs)
# ═══════════════════════════════════════════════════════════════════

class TestThirdOrderCounting:
    """Verify counting at third order matches Lean thirdOrder_count."""

    def test_count_3_equals_3(self):
        """count(3) = 3 — Lean: thirdOrder_count (Aristotle 3eedcabb)."""
        r = analyze_order(3, verbose=False)
        assert r.n_transport_no_parity == 3

    def test_count_3_formula(self):
        """count(3) = floor((3+1)/2) + 1 = 3."""
        assert count_coefficients(3) == 3

    def test_cumulative_through_3(self):
        """2 + 2 + 3 = 7 — Lean: cumulative_count_through_3."""
        cumulative = sum(count_coefficients(N) for N in range(1, 4))
        assert cumulative == 7

    def test_third_order_deriv_level(self):
        """Third order has derivative level L = 4."""
        r = analyze_order(3, verbose=False)
        assert r.deriv_level == 4

    def test_third_order_all_monomials(self):
        """At L=4, there are 5 candidate monomials (m+n=4)."""
        r = analyze_order(3, verbose=False)
        assert len(r.all_real_monomials) == 5

    def test_third_order_surviving_monomials(self):
        """After T-reversal, 3 survive: (0,4), (2,2), (4,0)."""
        r = analyze_order(3, verbose=False)
        expected = [DerivIndex(0, 4), DerivIndex(2, 2), DerivIndex(4, 0)]
        assert r.t_reversal_surviving == expected

    def test_killed_monomials(self):
        """T-reversal kills (1,3) and (3,1) — odd m."""
        r = analyze_order(3, verbose=False)
        killed = [d for d in r.all_real_monomials if d not in r.t_reversal_surviving]
        assert len(killed) == 2
        assert DerivIndex(1, 3) in killed
        assert DerivIndex(3, 1) in killed

    def test_enumerate_monomials_order_3(self):
        """enumerate_monomials(3) returns the three surviving pairs."""
        pairs = enumerate_monomials(3)
        assert pairs == [(0, 4), (2, 2), (4, 0)]


# ═══════════════════════════════════════════════════════════════════
# Parity alternation theorem
# ═══════════════════════════════════════════════════════════════════

class TestParityAlternation:
    """Test the parity alternation structural result."""

    def test_odd_N_parity_preserving(self):
        """At odd N, all monomials are parity-preserving."""
        for N in [1, 3, 5, 7]:
            pa = parity_alternation(N)
            assert not pa['requires_parity_breaking'], (
                f"Odd N={N} should NOT require parity breaking")
            assert pa['count_no_parity'] == pa['count_with_parity'], (
                f"At odd N={N}, parity count should equal no-parity count")

    def test_even_N_requires_parity_breaking(self):
        """At even N, all monomials require broken parity."""
        for N in [2, 4, 6, 8]:
            pa = parity_alternation(N)
            assert pa['requires_parity_breaking'], (
                f"Even N={N} SHOULD require parity breaking")
            assert pa['count_with_parity'] == 0, (
                f"At even N={N}, parity count should be 0")

    def test_third_order_parity_preserving(self):
        """All three third-order monomials have even n."""
        r = analyze_order(3, verbose=False)
        for d in r.t_reversal_surviving:
            assert d.n_x % 2 == 0, (
                f"Third-order monomial {d} should have even n_x")

    def test_second_order_parity_breaking(self):
        """All second-order monomials have odd n (contrast with third)."""
        r = analyze_order(2, verbose=False)
        for d in r.t_reversal_surviving:
            assert d.n_x % 2 == 1, (
                f"Second-order monomial {d} should have odd n_x")

    def test_alternation_pattern_through_8(self):
        """Verify the alternation pattern for N=1..8."""
        for N in range(1, 9):
            pa = parity_alternation(N)
            r = analyze_order(N, verbose=False)
            if N % 2 == 1:  # odd N
                assert r.n_transport_with_parity == r.n_transport_no_parity
            else:  # even N
                assert r.n_transport_with_parity == 0

    def test_parity_alternation_monomials_field(self):
        """parity_alternation returns the correct monomials."""
        pa = parity_alternation(3)
        assert len(pa['monomials']) == 3
        assert pa['all_monomials_parity_type'] == 'even_n'


# ═══════════════════════════════════════════════════════════════════
# Third-order coefficient data structures
# ═══════════════════════════════════════════════════════════════════

class TestThirdOrderCoeffs:
    """Test ThirdOrderCoeffs and FullCoeffsThrough3 data structures."""

    def test_coeffs_construction(self):
        """ThirdOrderCoeffs can be constructed with three parameters."""
        c = ThirdOrderCoeffs(gamma_3_1=0.001, gamma_3_2=0.002, gamma_3_3=0.003)
        assert c.gamma_3_1 == 0.001
        assert c.gamma_3_2 == 0.002
        assert c.gamma_3_3 == 0.003

    def test_full_coeffs_through_3(self):
        """FullCoeffsThrough3 combines all three orders."""
        c = FullCoeffsThrough3(
            first=FirstOrderCoeffs(0.01, 0.01),
            second=SecondOrderCoeffs(0.001, -0.001),
            third=ThirdOrderCoeffs(0.0001, 0.0002, 0.0001),
        )
        assert c.n_total == 7
        assert c.n_parity_preserving == 5

    def test_n_total_matches_cumulative_count(self):
        """n_total = 7 matches cumulative_count_through_3 Lean theorem."""
        c = FullCoeffsThrough3(
            first=FirstOrderCoeffs(0.01, 0.01),
            second=SecondOrderCoeffs(0.001, -0.001),
            third=ThirdOrderCoeffs(0.0, 0.0, 0.0),
        )
        lean_cumulative = sum(count_coefficients(N) for N in range(1, 4))
        assert c.n_total == lean_cumulative


# ═══════════════════════════════════════════════════════════════════
# Third-order action
# ═══════════════════════════════════════════════════════════════════

class TestThirdOrderAction:
    """Test the third-order SK action constructor."""

    def test_action_vanishes_without_psi_a(self):
        """L_re^(3) = 0 when psi_a = 0 (normalization axiom)."""
        result = third_order_action_re(
            gamma_3_1=1.0, gamma_3_2=1.0, gamma_3_3=1.0,
            psi_a=0.0, dxxxx_psi_r=1.0, dttxx_psi_r=1.0, dtttt_psi_r=1.0)
        assert result == 0.0

    def test_action_linearity_in_coefficients(self):
        """Action is linear in each γ_{3,i}."""
        psi_a, dxxxx, dttxx, dtttt = 1.0, 1.0, 1.0, 1.0

        # Only gamma_3_1
        r1 = third_order_action_re(2.0, 0.0, 0.0, psi_a, dxxxx, dttxx, dtttt)
        r1_half = third_order_action_re(1.0, 0.0, 0.0, psi_a, dxxxx, dttxx, dtttt)
        assert abs(r1 - 2 * r1_half) < 1e-15

    def test_action_bilinear_structure(self):
        """Action is bilinear: ψ_a · (derivative of ψ_r)."""
        # Doubling psi_a doubles the action
        r1 = third_order_action_re(1.0, 0.0, 0.0, 1.0, 1.0, 0.0, 0.0)
        r2 = third_order_action_re(1.0, 0.0, 0.0, 2.0, 1.0, 0.0, 0.0)
        assert abs(r2 - 2 * r1) < 1e-15


# ═══════════════════════════════════════════════════════════════════
# Third-order correction formulas
# ═══════════════════════════════════════════════════════════════════

class TestThirdOrderCorrections:
    """Test frequency-dependent third-order correction δ^(3)(ω)."""

    def _make_coeffs(self, g31=0.001, g32=0.001, g33=0.001):
        return FullCoeffsThrough3(
            first=FirstOrderCoeffs(0.01, 0.01),
            second=SecondOrderCoeffs(0.001, -0.001),
            third=ThirdOrderCoeffs(g31, g32, g33),
        )

    def test_correction_vanishes_without_third_order(self):
        """δ^(3)(ω) = 0 when all γ_{3,i} = 0."""
        coeffs = self._make_coeffs(0.0, 0.0, 0.0)
        delta = hawking_correction_third_order(
            omega=0.5, coeffs=coeffs, kappa=1.0, c_s=1.0)
        assert delta == 0.0

    def test_correction_frequency_dependent(self):
        """Third-order correction should grow with ω (∝ ω⁴)."""
        coeffs = self._make_coeffs()
        d_low = hawking_correction_third_order(
            omega=0.1, coeffs=coeffs, kappa=1.0, c_s=1.0)
        d_high = hawking_correction_third_order(
            omega=1.0, coeffs=coeffs, kappa=1.0, c_s=1.0)
        assert abs(d_high) > abs(d_low)

    def test_correction_even_in_frequency(self):
        """Third-order correction is EVEN in ω (unlike odd ω³ at second order).

        This is because all third-order monomials have even derivative counts,
        so on-shell (k = ω/c_s), the damping rate terms are:
        k⁴ ∝ ω⁴, ω²k² ∝ ω⁴, ω⁴ ∝ ω⁴ — all even powers.
        """
        coeffs = self._make_coeffs()
        d_pos = hawking_correction_third_order(
            omega=0.5, coeffs=coeffs, kappa=1.0, c_s=1.0)
        d_neg = hawking_correction_third_order(
            omega=-0.5, coeffs=coeffs, kappa=1.0, c_s=1.0)
        assert abs(d_pos - d_neg) < 1e-15, (
            "Third-order correction should be even in ω")

    def test_omega_fourth_scaling(self):
        """On-shell, δ^(3) ∝ ω⁴."""
        coeffs = self._make_coeffs(g31=0.001, g32=0.0, g33=0.0)
        # With only gamma_3_1, on-shell: k⁴ = (ω/c_s)⁴
        d1 = hawking_correction_third_order(
            omega=1.0, coeffs=coeffs, kappa=1.0, c_s=1.0)
        d2 = hawking_correction_third_order(
            omega=2.0, coeffs=coeffs, kappa=1.0, c_s=1.0)
        # Ratio should be 2⁴ = 16
        assert abs(d2 / d1 - 16.0) < 1e-10

    def test_array_input(self):
        """Correction works with numpy array input."""
        coeffs = self._make_coeffs()
        omega = np.linspace(0.1, 1.0, 10)
        delta = hawking_correction_third_order(
            omega=omega, coeffs=coeffs, kappa=1.0, c_s=1.0)
        assert delta.shape == (10,)
        # Should be monotonically increasing for positive coefficients
        assert np.all(np.diff(delta) > 0)


# ═══════════════════════════════════════════════════════════════════
# Extended damping rate
# ═══════════════════════════════════════════════════════════════════

class TestExtendedDampingRate:
    """Test damping_rate with third-order terms."""

    def test_backward_compatible(self):
        """damping_rate without third-order args matches first+second only."""
        k, omega, c_s = 1.0, 1.0, 1.0
        g1, g2, g21, g22 = 0.01, 0.01, 0.001, -0.001

        rate_old = g1 * k**2 + g2 * omega**2 / c_s**2 + g21 * k**3 + g22 * omega**2 * k / c_s**2
        rate_new = damping_rate(k, omega, c_s, g1, g2, g21, g22)
        assert abs(rate_old - rate_new) < 1e-15

    def test_third_order_additive(self):
        """Third-order terms add to the damping rate."""
        k, omega, c_s = 1.0, 1.0, 1.0
        rate_without = damping_rate(k, omega, c_s, 0.01, 0.01)
        rate_with = damping_rate(k, omega, c_s, 0.01, 0.01,
                                 gamma_3_1=0.001, gamma_3_2=0.001, gamma_3_3=0.001)
        assert rate_with > rate_without

    def test_damping_rate_zero_iff_all_zero(self):
        """Γ = 0 for all (k,ω) iff all γᵢ = 0.

        Lean: dampingRate_eq_zero_iff (extended to third order).
        """
        # All zero → rate is zero for any (k, ω)
        for k, omega in [(1.0, 0.5), (2.0, 1.0), (0.1, 3.0)]:
            assert damping_rate(k, omega, 1.0, 0, 0, 0, 0, 0, 0, 0) == 0.0

    def test_third_order_correction_formula(self):
        """third_order_correction in formulas.py matches coefficients.py."""
        k, omega, c_s, kappa = 1.0, 0.5, 1.0, 1.0
        g31, g32, g33 = 0.001, 0.002, 0.001

        from_formulas = third_order_correction(k, omega, c_s, g31, g32, g33, kappa)
        expected = (g31 * k**4 + g32 * omega**2 * k**2 / c_s**2 +
                    g33 * omega**4 / c_s**4) / kappa
        assert abs(from_formulas - expected) < 1e-15


# ═══════════════════════════════════════════════════════════════════
# FDR relations at third order
# ═══════════════════════════════════════════════════════════════════

class TestThirdOrderFDR:
    """Test FDR structure at third order."""

    def test_fdr_relations_count(self):
        """There should be 3 FDR relations at order 3 (one per real coefficient)."""
        relations = fdr_relations(3)
        assert len(relations) == 3

    def test_imaginary_sector_structure(self):
        """Count imaginary monomials at third order."""
        im3 = count_imaginary_monomials(3)
        # The imaginary sector has well-defined surviving pairs
        assert im3['n_surviving'] > 0
        # All should be determined by FDR from the 3 real coefficients
        assert im3['n_surviving'] >= 3


# ═══════════════════════════════════════════════════════════════════
# Cross-module consistency
# ═══════════════════════════════════════════════════════════════════

class TestCrossModuleConsistency:
    """Verify consistency between enumeration, coefficients, and formulas."""

    def test_enumeration_matches_coefficients_count(self):
        """ThirdOrderCoeffs has 3 fields matching count(3) = 3."""
        r = analyze_order(3, verbose=False)
        # ThirdOrderCoeffs has exactly 3 fields
        c = ThirdOrderCoeffs(0.0, 0.0, 0.0)
        n_fields = len([f for f in c.__dataclass_fields__])
        assert n_fields == r.n_transport_no_parity

    def test_formulas_enumerate_matches(self):
        """enumerate_monomials in formulas.py matches enumeration.py."""
        from_formulas = enumerate_monomials(3)
        r = analyze_order(3, verbose=False)
        from_enum = [(d.n_t, d.n_x) for d in r.t_reversal_surviving]
        assert from_formulas == from_enum

    def test_damping_rate_on_shell_consistency(self):
        """On-shell (k = ω/c_s), damping rate matches third_order_correction × κ."""
        omega, c_s, kappa = 0.5, 1.0, 1.0
        k = omega / c_s
        g31, g32, g33 = 0.001, 0.002, 0.001

        # Third-order contribution to damping rate
        gamma_3_contrib = damping_rate(k, omega, c_s, 0, 0, 0, 0, g31, g32, g33)
        # Third-order correction × kappa
        delta_3 = third_order_correction(k, omega, c_s, g31, g32, g33, kappa)

        assert abs(gamma_3_contrib - delta_3 * kappa) < 1e-15

    def test_third_order_analysis_runs(self):
        """third_order_analysis() executes without error."""
        r = third_order_analysis(verbose=False)
        assert r.n_transport_no_parity == 3
        assert r.n_transport_with_parity == 3  # All parity-preserving at odd N

    def test_bogoliubov_dispersion_connection(self):
        """The γ_{3,1}·k⁴ term has the same structure as Bogoliubov dispersion.

        In a BEC, the dispersion relation is ω² = c_s²·k² + (ℏk²/2m)².
        The quartic correction is ℏ²k⁴/(4m²). The EFT coefficient γ_{3,1}
        parametrizes the same k⁴ structure in the damping channel, providing
        a natural UV matching point.
        """
        # Just verify the structure: damping rate with only γ_{3,1} ∝ k⁴
        k_vals = np.array([1.0, 2.0, 3.0])
        rates = np.array([
            damping_rate(k, 0.0, 1.0, 0, 0, 0, 0, 1.0, 0, 0) for k in k_vals
        ])
        # Ratios should be k⁴: 1, 16, 81
        assert abs(rates[1] / rates[0] - 16.0) < 1e-10
        assert abs(rates[2] / rates[0] - 81.0) < 1e-10
