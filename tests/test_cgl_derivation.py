"""Tests for the CGL dynamical KMS derivation of the FDR.

Validates the Fourier-space CGL FDR formula:
    K_N(ω,k) = −i·[K_R(ω,k) − K_R(−ω,k)] / (β₀ω)

against known results (Einstein relation, BEC FDR) and checks
the general-order pattern at N=0 through N=4.
"""

import pytest
import sympy as sp

from src.second_order.cgl_derivation import (
    retarded_kernel,
    noise_kernel,
    cgl_fdr,
    extract_odd_kernel,
    extract_even_kernel,
    derive_fdr_fourier,
    verify_einstein_relation,
    verify_first_order_bec,
    verify_second_order_fdr,
)


# ═══════════════════════════════════════════════════════════════════
# Symbols used across tests
# ═══════════════════════════════════════════════════════════════════

omega = sp.Symbol('omega', real=True)
k = sp.Symbol('k', real=True)
beta = sp.Symbol('beta', positive=True)


# ═══════════════════════════════════════════════════════════════════
# Test: Fourier kernel construction
# ═══════════════════════════════════════════════════════════════════

class TestKernelConstruction:
    """Test that retarded_kernel and noise_kernel produce correct Fourier expressions."""

    def test_retarded_kernel_wave_equation(self):
        """ψ_a·(∂_t² - c_s²∂_x²)ψ_r → K_R = -ω² + c_s²k²... wait:
        coefficient of ∂_t² is 1, ∂_x² is -c_s².
        Fourier: 1·(-iω)² + (-c_s²)·(ik)² = -ω² + c_s²k²."""
        c_s = sp.Symbol('c_s', positive=True)
        coeffs = {(2, 0): sp.Integer(1), (0, 2): -c_s**2}
        K_R = retarded_kernel(coeffs, omega, k)
        assert sp.expand(K_R - (-omega**2 + c_s**2 * k**2)) == 0

    def test_retarded_kernel_friction(self):
        """ψ_a·(-γ∂_t)ψ_r → K_R = iγω (odd in ω, imaginary)."""
        gamma = sp.Symbol('gamma', positive=True)
        coeffs = {(1, 0): -gamma}
        K_R = retarded_kernel(coeffs, omega, k)
        assert sp.expand(K_R - sp.I * gamma * omega) == 0

    def test_even_kernel_is_real(self):
        """Even-m retarded kernel should be real for real coefficients."""
        r1, r2 = sp.symbols('r1 r2', real=True)
        coeffs = {(2, 0): r1, (0, 2): r2}
        K_R = retarded_kernel(coeffs, omega, k)
        assert sp.im(K_R) == 0

    def test_odd_kernel_is_imaginary(self):
        """Odd-m retarded kernel should be pure imaginary for real coefficients."""
        c10 = sp.Symbol('c10', real=True)
        coeffs = {(1, 0): c10}
        K_R = retarded_kernel(coeffs, omega, k)
        assert sp.re(K_R) == 0


# ═══════════════════════════════════════════════════════════════════
# Test: CGL FDR formula
# ═══════════════════════════════════════════════════════════════════

class TestCGLFDR:
    """Test the master CGL FDR formula."""

    def test_even_kernel_gives_zero_noise(self):
        """A purely even-ω retarded kernel produces zero noise."""
        r1, r2 = sp.symbols('r1 r2', real=True)
        K_R = -r1 * omega**2 - r2 * k**2
        K_N = cgl_fdr(K_R, omega, beta)
        assert K_N == 0

    def test_einstein_relation(self):
        """The CGL FDR reproduces the Einstein relation σ = γ/β₀."""
        assert verify_einstein_relation()

    def test_bec_first_order(self):
        """The CGL FDR reproduces the first-order BEC FDR."""
        assert verify_first_order_bec()

    def test_second_order_noise_real(self):
        """Second-order noise kernel from odd-ω terms is real."""
        assert verify_second_order_fdr()

    def test_fdr_linear_in_dissipative_coeffs(self):
        """K_N is linear in the dissipative (odd-ω) coefficients."""
        b1 = sp.Symbol('b1')
        b3 = sp.Symbol('b3')
        K_R = sp.I * b1 * omega + sp.I * b3 * omega**3
        K_N = cgl_fdr(K_R, omega, beta)
        # K_N should be linear in b1 and b3
        assert sp.diff(K_N, b1, 2) == 0
        assert sp.diff(K_N, b3, 2) == 0

    def test_fdr_proportional_to_inverse_beta(self):
        """Noise is proportional to temperature (1/β₀)."""
        gamma = sp.Symbol('gamma', positive=True)
        K_R = sp.I * gamma * omega
        K_N = cgl_fdr(K_R, omega, beta)
        # K_N should be proportional to 1/beta
        assert sp.simplify(K_N * beta - 2 * gamma) == 0


# ═══════════════════════════════════════════════════════════════════
# Test: Odd/even kernel decomposition
# ═══════════════════════════════════════════════════════════════════

class TestKernelDecomposition:
    """Test the odd/even decomposition of K_R."""

    def test_decomposition_sums_to_original(self):
        """K_R^{even} + K_R^{odd} = K_R."""
        r1 = sp.Symbol('r1')
        gamma = sp.Symbol('gamma')
        K_R = -r1 * omega**2 + sp.I * gamma * omega
        K_even = extract_even_kernel(K_R, omega)
        K_odd = extract_odd_kernel(K_R, omega)
        assert sp.expand(K_even + K_odd - K_R) == 0

    def test_even_part_is_even(self):
        """K_R^{even}(-ω) = K_R^{even}(ω)."""
        r1, gamma = sp.symbols('r1 gamma')
        K_R = -r1 * omega**2 + sp.I * gamma * omega
        K_even = extract_even_kernel(K_R, omega)
        assert sp.expand(K_even.subs(omega, -omega) - K_even) == 0

    def test_odd_part_is_odd(self):
        """K_R^{odd}(-ω) = -K_R^{odd}(ω)."""
        r1, gamma = sp.symbols('r1 gamma')
        K_R = -r1 * omega**2 + sp.I * gamma * omega
        K_odd = extract_odd_kernel(K_R, omega)
        assert sp.expand(K_odd.subs(omega, -omega) + K_odd) == 0


# ═══════════════════════════════════════════════════════════════════
# Test: General-order FDR pattern
# ═══════════════════════════════════════════════════════════════════

class TestGeneralPattern:
    """Test the general-order FDR pattern at multiple EFT orders."""

    def test_order_0_has_noise(self):
        """Order N=0 (level 1): one dissipative term, one noise bilinear."""
        results = derive_fdr_fourier(0)
        data = results[0]
        assert len(data['dissipative']) == 1  # c_{1,0}
        assert len(data['noise']) == 1  # i_{0,0} = ψ_a²
        assert data['K_N'] != 0

    def test_order_1_no_real_noise(self):
        """Order N=1 (level 2): dissipative c_{1,1} gives imaginary K_N.
        No real noise bilinears at this level."""
        results = derive_fdr_fourier(1)
        data = results[1]
        assert len(data['dissipative']) == 1  # c_{1,1}
        # K_N has factor of I*k → no real noise bilinears extracted
        assert len(data['noise']) == 0

    def test_order_2_has_two_noise(self):
        """Order N=2 (level 3): two dissipative, two noise bilinears."""
        results = derive_fdr_fourier(2)
        data = results[2]
        assert len(data['dissipative']) == 2  # c_{1,2}, c_{3,0}
        assert len(data['noise']) == 2  # i_{0,1}, i_{1,0}

    def test_order_4_has_three_noise(self):
        """Order N=4 (level 5): three dissipative, three noise bilinears."""
        results = derive_fdr_fourier(4)
        data = results[4]
        assert len(data['dissipative']) == 3  # c_{1,4}, c_{3,2}, c_{5,0}
        assert len(data['noise']) == 3  # i_{0,2}, i_{1,1}, i_{2,0}

    def test_conservative_unconstrained(self):
        """Conservative (even-ω) coefficients don't appear in K_N."""
        results = derive_fdr_fourier(2)
        data = results[2]
        K_N = data['K_N']
        # Check that conservative coefficients don't appear
        for _, _, sym in data['conservative']:
            assert sym not in K_N.free_symbols

    def test_noise_count_pattern(self):
        """At even order N=2n, there are n+1 noise bilinears.
        At odd order N=2n+1, there are 0 (K_N is imaginary)."""
        results = derive_fdr_fourier(4)
        # N=0: 1 noise, N=2: 2 noise, N=4: 3 noise
        assert len(results[0]['noise']) == 1
        assert len(results[2]['noise']) == 2
        assert len(results[4]['noise']) == 3
        # N=1, N=3: 0 noise (K_N is imaginary)
        assert len(results[1]['noise']) == 0
        assert len(results[3]['noise']) == 0


# ═══════════════════════════════════════════════════════════════════
# Test: Connection to existing Lean FDR
# ═══════════════════════════════════════════════════════════════════

class TestLeanConnection:
    """Test that the CGL FDR connects correctly to the Lean FirstOrderKMS."""

    def test_cgl_plus_bec_gives_lean_fdr(self):
        """CGL FDR + BEC identification γ₁=-r₂ gives i₁β=-r₂."""
        gamma_1 = sp.Symbol('gamma_1', positive=True)
        r2 = sp.Symbol('r2')

        # CGL gives: i₁ = γ₁/β₀
        i1_cgl = gamma_1 / beta

        # BEC identification: γ₁ = -r₂
        i1_lean = i1_cgl.subs(gamma_1, -r2)

        # Should give i₁ = -r₂/β → i₁β = -r₂
        assert sp.simplify(i1_lean * beta - (-r2)) == 0

    def test_second_order_fdr_structure(self):
        """At order N=2, the CGL FDR produces two noise coefficients
        paired with the two odd-m dissipative terms c_{1,2} and c_{3,0}.

        In the Lean model (with parity breaking), these correspond to
        s₁ (∂_x³) and s₃ (∂_t²∂_x) via a model-specific identification."""
        results = derive_fdr_fourier(2)
        data = results[2]

        # Two dissipative terms at level 3
        diss_mns = [(m, n) for m, n, _ in data['dissipative']]
        assert (1, 2) in diss_mns  # ψ_a·∂_t∂_x²ψ_r
        assert (3, 0) in diss_mns  # ψ_a·∂_t³ψ_r

        # Two conservative terms at level 3
        cons_mns = [(m, n) for m, n, _ in data['conservative']]
        assert (0, 3) in cons_mns  # ψ_a·∂_x³ψ_r (s₁ in Lean)
        assert (2, 1) in cons_mns  # ψ_a·∂_t²∂_x ψ_r (s₃ in Lean)


# ═══════════════════════════════════════════════════════════════════
# Test: Boundary term analysis (open question #3)
# ═══════════════════════════════════════════════════════════════════

class TestBoundaryTerms:
    """Test the IBP boundary correction from position-dependent coefficients."""

    def test_correction_is_order_D(self):
        """The gradient correction is O(D) relative to leading noise."""
        from src.second_order.cgl_derivation import boundary_term_estimate
        est = boundary_term_estimate(D=0.013)
        assert abs(est['relative_ibp_correction'] - 0.013) < 1e-10

    def test_correction_small_for_all_experiments(self):
        """All three experiments have D << 1, so corrections are small."""
        from src.second_order.cgl_derivation import boundary_term_estimate
        for D in [0.0134, 0.0118, 0.0137]:  # Steinhauer, Heidelberg, Trento
            est = boundary_term_estimate(D)
            assert est['relative_ibp_correction'] < 0.02  # < 2%

    def test_correction_vanishes_for_constant_coefficients(self):
        """With constant γ (D→0), the gradient correction vanishes."""
        from src.second_order.cgl_derivation import boundary_term_estimate
        est = boundary_term_estimate(D=0.0)
        assert est['relative_ibp_correction'] == 0.0

    def test_correction_grows_for_abrupt_horizons(self):
        """For D ~ 1 (abrupt horizons), the correction becomes O(1)."""
        from src.second_order.cgl_derivation import boundary_term_estimate
        est = boundary_term_estimate(D=1.0)
        assert est['relative_ibp_correction'] == 1.0

    def test_full_analysis_runs(self):
        """The full boundary analysis produces a non-empty result."""
        from src.second_order.cgl_derivation import boundary_term_analysis
        result = boundary_term_analysis()
        assert "RESOLVED" in result
        assert "Steinhauer" in result
        assert "relaxed_uniqueness_test" in result
