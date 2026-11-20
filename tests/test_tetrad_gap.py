"""Tests for the tetrad gap equation formulas (Phase 5d Wave 1).

Validates:
1. Gap integral properties: positivity, monotonicity, limits
2. Critical coupling: shared V_eff threshold coefficient, correct scaling
3. Gap operator: fixed-point structure, trivial/nontrivial solutions
4. Shared threshold coefficient only; separate nonzero model roots
"""

import numpy as np
import pytest

from src.core.formulas import (
    adw_critical_coupling,
    tetrad_critical_coupling_integral,
    tetrad_density_of_states,
    tetrad_gap_integral,
    tetrad_gap_operator,
    tetrad_gap_solution,
)




def _positive_kernel_B_reference(mp, z):
    """Independent positive kernel, scaled to O(1) when z>=1.

    z*B(z)=int_0^1 u/(1+u/z)du exactly. Quadrature working precision
    is not an accurate-relative-digit certificate; refinement is tested below.
    """
    if z >= 1:
        return mp.quad(lambda u: u / (1 + u / z), [0, 1]) / z
    return mp.quad(lambda u: u / (u + z), [0, z, 1])


def _positive_kernel_reference_gap(G, Lambda, N_f):
    """Independent highprecision positive-kernel inversion; no production calls."""
    import mpmath as mp
    with mp.workdps(90):
        cutoff, species, coupling = map(lambda x: mp.mpf(str(x)), (Lambda, N_f, G))
        r = coupling * species * cutoff**2 / (8 * mp.pi**2)
        assert r > 1
        lo, hi = mp.mpf(0), r / 2
        for _ in range(120):
            z = (lo + hi) / 2
            b = _positive_kernel_B_reference(mp, z)
            if r * b > 1:
                lo = z
            else:
                hi = z
        return float(cutoff * mp.sqrt((lo + hi) / 2))


# ══════════════════════════════════════════════════════
# Gap integral properties
# ══════════════════════════════════════════════════════


class TestGapIntegral:
    """Tests for I(Δ) = ∫₀^Λ ρ(p)/(p²+Δ²) dp."""

    def test_I0_formula(self):
        """I(0) = c₄·Λ²/2 = Λ²/(8π²)."""
        Lambda = 3.0
        I0 = tetrad_gap_integral(0, Lambda)
        expected = Lambda**2 / (8 * np.pi**2)
        assert abs(I0 - expected) < 1e-12

    def test_I0_positive(self):
        """I(0) > 0 for any Λ > 0."""
        for Lambda in [0.1, 1.0, np.pi, 10.0]:
            assert tetrad_gap_integral(0, Lambda) > 0

    def test_positive(self):
        """I(Δ) > 0 for Δ ≥ 0 and Λ > 0."""
        Lambda = np.pi
        for Delta in [0, 0.1, 0.5, 1.0, 2.0]:
            assert tetrad_gap_integral(Delta, Lambda) > 0

    def test_strictly_decreasing(self):
        """I(Δ₁) > I(Δ₂) when 0 ≤ Δ₁ < Δ₂."""
        Lambda = np.pi
        deltas = [0, 0.1, 0.5, 1.0, 2.0, 5.0]
        values = [tetrad_gap_integral(d, Lambda) for d in deltas]
        for i in range(len(values) - 1):
            assert values[i] > values[i + 1], (
                f"I({deltas[i]}) = {values[i]} should be > I({deltas[i+1]}) = {values[i+1]}"
            )

    def test_tends_to_zero(self):
        """I(Δ) → 0 as Δ → ∞."""
        Lambda = np.pi
        I_large = tetrad_gap_integral(1000, Lambda)
        assert I_large < 1e-4, f"I(1000) = {I_large} should be near zero"

    def test_upper_bound(self):
        """I(Δ) ≤ I(0) for all Δ ≥ 0."""
        Lambda = np.pi
        I0 = tetrad_gap_integral(0, Lambda)
        for Delta in [0.01, 0.1, 1.0, 5.0]:
            assert tetrad_gap_integral(Delta, Lambda) <= I0 + 1e-12

    def test_continuity_at_zero(self):
        """I(ε) → I(0) as ε → 0⁺."""
        Lambda = np.pi
        I0 = tetrad_gap_integral(0, Lambda)
        I_eps = tetrad_gap_integral(1e-8, Lambda)
        assert abs(I_eps - I0) < 1e-6, f"|I(ε) - I(0)| = {abs(I_eps - I0)} too large"


# ══════════════════════════════════════════════════════
# Critical coupling
# ══════════════════════════════════════════════════════


class TestCriticalCoupling:
    """Tests for G_c = 1/(N_f · I(0)) = 8π²/(N_f · Λ²)."""

    def test_matches_veff(self):
        """G_c from integral formulation matches V_eff formulation."""
        for Lambda in [1.0, np.pi, 5.0]:
            for N_f in [1, 2, 4]:
                Gc_int = tetrad_critical_coupling_integral(Lambda, N_f)
                Gc_veff = adw_critical_coupling(Lambda, N_f)
                assert abs(Gc_int - Gc_veff) < 1e-10, (
                    f"G_c mismatch at Λ={Lambda}, N_f={N_f}: "
                    f"integral={Gc_int}, V_eff={Gc_veff}"
                )

    def test_positive(self):
        """G_c > 0 for Λ > 0 and N_f > 0."""
        assert tetrad_critical_coupling_integral(np.pi, 2) > 0

    def test_explicit_formula(self):
        """G_c = 8π²/(N_f · Λ²) numerically."""
        Lambda = 2.0
        N_f = 3
        Gc = tetrad_critical_coupling_integral(Lambda, N_f)
        expected = 8 * np.pi**2 / (N_f * Lambda**2)
        assert abs(Gc - expected) < 1e-10

    def test_scaling_with_Lambda(self):
        """G_c ∝ 1/Λ². Doubling Λ divides G_c by 4."""
        N_f = 2
        Gc1 = tetrad_critical_coupling_integral(1.0, N_f)
        Gc2 = tetrad_critical_coupling_integral(2.0, N_f)
        assert abs(Gc1 / Gc2 - 4.0) < 1e-10

    def test_scaling_with_Nf(self):
        """G_c ∝ 1/N_f. Doubling N_f halves G_c."""
        Lambda = np.pi
        Gc1 = tetrad_critical_coupling_integral(Lambda, 1)
        Gc2 = tetrad_critical_coupling_integral(Lambda, 2)
        assert abs(Gc1 / Gc2 - 2.0) < 1e-10


# ══════════════════════════════════════════════════════
# Gap operator and solutions
# ══════════════════════════════════════════════════════


class TestGapOperator:
    """Tests for the gap operator f_G(Δ) = G·N_f·Δ·I(Δ)."""

    def test_trivial_fixed_point(self):
        """f_G(0) = 0 for any G."""
        assert tetrad_gap_operator(0, 5.0, np.pi, 2) == 0

    def test_nonneg(self):
        """f_G(Δ) ≥ 0 for Δ ≥ 0, G > 0."""
        assert tetrad_gap_operator(1.0, 5.0, np.pi, 2) > 0

    def test_subcritical_contraction(self):
        """For G < G_c: f_G(Δ)/Δ < 1 for all Δ > 0 (contraction)."""
        Lambda = np.pi
        N_f = 2
        Gc = tetrad_critical_coupling_integral(Lambda, N_f)
        G = 0.5 * Gc
        for Delta in [0.01, 0.1, 0.5, 1.0, 2.0]:
            ratio = tetrad_gap_operator(Delta, G, Lambda, N_f) / Delta
            assert ratio < 1.0, f"f_G(Δ)/Δ = {ratio} should be < 1 subcritically"

    def test_supercritical_expansion_at_origin(self):
        """For G > G_c: f_G(Δ)/Δ > 1 near Δ = 0 (expansion)."""
        Lambda = np.pi
        N_f = 2
        Gc = tetrad_critical_coupling_integral(Lambda, N_f)
        G = 2.0 * Gc
        Delta_small = 0.001
        ratio = tetrad_gap_operator(Delta_small, G, Lambda, N_f) / Delta_small
        assert ratio > 1.0, f"f_G(Δ)/Δ = {ratio} should be > 1 supercritically near 0"


class TestGapSolution:
    """Tests for the gap equation solver."""

    def test_subcritical_returns_zero(self):
        """For G < G_c, only trivial solution Δ = 0."""
        Lambda = np.pi
        N_f = 2
        Gc = tetrad_critical_coupling_integral(Lambda, N_f)
        assert tetrad_gap_solution(0.5 * Gc, Lambda, N_f) == 0.0

    def test_supercritical_returns_positive(self):
        """For G > G_c, nontrivial Δ* > 0."""
        Lambda = np.pi
        N_f = 2
        Gc = tetrad_critical_coupling_integral(Lambda, N_f)
        Delta_star = tetrad_gap_solution(2 * Gc, Lambda, N_f)
        assert Delta_star > 0, f"Δ* should be > 0 for G = 2·G_c"

    def test_fixed_point_equation(self):
        """Solution satisfies Δ* = f_G(Δ*)."""
        Lambda = np.pi
        N_f = 2
        Gc = tetrad_critical_coupling_integral(Lambda, N_f)
        G = 3.0 * Gc
        Delta_star = tetrad_gap_solution(G, Lambda, N_f)
        f_Delta = tetrad_gap_operator(Delta_star, G, Lambda, N_f)
        assert abs(Delta_star - f_Delta) / Delta_star < 1e-8, (
            f"Δ* = {Delta_star}, f_G(Δ*) = {f_Delta}"
        )

    def test_monotone_in_G(self):
        """Δ*(G) is increasing in G for G > G_c."""
        Lambda = np.pi
        N_f = 2
        Gc = tetrad_critical_coupling_integral(Lambda, N_f)
        G_values = [1.5 * Gc, 2.0 * Gc, 3.0 * Gc, 5.0 * Gc]
        solutions = [tetrad_gap_solution(G, Lambda, N_f) for G in G_values]
        for i in range(len(solutions) - 1):
            assert solutions[i] < solutions[i + 1], (
                f"Δ*({G_values[i]:.2f}) = {solutions[i]:.4f} should be < "
                f"Δ*({G_values[i+1]:.2f}) = {solutions[i+1]:.4f}"
            )

    def test_independent_accuracy_including_above_cutoff_hard_cases(self):
        """Keep r=5/10 hard cases; an imposed Delta<=Lambda cap must fail."""
        Lambda, N_f = np.pi, 2
        independent_Gc = 8 * np.pi**2 / (N_f * Lambda**2)
        for ratio in (1.5, 2.0, 5.0, 10.0):
            G = ratio * independent_Gc
            actual = tetrad_gap_solution(G, Lambda, N_f)
            expected = _positive_kernel_reference_gap(G, Lambda, N_f)
            assert actual == pytest.approx(expected, rel=2e-10, abs=0)
            if ratio in (5.0, 10.0):
                assert actual > Lambda

    def test_critical_point_zero(self):
        """At G = G_c, solution is exactly 0 (bifurcation point)."""
        Lambda = np.pi
        N_f = 2
        Gc = tetrad_critical_coupling_integral(Lambda, N_f)
        assert tetrad_gap_solution(Gc, Lambda, N_f) == 0.0


# ══════════════════════════════════════════════════════
# Density of states
# ══════════════════════════════════════════════════════


class TestDensityOfStates:
    """Tests for ρ(p) = c₄ · p³."""

    def test_nonneg(self):
        """ρ(p) ≥ 0 for p ≥ 0."""
        for p in [0, 0.1, 1.0, 10.0]:
            assert tetrad_density_of_states(p) >= 0

    def test_zero_at_origin(self):
        """ρ(0) = 0."""
        assert tetrad_density_of_states(0) == 0

    def test_c4_coefficient(self):
        """c₄ = 1/(4π²)."""
        rho_1 = tetrad_density_of_states(1.0)
        expected = 1 / (4 * np.pi**2)
        assert abs(rho_1 - expected) < 1e-12

    def test_cubic_scaling(self):
        """ρ(2p) = 8·ρ(p) (cubic in p)."""
        p = 1.5
        assert abs(tetrad_density_of_states(2 * p) / tetrad_density_of_states(p) - 8.0) < 1e-10


class TestNJLNumericalContract:
    @pytest.mark.parametrize("q,denominator", [
        (1.0, 1 - np.log(2.0)), (2.0, 1 - 4 * np.log(5 / 4)),
    ])
    @pytest.mark.parametrize("Lambda,N_f", [(1.0, 1), (np.pi, 2), (1e-20, 4)])
    def test_independent_closed_witnesses(self, q, denominator, Lambda, N_f):
        # Expected coupling uses only the stipulated analytic coefficient/witness.
        G = 8 * np.pi**2 / (N_f * Lambda**2 * denominator)
        actual = tetrad_gap_solution(G, Lambda, N_f)
        assert actual / Lambda == pytest.approx(q, rel=2e-10, abs=0)

    @pytest.mark.parametrize("Lambda", [1e-20, 1.0, 1e100])
    @pytest.mark.parametrize("q", [1e-12, 0.1, 1.0, np.sqrt(2)*(1-1e-10), np.sqrt(2)*(1+1e-10), 2.0, 10.0, 1e12, 1e150])
    def test_integral_against_independent_positive_kernel(self, Lambda, q):
        import mpmath as mp
        with mp.workdps(90):
            z = mp.mpf(str(q))**2
            expected = (mp.mpf(str(Lambda))**2 / (8 * mp.pi**2)
                        * _positive_kernel_B_reference(mp, z))
            expected_float = float(expected)
        if expected_float == 0:
            with pytest.raises(ArithmeticError):
                tetrad_gap_integral(q * Lambda, Lambda)
        else:
            actual = tetrad_gap_integral(q * Lambda, Lambda)
            assert actual > 0
            assert actual == pytest.approx(expected_float, rel=5e-12, abs=0)

    def test_resolved_nearcritical_gap_and_ambiguous_neighbors(self):
        Gc = 8 * np.pi**2 / 4
        G = (1 + 1e-8) * Gc
        actual = tetrad_gap_solution(G, 1.0, 4)
        assert actual > 0
        # Threshold conditioning amplifies coefficient rounding here; no 1e-12
        # mathematical root-accuracy assertion is inferred from solver tol.
        assert actual == pytest.approx(_positive_kernel_reference_gap(G, 1.0, 4), rel=1e-6, abs=0)
        represented = tetrad_critical_coupling_integral(1.0, 4)
        for neighbor in (np.nextafter(represented, 0.0), np.nextafter(represented, np.inf)):
            with pytest.raises(ArithmeticError, match="threshold guard"):
                tetrad_gap_solution(neighbor, 1.0, 4)
        assert tetrad_gap_solution(represented, 1.0, 4) == 0
        assert tetrad_gap_solution(0.0, 1.0, 4) == 0

    def test_huge_unrepresentable_ratio_has_finite_relative_gap(self):
        # r is about1e400, so forming a binary64 quotient would overflow.
        # Exact two-sided bound puts Delta/sqrt(G*N_f/(16*pi^2)) within O(1/r).
        N_f, G = 8 * np.pi**2 * 1e200, 1e200
        actual = tetrad_gap_solution(G, 1.0, N_f)
        assert np.isfinite(actual) and actual > 1
        assert actual / 1e200 == pytest.approx(1 / np.sqrt(2), rel=5e-12)

    def test_solver_logarithms_do_not_require_representable_I0(self):
        import mpmath as mp
        Lambda, N_f = 1e160, 1e-200
        with mp.workdps(90):
            G = float(8 * mp.pi**2 / (mp.mpf(str(N_f)) * mp.mpf(str(Lambda))**2
                                      * (1 - 4 * mp.log(mp.mpf(5) / 4))))
        with pytest.raises(ArithmeticError):
            tetrad_gap_integral(0, Lambda, N_f)
        assert tetrad_gap_solution(G, Lambda, N_f) / Lambda == pytest.approx(2, rel=2e-10)

    @pytest.mark.parametrize("bad", [True, -1, np.nan, np.inf, complex(1, 0), [1]])
    def test_nonnegative_scalar_domains(self, bad):
        with pytest.raises(ValueError):
            tetrad_gap_integral(bad, 1.0)
        with pytest.raises(ValueError):
            tetrad_gap_operator(1.0, bad, 1.0)
        with pytest.raises(ValueError):
            tetrad_gap_solution(bad, 1.0)

    @pytest.mark.parametrize("Lambda,N_f", [(0, 1), (-1, 1), (1, 0), (True, 1), (1, np.inf)])
    def test_positive_scale_and_species_domains(self, Lambda, N_f):
        with pytest.raises(ValueError):
            tetrad_critical_coupling_integral(Lambda, N_f)
        with pytest.raises(ValueError):
            tetrad_gap_solution(0, Lambda, N_f)

    @pytest.mark.parametrize("tol,max_iter", [(0, 1000), (1, 1000), (np.nan, 1000), (True, 1000), (1e-12, 0), (1e-12, True), (1e-12, 1.5)])
    def test_invalid_accuracy_budgets(self, tol, max_iter):
        with pytest.raises(ValueError):
            tetrad_gap_solution(100.0, 1.0, tol=tol, max_iter=max_iter)

    def test_exhaustion_stagnation_and_invalid_bracket_are_failures(self, monkeypatch):
        import src.core.formulas as formulas
        G = 8 * np.pi**2 / (1 - np.log(2))
        with pytest.raises(ArithmeticError, match="exhausted"):
            tetrad_gap_solution(G, 1.0, max_iter=1)
        with pytest.raises(ArithmeticError):
            tetrad_gap_solution(G, 1.0, tol=1e-30)
        monkeypatch.setattr(formulas, "_tetrad_njl_log_B", lambda z: 0.0)
        with pytest.raises(ArithmeticError, match="strict numerical sign bracket"):
            formulas.tetrad_gap_solution(4 * 8 * np.pi**2, 1.0)
        monkeypatch.setattr(formulas, "_tetrad_njl_log_B", lambda z: np.nan)
        with pytest.raises(ArithmeticError, match="nonfinite"):
            formulas.tetrad_gap_solution(4 * 8 * np.pi**2, 1.0)

    def test_dimension_and_nonrepresentable_root_contracts(self):
        with pytest.raises(NotImplementedError):
            tetrad_gap_integral(1.0, 1.0, d=3)
        with pytest.raises(ValueError):
            tetrad_gap_integral(1.0, 1.0, d=True)
        with pytest.raises(ArithmeticError, match="normal G_c"):
            tetrad_gap_solution(1.0, 1e160)
        with pytest.raises(ArithmeticError):
            tetrad_gap_solution(1e308, 1e150)

    def test_output_representability_is_explicit(self):
        with pytest.raises(ArithmeticError):
            tetrad_gap_integral(0, 1e300)
        with pytest.raises(ArithmeticError):
            tetrad_gap_integral(1e150, 1e-150)
        with pytest.raises(ArithmeticError):
            tetrad_critical_coupling_integral(1e-300)
        # Legitimate zero operator is still zero even if standalone I0 overflows.
        assert tetrad_gap_operator(0, 1.0, 1e300) == 0
        assert tetrad_gap_operator(1.0, 0.0, 1e300) == 0


class TestNJLOriginalScalarAdmission:
    @pytest.mark.parametrize("sign", [1, -1])
    def test_original_rational_underflow_is_refused_by_canonical_entrypoints(self, sign):
        from fractions import Fraction
        epsilon = Fraction(sign, 10**400)
        calls = (
            lambda: tetrad_gap_integral(epsilon, 1.0),
            lambda: tetrad_gap_solution(epsilon, 1.0),
            lambda: tetrad_gap_operator(epsilon, 1.0, 1.0),
            lambda: tetrad_gap_operator(1.0, epsilon, 1.0),
        )
        for call in calls:
            with pytest.raises(ValueError):
                call()

    def test_nonzero_compensated_operator_inputs_are_refused_not_zeroed(self):
        from fractions import Fraction
        epsilon = Fraction(1, 10**400)
        # Exact model outputs can be normal despite non-binary64 input:
        # G=epsilon,N_f=1e300,Delta=Lambda=1 gives a positive O(1e-100) product;
        # Delta=epsilon,G=1e300,Lambda=N_f=1 is another positive O(1e-100) case.
        # Input refusal is legitimate; silently replacing either with zero is not.
        with pytest.raises(ValueError):
            tetrad_gap_operator(1.0, epsilon, 1.0, 1e300)
        with pytest.raises(ValueError):
            tetrad_gap_operator(epsilon, 1e300, 1.0, 1.0)

    def test_true_zero_encodings_and_representable_subnormals_remain_valid(self):
        from fractions import Fraction
        for zero in (0.0, -0.0, Fraction(0, 1)):
            assert tetrad_gap_solution(zero, 1.0) == 0
            assert tetrad_gap_operator(1.0, zero, 1.0) == 0
            assert tetrad_gap_operator(zero, 1.0, 1.0) == 0
            assert tetrad_gap_integral(zero, 1.0) == pytest.approx(1 / (8 * np.pi**2))
        smallest = np.nextafter(0.0, 1.0)
        assert tetrad_gap_integral(smallest, 1.0) == pytest.approx(1 / (8 * np.pi**2))
        compensated = tetrad_gap_operator(smallest, 1e308, 1.0)
        # B(z) lies between1/4 and1 for0<z<1; expected scale is independent
        # of production I/Gc and finite after multiplying these binary64 inputs.
        scale = smallest * 1e308 / (8 * np.pi**2)
        assert np.isfinite(compensated) and scale / 4 < compensated < scale * 2

    @pytest.mark.parametrize("z_text", ["1", "4", "1e24", "1e300"])
    def test_scaled_kernel_reference_precision_refinement(self, z_text):
        import mpmath as mp
        values = []
        for digits in (60, 90, 120):
            with mp.workdps(digits):
                z = mp.mpf(z_text)
                values.append(z * _positive_kernel_B_reference(mp, z))
        with mp.workdps(120):
            assert mp.mpf("0.2") < values[-1] < mp.mpf("0.6")
            for value in values[:-1]:
                assert abs(value / values[-1] - 1) < mp.mpf("1e-35")
            # These are planned convergence checks, not pre-certified90 digits.
            if z_text in ("1", "4"):
                z = mp.mpf(z_text)
                closed = z * (1 - z * mp.log1p(1 / z))
                assert abs(values[-1] / closed - 1) < mp.mpf("1e-35")
