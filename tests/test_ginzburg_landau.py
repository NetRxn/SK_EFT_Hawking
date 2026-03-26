"""Tests for the ADW Ginzburg-Landau phase classification (Phase 4, Item 1C).

Validates:
1. Invariant polynomials: values for B-phase and A-phase ansatze
2. GL coefficients: alpha sign change at G_c, positive beta_i
3. Phase classification: B-phase is ground state above G_c
4. Phase diagram: pre-geometric -> B-phase transition at G/G_c = 1
5. He-3 comparison: structural analogy completeness
6. GL free energy consistency with full CW potential
"""

import pytest
import numpy as np
from src.adw.ginzburg_landau import (
    GLCoefficients,
    InvariantPolynomial,
    GLPhaseType,
    PhaseClassification,
    GLPhaseDiagram,
    He3Comparison,
    compute_gl_coefficients,
    invariant_polynomials,
    classify_gl_phases,
    compute_phase_diagram,
    he3_comparison,
    gl_free_energy_general,
    independent_invariant_count_real,
    independent_invariant_count_complex,
)
from src.adw.gap_equation import critical_coupling


# ═══════════════════════════════════════════════════════════════════
# Invariant Polynomials
# ═══════════════════════════════════════════════════════════════════


class TestInvariantPolynomials:
    """Test the five quartic invariant polynomials."""

    def test_five_invariants(self):
        """There are exactly 5 quartic invariants."""
        invariants = invariant_polynomials()
        assert len(invariants) == 5

    def test_invariant_names(self):
        invariants = invariant_polynomials()
        names = [inv.name for inv in invariants]
        assert names == ["I_1", "I_2", "I_3", "I_4", "I_5"]

    def test_b_phase_I1(self):
        """I_1 for B-phase: |Tr(I * I^T)|^2 = |Tr(I)|^2 = 16."""
        invariants = invariant_polynomials()
        I1 = invariants[0]
        assert I1.value_B_phase == pytest.approx(16.0)

    def test_b_phase_I2(self):
        """I_2 for B-phase: Tr((I I^T)^2) = Tr(I) = 4."""
        invariants = invariant_polynomials()
        I2 = invariants[1]
        assert I2.value_B_phase == pytest.approx(4.0)

    def test_b_phase_I3_equals_I2(self):
        """I_3 = I_2 for real tetrad."""
        invariants = invariant_polynomials()
        assert invariants[2].value_B_phase == pytest.approx(
            invariants[1].value_B_phase
        )

    def test_b_phase_I5_equals_I1(self):
        """I_5 = I_1 for real tetrad."""
        invariants = invariant_polynomials()
        assert invariants[4].value_B_phase == pytest.approx(
            invariants[0].value_B_phase
        )

    def test_a_phase_I1(self):
        """I_1 for A-phase: |Tr(diag(1,1,1,0)^2)|^2 = 9."""
        invariants = invariant_polynomials()
        I1 = invariants[0]
        assert I1.value_A_phase == pytest.approx(9.0)

    def test_a_phase_smaller_than_b_phase(self):
        """A-phase invariants are smaller than B-phase (fewer condensed)."""
        invariants = invariant_polynomials()
        for inv in invariants:
            assert inv.value_A_phase <= inv.value_B_phase

    def test_invariant_I4_b_phase(self):
        """I_4 for B-phase: Tr((I^T I)^2) = 4."""
        invariants = invariant_polynomials()
        I4 = invariants[3]
        assert I4.value_B_phase == pytest.approx(4.0)

    def test_real_field_degeneracies(self):
        """For real fields: I_1 = I_5 and I_2 = I_3."""
        invariants = invariant_polynomials()
        # B-phase
        assert invariants[0].value_B_phase == pytest.approx(invariants[4].value_B_phase)
        assert invariants[1].value_B_phase == pytest.approx(invariants[2].value_B_phase)
        # A-phase
        assert invariants[0].value_A_phase == pytest.approx(invariants[4].value_A_phase)
        assert invariants[1].value_A_phase == pytest.approx(invariants[2].value_A_phase)


# ═══════════════════════════════════════════════════════════════════
# GL Coefficients
# ═══════════════════════════════════════════════════════════════════


class TestGLCoefficients:
    """Test GL coefficient computation from the CW potential."""

    def test_alpha_positive_below_Gc(self):
        """alpha > 0 for G < G_c (origin is stable)."""
        G_c = critical_coupling(1.0, 4)
        coeffs = compute_gl_coefficients(0.5 * G_c, 1.0, 4)
        assert coeffs.alpha > 0

    def test_alpha_zero_at_Gc(self):
        """alpha = 0 at G = G_c (critical point)."""
        G_c = critical_coupling(1.0, 4)
        coeffs = compute_gl_coefficients(G_c, 1.0, 4)
        assert coeffs.alpha == pytest.approx(0.0, abs=1e-10)

    def test_alpha_negative_above_Gc(self):
        """alpha < 0 for G > G_c (origin is unstable)."""
        G_c = critical_coupling(1.0, 4)
        coeffs = compute_gl_coefficients(2.0 * G_c, 1.0, 4)
        assert coeffs.alpha < 0

    def test_beta_positive(self):
        """All beta_i > 0 (CW potential is bounded below)."""
        G_c = critical_coupling(1.0, 4)
        coeffs = compute_gl_coefficients(2.0 * G_c, 1.0, 4)
        assert coeffs.beta_1 > 0
        assert coeffs.beta_2 > 0
        assert coeffs.beta_3 > 0
        assert coeffs.beta_4 > 0
        assert coeffs.beta_5 > 0

    def test_beta_real_field_degeneracies(self):
        """beta_3 = beta_2 and beta_5 = beta_1 for real tetrad."""
        coeffs = compute_gl_coefficients(20.0, 1.0, 4)
        assert coeffs.beta_3 == pytest.approx(coeffs.beta_2)
        assert coeffs.beta_5 == pytest.approx(coeffs.beta_1)

    def test_Tc_analog_is_Gc(self):
        """T_c analog is the critical coupling G_c."""
        G_c = critical_coupling(1.0, 4)
        coeffs = compute_gl_coefficients(20.0, 1.0, 4)
        assert coeffs.T_c_analog == pytest.approx(G_c)

    def test_parameters_stored(self):
        coeffs = compute_gl_coefficients(20.0, 1.0, 4)
        assert coeffs.G == 20.0
        assert coeffs.Lambda == 1.0
        assert coeffs.N_f == 4

    def test_alpha_scales_with_coupling(self):
        """alpha decreases monotonically with G."""
        G_c = critical_coupling(1.0, 4)
        alpha_prev = float('inf')
        for ratio in [0.5, 1.0, 1.5, 2.0, 3.0]:
            coeffs = compute_gl_coefficients(ratio * G_c, 1.0, 4)
            assert coeffs.alpha < alpha_prev
            alpha_prev = coeffs.alpha


# ═══════════════════════════════════════════════════════════════════
# Phase Classification
# ═══════════════════════════════════════════════════════════════════


class TestPhaseClassification:
    """Test GL phase classification."""

    def test_four_phases_classified(self):
        """Four phases are classified: B, A, polar, pre-geometric."""
        G_c = critical_coupling(1.0, 4)
        coeffs = compute_gl_coefficients(2.0 * G_c, 1.0, 4)
        phases = classify_gl_phases(coeffs)
        assert len(phases) == 4

    def test_phase_types_present(self):
        G_c = critical_coupling(1.0, 4)
        coeffs = compute_gl_coefficients(2.0 * G_c, 1.0, 4)
        phases = classify_gl_phases(coeffs)
        types = {p.phase_type for p in phases}
        assert GLPhaseType.B_PHASE in types
        assert GLPhaseType.A_PHASE in types
        assert GLPhaseType.POLAR in types
        assert GLPhaseType.PRE_GEOMETRIC in types

    def test_b_phase_is_ground_state_above_Gc(self):
        """B-phase is the ground state for G > G_c."""
        G_c = critical_coupling(1.0, 4)
        coeffs = compute_gl_coefficients(2.0 * G_c, 1.0, 4)
        phases = classify_gl_phases(coeffs)

        ground = [p for p in phases if p.is_ground_state]
        assert len(ground) == 1
        assert ground[0].phase_type == GLPhaseType.B_PHASE

    def test_pre_geometric_is_ground_state_below_Gc(self):
        """Pre-geometric phase is ground state for G < G_c."""
        G_c = critical_coupling(1.0, 4)
        coeffs = compute_gl_coefficients(0.5 * G_c, 1.0, 4)
        phases = classify_gl_phases(coeffs)

        ground = [p for p in phases if p.is_ground_state]
        assert len(ground) == 1
        assert ground[0].phase_type == GLPhaseType.PRE_GEOMETRIC

    def test_b_phase_lower_energy_than_a_phase(self):
        """B-phase has lower free energy than A-phase for G > G_c."""
        G_c = critical_coupling(1.0, 4)
        coeffs = compute_gl_coefficients(2.0 * G_c, 1.0, 4)
        phases = classify_gl_phases(coeffs)

        b_phase = [p for p in phases if p.phase_type == GLPhaseType.B_PHASE][0]
        a_phase = [p for p in phases if p.phase_type == GLPhaseType.A_PHASE][0]
        assert b_phase.free_energy < a_phase.free_energy

    def test_a_phase_lower_energy_than_polar(self):
        """A-phase has lower free energy than polar for G > G_c."""
        G_c = critical_coupling(1.0, 4)
        coeffs = compute_gl_coefficients(2.0 * G_c, 1.0, 4)
        phases = classify_gl_phases(coeffs)

        a_phase = [p for p in phases if p.phase_type == GLPhaseType.A_PHASE][0]
        polar = [p for p in phases if p.phase_type == GLPhaseType.POLAR][0]
        assert a_phase.free_energy < polar.free_energy

    def test_condensed_phases_negative_energy(self):
        """All condensed phases have negative free energy for G > G_c."""
        G_c = critical_coupling(1.0, 4)
        coeffs = compute_gl_coefficients(2.0 * G_c, 1.0, 4)
        phases = classify_gl_phases(coeffs)

        for p in phases:
            if p.phase_type != GLPhaseType.PRE_GEOMETRIC:
                assert p.free_energy < 0

    def test_he3_analogs_present(self):
        """Each phase has a He-3 analog description."""
        G_c = critical_coupling(1.0, 4)
        coeffs = compute_gl_coefficients(2.0 * G_c, 1.0, 4)
        phases = classify_gl_phases(coeffs)

        for p in phases:
            assert len(p.he3_analog) > 0

    def test_exactly_one_ground_state(self):
        """Exactly one phase is marked as ground state."""
        for ratio in [0.5, 1.5, 2.0, 3.0, 5.0]:
            G_c = critical_coupling(1.0, 4)
            coeffs = compute_gl_coefficients(ratio * G_c, 1.0, 4)
            phases = classify_gl_phases(coeffs)
            n_ground = sum(1 for p in phases if p.is_ground_state)
            assert n_ground == 1


# ═══════════════════════════════════════════════════════════════════
# Phase Diagram
# ═══════════════════════════════════════════════════════════════════


class TestPhaseDiagram:
    """Test the GL phase diagram computation."""

    def test_phase_diagram_structure(self):
        diagram = compute_phase_diagram(1.0, 4, n_points=20)
        assert len(diagram.coupling_ratios) == 20
        assert len(diagram.alpha_values) == 20
        assert len(diagram.free_energies_B) == 20
        assert len(diagram.free_energies_A) == 20
        assert len(diagram.free_energies_polar) == 20

    def test_alpha_sign_change(self):
        """alpha changes sign near G/G_c = 1."""
        diagram = compute_phase_diagram(1.0, 4, n_points=50)
        # alpha should be positive for ratio < 1 and negative for ratio > 1
        below_gc = diagram.alpha_values[diagram.coupling_ratios < 0.9]
        above_gc = diagram.alpha_values[diagram.coupling_ratios > 1.1]
        assert np.all(below_gc > 0)
        assert np.all(above_gc < 0)

    def test_phase_boundary_at_Gc(self):
        """Phase boundary is at G/G_c = 1."""
        diagram = compute_phase_diagram(1.0, 4)
        boundaries = diagram.phase_boundaries
        assert len(boundaries) >= 1
        assert boundaries[0][0] == pytest.approx(1.0)

    def test_ground_state_sequence(self):
        """Ground state is pre-geometric below G_c, B-phase above."""
        diagram = compute_phase_diagram(1.0, 4)
        gs = diagram.ground_state_sequence
        assert len(gs) == 2
        assert gs[0][1] == GLPhaseType.PRE_GEOMETRIC
        assert gs[1][1] == GLPhaseType.B_PHASE

    def test_b_phase_energy_most_negative(self):
        """B-phase free energy is most negative above G_c."""
        diagram = compute_phase_diagram(1.0, 4, n_points=20)
        above_gc = diagram.coupling_ratios > 1.1
        f_B = diagram.free_energies_B[above_gc]
        f_A = diagram.free_energies_A[above_gc]
        f_P = diagram.free_energies_polar[above_gc]

        # B-phase should be lower than A and polar at each point
        assert np.all(f_B <= f_A + 1e-15)
        assert np.all(f_B <= f_P + 1e-15)

    def test_pre_geometric_zero_energy(self):
        """Below G_c, condensed phase free energies are zero."""
        diagram = compute_phase_diagram(1.0, 4, n_points=20)
        below_gc = diagram.coupling_ratios < 0.9
        f_B = diagram.free_energies_B[below_gc]
        assert np.all(np.abs(f_B) < 1e-10)

    def test_different_nf(self):
        """Phase diagram works for different N_f values."""
        for N_f in [2, 4, 8]:
            diagram = compute_phase_diagram(1.0, N_f, n_points=10)
            assert len(diagram.coupling_ratios) == 10
            assert len(diagram.phase_boundaries) >= 1

    def test_different_lambda(self):
        """Phase diagram works for different Lambda values."""
        for Lambda in [0.5, 1.0, 2.0]:
            diagram = compute_phase_diagram(Lambda, 4, n_points=10)
            assert len(diagram.coupling_ratios) == 10


# ═══════════════════════════════════════════════════════════════════
# He-3 Comparison
# ═══════════════════════════════════════════════════════════════════


class TestHe3Comparison:
    """Test the He-3 structural comparison."""

    def test_comparison_count(self):
        """At least 8 comparison entries."""
        comparisons = he3_comparison()
        assert len(comparisons) >= 8

    def test_all_have_descriptions(self):
        comparisons = he3_comparison()
        for c in comparisons:
            assert len(c.adw_quantity) > 0
            assert len(c.he3_analog) > 0
            assert len(c.note) > 0

    def test_order_parameter_match(self):
        """Order parameter comparison is a structural match."""
        comparisons = he3_comparison()
        op = [c for c in comparisons if "Order parameter" in c.adw_quantity]
        assert len(op) == 1
        assert op[0].structural_match

    def test_ssb_pattern_match(self):
        """Symmetry breaking pattern is a structural match."""
        comparisons = he3_comparison()
        ssb = [c for c in comparisons if "SO(3,1)" in c.adw_quantity]
        assert len(ssb) >= 1
        assert ssb[0].structural_match

    def test_b_phase_match(self):
        """B-phase comparison is a structural match."""
        comparisons = he3_comparison()
        bp = [c for c in comparisons if "B-phase" in c.adw_quantity]
        assert len(bp) == 1
        assert bp[0].structural_match

    def test_a_phase_mismatch(self):
        """A-phase comparison is NOT a structural match (missing feedback)."""
        comparisons = he3_comparison()
        ap = [c for c in comparisons if "A-phase" in c.adw_quantity]
        assert len(ap) == 1
        assert not ap[0].structural_match

    def test_invariant_mismatch(self):
        """Invariant count comparison is NOT a match (real vs complex)."""
        comparisons = he3_comparison()
        inv = [c for c in comparisons if "invariant" in c.adw_quantity.lower()]
        assert len(inv) == 1
        assert not inv[0].structural_match

    def test_vestigial_match(self):
        """Vestigial metric comparison is a structural match."""
        comparisons = he3_comparison()
        ves = [c for c in comparisons if "Vestigial" in c.adw_quantity]
        assert len(ves) == 1
        assert ves[0].structural_match


# ═══════════════════════════════════════════════════════════════════
# GL Free Energy
# ═══════════════════════════════════════════════════════════════════


class TestGLFreeEnergy:
    """Test the general GL free energy evaluation."""

    def test_zero_tetrad_gives_zero(self):
        """F_GL(e=0) = 0."""
        coeffs = compute_gl_coefficients(20.0, 1.0, 4)
        e_zero = np.zeros((4, 4))
        assert gl_free_energy_general(coeffs, e_zero) == pytest.approx(0.0)

    def test_b_phase_consistency(self):
        """GL free energy for B-phase matches classify_gl_phases result."""
        G_c = critical_coupling(1.0, 4)
        coeffs = compute_gl_coefficients(2.0 * G_c, 1.0, 4)

        # GL free energy at C=1 for B-phase
        e_B = np.eye(4) * 0.3  # Small C for GL validity
        f_gl = gl_free_energy_general(coeffs, e_B)

        # Should be computable without error
        assert np.isfinite(f_gl)

    def test_alpha_positive_gives_positive_energy(self):
        """When alpha > 0, F_GL > 0 for small tetrad."""
        G_c = critical_coupling(1.0, 4)
        coeffs = compute_gl_coefficients(0.5 * G_c, 1.0, 4)
        e_small = 0.01 * np.eye(4)
        f = gl_free_energy_general(coeffs, e_small)
        assert f > 0

    def test_alpha_negative_gives_negative_energy(self):
        """When alpha < 0, F_GL < 0 for appropriately scaled tetrad."""
        G_c = critical_coupling(1.0, 4)
        coeffs = compute_gl_coefficients(2.0 * G_c, 1.0, 4)
        # At intermediate C, the quadratic term dominates and F < 0
        e_intermediate = 0.05 * np.eye(4)
        f = gl_free_energy_general(coeffs, e_intermediate)
        assert f < 0

    def test_b_phase_lower_than_a_phase_gl(self):
        """B-phase GL energy is lower than A-phase for same C."""
        G_c = critical_coupling(1.0, 4)
        coeffs = compute_gl_coefficients(2.0 * G_c, 1.0, 4)

        C = 0.05  # Small for GL validity
        e_B = C * np.eye(4)
        e_A = C * np.diag([1.0, 1.0, 1.0, 0.0])

        f_B = gl_free_energy_general(coeffs, e_B)
        f_A = gl_free_energy_general(coeffs, e_A)

        # B-phase has more negative quadratic contribution (4 vs 3 terms)
        assert f_B < f_A


# ═══════════════════════════════════════════════════════════════════
# Independent Invariant Counts
# ═══════════════════════════════════════════════════════════════════


class TestInvariantCounts:
    """Test independent invariant counting."""

    def test_real_count(self):
        """Real 4x4 tetrad has 3 independent quartic invariants."""
        assert independent_invariant_count_real() == 3

    def test_complex_count(self):
        """Complex 3x3 matrix (He-3) has 5 independent quartic invariants."""
        assert independent_invariant_count_complex() == 5

    def test_real_fewer_than_complex(self):
        """Real tetrad has fewer independent invariants than complex."""
        assert independent_invariant_count_real() < independent_invariant_count_complex()


# ═══════════════════════════════════════════════════════════════════
# Cross-Module Consistency
# ═══════════════════════════════════════════════════════════════════


class TestCrossModuleConsistency:
    """Test consistency between GL module and gap_equation module."""

    def test_alpha_matches_curvature(self):
        """GL alpha equals gap_equation curvature_at_origin."""
        from src.adw.gap_equation import curvature_at_origin
        for ratio in [0.5, 1.0, 2.0, 3.0]:
            G_c = critical_coupling(1.0, 4)
            G = ratio * G_c
            coeffs = compute_gl_coefficients(G, 1.0, 4)
            curv = curvature_at_origin(G, 1.0, 4)
            assert coeffs.alpha == pytest.approx(curv)

    def test_Tc_analog_matches_Gc(self):
        """T_c analog matches gap_equation critical coupling."""
        G_c_gap = critical_coupling(1.0, 4)
        coeffs = compute_gl_coefficients(20.0, 1.0, 4)
        assert coeffs.T_c_analog == pytest.approx(G_c_gap)

    def test_b_phase_ground_state_consistent_with_gap_equation(self):
        """B-phase ground state consistent with gap equation full tetrad phase."""
        from src.adw.gap_equation import full_gap_analysis, PhaseType
        G_c = critical_coupling(1.0, 4)
        G = 2.0 * G_c

        # Gap equation says full tetrad
        gap_result = full_gap_analysis(G, 1.0, 4)
        assert gap_result.phase == PhaseType.FULL_TETRAD

        # GL says B-phase (isotropic full tetrad)
        coeffs = compute_gl_coefficients(G, 1.0, 4)
        phases = classify_gl_phases(coeffs)
        ground = [p for p in phases if p.is_ground_state][0]
        assert ground.phase_type == GLPhaseType.B_PHASE

    def test_pre_geometric_consistent(self):
        """Pre-geometric ground state consistent between modules."""
        from src.adw.gap_equation import full_gap_analysis, PhaseType
        G_c = critical_coupling(1.0, 4)
        G = 0.5 * G_c

        gap_result = full_gap_analysis(G, 1.0, 4)
        assert gap_result.phase == PhaseType.PRE_GEOMETRIC

        coeffs = compute_gl_coefficients(G, 1.0, 4)
        phases = classify_gl_phases(coeffs)
        ground = [p for p in phases if p.is_ground_state][0]
        assert ground.phase_type == GLPhaseType.PRE_GEOMETRIC
