"""Tests for the ADW mean-field gap equation (Phase 3, Item 3F).

Validates:
1. Wen's emergent QED model: N_f counting, Nielsen-Ninomiya, velocity structure
2. Hubbard-Stratonovich decomposition: action structure, tetrad field properties
3. Gap equation: effective potential, critical coupling, phase transitions
4. Fluctuation analysis: NG mode counting, graviton identification, Vergeles check
5. Structural obstacles for emergent fermion bootstrap
6. Cross-module consistency with formulas.py
"""

import pytest
import numpy as np
from src.adw.wen_model import (
    WenRotorModel,
    EmergentQED,
    VelocityStructure,
    wen_coulomb_phase,
    herbut_terminal_velocity,
    nielsen_ninomiya_weyl_count,
    nielsen_ninomiya_dirac_count,
)
from src.adw.hubbard_stratonovich import (
    ADWAction,
    TetradField,
    HSDecomposition,
    adw_cosmological_term,
    hubbard_stratonovich_decompose,
    fermion_effective_action,
    composite_tetrad_operator,
)
from src.adw.gap_equation import (
    GapEquationParams,
    TetradSolution,
    PhaseType,
    GapEquationResult,
    effective_potential,
    effective_potential_derivative,
    critical_coupling,
    curvature_at_origin,
    solve_gap_equation,
    classify_phase,
    vestigial_metric_condition,
    full_gap_analysis,
    effective_potential_landscape,
)
from src.adw.fluctuations import (
    SymmetryBreakingPattern,
    NGModeType,
    NGMode,
    FluctuationResult,
    lorentz_group_dimension,
    broken_generator_count,
    tetrad_component_count,
    classify_ng_modes,
    vergeles_mode_counting,
    graviton_identification,
    structural_obstacles,
    full_fluctuation_analysis,
)
from src.core.formulas import (
    adw_effective_potential,
    adw_critical_coupling,
    tetrad_broken_generators,
    graviton_polarization_count,
)


# ═══════════════════════════════════════════════════════════════════
# Wen's Emergent QED Model
# ═══════════════════════════════════════════════════════════════════

class TestWenRotorModel:
    """Test the Wen lattice rotor model."""

    def test_rotor_model_construction(self):
        model = WenRotorModel(U=1.0, t=2.0, g=5.0)
        assert model.lattice_dim == 3
        assert model.spacetime_dim == 4

    def test_coulomb_phase(self):
        """Coulomb phase requires t > U."""
        confined = WenRotorModel(U=2.0, t=1.0, g=5.0)
        deconfined = WenRotorModel(U=1.0, t=2.0, g=5.0)
        assert not confined.is_coulomb_phase
        assert deconfined.is_coulomb_phase

    def test_boundary_coupling(self):
        """At t = U, system is at the transition."""
        model = WenRotorModel(U=1.0, t=1.0, g=5.0)
        assert not model.is_coulomb_phase  # Not strictly in Coulomb phase


class TestNielsenNinomiya:
    """Test Nielsen-Ninomiya fermion doubling."""

    def test_3d_lattice(self):
        """3D cubic lattice: 2^3 = 8 Weyl, 4 Dirac."""
        assert nielsen_ninomiya_weyl_count(3) == 8
        assert nielsen_ninomiya_dirac_count(3) == 4

    def test_2d_lattice(self):
        """2D lattice: 2^2 = 4 Weyl, 2 Dirac."""
        assert nielsen_ninomiya_weyl_count(2) == 4
        assert nielsen_ninomiya_dirac_count(2) == 2

    def test_weyl_equals_double_dirac(self):
        """N_weyl = 2 * N_dirac for all dimensions."""
        for d in range(1, 6):
            assert nielsen_ninomiya_weyl_count(d) == 2 * nielsen_ninomiya_dirac_count(d)

    def test_weyl_is_power_of_two(self):
        for d in range(1, 6):
            n = nielsen_ninomiya_weyl_count(d)
            assert n == 2**d


class TestEmergentQED:
    """Test the emergent QED theory."""

    def test_default_construction(self):
        qed = wen_coulomb_phase()
        assert qed.N_f == 4
        assert qed.N_weyl == 8
        assert qed.gauge_group == "U(1)"
        assert not qed.is_chiral

    def test_non_chiral(self):
        """Lattice models always produce non-chiral fermions."""
        qed = wen_coulomb_phase()
        assert not qed.is_chiral

    def test_custom_velocities(self):
        qed = wen_coulomb_phase(v_F=0.5, v_B=1.5, c_lattice=1.0)
        assert qed.velocities.v_F == 0.5
        assert qed.velocities.v_B == 1.5


class TestVelocityEqualization:
    """Test Herbut velocity equalization RG flow."""

    def test_equal_velocities_stay_equal(self):
        """If all velocities are equal, they remain equal."""
        v = herbut_terminal_velocity(1.0, 1.0, 1.0)
        assert abs(v.v_F - 1.0) < 1e-10
        assert abs(v.v_B - 1.0) < 1e-10
        assert abs(v.c_lattice - 1.0) < 1e-10

    def test_velocities_converge(self):
        """RG flow reduces Lorentz violation."""
        initial = VelocityStructure(v_F=0.5, v_B=1.5, c_lattice=1.0)
        final = herbut_terminal_velocity(0.5, 1.5, 1.0, rg_steps=500)
        assert final.lorentz_violation < initial.lorentz_violation

    def test_convergence_monotonic(self):
        """Lorentz violation decreases monotonically with RG steps."""
        v_prev = VelocityStructure(v_F=0.3, v_B=1.5, c_lattice=1.0)
        for steps in [10, 50, 100, 500]:
            v = herbut_terminal_velocity(0.3, 1.5, 1.0, rg_steps=steps)
            assert v.lorentz_violation <= v_prev.lorentz_violation + 1e-10
            v_prev = v


# ═══════════════════════════════════════════════════════════════════
# Hubbard-Stratonovich Decomposition
# ═══════════════════════════════════════════════════════════════════

class TestADWAction:
    """Test the ADW multi-fermion interaction."""

    def test_action_construction(self):
        action = adw_cosmological_term(G=1.0)
        assert action.G == 1.0
        assert action.spacetime_dim == 4
        assert action.n_fermion_legs == 8
        assert action.n_derivatives == 4

    def test_fermion_mass_dimension_zero(self):
        """ADW spinors have mass dimension 0."""
        action = ADWAction(G=1.0)
        assert action.fermion_mass_dim == 0.0


class TestTetradField:
    """Test the tetrad field data structure."""

    def test_flat_spacetime(self):
        e = TetradField.flat_spacetime(C=1.0)
        np.testing.assert_array_almost_equal(e.components, np.eye(4))
        assert abs(e.determinant - 1.0) < 1e-10
        assert e.is_nondegenerate
        assert e.is_lorentzian

    def test_scaled_flat_spacetime(self):
        C = 2.5
        e = TetradField.flat_spacetime(C=C)
        assert abs(e.determinant - C**4) < 1e-10
        assert abs(e.magnitude - C) < 1e-10
        assert e.is_lorentzian

    def test_zero_tetrad(self):
        e = TetradField.zero()
        assert abs(e.determinant) < 1e-10
        assert not e.is_nondegenerate
        assert abs(e.magnitude) < 1e-10

    def test_metric_from_tetrad(self):
        """g_{mu nu} = eta_{ab} e^a_mu e^b_nu."""
        C = 1.5
        e = TetradField.flat_spacetime(C=C)
        expected = C**2 * np.diag([-1.0, 1.0, 1.0, 1.0])
        np.testing.assert_array_almost_equal(e.metric, expected)

    def test_lorentzian_signature(self):
        e = TetradField.flat_spacetime(C=1.0)
        assert e.signature == (1, 0, 3)

    def test_lorentz_rotated(self):
        """Lorentz-rotated tetrad preserves Lorentzian signature."""
        e = TetradField.lorentz_rotated(C=1.0, boost_rapidity=0.5)
        assert e.is_nondegenerate
        assert e.is_lorentzian

    def test_must_be_4x4(self):
        with pytest.raises(ValueError):
            TetradField(components=np.eye(3))

    def test_metric_determinant_relation(self):
        """det(g) = det(e)^2 * det(eta)."""
        C = 2.0
        e = TetradField.flat_spacetime(C=C)
        assert abs(e.metric_determinant - e.determinant**2 * (-1.0)) < 1e-10


class TestHSDecomposition:
    """Test the HS decomposition."""

    def test_decomposition_structure(self):
        action = adw_cosmological_term(G=1.0)
        hs = hubbard_stratonovich_decompose(action)
        assert hs.n_hs_steps == 2  # 8-fermion needs double HS
        assert hs.is_fermion_quadratic
        assert "Dirac" in hs.yukawa_structure

    def test_fermion_effective_action(self):
        e = TetradField.flat_spacetime(C=0.5)
        result = fermion_effective_action(e, N_f=4, Lambda=1.0, G=20.0)
        assert result['C'] == pytest.approx(0.5, abs=1e-10)
        assert 'V_tree' in result
        assert 'V_1loop' in result
        assert 'V_eff' in result

    def test_composite_tetrad_operator(self):
        expr = composite_tetrad_operator()
        assert "gamma^a" in expr
        assert "partial_mu" in expr


# ═══════════════════════════════════════════════════════════════════
# Gap Equation
# ═══════════════════════════════════════════════════════════════════

class TestEffectivePotential:
    """Test the effective potential V_eff(C)."""

    def test_veff_at_zero(self):
        """V_eff(0) = 0."""
        assert effective_potential(0.0, G=20.0, Lambda=1.0, N_f=4) == 0.0

    def test_veff_positive_below_Gc(self):
        """For G < G_c, V_eff(C) > 0 for all C > 0."""
        G_c = critical_coupling(1.0, 4)
        G = 0.5 * G_c
        for C in [0.01, 0.1, 0.5, 0.9]:
            assert effective_potential(C, G, 1.0, 4) > 0

    def test_veff_negative_above_Gc(self):
        """For G > G_c, V_eff has negative values (nontrivial minimum)."""
        G_c = critical_coupling(1.0, 4)
        G = 2.0 * G_c
        # The minimum should have V < 0
        V_values = [effective_potential(C, G, 1.0, 4) for C in np.linspace(0.01, 0.99, 50)]
        assert min(V_values) < 0

    def test_veff_large_C_positive(self):
        """V_eff grows positive for large C (theory is bounded below)."""
        G_c = critical_coupling(1.0, 4)
        G = 2.0 * G_c
        assert effective_potential(0.99, G, 1.0, 4) > effective_potential(0.5, G, 1.0, 4)


class TestCriticalCoupling:
    """Test the critical coupling G_c."""

    def test_critical_coupling_positive(self):
        assert critical_coupling(1.0, 4) > 0

    def test_critical_coupling_formula(self):
        """G_c = 8 pi^2 / (N_f Lambda^2)."""
        Lambda, N_f = 2.0, 6
        G_c = critical_coupling(Lambda, N_f)
        expected = 8.0 * np.pi**2 / (N_f * Lambda**2)
        assert G_c == pytest.approx(expected)

    def test_curvature_zero_at_Gc(self):
        """d^2V/dC^2 at origin vanishes at G = G_c."""
        G_c = critical_coupling(1.0, 4)
        assert curvature_at_origin(G_c, 1.0, 4) == pytest.approx(0.0, abs=1e-10)

    def test_curvature_positive_below_Gc(self):
        G_c = critical_coupling(1.0, 4)
        assert curvature_at_origin(0.5 * G_c, 1.0, 4) > 0

    def test_curvature_negative_above_Gc(self):
        G_c = critical_coupling(1.0, 4)
        assert curvature_at_origin(2.0 * G_c, 1.0, 4) < 0

    def test_Gc_scales_with_Lambda(self):
        """G_c ~ 1/Lambda^2."""
        G_c1 = critical_coupling(1.0, 4)
        G_c2 = critical_coupling(2.0, 4)
        assert G_c1 / G_c2 == pytest.approx(4.0)

    def test_Gc_scales_with_Nf(self):
        """G_c ~ 1/N_f."""
        G_c1 = critical_coupling(1.0, 2)
        G_c2 = critical_coupling(1.0, 4)
        assert G_c1 / G_c2 == pytest.approx(2.0)


class TestGapEquation:
    """Test the gap equation solver."""

    def test_below_Gc_gives_pregeometric(self):
        result = full_gap_analysis(G=5.0, Lambda=1.0, N_f=4)
        assert result.phase == PhaseType.PRE_GEOMETRIC
        assert result.nontrivial_solution is None

    def test_above_Gc_gives_full_tetrad(self):
        G_c = critical_coupling(1.0, 4)
        result = full_gap_analysis(G=2.0 * G_c, Lambda=1.0, N_f=4)
        assert result.phase == PhaseType.FULL_TETRAD
        assert result.nontrivial_solution is not None
        assert result.nontrivial_solution.C > 0

    def test_lorentzian_signature(self):
        """Nontrivial solution has Lorentzian signature."""
        G_c = critical_coupling(1.0, 4)
        result = full_gap_analysis(G=2.0 * G_c, Lambda=1.0, N_f=4)
        assert result.nontrivial_solution.is_lorentzian

    def test_nontrivial_is_global_minimum(self):
        """Nontrivial solution has lower energy than trivial."""
        G_c = critical_coupling(1.0, 4)
        result = full_gap_analysis(G=2.0 * G_c, Lambda=1.0, N_f=4)
        assert result.nontrivial_solution.V_eff < 0  # V(0) = 0

    def test_C_increases_with_coupling(self):
        """Stronger coupling gives larger tetrad VEV."""
        G_c = critical_coupling(1.0, 4)
        C_prev = 0.0
        for ratio in [1.5, 2.0, 3.0, 5.0]:
            result = full_gap_analysis(G=ratio * G_c, Lambda=1.0, N_f=4)
            C = result.nontrivial_solution.C
            assert C > C_prev
            C_prev = C

    def test_coupling_ratio(self):
        G_c = critical_coupling(1.0, 4)
        params = GapEquationParams(G=3.0 * G_c, Lambda=1.0, N_f=4)
        assert params.coupling_ratio == pytest.approx(3.0)


class TestPhaseClassification:
    """Test phase classification logic."""

    def test_pregeometric(self):
        assert classify_phase(0.0) == PhaseType.PRE_GEOMETRIC

    def test_full_tetrad(self):
        assert classify_phase(0.5) == PhaseType.FULL_TETRAD

    def test_vestigial_metric(self):
        assert classify_phase(0.0, has_metric_fluctuations=True) == PhaseType.VESTIGIAL_METRIC

    def test_vestigial_condition(self):
        G_c = critical_coupling(1.0, 4)
        assert vestigial_metric_condition(0.9 * G_c, G_c)
        assert not vestigial_metric_condition(0.5 * G_c, G_c)
        assert not vestigial_metric_condition(1.5 * G_c, G_c)


class TestEffectivePotentialLandscape:
    """Test landscape computation for plotting."""

    def test_landscape_returns_arrays(self):
        result = effective_potential_landscape(G=20.0, Lambda=1.0, N_f=4)
        assert len(result['C']) == 200
        assert len(result['V_eff']) == 200

    def test_landscape_starts_at_zero(self):
        result = effective_potential_landscape(G=20.0, Lambda=1.0, N_f=4)
        assert result['V_eff'][0] == 0.0


# ═══════════════════════════════════════════════════════════════════
# Fluctuation Analysis
# ═══════════════════════════════════════════════════════════════════

class TestLorentzDimension:
    """Test Lorentz group dimension formula."""

    def test_4d(self):
        assert lorentz_group_dimension(4) == 6

    def test_3d(self):
        assert lorentz_group_dimension(3) == 3

    def test_5d(self):
        assert lorentz_group_dimension(5) == 10

    def test_formula(self):
        for d in range(2, 8):
            assert lorentz_group_dimension(d) == d * (d - 1) // 2


class TestBrokenGenerators:
    """Test broken generator counting."""

    def test_4d(self):
        """In 4D: L_c x L_s -> L_J gives 6 broken generators."""
        assert broken_generator_count(4) == 6

    def test_equals_lorentz_dim(self):
        """n_broken = dim SO(d-1,1)."""
        for d in range(2, 8):
            assert broken_generator_count(d) == lorentz_group_dimension(d)


class TestNGModeClassification:
    """Test Nambu-Goldstone mode classification."""

    def test_4d_mode_count(self):
        modes = classify_ng_modes(4)
        total = sum(m.count for m in modes)
        assert total == 16  # 4^2 = 16 tetrad components

    def test_4d_graviton(self):
        """2 massless graviton polarizations in 4D."""
        modes = classify_ng_modes(4)
        graviton = [m for m in modes if m.mode_type == NGModeType.MASSLESS_GRAVITON]
        assert len(graviton) == 1
        assert graviton[0].count == 2
        assert graviton[0].spin == 2
        assert graviton[0].mass_status == "massless"

    def test_4d_absorbed(self):
        """6 modes absorbed by spin connection in 4D."""
        modes = classify_ng_modes(4)
        absorbed = [m for m in modes if m.mode_type == NGModeType.ABSORBED]
        assert absorbed[0].count == 6

    def test_4d_massive(self):
        """4 massive Higgs modes in 4D."""
        modes = classify_ng_modes(4)
        massive = [m for m in modes if m.mode_type == NGModeType.MASSIVE_HIGGS]
        assert massive[0].count == 4

    def test_4d_gauge(self):
        """4 pure gauge modes (diffeomorphisms) in 4D."""
        modes = classify_ng_modes(4)
        gauge = [m for m in modes if m.mode_type == NGModeType.PURE_GAUGE]
        assert gauge[0].count == 4

    def test_3d_no_graviton(self):
        """0 graviton polarizations in 3D (no gravitational waves)."""
        modes = classify_ng_modes(3)
        graviton = [m for m in modes if m.mode_type == NGModeType.MASSLESS_GRAVITON]
        assert graviton[0].count == 0


class TestVergelesModeCounting:
    """Test Vergeles mode counting verification."""

    def test_4d_vergeles(self):
        result = vergeles_mode_counting(4)
        assert result['n_total'] == 16
        assert result['n_lorentz_gauge'] == 6
        assert result['n_diffeo_gauge'] == 4
        assert result['n_physical'] == 6
        assert result['n_graviton'] == 2
        assert result['n_massive'] == 4
        assert result['matches_vergeles']

    def test_consistent_counting(self):
        """n_total = n_lorentz + n_diffeo + n_physical."""
        result = vergeles_mode_counting(4)
        assert (result['n_lorentz_gauge'] + result['n_diffeo_gauge']
                + result['n_physical']) == result['n_total']


class TestGravitonIdentification:
    """Test graviton identification."""

    def test_4d_graviton(self):
        grav = graviton_identification(4)
        assert grav['n_polarizations'] == 2
        assert grav['spin'] == 2
        assert grav['mass'] == 0
        assert grav['has_gravitational_waves']
        assert "Higgs" in grav['nature']

    def test_3d_no_waves(self):
        grav = graviton_identification(3)
        assert grav['n_polarizations'] == 0
        assert not grav['has_gravitational_waves']

    def test_5d_graviton(self):
        grav = graviton_identification(5)
        assert grav['n_polarizations'] == 5


class TestStructuralObstacles:
    """Test structural obstacle enumeration."""

    def test_four_obstacles(self):
        obstacles = structural_obstacles()
        assert len(obstacles) == 4

    def test_obstacle_names(self):
        obstacles = structural_obstacles()
        names = {o.name for o in obstacles}
        assert "spin_connection_gap" in names
        assert "grassmann_bosonic_incompatibility" in names
        assert "nielsen_ninomiya_doubling" in names
        assert "cosmological_constant" in names

    def test_all_open(self):
        """All obstacles are currently open (unresolved)."""
        obstacles = structural_obstacles()
        for o in obstacles:
            assert o.status == "open"

    def test_severity_levels(self):
        obstacles = structural_obstacles()
        severities = {o.severity for o in obstacles}
        assert severities == {"serious", "moderate"}


class TestFullFluctuationAnalysis:
    """Test the complete fluctuation analysis."""

    def test_full_analysis_4d(self):
        result = full_fluctuation_analysis(4)
        assert result.n_graviton_polarizations == 2
        assert result.n_absorbed_modes == 6
        assert result.n_massive_modes == 4
        assert result.n_gauge_modes == 4
        assert result.graviton_is_massless
        assert result.vergeles_check
        assert len(result.obstacles) == 4

    def test_ssb_pattern(self):
        result = full_fluctuation_analysis(4)
        ssb = result.ssb_pattern
        assert ssb.dim_G == 12  # 2 * 6
        assert ssb.dim_H == 6
        assert ssb.n_broken == 6
        assert ssb.tetrad_components == 16
        assert ssb.n_physical_dof == 10  # 16 - 6


# ═══════════════════════════════════════════════════════════════════
# Cross-Module Consistency
# ═══════════════════════════════════════════════════════════════════

class TestCrossModuleConsistency:
    """Test consistency between adw modules and formulas.py."""

    def test_critical_coupling_matches_formulas(self):
        """gap_equation.critical_coupling == formulas.adw_critical_coupling."""
        for Lambda in [0.5, 1.0, 2.0]:
            for N_f in [2, 4, 8]:
                gc_gap = critical_coupling(Lambda, N_f)
                gc_form = adw_critical_coupling(Lambda, N_f)
                assert gc_gap == pytest.approx(gc_form)

    def test_effective_potential_matches_formulas(self):
        """gap_equation.effective_potential == formulas.adw_effective_potential."""
        for C in [0.01, 0.1, 0.5]:
            v_gap = effective_potential(C, G=20.0, Lambda=1.0, N_f=4)
            v_form = adw_effective_potential(C, G=20.0, Lambda=1.0, N_f=4)
            assert v_gap == pytest.approx(v_form)

    def test_broken_generators_matches_formulas(self):
        for d in [3, 4, 5]:
            bg_fluct = broken_generator_count(d)
            bg_form = tetrad_broken_generators(d)
            assert bg_fluct == bg_form

    def test_graviton_count_matches_formulas(self):
        for d in [3, 4, 5, 6]:
            grav_fluct = graviton_identification(d)['n_polarizations']
            grav_form = graviton_polarization_count(d)
            assert grav_fluct == grav_form

    def test_wen_nf_used_in_gap_equation(self):
        """Wen model's N_f feeds correctly into gap equation."""
        qed = wen_coulomb_phase()
        G_c = critical_coupling(1.0, qed.N_f)
        result = full_gap_analysis(G=2 * G_c, Lambda=1.0, N_f=qed.N_f)
        assert result.phase == PhaseType.FULL_TETRAD

    def test_full_chain_consistency(self):
        """End-to-end: Wen -> gap equation -> fluctuations."""
        qed = wen_coulomb_phase()
        G_c = critical_coupling(1.0, qed.N_f)
        gap = full_gap_analysis(G=2 * G_c, Lambda=1.0, N_f=qed.N_f)
        fluct = full_fluctuation_analysis()

        # Gap equation succeeds
        assert gap.success_criteria['nontrivial_exists']
        assert gap.success_criteria['lorentzian_signature']
        assert gap.success_criteria['is_global_minimum']

        # Fluctuations consistent
        assert fluct.n_graviton_polarizations == 2
        assert fluct.vergeles_check

        # But structural obstacles remain for emergent fermions
        assert len(fluct.obstacles) == 4
