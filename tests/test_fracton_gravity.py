"""Tests for fracton-gravity Kerr-Schild analysis and non-Abelian fracton (Phase 4, Items 3A-3B).

Validates:
1. Linearized equivalence: fracton EOM matches linearized Einstein at omega=0
2. DOF counting: fracton has D(D+1)/2 - 2 DOF, GR has D(D-3)/2 DOF
3. Gupta-Feynman bootstrap: agrees at orders 1-2, fails at order 3
4. Bootstrap gap: five obstructions, structural and not closable
5. Gravity route comparison: acoustic (spin-0), fracton (spin-2 linearized), ADW (full)
6. Non-Abelian fracton: Wang-Xu-Yau, Bulmash-Barkeshli, Yang-Mills incompatibility
7. Derivative structure obstruction: dd vs d
8. Cross-consistency with Phase 4 Wave 2 fracton modules
"""

import pytest

from src.fracton.gravity_connection import (
    GaugeSymmetryType,
    ObstructionType,
    GravityRouteType,
    LinearizedEquivalence,
    BootstrapStep,
    BootstrapGap,
    BootstrapGapQuantification,
    CubicVertexStructure,
    GravityRouteComparison,
    GravityRouteProperties,
    NonAbelianResult,
    linearized_equivalence,
    gupta_feynman_bootstrap,
    bootstrap_gap_assessment,
    quantify_bootstrap_gap,
    compare_gravity_routes,
    non_abelian_fracton_analysis,
)
from src.fracton.non_abelian import (
    AlgebraType,
    NonAbelianSourceType,
    NonAbelianFractonGauge,
    YangMillsCompatibility,
    DerivativeStructureComparison,
    analyze_non_abelian_compatibility,
    wang_xu_yau_theory,
    bulmash_barkeshli_theory,
    standard_yang_mills,
    derivative_structure_comparison,
)


# ===================================================================
# Linearized equivalence (3A.1-3A.2)
# ===================================================================

class TestLinearizedEquivalence:
    """Test linearized equivalence between fracton and Einstein gravity."""

    def test_spin2_modes_4d(self):
        """In D=4, both fracton and GR produce 2 spin-2 modes (graviton)."""
        equiv = linearized_equivalence(spacetime_dim=4)
        assert equiv.spin2_modes == 2

    def test_omega_zero_is_gr(self):
        """At omega=0, the fracton action IS linearized GR."""
        equiv = linearized_equivalence(omega=0.0)
        assert equiv.is_exact_match_at_omega_zero

    def test_omega_nonzero_is_mixed(self):
        """At omega != 0, the theory is a 'mixed graviton-fracton phase'."""
        equiv = linearized_equivalence(omega=0.5)
        assert not equiv.is_exact_match_at_omega_zero

    def test_fracton_gauge_one_parameter(self):
        """Fracton gauge symmetry uses 1 scalar parameter."""
        equiv = linearized_equivalence(spacetime_dim=4)
        assert equiv.fracton_gauge_parameters == 1

    def test_diffeo_gauge_d_parameters(self):
        """Linearized diffeomorphisms use D vector parameters."""
        for D in [3, 4, 5]:
            equiv = linearized_equivalence(spacetime_dim=D)
            assert equiv.diffeo_gauge_parameters == D

    def test_fracton_dof_formula_4d(self):
        """In D=4: fracton has D(D+1)/2 - 2 = 8 propagating DOF."""
        equiv = linearized_equivalence(spacetime_dim=4)
        assert equiv.fracton_propagating_dof == 8

    def test_gr_dof_formula_4d(self):
        """In D=4: GR has D(D-3)/2 = 2 propagating DOF."""
        equiv = linearized_equivalence(spacetime_dim=4)
        assert equiv.gr_propagating_dof == 2

    def test_fracton_dof_formula_general(self):
        """Fracton DOF = D(D+1)/2 - 2 in general D."""
        for D in [3, 4, 5, 6]:
            equiv = linearized_equivalence(spacetime_dim=D)
            expected = D * (D + 1) // 2 - 2
            assert equiv.fracton_propagating_dof == expected

    def test_gr_dof_formula_general(self):
        """GR DOF = D(D-3)/2 in general D."""
        for D in [3, 4, 5, 6]:
            equiv = linearized_equivalence(spacetime_dim=D)
            expected = D * (D - 3) // 2
            assert equiv.gr_propagating_dof == expected

    def test_extra_dof_count_4d(self):
        """In D=4: 8 - 2 = 6 extra DOF (spin-1 + spin-0 sectors)."""
        equiv = linearized_equivalence(spacetime_dim=4)
        assert equiv.extra_dof_count == 6

    def test_gauge_parameter_ratio_4d(self):
        """Gauge parameter ratio D/1 = 4 in D=4."""
        equiv = linearized_equivalence(spacetime_dim=4)
        assert equiv.gauge_parameter_ratio == 4.0

    def test_matching_conditions_nonempty(self):
        """Matching conditions list should be populated."""
        equiv = linearized_equivalence()
        assert len(equiv.matching_conditions) >= 3

    def test_symmetry_deficit_description(self):
        """Symmetry deficit should mention scalar vs vector parameters."""
        equiv = linearized_equivalence()
        desc = equiv.symmetry_deficit
        assert "scalar" in desc.lower() or "1" in desc
        assert "vector" in desc.lower() or "4" in desc

    def test_eom_descriptions_nonempty(self):
        """EOMs should have non-trivial descriptions."""
        equiv = linearized_equivalence()
        assert len(equiv.fracton_eom) > 50
        assert len(equiv.einstein_eom) > 50

    def test_3d_has_fewer_spin2_modes(self):
        """In D=3, there is at most 1 spin-2 mode (topological gravity)."""
        equiv = linearized_equivalence(spacetime_dim=3)
        assert equiv.spin2_modes == 1

    def test_gr_zero_dof_in_3d(self):
        """In D=3, linearized GR has D(D-3)/2 = 0 DOF (topological)."""
        equiv = linearized_equivalence(spacetime_dim=3)
        assert equiv.gr_propagating_dof == 0


# ===================================================================
# Gupta-Feynman bootstrap (3A.3)
# ===================================================================

class TestGuptaFeynmanBootstrap:
    """Test the Gupta-Feynman bootstrap for fracton gravity."""

    def test_order_1_agrees(self):
        """Order 1 (linear): fracton agrees with linearized GR."""
        steps = gupta_feynman_bootstrap(max_order=1)
        assert len(steps) == 1
        assert steps[0].order == 1
        assert steps[0].agrees

    def test_order_2_agrees(self):
        """Order 2 (quadratic): stress-energy coupling is compatible."""
        steps = gupta_feynman_bootstrap(max_order=2)
        assert steps[1].order == 2
        assert steps[1].agrees

    def test_order_3_fails(self):
        """Order 3 (cubic): bootstrap breaks down."""
        steps = gupta_feynman_bootstrap(max_order=3)
        assert steps[2].order == 3
        assert not steps[2].agrees

    def test_order_1_is_trivial(self):
        """Order 1 is trivially satisfied."""
        steps = gupta_feynman_bootstrap(max_order=1)
        assert steps[0].is_trivial

    def test_order_3_is_not_trivial(self):
        """Order 3 is not trivial."""
        steps = gupta_feynman_bootstrap(max_order=3)
        assert not steps[2].is_trivial

    def test_default_gives_3_steps(self):
        """Default max_order=3 gives 3 bootstrap steps."""
        steps = gupta_feynman_bootstrap()
        assert len(steps) == 3

    def test_higher_orders_inherit_failure(self):
        """Orders beyond 3 all inherit the cubic failure."""
        steps = gupta_feynman_bootstrap(max_order=5)
        assert len(steps) == 5
        for step in steps[2:]:
            assert not step.agrees

    def test_orders_1_2_agree_3_plus_fail(self):
        """Orders 1-2 agree, order 3+ fail."""
        steps = gupta_feynman_bootstrap(max_order=4)
        assert all(s.agrees for s in steps[:2])
        assert all(not s.agrees for s in steps[2:])

    def test_invalid_max_order(self):
        """max_order < 1 should raise ValueError."""
        with pytest.raises(ValueError, match="max_order"):
            gupta_feynman_bootstrap(max_order=0)

    def test_cubic_vertex_non_uniqueness_mentioned(self):
        """Cubic step should mention non-unique vertices."""
        steps = gupta_feynman_bootstrap(max_order=3)
        cubic = steps[2]
        assert "non-unique" in cubic.fracton_result.lower() or "multiple" in cubic.fracton_result.lower()

    def test_spin1_instability_mentioned(self):
        """Cubic step should mention spin-1 instability."""
        steps = gupta_feynman_bootstrap(max_order=3)
        cubic = steps[2]
        assert "spin-1" in cubic.fracton_result.lower() or "unstable" in cubic.fracton_result.lower()

    def test_correction_terms_described(self):
        """Each step should have a non-empty correction term description."""
        steps = gupta_feynman_bootstrap(max_order=3)
        for step in steps:
            assert len(step.correction_term) > 10

    def test_deser_mentioned_in_gr_cubic(self):
        """Deser (1970) termination should be mentioned at cubic GR level."""
        steps = gupta_feynman_bootstrap(max_order=3)
        assert "deser" in steps[2].gr_result.lower()


# ===================================================================
# Bootstrap gap assessment (3A.4)
# ===================================================================

class TestBootstrapGap:
    """Test the bootstrap gap assessment."""

    def test_breaks_at_order_3(self):
        """Gap appears at cubic order (order 3)."""
        gap = bootstrap_gap_assessment()
        assert gap.order_where_breaks == 3

    def test_not_closable(self):
        """The gap is not closable by any known procedure."""
        gap = bootstrap_gap_assessment()
        assert not gap.is_closable

    def test_five_obstructions(self):
        """Five convergent obstructions are identified."""
        gap = bootstrap_gap_assessment()
        assert gap.n_obstructions == 5

    def test_is_structural(self):
        """The gap is structural (not merely technical)."""
        gap = bootstrap_gap_assessment()
        assert gap.is_structural

    def test_spin1_unstable(self):
        """Spin-1 sector is identified as unstable."""
        gap = bootstrap_gap_assessment()
        assert gap.spin1_unstable

    def test_hamiltonian_not_bounded(self):
        """Hamiltonian is unbounded from below."""
        gap = bootstrap_gap_assessment()
        assert not gap.hamiltonian_bounded

    def test_vertices_not_unique(self):
        """Cubic vertices are not uniquely determined."""
        gap = bootstrap_gap_assessment()
        assert not gap.vertices_unique

    def test_alternative_route_mentions_adw(self):
        """Alternative route should mention ADW mechanism."""
        gap = bootstrap_gap_assessment()
        assert "adw" in gap.alternative_route.lower() or "fermionic" in gap.alternative_route.lower()

    def test_obstructions_cover_all_types(self):
        """Obstructions should cover algebraic, geometric, kinematic, dynamical, foliation."""
        gap = bootstrap_gap_assessment()
        obs_text = " ".join(gap.obstructions).lower()
        assert "algebraic" in obs_text or "algebra" in obs_text
        assert "geometric" in obs_text or "gromov" in obs_text
        assert "kinematic" in obs_text or "aristotelian" in obs_text
        assert "dynamical" in obs_text or "spin-1" in obs_text
        assert "foliation" in obs_text

    def test_reason_nonempty(self):
        """Reason for breakdown should be substantial."""
        gap = bootstrap_gap_assessment()
        assert len(gap.reason) > 100

    def test_gromov_obstruction_mentioned(self):
        """Gromov's curvature obstruction should be explicitly mentioned."""
        gap = bootstrap_gap_assessment()
        obs_text = " ".join(gap.obstructions).lower()
        assert "gromov" in obs_text

    def test_inonu_wigner_contraction_mentioned(self):
        """Inonu-Wigner contraction should be mentioned in algebraic obstruction."""
        gap = bootstrap_gap_assessment()
        obs_text = " ".join(gap.obstructions).lower()
        assert "contraction" in obs_text


# ===================================================================
# Gravity route comparison (3A.5)
# ===================================================================

class TestGravityRouteComparison:
    """Test comparison of ADW vs fracton routes to gravity."""

    def test_fracton_is_spin2(self):
        """Fracton route produces spin-2 graviton."""
        comp = compare_gravity_routes()
        assert comp.fracton_route.graviton_spin == 2

    def test_adw_is_spin2(self):
        """ADW route produces spin-2 graviton."""
        comp = compare_gravity_routes()
        assert comp.adw_route.graviton_spin == 2

    def test_acoustic_is_spin0(self):
        """Acoustic/BEC route produces only spin-0 (Nordstrom)."""
        comp = compare_gravity_routes()
        assert comp.acoustic_route.graviton_spin == 0

    def test_fracton_breaks_spin0_ceiling(self):
        """Fracton route breaks the Nordstrom spin-0 ceiling."""
        comp = compare_gravity_routes()
        assert comp.fracton_breaks_spin0_ceiling

    def test_adw_has_full_gr(self):
        """ADW route delivers full nonlinear GR."""
        comp = compare_gravity_routes()
        assert comp.adw_has_full_gr

    def test_fracton_linearized_only(self):
        """Fracton route is linearized only."""
        comp = compare_gravity_routes()
        assert comp.fracton_route.is_linearized_only

    def test_adw_not_linearized_only(self):
        """ADW route is NOT limited to linearized gravity."""
        comp = compare_gravity_routes()
        assert not comp.adw_route.is_linearized_only

    def test_fracton_no_full_diffeo(self):
        """Fracton route does NOT produce full diffeomorphism invariance."""
        comp = compare_gravity_routes()
        assert not comp.fracton_route.has_full_diffeo

    def test_adw_has_full_diffeo(self):
        """ADW route produces full diffeomorphism invariance."""
        comp = compare_gravity_routes()
        assert comp.adw_route.has_full_diffeo

    def test_fracton_extra_modes_unstable(self):
        """Fracton extra modes (spin-1) are unstable."""
        comp = compare_gravity_routes()
        assert not comp.fracton_route.extra_modes_stable

    def test_adw_extra_modes_stable(self):
        """ADW extra modes (torsion) are stable."""
        comp = compare_gravity_routes()
        assert comp.adw_route.extra_modes_stable

    def test_fracton_no_fermions_required(self):
        """Fracton route does NOT require fermions."""
        comp = compare_gravity_routes()
        assert not comp.fracton_route.requires_fermions

    def test_adw_requires_fermions(self):
        """ADW route REQUIRES fermions."""
        comp = compare_gravity_routes()
        assert comp.adw_route.requires_fermions

    def test_acoustic_no_fermions_required(self):
        """Acoustic route does NOT require fermions."""
        comp = compare_gravity_routes()
        assert not comp.acoustic_route.requires_fermions

    def test_advantages_both_routes(self):
        """Both routes should have listed advantages."""
        comp = compare_gravity_routes()
        assert len(comp.advantages["fracton"]) >= 3
        assert len(comp.advantages["adw"]) >= 3

    def test_obstacles_both_routes(self):
        """Both routes should have listed obstacles."""
        comp = compare_gravity_routes()
        assert len(comp.obstacles["fracton"]) >= 3
        assert len(comp.obstacles["adw"]) >= 3

    def test_complementarity_assessment_nonempty(self):
        """Complementarity assessment should be substantial."""
        comp = compare_gravity_routes()
        assert len(comp.complementarity_assessment) > 100

    def test_volovik_two_step_mentioned(self):
        """Volovik's two-step picture should be mentioned."""
        comp = compare_gravity_routes()
        assert "volovik" in comp.complementarity_assessment.lower()

    def test_either_route_sufficient_via_adw(self):
        """At least one route (ADW) is sufficient for full GR."""
        comp = compare_gravity_routes()
        assert comp.either_route_sufficient

    def test_gravity_hierarchy(self):
        """Gravity hierarchy: acoustic < fracton < ADW."""
        comp = compare_gravity_routes()
        # Acoustic: spin-0, linearized
        assert comp.acoustic_route.graviton_spin == 0
        # Fracton: spin-2, linearized
        assert comp.fracton_route.graviton_spin == 2
        assert comp.fracton_route.is_linearized_only
        # ADW: spin-2, full nonlinear
        assert comp.adw_route.graviton_spin == 2
        assert not comp.adw_route.is_linearized_only


# ===================================================================
# Non-Abelian fracton analysis (3B)
# ===================================================================

class TestNonAbelianFractonAnalysis:
    """Test the non-Abelian fracton analysis (top-level function)."""

    def test_not_compatible_with_yang_mills(self):
        """Non-Abelian fracton is NOT compatible with Yang-Mills."""
        result = non_abelian_fracton_analysis()
        assert not result.is_compatible_with_yang_mills

    def test_route_not_viable(self):
        """The fracton route to Yang-Mills is not viable."""
        result = non_abelian_fracton_analysis()
        assert not result.route_viable

    def test_obstruction_nonempty(self):
        """Obstruction description should be substantial."""
        result = non_abelian_fracton_analysis()
        assert len(result.obstruction) > 100

    def test_algebra_structure_described(self):
        """Algebra structure should be described."""
        result = non_abelian_fracton_analysis()
        assert len(result.algebra_structure) > 50

    def test_wxy_analysis_present(self):
        """Wang-Xu-Yau analysis should be present."""
        result = non_abelian_fracton_analysis()
        assert len(result.wxy_analysis) > 50

    def test_bb_analysis_present(self):
        """Bulmash-Barkeshli analysis should be present."""
        result = non_abelian_fracton_analysis()
        assert len(result.bulmash_barkeshli_analysis) > 50


# ===================================================================
# Wang-Xu-Yau theory (3B.1-3B.2)
# ===================================================================

class TestWangXuYauTheory:
    """Test Wang-Xu-Yau non-Abelian tensor gauge theory."""

    def test_su2_gauge_dim(self):
        """SU(2) gauge group has dim = 3."""
        wxy = wang_xu_yau_theory("SU(2)")
        assert wxy.gauge_group_dim == 3

    def test_su3_gauge_dim(self):
        """SU(3) gauge group has dim = 8."""
        wxy = wang_xu_yau_theory("SU(3)")
        assert wxy.gauge_group_dim == 8

    def test_u1_gauge_dim(self):
        """U(1) gauge group has dim = 1."""
        wxy = wang_xu_yau_theory("U(1)")
        assert wxy.gauge_group_dim == 1

    def test_non_abelian_fracton_type(self):
        """WXY theories have AlgebraType.NON_ABELIAN_FRACTON."""
        wxy = wang_xu_yau_theory("SU(2)")
        assert wxy.algebra_type == AlgebraType.NON_ABELIAN_FRACTON

    def test_derivative_order_two(self):
        """WXY gauge transformation has derivative order 2."""
        wxy = wang_xu_yau_theory("SU(2)")
        assert wxy.derivative_order == 2

    def test_gauge_is_non_abelian(self):
        """WXY gauge transformation IS non-Abelian in color."""
        wxy = wang_xu_yau_theory("SU(2)")
        assert not wxy.is_abelian_gauge

    def test_no_non_abelian_fusion(self):
        """WXY non-Abelian structure is from gauge, not fusion."""
        wxy = wang_xu_yau_theory("SU(2)")
        assert not wxy.has_non_abelian_fusion

    def test_source_is_gauge_transformation(self):
        """Source of non-Abelian structure is gauge transformation."""
        wxy = wang_xu_yau_theory("SU(2)")
        assert wxy.source_of_non_abelian == NonAbelianSourceType.GAUGE_TRANSFORMATION

    def test_not_yang_mills_compatible(self):
        """WXY is NOT Yang-Mills compatible (derivative structure differs)."""
        wxy = wang_xu_yau_theory("SU(2)")
        assert not wxy.is_yang_mills_compatible

    def test_scalar_gauge_parameters(self):
        """WXY has dim(G) SCALAR gauge parameters."""
        wxy = wang_xu_yau_theory("SU(3)")
        assert wxy.n_gauge_parameters == 8  # dim(SU(3))

    def test_field_components_su2(self):
        """SU(2) in 3D: 3 * 6 = 18 field components."""
        wxy = wang_xu_yau_theory("SU(2)")
        assert wxy.field_components == 18  # 3 colors * 6 symmetric

    def test_field_components_su3(self):
        """SU(3) in 3D: 8 * 6 = 48 field components."""
        wxy = wang_xu_yau_theory("SU(3)")
        assert wxy.field_components == 48  # 8 colors * 6 symmetric

    def test_invalid_gauge_group(self):
        """Invalid gauge group should raise ValueError."""
        with pytest.raises(ValueError, match="not in supported"):
            wang_xu_yau_theory("SO(10)")

    def test_gauge_transformation_description(self):
        """Gauge transformation should be described with dd structure."""
        wxy = wang_xu_yau_theory("SU(2)")
        desc = wxy.gauge_transformation_description
        assert "partial_i partial_j" in desc


# ===================================================================
# Bulmash-Barkeshli theory (3B.2)
# ===================================================================

class TestBulmashBarkeshliTheory:
    """Test Bulmash-Barkeshli non-Abelian fracton model."""

    def test_gauge_is_abelian(self):
        """BB model has Abelian gauge structure."""
        bb = bulmash_barkeshli_theory()
        assert bb.is_abelian_gauge

    def test_has_non_abelian_fusion(self):
        """BB model has non-Abelian fusion rules."""
        bb = bulmash_barkeshli_theory()
        assert bb.has_non_abelian_fusion

    def test_algebra_type_is_fusion(self):
        """BB algebra type is FUSION_NON_ABELIAN."""
        bb = bulmash_barkeshli_theory()
        assert bb.algebra_type == AlgebraType.FUSION_NON_ABELIAN

    def test_source_is_fusion_rules(self):
        """Source of non-Abelian structure is fusion rules."""
        bb = bulmash_barkeshli_theory()
        assert bb.source_of_non_abelian == NonAbelianSourceType.FUSION_RULES

    def test_not_yang_mills_compatible(self):
        """BB model is NOT Yang-Mills compatible."""
        bb = bulmash_barkeshli_theory()
        assert not bb.is_yang_mills_compatible

    def test_single_gauge_parameter(self):
        """BB model has 1 scalar gauge parameter (Abelian)."""
        bb = bulmash_barkeshli_theory()
        assert bb.n_gauge_parameters == 1

    def test_derivative_order_two(self):
        """BB gauge transformation has derivative order 2."""
        bb = bulmash_barkeshli_theory()
        assert bb.derivative_order == 2


# ===================================================================
# Standard Yang-Mills comparison (3B.3)
# ===================================================================

class TestStandardYangMills:
    """Test standard Yang-Mills for comparison."""

    def test_yang_mills_algebra_type(self):
        """Standard YM has AlgebraType.YANG_MILLS."""
        ym = standard_yang_mills("SU(3)")
        assert ym.algebra_type == AlgebraType.YANG_MILLS

    def test_derivative_order_one(self):
        """YM gauge transformation has derivative order 1 (single partial_mu)."""
        ym = standard_yang_mills("SU(3)")
        assert ym.derivative_order == 1

    def test_is_yang_mills_compatible(self):
        """YM is compatible with itself (tautologically)."""
        ym = standard_yang_mills("SU(3)")
        assert ym.is_yang_mills_compatible

    def test_su3_field_components(self):
        """SU(3) in 4D: 8 * 4 = 32 field components."""
        ym = standard_yang_mills("SU(3)")
        assert ym.field_components == 32

    def test_su2_field_components(self):
        """SU(2) in 4D: 3 * 4 = 12 field components."""
        ym = standard_yang_mills("SU(2)")
        assert ym.field_components == 12

    def test_gauge_is_non_abelian(self):
        """Standard YM gauge is non-Abelian."""
        ym = standard_yang_mills("SU(3)")
        assert not ym.is_abelian_gauge

    def test_source_is_gauge_transformation(self):
        """YM non-Abelian structure is from gauge transformation."""
        ym = standard_yang_mills("SU(3)")
        assert ym.source_of_non_abelian == NonAbelianSourceType.GAUGE_TRANSFORMATION


# ===================================================================
# Derivative structure comparison (3B.3-3B.4)
# ===================================================================

class TestDerivativeStructure:
    """Test derivative structure obstruction."""

    def test_fracton_derivative_order(self):
        """Fracton uses 2nd-order derivatives."""
        comp = derivative_structure_comparison()
        assert comp.fracton_derivative_order == 2

    def test_yang_mills_derivative_order(self):
        """Yang-Mills uses 1st-order derivatives."""
        comp = derivative_structure_comparison()
        assert comp.yang_mills_derivative_order == 1

    def test_derivative_order_mismatch(self):
        """Derivative order mismatch is 1."""
        comp = derivative_structure_comparison()
        assert comp.derivative_order_mismatch == 1

    def test_commutator_does_not_match(self):
        """Commutator structures do NOT match."""
        comp = derivative_structure_comparison()
        assert not comp.commutator_structure_matches

    def test_closure_not_satisfied(self):
        """Gauge closure is NOT satisfied on curved manifolds."""
        comp = derivative_structure_comparison()
        assert not comp.closure_condition_satisfied

    def test_curvature_obstruction_exists(self):
        """Curvature obstruction (Gromov) IS present."""
        comp = derivative_structure_comparison()
        assert comp.curvature_obstruction

    def test_not_compatible(self):
        """Derivative structures are NOT compatible."""
        comp = derivative_structure_comparison()
        assert not comp.is_compatible


# ===================================================================
# Yang-Mills compatibility analysis (3B.4)
# ===================================================================

class TestYangMillsCompatibility:
    """Test full Yang-Mills compatibility analysis."""

    def test_not_compatible(self):
        """Non-Abelian fracton is NOT Yang-Mills compatible."""
        compat = analyze_non_abelian_compatibility()
        assert not compat.is_compatible

    def test_structural_incompatibility(self):
        """Incompatibility is structural (>= 3 obstructions)."""
        compat = analyze_non_abelian_compatibility()
        assert compat.is_structural

    def test_four_obstructions(self):
        """Four independent obstructions are identified."""
        compat = analyze_non_abelian_compatibility()
        assert compat.n_obstructions == 4

    def test_obstruction_summary_substantial(self):
        """Obstruction summary should be substantial."""
        compat = analyze_non_abelian_compatibility()
        assert len(compat.obstruction_summary) > 200

    def test_algebra_description_substantial(self):
        """Algebra description should be substantial."""
        compat = analyze_non_abelian_compatibility()
        assert len(compat.algebra_description) > 100

    def test_wxy_assessment_substantial(self):
        """WXY assessment should be substantial."""
        compat = analyze_non_abelian_compatibility()
        assert len(compat.wxy_assessment) > 100

    def test_bb_assessment_substantial(self):
        """BB assessment should be substantial."""
        compat = analyze_non_abelian_compatibility()
        assert len(compat.bb_assessment) > 100

    def test_obstructions_cover_key_issues(self):
        """Obstructions should cover derivative, commutator, closure, representation."""
        compat = analyze_non_abelian_compatibility()
        obs_text = " ".join(compat.obstructions).lower()
        assert "derivative" in obs_text
        assert "commutator" in obs_text
        assert "closure" in obs_text or "gromov" in obs_text
        assert "representation" in obs_text or "scalar" in obs_text

    def test_derivative_comparison_embedded(self):
        """Derivative comparison should be embedded in the result."""
        compat = analyze_non_abelian_compatibility()
        assert compat.derivative_comparison.fracton_derivative_order == 2
        assert compat.derivative_comparison.yang_mills_derivative_order == 1


# ===================================================================
# Cross-consistency with Phase 4 Wave 2 modules
# ===================================================================

class TestCrossConsistency:
    """Test consistency between gravity/non-Abelian and existing fracton modules."""

    def test_fracton_route_fracton_module_agreement(self):
        """Fracton route properties agree with fracton SK-EFT module."""
        comp = compare_gravity_routes()
        # Fracton route is purely bosonic
        assert not comp.fracton_route.requires_fermions
        # Fracton route is linearized only
        assert comp.fracton_route.is_linearized_only

    def test_bootstrap_gap_count_matches_obstructions(self):
        """Bootstrap gap should have exactly 5 obstructions."""
        gap = bootstrap_gap_assessment()
        assert gap.n_obstructions == 5

    def test_non_abelian_result_from_compatibility(self):
        """NonAbelianResult.from_compatibility should produce consistent result."""
        compat = analyze_non_abelian_compatibility()
        result = NonAbelianResult.from_compatibility(compat)
        assert result.is_compatible_with_yang_mills == compat.is_compatible
        assert result.obstruction == compat.obstruction_summary

    def test_wxy_vs_ym_derivative_mismatch(self):
        """WXY and standard YM should differ in derivative order."""
        wxy = wang_xu_yau_theory("SU(2)")
        ym = standard_yang_mills("SU(2)")
        assert wxy.derivative_order != ym.derivative_order
        assert wxy.derivative_order == 2
        assert ym.derivative_order == 1

    def test_wxy_vs_bb_gauge_type_difference(self):
        """WXY and BB have different sources of non-Abelian structure."""
        wxy = wang_xu_yau_theory("SU(2)")
        bb = bulmash_barkeshli_theory()
        assert wxy.source_of_non_abelian != bb.source_of_non_abelian
        assert not wxy.is_abelian_gauge  # WXY: non-Abelian gauge
        assert bb.is_abelian_gauge       # BB: Abelian gauge

    def test_all_gravity_routes_have_uv_completion(self):
        """All gravity routes should specify a UV completion."""
        comp = compare_gravity_routes()
        assert len(comp.acoustic_route.uv_completion) > 10
        assert len(comp.fracton_route.uv_completion) > 10
        assert len(comp.adw_route.uv_completion) > 10

    def test_package_imports(self):
        """All public names should be importable from src.fracton."""
        from src.fracton import (
            LinearizedEquivalence,
            BootstrapStep,
            BootstrapGap,
            GravityRouteComparison,
            NonAbelianResult,
            NonAbelianFractonGauge,
            YangMillsCompatibility,
            DerivativeStructureComparison,
            linearized_equivalence,
            gupta_feynman_bootstrap,
            bootstrap_gap_assessment,
            compare_gravity_routes,
            non_abelian_fracton_analysis,
            analyze_non_abelian_compatibility,
            wang_xu_yau_theory,
            bulmash_barkeshli_theory,
            standard_yang_mills,
            derivative_structure_comparison,
        )

    def test_enumeration_types_distinct(self):
        """Enum types should have distinct values."""
        assert GaugeSymmetryType.FRACTON_SCALAR.value != GaugeSymmetryType.FULL_DIFFEO.value
        assert ObstructionType.ALGEBRAIC.value != ObstructionType.GEOMETRIC.value
        assert GravityRouteType.FRACTON.value != GravityRouteType.ADW.value
        assert AlgebraType.NON_ABELIAN_FRACTON.value != AlgebraType.YANG_MILLS.value


# ===================================================================
# Bootstrap gap quantification
# ===================================================================

class TestBootstrapGapQuantification:
    """Test quantitative comparison of cubic vertices in GR vs fracton."""

    def test_gr_has_5_structures_in_4d(self):
        """Linearized GR in D=4 has 5 independent cubic vertex structures."""
        result = quantify_bootstrap_gap(spacetime_dim=4)
        assert result.n_gr_structures == 5

    def test_fracton_has_8_structures_in_4d(self):
        """Fracton theory in D=4 has 8 independent cubic vertex structures."""
        result = quantify_bootstrap_gap(spacetime_dim=4)
        assert result.n_fracton_structures == 8

    def test_gap_magnitude_4d(self):
        """Gap magnitude in D=4: |8-5|/5 = 0.6."""
        result = quantify_bootstrap_gap(spacetime_dim=4)
        assert abs(result.gap_magnitude - 0.6) < 1e-10

    def test_gap_percentage_4d(self):
        """Gap as percentage: 60%."""
        result = quantify_bootstrap_gap(spacetime_dim=4)
        assert abs(result.gap_percentage - 60.0) < 1e-10

    def test_three_excess_structures_4d(self):
        """3 excess structures in fracton vs GR in D=4."""
        result = quantify_bootstrap_gap(spacetime_dim=4)
        assert result.n_excess_structures == 3

    def test_not_exact_match(self):
        """GR and fracton do NOT have identical cubic structure in D=4."""
        result = quantify_bootstrap_gap(spacetime_dim=4)
        assert not result.is_exact_match

    def test_nothing_missing_in_fracton(self):
        """All GR structures are present in fracton (subset symmetry)."""
        result = quantify_bootstrap_gap(spacetime_dim=4)
        assert len(result.missing_in_fracton) == 0

    def test_three_extra_in_fracton(self):
        """3 extra structures identified in fracton theory."""
        result = quantify_bootstrap_gap(spacetime_dim=4)
        assert len(result.extra_in_fracton) == 3

    def test_excess_causes_instability(self):
        """Excess structures cause dynamical instability."""
        result = quantify_bootstrap_gap(spacetime_dim=4)
        assert result.excess_causes_instability

    def test_gap_not_closable(self):
        """The gap is NOT closable."""
        result = quantify_bootstrap_gap(spacetime_dim=4)
        assert not result.gap_closable

    def test_gr_coefficients_unique(self):
        """GR cubic vertex coefficients are uniquely fixed."""
        result = quantify_bootstrap_gap(spacetime_dim=4)
        assert result.gr_vertex.coefficients_unique

    def test_fracton_coefficients_not_unique(self):
        """Fracton cubic vertex coefficients are NOT uniquely fixed."""
        result = quantify_bootstrap_gap(spacetime_dim=4)
        assert not result.fracton_vertex.coefficients_unique

    def test_gr_vertex_label(self):
        """GR vertex should be labeled 'GR'."""
        result = quantify_bootstrap_gap(spacetime_dim=4)
        assert result.gr_vertex.theory_label == "GR"

    def test_fracton_vertex_label(self):
        """Fracton vertex should be labeled 'fracton'."""
        result = quantify_bootstrap_gap(spacetime_dim=4)
        assert result.fracton_vertex.theory_label == "fracton"

    def test_fracton_has_higher_derivative_vertices(self):
        """Fracton vertex structures include higher-derivative terms."""
        result = quantify_bootstrap_gap(spacetime_dim=4)
        assert result.fracton_vertex.has_higher_derivative_vertices

    def test_gr_no_higher_derivative_vertices(self):
        """GR vertex structures do NOT include higher-derivative terms."""
        result = quantify_bootstrap_gap(spacetime_dim=4)
        assert not result.gr_vertex.has_higher_derivative_vertices

    def test_extra_structures_mention_spin1(self):
        """Extra structures should mention spin-1 sector."""
        result = quantify_bootstrap_gap(spacetime_dim=4)
        extra_text = " ".join(result.extra_in_fracton).lower()
        assert "spin-1" in extra_text

    def test_extra_structures_mention_instability(self):
        """Extra structures should mention instability."""
        result = quantify_bootstrap_gap(spacetime_dim=4)
        extra_text = " ".join(result.extra_in_fracton).lower()
        assert "instability" in extra_text or "unstable" in extra_text

    def test_extra_structures_mention_4_derivative(self):
        """Extra structures should mention 4-derivative vertices."""
        result = quantify_bootstrap_gap(spacetime_dim=4)
        extra_text = " ".join(result.extra_in_fracton).lower()
        assert "4-derivative" in extra_text

    def test_3d_gr_topological(self):
        """In D=3, GR is topological: 0 cubic vertex structures."""
        result = quantify_bootstrap_gap(spacetime_dim=3)
        assert result.n_gr_structures == 0

    def test_3d_fracton_has_vertices(self):
        """In D=3, fracton still has cubic vertices (propagating DOF)."""
        result = quantify_bootstrap_gap(spacetime_dim=3)
        assert result.n_fracton_structures > 0

    def test_5d_same_gr_structure_count(self):
        """In D=5, GR still has 5 independent cubic structures."""
        result = quantify_bootstrap_gap(spacetime_dim=5)
        assert result.n_gr_structures == 5

    def test_gr_structures_described(self):
        """GR structures should have descriptions."""
        result = quantify_bootstrap_gap(spacetime_dim=4)
        for s in result.gr_vertex.structures:
            assert len(s) > 20

    def test_fracton_structures_described(self):
        """Fracton structures should have descriptions."""
        result = quantify_bootstrap_gap(spacetime_dim=4)
        for s in result.fracton_vertex.structures:
            assert len(s) > 20

    def test_gr_gauge_symmetry_mentions_diffeo(self):
        """GR gauge symmetry description should mention diffeomorphisms."""
        result = quantify_bootstrap_gap(spacetime_dim=4)
        assert "diffeo" in result.gr_vertex.gauge_symmetry_used.lower()

    def test_fracton_gauge_symmetry_mentions_scalar(self):
        """Fracton gauge symmetry description should mention scalar."""
        result = quantify_bootstrap_gap(spacetime_dim=4)
        assert "scalar" in result.fracton_vertex.gauge_symmetry_used.lower()

    def test_consistency_with_bootstrap_gap_assessment(self):
        """Quantification should be consistent with qualitative bootstrap gap."""
        qual = bootstrap_gap_assessment()
        quant = quantify_bootstrap_gap()
        # Both say gap appears at order 3
        assert qual.order_where_breaks == 3
        # Quantitative confirms excess structures exist
        assert quant.n_excess_structures > 0
        # Both say gap is not closable
        assert not qual.is_closable
        assert not quant.gap_closable
