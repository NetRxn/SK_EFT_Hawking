"""Tests for the non-Abelian gauge erasure theorem (Phase 3, Item 1B).

Validates:
1. Gauge group classification (Abelian/non-Abelian/discrete)
2. Higher-form symmetry type assignment
3. Goldstone vs domain wall distinction
4. The erasure theorem: non-Abelian → erased, U(1) → survives
5. Standard Model analysis (SU(3) × SU(2) × U(1))
6. N=4 SYM decisive test
7. Universality across gauge groups
"""

import pytest
from src.gauge_erasure.erasure_theorem import (
    GaugeGroup,
    GaugeGroupType,
    HigherFormSymmetry,
    HydrodynamicFate,
    GaugeErasureResult,
    su,
    u1,
    so,
    is_abelian,
    center_subgroup,
    higher_form_symmetry_type,
    goldstone_or_domain_wall,
    survives_hydrodynamization,
    gauge_erasure_analysis,
    standard_model_analysis,
    n4_sym_analysis,
)


# ═══════════════════════════════════════════════════════════════════
# Group construction
# ═══════════════════════════════════════════════════════════════════

class TestGaugeGroups:
    """Test gauge group constructors and properties."""

    def test_su2(self):
        g = su(2)
        assert g.name == "SU(2)"
        assert g.rank == 2
        assert not g.is_abelian
        assert g.is_continuous
        assert g.center == "Z_2"
        assert g.dim == 3

    def test_su3(self):
        g = su(3)
        assert g.name == "SU(3)"
        assert g.dim == 8
        assert g.center == "Z_3"

    def test_su_n_general(self):
        for N in range(2, 8):
            g = su(N)
            assert g.dim == N**2 - 1
            assert g.center == f"Z_{N}"
            assert not g.is_abelian

    def test_su1_invalid(self):
        with pytest.raises(ValueError):
            su(1)

    def test_u1(self):
        g = u1()
        assert g.is_abelian
        assert g.is_continuous
        assert g.dim == 1
        assert g.center == "U(1)"

    def test_so_groups(self):
        g = so(3)
        assert not g.is_abelian
        assert g.dim == 3

    def test_group_type_classification(self):
        assert u1().group_type == GaugeGroupType.ABELIAN
        assert su(3).group_type == GaugeGroupType.NON_ABELIAN


# ═══════════════════════════════════════════════════════════════════
# Higher-form symmetry
# ═══════════════════════════════════════════════════════════════════

class TestHigherFormSymmetry:
    """Test higher-form symmetry classification."""

    def test_u1_has_continuous_1form(self):
        """U(1) has continuous magnetic 1-form symmetry."""
        assert higher_form_symmetry_type(u1()) == HigherFormSymmetry.CONTINUOUS_1FORM

    def test_su_n_has_discrete_1form(self):
        """SU(N) has only discrete Z_N 1-form center symmetry."""
        for N in range(2, 6):
            assert higher_form_symmetry_type(su(N)) == HigherFormSymmetry.DISCRETE_1FORM

    def test_so_n_has_discrete_1form(self):
        """SO(N) has discrete 1-form center symmetry."""
        for N in [3, 4, 5, 10]:
            assert higher_form_symmetry_type(so(N)) == HigherFormSymmetry.DISCRETE_1FORM

    def test_higher_form_must_be_abelian(self):
        """The key theorem: higher-form symmetries must be Abelian.

        Codimension >1 operators commute → symmetry group is Abelian.
        Non-Abelian groups can only have discrete center as higher-form symmetry.
        """
        # Every non-Abelian group gets DISCRETE, not CONTINUOUS
        non_abelian_groups = [su(2), su(3), su(5), so(3), so(10)]
        for g in non_abelian_groups:
            hf = higher_form_symmetry_type(g)
            assert hf != HigherFormSymmetry.CONTINUOUS_1FORM, (
                f"{g.name}: non-Abelian group should not have continuous 1-form symmetry"
            )


# ═══════════════════════════════════════════════════════════════════
# Goldstone vs domain wall
# ═══════════════════════════════════════════════════════════════════

class TestGoldstoneDomainWall:
    """Test the Goldstone/domain wall distinction."""

    def test_continuous_gives_goldstone(self):
        """Continuous symmetry breaking → Goldstone boson."""
        assert goldstone_or_domain_wall(HigherFormSymmetry.CONTINUOUS_1FORM) == \
            HydrodynamicFate.GOLDSTONE_BOSON

    def test_discrete_gives_domain_wall(self):
        """Discrete symmetry breaking → domain wall, NOT Goldstone."""
        assert goldstone_or_domain_wall(HigherFormSymmetry.DISCRETE_1FORM) == \
            HydrodynamicFate.DOMAIN_WALL

    def test_none_gives_erasure(self):
        """No symmetry → complete erasure."""
        assert goldstone_or_domain_wall(HigherFormSymmetry.NONE) == \
            HydrodynamicFate.ERASURE


# ═══════════════════════════════════════════════════════════════════
# The erasure theorem
# ═══════════════════════════════════════════════════════════════════

class TestErasureTheorem:
    """Test the main theorem: non-Abelian gauge DOF are erased."""

    def test_u1_survives(self):
        """U(1) gauge structure survives hydrodynamization.

        The photon is the 1-form Goldstone boson of spontaneously broken
        magnetic U(1)^{(1)} symmetry (Grozdanov-Hofman-Iqbal).
        """
        assert survives_hydrodynamization(u1())

    def test_su_n_erased(self):
        """SU(N) gauge structure is erased for all N ≥ 2.

        Z_N center → domain walls, not Goldstone bosons → no hydro modes.
        """
        for N in range(2, 10):
            assert not survives_hydrodynamization(su(N)), (
                f"SU({N}) should be erased, not survive"
            )

    def test_so_n_erased(self):
        """SO(N) gauge structure is erased."""
        for N in [3, 4, 5, 10]:
            assert not survives_hydrodynamization(so(N))

    def test_erasure_is_structural(self):
        """Erasure depends only on Abelianness, not group details.

        All non-Abelian groups are erased regardless of rank, dimension,
        or center structure. This is because the obstruction is at the
        level of higher-form symmetry commutativity.
        """
        # All non-Abelian groups: erased
        for g in [su(2), su(3), su(5), su(10), so(3), so(10)]:
            result = gauge_erasure_analysis(g)
            assert not result.survives
            assert result.fate == HydrodynamicFate.DOMAIN_WALL

        # All Abelian groups: survive
        result = gauge_erasure_analysis(u1())
        assert result.survives
        assert result.fate == HydrodynamicFate.GOLDSTONE_BOSON


# ═══════════════════════════════════════════════════════════════════
# Standard Model
# ═══════════════════════════════════════════════════════════════════

class TestStandardModel:
    """Test Standard Model gauge group analysis."""

    def test_sm_analysis(self):
        """SU(3) × SU(2) × U(1): only U(1) survives."""
        results = standard_model_analysis()
        assert not results['SU(3)_c'].survives  # QCD: erased
        assert not results['SU(2)_L'].survives  # Weak: erased
        assert results['U(1)_Y'].survives       # Hypercharge: survives

    def test_sm_only_photon_survives(self):
        """After EWSB, only the photon (from U(1)_EM) survives."""
        results = standard_model_analysis()
        surviving = [k for k, v in results.items() if v.survives]
        assert surviving == ['U(1)_Y']


# ═══════════════════════════════════════════════════════════════════
# N=4 SYM decisive test
# ═══════════════════════════════════════════════════════════════════

class TestN4SYM:
    """Test the N=4 SYM analysis as the decisive case."""

    def test_n4_sym_erased(self):
        """N=4 SYM is non-confining yet gauge DOF are still erased.

        This proves erasure is structural (higher-form commutativity),
        not dynamical (confinement).
        """
        result = n4_sym_analysis()
        assert not result.survives

    def test_n4_sym_explanation_mentions_confinement(self):
        """The explanation should note that erasure is NOT from confinement."""
        result = n4_sym_analysis()
        assert "non-confining" in result.explanation


# ═══════════════════════════════════════════════════════════════════
# Full analysis output
# ═══════════════════════════════════════════════════════════════════

class TestFullAnalysis:
    """Test the complete gauge_erasure_analysis function."""

    def test_analysis_returns_all_fields(self):
        result = gauge_erasure_analysis(su(3))
        assert isinstance(result, GaugeErasureResult)
        assert result.group.name == "SU(3)"
        assert not result.is_abelian
        assert result.higher_form_type == HigherFormSymmetry.DISCRETE_1FORM
        assert result.fate == HydrodynamicFate.DOMAIN_WALL
        assert not result.survives
        assert len(result.explanation) > 0

    def test_u1_analysis_mentions_photonization(self):
        """U(1) analysis should reference the photonization theorem."""
        result = gauge_erasure_analysis(u1())
        assert "Grozdanov-Hofman-Iqbal" in result.explanation
        assert "photon" in result.explanation.lower() or "Goldstone" in result.explanation

    def test_non_abelian_analysis_mentions_domain_walls(self):
        """Non-Abelian analysis should explain domain wall mechanism."""
        result = gauge_erasure_analysis(su(3))
        assert "domain wall" in result.explanation.lower()
        assert "Z_3" in result.explanation
