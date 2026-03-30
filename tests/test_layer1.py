"""Tests for Layer 1 categorical infrastructure (Phase 5 Wave 4A).

Validates:
1. Constants: CATEGORY_HIERARCHY, FUSION_EXAMPLES, LAYER1_CONNECTIONS
2. Formulas: quantum_dimension, global_dimension_squared, fusion_multiplicity,
             categorical_trace, pivotal_indicator
3. Fusion example consistency (D² = |G| for group categories)
4. Fibonacci golden ratio identity
5. Lean module structure (KLinearCategory, SphericalCategory)
"""

import math
import pytest
import numpy as np

from src.core.constants import (
    CATEGORY_HIERARCHY,
    FUSION_EXAMPLES,
    LAYER1_CONNECTIONS,
)
from src.core.formulas import (
    quantum_dimension,
    global_dimension_squared,
    fusion_multiplicity,
    categorical_trace,
    pivotal_indicator,
)


class TestCategoryConstants:
    """Test the categorical infrastructure constants."""

    def test_hierarchy_keys(self):
        assert 'mathlib_existing' in CATEGORY_HIERARCHY
        assert 'wave4a_new' in CATEGORY_HIERARCHY
        assert 'wave4b_new' in CATEGORY_HIERARCHY

    def test_mathlib_existing_count(self):
        assert len(CATEGORY_HIERARCHY['mathlib_existing']) == 9

    def test_wave4a_new_count(self):
        assert len(CATEGORY_HIERARCHY['wave4a_new']) == 5

    def test_wave4b_new_count(self):
        assert len(CATEGORY_HIERARCHY['wave4b_new']) == 5

    def test_pivotal_in_wave4a(self):
        assert 'PivotalCategory' in CATEGORY_HIERARCHY['wave4a_new']

    def test_spherical_in_wave4a(self):
        assert 'SphericalCategory' in CATEGORY_HIERARCHY['wave4a_new']

    def test_fusion_in_wave4b(self):
        assert 'FusionCategory' in CATEGORY_HIERARCHY['wave4b_new']

    def test_drinfeld_center_existing(self):
        assert 'DrinfeldCenter' in CATEGORY_HIERARCHY['mathlib_existing']

    def test_rigid_existing(self):
        assert 'RigidCategory' in CATEGORY_HIERARCHY['mathlib_existing']


class TestFusionExamples:
    """Test the fusion category example data."""

    def test_five_examples(self):
        assert len(FUSION_EXAMPLES) == 5

    def test_vec_z2_simples(self):
        assert FUSION_EXAMPLES['Vec_Z2']['n_simples'] == 2

    def test_vec_z2_global_dim(self):
        assert FUSION_EXAMPLES['Vec_Z2']['global_dim_sq'] == 2

    def test_vec_z3_simples(self):
        assert FUSION_EXAMPLES['Vec_Z3']['n_simples'] == 3

    def test_vec_z3_global_dim(self):
        assert FUSION_EXAMPLES['Vec_Z3']['global_dim_sq'] == 3

    def test_vec_s3_simples(self):
        assert FUSION_EXAMPLES['Vec_S3']['n_simples'] == 6

    def test_vec_s3_global_dim(self):
        assert FUSION_EXAMPLES['Vec_S3']['global_dim_sq'] == 6

    def test_rep_s3_simples(self):
        assert FUSION_EXAMPLES['Rep_S3']['n_simples'] == 3

    def test_rep_s3_global_dim(self):
        """D² = 1² + 1² + 2² = 6 = |S₃|"""
        assert FUSION_EXAMPLES['Rep_S3']['global_dim_sq'] == 6

    def test_rep_s3_dims(self):
        assert FUSION_EXAMPLES['Rep_S3']['quantum_dims'] == [1, 1, 2]

    def test_fibonacci_simples(self):
        assert FUSION_EXAMPLES['Fibonacci']['n_simples'] == 2

    def test_fibonacci_golden_ratio(self):
        phi = (1 + math.sqrt(5)) / 2
        assert abs(FUSION_EXAMPLES['Fibonacci']['quantum_dims'][1] - phi) < 1e-10

    def test_fibonacci_global_dim(self):
        """D² = 1 + φ² = 1 + φ + 1 = 2 + φ = (5+√5)/2"""
        expected = (5 + math.sqrt(5)) / 2
        assert abs(FUSION_EXAMPLES['Fibonacci']['global_dim_sq'] - expected) < 1e-10


class TestGlobalDimConsistency:
    """Verify D² = Σ d_i² matches stored values for all examples."""

    @pytest.mark.parametrize("name", list(FUSION_EXAMPLES.keys()))
    def test_global_dim_from_quantum_dims(self, name):
        ex = FUSION_EXAMPLES[name]
        computed = sum(d**2 for d in ex['quantum_dims'])
        assert abs(computed - ex['global_dim_sq']) < 1e-10

    def test_vec_G_global_dim_equals_group_order(self):
        """For Vec_G, D² = |G| (all dims are 1)."""
        for name in ['Vec_Z2', 'Vec_Z3', 'Vec_S3']:
            ex = FUSION_EXAMPLES[name]
            assert all(d == 1 for d in ex['quantum_dims'])
            assert ex['global_dim_sq'] == ex['n_simples']


class TestLayer1Connections:
    """Test the physics connection registry."""

    def test_four_connections(self):
        assert len(LAYER1_CONNECTIONS) == 4

    def test_gauge_erasure_connection(self):
        assert 'gauge_erasure' in LAYER1_CONNECTIONS

    def test_fracton_hydro_connection(self):
        assert 'fracton_hydro' in LAYER1_CONNECTIONS

    def test_chirality_wall_connection(self):
        assert 'chirality_wall' in LAYER1_CONNECTIONS


class TestQuantumDimension:
    """Test the quantum dimension formula."""

    def test_dim_one(self):
        assert quantum_dimension(1.0) == 1.0

    def test_dim_two(self):
        assert quantum_dimension(2.0) == 2.0

    def test_dim_golden_ratio(self):
        phi = (1 + math.sqrt(5)) / 2
        assert abs(quantum_dimension(phi) - phi) < 1e-10


class TestGlobalDimensionSquared:
    """Test the global dimension squared formula."""

    def test_vec_z2(self):
        assert global_dimension_squared([1, 1]) == 2

    def test_vec_z3(self):
        assert global_dimension_squared([1, 1, 1]) == 3

    def test_rep_s3(self):
        assert global_dimension_squared([1, 1, 2]) == 6

    def test_fibonacci(self):
        phi = (1 + math.sqrt(5)) / 2
        expected = (5 + math.sqrt(5)) / 2  # 1 + φ² = 2 + φ
        assert abs(global_dimension_squared([1, phi]) - expected) < 1e-10

    def test_empty(self):
        assert global_dimension_squared([]) == 0

    def test_single(self):
        assert global_dimension_squared([3]) == 9


class TestFusionMultiplicity:
    """Test the fusion multiplicity formula."""

    def test_kronecker(self):
        """Vec_G fusion: N^k_{g,h} = δ_{k,gh}"""
        assert fusion_multiplicity({'gh': 1}) == 1

    def test_rep_decomposition(self):
        """Rep(S₃): standard ⊗ standard = trivial + sign + standard"""
        assert fusion_multiplicity({'trivial': 1, 'sign': 1, 'standard': 1}) == 3


class TestCategoricalTrace:
    """Test the categorical trace formula."""

    def test_trace_identity_2x2(self):
        assert categorical_trace([1, 1]) == 2

    def test_trace_zero(self):
        assert categorical_trace([0, 0, 0]) == 0

    def test_trace_general(self):
        assert categorical_trace([3, -1, 2]) == 4


class TestPivotalIndicator:
    """Test the pivotal/spherical indicator."""

    def test_spherical(self):
        assert pivotal_indicator(3.0, 3.0) is True

    def test_not_spherical(self):
        assert pivotal_indicator(3.0, 4.0) is False

    def test_near_spherical(self):
        assert pivotal_indicator(1.0, 1.0 + 1e-15) is True

    def test_fibonacci_spherical(self):
        """Fibonacci category is spherical: left=right traces."""
        phi = (1 + math.sqrt(5)) / 2
        assert pivotal_indicator(phi, phi) is True


class TestGoldenRatioIdentity:
    """Test the algebraic identity φ² = φ + 1."""

    def test_golden_ratio_squared(self):
        phi = (1 + math.sqrt(5)) / 2
        assert abs(phi**2 - (phi + 1)) < 1e-10

    def test_fibonacci_dim_identity(self):
        """1² + φ² = 2 + φ"""
        phi = (1 + math.sqrt(5)) / 2
        assert abs(1 + phi**2 - (2 + phi)) < 1e-10


class TestLeanModuleStructure:
    """Test that the new Lean modules exist and have expected structure."""

    def test_klinear_exists(self):
        import os
        path = os.path.join(os.path.dirname(__file__), '..', 'lean',
                           'SKEFTHawking', 'KLinearCategory.lean')
        assert os.path.exists(path)

    def test_spherical_exists(self):
        import os
        path = os.path.join(os.path.dirname(__file__), '..', 'lean',
                           'SKEFTHawking', 'SphericalCategory.lean')
        assert os.path.exists(path)

    def test_klinear_has_theorems(self):
        import os
        path = os.path.join(os.path.dirname(__file__), '..', 'lean',
                           'SKEFTHawking', 'KLinearCategory.lean')
        with open(path) as f:
            content = f.read()
        theorem_count = content.count('\ntheorem ')
        assert theorem_count >= 15  # at least 15 theorems

    def test_spherical_has_theorems(self):
        import os
        path = os.path.join(os.path.dirname(__file__), '..', 'lean',
                           'SKEFTHawking', 'SphericalCategory.lean')
        with open(path) as f:
            content = f.read()
        theorem_count = content.count('\ntheorem ')
        assert theorem_count >= 15  # at least 15 theorems

    def test_klinear_has_pivotal(self):
        """KLinearCategory should have semisimple infrastructure."""
        import os
        path = os.path.join(os.path.dirname(__file__), '..', 'lean',
                           'SKEFTHawking', 'KLinearCategory.lean')
        with open(path) as f:
            content = f.read()
        assert 'SemisimpleCategory' in content

    def test_spherical_has_pivotal(self):
        """SphericalCategory should have pivotal + spherical definitions."""
        import os
        path = os.path.join(os.path.dirname(__file__), '..', 'lean',
                           'SKEFTHawking', 'SphericalCategory.lean')
        with open(path) as f:
            content = f.read()
        assert 'PivotalCategory' in content
        assert 'SphericalCategory' in content
