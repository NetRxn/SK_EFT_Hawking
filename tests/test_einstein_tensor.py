"""Phase 6f Wave 2 — Classical-GR Einstein tensor tests.

Cross-layer agreement between Python ``formulas.py`` Einstein-tensor
helpers and the Lean ``EinsteinTensor.lean`` substantive theorems.

Organized into:

- TestEinsteinTensorBasic — definition agrees pointwise; symmetry holds
  when Ricci + metric are symmetric.
- TestTraceIdentity — ``G^μ_μ = -R`` in 4D (Lean
  ``einsteinTensor_trace_eq_neg_scalar``).
- TestConstantKWitness — for constant-K Riemann, ``G_{μν} = -3K g_{μν}``
  (Lean ``constantSectional_einsteinTensor_eq``).
- TestVacuumCharacterization — ``G = 0 ↔ Ric = 0`` in 4D (Lean
  ``einsteinTensor_zero_iff_ricci_zero``).
- TestDeSitterLambda — ``Λ = 3K`` for the Λ-vacuum equation (Lean
  ``constantSectional_lambda_vacuum_iff``).
- TestMinkowskiCrossBridge — ``Σ_{μν} η^{μν} η_{μν} = 4`` (Lean
  ``minkowski_dim_contraction``); flat-Minkowski Einstein tensor is
  zero at K=0.
"""

from __future__ import annotations

import pytest

from src.core.formulas import (
    riemann_constant_sectional_curvature,
    ricci_from_riemann,
    scalar_curvature_from_ricci,
    constant_sectional_ricci_predicted,
    constant_sectional_scalar_predicted,
    einstein_tensor_from_ricci,
    einstein_tensor_trace,
    constant_sectional_einstein_tensor_predicted,
    de_sitter_lambda_from_K,
    minkowski_dim_contraction_value,
)


def minkowski_metric():
    """Signature `(-,+,+,+)` Minkowski metric, matches LinearizedEFE.η."""
    return [
        [-1.0, 0.0, 0.0, 0.0],
        [0.0, 1.0, 0.0, 0.0],
        [0.0, 0.0, 1.0, 0.0],
        [0.0, 0.0, 0.0, 1.0],
    ]


def euclidean_metric():
    return [
        [1.0, 0.0, 0.0, 0.0],
        [0.0, 1.0, 0.0, 0.0],
        [0.0, 0.0, 1.0, 0.0],
        [0.0, 0.0, 0.0, 1.0],
    ]


# η is self-inverse for the (-,+,+,+) Minkowski (η² = I).
def minkowski_inverse():
    return minkowski_metric()


def constant_K_einstein_pipeline(K, g):
    """Full pipeline: K → Riemann → Ricci → R → G."""
    R = riemann_constant_sectional_curvature(K, g)
    Ric = ricci_from_riemann(R)
    g_inv = g  # tests use self-inverse metrics
    R_scalar = scalar_curvature_from_ricci(Ric, g_inv)
    G = einstein_tensor_from_ricci(Ric, R_scalar, g)
    return Ric, R_scalar, G


class TestEinsteinTensorBasic:
    """Definition pointwise; symmetry under Ricci + metric symmetry."""

    def test_definition_pointwise(self):
        Ric = [[1.0, 2.0, 3.0, 4.0], [2.0, 5.0, 6.0, 7.0],
               [3.0, 6.0, 8.0, 9.0], [4.0, 7.0, 9.0, 10.0]]
        R_scalar = 1.5
        g = euclidean_metric()
        G = einstein_tensor_from_ricci(Ric, R_scalar, g)
        for mu in range(4):
            for nu in range(4):
                assert G[mu][nu] == pytest.approx(
                    Ric[mu][nu] - 0.5 * R_scalar * g[mu][nu]
                )

    def test_symmetric_when_Ric_and_g_symmetric(self):
        # Symmetric Ricci, symmetric metric → G symmetric.
        Ric = [[1.0, 2.0, 3.0, 4.0], [2.0, 5.0, 6.0, 7.0],
               [3.0, 6.0, 8.0, 9.0], [4.0, 7.0, 9.0, 10.0]]
        g = euclidean_metric()
        G = einstein_tensor_from_ricci(Ric, 0.7, g)
        for mu in range(4):
            for nu in range(4):
                assert G[mu][nu] == pytest.approx(G[nu][mu])

    def test_constant_K_pipeline_minkowski(self):
        K = 1e-3
        g = minkowski_metric()
        _, R_scalar, G = constant_K_einstein_pipeline(K, g)
        # G should match -3K · g pointwise.
        G_pred = constant_sectional_einstein_tensor_predicted(K, g)
        for mu in range(4):
            for nu in range(4):
                assert G[mu][nu] == pytest.approx(G_pred[mu][nu], rel=1e-12,
                                                   abs=1e-14)


class TestTraceIdentity:
    """G^μ_μ = -R in 4D; dimension factor (n-2 = 2 for n = 4) emerges
    from the (1/2) R · n cancellation."""

    def test_trace_equals_neg_scalar_minkowski_constantK(self):
        K = 0.5
        g = minkowski_metric()
        g_inv = minkowski_inverse()
        Ric, R_scalar, G = constant_K_einstein_pipeline(K, g)
        # G^μ_μ should equal -R.
        trace = einstein_tensor_trace(G, g_inv)
        assert trace == pytest.approx(-R_scalar, rel=1e-12, abs=1e-14)

    def test_trace_equals_neg_scalar_euclidean_constantK(self):
        K = -0.7
        g = euclidean_metric()
        g_inv = euclidean_metric()
        _, R_scalar, G = constant_K_einstein_pipeline(K, g)
        trace = einstein_tensor_trace(G, g_inv)
        assert trace == pytest.approx(-R_scalar, rel=1e-12, abs=1e-14)

    def test_trace_quantitative_K_specific(self):
        # K=1 → R=12 → trace G = -12. Quantitative dimension-factor
        # check (mirrors Lean constantSectional_diag_trace_eq + 4D
        # specialization).
        K = 1.0
        g = euclidean_metric()
        g_inv = euclidean_metric()
        _, R_scalar, G = constant_K_einstein_pipeline(K, g)
        assert R_scalar == pytest.approx(12.0)
        assert einstein_tensor_trace(G, g_inv) == pytest.approx(-12.0)


class TestConstantKWitness:
    """G_{μν} = -3K · g_{μν} for constant-K (Lean constantSectional_einsteinTensor_eq)."""

    @pytest.mark.parametrize("K", [-0.7, 0.0, 0.1, 1.0])
    def test_constantK_predicted_eq_pipeline_minkowski(self, K):
        g = minkowski_metric()
        _, _, G_actual = constant_K_einstein_pipeline(K, g)
        G_pred = constant_sectional_einstein_tensor_predicted(K, g)
        for mu in range(4):
            for nu in range(4):
                assert G_actual[mu][nu] == pytest.approx(
                    G_pred[mu][nu], rel=1e-12, abs=1e-14
                )

    @pytest.mark.parametrize("K", [-0.5, 0.0, 1.0])
    def test_constantK_predicted_eq_pipeline_euclidean(self, K):
        g = euclidean_metric()
        _, _, G_actual = constant_K_einstein_pipeline(K, g)
        G_pred = constant_sectional_einstein_tensor_predicted(K, g)
        for mu in range(4):
            for nu in range(4):
                assert G_actual[mu][nu] == pytest.approx(
                    G_pred[mu][nu], rel=1e-12, abs=1e-14
                )

    def test_dimension_factor_3K(self):
        # G_diag_trace = -12K for constant-K in 4D.
        K = 2.0
        g = euclidean_metric()
        G = constant_sectional_einstein_tensor_predicted(K, g)
        diag_sum = sum(G[mu][mu] for mu in range(4))
        # G = -3K · g so diag_sum = -3K · 4 = -12K
        assert diag_sum == pytest.approx(-12.0 * K)


class TestVacuumCharacterization:
    """G = 0 ↔ Ric = 0 in 4D (Lean einsteinTensor_zero_iff_ricci_zero)."""

    def test_Ric_zero_implies_G_zero(self):
        Ric = [[0.0] * 4 for _ in range(4)]
        g = minkowski_metric()
        g_inv = minkowski_inverse()
        R_scalar = scalar_curvature_from_ricci(Ric, g_inv)
        assert R_scalar == 0.0
        G = einstein_tensor_from_ricci(Ric, R_scalar, g)
        for mu in range(4):
            for nu in range(4):
                assert G[mu][nu] == 0.0

    def test_K_zero_gives_zero_G(self):
        # Constant-K with K=0 is flat: Ric=0, R=0, G=0.
        K = 0.0
        g = minkowski_metric()
        Ric, R_scalar, G = constant_K_einstein_pipeline(K, g)
        for mu in range(4):
            for nu in range(4):
                assert Ric[mu][nu] == 0.0
                assert G[mu][nu] == 0.0
        assert R_scalar == 0.0


class TestDeSitterLambda:
    """Λ = 3K for the Λ-vacuum equation G + Λg = 0 (Lean
    constantSectional_lambda_vacuum_iff)."""

    @pytest.mark.parametrize("K", [-0.5, 0.1, 1.0, 5.0])
    def test_lambda_vacuum_satisfied_at_3K(self, K):
        g = minkowski_metric()
        _, _, G = constant_K_einstein_pipeline(K, g)
        Lambda = de_sitter_lambda_from_K(K)
        assert Lambda == pytest.approx(3.0 * K)
        # Verify Λ-vacuum equation: G + Λ · g = 0
        for mu in range(4):
            for nu in range(4):
                residual = G[mu][nu] + Lambda * g[mu][nu]
                assert residual == pytest.approx(0.0, abs=1e-13)

    def test_lambda_neq_3K_violates_vacuum_equation(self):
        # Falsifier: Λ != 3K should produce non-zero residual at some
        # index where g is non-zero.
        K = 1.0
        g = minkowski_metric()
        _, _, G = constant_K_einstein_pipeline(K, g)
        Lambda_wrong = 2.5 * K  # != 3K
        residuals = []
        for mu in range(4):
            for nu in range(4):
                residual = G[mu][nu] + Lambda_wrong * g[mu][nu]
                residuals.append(residual)
        # At least one residual must be non-zero (in particular at
        # diagonal indices where g is non-zero).
        assert max(abs(r) for r in residuals) > 1e-6


class TestMinkowskiCrossBridge:
    """Σ_{μν} η^{μν} η_{μν} = 4 (Lean minkowski_dim_contraction);
    flat-Minkowski case across the pipeline."""

    def test_self_inverse_contraction_eq_4(self):
        assert minkowski_dim_contraction_value() == pytest.approx(4.0)

    def test_explicit_contraction(self):
        eta = minkowski_metric()
        contraction = sum(
            eta[mu][nu] * eta[mu][nu]
            for mu in range(4) for nu in range(4)
        )
        # (-1)² + 1² + 1² + 1² = 4 (off-diagonals are zero)
        assert contraction == pytest.approx(4.0)

    def test_flat_Minkowski_einstein_tensor_zero(self):
        # K=0 on Minkowski → flat → G = 0 (the canonical Λ=0 vacuum).
        Ric, R_scalar, G = constant_K_einstein_pipeline(0.0, minkowski_metric())
        assert R_scalar == 0.0
        for mu in range(4):
            for nu in range(4):
                assert G[mu][nu] == 0.0
                assert Ric[mu][nu] == 0.0


class TestStrengtheningQuantitative:
    """Quantitative norm-num bounds carried from Phase 6f.1's
    discipline: the dimension factor (n-2 = 2 for n=4) is load-bearing."""

    def test_trace_factor_at_K_one(self):
        # K=1 → R=12, trace G = -12. The factor 12 - 6 = 6 cancellation
        # (R - (n/2)R) hits zero only at n=2; at n=4 it gives -R.
        K = 1.0
        Ric = constant_sectional_ricci_predicted(K, euclidean_metric())
        R_scalar = constant_sectional_scalar_predicted(K)
        G = einstein_tensor_from_ricci(Ric, R_scalar, euclidean_metric())
        diag_trace = sum(G[mu][mu] for mu in range(4))
        # R - (n/2) R = -R = -12 for n=4
        assert diag_trace == pytest.approx(-R_scalar)
        assert R_scalar == pytest.approx(12.0)

    def test_constant_K_consistent_at_multiple_K(self):
        # Pipeline reproducibility across many K values.
        for K in [-1.0, -0.1, 0.01, 0.5, 2.0, 10.0]:
            g = euclidean_metric()
            _, _, G = constant_K_einstein_pipeline(K, g)
            G_pred = constant_sectional_einstein_tensor_predicted(K, g)
            for mu in range(4):
                for nu in range(4):
                    assert G[mu][nu] == pytest.approx(
                        G_pred[mu][nu], rel=1e-10, abs=1e-12
                    )
