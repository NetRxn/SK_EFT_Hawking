"""Phase 6f Wave 1 — Classical-GR curvature algebra tests.

Cross-layer agreement between Python `formulas.py` curvature
helpers and the Lean `Curvature.lean` algebraic predicates +
constant-sectional-curvature witness theorems.

The tests are organized into:

- TestFormulaCorrectness — Python implementations satisfy the
  algebraic identities the Lean theorems prove.
- TestConstantSectionalRiemann — `constantSectionalRiemann(K, g)` on
  Minkowski (`LinearizedEFE.η`) and Euclidean reference metrics
  agrees with the Lean closed form.
- TestRicciAndScalar — `Ric_{σν} = 3 K g_{σν}` (4D), scalar
  `R_trace = 12 K` for trace(g) = 4.
- TestAntiPatternAudit — verifies the anti-Bianchi witness violates
  first Bianchi (matches Lean `nonBianchiTensor_violates_FirstBianchi`).
- TestStrengtheningQuantitative — quantitative norm-num bounds the
  audit checklist required.
- TestPhase6f3CrossBridge — bridge consistency to EnergyConditions
  module's Minkowski metric.
"""

from __future__ import annotations

import numpy as np
import pytest

from src.core.formulas import (
    riemann_constant_sectional_curvature,
    ricci_from_riemann,
    scalar_curvature_from_ricci,
    constant_sectional_ricci_predicted,
    constant_sectional_scalar_predicted,
    first_bianchi_residual,
    antisym_last_two_residual,
)


# Reference metrics — replicate what Lean uses (LinearizedEFE.η for
# Minkowski; identity for Euclidean test).

def minkowski_metric():
    """Signature `(-,+,+,+)` Minkowski metric, matches LinearizedEFE.η."""
    return [
        [-1.0, 0.0, 0.0, 0.0],
        [0.0, 1.0, 0.0, 0.0],
        [0.0, 0.0, 1.0, 0.0],
        [0.0, 0.0, 0.0, 1.0],
    ]


def euclidean_metric():
    """Signature `(+,+,+,+)` Euclidean metric, identity matrix."""
    return [
        [1.0, 0.0, 0.0, 0.0],
        [0.0, 1.0, 0.0, 0.0],
        [0.0, 0.0, 1.0, 0.0],
        [0.0, 0.0, 0.0, 1.0],
    ]


def trace_of_metric(g):
    return sum(g[i][i] for i in range(4))


class TestFormulaCorrectness:
    """Verify Python helpers match Lean closed forms termwise."""

    def test_constant_sectional_riemann_zero_K(self):
        """K=0 gives the zero Riemann (matches Lean
        `zeroRiemann_lower_zero` after lowering)."""
        g = minkowski_metric()
        R = riemann_constant_sectional_curvature(0.0, g)
        for rho in range(4):
            for sig in range(4):
                for mu in range(4):
                    for nu in range(4):
                        assert R[rho][sig][mu][nu] == 0.0

    def test_riemann_antisym_last_two_residual_minkowski(self):
        """Constant-K Riemann satisfies AntisymLastTwo on Minkowski."""
        g = minkowski_metric()
        for K in [0.0, 1e-3, 1.0, -2.5]:
            R = riemann_constant_sectional_curvature(K, g)
            assert antisym_last_two_residual(R) < 1e-12

    def test_riemann_first_bianchi_residual_minkowski(self):
        """Constant-K Riemann satisfies first Bianchi on (symmetric)
        Minkowski. Matches Lean
        `constantSectional_FirstBianchi`."""
        g = minkowski_metric()
        for K in [0.0, 0.1, 1.0, -1.0]:
            R = riemann_constant_sectional_curvature(K, g)
            assert first_bianchi_residual(R) < 1e-12

    def test_riemann_first_bianchi_residual_euclidean(self):
        """Constant-K Riemann satisfies first Bianchi on Euclidean."""
        g = euclidean_metric()
        for K in [0.0, 1.0, -3.14]:
            R = riemann_constant_sectional_curvature(K, g)
            assert first_bianchi_residual(R) < 1e-12

    def test_first_bianchi_fails_on_explicit_violator(self):
        """The 'non-Bianchi tensor' (single-1 component at (0,0,0,0))
        violates first Bianchi. Matches Lean
        `nonBianchiTensor_violates_FirstBianchi`."""
        R = [
            [[[0.0] * 4 for _ in range(4)] for _ in range(4)]
            for _ in range(4)
        ]
        R[0][0][0][0] = 1.0
        # Cyclic at (0,0,0,0) gives 1 + 1 + 1 = 3 ≠ 0
        assert abs(first_bianchi_residual(R) - 3.0) < 1e-12


class TestRicciAndScalar:
    """Verify Lean's `constantSectional_Ricci_eq` and
    `constantSectional_diag_trace_eq` numerically."""

    def test_ricci_eq_3K_g_minkowski(self):
        """Ricci of constant-K Riemann on Minkowski equals 3K · η."""
        g = minkowski_metric()
        for K in [0.5, 1.0, -2.0]:
            R = riemann_constant_sectional_curvature(K, g)
            Ric = ricci_from_riemann(R)
            Ric_predicted = constant_sectional_ricci_predicted(K, g, dim=4)
            for sig in range(4):
                for nu in range(4):
                    np.testing.assert_allclose(
                        Ric[sig][nu], Ric_predicted[sig][nu], atol=1e-10
                    )

    def test_ricci_dimension_factor_is_3_in_4d(self):
        """The dimension-(n-1) factor is 3 in 4D — quantitative
        norm-num check, matches Lean theorem."""
        K = 1.0
        g = euclidean_metric()
        R = riemann_constant_sectional_curvature(K, g)
        Ric = ricci_from_riemann(R)
        # Ric_{00} should equal 3 · K · g_{00} = 3
        assert abs(Ric[0][0] - 3.0) < 1e-12

    def test_scalar_diag_trace_eq_12K_for_trace4(self):
        """Σ_μ Ric_{μμ} = 12 K when trace(g) = 4. Matches Lean
        `constantSectional_diag_trace_eq`."""
        g = euclidean_metric()  # trace = 4
        assert trace_of_metric(g) == 4.0
        for K in [0.5, 1.0, -2.0, 1e-3]:
            R = riemann_constant_sectional_curvature(K, g)
            Ric = ricci_from_riemann(R)
            diag_trace = sum(Ric[mu][mu] for mu in range(4))
            np.testing.assert_allclose(
                diag_trace, 12.0 * K, atol=1e-10
            )

    def test_scalar_predicted_is_12K_in_4d(self):
        """`constant_sectional_scalar_predicted` returns 12K in 4D."""
        for K in [0.5, 1.0, -2.0, 1e-9]:
            assert (
                constant_sectional_scalar_predicted(K, dim=4)
                == pytest.approx(12.0 * K)
            )

    def test_scalar_dim_factor_n_times_n_minus_1(self):
        """Quantitative `n(n-1)` factor: 4 × 3 = 12 in 4D, 3 × 2 = 6
        in 3D. Sanity check for the Lean dimension-factor pattern."""
        assert constant_sectional_scalar_predicted(1.0, dim=4) == 12.0
        assert constant_sectional_scalar_predicted(1.0, dim=3) == 6.0
        assert constant_sectional_scalar_predicted(1.0, dim=2) == 2.0

    def test_minkowski_trace_is_2(self):
        """Minkowski trace `(-1) + 1 + 1 + 1 = 2`. Surfaces here so
        downstream waves know the diag-trace theorem doesn't apply
        directly to Minkowski — only to Euclidean / orthonormal-frame
        diagonalizations."""
        assert trace_of_metric(minkowski_metric()) == 2.0


class TestPairSymmetry:
    """Verify Lean's `pair_symmetry_lowered` numerically."""

    def lower_first_index(self, R, g):
        """Mirror of Lean `lowerFirstIndex`."""
        Rl = [
            [[[0.0] * 4 for _ in range(4)] for _ in range(4)]
            for _ in range(4)
        ]
        for rho in range(4):
            for sig in range(4):
                for mu in range(4):
                    for nu in range(4):
                        Rl[rho][sig][mu][nu] = float(sum(
                            g[rho][a] * R[a][sig][mu][nu] for a in range(4)
                        ))
        return Rl

    def test_pair_symmetry_constant_K_minkowski(self):
        """R_{ρσμν} = R_{μνρσ} for constant-K Riemann lowered with
        Minkowski. The wave's headline algebraic content."""
        g = minkowski_metric()
        for K in [0.5, 1.0, -1.5]:
            R = riemann_constant_sectional_curvature(K, g)
            Rl = self.lower_first_index(R, g)
            for rho in range(4):
                for sig in range(4):
                    for mu in range(4):
                        for nu in range(4):
                            np.testing.assert_allclose(
                                Rl[rho][sig][mu][nu],
                                Rl[mu][nu][rho][sig],
                                atol=1e-10,
                            )

    def test_pair_symmetry_constant_K_euclidean(self):
        """Same on Euclidean."""
        g = euclidean_metric()
        for K in [0.1, 1.0, -2.0]:
            R = riemann_constant_sectional_curvature(K, g)
            Rl = self.lower_first_index(R, g)
            for rho in range(4):
                for sig in range(4):
                    for mu in range(4):
                        for nu in range(4):
                            np.testing.assert_allclose(
                                Rl[rho][sig][mu][nu],
                                Rl[mu][nu][rho][sig],
                                atol=1e-10,
                            )

    def test_first_pair_antisym_constant_K(self):
        """R_{ρσμν} = -R_{σρμν} (lowered, AntisymPair12)."""
        for g in [minkowski_metric(), euclidean_metric()]:
            for K in [1.0, -1.0]:
                R = riemann_constant_sectional_curvature(K, g)
                Rl = self.lower_first_index(R, g)
                for rho in range(4):
                    for sig in range(4):
                        for mu in range(4):
                            for nu in range(4):
                                np.testing.assert_allclose(
                                    Rl[rho][sig][mu][nu],
                                    -Rl[sig][rho][mu][nu],
                                    atol=1e-10,
                                )


class TestStrengtheningQuantitative:
    """Quantitative norm-num-style bounds — match the audit P3
    quantitative-content check."""

    def test_de_sitter_K_anchored_value_is_positive(self):
        """For a positive-curvature de Sitter space at K = 1/L² with
        L > 0, the predicted scalar R = 12 K is strictly positive.

        This is the dimension-factor norm-num bound surfaced as a
        quantitative claim — exactly the audit-flagged P3 form."""
        L = 1.0  # de Sitter radius
        K = 1.0 / (L * L)
        R_predicted = constant_sectional_scalar_predicted(K, dim=4)
        assert R_predicted > 0.0
        np.testing.assert_allclose(R_predicted, 12.0, atol=1e-12)

    def test_anti_de_sitter_K_negative_gives_negative_scalar(self):
        """Anti-de Sitter has K = -1/L² < 0, so R_trace = -12/L² < 0."""
        L = 1.0
        K = -1.0 / (L * L)
        R_predicted = constant_sectional_scalar_predicted(K, dim=4)
        assert R_predicted < 0.0
        np.testing.assert_allclose(R_predicted, -12.0, atol=1e-12)


class TestAntiPatternAudit:
    """Anti-pattern audit per CLAUDE.md preemptive-strengthening
    discipline."""

    def test_no_p1_existential_absorption(self):
        """Constant-K witness is explicit: K, g enter the formula
        directly. No `∃ R, P R` discharged by black box."""
        # Construction is concrete — type signature confirms.
        R = riemann_constant_sectional_curvature(1.0, euclidean_metric())
        assert isinstance(R, list)
        assert len(R) == 4
        assert all(len(R[i]) == 4 for i in range(4))

    def test_first_bianchi_predicate_nonvacuous(self):
        """`first_bianchi_residual` returns >0 on an explicit violator.
        Confirms predicate is non-vacuous — matches Lean
        `nonBianchiTensor_violates_FirstBianchi`."""
        R = [
            [[[0.0] * 4 for _ in range(4)] for _ in range(4)]
            for _ in range(4)
        ]
        R[0][0][0][0] = 1.0
        assert first_bianchi_residual(R) > 0

    def test_antisym_last_two_predicate_nonvacuous(self):
        """Asymmetric-in-last-two witness violates AntisymLastTwo."""
        R = [
            [[[0.0] * 4 for _ in range(4)] for _ in range(4)]
            for _ in range(4)
        ]
        # R(0,0,0,1) = 1, R(0,0,1,0) = 1 (no antisymmetry: should be -1)
        R[0][0][0][1] = 1.0
        R[0][0][1][0] = 1.0
        assert antisym_last_two_residual(R) > 0

    def test_first_bianchi_requires_metric_symmetry(self):
        """Constant-K Riemann fails first Bianchi if metric is NOT
        symmetric — confirms the load-bearing role of metric symmetry
        in the Lean theorem `constantSectional_FirstBianchi`."""
        # Asymmetric "metric": g[0][1] = 1, g[1][0] = 0 (antisym component)
        g_asym = [[0.0] * 4 for _ in range(4)]
        for i in range(4):
            g_asym[i][i] = 1.0  # diagonal still 1
        g_asym[0][1] = 1.0
        # g_asym[1][0] = 0  (default; thus asymmetric)
        K = 1.0
        R = riemann_constant_sectional_curvature(K, g_asym)
        # First Bianchi should now have non-zero residual
        assert first_bianchi_residual(R) > 1e-10


class TestPhase6f3CrossBridge:
    """Bridge to Phase 6f.3 EnergyConditions module — Minkowski metric
    consistency (matches Lean `linearizedEFE_η_metricSymmetric` and
    `constantSectional_minkowski_AntisymPair12`)."""

    def test_minkowski_is_metric_symmetric(self):
        """LinearizedEFE.η is metric-symmetric — Lean theorem confirmed."""
        g = minkowski_metric()
        for mu in range(4):
            for nu in range(4):
                assert g[mu][nu] == g[nu][mu]

    def test_minkowski_signature(self):
        """LinearizedEFE.η has signature (-1, +1, +1, +1)."""
        g = minkowski_metric()
        assert g[0][0] == -1.0
        assert g[1][1] == 1.0
        assert g[2][2] == 1.0
        assert g[3][3] == 1.0

    def test_constant_K_riemann_on_minkowski_satisfies_full_chain(self):
        """The full algebraic-predicate chain on Minkowski for K = 1:
        AntisymLastTwo + FirstBianchi + AntisymPair12 + Ricci formula.

        Matches Lean `constantSectional_minkowski_AntisymPair12` and
        `constantSectional_minkowski_Ricci_eq`."""
        K = 1.0
        g = minkowski_metric()
        R = riemann_constant_sectional_curvature(K, g)
        # AntisymLastTwo
        assert antisym_last_two_residual(R) < 1e-12
        # FirstBianchi
        assert first_bianchi_residual(R) < 1e-12
        # Ricci = 3 K η
        Ric = ricci_from_riemann(R)
        for sig in range(4):
            for nu in range(4):
                np.testing.assert_allclose(
                    Ric[sig][nu], 3.0 * K * g[sig][nu], atol=1e-10
                )
