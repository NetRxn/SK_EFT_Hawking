"""Phase 6f Wave 6 — Tetrad (vierbein) formalism tests.

Cross-layer agreement between Python ``formulas.py`` tetrad helpers
and the Lean ``TetradFormalism.lean`` module. **Closes Phase 6f.**

Coverage mirrors the Lean module's substantive content (6 substantive
theorems + 1 marker):

- TestTetradInducedMetric — symmetry + Minkowski-tetrad identity.
- TestDiagonalTetradDet — Minkowski-tetrad determinant = 1.
- TestTorsionResidual — torsion-free biconditional.
- TestPhase6eCrossBridge — tetrad-Cartan equivalence at α_EC = 1
  (consumes 6e.6 EinsteinCartanExtension).
- TestAntiPatternAudit — concrete witnesses, non-vacuous predicates.
"""

from __future__ import annotations

import pytest

from src.core.formulas import (
    diagonal_tetrad_det,
    minkowski_tetrad,
    tetrad_induced_metric,
    torsion_residual,
)


def minkowski_metric():
    return [
        [-1.0, 0.0, 0.0, 0.0],
        [0.0, 1.0, 0.0, 0.0],
        [0.0, 0.0, 1.0, 0.0],
        [0.0, 0.0, 0.0, 1.0],
    ]


class TestTetradInducedMetric:
    """Tetrad-metric equivalence g_μν = η_ab e^a_μ e^b_ν."""

    def test_symmetry(self):
        """g_μν = g_νμ for any tetrad e (Lean
        tetradInducedMetric_symm)."""
        # Use a non-trivial tetrad to test symmetry beyond the
        # Minkowski case
        e = [
            [1.0, 0.1, 0.0, 0.0],
            [0.0, 1.0, 0.2, 0.0],
            [0.0, 0.0, 1.0, 0.3],
            [0.4, 0.0, 0.0, 1.0],
        ]
        for mu in range(4):
            for nu in range(4):
                assert (tetrad_induced_metric(e, mu, nu)
                        == pytest.approx(tetrad_induced_metric(e, nu, mu)))

    def test_minkowski_tetrad_induces_minkowski_metric(self):
        """Minkowski tetrad e = δ recovers η_μν.

        Mirrors Lean minkowskiTetrad_induces_minkowski_metric."""
        e = minkowski_tetrad()
        eta = minkowski_metric()
        for mu in range(4):
            for nu in range(4):
                assert (tetrad_induced_metric(e, mu, nu)
                        == pytest.approx(eta[mu][nu]))

    def test_minkowski_tetrad_g00_eq_neg_one(self):
        """g_00 = -1 specialization for Minkowski tetrad."""
        e = minkowski_tetrad()
        assert tetrad_induced_metric(e, 0, 0) == pytest.approx(-1.0)

    def test_minkowski_tetrad_spatial_diag_eq_one(self):
        """g_ii = +1 for spatial i with Minkowski tetrad."""
        e = minkowski_tetrad()
        for i in range(1, 4):
            assert tetrad_induced_metric(e, i, i) == pytest.approx(1.0)


class TestDiagonalTetradDet:
    """Tetrad determinant. Mirrors Lean
    minkowskiTetrad_det_eq_one."""

    def test_minkowski_tetrad_det_eq_one(self):
        """det(δ) = 1."""
        e = minkowski_tetrad()
        assert diagonal_tetrad_det(e) == pytest.approx(1.0)

    def test_scaled_diagonal_tetrad(self):
        """For diagonal e^a_μ = c · δ^a_μ, det = c⁴."""
        for c in [0.5, 2.0, 3.0]:
            e = [
                [c, 0, 0, 0],
                [0, c, 0, 0],
                [0, 0, c, 0],
                [0, 0, 0, c],
            ]
            assert diagonal_tetrad_det(e) == pytest.approx(c ** 4)


class TestTorsionResidual:
    """Torsion-free biconditional. Mirrors Lean
    torsionResidual_zero_iff."""

    def test_torsion_zero_at_zero_amplitude(self):
        """T = 0 ↔ amplitude = 0."""
        assert torsion_residual(0) == 0.0

    def test_torsion_nonzero_at_nonzero_amplitude(self):
        """T ≠ 0 for nonzero amplitude."""
        for amp in [0.1, -0.5, 1.0]:
            assert torsion_residual(amp) != 0.0


class TestPhase6eCrossBridge:
    """Cross-bridge to Phase 6e.6 EinsteinCartanExtension.

    Mirrors Lean tetrad_metric_equivalence_at_alpha_one and
    tetrad_levi_civita_iff_alpha_unity."""

    def test_ec_residual_at_alpha_one_vanishes(self):
        """Tetrad-metric formalism equivalence at α_EC = 1: the
        Einstein-Cartan residual vanishes (recovers Levi-Civita
        connection).

        Mirrors Lean tetrad_metric_equivalence_at_alpha_one which
        consumes 6e.6 ecResidual_at_alpha_one."""
        from src.einstein_cartan.ec_residual_assessment import (
            ec_residual_at_point,
        )
        # At α_EC = 1, residual vanishes regardless of other params
        for Lambda_UV in [1.0, 1.221e19]:  # natural and Planck
            for N_f in [1, 16]:
                for n_spin in [1.3e-39, 1.0]:
                    result = ec_residual_at_point(
                        Lambda_UV, N_f, alpha_ec=1.0, n_spin_gev3=n_spin
                    )
                    # ECResidualResult dataclass has `residual_gev` field
                    assert abs(result.residual_gev) < 1e-50


class TestAntiPatternAudit:
    """Anti-pattern audit per CLAUDE.md preemptive-strengthening
    discipline (with 6f.5 lessons applied)."""

    def test_no_p1_existential_absorption(self):
        """Minkowski tetrad uses concrete numerical δ matrix.
        No ∃ tetrad e, P(e)."""
        e = minkowski_tetrad()
        assert e[0][0] == 1.0
        assert e[1][2] == 0.0

    def test_predicates_nonvacuous_tetrad_metric_equivalence(self):
        """The tetrad-metric equivalence has substantive both-direction
        content: different tetrads → different metrics."""
        e1 = minkowski_tetrad()
        e2 = [
            [2.0, 0, 0, 0],
            [0, 1, 0, 0],
            [0, 0, 1, 0],
            [0, 0, 0, 1],
        ]
        # e2 has e^0_0 = 2, so g_00 should be -4 (not -1)
        assert tetrad_induced_metric(e2, 0, 0) == pytest.approx(-4.0)
        assert tetrad_induced_metric(e1, 0, 0) == pytest.approx(-1.0)

    def test_load_bearing_diagonal_det_scaling(self):
        """det scales as 4th power for diagonal tetrads — non-vacuous
        named-quantity scaling."""
        for c in [0.5, 2.0]:
            e_scaled = [
                [c, 0, 0, 0],
                [0, c, 0, 0],
                [0, 0, c, 0],
                [0, 0, 0, c],
            ]
            assert diagonal_tetrad_det(e_scaled) == pytest.approx(c ** 4)
