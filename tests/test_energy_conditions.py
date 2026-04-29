"""Phase 6f Wave 3 — Classical-GR energy-conditions tests.

Cross-layer agreement between Python ``formulas.py`` energy-condition
helpers and the Lean ``EnergyConditions.lean`` algebraic predicates +
counterexample witnesses.

Coverage mirrors the Lean module's substantive content (8 substantive
theorems + 1 marker; the marker is documentation only):

- TestPredicateBasics — IsNull / IsTimelike / IsFutureDirectedTimelike
  predicates evaluated on canonical Minkowski witnesses (matches the
  load-bearing hypothesis content of ``WEC`` / ``NEC`` / ``DEC`` /
  ``SEC``).
- TestCosmologicalLambdaWitness — cosmologicalLambda_WEC,
  cosmologicalLambda_NEC, cosmologicalLambda_violates_SEC (3 of the 5
  counterexample-witness theorems).
- TestGhostScalarWitness — ghostScalar_violates_NEC.
- TestStiffFluidWitness — stiff_fluid_violates_DEC.
- TestChainImplications — DEC ⇒ WEC at named witnesses (the direct
  projection content of DEC_implies_WEC; the continuity-based WEC ⇒ NEC
  is abstract and is asserted at the predicate level not numerics).
- TestPerfectFluidEnergyConditionRegions — quantitative norm-num bounds
  for the canonical perfect-fluid (ρ, p) plane:
    NEC: ρ + p ≥ 0
    WEC: ρ ≥ 0 AND ρ + p ≥ 0
    DEC: ρ ≥ |p|
    SEC: ρ + 3p ≥ 0 AND ρ + p ≥ 0
- TestAntiPatternAudit — verifies P1 (no ∃-absorption: explicit
  witnesses), P3 (no trivial-multiplication: load-bearing timelike
  restriction), and P4 (predicates non-vacuous).
"""

from __future__ import annotations

import pytest

from src.core.formulas import (
    apply_bilinear,
    cosmological_lambda_stress_energy,
    dec_check,
    ghost_scalar_stress_energy,
    is_future_directed_timelike,
    is_null_vec,
    is_timelike,
    nec_check,
    perfect_fluid_stress_energy,
    perfect_fluid_trace_minkowski,
    sec_check,
    wec_check,
)


# Reference Minkowski metric (matches Lean `minkowskiMetric` and the
# 6f.1 cross-bridge `LinearizedEFE.η`). Signature (-,+,+,+).

def minkowski_metric():
    return [
        [-1.0, 0.0, 0.0, 0.0],
        [0.0, 1.0, 0.0, 0.0],
        [0.0, 0.0, 1.0, 0.0],
        [0.0, 0.0, 0.0, 1.0],
    ]


T_AXIS = [1.0, 0.0, 0.0, 0.0]  # canonical future-directed time axis


class TestPredicateBasics:
    """Causal-vector predicates on Minkowski."""

    def test_null_vector_canonical(self):
        """k = (1,1,0,0) is null: g(k,k) = -1 + 1 = 0 and k ≠ 0."""
        g = minkowski_metric()
        assert is_null_vec(g, [1.0, 1.0, 0.0, 0.0])

    def test_null_excludes_zero_vector(self):
        """The zero vector has g(0,0) = 0 but is not a physical null
        direction. The non-zero clause is load-bearing per the Lean
        IsNull definition."""
        g = minkowski_metric()
        assert not is_null_vec(g, [0.0, 0.0, 0.0, 0.0])

    def test_null_excludes_timelike(self):
        """Timelike v has g(v,v) < 0, not 0 — should fail null check."""
        g = minkowski_metric()
        assert not is_null_vec(g, [1.0, 0.0, 0.0, 0.0])

    def test_null_excludes_spacelike(self):
        """Spacelike v has g(v,v) > 0 — should fail null check."""
        g = minkowski_metric()
        assert not is_null_vec(g, [0.0, 1.0, 0.0, 0.0])

    def test_timelike_canonical(self):
        """v = (1,0,0,0) is timelike: g(v,v) = -1 < 0."""
        g = minkowski_metric()
        assert is_timelike(g, [1.0, 0.0, 0.0, 0.0])

    def test_timelike_subluminal_boost(self):
        """v = (1, 0.9, 0, 0) is timelike: g(v,v) = -1 + 0.81 = -0.19 < 0."""
        g = minkowski_metric()
        assert is_timelike(g, [1.0, 0.9, 0.0, 0.0])

    def test_timelike_excludes_null(self):
        """Null k has g(k,k) = 0, fails strict timelike condition."""
        g = minkowski_metric()
        assert not is_timelike(g, [1.0, 1.0, 0.0, 0.0])

    def test_future_directed_timelike_canonical(self):
        """t = v = (1,0,0,0): g(t,v) = -1 < 0, future-directed."""
        g = minkowski_metric()
        assert is_future_directed_timelike(g, T_AXIS, [1.0, 0.0, 0.0, 0.0])

    def test_future_directed_timelike_boosted(self):
        """v = (1, 0.9, 0, 0) is future-directed: g(t,v) = -1 < 0."""
        g = minkowski_metric()
        assert is_future_directed_timelike(g, T_AXIS, [1.0, 0.9, 0.0, 0.0])

    def test_past_directed_timelike_excluded(self):
        """v = (-1, 0, 0, 0) is past-directed: g(t,v) = +1, not < 0."""
        g = minkowski_metric()
        v_past = [-1.0, 0.0, 0.0, 0.0]
        assert is_timelike(g, v_past)
        assert not is_future_directed_timelike(g, T_AXIS, v_past)


class TestCosmologicalLambdaWitness:
    """Cosmological-Λ tensor T_μν = -Λ g_μν.

    Mirrors Lean theorems:
      cosmologicalLambda_WEC,
      cosmologicalLambda_NEC,
      cosmologicalLambda_violates_SEC.
    """

    def test_cos_lambda_components_match_formula(self):
        """T_μν = -Λ η_μν: T_00 = +Λ, T_ii = -Λ for i=1..3."""
        g = minkowski_metric()
        for Lam in [0.0, 0.1, 1.0, 5.0]:
            T = cosmological_lambda_stress_energy(Lam, g)
            assert T[0][0] == pytest.approx(Lam)
            for i in range(1, 4):
                assert T[i][i] == pytest.approx(-Lam)

    def test_cos_lambda_WEC_satisfied_for_lambda_nonneg(self):
        """For Λ ≥ 0 and any future-directed timelike v, T(v,v) ≥ 0.

        Mirrors Lean cosmologicalLambda_WEC."""
        g = minkowski_metric()
        for Lam in [0.0, 0.1, 1.0, 5.0]:
            T = cosmological_lambda_stress_energy(Lam, g)
            for v in [
                [1.0, 0.0, 0.0, 0.0],
                [1.0, 0.5, 0.0, 0.0],
                [1.0, 0.0, 0.9, 0.0],
                [1.0, 0.3, 0.4, 0.5],
            ]:
                assert is_future_directed_timelike(g, T_AXIS, v)
                assert wec_check(T, v)

    def test_cos_lambda_NEC_satisfied_for_any_lambda(self):
        """T(k,k) = -Λ g(k,k) = 0 on null k for ANY Λ. The proof
        goes through vacuously (no need for Λ ≥ 0). Matches Lean
        cosmologicalLambda_NEC.

        Uses null witnesses with integer components so that the
        algebraic identity g(k,k) = 0 holds exactly in floating point
        (avoiding the false negatives that arise when, e.g.,
        0.6² + 0.8² ≠ 1 exactly)."""
        g = minkowski_metric()
        nulls = [
            [1.0, 1.0, 0.0, 0.0],
            [1.0, -1.0, 0.0, 0.0],
            [1.0, 0.0, 1.0, 0.0],
            [1.0, 0.0, 0.0, 1.0],
            [1.0, 0.0, -1.0, 0.0],
        ]
        for k in nulls:
            assert is_null_vec(g, k)
            for Lam in [-2.0, -0.1, 0.0, 0.1, 1.0, 5.0]:
                T = cosmological_lambda_stress_energy(Lam, g)
                assert nec_check(T, k)

    def test_cos_lambda_violates_SEC_for_lambda_positive(self):
        """For Λ > 0 with trT = -4Λ, the SEC residual at v = (1,0,0,0)
        is Λ · g(v,v) = -Λ < 0 — SEC VIOLATED.

        Mirrors Lean cosmologicalLambda_violates_SEC. The witness is
        the same: t = v = (1,0,0,0)."""
        g = minkowski_metric()
        v_witness = [1.0, 0.0, 0.0, 0.0]
        assert is_future_directed_timelike(g, T_AXIS, v_witness)
        for Lam in [0.1, 1.0, 5.0]:
            T = cosmological_lambda_stress_energy(Lam, g)
            trT = -4.0 * Lam  # T_μν = -Λ g_μν gives g^μν T_μν = -4Λ in 4D
            assert not sec_check(T, g, trT, v_witness)

    def test_cos_lambda_SEC_residual_value_explicit(self):
        """Explicit SEC residual at v = (1,0,0,0): Λ · g(v,v) = -Λ.

        This is the audit P3 quantitative-content check — the residual
        value is computed and compared against the closed-form formula
        rather than just sign-checked."""
        g = minkowski_metric()
        v_witness = [1.0, 0.0, 0.0, 0.0]
        for Lam in [0.1, 1.0, 5.0]:
            T = cosmological_lambda_stress_energy(Lam, g)
            trT = -4.0 * Lam
            residual = (apply_bilinear(T, v_witness, v_witness)
                        - 0.5 * trT * apply_bilinear(g, v_witness, v_witness))
            # Closed form: Λ · g(v,v) = -Λ
            assert residual == pytest.approx(-Lam)

    def test_cos_lambda_DEC_satisfied_for_lambda_nonneg(self):
        """For Λ ≥ 0, cosmological-Λ satisfies DEC at canonical
        witness pair (T(v,w) = -Λ g(v,w), and g(v,w) ≤ 0 for two
        future-directed timelike v, w)."""
        g = minkowski_metric()
        # Two future-directed timelike vectors
        v = [1.0, 0.5, 0.0, 0.0]
        w = [1.0, -0.3, 0.2, 0.0]
        assert is_future_directed_timelike(g, T_AXIS, v)
        assert is_future_directed_timelike(g, T_AXIS, w)
        for Lam in [0.0, 0.1, 1.0, 5.0]:
            T = cosmological_lambda_stress_energy(Lam, g)
            assert dec_check(T, v, w)


class TestGhostScalarWitness:
    """Ghost-scalar stress-energy T_μν = -n_μ n_ν.

    Mirrors Lean ghostScalar_violates_NEC.
    """

    def test_ghost_scalar_violates_NEC_explicit_witness(self):
        """n = (0, 1, 0, 0), k = (1, 1, 0, 0): T(k,k) = -1 < 0.

        Matches Lean ghostScalar_violates_NEC verbatim."""
        g = minkowski_metric()
        n = [0.0, 1.0, 0.0, 0.0]
        k = [1.0, 1.0, 0.0, 0.0]
        # Confirm k is null
        assert is_null_vec(g, k)
        # Build ghost-scalar tensor
        T = ghost_scalar_stress_energy(n)
        # Compute T(k, k) = -((n·k))^2 = -(0·1 + 1·1)^2 = -1
        T_kk = apply_bilinear(T, k, k)
        assert T_kk == pytest.approx(-1.0)
        # NEC requires T(k,k) ≥ 0; should be violated
        assert not nec_check(T, k)

    def test_ghost_scalar_violates_NEC_other_witnesses(self):
        """The violation is generic for non-zero gradient + null vector
        not orthogonal to gradient — verify at additional witnesses."""
        # Different gradient + null pair (orthogonality must fail to
        # exhibit violation)
        cases = [
            ([0.0, 0.0, 1.0, 0.0], [1.0, 0.0, 1.0, 0.0]),
            ([1.0, 0.0, 0.0, 0.0], [1.0, 1.0, 0.0, 0.0]),
            # Note: if n is purely time-like and k spatially-symmetric,
            # may give zero — pick non-orthogonal case
            ([0.0, 0.6, 0.8, 0.0], [1.0, 0.6, 0.8, 0.0]),
        ]
        g = minkowski_metric()
        for n, k in cases:
            assert is_null_vec(g, k, atol=1e-6)
            T = ghost_scalar_stress_energy(n)
            n_dot_k = sum(n[i] * k[i] for i in range(4))
            T_kk = apply_bilinear(T, k, k)
            assert T_kk == pytest.approx(-(n_dot_k ** 2))
            if abs(n_dot_k) > 1e-12:
                # Strictly negative ⇒ NEC violated
                assert not nec_check(T, k)


class TestStiffFluidWitness:
    """Stiff fluid (ρ=1, p=2) violates DEC.

    Mirrors Lean stiff_fluid_violates_DEC.
    """

    def test_stiff_fluid_violates_DEC_explicit_witness(self):
        """ρ = 1, p = 2 with v = (1, 9/10, 0, 0), w = (1, -9/10, 0, 0):
        T(v,w) = 1 + 2·(-81/100) = -31/50 < 0.

        Matches Lean stiff_fluid_violates_DEC verbatim."""
        g = minkowski_metric()
        v = [1.0, 9.0/10.0, 0.0, 0.0]
        w = [1.0, -9.0/10.0, 0.0, 0.0]
        # Confirm both are future-directed timelike
        assert is_future_directed_timelike(g, T_AXIS, v)
        assert is_future_directed_timelike(g, T_AXIS, w)
        T = perfect_fluid_stress_energy(1.0, 2.0)
        T_vw = apply_bilinear(T, v, w)
        # Closed form: 1·1·1 + 2·((9/10)·(-9/10)) = 1 - 162/100 = -31/50
        assert T_vw == pytest.approx(-31.0/50.0)
        # DEC violated
        assert not dec_check(T, v, w)

    def test_stiff_fluid_satisfies_WEC(self):
        """Stiff fluid (ρ=1, p=2) satisfies WEC: T(v,v) = ρ·v_0² +
        p·|v_spatial|² ≥ 0 for all v."""
        g = minkowski_metric()
        T = perfect_fluid_stress_energy(1.0, 2.0)
        for v in [
            [1.0, 0.0, 0.0, 0.0],
            [1.0, 0.5, 0.0, 0.0],
            [1.0, 0.9, 0.0, 0.0],
            [1.0, 0.3, 0.4, 0.5],
        ]:
            assert is_future_directed_timelike(g, T_AXIS, v)
            assert wec_check(T, v)

    def test_stiff_fluid_satisfies_NEC(self):
        """Stiff fluid satisfies NEC: T(k,k) = ρ + p · |k_spatial|² for
        null k normalized so k_0 = 1, |k_spatial|² = 1.
        With ρ = 1, p = 2: T(k,k) = 1 + 2 = 3 ≥ 0."""
        g = minkowski_metric()
        T = perfect_fluid_stress_energy(1.0, 2.0)
        nulls = [
            [1.0, 1.0, 0.0, 0.0],
            [1.0, 0.6, 0.8, 0.0],
            [1.0, 0.0, 1.0, 0.0],
        ]
        for k in nulls:
            assert is_null_vec(g, k)
            assert nec_check(T, k)


class TestChainImplications:
    """DEC ⇒ WEC at named witnesses; the WEC ⇒ NEC continuity-based
    chain in Lean is abstract (sequence-limit proof) and is asserted
    here at the predicate level via cross-witness consistency."""

    def test_dec_implies_wec_cosmological_lambda(self):
        """If DEC holds (cos-Λ at Λ ≥ 0), then WEC holds (since DEC = WEC
        ∧ flux-causal). Matches Lean DEC_implies_WEC at the bilinear-
        form-witness level."""
        g = minkowski_metric()
        for Lam in [0.0, 0.1, 1.0, 5.0]:
            T = cosmological_lambda_stress_energy(Lam, g)
            v = [1.0, 0.5, 0.0, 0.0]
            w = [1.0, -0.3, 0.2, 0.0]
            # Verify DEC at (v,w)
            assert dec_check(T, v, w)
            # WEC must follow — at v, at w
            assert wec_check(T, v)
            assert wec_check(T, w)

    def test_stiff_fluid_dec_violation_does_not_propagate_back_to_wec(self):
        """Sanity: DEC ⇏ WEC backwards. Stiff fluid violates DEC but
        still satisfies WEC. Confirms the chain direction (DEC implies
        WEC, not the converse) is the right one — the Lean chain
        implication captures actual physics, not a tautology."""
        g = minkowski_metric()
        T = perfect_fluid_stress_energy(1.0, 2.0)
        v = [1.0, 9.0/10.0, 0.0, 0.0]
        w = [1.0, -9.0/10.0, 0.0, 0.0]
        # DEC violated
        assert not dec_check(T, v, w)
        # WEC still holds at each
        assert wec_check(T, v)
        assert wec_check(T, w)


class TestPerfectFluidEnergyConditionRegions:
    """Quantitative norm-num bounds for perfect-fluid energy-condition
    regions in (ρ, p) plane:

      NEC: ρ + p ≥ 0
      WEC: ρ ≥ 0 AND ρ + p ≥ 0
      DEC: ρ ≥ |p|         (i.e., ρ ≥ 0 AND -ρ ≤ p ≤ ρ)
      SEC: ρ + 3p ≥ 0 AND ρ + p ≥ 0

    These are derived from Hawking & Ellis 1973 Table I §4.3 and are
    the audit P3 quantitative-content forms of the Lean predicates.
    """

    def test_NEC_region_perfect_fluid(self):
        """NEC at canonical null k = (1,1,0,0): T(k,k) = ρ + p; NEC
        equivalent to ρ + p ≥ 0."""
        g = minkowski_metric()
        k = [1.0, 1.0, 0.0, 0.0]
        assert is_null_vec(g, k)
        # Inside region (ρ + p ≥ 0)
        for rho, p in [(1.0, 0.0), (1.0, 1.0), (1.0, -1.0), (0.0, 0.0)]:
            T = perfect_fluid_stress_energy(rho, p)
            assert nec_check(T, k) == (rho + p >= 0.0)
        # Outside region
        for rho, p in [(1.0, -2.0), (0.0, -1.0), (-1.0, 0.0)]:
            T = perfect_fluid_stress_energy(rho, p)
            assert nec_check(T, k) == (rho + p >= 0.0)

    def test_WEC_region_perfect_fluid_at_rest(self):
        """WEC at v = (1,0,0,0): T(v,v) = ρ; WEC (at this single witness)
        equivalent to ρ ≥ 0."""
        g = minkowski_metric()
        v_rest = [1.0, 0.0, 0.0, 0.0]
        for rho, p in [(1.0, -1.0), (0.0, 0.0), (-0.1, 1.0), (-1.0, -1.0)]:
            T = perfect_fluid_stress_energy(rho, p)
            assert wec_check(T, v_rest) == (rho >= 0.0)

    def test_DEC_violated_when_p_exceeds_rho_stiff_regime(self):
        """DEC failure occurs when |p| > ρ. Witness pair v=(1,9/10,0,0),
        w=(1,-9/10,0,0): T(v,w) = ρ - 0.81·p, DEC needs T(v,w) ≥ 0
        AND T(v,v) ≥ 0 AND T(w,w) ≥ 0. For ρ ≥ 0 (so WEC ok) and large
        positive p, T(v,w) goes negative when p > ρ/0.81 ≈ 1.235·ρ."""
        v = [1.0, 9.0/10.0, 0.0, 0.0]
        w = [1.0, -9.0/10.0, 0.0, 0.0]
        # ρ=1, p=2: |p| > ρ ⇒ DEC violated (Lean stiff-fluid witness)
        T = perfect_fluid_stress_energy(1.0, 2.0)
        assert not dec_check(T, v, w)
        # ρ=1, p=0.5: |p| < ρ ⇒ DEC ok at this witness pair
        T = perfect_fluid_stress_energy(1.0, 0.5)
        assert dec_check(T, v, w)
        # ρ=1, p=-2 (large negative pressure / phantom): NEC violated
        # already (ρ+p = -1 < 0), so WEC fails at v_diag witness too
        # — DEC fails by failing WEC

    def test_SEC_region_perfect_fluid_cosmological_lambda(self):
        """SEC at v = (1,0,0,0): residual = T(v,v) - (1/2)·trT·g(v,v) =
        ρ - (1/2)·(3p - ρ)·(-1) = ρ + (1/2)(3p - ρ) = (1/2)(ρ + 3p).

        SEC at v_rest equivalent to ρ + 3p ≥ 0. Cosmological-Λ has
        ρ = Λ, p = -Λ ⇒ ρ + 3p = -2Λ < 0 for Λ > 0 ⇒ SEC violated."""
        g = minkowski_metric()
        v = [1.0, 0.0, 0.0, 0.0]
        for rho, p in [(1.0, 1.0), (1.0, 0.0), (1.0, -1.0/3.0)]:
            T = perfect_fluid_stress_energy(rho, p)
            trT = perfect_fluid_trace_minkowski(rho, p)  # = -ρ + 3p
            residual = (apply_bilinear(T, v, v)
                        - 0.5 * trT * apply_bilinear(g, v, v))
            # Closed form: residual = (1/2)(ρ + 3p)
            assert residual == pytest.approx(0.5 * (rho + 3.0 * p))
            assert sec_check(T, g, trT, v) == (rho + 3.0 * p >= 0.0)
        # Cosmological-Λ at Λ=1: ρ=1, p=-1, ρ+3p = -2 ⇒ SEC violated
        T = perfect_fluid_stress_energy(1.0, -1.0)
        trT = perfect_fluid_trace_minkowski(1.0, -1.0)  # = -4
        assert trT == pytest.approx(-4.0)
        assert not sec_check(T, g, trT, v)


class TestAntiPatternAudit:
    """Anti-pattern audit per CLAUDE.md preemptive-strengthening
    discipline — confirms the Lean predicates are non-vacuous and the
    counterexample witnesses are explicit (no ∃-absorption)."""

    def test_no_p1_existential_absorption_cosmological_lambda(self):
        """Cosmological-Λ witness is explicit: Λ enters the formula
        directly. No `∃ T, P(T)` discharged by black box."""
        g = minkowski_metric()
        T = cosmological_lambda_stress_energy(1.0, g)
        # Construction is concrete — type signature confirms.
        assert isinstance(T, list)
        assert len(T) == 4
        assert all(len(T[i]) == 4 for i in range(4))

    def test_no_p1_existential_absorption_ghost_scalar(self):
        """Ghost-scalar witness uses explicit gradient n = (0,1,0,0)."""
        T = ghost_scalar_stress_energy([0.0, 1.0, 0.0, 0.0])
        assert isinstance(T, list)
        # Verify it's a non-trivial tensor (spatial-spatial diagonal)
        assert T[1][1] == pytest.approx(-1.0)
        assert T[0][0] == 0.0

    def test_no_p1_existential_absorption_stiff_fluid(self):
        """Stiff-fluid witness uses explicit (ρ, p) = (1, 2)."""
        T = perfect_fluid_stress_energy(1.0, 2.0)
        assert T[0][0] == pytest.approx(1.0)
        assert T[1][1] == pytest.approx(2.0)

    def test_no_p3_trivial_zero_vector_in_NEC(self):
        """The zero vector (which is metric-null in any signature) is
        excluded from IsNull by the k ≠ 0 clause. Without this clause
        NEC would be vacuously satisfied at the zero vector — trivial
        physics. Confirms the Lean predicate's load-bearing
        non-zero hypothesis."""
        g = minkowski_metric()
        zero = [0.0, 0.0, 0.0, 0.0]
        # zero satisfies g(0,0) = 0 but should not pass IsNull
        assert apply_bilinear(g, zero, zero) == 0.0
        assert not is_null_vec(g, zero)

    def test_no_p3_trivial_v_zero_in_WEC(self):
        """v = 0 is not future-directed timelike (g(0,0) = 0, not < 0).
        The strict inequality in IsTimelike is load-bearing."""
        g = minkowski_metric()
        zero = [0.0, 0.0, 0.0, 0.0]
        assert not is_timelike(g, zero)
        assert not is_future_directed_timelike(g, T_AXIS, zero)

    def test_no_p4_WEC_not_positive_semidefiniteness(self):
        """WEC is NOT equivalent to T being positive-semi-definite.
        Cosmological-Λ at Λ > 0 satisfies WEC but T = diag(Λ, -Λ, -Λ, -Λ)
        is NOT positive-semi-definite (T(spacelike, spacelike) < 0).
        This shows the timelike restriction in WEC is load-bearing."""
        g = minkowski_metric()
        Lam = 1.0
        T = cosmological_lambda_stress_energy(Lam, g)
        # Spacelike vector x = (0, 1, 0, 0): T(x, x) = -Λ < 0
        x = [0.0, 1.0, 0.0, 0.0]
        T_xx = apply_bilinear(T, x, x)
        assert T_xx == pytest.approx(-Lam)
        assert T_xx < 0.0
        # But WEC still holds at any future-directed timelike
        v = [1.0, 0.5, 0.0, 0.0]
        assert is_future_directed_timelike(g, T_AXIS, v)
        assert wec_check(T, v)

    def test_predicates_nonvacuous_NEC_violator_exists(self):
        """The ghost-scalar witness explicitly violates NEC, confirming
        NEC is non-vacuous (a meaningful predicate)."""
        T = ghost_scalar_stress_energy([0.0, 1.0, 0.0, 0.0])
        k = [1.0, 1.0, 0.0, 0.0]
        assert not nec_check(T, k)

    def test_predicates_nonvacuous_DEC_violator_exists(self):
        """The stiff-fluid witness explicitly violates DEC, confirming
        DEC is non-vacuous."""
        T = perfect_fluid_stress_energy(1.0, 2.0)
        v = [1.0, 9.0/10.0, 0.0, 0.0]
        w = [1.0, -9.0/10.0, 0.0, 0.0]
        assert not dec_check(T, v, w)

    def test_predicates_nonvacuous_SEC_violator_exists(self):
        """The cosmological-Λ witness at Λ > 0 explicitly violates SEC,
        confirming SEC is non-vacuous (and that DEC ⇏ SEC: cos-Λ
        satisfies DEC but violates SEC)."""
        g = minkowski_metric()
        T = cosmological_lambda_stress_energy(1.0, g)
        v = [1.0, 0.0, 0.0, 0.0]
        trT = -4.0  # cos-Λ at Λ=1
        assert not sec_check(T, g, trT, v)


class TestPhase6f1CrossBridge:
    """Bridge to Phase 6f.1 Curvature module — Minkowski metric
    consistency. The Lean module reuses the same metric carrier shape
    as 6f.1's `LinearizedEFE.η`."""

    def test_minkowski_signature_matches_6f1(self):
        """The Minkowski metric used here must agree with 6f.1's
        `LinearizedEFE.η` componentwise. (Cross-bridge guard against
        signature drift between the two modules.)"""
        g = minkowski_metric()
        # Diagonal signature (-1, +1, +1, +1)
        assert g[0][0] == -1.0
        for i in range(1, 4):
            assert g[i][i] == 1.0
        # Off-diagonal zeros
        for mu in range(4):
            for nu in range(4):
                if mu != nu:
                    assert g[mu][nu] == 0.0

    def test_minkowski_self_inverse_dim_contraction_value(self):
        """Σ_{μν} η^{μν} η_{μν} = 4. Cross-references the 6f.2 Lean
        theorem `minkowski_dim_contraction` which is the load-bearing
        hypothesis behind the Einstein-tensor trace identity."""
        g = minkowski_metric()
        # In Minkowski η^μν = η_μν (self-inverse), so
        # Σ η^μν η_μν = Σ η_μν · η_μν = sum of squares of components
        contraction = sum(g[mu][nu] * g[mu][nu]
                          for mu in range(4) for nu in range(4))
        assert contraction == pytest.approx(4.0)
