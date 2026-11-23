"""Regression source for geometric arithmetic, precision and scalar comparisons.

Existing assertions, tolerances, populations and legacy names are retained.
These tests do not verify physical CHHK premises or material uniqueness.
Stored fitted lengths give S1/S2/S3 ratios about6098/2439/138 and scalar
margins about8.1e4/3.2e4/1.8e3; none identifies a collective transport length.
"""

import pytest

from src.core.formulas import (
    chhk_beta_d,
    chhk_mir_constant,
    graphene_mir_constant,
    graphene_mir_constant_mpmath,
    unit_sphere_surface,
)
from src.dkm_bootstrap import (
    CROSSNO_GRAPHENE_MEAN_FREE_PATH_M,
    CROSSNO_GRAPHENE_MEAN_FREE_PATH_RANGE_M,
    GRAPHENE_LATTICE_SPACING_M,
    crossno_graphene_satisfies_chhk_bound,
    graphene_mir_bound_constant,
    graphene_mir_constraint,
)
from src.dkm_bootstrap.graphene_mir import graphene_mir_constant_high_precision


# ──────────────────────────────────────────────────────────────────────
# §1. Unit-sphere surface area sanity check.
# ──────────────────────────────────────────────────────────────────────


class TestUnitSphereSurface:
    """V_{d-1} = 2 π^(d/2)/Γ(d/2) standard physics convention."""

    def test_V_0_two_endpoints(self):
        """d=1 → V_0 = 2 (endpoints of unit interval)."""
        import math
        assert math.isclose(unit_sphere_surface(1), 2.0)

    def test_V_1_unit_circle(self):
        """d=2 → V_1 = 2π (circumference of unit circle)."""
        import math
        assert math.isclose(unit_sphere_surface(2), 2 * math.pi)

    def test_V_2_unit_sphere(self):
        """d=3 → V_2 = 4π (surface of unit 2-sphere)."""
        import math
        assert math.isclose(unit_sphere_surface(3), 4 * math.pi)


# ──────────────────────────────────────────────────────────────────────
# §2. CHHK β_d closed form.
# ──────────────────────────────────────────────────────────────────────


class TestCHHKBetaD:
    """β_d = (1/π)·(V_{d-1}/(2π)^d)·(1-π/4)/(d+2) — CHHK arXiv:2509.18255v2 Eq. (9) [v1 Eq. (26)]."""

    def test_beta_d_positive(self):
        """β_d > 0 for physical dimensions d ∈ {2, 3}."""
        assert chhk_beta_d(2) > 0
        assert chhk_beta_d(3) > 0

    def test_beta_2_closed_form_matches_manual(self):
        """β_2 = (1 - π/4)/(8 π^2) by direct algebra with V_1 = 2π.

        Derivation: β_2 = (1/π)·(2π/(2π)²)·(1−π/4)/4 = (1−π/4)/(8π²).
        """
        import math
        manual = (1 - math.pi / 4) / (8 * math.pi**2)
        assert math.isclose(chhk_beta_d(2), manual, rel_tol=1e-12)

    def test_beta_d_decreases_with_d(self):
        """β_d decreases with d in physical range (volume measure shrinks)."""
        assert chhk_beta_d(3) < chhk_beta_d(2)


# ──────────────────────────────────────────────────────────────────────
# §3. MIR constant: float vs mpmath agreement.
# ──────────────────────────────────────────────────────────────────────


class TestMIRConstant:
    """``chhk_mir_constant(d) = (d·β_d/(4π))^(1/(d+1))`` — CHHK arXiv:2509.18255v2 Eq. (12) [v1 Eq. (29)]."""

    def test_graphene_value(self):
        """d=2 graphene MIR constant ≈ 0.0756."""
        import math
        c = graphene_mir_constant()
        assert math.isclose(c, 0.07562892800257202, rel_tol=1e-12)

    def test_float_mpmath_agreement_15_digits(self):
        """float and mpmath agree to ~15 significant figures."""
        import math
        float_val = graphene_mir_constant()
        mp_val = float(graphene_mir_constant_mpmath(30))
        assert math.isclose(float_val, mp_val, rel_tol=1e-14)

    def test_high_precision_30dps(self):
        """mpmath delivers 30 decimal places (DR §6 polished precision target)."""
        import mpmath
        with mpmath.workdps(40):
            mp_30 = graphene_mir_constant_mpmath(30)
            mp_40 = graphene_mir_constant_mpmath(40)
            # Both should agree to ~28 digits after rounding to 30 dps reference.
            diff = abs(mp_40 - mp_30)
            assert diff < mpmath.mpf("1e-25")

    def test_DR_says_order_O_01_to_O_1(self):
        """Wave 2a.1 DR §6: constant is approximately O(0.1)–O(1)."""
        c = graphene_mir_constant()
        # Our computed value 0.0756 is at the lower edge of O(0.1).
        assert 0.01 < c < 1.0

    def test_d3_constant_larger_than_d2(self):
        """MIR constant grows with d in physical range."""
        c2 = chhk_mir_constant(2)
        c3 = chhk_mir_constant(3)
        assert c3 > c2  # ~0.113 > ~0.076


# Scalar ordering between a normalized Lean constant and adopted arithmetic.


class TestLeanSubstrateLift:
    """Compare the adopted scalar with the normalized Lean constant.

    Legacy class name retained; this is no physical model lift."""

    def test_lean_placeholder_is_safe_upper_bound(self):
        """Check scalar ordering; implication requires the very same ratio/parameter tuple."""
        lean_placeholder = 0.5
        substantive = graphene_mir_bound_constant()
        # Ordering concerns the same abstract ratio only, not physical parameters.
        assert lean_placeholder > substantive

    def test_lean_placeholder_within_one_order(self):
        """Check the numerical ratio of two constants, not approximation accuracy."""
        lean_placeholder = 0.5
        substantive = graphene_mir_bound_constant()
        ratio = lean_placeholder / substantive
        assert 1 < ratio < 10  # Larger scalar lower bound, by about6.6; no material approximation claim


# Fitted-length scalar comparisons; physical model applicability stays separate.


class TestCrossnoGrapheneSatisfiesBound:
    """Check stored fit-estimate arithmetic; legacy name implies no physical verification."""

    def test_graphene_lattice_spacing_is_castro_neto(self):
        """Lattice spacing a = 0.246 nm per Castro Neto et al. RMP 81, 109 (2009)."""
        assert GRAPHENE_LATTICE_SPACING_M == pytest.approx(0.246e-9, rel=1e-12)

    def test_crossno_mean_free_path_anchored_to_S1(self):
        """Representative ℓ_m = 1.5 μm (Crossno 2016 sample S1, 60 K, Fig. 3C)."""
        assert CROSSNO_GRAPHENE_MEAN_FREE_PATH_M == pytest.approx(1.5e-6, rel=1e-12)

    def test_crossno_sample_range_anchored_to_paper(self):
        """Stored impurity-length fit estimates at60K: S3=.034,S2=.6,S1=1.5 micrometres."""
        s3, s2, s1 = CROSSNO_GRAPHENE_MEAN_FREE_PATH_RANGE_M
        assert s3 == pytest.approx(0.034e-6, rel=1e-12)
        assert s2 == pytest.approx(0.6e-6, rel=1e-12)
        assert s1 == pytest.approx(1.5e-6, rel=1e-12)

    def test_crossno_all_samples_satisfy_chhk_bound(self):
        """Compare supplied ratios with the scalar; margins about1.8e3 to8.1e4."""
        result = crossno_graphene_satisfies_chhk_bound()
        assert result["satisfies_bound_all_samples"]
        # S1 has the largest supplied ratio; this is arithmetic ordering.
        assert result["margin_per_sample"]["S1"] > 50000  # ~80000×
        assert result["margin_per_sample"]["S2"] > 20000  # ~32000×
        assert result["margin_per_sample"]["S3"] > 1  # about1.8e3 scalar margin; the existing >1 assertion stays exact

    def test_crossno_representative_S1_margin(self):
        """S1 supplied-length ratio is about6098; no collective-length identification."""
        result = crossno_graphene_satisfies_chhk_bound()
        # S1 = 1.5 μm; a = 0.246 nm; ℓ/a ≈ 6098
        assert result["ell_over_a_representative"] > 5000
        assert result["margin_representative"] > 50000  # ~80000×

    def test_graphene_mir_constraint_function(self):
        """The legacy helper returns True for the S1 supplied-ratio arithmetic."""
        assert graphene_mir_constraint(1.5e-6, 0.246e-9) is True

    def test_graphene_mir_constraint_below_bound(self):
        """ℓ/a below MIR constant → constraint violated."""
        # ℓ/a = 0.05 < 0.0756 — clearly below MIR bound.
        assert graphene_mir_constraint(ell_m=0.05e-9, a_m=1e-9) is False

    def test_graphene_mir_constraint_at_bound(self):
        """ℓ/a exactly at MIR constant satisfies bound (≥ not >)."""
        mir = graphene_mir_bound_constant()
        a = 1e-9
        ell = mir * a
        assert graphene_mir_constraint(ell, a) is True

    def test_graphene_mir_constraint_rejects_nonpositive(self):
        """Non-positive inputs raise ValueError."""
        with pytest.raises(ValueError):
            graphene_mir_constraint(ell_m=-1e-9)
        with pytest.raises(ValueError):
            graphene_mir_constraint(ell_m=1e-9, a_m=0.0)


# ──────────────────────────────────────────────────────────────────────
# §6. High-precision string export (for Lean numeric literal use).
# ──────────────────────────────────────────────────────────────────────


class TestHighPrecisionExport:
    """String export at 30 dps — Lean literal commit precision."""

    def test_high_precision_30dps_format(self):
        """String export starts with '0.0756...' (digits 1-5 of MIR constant)."""
        s = graphene_mir_constant_high_precision(30)
        assert s.startswith("0.0756")

    def test_high_precision_default_dps_30(self):
        """Default dps is 30 (Wave 2a.1 DR §6 polished target).

        mpmath.nstr rounds the final digits, so equality round-trip can lose
        one ULP at the last decimal place. We accept that as a precision-
        format artifact and check agreement to 28 decimals.
        """
        import mpmath
        s = graphene_mir_constant_high_precision()
        with mpmath.workdps(30):
            roundtrip = mpmath.mpf(s)
            reference = graphene_mir_constant_mpmath(30)
            assert abs(roundtrip - reference) < mpmath.mpf("1e-28")


# ──────────────────────────────────────────────────────────────────────
# §7. Cross-module consistency: src.dkm_bootstrap ↔ src.core.formulas.
# ──────────────────────────────────────────────────────────────────────


class TestCrossModuleConsistency:
    """`src.dkm_bootstrap.graphene_mir_bound_constant` re-exports
    `src.core.formulas.graphene_mir_constant`."""

    def test_module_re_export_matches_canonical(self):
        """src.dkm_bootstrap result == src.core.formulas result."""
        assert graphene_mir_bound_constant() == graphene_mir_constant()
