"""Phase 6e Wave 1: tests for the Seeley-DeWitt heat-kernel expansion.

Mirrors ``lean/SKEFTHawking/HeatKernelExpansion.lean``. Validates:
- closed-form a_0 / a_2 / a_4 coefficients (Christensen-Duff)
- Decision Gate E.2: a_2 calibration to Phase 6a.1 G_N_sakharov (exact
  at α_ADW = 1)
- positivity / sign structure
- linearity in N_f
- Gauss-Bonnet local-algebra identity
"""

from __future__ import annotations

import math

import pytest

from src.core.constants import GRAV_PARAMS, HEAT_KERNEL_PARAMS
from src.core.formulas import (
    G_N_from_seeley_dewitt,
    gauss_bonnet_density,
    heat_kernel_a2_matches_GN_sakharov,
    seeley_dewitt_a0,
    seeley_dewitt_a2_R_coefficient,
    seeley_dewitt_a4_basis,
)
from src.heat_kernel import (
    SeeleyDeWittCoefficients,
    a2_calibration_passes,
    a2_calibration_relative_error,
    a4_basis,
    gauss_bonnet_combination,
    higher_curvature_dirac_signs,
    seeley_dewitt_coefficients,
)
from src.heat_kernel.a4_computation import coefficient_overall_factor
from src.heat_kernel.a2_computation import G_N_linearized_at_alpha, planck_anchor_match


FOUR_PI_SQ = (4.0 * math.pi) ** 2


# ════════════════════════════════════════════════════════════════════
# §1: Leading coefficient a_0
# ════════════════════════════════════════════════════════════════════


class TestA0:
    def test_a0_closed_form(self):
        """Lean: a0_dirac (definition)."""
        for N_f in [1.0, 4.0, 15.0, 45.0]:
            assert seeley_dewitt_a0(N_f) == pytest.approx(
                4 * N_f / FOUR_PI_SQ
            )

    def test_a0_pos(self):
        """Lean: a0_dirac_pos."""
        for N_f in [0.1, 1.0, 15.0, 1000.0]:
            assert seeley_dewitt_a0(N_f) > 0

    def test_a0_linear(self):
        """Lean: a0_dirac_linear."""
        a0_3 = seeley_dewitt_a0(3.0)
        a0_15 = seeley_dewitt_a0(15.0)
        # 15 = 5 * 3
        assert a0_15 == pytest.approx(5.0 * a0_3)

    def test_a0_at_unit_species(self):
        """a_0(1) = 4/(4π)² = 1/(4π²)."""
        assert seeley_dewitt_a0(1.0) == pytest.approx(1.0 / (4.0 * math.pi**2))


# ════════════════════════════════════════════════════════════════════
# §2: Einstein-Hilbert coefficient a_2
# ════════════════════════════════════════════════════════════════════


class TestA2:
    def test_a2_closed_form(self):
        """Lean: a2_R_coefficient (definition)."""
        for N_f in [1.0, 15.0, 45.0]:
            assert seeley_dewitt_a2_R_coefficient(N_f) == pytest.approx(
                -N_f / (12.0 * FOUR_PI_SQ)
            )

    def test_a2_negative(self):
        """Lean: a2_R_coefficient_neg."""
        for N_f in [0.5, 15.0, 100.0]:
            assert seeley_dewitt_a2_R_coefficient(N_f) < 0

    def test_a2_zero_iff_no_species(self):
        """Lean: a2_R_coefficient_eq_zero_iff."""
        assert seeley_dewitt_a2_R_coefficient(0.0) == 0.0
        assert seeley_dewitt_a2_R_coefficient(1e-6) != 0.0


# ════════════════════════════════════════════════════════════════════
# §3: Decision Gate E.2 — calibration to G_N_sakharov
# ════════════════════════════════════════════════════════════════════


class TestG_N_Calibration:
    def test_G_N_closed_form(self):
        """Lean: G_N_from_a2 (definition)."""
        Lambda, N_f = 1e16, 15
        assert G_N_from_seeley_dewitt(Lambda, N_f) == pytest.approx(
            12 * math.pi / (N_f * Lambda**2)
        )

    def test_calibration_exact_at_alpha_one(self):
        """Lean: G_N_from_a2_eq_G_N_sakharov.

        At α_ADW = 1, the heat-kernel a_2 calibration matches the
        Sakharov-Adler linearized G_N exactly — no tolerance needed.
        """
        for Lambda in [1e10, 1e16, 1e19]:
            for N_f in [1, 15, 45]:
                assert a2_calibration_relative_error(Lambda, N_f, 1.0) == 0.0
                assert a2_calibration_passes(Lambda, N_f, 1.0)

    def test_calibration_fails_at_alpha_far_from_one(self):
        """Lean: a2_matches_GNemerg_iff_alpha_ADW_unity (→ direction).

        At α_ADW well outside the natural band, the heat-kernel
        calibration disagrees with the linearized form.
        """
        # alpha = 5 → rel err = |1 - 5|/5 = 0.8 > 0.5
        assert not a2_calibration_passes(1e16, 15, 5.0)
        # alpha = 0.1 → rel err = |1 - 0.1|/0.1 = 9.0 > 0.5
        assert not a2_calibration_passes(1e16, 15, 0.1)

    def test_calibration_boundary_at_tolerance(self):
        """At α_ADW = 2, rel err = 0.5 exactly = tolerance (≤ → True)."""
        rel_err = a2_calibration_relative_error(1e16, 15, 2.0)
        assert rel_err == pytest.approx(0.5, rel=1e-12)
        assert a2_calibration_passes(1e16, 15, 2.0)

    def test_explicit_tolerance_override(self):
        """Tighten tolerance to reject α = 1.5 (rel err = 1/3 = 0.333)."""
        # default tol 0.5 → 1.5 passes
        assert a2_calibration_passes(1e16, 15, 1.5)
        # tighter tol 0.1 → fails
        assert not a2_calibration_passes(1e16, 15, 1.5, tolerance=0.1)


# ════════════════════════════════════════════════════════════════════
# §4: SeeleyDeWittCoefficients dataclass
# ════════════════════════════════════════════════════════════════════


class TestSDCoefficientsBundle:
    def test_dataclass_fields(self):
        sd = seeley_dewitt_coefficients(15)
        assert isinstance(sd, SeeleyDeWittCoefficients)
        assert sd.N_f == 15.0
        assert sd.a0 == seeley_dewitt_a0(15)
        assert sd.a2_R_coef == seeley_dewitt_a2_R_coefficient(15)

    def test_rejects_nonpositive_N_f(self):
        with pytest.raises(ValueError):
            seeley_dewitt_coefficients(0)
        with pytest.raises(ValueError):
            seeley_dewitt_coefficients(-1)

    def test_asdict_roundtrip(self):
        sd = seeley_dewitt_coefficients(45)
        d = sd.asdict()
        assert set(d.keys()) == {
            "N_f", "a0", "a2_R_coef", "a4_R_sq", "a4_Ricci_sq", "a4_Riemann_sq"
        }


# ════════════════════════════════════════════════════════════════════
# §5: a_4 higher-curvature basis
# ════════════════════════════════════════════════════════════════════


class TestA4Basis:
    def test_a4_keys(self):
        """Lean: a4_R_sq_coef, a4_Ricci_sq_coef, a4_Riemann_sq_coef."""
        a4 = a4_basis(15)
        assert set(a4.keys()) == {"R_sq", "Ricci_sq", "Riemann_sq"}

    def test_a4_signs(self):
        """Lean: a4_R_sq_coef_neg, a4_Ricci_sq_coef_pos,
        a4_Riemann_sq_coef_neg."""
        signs = higher_curvature_dirac_signs(15)
        assert signs["R_sq"] == "neg"
        assert signs["Ricci_sq"] == "pos"
        assert signs["Riemann_sq"] == "neg"

    def test_a4_signs_invariant_in_N_f(self):
        """Signs do not depend on the species count (only the magnitude)."""
        for N_f in [0.5, 15.0, 1000.0]:
            signs = higher_curvature_dirac_signs(N_f)
            assert signs == {"R_sq": "neg", "Ricci_sq": "pos", "Riemann_sq": "neg"}

    def test_a4_rejects_nonpositive_N_f(self):
        with pytest.raises(ValueError):
            higher_curvature_dirac_signs(0)

    def test_a4_riemann_canonical_value(self):
        """a_4 Riemann² coefficient = -12/(12·180) · N_f / (4π)²."""
        for N_f in [1.0, 15.0]:
            expected = N_f * (-12.0 / (12.0 * 180.0)) / FOUR_PI_SQ
            assert seeley_dewitt_a4_basis(N_f)["Riemann_sq"] == pytest.approx(expected)


# ════════════════════════════════════════════════════════════════════
# §6: Gauss-Bonnet local-algebra identity
# ════════════════════════════════════════════════════════════════════


class TestGaussBonnet:
    def test_gauss_bonnet_density_unit(self):
        """𝒢 = R² − 4 R_μν² + R_μνρσ²; density at (1,1,1) = -2."""
        assert gauss_bonnet_density(1.0, 1.0, 1.0) == -2.0

    def test_gauss_bonnet_dirac_a4_combination(self):
        """Lean: a4_gauss_bonnet_combination.

        c_R² − 4 c_Ricci² + c_Riem²
            = N_f · (-45/(12·180)) / (4π)²
            = -N_f / (48 (4π)²)
        """
        for N_f in [1.0, 15.0, 45.0]:
            gb = gauss_bonnet_combination(N_f)
            expected = N_f * (-45.0 / (12.0 * 180.0)) / FOUR_PI_SQ
            assert gb == pytest.approx(expected, rel=1e-12)

    def test_gauss_bonnet_simplified_form(self):
        """The combination = -N_f / (48 (4π)²)."""
        for N_f in [1.0, 15.0]:
            gb = gauss_bonnet_combination(N_f)
            simplified = -N_f / (48.0 * FOUR_PI_SQ)
            assert gb == pytest.approx(simplified, rel=1e-12)


# ════════════════════════════════════════════════════════════════════
# §7: Quantitative anchors / Lean norm_num parity
# ════════════════════════════════════════════════════════════════════


class TestQuantitativeAnchors:
    def test_GUT_anchor_value(self):
        """Lean: G_N_from_a2_at_GUT_anchor."""
        # G_N(GUT, 15) = 12π/(15·10³²)
        Lambda, N_f = 1e16, 15
        assert G_N_from_seeley_dewitt(Lambda, N_f) == pytest.approx(
            12.0 * math.pi / (N_f * Lambda**2), rel=1e-12
        )

    def test_GUT_inverse_below_planck_squared(self):
        """Lean: G_N_from_a2_inverse_at_GUT_below_planck_squared.

        1/G_N(GUT, 15) = 15·10³²/(12π) ≈ 3.98e31.
        Should be (much) smaller than 10³⁸ = M_Pl_anchor².
        """
        Lambda, N_f = 1e16, 15
        inv_G = 1.0 / G_N_from_seeley_dewitt(Lambda, N_f)
        assert inv_G < (1e19) ** 2

    def test_planck_anchor_match_dict(self):
        """Anchor introspection produces the expected fields."""
        anchor = planck_anchor_match()
        assert "Lambda_UV_GeV" in anchor
        assert "G_N_heat_kernel_GeV_m2" in anchor
        assert anchor["G_N_heat_kernel_GeV_m2"] > 0
        # At Planck Λ + 3-gen N_f, the heat-kernel G_N is within order of
        # magnitude of CODATA G_N (sanity).
        assert anchor["rel_diff"] < 5.0  # generous OOM band


# ════════════════════════════════════════════════════════════════════
# §8: Constants / provenance consistency
# ════════════════════════════════════════════════════════════════════


class TestConstantsConsistency:
    def test_dirac_trace_dim_is_four(self):
        """tr 𝟙_4 = 4 in 4D Dirac-spinor representation."""
        assert HEAT_KERNEL_PARAMS["DIRAC_TRACE_DIM"] == 4

    def test_a0_rational_is_four(self):
        assert HEAT_KERNEL_PARAMS["A0_DIRAC_RATIONAL"] == 4.0

    def test_a2_R_coef_is_neg_one_twelfth(self):
        assert HEAT_KERNEL_PARAMS["A2_DIRAC_R_COEF"] == pytest.approx(-1.0 / 12.0)

    def test_four_pi_sq_consistency(self):
        assert HEAT_KERNEL_PARAMS["FOUR_PI_SQ"] == pytest.approx(FOUR_PI_SQ)

    def test_eh_prefactor_consistency(self):
        """12 · (4π)² appears in `1/G_N = N_f Λ² / (12 (4π)²)` after
        absorbing the EH `-1/(16π G_N)` sign convention."""
        assert HEAT_KERNEL_PARAMS["EH_PREFACTOR_TWELVE_FOUR_PI_SQ"] == pytest.approx(
            12.0 * FOUR_PI_SQ
        )

    def test_match_tolerance_consistent_with_GRAV(self):
        """The HK calibration band should reuse the GRAV_PARAMS band."""
        assert (
            HEAT_KERNEL_PARAMS["A2_GN_MATCH_TOLERANCE"]
            == GRAV_PARAMS["G_N_MATCH_TOLERANCE"]
        )

    def test_gauss_bonnet_signature(self):
        """Gauss-Bonnet weights (1, -4, 1) on (R², Ricci², Riem²)."""
        assert HEAT_KERNEL_PARAMS["GAUSS_BONNET_R_SQ"] == 1.0
        assert HEAT_KERNEL_PARAMS["GAUSS_BONNET_RICCI_SQ"] == -4.0
        assert HEAT_KERNEL_PARAMS["GAUSS_BONNET_RIEMANN_SQ"] == 1.0

    def test_four_pi_sq_inv_helper(self):
        """coefficient_overall_factor = 1/(4π)²."""
        assert coefficient_overall_factor() == pytest.approx(1.0 / FOUR_PI_SQ)


# ════════════════════════════════════════════════════════════════════
# §9: Linearized side parity
# ════════════════════════════════════════════════════════════════════


class TestLinearizedSideParity:
    def test_G_N_linearized_at_alpha_one_equals_heat_kernel(self):
        """At α=1, the linearized formula matches the heat-kernel form."""
        Lambda, N_f = 1e16, 15
        assert G_N_linearized_at_alpha(Lambda, N_f, 1.0) == pytest.approx(
            G_N_from_seeley_dewitt(Lambda, N_f)
        )

    def test_G_N_linearized_scales_with_alpha(self):
        """G_N_emerg = α · G_N_sakharov; linear in α."""
        Lambda, N_f = 1e16, 15
        base = G_N_linearized_at_alpha(Lambda, N_f, 1.0)
        assert G_N_linearized_at_alpha(Lambda, N_f, 2.5) == pytest.approx(2.5 * base)
