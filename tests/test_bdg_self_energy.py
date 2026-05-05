"""Tests for src/resurgence/bdg_self_energy.py.

Phase 6n Wave 1a.3 Path A — Stage 2 γ_1 Beliaev LO + Stage 3 γ_2 NLO
kinematic-dispersive derivation tests.

Stage 2 (Session 10): γ_1 implementation tests + numerical-verification
tests for the kinematic phase-space integral.
Stage 3 (Session 11, this revision): γ_2 kinematic-dispersive tests +
SymPy symbolic Bogoliubov inverse-dispersion expansion verification +
asymptotic-ratio convergence-radius checks.

Stage 4-5 tests (γ_2^(loop) Beliaev-Galitskii + γ_3..γ_7 higher loops)
remain skip-marked until the underlying functions ship.

References:
  temporary/working-docs/phase6n/wave_1a_3_path_A_stage1.md
  src/resurgence/bdg_self_energy.py module docstring
"""

from __future__ import annotations

import math

import pytest
import sympy as sp

from src.resurgence.bdg_self_energy import (
    BELIAEV_2LOOP_KINEMATIC_RATE,
    BELIAEV_BOGOLIUBOV_PREFACTOR,
    BELIAEV_KINEMATIC_INTEGRAL,
    BELIAEV_LO_PREFACTOR,
    BELIAEV_NLO_KIN_DISP_PREFACTOR,
    BELIAEV_NLO_KIN_DISP_RATIO,
    KIN_DISP_ENVELOPE,
    BdGSelfEnergyResult,
    GeometricEnvelope,
    andreev_khalatnikov_anchor_gamma_2,
    beliaev_anchor_gamma_1,
    beliaev_lo_dimensionless,
    beliaev_lo_rate,
    bogoliubov_inverse_dispersion_expansion,
    compute_gamma_n,
    compute_gamma_sequence,
    derive_beliaev_lo_dimensionless,
    derive_beliaev_lo_kinematic_integral,
    derive_gamma_2_kinematic_dispersive,
    envelope_borel_transform_bound,
    envelope_sum,
    gamma_2_kinematic_dispersive_anchor,
    gamma_kinematic_dispersive_sequence,
    gamma_n_kinematic_dispersive,
    gamma_n_kinematic_dispersive_closed_form,
    gamma_n_loop_kinematic_dispersive_relative,
    is_borel_summable_under_envelope,
    loop_envelope_at_dilute_bec,
    stage_4a_structural_verdict,
    stage_4b_dilute_bec_verdict,
    stage_5_sharpened_verdict,
)


# ---------------------------------------------------------------------------
# Stage 1 sanity tests (dataclass shape)
# ---------------------------------------------------------------------------


def test_bdg_self_energy_result_dataclass_shape() -> None:
    """BdGSelfEnergyResult is a frozen dataclass with the expected fields."""
    result = BdGSelfEnergyResult(
        order=1,
        gamma=0.0,
        cross_validated=False,
        anchor_citation="Beliaev 1958",
        method="Beliaev-LO",
    )
    assert result.order == 1
    assert result.gamma == 0.0
    assert result.cross_validated is False
    assert result.anchor_citation == "Beliaev 1958"
    assert result.method == "Beliaev-LO"


# ---------------------------------------------------------------------------
# Stage 2 tests (Beliaev LO)
# ---------------------------------------------------------------------------


def test_beliaev_anchor_returns_finite_positive() -> None:
    """Beliaev γ_1 anchor is a finite positive value below unity (weak coupling)."""
    anchor = beliaev_anchor_gamma_1()
    assert anchor > 0.0
    assert anchor < 1.0  # dimensionless rate; should be < 1 for weak coupling
    # Closed-form value: 3/(640π) ≈ 1.4924e-3
    assert anchor == pytest.approx(3.0 / (640.0 * math.pi), rel=1e-12)


def test_beliaev_lo_prefactor_constant() -> None:
    """The module-level constant BELIAEV_LO_PREFACTOR equals the literature value."""
    assert BELIAEV_LO_PREFACTOR == 3.0 / (640.0 * math.pi)
    assert BELIAEV_LO_PREFACTOR == pytest.approx(1.4924e-3, rel=1e-3)


def test_beliaev_kinematic_integral_numerical() -> None:
    """The kinematic phase-space integral ∫₀^1 u²(1-u)² du equals 1/30."""
    numerical = derive_beliaev_lo_kinematic_integral()
    assert numerical == pytest.approx(1.0 / 30.0, rel=1e-9)
    assert BELIAEV_KINEMATIC_INTEGRAL == 1.0 / 30.0


def test_beliaev_bogoliubov_prefactor_constant() -> None:
    """The Bogoliubov + Jacobian prefactor is 9/64."""
    assert BELIAEV_BOGOLIUBOV_PREFACTOR == 9.0 / 64.0


def test_derive_beliaev_lo_dimensionless_matches_anchor() -> None:
    """The analytic decomposition (1/30)·(9/64)/π reconstructs γ_1 = 3/(640π)."""
    derivation = derive_beliaev_lo_dimensionless()
    assert derivation["kinematic_integral"] == pytest.approx(1.0 / 30.0, rel=1e-9)
    assert derivation["kinematic_integral_exact"] == 1.0 / 30.0
    assert derivation["bogoliubov_prefactor"] == 9.0 / 64.0
    assert derivation["gamma_1_derived"] == pytest.approx(
        derivation["gamma_1_anchor"], rel=1e-9
    )
    assert derivation["relative_error"] < 1e-9


def test_gamma_1_matches_beliaev_anchor() -> None:
    """γ_1 from compute_gamma_n(1, ...) matches Beliaev 1958 anchor."""
    c_s = 0.5e-3  # m/s; Steinhauer-class BEC
    xi = 200e-9  # m; Steinhauer-class healing length
    result = compute_gamma_n(order=1, c_s=c_s, xi=xi)
    anchor = beliaev_anchor_gamma_1()
    assert result.cross_validated is True
    assert result.gamma == pytest.approx(anchor, rel=1e-12)
    assert result.order == 1
    assert result.method == "Beliaev-LO"
    assert result.anchor_citation is not None
    assert "Beliaev" in result.anchor_citation
    assert "Pitaevskii" in result.anchor_citation


def test_beliaev_lo_rate_dimensional_form() -> None:
    """Dimensional Γ_Bel(k) = (3/(640π))·c_s·ξ⁴·k⁵ at Steinhauer-class params."""
    c_s = 0.5e-3
    xi = 200e-9
    # At horizon k_H = κ/c_s with κ = 2π·100 Hz ≈ 628 Hz
    kappa = 2 * math.pi * 100.0
    k_H = kappa / c_s
    rate = beliaev_lo_rate(k_H, c_s, xi)
    expected = BELIAEV_LO_PREFACTOR * c_s * xi**4 * k_H**5
    assert rate == pytest.approx(expected, rel=1e-12)
    assert rate > 0.0
    # Sanity: dimensionless rate at horizon Γ/κ should be tiny
    # Γ_Bel/κ = γ_1 · (ξ·κ/c_s)^4 with ξκ/c_s = κ/Λ_UV ≈ 0.25 (since
    # Λ_UV = c_s/ξ = 2500 Hz and κ ≈ 628 Hz)
    Lambda_UV = c_s / xi
    g_H_linear = kappa / Lambda_UV  # dimensionless ratio
    expected_diss = BELIAEV_LO_PREFACTOR * g_H_linear**4
    assert rate / kappa == pytest.approx(expected_diss, rel=1e-9)


def test_beliaev_lo_dimensionless_form_consistency() -> None:
    """beliaev_lo_dimensionless(ξk) matches beliaev_lo_rate(k)/ω(k) at LO."""
    c_s = 0.5e-3
    xi = 200e-9
    k = 1.0e6  # m⁻¹; ξk = 0.2 (linear regime)
    xi_k = xi * k
    omega_lo = c_s * k  # linear-dispersion approximation
    rate_dim = beliaev_lo_rate(k, c_s, xi)
    rate_dimless = beliaev_lo_dimensionless(xi_k)
    assert rate_dim / omega_lo == pytest.approx(rate_dimless, rel=1e-12)


def test_compute_gamma_sequence_ships_through_max_order_2_at_stage_3() -> None:
    """Stage 3 ships γ_1 + γ_2; max_order ≥ 3 raises NotImplementedError."""
    c_s = 0.5e-3
    xi = 200e-9
    seq_one = compute_gamma_sequence(max_order=1, c_s=c_s, xi=xi)
    assert len(seq_one) == 1
    assert seq_one[0].order == 1
    assert seq_one[0].cross_validated is True
    seq_two = compute_gamma_sequence(max_order=2, c_s=c_s, xi=xi)
    assert len(seq_two) == 2
    assert seq_two[0].order == 1
    assert seq_two[1].order == 2
    assert seq_two[1].method == "Beliaev-NLO-kin-disp"
    assert seq_two[1].cross_validated is True
    with pytest.raises(NotImplementedError):
        compute_gamma_sequence(max_order=3, c_s=c_s, xi=xi)


def test_compute_gamma_n_rejects_nonpositive_order() -> None:
    """compute_gamma_n raises ValueError for order ≤ 0."""
    with pytest.raises(ValueError):
        compute_gamma_n(order=0, c_s=0.5e-3, xi=200e-9)
    with pytest.raises(ValueError):
        compute_gamma_n(order=-1, c_s=0.5e-3, xi=200e-9)


# ---------------------------------------------------------------------------
# Stage 3 tests (γ_2 kinematic-dispersive NLO)
# ---------------------------------------------------------------------------


def test_beliaev_nlo_kin_disp_ratio_constant() -> None:
    """The NLO kinematic-dispersive ratio γ_2^(kin-disp)/γ_1 = -1/8."""
    assert BELIAEV_NLO_KIN_DISP_RATIO == -1.0 / 8.0


def test_beliaev_nlo_kin_disp_prefactor_constant() -> None:
    """γ_2^(kin-disp) = -γ_1/8 = -3/(5120π) ≈ -1.866 × 10⁻⁴."""
    expected = -3.0 / (5120.0 * math.pi)
    assert BELIAEV_NLO_KIN_DISP_PREFACTOR == pytest.approx(expected, rel=1e-12)
    # Magnitude sanity: at the order of 10⁻⁴.
    assert abs(BELIAEV_NLO_KIN_DISP_PREFACTOR) == pytest.approx(1.866e-4, rel=1e-3)
    # Sign: negative (LO Beliaev rate divided by larger Bogoliubov ω).
    assert BELIAEV_NLO_KIN_DISP_PREFACTOR < 0.0


def test_bogoliubov_inverse_dispersion_expansion_first_few_coefficients() -> None:
    """SymPy expansion of [1+(ξk/2)²]^(-1/2) matches closed form."""
    coeffs = bogoliubov_inverse_dispersion_expansion(max_order=4)
    # Closed-form coefficients of (ξk)^(2k) for k=0..4
    assert coeffs[0] == sp.Rational(1)
    assert coeffs[1] == sp.Rational(-1, 8)
    assert coeffs[2] == sp.Rational(3, 128)
    assert coeffs[3] == sp.Rational(-5, 1024)
    assert coeffs[4] == sp.Rational(35, 32768)


def test_bogoliubov_inverse_dispersion_expansion_general_n() -> None:
    """SymPy coefficients match (-1)^n · C(2n, n) / 16^n closed form."""
    N = 6
    coeffs = bogoliubov_inverse_dispersion_expansion(max_order=N)
    for k in range(N + 1):
        expected = sp.Rational((-1) ** k * sp.binomial(2 * k, k), 16**k)
        assert coeffs[k] == expected


def test_bogoliubov_inverse_dispersion_expansion_rejects_negative_order() -> None:
    """Negative max_order raises ValueError."""
    with pytest.raises(ValueError):
        bogoliubov_inverse_dispersion_expansion(max_order=-1)


def test_gamma_n_kinematic_dispersive_closed_form_first_orders() -> None:
    """Closed-form γ_n^(kin-disp)/γ_1 ratio matches expected rationals."""
    assert gamma_n_kinematic_dispersive_closed_form(1) == sp.Rational(1)
    assert gamma_n_kinematic_dispersive_closed_form(2) == sp.Rational(-1, 8)
    assert gamma_n_kinematic_dispersive_closed_form(3) == sp.Rational(3, 128)
    assert gamma_n_kinematic_dispersive_closed_form(4) == sp.Rational(-5, 1024)


def test_gamma_n_kinematic_dispersive_closed_form_rejects_zero() -> None:
    """n < 1 raises ValueError."""
    with pytest.raises(ValueError):
        gamma_n_kinematic_dispersive_closed_form(0)
    with pytest.raises(ValueError):
        gamma_n_kinematic_dispersive_closed_form(-1)


def test_gamma_n_kinematic_dispersive_n_equals_1_returns_gamma_1() -> None:
    """At n=1 γ_n^(kin-disp) = γ_1 exactly (no LO dispersive correction)."""
    g1 = gamma_n_kinematic_dispersive(1)
    assert g1 == pytest.approx(BELIAEV_LO_PREFACTOR, rel=1e-12)


def test_gamma_n_kinematic_dispersive_n_equals_2_anchor() -> None:
    """At n=2 γ_n^(kin-disp) = -γ_1/8 = anchor value."""
    g2 = gamma_n_kinematic_dispersive(2)
    assert g2 == pytest.approx(BELIAEV_NLO_KIN_DISP_PREFACTOR, rel=1e-12)
    assert g2 < 0.0


def test_gamma_2_kinematic_dispersive_anchor_value() -> None:
    """γ_2^(kin-disp) anchor = -γ_1/8 = -3/(5120π)."""
    anchor = gamma_2_kinematic_dispersive_anchor()
    assert anchor == BELIAEV_NLO_KIN_DISP_PREFACTOR
    assert anchor == pytest.approx(-3.0 / (5120.0 * math.pi), rel=1e-12)


def test_derive_gamma_2_kinematic_dispersive_matches_anchor() -> None:
    """SymPy-derived γ_2^(kin-disp) reconstructs the anchor."""
    derivation = derive_gamma_2_kinematic_dispersive()
    assert derivation["sympy_kin_disp_ratio"] == pytest.approx(-1.0 / 8.0, rel=1e-12)
    assert derivation["closed_form_ratio"] == pytest.approx(-1.0 / 8.0, rel=1e-12)
    assert derivation["gamma_2_kin_disp_derived"] == pytest.approx(
        derivation["gamma_2_kin_disp_anchor"], rel=1e-12
    )
    assert derivation["relative_error"] < 1e-12


def test_gamma_2_matches_kinematic_dispersive_anchor() -> None:
    """γ_2 from compute_gamma_n(2, ...) matches the kinematic-dispersive anchor."""
    c_s = 0.5e-3
    xi = 200e-9
    result = compute_gamma_n(order=2, c_s=c_s, xi=xi)
    anchor = gamma_2_kinematic_dispersive_anchor()
    assert result.order == 2
    assert result.cross_validated is True
    assert result.gamma == pytest.approx(anchor, rel=1e-12)
    assert result.method == "Beliaev-NLO-kin-disp"
    assert result.anchor_citation is not None
    assert "Pitaevskii" in result.anchor_citation
    assert "Beliaev-Galitskii" in result.anchor_citation
    assert "Stage 4" in result.anchor_citation


def test_gamma_kinematic_dispersive_sequence_first_few() -> None:
    """gamma_kinematic_dispersive_sequence(N) returns N values matching closed form."""
    seq = gamma_kinematic_dispersive_sequence(max_order=5)
    assert len(seq) == 5
    g1 = BELIAEV_LO_PREFACTOR
    assert seq[0] == pytest.approx(g1, rel=1e-12)
    assert seq[1] == pytest.approx(-g1 / 8.0, rel=1e-12)
    assert seq[2] == pytest.approx(3.0 * g1 / 128.0, rel=1e-12)
    assert seq[3] == pytest.approx(-5.0 * g1 / 1024.0, rel=1e-12)
    assert seq[4] == pytest.approx(35.0 * g1 / 32768.0, rel=1e-12)


def test_gamma_kinematic_dispersive_sequence_asymptotic_ratio() -> None:
    """Asymptotic |γ_{n+1}^(kin-disp) / γ_n^(kin-disp)| → 1/4 from below.

    This is the substantive Stage-3 finding: the kinematic piece of the
    gradient-expansion coefficient sequence is sharply geometric with
    convergence ratio 1/4 — i.e., series convergence radius ξk = 2,
    equivalently k = 2 · Λ_UV.

    Closed-form ratio: |γ_{k+1}^(kin-disp) / γ_k^(kin-disp)| = (2k-1)/(8k)
    for the index k = (n-1) into the inverse-dispersion-expansion sequence.
    Approach to 1/4 is monotone-increasing from below (slow O(1/n) correction).
    """
    N = 30
    seq = gamma_kinematic_dispersive_sequence(max_order=N)
    # seq[k] = γ_{k+1}^(kin-disp); the ratio between consecutive entries:
    ratio_at_10 = abs(seq[10] / seq[9])  # γ_11/γ_10 ratio
    ratio_at_20 = abs(seq[20] / seq[19])
    ratio_at_29 = abs(seq[29] / seq[28])
    # Closed form: |seq[k]/seq[k-1]| = (2k-1)/(8k); below 1/4 for all finite k.
    assert ratio_at_10 == pytest.approx((2 * 10 - 1) / (8 * 10), rel=1e-12)
    assert ratio_at_20 == pytest.approx((2 * 20 - 1) / (8 * 20), rel=1e-12)
    assert ratio_at_29 == pytest.approx((2 * 29 - 1) / (8 * 29), rel=1e-12)
    # Monotone convergence to 1/4 from below.
    assert ratio_at_10 < ratio_at_20 < ratio_at_29 < 0.25
    # The limit at order 30 is within ~0.005 of 1/4:
    assert ratio_at_29 == pytest.approx(0.25, abs=0.01)


def test_gamma_kinematic_dispersive_sequence_alternates_sign() -> None:
    """γ_n^(kin-disp) signs alternate as (-1)^(n-1)."""
    seq = gamma_kinematic_dispersive_sequence(max_order=8)
    for n, val in enumerate(seq, start=1):
        if n % 2 == 1:  # n odd
            assert val > 0.0, f"γ_{n}^(kin-disp) should be positive; got {val}"
        else:  # n even
            assert val < 0.0, f"γ_{n}^(kin-disp) should be negative; got {val}"


def test_gamma_kinematic_dispersive_sequence_rejects_zero() -> None:
    """max_order < 1 raises ValueError."""
    with pytest.raises(ValueError):
        gamma_kinematic_dispersive_sequence(max_order=0)
    with pytest.raises(ValueError):
        gamma_kinematic_dispersive_sequence(max_order=-1)


# ---------------------------------------------------------------------------
# Stage 4-5 tests (skip-marked until γ_2^(loop) / γ_3..γ_7 ship)
# ---------------------------------------------------------------------------


@pytest.mark.skip(
    reason=(
        "Stage 4-5 deliverable. Genuine new content: γ_3 through γ_7 via"
        " systematic loop-order BdG self-energy enumeration. No published"
        " literature anchor expected for γ_3+; cross-validation via internal"
        " consistency checks (parity-alternation pattern; FDR positivity)."
    )
)
def test_gamma_sequence_through_order_7() -> None:
    """compute_gamma_sequence(7, ...) returns 7 BdGSelfEnergyResult entries."""
    c_s = 0.5e-3
    xi = 200e-9
    seq = compute_gamma_sequence(max_order=7, c_s=c_s, xi=xi)
    assert len(seq) == 7
    assert seq[0].cross_validated is True
    assert seq[1].cross_validated is True
    for k in range(2, 7):
        assert seq[k].method.startswith("BdG-")


# ---------------------------------------------------------------------------
# Honest-scoping sanity (Stage 3+ NotImplementedError behavior)
# ---------------------------------------------------------------------------


def test_compute_gamma_n_raises_not_implemented_at_order_3() -> None:
    """Stage 4-5 placeholder behavior: compute_gamma_n(order=3,...) raises."""
    with pytest.raises(NotImplementedError):
        compute_gamma_n(order=3, c_s=0.5e-3, xi=200e-9)


def test_andreev_khalatnikov_stub_explicitly_raises_with_redirect() -> None:
    """Andreev-Khalatnikov anchor stub raises with redirect to kin-disp anchor.

    AK 1963 supplies a finite-T 4-phonon scattering coefficient (T/T_c gradient),
    NOT the T → 0 (ξk) gradient γ_n. This is preserved as a stub for the
    future finite-T SK-EFT extension wave; in Phase 6n Wave 1a.3 it raises
    NotImplementedError with a redirect to gamma_2_kinematic_dispersive_anchor().
    """
    with pytest.raises(NotImplementedError) as exc_info:
        andreev_khalatnikov_anchor_gamma_2()
    # The message should redirect to the proper Stage-3 anchor.
    assert "gamma_2_kinematic_dispersive_anchor" in str(exc_info.value)
    assert "finite-T" in str(exc_info.value)


# ---------------------------------------------------------------------------
# Stage 3 cross-module integration: kinematic sequence → Padé-Borel pipeline
# (Session 12 cross-bridge between bdg_self_energy.py and borel.py)
# ---------------------------------------------------------------------------


def test_kinematic_sequence_ratio_test_signals_geometric_not_gevrey1() -> None:
    """Ratio test on γ_n^(kin-disp) sequence signals geometric (not Gevrey-1).

    Substantive Stage-3 cross-module integration: feed the closed-form
    kinematic-dispersive sequence into ``borel.ratio_test``. Expected
    behavior:

    - For Gevrey-1 (a_n ~ n! / A^n): R_n = a_{n+1} / ((n+1)·a_n) → 1/A,
      a nonzero positive constant.
    - For geometric (a_n ~ C / A^n): R_n = a_{n+1} / ((n+1)·a_n)
      ~ 1 / ((n+1)·A) → 0 monotonically.

    The kinematic-dispersive sequence γ_n^(kin-disp) is geometric per
    `gamma_kinematic_dispersive_sequence_asymptotic_ratio` above; its
    ratio-test signature must therefore decay to zero. This test confirms
    Wave 1a.2 Padé-Borel infrastructure correctly distinguishes the two
    asymptotic-growth classes on the closed-form Stage-3 sequence.

    For the kinematic piece specifically:
        |R_n| = |γ_{n+1}^(kin-disp)| / ((n+1) · |γ_n^(kin-disp)|)
              = (2n-1) / (8 n (n+1))   for n ≥ 1,
        ∼ 1/(4n²) → 0.
    """
    from src.resurgence.bdg_self_energy import gamma_kinematic_dispersive_sequence
    from src.resurgence.borel import ratio_test

    seq = list(gamma_kinematic_dispersive_sequence(max_order=15))
    R = ratio_test(seq)

    # Initial ratio at n=1: γ_2^(kin-disp) / (2 · γ_1^(kin-disp)) = (-1/8) / 2 = -1/16
    # Wait — ratio_test uses R_n = a_{n+1} / ((n+1) a_n) with n=0, 1, ..., len-2 indexing.
    # So R[0] = γ_2 / (1 · γ_1) = -1/8 ≈ -0.125. Confirmed.
    assert R[0] == pytest.approx(-1.0 / 8.0, rel=1e-9)

    # Closed-form check at n=1 (= R[1]): γ_3 / (2 · γ_2) = (3/128) / (2 · (-1/8))
    # = (3/128) / (-1/4) = -3/32 ≈ -0.09375
    assert R[1] == pytest.approx(-3.0 / 32.0, rel=1e-9)

    # Monotone decay to 0 in absolute value (geometric signature).
    abs_R = [abs(r) for r in R]
    for i in range(len(abs_R) - 1):
        assert abs_R[i] >= abs_R[i + 1], (
            f"|R[{i}]| = {abs_R[i]} should ≥ |R[{i+1}]| = {abs_R[i+1]}"
        )

    # Asymptotic decay: R[10] should be much smaller than R[0] (factor << 1).
    # For Gevrey-1, R[10] would be ≈ R[0] (constant).
    assert abs_R[10] < abs_R[0] / 4, (
        f"|R[10]| = {abs_R[10]} should be << |R[0]| = {abs_R[0]} for geometric series"
    )

    # Final ratio must be small (decaying to 0).
    assert abs_R[-1] < 0.05, (
        f"|R[{len(R) - 1}]| = {abs_R[-1]} should be < 0.05 for clean geometric decay"
    )


def test_kinematic_sequence_borel_transform_has_no_finite_singularity() -> None:
    """Padé-Borel applied to kinematic-dispersive γ_n returns no positive-real pole.

    Substantive consequence of `kinDispSeq_borelTransform_bounded` (Lean,
    Session 12) at the Python pipeline level: a geometric series Borel-
    transforms to an entire function, which has no finite singularities.
    `leading_borel_singularity` should therefore return None on the
    kinematic-dispersive sequence (potentially modulo numerical noise from
    the Padé approximant).

    This is the load-bearing end-to-end verification that the Wave 1a.2
    Padé-Borel infrastructure correctly classifies geometric vs Gevrey-1
    sequences on the closed-form Stage-3 input.
    """
    from src.resurgence.bdg_self_energy import gamma_kinematic_dispersive_sequence
    from src.resurgence.borel import leading_borel_singularity

    seq = list(gamma_kinematic_dispersive_sequence(max_order=15))
    # M=4 with N=4 ⇒ needs 9 ≤ 15 coefficients ✓
    A = leading_borel_singularity(seq, M=4)
    # Kinematic piece is geometric ⇒ Borel transform entire ⇒ no positive-real
    # pole at finite distance. `leading_borel_singularity` returns None or a
    # large-real / spurious-imaginary root that gets filtered by imag_tol.
    assert A is None, (
        f"Expected None (entire Borel transform) for geometric kinematic "
        f"sequence; got A = {A}. If a finite positive-real pole was found, "
        f"the kinematic piece is being mis-classified as Gevrey-1."
    )


def test_kinematic_sequence_lambda_uv_estimate_returns_none() -> None:
    """λ_UV estimate from kinematic-only sequence: None (no resurgence content).

    Direct cross-module consequence: with no Borel singularity from the
    kinematic piece, there is no resurgence-theoretic Λ_UV from kinematic
    content alone. Loop-piece (Stage 4) contributions may yield genuine
    Gevrey-1 content with finite Borel action — but the kinematic piece
    by itself doesn't.

    This pins the substantive Stage-3 finding at the Python pipeline level:
    the kinematic piece is Borel-summable; only Stage 4 can establish
    whether the full γ_n verdict yields a finite Λ_UV from resurgence.
    """
    from src.resurgence.bdg_self_energy import gamma_kinematic_dispersive_sequence
    from src.resurgence.borel import lambda_uv_estimate

    kappa = 2.0 * math.pi * 100.0  # Steinhauer-class κ ≈ 628 Hz
    seq = list(gamma_kinematic_dispersive_sequence(max_order=15))
    Lambda_UV = lambda_uv_estimate(seq, kappa, M=4)
    assert Lambda_UV is None, (
        f"Expected None (no resurgence Λ_UV from kinematic-only sequence) "
        f"for geometric series; got Λ_UV = {Lambda_UV}."
    )


# ---------------------------------------------------------------------------
# Stage 4a tests (structural envelope theorem; Session 13)
# ---------------------------------------------------------------------------


def test_geometric_envelope_constructor_validates_bounds() -> None:
    """GeometricEnvelope rejects M < 0 and r ∉ (0, 1)."""
    with pytest.raises(ValueError, match="non-negative"):
        GeometricEnvelope(constant=-1.0, rate=0.5)
    with pytest.raises(ValueError, match=r"\(0, 1\)"):
        GeometricEnvelope(constant=1.0, rate=0.0)
    with pytest.raises(ValueError, match=r"\(0, 1\)"):
        GeometricEnvelope(constant=1.0, rate=1.0)
    with pytest.raises(ValueError, match=r"\(0, 1\)"):
        GeometricEnvelope(constant=1.0, rate=1.5)


def test_kin_disp_envelope_module_constant() -> None:
    """KIN_DISP_ENVELOPE matches the Stage-3 Lean theorem (M=1, r=1/4)."""
    assert KIN_DISP_ENVELOPE.constant == 1.0
    assert KIN_DISP_ENVELOPE.rate == 0.25


def test_kin_disp_envelope_dominates_closed_form_ratios() -> None:
    """The KIN_DISP_ENVELOPE bound `1·(1/4)^k` dominates |γ_{k+1}/γ_1|.

    For each k = 0..6, the closed-form ratio
    |γ_{k+1}^(kin-disp) / γ_1| = C(2k, k) / 16^k
    is ≤ (1/4)^k. This is the Python cross-validation of the Lean
    theorem `kinDispRatio_abs_le_quarter_pow` in
    `lean/SKEFTHawking/Resurgence/KinematicDispersive.lean`.
    """
    for k in range(7):
        closed_form_ratio = abs(
            float(gamma_n_kinematic_dispersive_closed_form(k + 1))
        )
        envelope_bound = KIN_DISP_ENVELOPE.bound_at(k)
        assert closed_form_ratio <= envelope_bound, (
            f"Closed-form ratio {closed_form_ratio} exceeds envelope bound "
            f"{envelope_bound} at k={k} — Lean theorem mismatch."
        )


def test_envelope_sum_combines_constants_and_takes_max_rate() -> None:
    """envelope_sum: sum of two envelopes is M₁+M₂, max(r₁, r₂).

    Direct Python counterpart of Lean theorem `IsGeometric.add` in
    `lean/SKEFTHawking/Resurgence/LoopEnvelope.lean`.
    """
    e1 = GeometricEnvelope(constant=1.0, rate=0.25)
    e2 = GeometricEnvelope(constant=0.5, rate=0.1)
    e_sum = envelope_sum(e1, e2)
    assert e_sum.constant == 1.5
    assert e_sum.rate == 0.25
    # Symmetric in arguments
    assert envelope_sum(e2, e1).rate == 0.25
    assert envelope_sum(e2, e1).constant == 1.5


def test_envelope_sum_dilute_BEC_kinematic_dominates() -> None:
    """Dilute-BEC regime (g_BEC² ≪ 1/4): kinematic rate dominates.

    For Steinhauer-class BECs, g_BEC ~ 10⁻³ ⇒ g_BEC² ~ 10⁻⁶ ≪ 1/4.
    The full envelope rate is then 1/4 — the kinematic-piece value.
    """
    g_BEC_squared = 1.0e-6
    loop = GeometricEnvelope(constant=1.0, rate=g_BEC_squared)
    full = envelope_sum(KIN_DISP_ENVELOPE, loop)
    assert full.rate == 0.25
    assert full.constant == 2.0


def test_envelope_sum_strong_coupling_loop_dominates() -> None:
    """Strong-coupling regime (r_loop > 1/4): loop rate dominates.

    In this regime the envelope theorem still applies (geometric, not
    Gevrey-1) but the asymptotic rate is set by the loop piece.
    """
    loop = GeometricEnvelope(constant=2.0, rate=0.5)
    full = envelope_sum(KIN_DISP_ENVELOPE, loop)
    assert full.rate == 0.5
    assert full.constant == 3.0


def test_envelope_borel_transform_bound_decays_super_geometrically() -> None:
    """Borel transform bound `M·r^n / n!` decays factorially fast.

    Direct counterpart of Lean theorem
    `borelTransform_bounded_of_isGeometric` in `Resurgence/Basic.lean`.
    For the kinematic envelope (M=1, r=1/4), the Borel-transform bound
    at n=10 is (1/4)^10 / 10! ≈ 2.6e-13 — vanishing.
    """
    bound_at_10 = envelope_borel_transform_bound(KIN_DISP_ENVELOPE, n=10)
    expected = (0.25**10) / math.factorial(10)
    assert bound_at_10 == pytest.approx(expected, rel=1e-12)
    # Decay is super-geometric: ratio of consecutive bounds → 0
    bound_n10 = envelope_borel_transform_bound(KIN_DISP_ENVELOPE, n=10)
    bound_n11 = envelope_borel_transform_bound(KIN_DISP_ENVELOPE, n=11)
    ratio = bound_n11 / bound_n10
    # Ratio = r/(n+1) = 0.25/11 ≈ 0.0227
    assert ratio == pytest.approx(0.25 / 11.0, rel=1e-12)


def test_is_borel_summable_under_envelope_true_for_geometric() -> None:
    """IsBorelSummable: True for any GeometricEnvelope (rate ∈ (0,1))."""
    assert is_borel_summable_under_envelope(KIN_DISP_ENVELOPE) is True
    assert (
        is_borel_summable_under_envelope(
            GeometricEnvelope(constant=10.0, rate=0.99)
        )
        is True
    )


def test_stage_4a_verdict_dilute_BEC_full_pipeline() -> None:
    """Stage 4a structural verdict on a dilute-BEC loop envelope.

    Direct counterpart of Lean theorem
    `wave_1a_3_stage4a_structural_closure` in `LoopEnvelope.lean`.

    For dilute BECs (r_loop = g_BEC² ~ 10⁻⁶ ≪ 1/4):
      - Full γ_n envelope rate is 1/4 (kinematic-dominated).
      - Convergence radius in g = (ξk)² is 1/(1/4) = 4.
      - Convergence radius in ξk is √4 = 2 (i.e., k_max = 2 · Λ_UV).
      - Borel-summable (no Gevrey-1 transseries content).
      - Kinematic dominates (loop rate ≤ 1/4).
    """
    loop = GeometricEnvelope(constant=0.5, rate=1.0e-6)
    verdict = stage_4a_structural_verdict(loop)
    assert verdict["full_gamma_constant"] == pytest.approx(1.5, rel=1e-12)
    assert verdict["full_gamma_rate"] == pytest.approx(0.25, rel=1e-12)
    assert verdict["full_gamma_borel_summable"] is True
    assert verdict["kinematic_dominates"] is True
    assert verdict["convergence_radius_g"] == pytest.approx(4.0, rel=1e-12)
    assert verdict["convergence_radius_xik"] == pytest.approx(2.0, rel=1e-12)


def test_stage_4a_verdict_strong_coupling_loop_dominates() -> None:
    """Stage 4a structural verdict on a strong-coupling loop envelope.

    For r_loop > 1/4 the envelope still gives geometric convergence
    (preserves Wave 1a.3 verdict) but with the loop rate dominant; the
    convergence radius is correspondingly smaller.
    """
    loop = GeometricEnvelope(constant=1.0, rate=0.5)
    verdict = stage_4a_structural_verdict(loop)
    assert verdict["full_gamma_rate"] == pytest.approx(0.5, rel=1e-12)
    assert verdict["full_gamma_borel_summable"] is True
    assert verdict["kinematic_dominates"] is False
    assert verdict["convergence_radius_g"] == pytest.approx(2.0, rel=1e-12)


def test_stage_4a_envelope_borel_summable_for_any_geometric_loop() -> None:
    """For any geometric loop-piece envelope (any r_loop ∈ (0, 1)),
    the full γ_n is Borel-summable.

    Substantive content: the envelope theorem decouples the
    Gevrey-1-vs-geometric verdict from the explicit γ_n^(loop) value.
    Even with strong loop coupling (r_loop close to 1), the verdict
    holds: geometric, not Gevrey-1.
    """
    for r_loop in (0.01, 0.1, 0.25, 0.5, 0.9, 0.99):
        loop = GeometricEnvelope(constant=1.0, rate=r_loop)
        verdict = stage_4a_structural_verdict(loop)
        assert verdict["full_gamma_borel_summable"] is True, (
            f"Envelope theorem failed for r_loop = {r_loop}"
        )


def test_stage_4a_envelope_sum_is_associative_with_kin_disp() -> None:
    """envelope_sum(KIN_DISP, loop) == envelope_sum(loop, KIN_DISP).

    Direct test of `IsGeometric.add` symmetry in arguments at the
    Python level; ensures the Lean-Python correspondence is symmetric.
    """
    loop = GeometricEnvelope(constant=2.0, rate=0.1)
    forward = envelope_sum(KIN_DISP_ENVELOPE, loop)
    backward = envelope_sum(loop, KIN_DISP_ENVELOPE)
    assert forward.constant == backward.constant
    assert forward.rate == backward.rate


# ---------------------------------------------------------------------------
# Stage 4b: 2-loop kinematic-dispersive rate preservation + parametric
# loop coupling scaling (Session 14, 2026-05-05)
# ---------------------------------------------------------------------------


def test_stage_4b_2loop_kinematic_rate_equals_one_quarter() -> None:
    """The 2-loop kinematic-dispersive rate equals 1/4 (substrate property).

    Substantive Stage-4b finding: the Bogoliubov dispersion is loop-order-
    independent, so the on-shell evaluation Im Σ^R(ω = ω_Bog(k), k) at any
    loop order carries the same [1+(ξk/2)²]^(-1/2) factor — hence rate 1/4.
    """
    assert BELIAEV_2LOOP_KINEMATIC_RATE == 0.25


def test_stage_4b_2loop_kin_disp_relative_matches_1loop_pattern() -> None:
    """The 2-loop kin-disp relative ratio mirrors 1-loop closed form.

    γ_n^(2-loop, kd) / γ_2^(2-loop, kd) = γ_n^(kin-disp) / γ_2^(kin-disp)
    by rate-preservation. Verifies for n = 2, 3, 4, 5.
    """
    for n in range(2, 6):
        relative = gamma_n_loop_kinematic_dispersive_relative(n)
        expected = (
            gamma_n_kinematic_dispersive_closed_form(n)
            / gamma_n_kinematic_dispersive_closed_form(2)
        )
        assert relative == expected


def test_stage_4b_2loop_kin_disp_relative_index_2_is_one() -> None:
    """At n = 2 the relative ratio is by definition 1."""
    assert gamma_n_loop_kinematic_dispersive_relative(2) == sp.Rational(1)


def test_stage_4b_loop_kin_disp_rejects_n_below_2() -> None:
    """gamma_n_loop_kinematic_dispersive_relative is undefined for n < 2."""
    with pytest.raises(ValueError):
        gamma_n_loop_kinematic_dispersive_relative(1)


def test_stage_4b_loop_envelope_dilute_bec_zero_gives_zero_constant() -> None:
    """At na³ = 0 (idealized non-interacting limit), M_loop = 0."""
    env = loop_envelope_at_dilute_bec(0.0)
    assert env.constant == 0.0
    assert env.rate == 0.25


def test_stage_4b_loop_envelope_dilute_bec_steinhauer_class() -> None:
    """Steinhauer-class BEC na³ ~ 10⁻⁴ → M_loop ~ 0.01·prefactor.

    Substantive content: dilute BECs are deeply in the kinematic-dominated
    regime; M_loop is sub-leading to KIN_DISP_ENVELOPE.constant = 1.
    """
    na3 = 1.0e-4
    env = loop_envelope_at_dilute_bec(na3, prefactor_estimate=1.0)
    assert env.constant == pytest.approx(0.01, rel=1e-12)
    assert env.rate == 0.25


def test_stage_4b_loop_envelope_rejects_invalid_na3() -> None:
    """na³ must lie in [0, 1)."""
    with pytest.raises(ValueError):
        loop_envelope_at_dilute_bec(-0.1)
    with pytest.raises(ValueError):
        loop_envelope_at_dilute_bec(1.0)
    with pytest.raises(ValueError):
        loop_envelope_at_dilute_bec(2.0)


def test_stage_4b_loop_envelope_rejects_negative_prefactor() -> None:
    """prefactor_estimate must be non-negative."""
    with pytest.raises(ValueError):
        loop_envelope_at_dilute_bec(0.5, prefactor_estimate=-1.0)


def test_stage_4b_dilute_bec_verdict_steinhauer_kinematic_dominates() -> None:
    """For Steinhauer-class na³ ~ 10⁻⁴, the kinematic dominates.

    Full envelope: rate = 1/4 exactly, constant = 1 + √(na³)·prefactor ≈ 1.01.
    Borel-summable. Convergence radius in g = (ξk)² is 4 (i.e., ξk = 2 = 2·Λ_UV).
    """
    verdict = stage_4b_dilute_bec_verdict(na3=1.0e-4, prefactor_estimate=1.0)
    assert verdict["full_gamma_rate"] == pytest.approx(0.25, rel=1e-12)
    assert verdict["full_gamma_constant"] == pytest.approx(1.01, rel=1e-12)
    assert verdict["full_gamma_borel_summable"] is True
    assert verdict["kinematic_dominates"] is True
    assert verdict["convergence_radius_g"] == pytest.approx(4.0, rel=1e-12)
    assert verdict["convergence_radius_xik"] == pytest.approx(2.0, rel=1e-12)


def test_stage_4b_dilute_bec_verdict_idealized_zero_loop() -> None:
    """At na³ = 0 the loop piece vanishes; full envelope = kinematic alone."""
    verdict = stage_4b_dilute_bec_verdict(na3=0.0)
    assert verdict["full_gamma_rate"] == 0.25
    assert verdict["full_gamma_constant"] == 1.0
    assert verdict["full_gamma_borel_summable"] is True
    assert verdict["kinematic_dominates"] is True


def test_stage_4b_dilute_bec_verdict_finite_na3_borel_summable() -> None:
    """For any na³ ∈ [0, 1), the FULL γ_n is Borel-summable.

    This is the substantive Stage-4b verdict refinement: combined with
    Stage 4a's envelope theorem, the BEC SK-EFT geometric-not-Gevrey-1
    classification holds for any dilute-gas parameter — robust to the
    explicit unknown γ_2^(loop) prefactor. The convergence-radius
    statement (full_gamma_rate = 1/4) is rigorous because the rate is
    preserved across loop orders by the Bogoliubov-dispersion structure.
    """
    for na3 in (0.001, 0.01, 0.05, 0.1, 0.5, 0.9):
        verdict = stage_4b_dilute_bec_verdict(na3, prefactor_estimate=1.0)
        assert verdict["full_gamma_rate"] == pytest.approx(0.25, rel=1e-12)
        assert verdict["full_gamma_borel_summable"] is True


def test_stage_4b_verdict_compose_with_stage_4a() -> None:
    """Stage 4b composes with Stage 4a: same envelope_sum machinery.

    The dilute-BEC verdict is just stage_4a_structural_verdict applied to
    loop_envelope_at_dilute_bec; verifies the composition is consistent.
    """
    na3 = 0.01
    prefactor = 1.5
    loop_env = loop_envelope_at_dilute_bec(na3, prefactor)
    stage_4a = stage_4a_structural_verdict(loop_env)
    stage_4b = stage_4b_dilute_bec_verdict(na3, prefactor)
    assert stage_4a["full_gamma_constant"] == stage_4b["full_gamma_constant"]
    assert stage_4a["full_gamma_rate"] == stage_4b["full_gamma_rate"]
    assert stage_4a["full_gamma_borel_summable"] == stage_4b["full_gamma_borel_summable"]
    assert stage_4a["kinematic_dominates"] == stage_4b["kinematic_dominates"]


# ---------------------------------------------------------------------------
# Stage 5: Sharpened verdict — γ_6-γ_7 + Padé-Borel re-run + closure
# (Session 14, 2026-05-05)
# ---------------------------------------------------------------------------


def test_stage_5_sharpened_verdict_idealized_no_loop() -> None:
    """Stage 5 sharpened verdict at na³ = 0 (idealized non-interacting limit).

    With no loop piece, the kinematic-only sequence γ_1..γ_7 should:
      - Have ratio test signature decaying monotonically
      - Have no finite leading Borel singularity
      - Yield Λ_UV estimate of None (no resurgence)
      - Combined: BEC SK-EFT geometric, NOT Gevrey-1.
    """
    verdict = stage_5_sharpened_verdict(na3=0.0, max_order=7)
    assert verdict["leading_borel_singularity"] is None
    assert verdict["lambda_uv_estimate"] is None
    assert verdict["is_geometric_not_gevrey1"] is True
    assert verdict["full_gamma_rate"] == 0.25
    assert verdict["full_gamma_borel_summable"] is True
    assert verdict["kinematic_dominates"] is True
    # Sequence is length 7
    assert len(verdict["kinematic_sequence"]) == 7
    # γ_1 is the LO Beliaev anchor
    assert verdict["kinematic_sequence"][0] == pytest.approx(BELIAEV_LO_PREFACTOR)


def test_stage_5_sharpened_verdict_steinhauer_class() -> None:
    """Stage 5 verdict on Steinhauer-class BEC (na³ ~ 10⁻⁴).

    Loop piece is parametrically suppressed; full verdict is unchanged
    from idealized: geometric, rate 1/4, Borel-summable, no resurgence.
    """
    verdict = stage_5_sharpened_verdict(na3=1.0e-4, max_order=7)
    assert verdict["full_gamma_rate"] == 0.25
    assert verdict["full_gamma_borel_summable"] is True
    assert verdict["kinematic_dominates"] is True
    assert verdict["is_geometric_not_gevrey1"] is True
    # Full constant ≈ 1.01 (kinematic 1.0 + loop 0.01)
    assert verdict["full_gamma_constant"] == pytest.approx(1.01, rel=1e-12)


def test_stage_5_sharpened_verdict_gamma_6_gamma_7_closed_form() -> None:
    """Stage 5 ships the γ_6 and γ_7 closed-form coefficients explicitly."""
    verdict = stage_5_sharpened_verdict(na3=0.0, max_order=7)
    # γ_6 = γ_1 · (-1)^5 · C(10, 5) / 16^5 = -γ_1 · 252 / 1048576
    expected_gamma_6 = (
        BELIAEV_LO_PREFACTOR * (-1) * math.comb(10, 5) / (16**5)
    )
    # γ_7 = γ_1 · (-1)^6 · C(12, 6) / 16^6 = +γ_1 · 924 / 16777216
    expected_gamma_7 = (
        BELIAEV_LO_PREFACTOR * (+1) * math.comb(12, 6) / (16**6)
    )
    seq = verdict["kinematic_sequence"]
    assert seq[5] == pytest.approx(expected_gamma_6, rel=1e-12)
    assert seq[6] == pytest.approx(expected_gamma_7, rel=1e-12)


def test_stage_5_ratio_test_decays_monotonically() -> None:
    """Stage 5 sequence ratio test decays monotonically (geometric signature).

    For Gevrey-1, the ratio test would saturate at a positive constant.
    Monotone decay to 0 is the geometric signature.
    """
    verdict = stage_5_sharpened_verdict(na3=0.0, max_order=15)
    assert verdict["ratio_test_monotone_decay"] is True


def test_stage_5_verdict_string_present() -> None:
    """Stage 5 verdict carries a substantive verdict string."""
    verdict = stage_5_sharpened_verdict(na3=0.0)
    assert isinstance(verdict["verdict"], str)
    assert "geometrically convergent" in verdict["verdict"]
    assert "NOT Gevrey-1" in verdict["verdict"]
    assert "ξk = 2 = 2·Λ_UV" in verdict["verdict"]


def test_stage_5_verdict_rejects_max_order_too_small() -> None:
    """Stage 5 requires max_order >= 2 for meaningful Padé-Borel content."""
    with pytest.raises(ValueError):
        stage_5_sharpened_verdict(max_order=1)


def test_stage_5_verdict_rejects_invalid_na3() -> None:
    """Stage 5 inherits na³ ∈ [0, 1) validation from Stage 4b."""
    with pytest.raises(ValueError):
        stage_5_sharpened_verdict(na3=-0.1)
    with pytest.raises(ValueError):
        stage_5_sharpened_verdict(na3=1.0)
