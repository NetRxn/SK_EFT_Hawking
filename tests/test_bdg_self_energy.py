"""Tests for src/resurgence/bdg_self_energy.py.

Phase 6n Wave 1a.3 Path A — Stage 2 γ_1 Beliaev LO derivation tests.

Stage 2 (this revision): γ_1 implementation tests un-skipped + new
numerical-verification tests for the kinematic phase-space integral.

Stage 3+ tests (γ_2 Andreev-Khalatnikov + γ_3..γ_7 higher loops) remain
skip-marked until the underlying functions ship.

References:
  temporary/working-docs/phase6n/wave_1a_3_path_A_stage1.md
  src/resurgence/bdg_self_energy.py module docstring
"""

from __future__ import annotations

import math

import pytest

from src.resurgence.bdg_self_energy import (
    BELIAEV_BOGOLIUBOV_PREFACTOR,
    BELIAEV_KINEMATIC_INTEGRAL,
    BELIAEV_LO_PREFACTOR,
    BdGSelfEnergyResult,
    andreev_khalatnikov_anchor_gamma_2,
    beliaev_anchor_gamma_1,
    beliaev_lo_dimensionless,
    beliaev_lo_rate,
    compute_gamma_n,
    compute_gamma_sequence,
    derive_beliaev_lo_dimensionless,
    derive_beliaev_lo_kinematic_integral,
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


def test_compute_gamma_sequence_ships_only_gamma_1_at_stage_2() -> None:
    """Stage 2 ships only γ_1; max_order ≥ 2 raises NotImplementedError."""
    c_s = 0.5e-3
    xi = 200e-9
    seq_one = compute_gamma_sequence(max_order=1, c_s=c_s, xi=xi)
    assert len(seq_one) == 1
    assert seq_one[0].order == 1
    assert seq_one[0].cross_validated is True
    with pytest.raises(NotImplementedError):
        compute_gamma_sequence(max_order=2, c_s=c_s, xi=xi)


def test_compute_gamma_n_rejects_nonpositive_order() -> None:
    """compute_gamma_n raises ValueError for order ≤ 0."""
    with pytest.raises(ValueError):
        compute_gamma_n(order=0, c_s=0.5e-3, xi=200e-9)
    with pytest.raises(ValueError):
        compute_gamma_n(order=-1, c_s=0.5e-3, xi=200e-9)


# ---------------------------------------------------------------------------
# Stage 3+ tests (skip-marked until implementation ships)
# ---------------------------------------------------------------------------


@pytest.mark.skip(
    reason=(
        "Stage 3 deliverable. Implement γ_2 via Andreev-Khalatnikov 1963"
        " NLO scattering, cross-validate against published value in AK 1963"
        " / Pitaevskii-Stringari §4.5."
    )
)
def test_gamma_2_matches_andreev_khalatnikov_anchor() -> None:
    """γ_2 from compute_gamma_n(2, ...) matches Andreev-Khalatnikov anchor."""
    c_s = 0.5e-3
    xi = 200e-9
    result = compute_gamma_n(order=2, c_s=c_s, xi=xi)
    anchor = andreev_khalatnikov_anchor_gamma_2()
    assert result.cross_validated is True
    assert result.gamma == pytest.approx(anchor, rel=1e-3)


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
    # γ_1 + γ_2 cross-validated against literature anchors.
    assert seq[0].cross_validated is True
    assert seq[1].cross_validated is True
    # γ_3-γ_7 internal-consistency-validated only.
    for k in range(2, 7):
        assert seq[k].method.startswith("BdG-")


@pytest.mark.skip(
    reason="Stage 3 deliverable — depends on test_gamma_2_matches_andreev_khalatnikov_anchor."
)
def test_andreev_khalatnikov_anchor_returns_finite() -> None:
    """Andreev-Khalatnikov γ_2 anchor is a finite (possibly negative) value."""
    anchor = andreev_khalatnikov_anchor_gamma_2()
    assert isinstance(anchor, float)
    # Sign and magnitude depend on the convention in AK 1963; checked at Stage 3.


# ---------------------------------------------------------------------------
# Stage 3+ NotImplementedError sanity (Stage 3+ placeholder behavior is honest)
# ---------------------------------------------------------------------------


def test_compute_gamma_n_raises_not_implemented_at_order_2() -> None:
    """Stage 3+ placeholder behavior: compute_gamma_n(order=2,...) raises."""
    with pytest.raises(NotImplementedError):
        compute_gamma_n(order=2, c_s=0.5e-3, xi=200e-9)


def test_compute_gamma_n_raises_not_implemented_at_order_3() -> None:
    """Stage 4-5 placeholder behavior: compute_gamma_n(order=3,...) raises."""
    with pytest.raises(NotImplementedError):
        compute_gamma_n(order=3, c_s=0.5e-3, xi=200e-9)


def test_andreev_khalatnikov_anchor_stub_raises_not_implemented_at_stage_2() -> None:
    """Stage 3 placeholder: Andreev-Khalatnikov anchor stub still raises at Stage 2."""
    with pytest.raises(NotImplementedError):
        andreev_khalatnikov_anchor_gamma_2()
