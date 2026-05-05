"""Tests for src/resurgence/bdg_self_energy.py (Path A Stage 1 skeleton).

Phase 6n Wave 1a.3 Path A — Stage 1 module skeleton tests.

All tests skip-marked at Stage 1 until the underlying functions are
implemented at Stage 2+. The skip messages document the literature
anchors that will be cross-validated when each stage ships.

References:
  temporary/working-docs/phase6n/wave_1a_3_path_A_stage1.md
  src/resurgence/bdg_self_energy.py module docstring
"""

from __future__ import annotations

import pytest

from src.resurgence.bdg_self_energy import (
    BdGSelfEnergyResult,
    andreev_khalatnikov_anchor_gamma_2,
    beliaev_anchor_gamma_1,
    compute_gamma_n,
    compute_gamma_sequence,
)


# ---------------------------------------------------------------------------
# Stage 1 sanity tests (no skip needed; verify the module is importable)
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
# Stage 2+ tests (skip-marked until implementation ships)
# ---------------------------------------------------------------------------


@pytest.mark.skip(
    reason=(
        "Stage 2 deliverable. Implement γ_1 via Beliaev 1958 LO scattering"
        " (Beliaev decay + Landau damping channels), cross-validate against"
        " published value in Beliaev 1958 / Pitaevskii-Stringari §4.4 /"
        " Liu-Fukuyama 1985."
    )
)
def test_gamma_1_matches_beliaev_anchor() -> None:
    """γ_1 from compute_gamma_n(1, ...) matches Beliaev 1958 anchor."""
    c_s = 0.5e-3  # m/s; Steinhauer-class BEC
    xi = 200e-9  # m; Steinhauer-class healing length
    result = compute_gamma_n(order=1, c_s=c_s, xi=xi)
    anchor = beliaev_anchor_gamma_1()
    assert result.cross_validated is True
    # Stage 2 specifies the tolerance based on the primary-source's stated
    # uncertainty + the diagrammatic computation's truncation error.
    assert result.gamma == pytest.approx(anchor, rel=1e-3)


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


@pytest.mark.skip(reason="Stage 2 deliverable — depends on test_gamma_1_matches_beliaev_anchor.")
def test_beliaev_anchor_returns_finite_positive() -> None:
    """Beliaev γ_1 anchor is a finite positive value."""
    anchor = beliaev_anchor_gamma_1()
    assert anchor > 0.0
    assert anchor < 1.0  # dimensionless rate; should be < 1 for weak coupling


@pytest.mark.skip(reason="Stage 3 deliverable — depends on test_gamma_2_matches_andreev_khalatnikov_anchor.")
def test_andreev_khalatnikov_anchor_returns_finite() -> None:
    """Andreev-Khalatnikov γ_2 anchor is a finite (possibly negative) value."""
    anchor = andreev_khalatnikov_anchor_gamma_2()
    assert isinstance(anchor, float)
    # Sign and magnitude depend on the convention in AK 1963; checked at Stage 3.


# ---------------------------------------------------------------------------
# NotImplementedError sanity (Stage 1 placeholder behavior is honest)
# ---------------------------------------------------------------------------


def test_compute_gamma_n_raises_not_implemented_at_stage_1() -> None:
    """Stage 1 placeholder behavior: compute_gamma_n raises NotImplementedError."""
    with pytest.raises(NotImplementedError):
        compute_gamma_n(order=1, c_s=0.5e-3, xi=200e-9)


def test_compute_gamma_sequence_raises_not_implemented_at_stage_1() -> None:
    """Stage 1 placeholder: compute_gamma_sequence raises NotImplementedError."""
    with pytest.raises(NotImplementedError):
        compute_gamma_sequence(max_order=7, c_s=0.5e-3, xi=200e-9)


def test_anchor_stubs_raise_not_implemented_at_stage_1() -> None:
    """Stage 1 placeholder: literature anchor stubs raise NotImplementedError."""
    with pytest.raises(NotImplementedError):
        beliaev_anchor_gamma_1()
    with pytest.raises(NotImplementedError):
        andreev_khalatnikov_anchor_gamma_2()
