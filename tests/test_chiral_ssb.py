"""Tests for `src/chiral_ssb/` (Phase 6d Wave 2).

Mirrors `lean/SKEFTHawking/ChiralSSB_QCD.lean`. Each test maps to a Lean
theorem one-to-one where applicable; cross-checks confirm Python ↔ Lean
numerical agreement on the GMOR PDG match and tetrad-quark naturalness.
"""

import pytest

from src.chiral_ssb import (
    FLAG_LATTICE_VALUE,
    H_TetradQuarkScalesNatural,
    PDG_F_PI,
    PDG_M_PI,
    PDG_M_Q,
    QuarkCondensate,
    gmor_holds,
    gmor_lhs,
    gmor_pdg_match,
    gmor_rhs,
    is_quark_condensate_candidate,
)


# === §1. Quark condensate ===


def test_quark_condensate_requires_negative_sigma() -> None:
    """sigma < 0 constraint mirrors Lean `sigma_neg`."""
    with pytest.raises(ValueError):
        QuarkCondensate(sigma=0.0)
    with pytest.raises(ValueError):
        QuarkCondensate(sigma=0.01)
    # Negative sigma OK
    qc = QuarkCondensate(sigma=-0.01)
    assert qc.sigma == -0.01


def test_flag_lattice_value() -> None:
    """FLAG 2021 lattice central value: ⟨q̄q⟩ ≈ −0.0227 GeV³.

    Mirrors Lean `flagLatticeValue`.
    """
    assert FLAG_LATTICE_VALUE.sigma == -0.0227
    assert FLAG_LATTICE_VALUE.sigma < 0


def test_is_quark_condensate_candidate_close_match() -> None:
    """A condensate within tol of the FLAG value passes the candidate test."""
    qc = QuarkCondensate(sigma=-0.0228)  # very close to -0.0227
    assert is_quark_condensate_candidate(qc, sigma_obs=-0.0227, tol=0.05)


def test_not_isQuarkCondensateCandidate_of_too_negative() -> None:
    """A condensate too negative fails the candidate test.

    Mirrors Lean `not_isQuarkCondensateCandidate_of_too_negative`.
    """
    qc = QuarkCondensate(sigma=-0.05)  # 2x too negative
    assert not is_quark_condensate_candidate(qc, sigma_obs=-0.0227, tol=0.1)


# === §2. GMOR relation ===


def test_gmor_lhs_nonneg() -> None:
    """LHS = m_π² · f_π² ≥ 0. Mirrors Lean `gmor_lhs_nonneg`."""
    assert gmor_lhs(PDG_M_PI, PDG_F_PI) > 0
    assert gmor_lhs(0, 0.5) == 0
    assert gmor_lhs(0.5, 0) == 0


def test_gmor_rhs_pos_of_quark_mass_pos() -> None:
    """RHS > 0 when m_q > 0 (and σ < 0 by structure).

    Mirrors Lean `gmor_rhs_pos_of_quark_mass_pos`.
    """
    assert gmor_rhs(PDG_M_Q, FLAG_LATTICE_VALUE) > 0


def test_gmor_pdg_match() -> None:
    """GMOR holds at PDG/FLAG central values within 1e-4 GeV⁴.

    Mirrors Lean `gmor_pdg_match`. The LHS = (0.137)² · (0.092)² ≈
    1.589e-4 GeV⁴; the RHS = −2 · 0.0035 · (−0.0227) ≈ 1.589e-4 GeV⁴.
    """
    assert gmor_pdg_match()
    diff = abs(
        gmor_lhs(PDG_M_PI, PDG_F_PI) - gmor_rhs(PDG_M_Q, FLAG_LATTICE_VALUE)
    )
    assert diff < 1.0e-4
    # Tighter: agreement to ~4e-8
    assert diff < 1.0e-7


def test_gmor_holds_within_tolerance() -> None:
    """gmor_holds returns True at PDG values, False at exaggerated values."""
    assert gmor_holds(PDG_M_PI, PDG_F_PI, PDG_M_Q, FLAG_LATTICE_VALUE)
    # 10x larger pion mass → LHS 100x larger → fails GMOR
    assert not gmor_holds(10 * PDG_M_PI, PDG_F_PI, PDG_M_Q, FLAG_LATTICE_VALUE)


# === §3. Chiral SSB consequences ===


def test_chiral_unbroken_violates_gmor_in_python() -> None:
    """Non-condensed phase (σ ≥ 0) violates GMOR for positive m_q + non-zero
    pion sector.

    Python check (Lean `chiral_unbroken_violates_gmor` is a False-conclusion
    contradiction theorem; Python encodes this as an inequality check).
    """
    # σ = 0 → RHS = 0; LHS > 0; not equal
    rhs_zero = -2.0 * PDG_M_Q * 0.0
    lhs = gmor_lhs(PDG_M_PI, PDG_F_PI)
    assert rhs_zero == 0
    assert lhs > 0
    assert lhs != rhs_zero


# === §4. Tetrad-quark naturalness (correctness-push) ===


def test_tetrad_quark_naturalness_witness() -> None:
    """Unit-ratio v_tetrad = sigma_scale satisfies naturalness.

    Mirrors Lean `H_TetradQuarkScalesNatural_witness`.
    """
    h = H_TetradQuarkScalesNatural(v_tetrad=1.0, sigma_scale=1.0)
    assert h.holds
    assert h.positivity
    assert h.lower_bound
    assert h.upper_bound


def test_tetrad_quark_naturalness_falsifier_super_large() -> None:
    """v_tetrad = 100 · sigma_scale fails the upper-bound conjunct.

    Mirrors Lean `H_TetradQuarkScalesNatural_falsifier_super_large`.
    """
    h = H_TetradQuarkScalesNatural(v_tetrad=100.0, sigma_scale=1.0)
    assert not h.holds
    assert not h.upper_bound
    assert h.lower_bound  # 100 > 1/10 = 0.1, so lower bound passes


def test_tetrad_quark_naturalness_falsifier_super_small() -> None:
    """v_tetrad = sigma_scale / 100 fails the lower-bound conjunct.

    Mirrors Lean `H_TetradQuarkScalesNatural_falsifier_super_small`.
    """
    h = H_TetradQuarkScalesNatural(v_tetrad=0.01, sigma_scale=1.0)
    assert not h.holds
    assert not h.lower_bound


# === Anti-pattern audit ===


def test_gmor_central_values_within_one_part_in_ten_thousand() -> None:
    """Anti-pattern check: the GMOR PDG match is *quantitative*, not a
    within-own-band tautology — agreement is at ~3-4e-8, well below the
    1e-4 tolerance and far tighter than the ~3e-3 PDG uncertainty band
    on m_q.
    """
    diff = abs(
        gmor_lhs(PDG_M_PI, PDG_F_PI) - gmor_rhs(PDG_M_Q, FLAG_LATTICE_VALUE)
    )
    # Agreement is ~ 3.9e-8, much tighter than 1e-4
    assert diff / 1.0e-4 < 1.0e-3


def test_quark_condensate_rejection_at_zero() -> None:
    """Anti-pattern check: the QuarkCondensate dataclass strictly enforces
    sigma < 0 — the chiral-unbroken phase is structurally forbidden as a
    QuarkCondensate, mirroring the Lean `sigma_neg` invariant.
    """
    with pytest.raises(ValueError):
        QuarkCondensate(sigma=0.0)
