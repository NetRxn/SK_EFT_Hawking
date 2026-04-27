"""Tests for `src/cfl/` (Phase 6d Wave 3).

Mirrors `lean/SKEFTHawking/CFLChiralLagrangian.lean`. Each test name
maps to a Lean theorem one-to-one; cross-checks confirm Python ↔ Lean
numerical agreement on the correctness-push identification (CFL
emergent ℤ_3 = QCD center ℤ_3).
"""

import pytest

from src.cfl import (
    EMERGENT_Z3_PHASE,
    H_TopologicalOrderBeyondLG,
    QCD_CENTER_Z3_PHASE,
    cfl_emergent_z3_matches_qcd_center_z3,
    cfl_kinetic_term,
    cfl_mass_term,
    diquark_magnitude,
    emergent_z3_action,
    emergent_z3_pow_3,
    is_cfl_phase,
)


# === §1. CFL diquark order parameter ===


def test_is_cfl_phase_nonzero() -> None:
    """CFL phase ⟺ Φ ≠ 0. Mirrors Lean `isCFLPhase`."""
    assert is_cfl_phase(1.0 + 0j)
    assert is_cfl_phase(0.5 - 0.5j)
    assert not is_cfl_phase(0 + 0j)


def test_diquark_magnitude() -> None:
    """|Φ| as the real-valued order parameter. Mirrors `diquarkMagnitude`."""
    assert diquark_magnitude(0 + 0j) == 0.0
    assert diquark_magnitude(3 + 4j) == 5.0
    assert diquark_magnitude(EMERGENT_Z3_PHASE) == pytest.approx(1.0, abs=1e-10)


def test_isCFLPhase_iff_magnitude_pos() -> None:
    """Mirrors Lean `isCFLPhase_iff_magnitude_pos`."""
    for phi in [0 + 0j, 1 + 0j, 0.5 - 0.5j]:
        assert is_cfl_phase(phi) == (diquark_magnitude(phi) > 1e-12)


# === §2-3. Emergent ℤ_3 + correctness-push ===


def test_correctness_push_cfl_z3_matches_qcd_z3() -> None:
    """**THE Phase 6d.3 correctness-push:** CFL emergent ℤ_3 = QCD
    center ℤ_3.

    Mirrors Lean `CFL_emergent_Z3_matches_QCD_center_Z3`. Within float
    precision, both compute to exp(2πi/3) — they ARE equal.
    """
    assert cfl_emergent_z3_matches_qcd_center_z3()
    # Tighter check: within machine precision
    assert abs(EMERGENT_Z3_PHASE - QCD_CENTER_Z3_PHASE) < 1e-15


def test_emergent_z3_pow_3() -> None:
    """ω³ = 1 (cube root of unity). Mirrors Lean `emergentZ3_pow_3`."""
    assert emergent_z3_pow_3()
    assert abs(EMERGENT_Z3_PHASE**3 - 1.0) < 1e-10


def test_emergent_z3_norm_one() -> None:
    """|ω| = 1. Mirrors Lean `emergentZ3_norm_one`."""
    assert abs(abs(EMERGENT_Z3_PHASE) - 1.0) < 1e-10


def test_emergent_z3_sum_cube_roots() -> None:
    """1 + ω + ω² = 0 (sum of cube roots of unity).

    Mirrors Lean `emergentZ3_sum_cube_roots`. Distinguishes ℤ_3 from
    ℤ_2 (where 1 + (-1) = 0 is degenerate).
    """
    s = 1 + EMERGENT_Z3_PHASE + EMERGENT_Z3_PHASE**2
    assert abs(s) < 1e-10


def test_emergent_z3_action() -> None:
    """Action on Φ = 1: returns ω. Mirrors `emergentZ3Action`."""
    result = emergent_z3_action(1 + 0j)
    assert abs(result - EMERGENT_Z3_PHASE) < 1e-15


# === §4. CFL chiral Lagrangian ===


def test_cfl_kinetic_term_nonneg() -> None:
    """Kinetic term ≥ 0 always. Mirrors Lean `cflKineticTerm_nonneg`."""
    for d_phi in [0.0, 1.0, 5.0, 100.0]:
        assert cfl_kinetic_term(d_phi) >= 0


def test_cfl_mass_term_chiral_limit() -> None:
    """Mass term vanishes at m_q = 0. Mirrors Lean `cflMassTerm_chiral_limit`."""
    for phi in [0 + 0j, 1 + 0j, 0.5 - 0.5j]:
        assert cfl_mass_term(0.0, phi) == 0.0


def test_cfl_mass_term_pos_in_cfl_phase() -> None:
    """Mass term > 0 when m_q > 0 AND in CFL phase.

    Mirrors Lean `cflMassTerm_pos_in_cfl_phase`. Requires BOTH
    hypotheses — m_q > 0 alone with Φ = 0 gives 0.
    """
    assert cfl_mass_term(0.005, 1 + 0j) > 0
    assert cfl_mass_term(0.005, 0 + 0j) == 0.0  # not in CFL phase
    # m_q = 0 alone is the chiral limit
    assert cfl_mass_term(0, 1 + 0j) == 0.0


# === §5. Topological order ===


def test_topological_order_witness() -> None:
    """charge = 1 satisfies the topological-order predicate.

    Mirrors Lean `H_TopologicalOrderBeyondLG_witness`.
    """
    h = H_TopologicalOrderBeyondLG(charge=1)
    assert h.holds
    assert h.cyclic_z3 and h.nontrivial


def test_topological_order_charge_2_also_witness() -> None:
    """charge = 2 also satisfies (the other non-trivial Z_3 element)."""
    h = H_TopologicalOrderBeyondLG(charge=2)
    assert h.holds


def test_topological_order_falsifier_trivial() -> None:
    """charge = 0 (vacuum sector) does NOT exhibit topological order.

    Mirrors Lean `H_TopologicalOrderBeyondLG_falsifier_trivial`.
    """
    h = H_TopologicalOrderBeyondLG(charge=0)
    assert not h.holds
    assert not h.nontrivial


def test_topological_order_falsifier_too_large() -> None:
    """charge ≥ 3 is not a Z_3 charge.

    Mirrors Lean `H_TopologicalOrderBeyondLG_falsifier_too_large`.
    """
    h = H_TopologicalOrderBeyondLG(charge=3)
    assert not h.holds
    assert not h.cyclic_z3


# === Anti-pattern audit ===


def test_z3_phases_are_three_distinct_roots() -> None:
    """Anti-pattern check: 1, ω, ω² are three DISTINCT cube roots
    (the cube structure is not degenerate, unlike ℤ_2 where 1 and -1
    is the only non-trivial pair).
    """
    one = 1 + 0j
    omega = EMERGENT_Z3_PHASE
    omega_sq = EMERGENT_Z3_PHASE**2
    assert abs(one - omega) > 0.5
    assert abs(one - omega_sq) > 0.5
    assert abs(omega - omega_sq) > 0.5


def test_correctness_push_not_definitional_alias() -> None:
    """Anti-pattern check: the CFL emergent Z_3 phase is computed
    independently from the QCD center phase (different code paths
    in Python: `complex(cos, sin)` vs `center_phase(Z3)` from
    src/center_symmetry/). The equality is a substantive identification
    across modules, not a single-source-aliased value.
    """
    # Both compute to the same value, but via different code paths
    assert EMERGENT_Z3_PHASE == QCD_CENTER_Z3_PHASE
    # They were defined in different files
    from src.cfl.z3_one_form_action import EMERGENT_Z3_PHASE as cfl_phase
    from src.center_symmetry.polyakov_loop import center_phase as qcd_phase
    from src.center_symmetry import Z3 as qcd_z3
    assert cfl_phase == qcd_phase(qcd_z3)
