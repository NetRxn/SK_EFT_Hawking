"""Tests for src.dark_sector.z16_hidden_sector.

Cross-checks the Python enumeration against the Lean-proved facts in
``HiddenSectorClassification.lean``:

- T1 (anomaly_index_weyl_singlet): N singlets have index N mod 16.
- T2 (hidden_sector_anomaly_value): 3-gen SM without ν_R requires N ≡ 3 mod 16.
- T3 (minimal_singlet_count): minimum N satisfying T2 is 3.
- T10 (all_singlet_solutions_bounded): for N ≤ 32, solutions are {3, 19}.
- T11 (z4x_singlet_constraint): ℤ₁₆ does not imply ∑ X³ = 0.
"""

from __future__ import annotations

import pytest

from src.dark_sector.z16_hidden_sector import (
    DM_CANDIDATE_MATRIX,
    HIDDEN_SECTOR_REQUIRED_INDEX,
    SM_3GEN_NO_NUR_ANOMALY,
    DMCandidate,
    enumerate_bounded_solutions,
    match_n_weyl_to_candidates,
    singlet_anomaly_index,
    u1x_linear_sum,
    verify_anomaly_cancellation,
    verify_joint_cancellation,
    z4x_cubic_anomaly,
)


class TestConstants:
    def test_sm_3gen_no_nur_anomaly_value(self):
        """3 × 15 = 45 ≡ 13 mod 16 — matches Z16AnomalyComputation.three_gen_mod16."""
        assert SM_3GEN_NO_NUR_ANOMALY == 13
        assert (3 * 15) % 16 == SM_3GEN_NO_NUR_ANOMALY

    def test_hidden_sector_required_index(self):
        """Hidden sector must carry +3 mod 16 to close (13 + N) ≡ 0."""
        assert HIDDEN_SECTOR_REQUIRED_INDEX == 3
        assert (SM_3GEN_NO_NUR_ANOMALY + HIDDEN_SECTOR_REQUIRED_INDEX) % 16 == 0


class TestSingletAnomalyIndex:
    """Lean anchor: T1 anomaly_index_weyl_singlet."""

    def test_zero(self):
        assert singlet_anomaly_index(0) == 0

    def test_one(self):
        assert singlet_anomaly_index(1) == 1

    def test_sixteen_wraps(self):
        assert singlet_anomaly_index(16) == 0

    def test_matches_mod_16(self):
        """For all N in [0, 50), index equals N mod 16."""
        for n in range(50):
            assert singlet_anomaly_index(n) == n % 16

    def test_rejects_negative(self):
        with pytest.raises(ValueError):
            singlet_anomaly_index(-1)


class TestEnumerateBoundedSolutions:
    """Lean anchor: T10 all_singlet_solutions_bounded."""

    def test_default_max_n_32(self):
        """For N ≤ 32, solutions are exactly {3, 19} — matches Lean."""
        assert enumerate_bounded_solutions() == [3, 19]
        assert enumerate_bounded_solutions(32) == [3, 19]

    def test_max_n_below_first_solution(self):
        """For max_n < 3, no solutions."""
        assert enumerate_bounded_solutions(2) == []

    def test_first_solution_at_three(self):
        """Lean T3: minimal is 3."""
        assert enumerate_bounded_solutions(3) == [3]
        assert enumerate_bounded_solutions(18) == [3]
        assert enumerate_bounded_solutions(19) == [3, 19]

    def test_periodicity_16(self):
        """Solutions are arithmetic progression with period 16."""
        large = enumerate_bounded_solutions(100)
        assert large == [3, 19, 35, 51, 67, 83, 99]
        differences = [large[i + 1] - large[i] for i in range(len(large) - 1)]
        assert all(d == 16 for d in differences)


class TestMinimalSingletCount:
    """Lean anchor: T3 minimal_singlet_count — minimum N with index = 3 is 3."""

    def test_zero_through_two_fail(self):
        """N ∈ {0, 1, 2} do not satisfy the constraint."""
        for n in range(3):
            assert singlet_anomaly_index(n) != HIDDEN_SECTOR_REQUIRED_INDEX

    def test_three_satisfies(self):
        assert singlet_anomaly_index(3) == HIDDEN_SECTOR_REQUIRED_INDEX

    def test_no_smaller_solution(self):
        """Enumeration agrees: first solution is at N = 3."""
        assert enumerate_bounded_solutions(32)[0] == 3


class TestVerifyAnomalyCancellation:
    """Lean anchor: T2 hidden_sector_anomaly_value."""

    def test_three_cancels(self):
        assert verify_anomaly_cancellation(3)

    def test_nineteen_cancels(self):
        assert verify_anomaly_cancellation(19)

    def test_zero_fails(self):
        assert not verify_anomaly_cancellation(0)

    def test_solutions_all_cancel(self):
        """Every enumerated solution must verify."""
        for n in enumerate_bounded_solutions(100):
            assert verify_anomaly_cancellation(n)

    def test_non_solutions_all_fail(self):
        """Every non-solution up to 32 must fail."""
        solutions = set(enumerate_bounded_solutions(32))
        for n in range(33):
            if n not in solutions:
                assert not verify_anomaly_cancellation(n), (
                    f"N={n} should not satisfy ℤ₁₆ cancellation"
                )


class TestDMCandidateMatrix:
    """DM candidate metadata sanity checks."""

    def test_all_candidates_populated(self):
        """S-0, S-1, C-1, T-0 all present."""
        assert set(DM_CANDIDATE_MATRIX.keys()) == {"S-0", "S-1", "C-1", "T-0"}

    def test_singlet_candidates_satisfy_z16(self):
        """Every singlet_cancellation candidate's n_weyl satisfies N mod 16 = 3.

        C-1 (mixed-charge) and T-0 (TQFT) are excluded — their cancellation
        mechanisms involve ℤ₄ charge algebra / topological contributions beyond
        the pure SM-singlet count rule formalized in Lean T2/T3/T10.
        """
        for tag, candidate in DM_CANDIDATE_MATRIX.items():
            if not candidate.singlet_cancellation:
                continue
            assert verify_anomaly_cancellation(candidate.n_weyl), (
                f"Singlet-cancellation candidate {tag} "
                f"(n_weyl={candidate.n_weyl}) fails ℤ₁₆"
            )

    def test_mixed_and_topological_candidates_not_singlet(self):
        """C-1 and T-0 are flagged as non-singlet (different cancellation)."""
        assert not DM_CANDIDATE_MATRIX["C-1"].singlet_cancellation
        assert not DM_CANDIDATE_MATRIX["T-0"].singlet_cancellation

    def test_s0_minimal(self):
        """S-0 is the minimal particle candidate (3 Weyl = 3 sterile ν)."""
        assert DM_CANDIDATE_MATRIX["S-0"].n_weyl == 3
        assert "sterile-neutrino" in DM_CANDIDATE_MATRIX["S-0"].dm_types

    def test_s1_nineteen(self):
        assert DM_CANDIDATE_MATRIX["S-1"].n_weyl == 19

    def test_t0_topological_zero_particles(self):
        assert DM_CANDIDATE_MATRIX["T-0"].n_weyl == 0
        assert "topological" in DM_CANDIDATE_MATRIX["T-0"].dm_types


class TestMatchNWeylToCandidates:
    def test_three_weyl_matches_s0(self):
        matches = match_n_weyl_to_candidates(3)
        assert len(matches) == 1
        assert matches[0].tag == "S-0"

    def test_nineteen_weyl_matches_s1(self):
        matches = match_n_weyl_to_candidates(19)
        assert len(matches) == 1
        assert matches[0].tag == "S-1"

    def test_eight_weyl_matches_c1(self):
        matches = match_n_weyl_to_candidates(8)
        assert len(matches) == 1
        assert matches[0].tag == "C-1"

    def test_zero_weyl_matches_t0(self):
        """Only the T-0 TQFT candidate has zero particle content."""
        matches = match_n_weyl_to_candidates(0)
        assert len(matches) == 1
        assert matches[0].tag == "T-0"

    def test_unmatched_count(self):
        """N = 5 has no registered candidate."""
        assert match_n_weyl_to_candidates(5) == []


class TestZ4XCubicAnomaly:
    """Lean anchor: T11 z4x_singlet_constraint — ℤ₁₆ does not imply ∑X³ = 0."""

    def test_all_unit_charges_nonzero(self):
        """Lean T11 witness: N=3 singlets all with X=1 have ∑X³ = 3 ≠ 0."""
        assert z4x_cubic_anomaly([1, 1, 1]) == 3

    def test_antisymmetric_cancels(self):
        """N=2 with charges (+1, -1) cancels."""
        assert z4x_cubic_anomaly([1, -1]) == 0

    def test_empty(self):
        assert z4x_cubic_anomaly([]) == 0

    def test_t11_compatibility_with_z16(self):
        """There exists a hidden sector that satisfies ℤ₁₆ (N=3) but fails ∑X³=0.

        Matches the Lean existential witness in z4x_singlet_constraint.
        """
        n_weyl = 3
        charges = [1, 1, 1]
        assert verify_anomaly_cancellation(n_weyl)  # ℤ₁₆ cancels
        assert z4x_cubic_anomaly(charges) != 0  # but U(1)_X³ does not


class TestMixedChargeChannel:
    """Lean anchor: HiddenSectorMixedCharge (Phase 5x Wave 2b Track X).

    Verifies the Wan-Wang ℤ₁₆ ⊕ ℤ₄ mixed-charge channel's two
    *decidable* conditions:

    - (b) ∑ Xᵢ³ ≡ 0 mod 4 (U(1)_X³ cubic)
    - (c) ∑ Xᵢ   ≡ 0 mod 4 (U(1)_X × gravity² linear)

    The third condition (ℤ₁₆ cancellation via the ℤ₁₆ ⊕ ℤ₄ mechanism)
    is the Lean tracked hypothesis ``H_MixedChannelZ16Cancels`` and is
    NOT exercised by these tests.
    """

    def test_c1_linear_sum(self):
        """C-1: 7 × (-2) + 6 = -8."""
        c1 = DM_CANDIDATE_MATRIX["C-1"]
        assert u1x_linear_sum(c1.x_charges) == -8

    def test_c1_cubic_sum(self):
        """C-1: 7 × (-8) + 216 = 160."""
        c1 = DM_CANDIDATE_MATRIX["C-1"]
        assert z4x_cubic_anomaly(list(c1.x_charges)) == 160

    def test_c1_joint_cancellation(self):
        """C-1 satisfies both U(1)_X conditions (160 and -8 both ≡ 0 mod 4)."""
        c1 = DM_CANDIDATE_MATRIX["C-1"]
        assert verify_joint_cancellation(c1.n_weyl, c1.x_charges)

    def test_non_singlet_candidates_have_u1x_verification(self):
        """Every non-singlet candidate with x_charges populated satisfies (b) ∧ (c).

        T-0 has empty x_charges (topological, no particle content) and is
        excluded; the topological channel is deferred (Track Y).
        """
        for tag, candidate in DM_CANDIDATE_MATRIX.items():
            if candidate.singlet_cancellation or not candidate.x_charges:
                continue
            assert verify_joint_cancellation(
                candidate.n_weyl, candidate.x_charges
            ), f"Mixed-charge candidate {tag} fails joint U(1)_X cancellation"

    def test_c1_not_in_singlet_channel(self):
        """X6 witness: C-1 fails the pure-singlet rule (N mod 16 = 3).

        Matches Lean ``mixed_channel_orthogonal_to_singlet``.
        """
        c1 = DM_CANDIDATE_MATRIX["C-1"]
        assert c1.n_weyl % 16 == 8
        assert c1.n_weyl % 16 != HIDDEN_SECTOR_REQUIRED_INDEX

    def test_c1_wan_wang_canonical_assignment(self):
        """Wan-Wang arXiv:2512.25038 Table IV: 7 q=-2 + 1 q=+6."""
        c1 = DM_CANDIDATE_MATRIX["C-1"]
        assert c1.x_charges == (-2, -2, -2, -2, -2, -2, -2, 6)
        assert sum(1 for q in c1.x_charges if q == -2) == 7
        assert sum(1 for q in c1.x_charges if q == 6) == 1

    def test_verify_joint_rejects_wrong_length(self):
        """Mismatched n_weyl and charge-list length raises ValueError."""
        with pytest.raises(ValueError):
            verify_joint_cancellation(3, [1, -1])

    def test_dmcandidate_rejects_inconsistent_charges(self):
        """Construction with mismatched x_charges length raises ValueError."""
        with pytest.raises(ValueError):
            DMCandidate(
                tag="TEST",
                n_weyl=4,
                dm_types=("test",),
                detection_notes="",
                singlet_cancellation=False,
                x_charges=(1, 2, 3),  # length 3, not 4
            )


class TestGenerationIndependenceFromZ16:
    """Lean anchor: T12 generation_independent_z16.

    The ℤ₃ generation constraint (3 ∣ N_f) and the ℤ₁₆ anomaly constraint
    (N_f · 15 ≡ 0 mod 16) are independent.
    """

    def test_nf3_satisfies_gen_fails_z16(self):
        """N_f = 3 satisfies 3 ∣ 3 but (3 * 15) mod 16 = 13 ≠ 0."""
        n_f = 3
        assert n_f % 3 == 0  # generation constraint holds
        assert (n_f * 15) % 16 != 0  # ℤ₁₆ fails

    def test_nf16_satisfies_z16_fails_gen(self):
        """N_f = 16 satisfies (16 * 15) mod 16 = 0 but 16 mod 3 = 1 ≠ 0."""
        n_f = 16
        assert (n_f * 15) % 16 == 0  # ℤ₁₆ holds
        assert n_f % 3 != 0  # generation fails
