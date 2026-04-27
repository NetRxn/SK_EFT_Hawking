"""Tests for `src/bbn/` (Phase 6b Wave 1).

Mirrors `lean/SKEFTHawking/BBN.lean`. Each test name maps to a Lean
theorem one-to-one where applicable; cross-checks confirm Python ↔
Lean numerical agreement on the BBN-conformance matrix.
"""

import pytest

from src.bbn import (
    DMCandidate,
    BBNConformance,
    OMEGA_B_H2_CENTRAL,
    OMEGA_B_H2_SIGMA,
    Y_P_CENTRAL,
    Y_P_SIGMA,
    D_OVER_H_CENTRAL,
    D_OVER_H_SIGMA,
    LI7_OVER_H_CENTRAL,
    LI7_OVER_H_SIGMA,
    N_EFF_CENTRAL,
    N_EFF_SIGMA,
    N_EFF_2SIGMA_SLACK,
    bbn_conformance,
    evaluate_all_candidates,
)


# === Numerical bounds (Lean §1 cross-checks) ===


class TestObservationalBounds:
    """Cross-checks for the published bounds tied to Lean §1 theorems."""

    def test_omega_baryon_h2_positive(self):
        # Lean: omega_baryon_h2_positive
        assert OMEGA_B_H2_CENTRAL > 0.0

    def test_n_eff_slack_below_radiation_thermalization(self):
        # Lean: n_eff_slack_below_radiation_thermalization
        # The slack 0.34 separates conformant from FG-radiation-thermalized
        # (ΔN_eff ≥ 1.0). Replaces the original `0.34 = 2 × 0.17`
        # definitional unfolding (P3 trivial-multiplication-as-physics).
        assert N_EFF_2SIGMA_SLACK < 1.0

    def test_y_p_central_in_physical_range(self):
        # Lean: y_p_central_in_physical_range
        # Y_p is a mass fraction so must be in (0, 1). Replaces the
        # original `y_p_within_pdg_2sigma` which was P5 structural-
        # tautology (within own ±2σ band, vacuously true).
        assert 0 < Y_P_CENTRAL < 1

    def test_d_over_h_central_positive_and_dilute(self):
        # Lean: d_over_h_central_positive_and_dilute
        # D/H is positive (both species exist) and dilute (D much
        # rarer than H). Replaces P5 structural-tautology.
        assert 0 < D_OVER_H_CENTRAL < 1.0e-3

    def test_li7_data_consistent(self):
        # Lean: li7_over_h_data_consistent
        assert LI7_OVER_H_CENTRAL > 0.0
        assert LI7_OVER_H_CENTRAL <= 1.0e-9


# === Per-candidate conformance ===


class TestCandidateConformance:
    """Tests for the 5 Phase 5x candidates' BBN-conformance verdicts."""

    def test_z16_topological_t0_conformant(self):
        # Lean: z16_topological_t0_decouples_at_bbn (qualitative side)
        verdicts = evaluate_all_candidates()
        assert verdicts[DMCandidate.Z16Topological_T0].is_conformant

    def test_z16_mixed_c1_conformant(self):
        # Lean: z16_mixed_c1_decouples_at_bbn
        verdicts = evaluate_all_candidates()
        assert verdicts[DMCandidate.Z16Mixed_C1].is_conformant

    def test_fracton_p_wave_conformant(self):
        # Lean: fracton_p_wave_decouples_at_bbn
        verdicts = evaluate_all_candidates()
        assert verdicts[DMCandidate.FractonPWave].is_conformant

    def test_z16_singlet_s0_violates_under_thermalization(self):
        # Lean: z16_singlet_s0_violates_bbn_under_thermalization
        verdicts = evaluate_all_candidates()
        v = verdicts[DMCandidate.Z16Singlet_S0]
        # Under default (3 sterile Weyl thermalize): δN_eff = 3.0 > 0.34
        assert not v.delta_n_eff_within_bound
        assert not v.is_conformant

    def test_z16_singlet_s0_conformant_if_no_thermalization(self):
        # Override: no thermalization → satisfies BBN
        verdicts = evaluate_all_candidates(
            n_eff_overrides={DMCandidate.Z16Singlet_S0: 0.0}
        )
        assert verdicts[DMCandidate.Z16Singlet_S0].is_conformant

    def test_fg_torsion_violates_under_radiation_thermalization(self):
        # Lean: fg_torsion_violates_bbn_under_radiation_thermalization
        verdicts = evaluate_all_candidates()
        v = verdicts[DMCandidate.FGTorsion]
        # Under default (FG thermalizes as radiation): δN_eff = 1.0 > 0.34
        assert not v.delta_n_eff_within_bound
        assert not v.is_conformant

    def test_fg_torsion_conformant_if_no_thermalization(self):
        verdicts = evaluate_all_candidates(
            n_eff_overrides={DMCandidate.FGTorsion: 0.0}
        )
        assert verdicts[DMCandidate.FGTorsion].is_conformant


# === Cardinality / cross-tension ===


class TestCardinalityAndCrossTension:
    """Cross-tension between candidates."""

    def test_at_least_three_candidates_conformant(self):
        # Lean: at_least_three_phase5x_candidates_bbn_conformant
        verdicts = evaluate_all_candidates()
        conformant = [v for v in verdicts.values() if v.is_conformant]
        assert len(conformant) >= 3

    def test_two_violators_share_n_eff_failure_mode(self):
        # Lean: bbn_violators_share_n_eff_failure_mode
        verdicts = evaluate_all_candidates()
        violators = [
            (k, v) for k, v in verdicts.items()
            if not v.is_conformant
        ]
        # All non-conformant candidates fail via δN_eff bound
        for _, v in violators:
            assert not v.delta_n_eff_within_bound, (
                "Violator failure mode should be δN_eff (not Ω_B or "
                "injection)"
            )

    def test_exactly_two_default_violators(self):
        # Default tracked-hypothesis: S-0 thermalizes + FG thermalizes
        # ⟹ exactly 2 violators
        verdicts = evaluate_all_candidates()
        violators = {
            k for k, v in verdicts.items() if not v.is_conformant
        }
        assert violators == {
            DMCandidate.Z16Singlet_S0,
            DMCandidate.FGTorsion,
        }


# === Anti-pattern audit (preemptive strengthening) ===


class TestAntiPatternAudit:
    """6-pattern audit checks confirming first-pass discipline applied."""

    def test_h_bbn_conformance_three_field_drop_conjunct(self):
        # P2 drop-conjunct: each field independently breakable.
        # Construct conformances that fail on ONE field only:
        only_omega_fails = BBNConformance(
            omega_b_consistent=False,
            delta_n_eff_within_bound=True,
            injection_below_threshold=True,
        )
        only_n_eff_fails = BBNConformance(
            omega_b_consistent=True,
            delta_n_eff_within_bound=False,
            injection_below_threshold=True,
        )
        only_injection_fails = BBNConformance(
            omega_b_consistent=True,
            delta_n_eff_within_bound=True,
            injection_below_threshold=False,
        )
        # All three independent failure modes produce non-conformance:
        assert not only_omega_fails.is_conformant
        assert not only_n_eff_fails.is_conformant
        assert not only_injection_fails.is_conformant
        # And the 3-conjunct is genuinely 3-conjunct (no field implies another):
        assert only_omega_fails.delta_n_eff_within_bound
        assert only_n_eff_fails.omega_b_consistent
        assert only_injection_fails.omega_b_consistent
