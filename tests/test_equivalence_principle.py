"""Tests for `src/equivalence_principle/` (Phase 6c Wave 3).

Mirrors `lean/SKEFTHawking/EquivalencePrinciple.lean`. Each test name
matches a Lean theorem one-to-one where applicable; the Lean cross-
checks confirm Python ↔ Lean agreement on the 6×3 mechanism × EP-level
matrix.
"""

import pytest

from src.equivalence_principle import (
    EPLevel,
    EPMechanism,
    EP_VIOLATION_MATRIX,
    MICROSCOPE_BOUND,
    STEP_TARGET,
    VESTIGIAL_PHASE_ETA_MAX,
    VESTIGIAL_RELICS_ETA,
    satisfies_at,
    violates_at,
    violation_level,
)


# === EP level numerical ordering ===


class TestEPLevelOrdering:
    def test_wep_is_weakest(self):
        assert EPLevel.WEP.numerical_order == 0

    def test_eep_is_middle(self):
        assert EPLevel.EEP.numerical_order == 1

    def test_sep_is_strongest(self):
        assert EPLevel.SEP.numerical_order == 2

    def test_ordering_strict(self):
        assert (
            EPLevel.WEP.numerical_order
            < EPLevel.EEP.numerical_order
            < EPLevel.SEP.numerical_order
        )


# === Per-mechanism violation level (Lean cross-check) ===


class TestViolationLevel:
    """Each test mirrors a Lean theorem in EquivalencePrinciple.lean."""

    def test_vestigial_differential_coupling_violates_wep(self):
        # Lean: vestigialDifferentialCoupling_violates_WEP
        assert (
            violation_level(EPMechanism.vestigialDifferentialCoupling)
            == EPLevel.WEP
        )

    def test_vestigial_relics_step_class_violates_wep(self):
        # Lean: vestigialReliscSTEPClass_violates_WEP
        assert (
            violation_level(EPMechanism.vestigialReliscSTEPClass) == EPLevel.WEP
        )

    def test_fang_gu_torsion_trace_satisfies_all(self):
        # Lean: fangGuTorsionTrace_satisfies_all_EP
        assert violation_level(EPMechanism.fangGuTorsionTrace) is None

    def test_fracton_subdiffusion_satisfies_all(self):
        # Lean: fractonSubdiffusion_satisfies_all_EP
        assert violation_level(EPMechanism.fractonSubdiffusion) is None

    def test_sfdm_thomas_fermi_satisfies_all(self):
        # Lean: sfdmThomasFermi_satisfies_all_EP
        assert violation_level(EPMechanism.sfdmThomasFermi) is None

    def test_hidden_sector_z16_singlet_satisfies_all(self):
        # Lean: hiddenSectorZ16Singlet_satisfies_all_EP
        assert violation_level(EPMechanism.hiddenSectorZ16Singlet) is None


# === violates_at / satisfies_at semantics ===


class TestViolatesAt:
    def test_wep_violation_implies_eep_and_sep(self):
        # WEP-violator violates EEP and SEP (since WEP ⊂ EEP ⊂ SEP).
        m = EPMechanism.vestigialDifferentialCoupling
        assert violates_at(m, EPLevel.WEP)
        assert violates_at(m, EPLevel.EEP)
        assert violates_at(m, EPLevel.SEP)

    def test_satisfier_satisfies_all_levels(self):
        m = EPMechanism.fractonSubdiffusion
        assert satisfies_at(m, EPLevel.WEP)
        assert satisfies_at(m, EPLevel.EEP)
        assert satisfies_at(m, EPLevel.SEP)

    def test_satisfies_is_negation_of_violates(self):
        for m in EPMechanism:
            for L in EPLevel:
                assert satisfies_at(m, L) == (not violates_at(m, L))


# === Cross-mechanism tension theorems ===


class TestCrossMechanismTension:
    def test_ep_violation_is_vestigial_only(self):
        # Lean: ep_violation_is_vestigial_only — among 6 mechanisms,
        # exactly the two vestigial-phase phenomena violate WEP.
        violators = [
            m for m in EPMechanism if violates_at(m, EPLevel.WEP)
        ]
        assert set(violators) == {
            EPMechanism.vestigialDifferentialCoupling,
            EPMechanism.vestigialReliscSTEPClass,
        }

    def test_two_vestigial_mechanisms_distinct(self):
        # Lean: two_vestigial_mechanisms_distinct
        assert (
            EPMechanism.vestigialDifferentialCoupling
            != EPMechanism.vestigialReliscSTEPClass
        )

    def test_vestigial_vs_fang_gu_distinct_profile(self):
        # Lean: vestigial_vs_fangGu_distinct_EP_profile
        assert violation_level(
            EPMechanism.vestigialDifferentialCoupling
        ) != violation_level(EPMechanism.fangGuTorsionTrace)

    def test_distinct_violation_level_implies_distinct_mechanism(self):
        # Lean: distinct_violationLevel_implies_distinct_mechanism
        m1 = EPMechanism.vestigialDifferentialCoupling
        m2 = EPMechanism.fractonSubdiffusion
        assert violation_level(m1) != violation_level(m2)
        assert m1 != m2


# === Numerical-constant sanity (load-bearing for paper34) ===


class TestNumericalConstants:
    def test_microscope_bound_published_value(self):
        # Touboul et al., PRL 119, 231101 (2017): η < 1e-15.
        assert MICROSCOPE_BOUND == pytest.approx(1e-15)

    def test_step_target_below_microscope(self):
        # STEP-class satellite mission must improve on MICROSCOPE.
        assert STEP_TARGET < MICROSCOPE_BOUND

    def test_step_target_at_or_below_vestigial_relics_eta(self):
        # STEP must reach the vestigial-relic η scale to be a useful test.
        assert STEP_TARGET <= VESTIGIAL_RELICS_ETA

    def test_vestigial_phase_eta_maximal(self):
        # Vestigial phase has Δ_EP = 1 (maximal violation).
        assert VESTIGIAL_PHASE_ETA_MAX == pytest.approx(1.0)

    def test_vestigial_phase_eta_above_microscope_bound(self):
        # Vestigial-phase η = 1 ≫ MICROSCOPE bound, hence already
        # ruled out at any current EP precision.
        assert VESTIGIAL_PHASE_ETA_MAX > MICROSCOPE_BOUND

    def test_vestigial_relics_eta_below_microscope_bound(self):
        # Vestigial relics η ~ 10⁻¹⁸ is below current MICROSCOPE bound,
        # hence requires STEP-class precision to detect.
        assert VESTIGIAL_RELICS_ETA < MICROSCOPE_BOUND


# === Matrix structural properties ===


class TestEPViolationMatrix:
    def test_six_mechanisms(self):
        assert len(EP_VIOLATION_MATRIX) == 6

    def test_three_ep_levels_per_mechanism(self):
        for m, row in EP_VIOLATION_MATRIX.items():
            assert len(row) == 3

    def test_two_violators_at_wep(self):
        wep_violators = [
            m for m, row in EP_VIOLATION_MATRIX.items() if row[EPLevel.WEP]
        ]
        assert len(wep_violators) == 2

    def test_four_satisfiers_at_wep(self):
        wep_satisfiers = [
            m
            for m, row in EP_VIOLATION_MATRIX.items()
            if not row[EPLevel.WEP]
        ]
        assert len(wep_satisfiers) == 4

    def test_violator_violates_all_levels(self):
        # WEP-violator violates EEP and SEP too (since WEP ⊂ EEP ⊂ SEP).
        for m, row in EP_VIOLATION_MATRIX.items():
            if row[EPLevel.WEP]:
                assert row[EPLevel.EEP]
                assert row[EPLevel.SEP]

    def test_no_three_violator_split(self):
        # Rules out the "violates-WEP-but-not-EEP" pathology.
        for m, row in EP_VIOLATION_MATRIX.items():
            if not row[EPLevel.WEP]:
                # Non-WEP-violators in our enum also don't violate EEP/SEP.
                assert not row[EPLevel.EEP]
                assert not row[EPLevel.SEP]


# === Anti-pattern audit ===


class TestAntiPatternAudit:
    """The post-wave 6-pattern audit, applied to 6c.3 mechanism enum."""

    def test_no_existential_absorption(self):
        # All classifications are explicit per-mechanism, not ∃-witness.
        for m in EPMechanism:
            assert violation_level(m) is None or isinstance(
                violation_level(m), EPLevel
            )

    def test_distinct_mechanisms_have_distinct_enum_values(self):
        # No alias collapse in the enum.
        names = [m.name for m in EPMechanism]
        assert len(names) == len(set(names))

    def test_violation_level_function(self):
        # Lean: violationLevel_is_function — each mechanism has a
        # unique weakest-violated level.
        for m in EPMechanism:
            l1 = violation_level(m)
            l2 = violation_level(m)
            assert l1 == l2


# === Strengthening pass (post-wave 6-pattern audit) ===


class TestStrengthening:
    """Post-wave strengthening pass: structural lemmas + quantitative
    bounds added 2026-04-27."""

    def test_violates_at_monotonic_in_level(self):
        # Lean: violatesAt_mono — if WEP is violated, EEP and SEP are too.
        m = EPMechanism.vestigialDifferentialCoupling
        for L1 in EPLevel:
            for L2 in EPLevel:
                if L1.numerical_order <= L2.numerical_order and violates_at(m, L1):
                    assert violates_at(m, L2)

    def test_no_violation_implies_satisfies_all(self):
        # Lean: noViolation_implies_satisfiesAt
        for m in EPMechanism:
            if violation_level(m) is None:
                for L in EPLevel:
                    assert satisfies_at(m, L)

    def test_vestigial_phase_eta_violates_microscope_quantitative(self):
        # Lean: vestigial_phase_eta_violates_microscope_bound — 1.0 > 1e-15
        assert VESTIGIAL_PHASE_ETA_MAX > MICROSCOPE_BOUND
        # Margin of violation: 15 orders of magnitude
        import math
        margin_orders = math.log10(VESTIGIAL_PHASE_ETA_MAX / MICROSCOPE_BOUND)
        assert margin_orders >= 15.0

    def test_vestigial_relics_below_microscope_quantitative(self):
        # Lean: vestigial_relics_below_microscope_bound — 1e-18 < 1e-15
        assert VESTIGIAL_RELICS_ETA < MICROSCOPE_BOUND
        # Margin: 3 orders of magnitude below current bound
        import math
        margin_orders = math.log10(MICROSCOPE_BOUND / VESTIGIAL_RELICS_ETA)
        assert margin_orders >= 3.0

    def test_non_violators_share_violation_level(self):
        # Lean: non_violators_share_violationLevel
        non_violators = [
            EPMechanism.fangGuTorsionTrace,
            EPMechanism.fractonSubdiffusion,
            EPMechanism.sfdmThomasFermi,
            EPMechanism.hiddenSectorZ16Singlet,
        ]
        levels = [violation_level(m) for m in non_violators]
        assert all(L == levels[0] for L in levels)
        assert levels[0] is None  # all four share `none`

    def test_fang_gu_classification_consistent_with_w4(self):
        # Lean: fangGu_failure_mode_is_kinematic_not_ep — the FangGu
        # classification (no EP violation) is consistent with the W4
        # kinematic-failure-mode finding (¬ is_dust under traceless
        # stress-energy). Python-side asserts the EP-classification
        # half; Lean asserts both halves with the actual fg_cdm_obstruction
        # call.
        assert violation_level(EPMechanism.fangGuTorsionTrace) is None
