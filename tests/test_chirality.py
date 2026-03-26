"""Tests for the chirality wall synthesis (Phase 4, Item 1B).

Validates:
1. GS no-go condition extraction (four conditions, correct names/types)
2. TPF construction extraction (four ingredients, correct structure)
3. Per-condition compatibility check (evasion verdicts)
4. Numerical evidence compilation
5. Overall compatibility result and wall status
6. Convenience functions (summary, counts)
7. Dataclass structure and field completeness
"""

import pytest
from src.chirality.tpf_gs_analysis import (
    EvasionVerdict,
    NoGoCondition,
    TPFIngredient,
    TPFConstruction,
    NumericalEvidence,
    WallStatus,
    CompatibilityResult,
    gs_conditions,
    tpf_construction,
    numerical_evidence,
    check_compatibility,
    chirality_wall_status,
    conditions_summary,
    evasion_count,
)


# ═══════════════════════════════════════════════════════════════════
# GS no-go conditions
# ═══════════════════════════════════════════════════════════════════

class TestGSConditions:
    """Test extraction of Golterman-Shamir no-go conditions."""

    def test_four_conditions(self):
        """GS theorem has exactly four conditions."""
        conditions = gs_conditions()
        assert len(conditions) == 4

    def test_condition_names(self):
        """All four conditions have the expected names."""
        conditions = gs_conditions()
        names = {c.name for c in conditions}
        expected = {
            "lattice_translation_invariance",
            "finite_range_hamiltonian",
            "relativistic_continuum_limit",
            "complete_interpolating_fields",
        }
        assert names == expected

    def test_conditions_are_dataclasses(self):
        """Each condition is a NoGoCondition dataclass."""
        for c in gs_conditions():
            assert isinstance(c, NoGoCondition)

    def test_all_conditions_have_descriptions(self):
        """Every condition has a nonempty description."""
        for c in gs_conditions():
            assert len(c.description) > 0
            assert len(c.mathematical_statement) > 0

    def test_all_conditions_have_verdicts(self):
        """Every condition has a valid EvasionVerdict."""
        for c in gs_conditions():
            assert isinstance(c.applies_to_tpf, EvasionVerdict)

    def test_evaded_conditions_have_mechanisms(self):
        """Conditions marked EVADED must have an evasion mechanism."""
        for c in gs_conditions():
            if c.applies_to_tpf == EvasionVerdict.EVADED:
                assert c.evasion_mechanism is not None
                assert len(c.evasion_mechanism) > 0

    def test_applying_conditions_have_no_mechanism(self):
        """Conditions marked APPLIES should have no evasion mechanism."""
        for c in gs_conditions():
            if c.applies_to_tpf == EvasionVerdict.APPLIES:
                assert c.evasion_mechanism is None

    def test_translation_invariance_evaded(self):
        """Lattice translation invariance is evaded by the slab geometry."""
        conditions = {c.name: c for c in gs_conditions()}
        c = conditions["lattice_translation_invariance"]
        assert c.applies_to_tpf == EvasionVerdict.EVADED
        assert "slab" in c.evasion_mechanism.lower() or "extra" in c.evasion_mechanism.lower()

    def test_finite_range_applies(self):
        """Finite-range Hamiltonian applies — TPF is local."""
        conditions = {c.name: c for c in gs_conditions()}
        c = conditions["finite_range_hamiltonian"]
        assert c.applies_to_tpf == EvasionVerdict.APPLIES

    def test_relativistic_limit_unclear(self):
        """Relativistic continuum limit is unclear — depends on conjecture."""
        conditions = {c.name: c for c in gs_conditions()}
        c = conditions["relativistic_continuum_limit"]
        assert c.applies_to_tpf == EvasionVerdict.UNCLEAR

    def test_interpolating_fields_evaded(self):
        """Complete interpolating fields is evaded by ancilla + rotors."""
        conditions = {c.name: c for c in gs_conditions()}
        c = conditions["complete_interpolating_fields"]
        assert c.applies_to_tpf == EvasionVerdict.EVADED
        assert "ancilla" in c.evasion_mechanism.lower()


# ═══════════════════════════════════════════════════════════════════
# TPF construction
# ═══════════════════════════════════════════════════════════════════

class TestTPFConstruction:
    """Test extraction of the TPF disentangler construction."""

    def test_construction_is_dataclass(self):
        """TPF construction is a TPFConstruction dataclass."""
        c = tpf_construction()
        assert isinstance(c, TPFConstruction)

    def test_four_ingredients(self):
        """TPF construction has exactly four key ingredients."""
        c = tpf_construction()
        assert len(c.ingredients) == 4

    def test_ingredient_names(self):
        """All four ingredients have the expected names."""
        c = tpf_construction()
        names = {i.name for i in c.ingredients}
        expected = {
            "infinite_dimensional_rotors",
            "not_on_site_symmetry",
            "ancilla_degrees_of_freedom",
            "extra_dimensional_spt_slab",
        }
        assert names == expected

    def test_ingredients_are_dataclasses(self):
        """Each ingredient is a TPFIngredient dataclass."""
        for i in tpf_construction().ingredients:
            assert isinstance(i, TPFIngredient)

    def test_all_ingredients_have_descriptions(self):
        """Every ingredient has nonempty description and mathematical setting."""
        for i in tpf_construction().ingredients:
            assert len(i.description) > 0
            assert len(i.mathematical_setting) > 0

    def test_bulk_dimension(self):
        """Bulk is 4+1D = 5 dimensions."""
        c = tpf_construction()
        assert c.spacetime_dim_bulk == 5

    def test_boundary_dimension(self):
        """Boundary is 3+1D = 4 dimensions."""
        c = tpf_construction()
        assert c.spacetime_dim_boundary == 4

    def test_hilbert_space_type(self):
        """Hilbert space is infinite-dimensional rotors."""
        c = tpf_construction()
        assert "rotor" in c.hilbert_space_type.lower()
        assert "infinite" in c.hilbert_space_type.lower()

    def test_symmetry_not_on_site(self):
        """Symmetry implementation is not-on-site."""
        c = tpf_construction()
        assert "not-on-site" in c.symmetry_implementation.lower()

    def test_critical_conjecture_stated(self):
        """The critical conjecture is explicitly stated."""
        c = tpf_construction()
        assert len(c.critical_conjecture) > 0
        assert "gap" in c.critical_conjecture.lower()

    def test_ingredients_reference_gs_conditions(self):
        """Each ingredient references which GS conditions it affects."""
        gs_names = {c.name for c in gs_conditions()}
        for i in tpf_construction().ingredients:
            for affected in i.gs_conditions_affected:
                assert affected in gs_names, (
                    f"Ingredient {i.name} references unknown GS condition: {affected}"
                )

    def test_at_least_one_condition_affected_per_ingredient(self):
        """Every ingredient should affect at least one GS condition."""
        for i in tpf_construction().ingredients:
            assert len(i.gs_conditions_affected) >= 1, (
                f"Ingredient {i.name} does not affect any GS condition"
            )


# ═══════════════════════════════════════════════════════════════════
# Numerical evidence
# ═══════════════════════════════════════════════════════════════════

class TestNumericalEvidence:
    """Test compilation of numerical lattice evidence."""

    def test_evidence_count(self):
        """At least four pieces of numerical evidence."""
        evidence = numerical_evidence()
        assert len(evidence) >= 4

    def test_evidence_are_dataclasses(self):
        """Each piece of evidence is a NumericalEvidence dataclass."""
        for e in numerical_evidence():
            assert isinstance(e, NumericalEvidence)

    def test_butt_catterall_hasenfratz(self):
        """Butt-Catterall-Hasenfratz PRL 2025 is included."""
        evidence = {e.group: e for e in numerical_evidence()}
        assert "Butt-Catterall-Hasenfratz" in evidence
        e = evidence["Butt-Catterall-Hasenfratz"]
        assert e.year == 2025
        assert "SMG" in e.finding or "symmetric mass generation" in e.finding.lower()

    def test_hasenfratz_witzel(self):
        """Hasenfratz-Witzel Nov 2025 is included."""
        evidence = {e.group: e for e in numerical_evidence()}
        assert "Hasenfratz-Witzel" in evidence
        e = evidence["Hasenfratz-Witzel"]
        assert e.year == 2025
        assert "16" in e.finding

    def test_gioia_thorngren(self):
        """Gioia-Thorngren Mar 2025 is included."""
        evidence = {e.group: e for e in numerical_evidence()}
        assert "Gioia-Thorngren" in evidence

    def test_seifnashri(self):
        """Seifnashri Jan 2026 is included."""
        evidence = {e.group: e for e in numerical_evidence()}
        assert "Seifnashri" in evidence
        assert evidence["Seifnashri"].year == 2026

    def test_all_evidence_has_relevance(self):
        """Every piece of evidence explains its relevance."""
        for e in numerical_evidence():
            assert len(e.relevance) > 0


# ═══════════════════════════════════════════════════════════════════
# Compatibility check
# ═══════════════════════════════════════════════════════════════════

class TestCompatibilityCheck:
    """Test the formal compatibility check between GS and TPF."""

    def test_result_is_dataclass(self):
        """Compatibility result is a CompatibilityResult dataclass."""
        result = check_compatibility()
        assert isinstance(result, CompatibilityResult)

    def test_conditions_in_result(self):
        """Result contains all four GS conditions."""
        result = check_compatibility()
        assert len(result.conditions) == 4

    def test_construction_in_result(self):
        """Result contains the TPF construction."""
        result = check_compatibility()
        assert isinstance(result.construction, TPFConstruction)

    def test_evasion_counts(self):
        """Evasion counts are consistent: 2 evaded, 1 applying, 1 unclear."""
        result = check_compatibility()
        assert result.conditions_evaded == 2
        assert result.conditions_applying == 1
        assert result.conditions_unclear == 1

    def test_counts_sum_to_four(self):
        """Evasion counts sum to the total number of conditions."""
        result = check_compatibility()
        total = (
            result.conditions_evaded
            + result.conditions_applying
            + result.conditions_unclear
        )
        assert total == len(result.conditions)

    def test_wall_status_conditional_breach(self):
        """Wall status is CONDITIONAL_BREACH."""
        result = check_compatibility()
        assert result.wall_status == WallStatus.CONDITIONAL_BREACH

    def test_critical_conjecture_unproven(self):
        """Critical conjecture is marked as unproven."""
        result = check_compatibility()
        assert "UNPROVEN" in result.critical_conjecture_status.upper()

    def test_assessment_nonempty(self):
        """Assessment text is substantial."""
        result = check_compatibility()
        assert len(result.assessment) > 100

    def test_assessment_mentions_key_elements(self):
        """Assessment mentions the key analytical elements."""
        result = check_compatibility()
        text = result.assessment.lower()
        assert "conditional" in text
        assert "conjecture" in text
        assert "evade" in text or "evaded" in text

    def test_numerical_evidence_included(self):
        """Numerical evidence is included in the result."""
        result = check_compatibility()
        assert len(result.numerical_evidence) >= 4


# ═══════════════════════════════════════════════════════════════════
# Top-level status functions
# ═══════════════════════════════════════════════════════════════════

class TestChiralityWallStatus:
    """Test the top-level wall status function."""

    def test_returns_wall_status(self):
        """chirality_wall_status returns a WallStatus enum."""
        status = chirality_wall_status()
        assert isinstance(status, WallStatus)

    def test_conditional_breach(self):
        """Current status is CONDITIONAL_BREACH."""
        assert chirality_wall_status() == WallStatus.CONDITIONAL_BREACH


class TestConditionsSummary:
    """Test the conditions_summary convenience function."""

    def test_returns_dict(self):
        """conditions_summary returns a dict."""
        summary = conditions_summary()
        assert isinstance(summary, dict)

    def test_four_entries(self):
        """Summary has four entries (one per GS condition)."""
        summary = conditions_summary()
        assert len(summary) == 4

    def test_expected_keys(self):
        """Summary has the expected condition names as keys."""
        summary = conditions_summary()
        expected_keys = {
            "lattice_translation_invariance",
            "finite_range_hamiltonian",
            "relativistic_continuum_limit",
            "complete_interpolating_fields",
        }
        assert set(summary.keys()) == expected_keys

    def test_expected_values(self):
        """Summary values match the expected verdicts."""
        summary = conditions_summary()
        assert summary["lattice_translation_invariance"] == "EVADED"
        assert summary["finite_range_hamiltonian"] == "APPLIES"
        assert summary["relativistic_continuum_limit"] == "UNCLEAR"
        assert summary["complete_interpolating_fields"] == "EVADED"


class TestEvasionCount:
    """Test the evasion_count convenience function."""

    def test_returns_tuple(self):
        """evasion_count returns a 3-tuple."""
        result = evasion_count()
        assert isinstance(result, tuple)
        assert len(result) == 3

    def test_counts(self):
        """Counts are (2, 1, 1): 2 evaded, 1 applying, 1 unclear."""
        evaded, applying, unclear = evasion_count()
        assert evaded == 2
        assert applying == 1
        assert unclear == 1

    def test_counts_sum_to_four(self):
        """Counts sum to the total number of GS conditions."""
        evaded, applying, unclear = evasion_count()
        assert evaded + applying + unclear == 4


# ═══════════════════════════════════════════════════════════════════
# Enum values
# ═══════════════════════════════════════════════════════════════════

class TestEnums:
    """Test enum definitions and values."""

    def test_evasion_verdict_values(self):
        """EvasionVerdict has the expected three values."""
        assert EvasionVerdict.APPLIES.value == "applies"
        assert EvasionVerdict.EVADED.value == "evaded"
        assert EvasionVerdict.UNCLEAR.value == "unclear"

    def test_wall_status_values(self):
        """WallStatus has the expected four values."""
        assert WallStatus.STANDING.value == "standing"
        assert WallStatus.BREACHED.value == "breached"
        assert WallStatus.CONDITIONAL_BREACH.value == "conditional_breach"
        assert WallStatus.UNDER_SIEGE.value == "under_siege"


# ═══════════════════════════════════════════════════════════════════
# Cross-references and consistency
# ═══════════════════════════════════════════════════════════════════

class TestCrossConsistency:
    """Test cross-references between GS conditions and TPF ingredients."""

    def test_every_evaded_condition_has_tpf_ingredient(self):
        """Every evaded GS condition is referenced by at least one TPF ingredient."""
        evaded_names = {
            c.name for c in gs_conditions()
            if c.applies_to_tpf == EvasionVerdict.EVADED
        }
        construction = tpf_construction()
        affected_by_ingredients = set()
        for ingredient in construction.ingredients:
            affected_by_ingredients.update(ingredient.gs_conditions_affected)

        for name in evaded_names:
            assert name in affected_by_ingredients, (
                f"Evaded condition '{name}' is not referenced by any TPF ingredient"
            )

    def test_gs_conditions_stable(self):
        """GS conditions return the same result on repeated calls."""
        c1 = gs_conditions()
        c2 = gs_conditions()
        assert len(c1) == len(c2)
        for a, b in zip(c1, c2):
            assert a.name == b.name
            assert a.applies_to_tpf == b.applies_to_tpf

    def test_compatibility_result_stable(self):
        """check_compatibility returns consistent results on repeated calls."""
        r1 = check_compatibility()
        r2 = check_compatibility()
        assert r1.conditions_evaded == r2.conditions_evaded
        assert r1.wall_status == r2.wall_status

    def test_module_import_from_init(self):
        """All public API symbols are importable from src.chirality."""
        from src.chirality import (
            EvasionVerdict,
            NoGoCondition,
            TPFIngredient,
            TPFConstruction,
            NumericalEvidence,
            WallStatus,
            CompatibilityResult,
            gs_conditions,
            tpf_construction,
            numerical_evidence,
            check_compatibility,
            chirality_wall_status,
            conditions_summary,
            evasion_count,
        )
        # Verify they are the same objects (not re-implementations)
        from src.chirality.tpf_gs_analysis import (
            gs_conditions as gs_conditions_direct,
        )
        assert gs_conditions is gs_conditions_direct
