"""
Tests for SM anomaly computation in ℤ₁₆.

Validates:
  - ℤ₄ charge computation X = 5(B-L) - 4Y
  - All SM fermion charges are odd
  - Anomaly index: 16 (with ν_R), 15 (without)
  - Three-generation anomaly: -3 mod 16
  - Hidden sector theorem
  - Generation constraint: N_f ≡ 0 mod 3
  - Physical bounds on all quantities

References:
  García-Etxebarria & Montero, JHEP 08, 003 (2019) [arXiv:1808.00009]
  Wang, PRD 110, 125028 (2024) [arXiv:2312.14928]
"""

import pytest

from src.core.constants import SM_FERMION_DATA, SM_Z4_CHARGE_FORMULA, SM_ANOMALY
from src.core.formulas import (
    sm_z4_charge,
    sm_anomaly_index,
    sm_three_gen_anomaly,
    sm_generation_constraint,
)
from src.core.sm_anomaly import (
    compute_fermion_anomaly_data,
    compute_full_anomaly_report,
    anomaly_cancellation_check,
    FermionAnomalyData,
    SMAnomalyReport,
)


# ════════════════════════════════════════════════════════════════════
# ℤ₄ Charge Tests
# ════════════════════════════════════════════════════════════════════

class TestZ4Charge:
    """Test the ℤ₄ charge formula X = 5(B-L) - 4Y."""

    def test_Q_L_charge(self):
        """Quark doublet: X = 5(1/3) - 4(1/6) = 5/3 - 2/3 = 1."""
        assert sm_z4_charge(1/3, 1/6) == 1

    def test_u_R_bar_charge(self):
        """Up antiquark: X = 5(-1/3) - 4(-2/3) = -5/3 + 8/3 = 1."""
        assert sm_z4_charge(-1/3, -2/3) == 1

    def test_d_R_bar_charge(self):
        """Down antiquark: X = 5(-1/3) - 4(1/3) = -5/3 - 4/3 = -3 ≡ 1 mod 4."""
        assert sm_z4_charge(-1/3, 1/3) == 1  # -3 mod 4 = 1

    def test_L_charge(self):
        """Lepton doublet: X = 5(-1) - 4(-1/2) = -5 + 2 = -3 ≡ 1 mod 4."""
        assert sm_z4_charge(-1, -1/2) == 1  # -3 mod 4 = 1

    def test_e_R_bar_charge(self):
        """Positron: X = 5(1) - 4(1) = 1."""
        assert sm_z4_charge(1, 1) == 1

    def test_nu_R_bar_charge(self):
        """Right-handed neutrino: X = 5(1) - 4(0) = 5 ≡ 1 mod 4."""
        assert sm_z4_charge(1, 0) == 1  # 5 mod 4 = 1

    def test_all_charges_odd(self):
        """All SM fermion ℤ₄ charges must be odd (key property for anomaly)."""
        for name, f in SM_FERMION_DATA.items():
            X = sm_z4_charge(f['B_minus_L'], f['Y'])
            assert X % 2 == 1, f"{name} has even ℤ₄ charge {X}"

    def test_all_charges_are_one_mod4(self):
        """All SM fermion ℤ₄ charges are ≡ 1 mod 4."""
        for name, f in SM_FERMION_DATA.items():
            X = sm_z4_charge(f['B_minus_L'], f['Y'])
            assert X == 1, f"{name} has ℤ₄ charge {X}, expected 1"

    def test_z4_formula_coefficients(self):
        """Verify the formula coefficients match constants."""
        assert SM_Z4_CHARGE_FORMULA['B_minus_L_coeff'] == 5
        assert SM_Z4_CHARGE_FORMULA['Y_coeff'] == -4


# ════════════════════════════════════════════════════════════════════
# Component Counting Tests
# ════════════════════════════════════════════════════════════════════

class TestComponentCounting:
    """Test SM fermion component counts."""

    def test_Q_L_components(self):
        assert SM_FERMION_DATA['Q_L']['components'] == 6  # 3 color × 2 weak

    def test_u_R_bar_components(self):
        assert SM_FERMION_DATA['u_R_bar']['components'] == 3

    def test_d_R_bar_components(self):
        assert SM_FERMION_DATA['d_R_bar']['components'] == 3

    def test_L_components(self):
        assert SM_FERMION_DATA['L']['components'] == 2

    def test_e_R_bar_components(self):
        assert SM_FERMION_DATA['e_R_bar']['components'] == 1

    def test_nu_R_bar_components(self):
        assert SM_FERMION_DATA['nu_R_bar']['components'] == 1

    def test_total_with_nu_R(self):
        total = sum(f['components'] for f in SM_FERMION_DATA.values())
        assert total == 16

    def test_total_without_nu_R(self):
        total = sum(f['components'] for name, f in SM_FERMION_DATA.items()
                     if name != 'nu_R_bar')
        assert total == 15

    def test_six_fermion_types(self):
        assert len(SM_FERMION_DATA) == 6


# ════════════════════════════════════════════════════════════════════
# Anomaly Index Tests
# ════════════════════════════════════════════════════════════════════

class TestAnomalyIndex:
    """Test anomaly computation in ℤ₁₆."""

    def test_anomaly_with_nu_R(self):
        """With ν_R: 16 ≡ 0 mod 16 (anomaly-free)."""
        result = sm_anomaly_index(SM_FERMION_DATA, include_nu_R=True)
        assert result['total_components'] == 16
        assert result['anomaly_mod16'] == 0
        assert result['anomaly_free'] is True

    def test_anomaly_without_nu_R(self):
        """Without ν_R: 15 ≡ 15 mod 16 (anomalous)."""
        result = sm_anomaly_index(SM_FERMION_DATA, include_nu_R=False)
        assert result['total_components'] == 15
        assert result['anomaly_mod16'] == 15  # 15 ≡ -1 mod 16
        assert result['anomaly_free'] is False

    def test_anomaly_constants_match(self):
        """Verify constants match computation."""
        assert SM_ANOMALY['COMPONENTS_WITH_NU_R'] == 16
        assert SM_ANOMALY['COMPONENTS_WITHOUT_NU_R'] == 15
        assert SM_ANOMALY['ANOMALY_WITH_NU_R'] == 0
        assert SM_ANOMALY['ANOMALY_WITHOUT_NU_R'] == -1

    def test_breakdown_has_all_fermions(self):
        result = sm_anomaly_index(SM_FERMION_DATA, include_nu_R=True)
        assert len(result['breakdown']) == 6

    def test_breakdown_without_nu_R_excludes_nu(self):
        result = sm_anomaly_index(SM_FERMION_DATA, include_nu_R=False)
        assert 'nu_R_bar' not in result['breakdown']
        assert len(result['breakdown']) == 5


# ════════════════════════════════════════════════════════════════════
# Three-Generation Tests
# ════════════════════════════════════════════════════════════════════

class TestThreeGeneration:
    """Test multi-generation anomaly."""

    def test_three_gen_without_nu_R(self):
        """3 × 15 = 45 ≡ 13 mod 16 (anomalous, forces hidden sectors)."""
        result = sm_three_gen_anomaly(15, n_gen=3)
        assert result['total_anomaly'] == 45
        assert result['anomaly_mod16'] == 13  # 45 mod 16 = 13 = -3 mod 16
        assert result['anomaly_free'] is False
        assert result['requires_hidden_sector'] is True

    def test_three_gen_with_nu_R(self):
        """3 × 16 = 48 ≡ 0 mod 16 (anomaly-free)."""
        result = sm_three_gen_anomaly(16, n_gen=3)
        assert result['total_anomaly'] == 48
        assert result['anomaly_mod16'] == 0
        assert result['anomaly_free'] is True

    def test_one_gen_without_nu_R(self):
        result = sm_three_gen_anomaly(15, n_gen=1)
        assert result['anomaly_mod16'] == 15

    def test_sixteen_gen_without_nu_R(self):
        """16 generations without ν_R: 16 × 15 = 240 ≡ 0 mod 16."""
        result = sm_three_gen_anomaly(15, n_gen=16)
        assert result['anomaly_mod16'] == 0
        assert result['anomaly_free'] is True

    def test_constants_match(self):
        assert SM_ANOMALY['N_GENERATIONS'] == 3
        assert SM_ANOMALY['THREE_GEN_ANOMALY'] == -3


# ════════════════════════════════════════════════════════════════════
# Generation Constraint Tests
# ════════════════════════════════════════════════════════════════════

class TestGenerationConstraint:
    """Test N_f ≡ 0 mod 3 constraint."""

    def test_n_f_3_satisfies(self):
        result = sm_generation_constraint(3)
        assert result['satisfies_generation_constraint'] is True
        assert result['satisfies_modular_invariance'] is True
        assert result['c_minus'] == 24
        assert result['is_minimal_nontrivial'] is True

    def test_n_f_1_fails(self):
        result = sm_generation_constraint(1)
        assert result['satisfies_generation_constraint'] is False
        assert result['c_minus'] == 8
        assert result['c_minus_mod24'] == 8

    def test_n_f_2_fails(self):
        result = sm_generation_constraint(2)
        assert result['satisfies_generation_constraint'] is False

    def test_n_f_6_satisfies(self):
        result = sm_generation_constraint(6)
        assert result['satisfies_generation_constraint'] is True
        assert result['c_minus'] == 48

    def test_n_f_0_satisfies(self):
        result = sm_generation_constraint(0)
        assert result['satisfies_generation_constraint'] is True
        assert result['is_minimal_nontrivial'] is False

    def test_modular_invariance_mod24(self):
        """c₋ = 8 N_f must satisfy c₋ ≡ 0 mod 24."""
        assert SM_ANOMALY['CHIRAL_CENTRAL_CHARGE_COEFF'] == 8
        assert SM_ANOMALY['MODULAR_INVARIANCE_MOD'] == 24


# ════════════════════════════════════════════════════════════════════
# SM Anomaly Module Tests
# ════════════════════════════════════════════════════════════════════

class TestSMAnomalyModule:
    """Test the sm_anomaly.py module functions."""

    def test_compute_fermion_anomaly_data(self):
        data = compute_fermion_anomaly_data()
        assert len(data) == 6
        for fd in data:
            assert isinstance(fd, FermionAnomalyData)
            assert fd.is_odd is True
            assert fd.anomaly_contribution == fd.components

    def test_compute_full_report(self):
        report = compute_full_anomaly_report()
        assert isinstance(report, SMAnomalyReport)
        assert report.total_components_with_nu_R == 16
        assert report.total_components_without_nu_R == 15
        assert report.anomaly_with_nu_R == 0
        assert report.anomaly_without_nu_R == 15
        assert report.three_gen_anomaly == 13  # -3 mod 16
        assert report.requires_hidden_sector is True
        assert report.generation_constraint_satisfied is True
        assert report.n_generations == 3

    def test_anomaly_cancellation_check_zero(self):
        result = anomaly_cancellation_check(0)
        assert result['hidden_sector_needed'] is False

    def test_anomaly_cancellation_check_fifteen(self):
        result = anomaly_cancellation_check(15)
        assert result['hidden_sector_needed'] is True
        assert result['hidden_anomaly_mod16'] == 1
        assert result['min_hidden_weyl'] == 1

    def test_anomaly_cancellation_check_thirteen(self):
        """3-gen SM without ν_R: visible anomaly 13 → need 3 hidden Weyl."""
        result = anomaly_cancellation_check(13)
        assert result['hidden_sector_needed'] is True
        assert result['hidden_anomaly_mod16'] == 3
        assert result['min_hidden_weyl'] == 3

    def test_anomaly_cancellation_check_sixteen(self):
        """16 is 0 mod 16 → no hidden sector."""
        result = anomaly_cancellation_check(16)
        assert result['hidden_sector_needed'] is False


# ════════════════════════════════════════════════════════════════════
# Physical Bounds
# ════════════════════════════════════════════════════════════════════

class TestPhysicalBounds:
    """Physical reasonableness checks."""

    def test_all_components_positive(self):
        for name, f in SM_FERMION_DATA.items():
            assert f['components'] > 0, f"{name} has non-positive components"

    def test_anomaly_mod16_range(self):
        """Anomaly index must be in [0, 15]."""
        for include_nu in [True, False]:
            result = sm_anomaly_index(SM_FERMION_DATA, include_nu_R=include_nu)
            assert 0 <= result['anomaly_mod16'] <= 15

    def test_generation_constraint_algebraic(self):
        """8n ≡ 0 mod 24 ↔ n ≡ 0 mod 3 for all n in [0, 100]."""
        for n in range(101):
            assert ((8 * n) % 24 == 0) == (n % 3 == 0)

    def test_z4_charge_formula_consistency(self):
        """X = 5(B-L) - 4Y gives integer for all SM fermions."""
        for name, f in SM_FERMION_DATA.items():
            X_raw = 5 * f['B_minus_L'] - 4 * f['Y']
            assert abs(X_raw - round(X_raw)) < 1e-10, f"{name}: X = {X_raw} is not integer"
