"""
Standard Model Anomaly Computation in ℤ₁₆.

Computes the SM's anomaly class from representation-theoretic data:
  - ℤ₄ charge X = 5(B-L) - 4Y for each fermion
  - Anomaly index: sum of components with odd ℤ₄ charge, valued in ℤ₁₆
  - Generation constraint: N_f ≡ 0 mod 3 from modular invariance

All physics formulas imported from formulas.py. All constants from constants.py.

Lean verification:
  - SMFermionData.lean: fermion enumeration, ℤ₄ charges, component counts
  - Z16AnomalyComputation.lean: anomaly index, hidden sector theorem
  - GenerationConstraint.lean: N_f ≡ 0 mod 3

References:
  García-Etxebarria & Montero, JHEP 08, 003 (2019) [arXiv:1808.00009]
  Wang, PRD 110, 125028 (2024) [arXiv:2312.14928]
"""

from dataclasses import dataclass

from src.core.constants import SM_FERMION_DATA, SM_Z4_CHARGE_FORMULA, SM_ANOMALY
from src.core.formulas import (
    sm_z4_charge,
    sm_anomaly_index,
    sm_three_gen_anomaly,
    sm_generation_constraint,
)


@dataclass
class FermionAnomalyData:
    """Anomaly data for a single SM fermion multiplet."""
    name: str
    label: str
    B_minus_L: float
    Y: float
    components: int
    z4_charge: int
    is_odd: bool
    anomaly_contribution: int


@dataclass
class SMAnomalyReport:
    """Complete anomaly analysis for the Standard Model."""
    fermion_data: list[FermionAnomalyData]
    total_components_with_nu_R: int
    total_components_without_nu_R: int
    anomaly_with_nu_R: int
    anomaly_without_nu_R: int
    three_gen_anomaly: int
    requires_hidden_sector: bool
    generation_constraint_satisfied: bool
    n_generations: int


def compute_fermion_anomaly_data() -> list[FermionAnomalyData]:
    """Compute ℤ₄ charge and anomaly contribution for each SM fermion."""
    result = []
    for name, f in SM_FERMION_DATA.items():
        z4 = sm_z4_charge(f['B_minus_L'], f['Y'])
        is_odd = (z4 % 2 == 1)
        result.append(FermionAnomalyData(
            name=name,
            label=f['label'],
            B_minus_L=f['B_minus_L'],
            Y=f['Y'],
            components=f['components'],
            z4_charge=z4,
            is_odd=is_odd,
            anomaly_contribution=f['components'] if is_odd else 0,
        ))
    return result


def compute_full_anomaly_report() -> SMAnomalyReport:
    """Compute the complete SM anomaly analysis.

    Returns a SMAnomalyReport with all anomaly computations,
    generation constraints, and hidden sector requirements.
    """
    fermion_data = compute_fermion_anomaly_data()

    # One-generation anomaly (with and without ν_R)
    result_with = sm_anomaly_index(SM_FERMION_DATA, include_nu_R=True)
    result_without = sm_anomaly_index(SM_FERMION_DATA, include_nu_R=False)

    # Three-generation anomaly (without ν_R)
    three_gen = sm_three_gen_anomaly(
        result_without['total_components'],
        n_gen=SM_ANOMALY['N_GENERATIONS'],
    )

    # Generation constraint
    gen_constraint = sm_generation_constraint(SM_ANOMALY['N_GENERATIONS'])

    return SMAnomalyReport(
        fermion_data=fermion_data,
        total_components_with_nu_R=result_with['total_components'],
        total_components_without_nu_R=result_without['total_components'],
        anomaly_with_nu_R=result_with['anomaly_mod16'],
        anomaly_without_nu_R=result_without['anomaly_mod16'],
        three_gen_anomaly=three_gen['anomaly_mod16'],
        requires_hidden_sector=three_gen['requires_hidden_sector'],
        generation_constraint_satisfied=gen_constraint['satisfies_generation_constraint'],
        n_generations=SM_ANOMALY['N_GENERATIONS'],
    )


def anomaly_cancellation_check(visible_anomaly: int) -> dict:
    """Check what hidden sector content is needed to cancel a given anomaly.

    Args:
        visible_anomaly: anomaly index of visible sector (mod 16)

    Returns:
        dict with required hidden sector anomaly and minimal Weyl fermion count
    """
    mod16 = visible_anomaly % 16
    if mod16 == 0:
        return {
            'visible_anomaly_mod16': 0,
            'hidden_sector_needed': False,
            'hidden_anomaly_mod16': 0,
            'min_hidden_weyl': 0,
        }
    hidden = (16 - mod16) % 16
    return {
        'visible_anomaly_mod16': mod16,
        'hidden_sector_needed': True,
        'hidden_anomaly_mod16': hidden,
        'min_hidden_weyl': hidden,
    }
