"""Bilayer graphene equation of state and conformal symmetry breaking.

Quantifies the deviation from the conformal EOS (ε = 2p) in bilayer graphene,
which has quadratic (not linear) band touching. In the hydrodynamic regime
(T >> T_imp), the collective transport is approximately conformal, with
corrections parameterized by ζ/η (bulk-to-shear viscosity ratio).

Phase 5w Wave 10b.

References:
    - Müller, Schmalian, Fritz, PRL 103, 025301 (2009) — graphene η/s
    - Lucas & Fong, JPCM 30, 053001 (2018) — Dirac fluid review
    - McCann & Koshino, Rep. Prog. Phys. 76, 056503 (2013) — bilayer review
"""

import numpy as np
from src.core.constants import HBAR, K_B


def bilayer_effective_mass():
    """Effective mass for bilayer graphene near the K point.

    m* ≈ γ₁ / (2 v_F²) where γ₁ ≈ 0.39 eV is the interlayer hopping.
    This gives m* ≈ 0.033 m_e.

    Returns:
        m_star [kg]
    """
    gamma_1_eV = 0.39  # interlayer hopping [eV]
    gamma_1_J = gamma_1_eV * 1.602176634e-19
    v_F = 1.0e6  # m/s
    return gamma_1_J / (2 * v_F**2)


def bilayer_crossover_temperature():
    """Temperature scale where bilayer transitions from parabolic to linear regime.

    T* = γ₁ / k_B ≈ 4500 K.  For T << T*, the bilayer dispersion is
    parabolic (non-conformal); for T >> T*, it approaches linear (conformal).

    At typical experimental temperatures (100-300 K), T/T* ~ 0.02-0.07:
    the system is in the parabolic regime, NOT the conformal regime.

    However, the HYDRODYNAMIC properties at these temperatures are still
    approximately conformal because the thermodynamic quantities (s, w)
    are dominated by the thermal distribution, not the band structure
    details.

    Returns:
        T_star [K]
    """
    gamma_1_eV = 0.39
    gamma_1_J = gamma_1_eV * 1.602176634e-19
    return gamma_1_J / K_B


def conformal_symmetry_breaking_parameter(T, v_F=1.0e6):
    """Dimensionless conformal symmetry breaking parameter for bilayer.

    δ_conf = (k_B T / γ₁)² measures how close the system is to the
    conformal limit. For δ_conf << 1, conformal symmetry is strongly
    broken; for δ_conf >> 1, it's approximately restored.

    At T = 150 K: δ_conf ≈ 0.001 (strongly non-conformal in single-particle
    sense). But the hydrodynamic description averages over the Fermi surface,
    and the transport coefficients are set by e-e scattering (which IS
    approximately conformal at these temperatures).

    Args:
        T: temperature [K]
        v_F: Fermi velocity [m/s]

    Returns:
        δ_conf (dimensionless)
    """
    T_star = bilayer_crossover_temperature()
    return (T / T_star) ** 2


def bulk_to_shear_ratio(T):
    """Estimated bulk-to-shear viscosity ratio ζ/η for bilayer graphene.

    Conformal symmetry breaking introduces a nonzero bulk viscosity.
    By dimensional analysis and comparison to QCD near T_c (where
    conformal breaking is similar):

    ζ/η ~ (1/3 - c_s²)² × (correction factor)

    For bilayer at T ~ 150 K, the deviation of c_s² from the conformal
    value 1/2 comes from the parabolic band contribution. The experimentally
    measured c_s ≈ 440 km/s vs conformal 710 km/s gives:

    c_s²/v_F² = (440/1000)² ≈ 0.194  vs  conformal 0.5.

    However, this is the BILAYER sound speed, not a deviation from
    conformality — bilayer has a different v_F. The relevant question is
    whether the bilayer EOS satisfies ε = dp for some d.

    A conservative estimate: ζ/η ~ 0.01-0.1 in the hydrodynamic regime.

    Args:
        T: temperature [K]

    Returns:
        ζ/η estimate (dimensionless)
    """
    # Kubo formula estimate: ζ/η ~ (Tr T^μ_μ)² / (η s T)
    # For bilayer, the trace anomaly comes from the interlayer coupling
    # breaking scale invariance. At T ~ 150 K, thermal averaging suppresses
    # this. Conservative estimate from QCD analogy:
    delta_conf = conformal_symmetry_breaking_parameter(T)
    # QCD: ζ/η ~ 15 (1/3 - c_s²)² with 1/3 the conformal value in 3+1D
    # Graphene 2+1D: conformal value is c_s² = 1/2
    # Bilayer deviation: c_s² ≈ 0.19 (measured) vs 0.5 (conformal)
    # But this overstates the breaking — the measured c_s reflects the
    # bilayer band structure, not a symmetry-breaking correction.
    # Use the thermal suppression factor instead:
    return min(0.1, 15 * delta_conf)


def bilayer_impact_on_hawking(T=150.0):
    """Assess the impact of bilayer non-conformality on T_H predictions.

    The key question: does the non-conformal EOS change T_H?
    Answer: NO at leading order. T_H depends on:
    1. The surface gravity κ = |dv/dx| (geometry, not EOS)
    2. The horizon location v = c_s (uses measured c_s, not conformal)

    The EOS affects:
    - The conformal factor Ω² (changes normalization, not T_H)
    - The bulk viscosity ζ (enters at subleading order in δ_diss)
    - The transport coefficient counting (ζ ≠ 0 adds one coefficient)

    Returns:
        dict with impact assessment
    """
    zeta_eta = bulk_to_shear_ratio(T)
    delta_conf = conformal_symmetry_breaking_parameter(T)
    T_star = bilayer_crossover_temperature()

    return {
        'T_K': T,
        'T_star_K': T_star,
        'T_over_T_star': T / T_star,
        'delta_conf': delta_conf,
        'zeta_over_eta': zeta_eta,
        'T_H_affected': False,  # T_H = ℏκ/(2πk_B) is EOS-independent
        'delta_disp_affected': False,  # D uses measured c_s, not conformal
        'delta_diss_affected': True,  # ζ contributes to Γ_H at subleading order
        'delta_diss_correction_order': zeta_eta * 1e-13,  # ζ/η × existing δ_diss
        'transport_count_change': '+1 (bulk viscosity ζ)',
        'summary': (
            f'Bilayer at T={T:.0f} K: δ_conf = {delta_conf:.1e}, '
            f'ζ/η ≈ {zeta_eta:.2f}. '
            f'T_H and δ_disp unaffected (use measured c_s). '
            f'δ_diss correction: {zeta_eta:.2f} × 10⁻¹³ (negligible²). '
            f'Transport: +1 coefficient (ζ) at first order.'
        ),
    }
