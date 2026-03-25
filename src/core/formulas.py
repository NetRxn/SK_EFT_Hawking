"""
Canonical implementations of every formula verified by Lean/Aristotle.

Each function documents which Lean theorem it corresponds to,
the Aristotle run ID, and the exact mathematical statement.

These are the SINGLE SOURCE OF TRUTH for formulas used in notebooks,
visualizations, and paper numerical estimates. No other file in the
project should reimplement these.

Unit conventions:
    - All inputs/outputs in SI unless otherwise noted.
    - Transport coefficients γ₁, γ₂ are [m²/s] (diffusion coefficients).
    - Transport coefficients γ_{2,1}, γ_{2,2} are [m³/s].
    - Frequencies ω, κ are [s⁻¹].
    - Wavenumbers k are [m⁻¹].
    - The damping rate Γ has units [s⁻¹].
    - All corrections δ are dimensionless.
"""

import numpy as np


# ════════════════════════════════════════════════════════════════════
# Counting formula (SecondOrderSK.lean)
# ════════════════════════════════════════════════════════════════════

def count_coefficients(N: int) -> int:
    """
    Number of independent transport coefficients at EFT order N.

    count(N) = ⌊(N+1)/2⌋ + 1

    Lean: secondOrder_count, counting_formula_N2, counting_formula_N3
    Aristotle: d61290fd (all three)

    At N=1: count=2 (γ₁, γ₂)
    At N=2: count=2 new (γ_{2,1}, γ_{2,2})
    At N=3: count=3 new
    """
    return (N + 1) // 2 + 1


def enumerate_monomials(N: int, require_spatial_parity: bool = False):
    """
    Enumerate (m, n) pairs for SK monomials ψ_a · ∂_t^m ∂_x^n ψ_r
    at EFT order N.

    Constraints:
        - m + n = N + 1 (derivative level L = N+1)
        - m even (KMS / time-reversal invariance)
        - if require_spatial_parity: n even

    Lean: spatial_parity_eliminates_second_order, parity_null_test
    Aristotle: 3eedcabb

    Returns:
        List of (m, n) tuples.
    """
    L = N + 1
    pairs = []
    for m in range(0, L + 1, 2):  # m = 0, 2, 4, ...
        n = L - m
        if n >= 0:
            if require_spatial_parity and n % 2 != 0:
                continue
            pairs.append((m, n))
    return pairs


# ════════════════════════════════════════════════════════════════════
# Damping rate (WKBAnalysis.lean: DissipativeDispersion.dampingRate)
# ════════════════════════════════════════════════════════════════════

def damping_rate(k, omega, c_s, gamma_1, gamma_2, gamma_2_1=0.0, gamma_2_2=0.0,
                 gamma_3_1=0.0, gamma_3_2=0.0, gamma_3_3=0.0):
    """
    Dissipative damping rate including first, second, and third order.

    Γ(k, ω) = γ₁·k² + γ₂·ω²/c_s²                        (order 1)
            + γ_{2,1}·k³ + γ_{2,2}·ω²·k/c_s²             (order 2)
            + γ_{3,1}·k⁴ + γ_{3,2}·ω²·k²/c_s² + γ_{3,3}·ω⁴/c_s⁴  (order 3)

    Lean: dampingRate_eq_zero_iff — proves Γ=0 for all (k,ω) iff all γᵢ=0.
    Aristotle: 518636d7

    Parity alternation:
        Order 1 terms (k², ω²) are parity-even → universal
        Order 2 terms (k³, ω²k) are parity-odd → require background flow
        Order 3 terms (k⁴, ω²k², ω⁴) are parity-even → universal

    Args:
        k: wavenumber [m⁻¹]
        omega: frequency [s⁻¹]
        c_s: speed of sound [m/s]
        gamma_1: first-order transport coefficient [m²/s]
        gamma_2: first-order transport coefficient [m²/s]
        gamma_2_1: second-order transport coefficient [m³/s]
        gamma_2_2: second-order transport coefficient [m³/s]
        gamma_3_1: third-order transport coefficient [m⁴/s]
        gamma_3_2: third-order transport coefficient [m⁴/s]
        gamma_3_3: third-order transport coefficient [m⁴/s]

    Returns:
        Γ(k, ω) [s⁻¹]
    """
    first_order = gamma_1 * k**2 + gamma_2 * (omega**2 / c_s**2)
    second_order = gamma_2_1 * k**3 + gamma_2_2 * (omega**2 * k / c_s**2)
    third_order = (gamma_3_1 * k**4 +
                   gamma_3_2 * (omega**2 * k**2 / c_s**2) +
                   gamma_3_3 * (omega**4 / c_s**4))
    return first_order + second_order + third_order


# ════════════════════════════════════════════════════════════════════
# Dispersive correction (HawkingUniversality.lean: dispersive_bound)
# ════════════════════════════════════════════════════════════════════

def dispersive_correction(D):
    """
    Dispersive correction to the effective Hawking temperature.

    δ_disp = -(π/6) · D²

    where D = κξ/c_s is the adiabaticity parameter.

    Lean: dispersive_bound, dispersive_bound_tight
    Aristotle: a87f425a, 3eedcabb

    Args:
        D: adiabaticity parameter (dimensionless)

    Returns:
        δ_disp (dimensionless, negative for subluminal dispersion)
    """
    return -(np.pi / 6) * D**2


# ════════════════════════════════════════════════════════════════════
# First-order dissipative correction (WKBAnalysis.lean)
# ════════════════════════════════════════════════════════════════════

def first_order_correction(Gamma_H, kappa):
    """
    First-order dissipative correction to T_eff.

    δ_diss = Γ_H / κ

    This is FREQUENCY-INDEPENDENT (constant across spectrum).

    Lean: firstOrder_correction_zero_iff — proves δ_diss=0 iff Γ_H=0.
          Uses κ > 0 (total-division strengthening).
    Aristotle: 518636d7

    Args:
        Gamma_H: damping rate at horizon [s⁻¹]
        kappa: surface gravity [s⁻¹]

    Returns:
        δ_diss (dimensionless)
    """
    return Gamma_H / kappa


# ════════════════════════════════════════════════════════════════════
# Second-order dissipative correction (WKBAnalysis.lean)
# ════════════════════════════════════════════════════════════════════

def second_order_correction(k, omega, c_s, gamma_2_1, gamma_2_2, kappa):
    """
    Second-order dissipative correction to T_eff.

    δ⁽²⁾(ω) = [γ_{2,1}·k³ + γ_{2,2}·ω²·k/c_s²] / κ

    This is FREQUENCY-DEPENDENT — the new physics of Phase 2.
    With the positivity constraint γ_{2,2} = -γ_{2,1}, it simplifies to:
    δ⁽²⁾(ω) = γ_{2,1}·k·(k² - ω²/c_s²) / κ
    which vanishes for acoustic modes (k = ω/c_s) and grows with dispersion.

    Lean: secondOrderCorrection (WKBAnalysis.lean)
    Aristotle: 518636d7

    Args:
        k: wavenumber [m⁻¹]
        omega: frequency [s⁻¹]
        c_s: speed of sound [m/s]
        gamma_2_1: second-order transport coefficient [m³/s]
        gamma_2_2: second-order transport coefficient [m³/s]
        kappa: surface gravity [s⁻¹]

    Returns:
        δ⁽²⁾(ω) (dimensionless)
    """
    Gamma_H_2 = gamma_2_1 * k**3 + gamma_2_2 * (omega**2 * k / c_s**2)
    return Gamma_H_2 / kappa


# ════════════════════════════════════════════════════════════════════
# Effective temperature (WKBAnalysis.lean: effectiveTemperature)
# ════════════════════════════════════════════════════════════════════

def third_order_correction(k, omega, c_s, gamma_3_1, gamma_3_2, gamma_3_3, kappa):
    """
    Third-order dissipative correction to T_eff.

    δ⁽³⁾(ω) = [γ_{3,1}·k⁴ + γ_{3,2}·ω²·k²/c_s² + γ_{3,3}·ω⁴/c_s⁴] / κ

    This is FREQUENCY-DEPENDENT and EVEN in ω — the new physics of Phase 3.
    Unlike second-order (odd in ω, requires parity breaking), third-order
    corrections are parity-preserving and exist universally.

    The γ_{3,1}·k⁴ term has the same structure as the Bogoliubov
    superluminal dispersion ℏ²k⁴/(4m²), connecting the EFT to the
    microscopic UV physics of the BEC.

    Lean: thirdOrder_count, cumulative_count_through_3
    Aristotle: 3eedcabb

    Args:
        k: wavenumber [m⁻¹]
        omega: frequency [s⁻¹]
        c_s: speed of sound [m/s]
        gamma_3_1: third-order transport coefficient [m⁴/s]
        gamma_3_2: third-order transport coefficient [m⁴/s]
        gamma_3_3: third-order transport coefficient [m⁴/s]
        kappa: surface gravity [s⁻¹]

    Returns:
        δ⁽³⁾(ω) (dimensionless)
    """
    Gamma_3 = (gamma_3_1 * k**4 +
               gamma_3_2 * (omega**2 * k**2 / c_s**2) +
               gamma_3_3 * (omega**4 / c_s**4))
    return Gamma_3 / kappa


def effective_temperature_ratio(omega, c_s, kappa, D,
                                 gamma_1, gamma_2,
                                 gamma_2_1=0.0, gamma_2_2=0.0):
    """
    Ratio T_eff(ω) / T_H including all corrections.

    T_eff/T_H = 1 + δ_disp + δ_diss + δ⁽²⁾(ω)

    Lean: effective_temperature_well_defined
    Aristotle: 518636d7

    Args:
        omega: frequency [s⁻¹]
        c_s: speed of sound [m/s]
        kappa: surface gravity [s⁻¹]
        D: adiabaticity parameter (dimensionless)
        gamma_1, gamma_2: first-order transport coefficients [m²/s]
        gamma_2_1, gamma_2_2: second-order transport coefficients [m³/s]

    Returns:
        (ratio, details_dict) where ratio = T_eff/T_H and details_dict
        contains the individual corrections.
    """
    k = omega / c_s  # On-shell acoustic wavenumber

    delta_disp = dispersive_correction(D)
    Gamma_H = damping_rate(k, omega, c_s, gamma_1, gamma_2, gamma_2_1, gamma_2_2)
    delta_diss = first_order_correction(Gamma_H, kappa)
    delta_2 = second_order_correction(k, omega, c_s, gamma_2_1, gamma_2_2, kappa)

    ratio = 1.0 + delta_disp + delta_diss + delta_2

    return ratio, {
        'delta_disp': delta_disp,
        'delta_diss': delta_diss,
        'delta_2': delta_2,
        'Gamma_H': Gamma_H,
    }


# ════════════════════════════════════════════════════════════════════
# WKB turning point shift (WKBAnalysis.lean: turning_point_shift_nonzero)
# ════════════════════════════════════════════════════════════════════

def turning_point_shift(Gamma_H, kappa, c_s):
    """
    Imaginary part of WKB turning point shift due to dissipation.

    δx_imag = c_s · Γ_H / (2κ²)

    In the WKB connection formula, the turning point at x* ≈ -i·c_s/κ
    acquires an additional imaginary shift proportional to Γ_H/κ:
        x* ≈ -i·(c_s/κ)·(1 + Γ_H/(2κ))

    The Lean theorem `turning_point_shift_nonzero` proves that
    Γ_H > 0, κ > 0, c_s > 0 imply δx > 0.

    Lean: turning_point_shift_nonzero, turning_point_shift_nonzero_strengthened
    Aristotle: 518636d7

    Args:
        Gamma_H: damping rate at horizon [s⁻¹]
        kappa: surface gravity [s⁻¹]
        c_s: speed of sound [m/s]

    Returns:
        δx_imag [m] — imaginary shift in position of WKB turning point
    """
    return c_s * Gamma_H / (2 * kappa**2)


# ════════════════════════════════════════════════════════════════════
# Decoherence parameter (WKBConnection.lean: decoherence_nonneg)
# ════════════════════════════════════════════════════════════════════

def decoherence_parameter(Gamma_H, kappa):
    """
    Decoherence parameter for the modified Bogoliubov relation.

    δ_k = 2 · Γ_H / κ = 2 · δ_diss

    This measures the probability of phonon absorption during horizon
    crossing. The factor of 2 arises from the two traversals of the
    dissipative region on the SK contour (retarded + advanced branches).

    Modified unitarity: |α|² - |β|² = 1 - δ_k

    Lean: decoherence_nonneg, decoherence_double_delta_diss,
          decoherence_zero_iff (WKBConnection.lean)

    Args:
        Gamma_H: damping rate at horizon [s⁻¹]
        kappa: surface gravity [s⁻¹]

    Returns:
        δ_k (dimensionless, non-negative)
    """
    if kappa <= 0:
        return 0.0
    return 2.0 * Gamma_H / kappa


def fdr_noise_floor(delta_k, omega=None, T_env=0.0):
    """
    FDR/KMS-mandated noise floor.

    n_noise = δ_k / 2  (at T_env = 0)

    The fluctuation-dissipation relation requires that dissipation
    is accompanied by noise. At zero environment temperature,
    n_noise = δ_k/2 = Γ_H/κ = δ_diss.

    Lean: noise_floor_nonneg, noise_floor_eq_delta_diss,
          noise_floor_zero_iff (WKBConnection.lean)

    Args:
        delta_k: decoherence parameter
        omega: mode frequency (unused at T_env=0, for future extension)
        T_env: environment temperature (default 0)

    Returns:
        n_noise (dimensionless, non-negative)
    """
    if delta_k <= 0:
        return 0.0
    if T_env > 0 and omega is not None and omega > 0:
        x = omega / (2.0 * T_env)
        if x > 30:
            coth_x = 1.0
        elif x < 1e-10:
            coth_x = 1.0 / x
        else:
            coth_x = 1.0 / np.tanh(x)
        return (delta_k / 2.0) * coth_x
    return delta_k / 2.0


# ════════════════════════════════════════════════════════════════════
# Beliaev damping estimate
# ════════════════════════════════════════════════════════════════════

def beliaev_damping_rate(n_1D, a_s, kappa, c_s):
    """
    Estimate the Beliaev phonon damping rate at the Hawking frequency.

    Γ_Bel(ω_H) ≈ √(n₁D · a_s³) · κ² / c_s

    This gives the total first-order damping RATE [s⁻¹] at the horizon.
    To extract EFT transport coefficients, use beliaev_transport_coefficients().

    Args:
        n_1D: quasi-1D linear density [m⁻¹]
        a_s: s-wave scattering length [m]
        kappa: surface gravity [s⁻¹]
        c_s: speed of sound [m/s]

    Returns:
        Γ_Bel [s⁻¹]
    """
    return np.sqrt(n_1D * a_s**3) * kappa**2 / c_s


def beliaev_transport_coefficients(n_1D, a_s, kappa, c_s, xi):
    """
    Extract EFT transport coefficients from the Beliaev damping estimate.

    At the horizon (ω = κ, k_H = κ/c_s), the EFT damping rate is:
        Γ_H = (γ₁ + γ₂) · k_H²

    Matching to Beliaev: γ₁ = γ₂ = Γ_Bel / (2·k_H²)
    (equal splitting from leading-order KMS: FirstOrderKMS theorem)

    Second-order coefficients are suppressed by ξ/c_s:
        γ_{2,1} scale ~ Γ_Bel · (ξ/c_s) / (2·k_H³)
        γ_{2,2} = -γ_{2,1}  (positivity constraint)

    Args:
        n_1D: quasi-1D linear density [m⁻¹]
        a_s: s-wave scattering length [m]
        kappa: surface gravity [s⁻¹]
        c_s: speed of sound [m/s]
        xi: healing length [m]

    Returns:
        dict with keys: gamma_1, gamma_2, gamma_2_1, gamma_2_2,
                        Gamma_Bel, k_H
    """
    Gamma_Bel = beliaev_damping_rate(n_1D, a_s, kappa, c_s)
    k_H = kappa / c_s

    # First-order transport coefficients [m²/s]
    gamma_1 = Gamma_Bel / (2 * k_H**2)
    gamma_2 = gamma_1  # KMS: equal splitting at leading order

    # Second-order transport coefficients [m³/s]
    Gamma_Bel_2nd = Gamma_Bel * xi / c_s
    gamma_2_1 = Gamma_Bel_2nd / (2 * k_H**3)
    gamma_2_2 = -gamma_2_1  # Positivity constraint

    return {
        'gamma_1': gamma_1,
        'gamma_2': gamma_2,
        'gamma_2_1': gamma_2_1,
        'gamma_2_2': gamma_2_2,
        'Gamma_Bel': Gamma_Bel,
        'k_H': k_H,
    }
