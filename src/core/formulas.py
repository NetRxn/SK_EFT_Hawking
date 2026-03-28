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

    Lean: secondOrder_count, secondOrder_count_with_parity, thirdOrder_count
    Aristotle: d61290fd, 3eedcabb

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

    Lean: secondOrder_count_with_parity, secondOrder_requires_parity_breaking
    Aristotle: d61290fd, 3eedcabb

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
# Dispersive correction (HawkingUniversality.lean: dispersive_correction_bound)
# ════════════════════════════════════════════════════════════════════

def dispersive_correction(D):
    """
    Dispersive correction to the effective Hawking temperature.

    δ_disp = -(π/6) · D²

    where D = κξ/c_s is the adiabaticity parameter.

    Lean: dispersive_correction_bound, bogoliubov_superluminal
    Aristotle: d65e3bba, 3eedcabb

    Args:
        D: adiabaticity parameter (dimensionless)

    Returns:
        δ_disp (dimensionless, negative for subluminal dispersion)
    """
    return -(np.pi / 6) * D**2


# ════════════════════════════════════════════════════════════════════
# Hawking temperature (AcousticMetric.lean)
# ════════════════════════════════════════════════════════════════════

def hawking_temperature(kappa):
    """
    Hawking temperature from surface gravity.

    T_H = hbar * kappa / (2 * pi * k_B)

    This is the Unruh-Hawking result for a 1+1D acoustic black hole.

    Lean: hawking_temp_from_surface_gravity (AcousticMetric.lean)
    Aristotle: manual

    Args:
        kappa: surface gravity [s^-1]

    Returns:
        T_H [K]
    """
    from src.core.constants import HBAR, K_B
    return HBAR * kappa / (2 * np.pi * K_B)


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

    Lean: secondOrder_vanishes_on_shell_with_positivity (WKBAnalysis.lean)
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

    Lean: effective_temp_zeroth_order
    Aristotle: c4d73ca8

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

    Lean: turning_point_shift_nonzero, turning_point_shift
    Aristotle: 518636d7, c4d73ca8

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

# ════════════════════════════════════════════════════════════════════
# ADW gap equation (ADWMechanism.lean)
# ════════════════════════════════════════════════════════════════════

def adw_effective_potential(C, G, Lambda, N_f):
    """
    Effective potential for tetrad condensation.

    V_eff(C) = C²/(2G) - (N_f/16π²)[Λ²C² - C⁴ ln(Λ²/C² + 1)]

    The first term is the tree-level HS potential.
    The second term is the one-loop Coleman-Weinberg contribution
    from integrating out N_f Dirac fermions in the tetrad background.

    Lean: critical_coupling_pos (ADWMechanism.lean) — V_eff structure verified via G_c positivity
    Aristotle: manual

    Args:
        C: Tetrad magnitude (order parameter)
        G: ADW coupling constant
        Lambda: UV cutoff
        N_f: Number of Dirac fermion species

    Returns:
        V_eff(C)
    """
    if C < 1e-15:
        return 0.0
    V_tree = C**2 / (2.0 * G)
    prefactor = N_f / (16.0 * np.pi**2)
    ratio_sq = Lambda**2 / C**2
    V_1loop = -prefactor * (Lambda**2 * C**2 - C**4 * np.log(ratio_sq + 1.0))
    return V_tree + V_1loop


def adw_critical_coupling(Lambda, N_f):
    """
    Critical coupling for tetrad condensation.

    G_c = 8π² / (N_f · Λ²)

    Derived from d²V_eff/dC²|_{C=0} = 0 with V_eff = C²/(2G) - (N_f/16π²)[...].
    For G > G_c, the origin becomes unstable and the effective potential
    develops a nontrivial minimum at C ≠ 0 (tetrad condensation).

    Lean: critical_coupling_pos (ADWMechanism.lean)

    Args:
        Lambda: UV cutoff
        N_f: Number of Dirac fermion species

    Returns:
        G_c (positive)
    """
    return 8.0 * np.pi**2 / (N_f * Lambda**2)


def adw_curvature_at_origin(G, Lambda, N_f):
    """
    Second derivative of V_eff at C=0 (curvature at the origin).

    d²V_eff/dC²|_{C=0} = 1/G - N_f · Λ² / (8π²)

    Positive for G < G_c (origin is a minimum, pre-geometric).
    Zero at G = G_c (phase transition).
    Negative for G > G_c (origin is unstable, tetrad condenses).

    In the vestigial phase analysis, this curvature determines the
    metric correlation length: ξ_metric ~ 1/√curvature. As curvature → 0
    near G_c, metric correlations grow, producing vestigial ordering.

    Lean: curvature_zero_at_Gc (ADWMechanism.lean)
    Aristotle: f8de66d1

    Args:
        G: ADW coupling constant
        Lambda: UV cutoff
        N_f: Number of Dirac fermion species

    Returns:
        d²V_eff/dC²|_{C=0}
    """
    return 1.0 / G - N_f * Lambda**2 / (8.0 * np.pi**2)


def tetrad_broken_generators(spacetime_dim):
    """
    Number of broken generators in L_c × L_s → L_J.

    n_broken = dim SO(d-1,1) = d(d-1)/2

    For d=4: n_broken = 6.

    Lean: broken_generators_4d (ADWMechanism.lean)
    Aristotle: manual

    Args:
        spacetime_dim: Dimension of spacetime (d)

    Returns:
        d(d-1)/2
    """
    d = spacetime_dim
    return d * (d - 1) // 2


def graviton_polarization_count(spacetime_dim):
    """
    Number of massless graviton polarizations in d dimensions.

    n_pol = d(d-3)/2

    For d=4: 2 polarizations (helicity ±2).
    For d=3: 0 (no gravitational waves in 2+1D).

    Lean: graviton_pol_4d (ADWMechanism.lean)
    Aristotle: manual

    Args:
        spacetime_dim: Dimension of spacetime (d)

    Returns:
        d(d-3)/2
    """
    d = spacetime_dim
    return d * (d - 3) // 2


# ════════════════════════════════════════════════════════════════════
# Beliaev damping estimate
# ════════════════════════════════════════════════════════════════════

def beliaev_damping_rate(n_1D, a_s, kappa, c_s):
    """
    Estimate the Beliaev phonon damping rate at the Hawking frequency.

    Γ_Bel(ω_H) ≈ √(n₁D · a_s³) · κ² / c_s

    This gives the total first-order damping RATE [s⁻¹] at the horizon.
    To extract EFT transport coefficients, use beliaev_transport_coefficients().

    Lean: dampingRate_firstOrder_nonneg (WKBAnalysis.lean) — verifies Γ_H ≥ 0
    Aristotle: manual (UV matching formula; Lean verifies the EFT structure, not the microscopic derivation)

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

    Lean: firstOrder_uniqueness (SKDoubling.lean) — verifies the (γ₁, γ₂) parameterization
    Aristotle: manual (UV matching; Lean verifies the EFT structure)

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


# ════════════════════════════════════════════════════════════════════
# Kappa-scaling test predictions (KappaScaling.lean)
# ════════════════════════════════════════════════════════════════════

def kappa_scaling_dispersive(kappa, xi, c_s):
    """
    Dispersive correction as a function of surface gravity kappa.

    δ_disp(κ) = -(π/6) · (ξ·κ/c_s)²

    At fixed BEC material properties (ξ, c_s constant), the dispersive
    correction scales quadratically with kappa: |δ_disp| ∝ κ².

    This is equivalent to dispersive_correction(D) with D = ξκ/c_s.

    Lean: kappa_scaling_dispersive_quadratic
    Aristotle: pending

    Args:
        kappa: surface gravity [s⁻¹]
        xi: healing length [m]
        c_s: speed of sound [m/s]

    Returns:
        δ_disp(κ) (dimensionless, negative)
    """
    D = xi * kappa / c_s
    return -(np.pi / 6) * D**2


def kappa_scaling_dissipative(kappa, gamma_1, gamma_2, c_s):
    """
    Dissipative correction as a function of surface gravity kappa.

    δ_diss(κ) = (γ₁ + γ₂) · κ / c_s²

    At fixed BEC material properties (γ₁, γ₂, c_s constant), the
    dissipative correction scales linearly with kappa: δ_diss ∝ κ.

    Derivation: Γ_H = (γ₁ + γ₂) · k_H² = (γ₁ + γ₂) · κ²/c_s²,
    then δ_diss = Γ_H/κ = (γ₁ + γ₂) · κ/c_s².

    Lean: kappa_scaling_dissipative_linear
    Aristotle: pending

    Args:
        kappa: surface gravity [s⁻¹]
        gamma_1: first-order transport coefficient [m²/s]
        gamma_2: first-order transport coefficient [m²/s]
        c_s: speed of sound [m/s]

    Returns:
        δ_diss(κ) (dimensionless, non-negative)
    """
    return (gamma_1 + gamma_2) * kappa / c_s**2


def kappa_scaling_crossover(gamma_1, gamma_2, xi):
    """
    Crossover surface gravity where |δ_disp| = δ_diss.

    κ_cross = 6 · (γ₁ + γ₂) / (π · ξ²)

    Below κ_cross: dissipative correction dominates (linear in κ).
    Above κ_cross: dispersive correction dominates (quadratic in κ).

    This crossover provides the experimental handle for the κ-scaling
    test: measuring the spectrum at multiple κ values reveals the
    transition from linear to quadratic scaling, confirming the EFT
    prediction structure.

    Derivation: Set |δ_disp| = δ_diss:
        (π/6)(ξκ/c_s)² = (γ₁+γ₂)κ/c_s²
    The c_s² cancels from both sides:
        (π/6)ξ²κ = (γ₁+γ₂)
        κ_cross = 6(γ₁+γ₂) / (πξ²)

    Lean: kappa_scaling_crossover_unique
    Aristotle: pending

    Args:
        gamma_1: first-order transport coefficient [m²/s]
        gamma_2: first-order transport coefficient [m²/s]
        xi: healing length [m]

    Returns:
        κ_cross [s⁻¹]
    """
    return 6.0 * (gamma_1 + gamma_2) / (np.pi * xi**2)


# ════════════════════════════════════════════════════════════════════
# Polariton Tier 1 corrections (PolaritonTier1.lean)
# ════════════════════════════════════════════════════════════════════

def polariton_spatial_attenuation(Gamma_pol, L, v_g):
    """
    Spatial attenuation correction for polariton Hawking radiation.

    N_corr(k) = N_meas(k) × exp[Γ_pol · L / v_g(k)]

    In driven-dissipative polariton condensates, excitations propagating
    away from the horizon decay at rate Γ_pol. The measured occupation
    must be corrected by the spatial attenuation factor to recover the
    intrinsic thermal envelope.

    Lean: polariton_attenuation_positive
    Aristotle: pending

    Args:
        Gamma_pol: polariton decay rate [s⁻¹]
        L: propagation distance from horizon [m]
        v_g: group velocity of the mode [m/s]

    Returns:
        Correction factor (≥ 1) to multiply measured occupation
    """
    if v_g <= 0 or L <= 0:
        return 1.0
    return np.exp(Gamma_pol * L / v_g)


def polariton_tier1_validity(Gamma_pol, kappa):
    """
    Tier 1 validity parameter: Γ_pol / κ.

    The perturbative Tier 1 patch (uniform imaginary frequency shift)
    is valid when Γ_pol/κ << 1. Classification:
        < 0.03: excellent (ultra-long cavities)
        < 0.1:  perturbative (long-lifetime cavities)
        < 1.0:  borderline (need Tier 2 complex couplings)
        ≥ 1.0:  intractable (need Tier 3 full open quantum system)

    Lean: polariton_validity_nonneg
    Aristotle: pending

    Args:
        Gamma_pol: polariton decay rate [s⁻¹]
        kappa: surface gravity [s⁻¹]

    Returns:
        Γ_pol / κ (dimensionless, non-negative)
    """
    if kappa <= 0:
        return float('inf')
    return Gamma_pol / kappa


def polariton_hawking_temperature(kappa):
    """
    Hawking temperature for polariton condensate.

    T_H = ℏκ/(2πk_B)

    Same formula as BEC (kinematics are identical). The key difference
    is that polariton κ values are ~10^10x larger, giving T_H ~ 0.1-4 K
    vs ~0.35 nK for BEC.

    Lean: hawking_temp_from_surface_gravity (AcousticMetric.lean) — same formula
    Aristotle: manual

    Args:
        kappa: surface gravity [s⁻¹]

    Returns:
        T_H [K]
    """
    return hawking_temperature(kappa)


# ════════════════════════════════════════════════════════════════════
# 2D ADW model / Grassmann TRG (SU2PseudoReality.lean)
# ════════════════════════════════════════════════════════════════════

def su2_one_link_integral(dim_fund=2):
    """
    SU(2) Haar measure one-link integral normalization.

    ∫ dU U_ij U*_kl = (1/dim_fund) δ_il δ_jk

    After integrating out one SU(2) gauge link connecting sites x and y,
    the gauge-coupled 4-fermion vertex becomes a color-singlet exchange
    with strength reduced by 1/dim_fund = 1/2.

    This is a consequence of Schur orthogonality for the fundamental
    representation: the normalized Haar measure on SU(2) projects
    the tensor product fund ⊗ fund* onto the singlet channel.

    Lean: su2_one_link_normalization (SU2PseudoReality.lean)
    Aristotle: pending

    Args:
        dim_fund: dimension of the fundamental representation (2 for SU(2))

    Returns:
        1/dim_fund (the normalization factor)
    """
    return 1.0 / dim_fund


def adw_2d_effective_coupling(g_EH, dim_fund=2):
    """
    Effective 4-fermion coupling in 2D after SU(2) integration.

    g_eff = g_EH / dim_fund

    In the 2D reduced ADW model, after analytically integrating out the
    SU(2) spin connection on each link using the Haar measure, the
    nearest-neighbor gauge-coupled vertex reduces to a purely fermionic
    4-fermion interaction with effective coupling g_eff.

    The cosmological (on-site) term g_cosmo is unchanged by gauge
    integration since it doesn't involve the link variable.

    Lean: effective_coupling_positive (SU2PseudoReality.lean)
    Aristotle: pending

    Args:
        g_EH: Einstein-Hilbert coupling (nearest-neighbor gauge term)
        dim_fund: dimension of fundamental representation (2 for SU(2))

    Returns:
        g_eff (effective 4-fermion coupling, same sign as g_EH)
    """
    return g_EH / dim_fund


def binder_cumulant(m2_mean, m4_mean):
    """
    Binder cumulant for an order parameter.

    U_L = 1 - <m⁴> / (3 <m²>²)

    At a second-order phase transition, U_L crosses at a universal value
    independent of lattice size L. For Ising universality class: U* ≈ 0.61.
    In the disordered phase: U_L → 0 (Gaussian fluctuations).
    In the ordered phase: U_L → 2/3 (delta-function distribution).

    For vestigial gravity: separate Binder cumulants for tetrad and metric
    order parameters. If crossings occur at different couplings, the
    vestigial phase exists as a distinct thermodynamic phase.

    Lean: binder_cumulant_ordered_limit (SU2PseudoReality.lean)
    Aristotle: pending

    Args:
        m2_mean: ensemble average <m²> of squared order parameter
        m4_mean: ensemble average <m⁴> of quartic order parameter

    Returns:
        U_L (dimensionless, between 0 and 2/3 for well-behaved distributions)
    """
    if m2_mean <= 0:
        return 0.0
    return 1.0 - m4_mean / (3.0 * m2_mean**2)


def grassmann_trg_free_energy(ln_Z, volume):
    """
    Per-site free energy from Grassmann TRG partition function.

    f = -ln(Z) / V

    The Grassmann TRG computes the partition function Z of the 2D
    lattice model by iterative tensor contraction. The free energy
    density is the intensive thermodynamic quantity.

    Phase transitions appear as non-analyticities in f(g) as a
    function of the coupling constant.

    Lean: free_energy_extensive (SU2PseudoReality.lean)
    Aristotle: pending

    Args:
        ln_Z: natural log of the partition function (from TRG)
        volume: number of lattice sites V = L²

    Returns:
        f (free energy per site)
    """
    if volume <= 0:
        return 0.0
    return -ln_Z / volume


# ════════════════════════════════════════════════════════════════════
# Phase 5 Wave 2B: 4D fermion-bag Monte Carlo
# ════════════════════════════════════════════════════════════════════

def so4_one_link_integral(dim_L=2, dim_R=2):
    """
    SO(4) ≅ SU(2)_L × SU(2)_R one-link integral factor.

    ∫ dU_{SO(4)} U_{ij} U*_{kl} = (1/dim_L)(1/dim_R) δ_il δ_jk

    Since SO(4) = SU(2)_L × SU(2)_R, each factor integrates independently
    via the Schur orthogonality relation. The combined factor is the product.

    For dim_L = dim_R = 2 (fundamental reps): factor = 1/4.

    Lean: so4_one_link_factor (FermionBag4D.lean)
    Aristotle: pending

    Args:
        dim_L: dimension of SU(2)_L fundamental rep (default 2)
        dim_R: dimension of SU(2)_R fundamental rep (default 2)

    Returns:
        1/(dim_L × dim_R)
    """
    return 1.0 / (dim_L * dim_R)


def adw_4d_effective_coupling(g_EH, dim_fund=4):
    """
    Effective nearest-neighbor coupling after SO(4) gauge integration in 4D.

    g_eff = g_EH / dim_fund = g_EH / 4

    Analogous to the 2D case (g_eff = g_EH/2) but with SO(4) fundamental
    rep dimension 4 instead of SU(2) dimension 2.

    Lean: so4_effective_coupling_pos (FermionBag4D.lean)
    Aristotle: pending

    Args:
        g_EH: Einstein-Hilbert gauge coupling
        dim_fund: SO(4) fundamental representation dimension (default 4)

    Returns:
        Effective 4-fermion coupling after gauge integration
    """
    return g_EH / dim_fund


def eight_fermion_vertex_weight(n_occ, g_cosmo):
    """
    Boltzmann weight for the on-site 8-fermion cosmological vertex.

    The 8-fermion vertex is the product of all 8 Grassmann variables
    at a site. Its weight is:
        w = exp(-g_cosmo × Π_{i=1}^{8} n_i)

    Since each n_i ∈ {0,1}, the product is 1 only when ALL 8 variables
    are occupied (n_occ = 8), otherwise 0.

    w(n_occ < 8) = 1  (no cosmological contribution)
    w(n_occ = 8) = exp(-g_cosmo)  (full 8-fermion vertex)

    Lean: eight_fermion_weight_bounds (FermionBag4D.lean)
    Aristotle: pending

    Args:
        n_occ: number of occupied Grassmann variables at the site (0-8)
        g_cosmo: cosmological coupling constant

    Returns:
        Boltzmann weight for this occupation configuration
    """
    import numpy as np
    if n_occ == 8:
        return np.exp(-g_cosmo)
    return 1.0


def fermion_bag_local_weight(bag_config, g_cosmo, g_eff):
    """
    Total Boltzmann weight for a fermion bag configuration.

    A fermion bag is a connected cluster of sites where Grassmann
    variables are occupied. The weight is the product of:
    1. On-site 8-fermion vertices (cosmological term)
    2. Nearest-neighbor 4-fermion bonds (Einstein-Hilbert term)

    W(bag) = Π_sites exp(-g_cosmo × δ_{n=8}) × Π_bonds exp(-g_eff × n_bond)

    where n_bond is the bond occupation (0 or 1) and δ_{n=8} is 1 only
    when all 8 Grassmann variables at a site are occupied.

    Lean: fermion_bag_weight_positive (FermionBag4D.lean)
    Aristotle: pending

    Args:
        bag_config: dict with 'site_occupations' (list of ints 0-8)
                    and 'bond_occupations' (list of ints 0 or 1)
        g_cosmo: cosmological coupling
        g_eff: effective NN coupling (after SO(4) integration)

    Returns:
        Total Boltzmann weight (always positive for Euclidean SO(4))
    """
    import numpy as np
    w = 1.0
    for n_occ in bag_config['site_occupations']:
        w *= eight_fermion_vertex_weight(n_occ, g_cosmo)
    for n_bond in bag_config['bond_occupations']:
        w *= np.exp(-g_eff * n_bond)
    return w


def metric_correlator_connected(tetrad_m2, tetrad_m4):
    """
    Connected metric correlator from tetrad moments.

    The metric is the composite operator g_μν = η_{ab} E^a_μ E^b_ν.
    The connected correlator (vestigial diagnostic) is:

    ⟨g_μν g_ρσ⟩_c = ⟨E²E²⟩ - ⟨E²⟩² = m4 - m2²

    where m2 = ⟨|E|²⟩ and m4 = ⟨|E|⁴⟩.

    In the vestigial phase: ⟨E⟩ = 0 but ⟨g⟩ ≠ 0, so m4 - m2² > 0.
    In the pre-geometric phase: m4 - m2² → 0.
    In the tetrad-ordered phase: m4 ≈ m2² (Gaussian).

    Lean: metric_correlator_nonneg (FermionBag4D.lean)
    Aristotle: pending

    Args:
        tetrad_m2: ⟨|E|²⟩ (second moment of tetrad magnitude)
        tetrad_m4: ⟨|E|⁴⟩ (fourth moment of tetrad magnitude)

    Returns:
        Connected metric correlator (≥ 0 by Cauchy-Schwarz)
    """
    return max(0.0, tetrad_m4 - tetrad_m2**2)


def vestigial_phase_indicator(binder_tetrad, binder_metric):
    """
    Classify phase from Binder cumulants of tetrad and metric order parameters.

    Phase classification (Volovik 2024):
    - Pre-geometric:  U_tetrad → 0, U_metric → 0
    - Vestigial:      U_tetrad → 0, U_metric → 2/3
    - Tetrad-ordered: U_tetrad → 2/3, U_metric → 2/3

    The vestigial phase exists iff there's a coupling window where
    U_metric has crossed to 2/3 but U_tetrad has not.

    Lean: vestigial_phase_splitting (FermionBag4D.lean)
    Aristotle: pending

    Args:
        binder_tetrad: Binder cumulant for tetrad order parameter
        binder_metric: Binder cumulant for metric order parameter

    Returns:
        String: 'pre_geometric', 'vestigial', 'tetrad_ordered', or 'crossover'
    """
    threshold_ordered = 0.4    # U_L > 0.4 indicates ordered
    threshold_disordered = 0.2  # U_L < 0.2 indicates disordered

    metric_ordered = binder_metric > threshold_ordered
    tetrad_ordered = binder_tetrad > threshold_ordered
    metric_disordered = binder_metric < threshold_disordered
    tetrad_disordered = binder_tetrad < threshold_disordered

    if tetrad_disordered and metric_disordered:
        return 'pre_geometric'
    elif tetrad_disordered and metric_ordered:
        return 'vestigial'
    elif tetrad_ordered and metric_ordered:
        return 'tetrad_ordered'
    else:
        return 'crossover'
