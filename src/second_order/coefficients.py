"""Second-Order SK-EFT: Frequency-Dependent Corrections to Dissipative Hawking Radiation.

Extends the Phase 1 first-order SK-EFT (2 free parameters: γ₁, γ₂)
to second order in the derivative expansion.

Results (from second_order_enumeration.py, validated against Phase 1 Lean):

    Order 1 (L=2): 2 transport coefficients (γ₁, γ₂)
        - ψ_a · ∂²_t ψ_r  and  ψ_a · ∂²_x ψ_r
        - Lean-verified: FirstOrderKMS → 9 coefficients reduced to 2

    Order 2 (L=3): 2 NEW transport coefficients (γ_{2,1}, γ_{2,2})
        - ψ_a · ∂³_x ψ_r      (m=0, n=3) — cubic spatial dispersion
        - ψ_a · ∂²_t ∂_x ψ_r  (m=2, n=1) — temporal-spatial damping
        - Both require broken spatial parity (odd n) → only present with
          background flow (BEC transonic configuration)
        - With parity: ZERO new coefficients at this order

    General formula: floor((N+1)/2) + 1 at order N

Physical implications:
    At first order, δ_diss = Γ_H/κ is frequency-INDEPENDENT.
    At second order, the correction becomes frequency-dependent:

        δ^(2)(ω) = γ_{2,1} · (ω/Λ_x)³ + γ_{2,2} · (ω²/Λ²) · (ω/Λ_x)

    where Λ is the EFT cutoff and Λ_x ~ κ/c_s is the spatial momentum scale
    set by the background flow gradient. This generates a non-trivial spectral
    shape that is in principle measurable.

Lean formalization:
    SecondOrderSK.lean provides:
    - SecondOrderCoeffs, SecondOrderDissipativeCoeffs structures
    - SecondOrderKMS: T-reversal kills 2 of 4 candidate monomials
    - secondOrder_uniqueness: proven (direct from SecondOrderKMS)
    - secondOrder_count: 2 new coefficients (sorry, for Aristotle)
    - secondOrder_count_with_parity: 0 with parity (sorry, for Aristotle)

References:
    - Crossley-Glorioso-Liu, JHEP 2017 (arXiv:1511.03646)
    - Jain-Kovtun, JHEP 2024 (arXiv:2309.00511)
    - Glorioso-Liu, JHEP 2018 (arXiv:1612.07705)
"""

from dataclasses import dataclass
from typing import Optional

import numpy as np


# ═══════════════════════════════════════════════════════════════════
# Transport coefficient data structures
# ═══════════════════════════════════════════════════════════════════

@dataclass
class FirstOrderCoeffs:
    """First-order SK-EFT transport coefficients (Phase 1, Lean-verified).

    Physical meaning:
        gamma_1: Coefficient of ψ_a · (∂²_t - ∂²_x)ψ_r = ψ_a · □ψ_r.
            This is the "sound cone" damping — it damps the wave operator.
            Microscopically related to Beliaev damping rate.

        gamma_2: Coefficient of ψ_a · ∂²_t ψ_r.
            This is "anomalous density" damping — it breaks the (∂_t, ∂_x)
            symmetry of the wave operator. Physically related to the
            anomalous density fluctuations ⟨ψ̂ψ̂⟩.

    Constraints:
        gamma_1 ≥ 0, gamma_2 ≥ 0 (from positivity / second law)

    FDR (from FirstOrderKMS):
        i₁ = γ₁/β  (noise coefficient for ψ_a²)
        i₂ = γ₂/β  (noise coefficient for (∂_t ψ_a)²)
        i₃ = 0      (no (∂_x ψ_a)² noise at first order)
    """
    gamma_1: float  # ψ_a · □ψ_r
    gamma_2: float  # ψ_a · ∂²_t ψ_r

    def __post_init__(self):
        if self.gamma_1 < 0:
            raise ValueError(f"gamma_1 must be ≥ 0 (got {self.gamma_1})")
        if self.gamma_2 < 0:
            raise ValueError(f"gamma_2 must be ≥ 0 (got {self.gamma_2})")


@dataclass
class SecondOrderCoeffs:
    """Second-order SK-EFT transport coefficients (Phase 2, new result).

    At derivative level 3, the four candidate monomials are:
        ψ_a · ∂³_x ψ_r       (m=0, n=3) — SURVIVES (m even)
        ψ_a · ∂_t ∂²_x ψ_r   (m=1, n=2) — KILLED (m odd, T-reversal)
        ψ_a · ∂²_t ∂_x ψ_r   (m=2, n=1) — SURVIVES (m even)
        ψ_a · ∂³_t ψ_r        (m=3, n=0) — KILLED (m odd, T-reversal)

    After T-reversal: 2 surviving coefficients.
    Both have odd n → require broken spatial parity (background flow).

    Physical meaning:
        gamma_2_1: Coefficient of ψ_a · ∂³_x ψ_r.
            Cubic spatial dispersion/damping. Generates ω³ corrections
            in the dispersion relation. Analogous to third-order dispersion
            in nonlinear optics.

        gamma_2_2: Coefficient of ψ_a · ∂²_t ∂_x ψ_r.
            Flow-dependent temporal-spatial damping. Mixes time and space
            derivatives in a parity-breaking way. Generates ω²k corrections
            where k is set by the background flow gradient.

    The signs of γ_{2,1} and γ_{2,2} are NOT constrained by positivity alone
    at this order (positivity constraints at second order involve the full
    imaginary sector including first-order terms). This is an important
    difference from first order.
    """
    gamma_2_1: float  # ψ_a · ∂³_x ψ_r  (cubic spatial)
    gamma_2_2: float  # ψ_a · ∂²_t ∂_x ψ_r  (temporal-spatial)


@dataclass
class FullCoeffs:
    """Combined first + second order transport coefficients.

    Total: 4 free parameters (2 first-order + 2 second-order).
    Through order 2, the SK-EFT for a BEC with background flow has
    4 independent dissipative transport coefficients.

    With spatial parity (no flow): only 2 (the first-order ones).
    """
    first: FirstOrderCoeffs
    second: SecondOrderCoeffs

    @property
    def n_total(self) -> int:
        """Total number of transport coefficients through second order."""
        return 4


# ═══════════════════════════════════════════════════════════════════
# SK action construction
# ═══════════════════════════════════════════════════════════════════

def first_order_action_re(gamma_1: float, gamma_2: float,
                          psi_a: float, dtt_psi_r: float,
                          dxx_psi_r: float) -> float:
    """Real part of the first-order SK action (dissipative response).

    L_re^(1) = γ₁ · ψ_a · (∂²_t - ∂²_x)ψ_r + γ₂ · ψ_a · ∂²_t ψ_r

    This matches firstOrderDissipativeAction in SKDoubling.lean.
    """
    return gamma_1 * psi_a * (dtt_psi_r - dxx_psi_r) + \
           gamma_2 * psi_a * dtt_psi_r


def first_order_action_im(gamma_1: float, gamma_2: float, beta: float,
                          psi_a: float, dt_psi_a: float) -> float:
    """Imaginary part of the first-order SK action (noise).

    L_im^(1) = (γ₁/β) · ψ_a² + (γ₂/β) · (∂_t ψ_a)²

    Fixed by FDR relative to L_re^(1).
    """
    return (gamma_1 / beta) * psi_a**2 + (gamma_2 / beta) * dt_psi_a**2


def second_order_action_re(gamma_2_1: float, gamma_2_2: float,
                           psi_a: float, dxxx_psi_r: float,
                           dttx_psi_r: float) -> float:
    """Real part of the second-order SK action correction.

    L_re^(2) = γ_{2,1} · ψ_a · ∂³_x ψ_r + γ_{2,2} · ψ_a · ∂²_t ∂_x ψ_r

    Both monomials break spatial parity (odd n).
    """
    return gamma_2_1 * psi_a * dxxx_psi_r + \
           gamma_2_2 * psi_a * dttx_psi_r


# ═══════════════════════════════════════════════════════════════════
# Frequency-dependent corrections
# ═══════════════════════════════════════════════════════════════════

def hawking_correction_first_order(
    gamma_1: float,
    gamma_2: float,
    kappa: float,
    c_s: float,
) -> float:
    """First-order correction to the Hawking temperature.

    δ_diss = Γ_H / κ  where  Γ_H = effective damping rate at the horizon.

    This is frequency-INDEPENDENT (a constant shift in T_eff).

    Args:
        gamma_1: First transport coefficient.
        gamma_2: Second transport coefficient.
        kappa: Surface gravity of the acoustic horizon.
        c_s: Sound speed at the horizon.

    Returns:
        δ_diss (dimensionless correction to T_H).
    """
    # The effective damping rate Γ_H depends on the mode structure at the horizon.
    # From Phase 1: Γ_H ∝ (γ₁ + γ₂) · κ² / c_s (Beliaev damping scaling)
    gamma_eff = gamma_1 + gamma_2
    Gamma_H = gamma_eff * kappa**2 / c_s
    return Gamma_H / kappa


def hawking_correction_second_order(
    omega: float | np.ndarray,
    coeffs: FullCoeffs,
    kappa: float,
    c_s: float,
    v_gradient: float,
) -> float | np.ndarray:
    """Second-order correction to the Hawking spectrum (frequency-dependent).

    δ^(2)(ω) = γ_{2,1} · (ω · ξ / c_s)³ / κ
             + γ_{2,2} · (ω · ξ / c_s)² · (v' · ξ / c_s) / κ

    where ξ = c_s / κ is the natural length scale at the horizon.

    The key new physics:
    1. The correction is frequency-dependent → spectral shape distortion
    2. Both terms are odd powers of ω/Λ_x → asymmetry between ω > 0 and ω < 0
    3. The v_gradient dependence shows this is purely a background-flow effect

    Args:
        omega: Mode frequency (or array of frequencies).
        coeffs: Full first + second order transport coefficients.
        kappa: Surface gravity at the acoustic horizon.
        c_s: Sound speed at the horizon.
        v_gradient: Gradient of the background flow velocity dv/dx at the horizon.

    Returns:
        δ^(2)(ω) — the frequency-dependent second-order correction.

    Note:
        The total effective temperature through second order is:
            T_eff(ω) = T_H · [1 + δ_diss + δ^(2)(ω) + ...]
        where δ_diss is the constant first-order correction.
    """
    # Natural length and momentum scales
    xi = c_s / kappa  # healing-length-like scale at the horizon

    # Dimensionless frequency
    omega_bar = omega * xi / c_s  # = ω / κ

    # Dimensionless flow gradient
    v_bar = v_gradient * xi / c_s  # = v' / κ (typically ~ 1 at the horizon)

    # Second-order correction from the two transport coefficients
    delta_cubic = coeffs.second.gamma_2_1 * omega_bar**3 / kappa
    delta_mixed = coeffs.second.gamma_2_2 * omega_bar**2 * v_bar / kappa

    return delta_cubic + delta_mixed


def effective_temperature(
    omega: float | np.ndarray,
    coeffs: FullCoeffs,
    kappa: float,
    c_s: float,
    v_gradient: float,
) -> float | np.ndarray:
    """Full effective Hawking temperature through second order.

    T_eff(ω) = T_H · [1 + δ_diss + δ^(2)(ω)]

    Args:
        omega: Mode frequency (or array).
        coeffs: Full transport coefficients through second order.
        kappa: Surface gravity.
        c_s: Sound speed at horizon.
        v_gradient: Flow velocity gradient at horizon.

    Returns:
        T_eff(ω) for each frequency.
    """
    T_H = kappa / (2 * np.pi)

    # First-order correction (constant)
    delta_1 = hawking_correction_first_order(
        coeffs.first.gamma_1, coeffs.first.gamma_2, kappa, c_s)

    # Second-order correction (frequency-dependent)
    delta_2 = hawking_correction_second_order(
        omega, coeffs, kappa, c_s, v_gradient)

    return T_H * (1 + delta_1 + delta_2)


# ═══════════════════════════════════════════════════════════════════
# Spectral distortion analysis
# ═══════════════════════════════════════════════════════════════════

def planck_spectrum(omega: np.ndarray, T: float) -> np.ndarray:
    """Planck (Bose-Einstein) spectrum at temperature T.

    n(ω) = 1 / (exp(ω/T) - 1)

    Args:
        omega: Frequency array (positive values).
        T: Temperature.

    Returns:
        Occupation number at each frequency.
    """
    x = omega / T
    return 1.0 / (np.exp(x) - 1.0)


def spectral_distortion(
    omega: np.ndarray,
    coeffs: FullCoeffs,
    kappa: float,
    c_s: float,
    v_gradient: float,
) -> np.ndarray:
    """Compute the spectral distortion relative to a perfect Planck spectrum.

    The distortion is defined as:
        Δn(ω) / n_Planck(ω) = [n_actual(ω) - n_Planck(ω, T_H)] / n_Planck(ω, T_H)

    At first order, this is approximately constant (~ δ_diss · ω/T_H).
    At second order, the ω-dependence of δ^(2)(ω) creates a frequency-dependent
    distortion that deviates from the constant first-order shift.

    This is the key observable: a measurement of the Hawking spectrum shape
    that goes beyond just measuring T_eff.

    Args:
        omega: Frequency array (positive values, in units where ℏ = 1).
        coeffs: Full transport coefficients.
        kappa: Surface gravity.
        c_s: Sound speed at horizon.
        v_gradient: Flow velocity gradient at horizon.

    Returns:
        Relative spectral distortion array.
    """
    T_H = kappa / (2 * np.pi)
    T_eff = effective_temperature(omega, coeffs, kappa, c_s, v_gradient)

    n_planck = planck_spectrum(omega, T_H)
    n_actual = planck_spectrum(omega, T_eff)

    return (n_actual - n_planck) / n_planck


# ═══════════════════════════════════════════════════════════════════
# Experimental parameter sets (extending Phase 1)
# ═══════════════════════════════════════════════════════════════════

def estimate_second_order_coeffs_beliaev(
    n: float,
    a_s: float,
    m: float,
    c_s: float,
    kappa: float,
) -> SecondOrderCoeffs:
    """Estimate second-order transport coefficients from Beliaev damping theory.

    The first-order coefficients are related to the Beliaev damping rate:
        γ_Bel = √(n·a_s³) · κ² / c_s

    At second order, dimensional analysis and the derivative structure give:
        γ_{2,1} ~ γ_Bel · (ξ/c_s)  [one extra ∂_x → one power of 1/c_s]
        γ_{2,2} ~ γ_Bel · (ξ/c_s)  [one extra ∂_t∂_x → similar scaling]

    where ξ = ℏ/(m·c_s) is the healing length.

    CAVEAT: These are order-of-magnitude estimates. The exact numerical
    prefactors require a microscopic UV matching calculation (Bogoliubov theory
    → SK-EFT coefficients). This is a direction for future work.

    Args:
        n: Condensate density (1/length in 1D, 1/length³ in 3D).
        a_s: s-wave scattering length.
        m: Atomic mass.
        c_s: Sound speed.
        kappa: Surface gravity.

    Returns:
        Estimated second-order coefficients.
    """
    import scipy.constants as const

    hbar = const.hbar
    xi = hbar / (m * c_s)  # healing length

    # Beliaev damping rate
    gas_param = n * a_s**3  # dimensionless gas parameter (1D analog)
    gamma_bel = np.sqrt(gas_param) * kappa**2 / c_s

    # Second-order coefficients (dimensional estimate)
    # Extra derivative → extra factor of ξ/c_s ~ 1/Λ_UV
    suppression = xi / c_s  # ~ 1/Λ_UV, the EFT expansion parameter

    gamma_2_1 = gamma_bel * suppression  # order-of-magnitude
    gamma_2_2 = gamma_bel * suppression  # order-of-magnitude

    return SecondOrderCoeffs(gamma_2_1=gamma_2_1, gamma_2_2=gamma_2_2)
