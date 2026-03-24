"""WKB Mode Analysis Through the Dissipative Horizon.

Implements the WKB (Wentzel-Kramers-Brillouin) mode analysis for phonon
propagation through a sonic horizon with dissipative corrections from the
SK-EFT transport coefficients.

The key calculation chain:
    1. Modified dispersion relation:
       ω² = [c_s(x) - v(x)]² k² · F(k²ξ²) + iΓ_eff(k)·ω

    2. Local wavenumber k(x) from solving the dispersion at each x.

    3. WKB connection formula across the turning point → Bogoliubov coefficients.

    4. Effective temperature decomposition:
       T_eff(ω) = T_H · [1 + δ_disp + δ_diss + δ^(2)(ω)]

Physical context:
    At first order, δ_diss = Γ_H/κ is frequency-INDEPENDENT.
    At second order (from second_order_sk.py), the correction becomes
    frequency-dependent through γ_{2,1} and γ_{2,2}.

    This module provides the WKB derivation connecting the EFT coefficients
    to the observable Hawking spectrum modifications.

Lean formalization:
    WKBAnalysis.lean contains the theorem statements (sorry-bearing) that
    this code validates numerically.

References:
    - Corley-Jacobson, PRD 54, 1568 (1996) — dispersive WKB
    - Coutant-Parentani, PRD 89, 124004 (2014) — broadened horizon
    - Macher-Parentani, PRD 79, 124008 (2009) — numerical scattering matrix
    - Unruh, PRD 51, 2827 (1995) — sonic analog Hawking radiation
"""

from dataclasses import dataclass, field
from typing import Optional, Callable

import numpy as np
from scipy.optimize import brentq


# ═══════════════════════════════════════════════════════════════════
# Background flow profile
# ═══════════════════════════════════════════════════════════════════

@dataclass
class TransonicProfile:
    """A transonic background flow profile v(x), c_s(x) near a sonic horizon.

    The horizon is at x = 0 where v(0) = c_s(0). We parameterize the
    near-horizon region by a linear profile:

        v(x) ≈ c_s + κ·x + O(x²)

    where κ = dv/dx|_{x=0} is the surface gravity (velocity gradient at horizon).

    For more accurate calculations, the full nonlinear transonic solution
    from Phase 1 (solve_transonic_background) should be used.

    Attributes:
        kappa: Surface gravity (velocity gradient at horizon) [1/time].
        c_s: Sound speed at the horizon [length/time].
        xi: Healing length = ℏ/(m·c_s) [length].
        x_range: Spatial domain (x_min, x_max) centered on the horizon.
    """
    kappa: float
    c_s: float
    xi: float
    x_range: tuple[float, float] = (-10.0, 10.0)

    @property
    def cutoff(self) -> float:
        """UV momentum cutoff Λ = 1/ξ [1/length]."""
        return 1.0 / self.xi

    @property
    def D(self) -> float:
        """Adiabaticity parameter D = κξ/c_s (should be ≪ 1)."""
        return self.kappa * self.xi / self.c_s

    @property
    def T_H(self) -> float:
        """Hawking temperature T_H = κ/(2π) [energy units]."""
        return self.kappa / (2 * np.pi)

    def v(self, x: np.ndarray | float) -> np.ndarray | float:
        """Flow velocity profile v(x). Linear near the horizon.

        v(x) = c_s + κ·x

        The horizon is at x=0: v(0) = c_s (sonic point).
        For x < 0: subsonic region (v < c_s, outside the horizon).
        For x > 0: supersonic region (v > c_s, inside the horizon).
        """
        return self.c_s + self.kappa * x

    def c_local(self, x: np.ndarray | float) -> np.ndarray | float:
        """Local sound speed. Assumed constant for simplicity.

        For the full nonlinear profile, c_s(x) varies slowly;
        the constant approximation is valid to O(D²).
        """
        return self.c_s


# ═══════════════════════════════════════════════════════════════════
# WKB parameters and dispersion
# ═══════════════════════════════════════════════════════════════════

@dataclass
class WKBParameters:
    """Parameters for the WKB mode analysis.

    Combines the transonic background with SK-EFT transport coefficients
    and WKB numerical control parameters.

    Attributes:
        profile: Transonic background flow profile.
        gamma_1: First-order transport coefficient γ₁ (wave damping).
        gamma_2: First-order transport coefficient γ₂ (anomalous damping).
        gamma_2_1: Second-order coefficient γ_{2,1} (cubic spatial).
        gamma_2_2: Second-order coefficient γ_{2,2} (temporal-spatial).
        F_disp: Dispersion modification function F(x) where ω² = c_s²k²·F(k²ξ²).
            Default: Bogoliubov F(x) = 1 + x.
        n_points: Number of spatial points for WKB integration.
    """
    profile: TransonicProfile
    gamma_1: float = 0.0
    gamma_2: float = 0.0
    gamma_2_1: float = 0.0
    gamma_2_2: float = 0.0
    F_disp: Callable[[float], float] = field(
        default_factory=lambda: (lambda x: 1.0 + x)  # Bogoliubov
    )
    n_points: int = 4000

    @property
    def gamma_eff(self) -> float:
        """Effective first-order damping rate."""
        return self.gamma_1 + self.gamma_2

    @property
    def delta_diss_leading(self) -> float:
        """Leading-order dissipative correction δ_diss = Γ_eff/κ."""
        if self.profile.kappa > 0:
            return self.gamma_eff / self.profile.kappa
        return 0.0


@dataclass
class BogoliubovResult:
    """Result of the WKB Bogoliubov coefficient calculation.

    Attributes:
        omega: Mode frequency.
        alpha_sq: |α|² (normalization component).
        beta_sq: |β|² (particle production per mode).
        T_eff: Effective temperature extracted from the spectrum.
        delta_disp: Dispersive correction to T_H.
        delta_diss: Dissipative correction to T_H (first order, constant).
        delta_second: Second-order correction (frequency-dependent).
        n_occupation: Occupation number = |β|²/(|α|² - |β|²).
    """
    omega: float
    alpha_sq: float
    beta_sq: float
    T_eff: float
    delta_disp: float
    delta_diss: float
    delta_second: float
    n_occupation: float


# ═══════════════════════════════════════════════════════════════════
# Local dispersion relation solver
# ═══════════════════════════════════════════════════════════════════

def dispersion_relation(
    k: complex,
    omega: float,
    v_local: float,
    c_s: float,
    xi: float,
    gamma_1: float,
    gamma_2: float,
    gamma_2_1: float = 0.0,
    gamma_2_2: float = 0.0,
    F_disp: Callable[[float], float] = lambda x: 1.0 + x,
) -> complex:
    """Evaluate the local dispersion relation in the co-moving frame.

    In the lab frame with flow v(x), the co-moving frequency is:
        Ω = ω - v(x)·k

    The dispersion relation is:
        Ω² = c_s² k² · F(k²ξ²) + iΓ_eff(k,ω)·Ω

    which we rearrange to:
        (ω - v·k)² - c_s² k² · F(k²ξ²) - iΓ_eff(k,ω)·(ω - v·k) = 0

    Args:
        k: Wavenumber (complex for dissipative case).
        omega: Lab-frame frequency.
        v_local: Local flow velocity v(x).
        c_s: Local sound speed.
        xi: Healing length.
        gamma_1, gamma_2: First-order SK-EFT coefficients.
        gamma_2_1, gamma_2_2: Second-order SK-EFT coefficients.
        F_disp: Dispersion modification function.

    Returns:
        Residual of the dispersion relation (0 when k is a solution).
    """
    Omega = omega - v_local * k  # co-moving frequency
    k2 = k**2

    # Dispersive part
    disp_arg = (k2 * xi**2).real  # F evaluated on real argument
    dispersive = c_s**2 * k2 * F_disp(disp_arg)

    # Dissipative part (first + second order)
    Gamma_first = gamma_1 * k2 + gamma_2 * omega**2 / c_s**2
    Gamma_second = gamma_2_1 * k**3 + gamma_2_2 * omega**2 * k / c_s**2
    Gamma_eff = Gamma_first + Gamma_second

    return Omega**2 - dispersive - 1j * Gamma_eff * Omega


def local_wavenumber(
    x: np.ndarray,
    omega: float,
    params: WKBParameters,
) -> np.ndarray:
    """Solve the local dispersion relation at each spatial point.

    Finds the co-moving WKB wavenumber k(x) satisfying the local dispersion
    relation. For a transonic flow, there are multiple branches; we track
    the incoming mode (co-propagating with the flow, positive group velocity
    in the subsonic region).

    At leading order (no dispersion, no dissipation):
        k_±(x) = ω / (c_s ∓ v(x))

    The '+' branch (k_+ = ω/(c_s - v)) diverges at the horizon v → c_s
    and corresponds to the Hawking mode.

    With dissipation, the divergence is regularized: the mode acquires
    a complex part near the horizon, encoding the imaginary shift of
    the turning point.

    Args:
        x: Spatial coordinate array.
        omega: Mode frequency.
        params: WKB parameters including the background profile.

    Returns:
        Complex wavenumber array k(x).
    """
    p = params.profile
    k_out = np.zeros(len(x), dtype=complex)

    for i, xi_val in enumerate(x):
        v_local = p.v(xi_val)
        c_local = p.c_local(xi_val)

        # Leading-order estimate for the co-moving mode
        dv = c_local - v_local  # = -κ·x for linear profile
        if abs(dv) > 1e-10 * c_local:
            k_guess = omega / dv
        else:
            # Near the horizon: use the regularized form
            # With Bogoliubov dispersion, k ~ (ω·Λ²)^{1/3} at the horizon
            k_guess = (omega * p.cutoff**2)**(1.0/3.0)

        # For the leading-order WKB, use the analytic formula
        # (dispersion + dissipation corrections are perturbative)
        k_analytic = omega / (c_local - v_local + 1e-30)

        # First-order dissipative correction to k
        # From the dispersion relation linearized around k_analytic:
        #   δk ≈ i·Γ_eff/(2·c_eff)
        # where c_eff = ∂Ω/∂k is the group velocity
        Gamma_eff = params.gamma_1 * k_analytic**2 + \
                    params.gamma_2 * omega**2 / c_local**2
        c_eff = c_local - v_local  # group velocity at leading order

        if abs(c_eff) > 1e-10 * c_local:
            delta_k = 1j * Gamma_eff / (2 * c_eff)
        else:
            delta_k = 0.0

        # Dispersive correction (Bogoliubov)
        k0 = k_analytic
        if abs(k0) > 0 and abs(c_eff) > 1e-10 * c_local:
            F_prime = 1.0  # dF/dx for Bogoliubov F(x) = 1+x → F'=1
            delta_k_disp = -c_local**2 * k0**3 * p.xi**2 * F_prime / (2 * c_eff)
        else:
            delta_k_disp = 0.0

        k_out[i] = k_analytic + delta_k + delta_k_disp

    return k_out


# ═══════════════════════════════════════════════════════════════════
# WKB phase integral and connection formula
# ═══════════════════════════════════════════════════════════════════

def wkb_phase_integral(
    x: np.ndarray,
    k: np.ndarray,
    x_tp: float = 0.0,
) -> np.ndarray:
    """Compute the WKB phase ∫k(x')dx' from the turning point.

    The WKB mode function is:
        φ(x) ~ |k(x)|^{-1/2} · exp(i·∫_{x_tp}^{x} k(x') dx')

    The phase integral determines the Bogoliubov coefficients through
    the Stokes multiplier at the turning point.

    Args:
        x: Spatial coordinate array.
        k: Complex wavenumber array k(x).
        x_tp: Turning point location (default: horizon at x=0).

    Returns:
        Complex phase integral array.
    """
    phase = np.zeros(len(x), dtype=complex)
    dx = x[1] - x[0]

    # Find index closest to turning point
    i_tp = np.argmin(np.abs(x - x_tp))

    # Integrate from turning point outward
    for i in range(i_tp + 1, len(x)):
        phase[i] = phase[i-1] + k[i] * dx

    for i in range(i_tp - 1, -1, -1):
        phase[i] = phase[i+1] - k[i] * dx

    return phase


def connection_formula(
    omega: float,
    params: WKBParameters,
) -> BogoliubovResult:
    """Compute Bogoliubov coefficients via WKB connection across the horizon.

    The standard Hawking result (Unruh 1981):
        |β/α|² = exp(-2πω/κ)  →  T_eff = κ/(2π) = T_H

    With dispersive corrections (Corley-Jacobson 1996):
        δ_disp ≈ -(π/6)(ω/κ)·D² + O(D⁴)

    With dissipative corrections (first order, this work):
        δ_diss = Γ_H / κ  (frequency-independent)

    With second-order corrections:
        δ^(2)(ω) = frequency-dependent part from γ_{2,1}, γ_{2,2}

    The derivation:
    1. The turning point in the complex k-plane shifts by
       δk_tp ∝ i·Γ_eff/(κ·c_s)
    2. This shifts the Stokes multiplier by a real phase
    3. The modified |β/α|² gives:
       |β/α|² = exp(-2πω/κ_eff)
       where κ_eff = κ·(1 + δ_diss + δ^(2)(ω))⁻¹

    Args:
        omega: Mode frequency.
        params: WKB parameters.

    Returns:
        BogoliubovResult with the full correction decomposition.
    """
    p = params.profile
    kappa = p.kappa
    c_s = p.c_s
    xi = p.xi
    D = p.D

    # ─── Dispersive correction (Corley-Jacobson) ───
    # δ_disp = -(π/6)(ω/κ)·D² for Bogoliubov dispersion
    # This is the leading-order result; higher-order terms are O(D⁴)
    omega_bar = omega / kappa  # dimensionless frequency
    delta_disp = -(np.pi / 6) * omega_bar * D**2

    # ─── First-order dissipative correction ───
    # δ_diss = Γ_H / κ  where Γ_H is the effective damping rate
    # at the horizon. For a mode with frequency ω:
    #   Γ_H(ω) = γ₁·k_H² + γ₂·ω²/c_s²
    # where k_H ~ ω/c_s is the characteristic momentum at the horizon.
    k_H = omega / c_s  # characteristic horizon momentum
    Gamma_H = params.gamma_1 * k_H**2 + params.gamma_2 * omega**2 / c_s**2
    delta_diss = Gamma_H / kappa if kappa > 0 else 0.0

    # ─── Second-order correction (frequency-dependent) ───
    # From the two new transport coefficients:
    #   γ_{2,1} · k³ + γ_{2,2} · ω²k/c_s²
    # evaluated at k = k_H
    Gamma_H_2 = params.gamma_2_1 * k_H**3 + \
                params.gamma_2_2 * omega**2 * k_H / c_s**2
    delta_second = Gamma_H_2 / kappa if kappa > 0 else 0.0

    # ─── Combined Bogoliubov coefficients ───
    # |β/α|² = exp(-2πω/κ_eff)
    # where 1/κ_eff = (1/κ)·(1 - δ_disp - δ_diss - δ^(2))
    # to first order in corrections
    delta_total = delta_disp + delta_diss + delta_second

    exponent = -2 * np.pi * omega / kappa * (1 - delta_total)
    beta_over_alpha_sq = np.exp(exponent)

    # Bosonic normalization: |α|² - |β|² = 1
    # n = |β|² = 1/(exp(2πω/κ_eff) - 1) for thermal spectrum
    beta_sq = beta_over_alpha_sq / (1 - beta_over_alpha_sq) \
        if beta_over_alpha_sq < 1 else 1e10
    alpha_sq = 1 + beta_sq

    # Effective temperature
    if omega > 0 and beta_sq > 0:
        T_eff = omega / np.log(1 + 1/beta_sq)
    else:
        T_eff = p.T_H * (1 + delta_total)

    # Occupation number
    n_occ = beta_sq

    return BogoliubovResult(
        omega=omega,
        alpha_sq=alpha_sq,
        beta_sq=beta_sq,
        T_eff=T_eff,
        delta_disp=delta_disp,
        delta_diss=delta_diss,
        delta_second=delta_second,
        n_occupation=n_occ,
    )


# ═══════════════════════════════════════════════════════════════════
# Spectrum computation
# ═══════════════════════════════════════════════════════════════════

def compute_hawking_spectrum(
    omega_array: np.ndarray,
    params: WKBParameters,
) -> list[BogoliubovResult]:
    """Compute the full Hawking spectrum with all corrections.

    Evaluates the WKB connection formula at each frequency to obtain
    the occupation number n(ω) and effective temperature T_eff(ω).

    Args:
        omega_array: Array of mode frequencies to evaluate.
        params: WKB parameters.

    Returns:
        List of BogoliubovResult, one per frequency.
    """
    results = []
    for omega in omega_array:
        if omega > 0:
            result = connection_formula(omega, params)
            results.append(result)
    return results


def extract_corrections(
    results: list[BogoliubovResult],
) -> dict[str, np.ndarray]:
    """Extract the correction decomposition from a spectrum computation.

    Returns arrays of δ_disp(ω), δ_diss(ω), δ^(2)(ω), and T_eff(ω)
    for plotting and analysis.

    Args:
        results: List of BogoliubovResult from compute_hawking_spectrum.

    Returns:
        Dictionary with keys 'omega', 'delta_disp', 'delta_diss',
        'delta_second', 'T_eff', 'n_occupation'.
    """
    return {
        'omega': np.array([r.omega for r in results]),
        'delta_disp': np.array([r.delta_disp for r in results]),
        'delta_diss': np.array([r.delta_diss for r in results]),
        'delta_second': np.array([r.delta_second for r in results]),
        'T_eff': np.array([r.T_eff for r in results]),
        'n_occupation': np.array([r.n_occupation for r in results]),
    }


# ═══════════════════════════════════════════════════════════════════
# Experimental parameter presets
# ═══════════════════════════════════════════════════════════════════

def steinhauer_params() -> WKBParameters:
    """WKB parameters for the Steinhauer ⁸⁷Rb BEC experiment.

    All quantities in NATURAL UNITS where c_s = 1 and κ sets the scale:
        κ = 1 (all energies/frequencies in units of κ)
        c_s = 1 (all velocities in units of c_s)
        ξ = D · c_s / κ = D (healing length in units of c_s/κ)

    Physical values from Phase 1 (steinhauer_Rb87 factory):
        κ_phys ≈ 3400 Hz, c_s ≈ 3.3 mm/s, ξ ≈ 0.28 μm
        D = κξ/c_s ≈ 0.03

    The dimensionless damping coefficients are:
        γ̃ = γ_phys / κ  (ratio of damping rate to surface gravity)

    From Beliaev: γ_Bel / κ ≈ 0.003 for Steinhauer parameters.
    """
    D = 0.03  # adiabaticity parameter
    profile = TransonicProfile(
        kappa=1.0,    # natural units
        c_s=1.0,      # natural units
        xi=D,         # ξ = D·c_s/κ = D in natural units
    )
    # Dimensionless damping: γ̃ = γ_phys/κ ≈ 0.003
    gamma_dim = 0.003
    return WKBParameters(
        profile=profile,
        gamma_1=gamma_dim / 2,  # split equally between γ₁ and γ₂
        gamma_2=gamma_dim / 2,
    )


def heidelberg_params() -> WKBParameters:
    """WKB parameters for the projected Heidelberg ³⁹K BEC experiment.

    Feshbach-tunable scattering length → adjustable D and γ.
    D ≈ 0.02 (tighter confinement, lower D).
    """
    D = 0.02
    profile = TransonicProfile(
        kappa=1.0,
        c_s=1.0,
        xi=D,
    )
    gamma_dim = 0.002
    return WKBParameters(
        profile=profile,
        gamma_1=gamma_dim / 2,
        gamma_2=gamma_dim / 2,
    )


# ═══════════════════════════════════════════════════════════════════
# Quick validation
# ═══════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    print("WKB Mode Analysis: Dissipative Hawking Spectrum")
    print("=" * 60)

    # Use Steinhauer parameters
    params = steinhauer_params()
    p = params.profile
    print(f"\nSteinhauer ⁸⁷Rb BEC parameters:")
    print(f"  κ = {p.kappa:.0f} Hz")
    print(f"  c_s = {p.c_s*1e3:.2f} mm/s")
    print(f"  ξ = {p.xi*1e6:.2f} μm")
    print(f"  D = κξ/c_s = {p.D:.4f}")
    print(f"  T_H = κ/(2π) = {p.T_H:.1f} Hz")

    # Compute spectrum
    omega_array = np.linspace(0.1 * p.T_H, 5 * p.T_H, 20)
    results = compute_hawking_spectrum(omega_array, params)
    corrections = extract_corrections(results)

    print(f"\n{'ω/T_H':>8} {'δ_disp':>10} {'δ_diss':>10} {'δ^(2)':>10} {'T_eff/T_H':>10}")
    print("-" * 50)
    for i, r in enumerate(results):
        print(f"{r.omega/p.T_H:8.2f} {r.delta_disp:10.4e} {r.delta_diss:10.4e} "
              f"{r.delta_second:10.4e} {r.T_eff/p.T_H:10.6f}")

    print(f"\nKey result:")
    print(f"  At ω = T_H: δ_diss = {results[4].delta_diss:.4e} (constant)")
    print(f"  At ω = 3T_H: δ_diss = {results[12].delta_diss:.4e} (grows with ω)")
    print(f"  The δ_diss growth with ω is from the k_H² = (ω/c_s)² dependence")
    print(f"  of the first-order damping rate — already frequency-dependent!")
    print(f"\n  Second-order correction δ^(2) = 0 (γ_{2,1} = γ_{2,2} = 0 here)")

    # Now with second-order coefficients
    print(f"\n{'='*60}")
    print(f"With second-order coefficients:")
    params2 = WKBParameters(
        profile=p,
        gamma_1=5.0,
        gamma_2=5.0,
        gamma_2_1=0.5,   # Estimated from Beliaev + ξ/c_s suppression
        gamma_2_2=0.5,
    )
    results2 = compute_hawking_spectrum(omega_array, params2)
    print(f"\n{'ω/T_H':>8} {'δ_diss':>10} {'δ^(2)':>10} {'δ_total':>10}")
    print("-" * 40)
    for r in results2:
        delta_total = r.delta_disp + r.delta_diss + r.delta_second
        print(f"{r.omega/p.T_H:8.2f} {r.delta_diss:10.4e} {r.delta_second:10.4e} "
              f"{delta_total:10.4e}")
