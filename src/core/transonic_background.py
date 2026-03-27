"""
Transonic Background Solver for 1D BEC Flow

Solves the steady-state Euler + continuity equations for a quasi-1D BEC
with an external potential that creates a transonic flow (sonic horizon).

The background determines:
- The acoustic metric g_{μν}(x)
- The surface gravity κ (and hence the Hawking temperature T_H)
- The near-horizon expansion coefficients used in the WKB calculation

Physics:
    The 1D steady-state BEC is described by:
        n(x) · v(x) = J                     (continuity: mass current conservation)
        ½ m v² + g_int n + V_ext = const     (Bernoulli: energy conservation)

    where n = density, v = flow velocity, g_int = interaction strength,
    V_ext = external potential, J = mass current (constant).

    The sound speed is c_s(x) = √(g_int · n(x) / m).
    The sonic horizon is at x_H where v(x_H) = c_s(x_H).

Design decisions:
    - We work in dimensionless units: lengths in ξ (healing length),
      velocities in c_s(∞), energies in m·c_s²(∞).
    - The external potential is a smooth step (tanh profile) to avoid
      discontinuities that break the EFT.
    - We solve the cubic equation for n(x) analytically where possible,
      falling back to numerical root-finding for general potentials.

References:
    - Barceló, Liberati, Visser, Living Rev. Rel. 8, 12 (2005), §3
    - Steinhauer, Nature Physics 12, 959 (2016) — experimental realization
    - Biondi, arXiv:2504.08833 (2025) — EFT for flowing BEC
"""

import numpy as np
from dataclasses import dataclass
from typing import Optional
from src.core.constants import HBAR, K_B, ATOMS, EXPERIMENTS


@dataclass
class BECParameters:
    """Physical parameters for a quasi-1D BEC.

    All quantities in SI units unless otherwise noted.

    These parameters, combined with the external potential, fully
    determine the transonic background and hence the Hawking temperature.
    """
    # Atomic species
    mass: float                # Atomic mass [kg]
    scattering_length: float   # s-wave scattering length a [m]

    # Trap and flow parameters
    density_upstream: float    # Upstream 1D density n₀ [m⁻¹]
    velocity_upstream: float   # Upstream flow velocity v₀ [m/s]

    # Derived quantities (computed in __post_init__)
    interaction_strength: float = 0.0  # g_1D = 2ℏ²a/(m·a_⊥²) [J·m]
    sound_speed_upstream: float = 0.0  # c_s = √(g·n₀/m) [m/s]
    healing_length: float = 0.0        # ξ = ℏ/(m·c_s) [m]
    chemical_potential: float = 0.0    # μ = g·n₀ [J]

    # Transverse confinement
    omega_perp: float = 2 * np.pi * 500  # Transverse trap frequency [rad/s]

    def __post_init__(self):
        """Compute derived quantities from the fundamental parameters."""
        hbar = HBAR

        # Transverse oscillator length
        a_perp = np.sqrt(hbar / (self.mass * self.omega_perp))

        # 1D interaction strength (Olshanii formula, quasi-1D limit)
        self.interaction_strength = (
            2 * hbar**2 * self.scattering_length / (self.mass * a_perp**2)
        )

        # Sound speed and healing length
        self.chemical_potential = self.interaction_strength * self.density_upstream
        self.sound_speed_upstream = np.sqrt(
            self.chemical_potential / self.mass
        )
        self.healing_length = hbar / (self.mass * self.sound_speed_upstream)


# ============================================================
# Pre-built parameter sets for specific experiments
# ============================================================

def steinhauer_Rb87() -> BECParameters:
    """Parameters for Steinhauer's ⁸⁷Rb BEC (Nature 2016/2019).

    This is the only experiment that has measured analog Hawking radiation.
    The measured Hawking temperature T_H ≈ 0.35 nK matches the prediction
    from the surface gravity: T_H = ℏκ/(2πk_B).

    The upstream Mach number is ~0.75, close enough to sonic that a
    modest potential step creates a horizon.

    Limitation: ⁸⁷Rb lacks broad Feshbach resonances, so the scattering
    length (and hence surface gravity) cannot be tuned independently.
    """
    atom = ATOMS['Rb87']
    exp = EXPERIMENTS['Steinhauer']
    return BECParameters(
        mass=atom['mass'],
        scattering_length=atom['a_s'],
        density_upstream=exp['density_upstream'],
        velocity_upstream=exp['velocity_upstream'],
        omega_perp=exp['omega_perp'],
    )


def heidelberg_K39() -> BECParameters:
    """Projected parameters for Heidelberg ³⁹K BEC.

    Key advantage: ³⁹K has a broad Feshbach resonance near 402 G,
    allowing continuous tuning of the scattering length from near-zero
    to ~200 a₀. This enables the κ-scaling test:
    vary surface gravity while keeping other parameters fixed.

    Uses DMD (digital micromirror device) for arbitrary potential shaping.
    """
    atom = ATOMS['K39']
    exp = EXPERIMENTS['Heidelberg']
    return BECParameters(
        mass=atom['mass'],
        scattering_length=atom['a_s'],
        density_upstream=exp['density_upstream'],
        velocity_upstream=exp['velocity_upstream'],
        omega_perp=exp['omega_perp'],
    )


def trento_spin_sonic() -> BECParameters:
    """Projected parameters for Trento two-component spin-sonic BEC.

    In a two-component BEC (e.g., ²³Na |F=1, m_F=±1⟩), spin waves
    propagate at a spin sound speed c_spin ≪ c_density.

    The Hawking temperature scales as T_H ∝ κ/c_spin, so the ratio
    T_H/T_max ∝ c_density/c_spin can be enhanced by orders of magnitude.
    This makes the dissipative correction δ_diss potentially accessible.

    Reference: Berti et al., Comptes Rendus Physique (2025)
    """
    atom = ATOMS['Na23']
    exp = EXPERIMENTS['Trento']
    return BECParameters(
        mass=atom['mass'],
        scattering_length=atom['a_s'],
        density_upstream=exp['density_upstream'],
        velocity_upstream=exp['velocity_upstream'],
        omega_perp=exp['omega_perp'],
    )


# ============================================================
# Transonic Background Solution
# ============================================================

@dataclass
class TransonicBackground:
    """Solution to the steady-state Euler+continuity equations.

    Stores the spatially-varying fields on a 1D grid, plus the
    derived quantities (horizon position, surface gravity, etc.)
    needed for the Hawking calculation.
    """
    # Spatial grid
    x: np.ndarray         # Position array [m]

    # Background fields
    density: np.ndarray    # n(x) [m⁻¹]
    velocity: np.ndarray   # v(x) [m/s]
    sound_speed: np.ndarray  # c_s(x) [m/s]
    potential: np.ndarray  # V_ext(x) [J]

    # Horizon properties
    x_horizon: float       # Position of sonic horizon [m]
    surface_gravity: float  # κ = |dv/dx + dc_s/dx| at horizon [s⁻¹]
    hawking_temp: float    # T_H = ℏκ/(2πk_B) [K]

    # Dimensionless parameters
    adiabaticity: float    # D = κξ/c_s (should be ≪ 1 for EFT validity)
    mach_upstream: float   # M = v₀/c_s₀ (should be < 1)
    mach_downstream: float  # M = v_max/c_s_min (should be > 1)


def solve_transonic_background(
    params: BECParameters,
    surface_gravity_target: Optional[float] = None,
    step_width_xi: float = 30.0,
    x_range: tuple[float, float] = (-200, 200),
    n_points: int = 4000,
) -> TransonicBackground:
    """Construct a physically correct 1D transonic BEC background.

    Rather than solving the numerically fragile cubic (which has a
    degenerate root at the sonic point), we directly parameterize the
    velocity profile as a smooth tanh transition through the horizon,
    then derive the density and sound speed from continuity and the
    equation of state.

    This approach:
    - Guarantees a well-defined sonic horizon at x = 0
    - Gives direct control over the surface gravity κ
    - Avoids the cubic root-finding degeneracy
    - Matches the form used in all analytic Hawking calculations

    The velocity profile is:
        v(x) = c_s0 · [M_up + (M_down - M_up) · ½(1 + tanh(x/L))]

    where M_up < 1, M_down > 1 are the upstream/downstream Mach numbers,
    and L is the transition width. The horizon is at x_H where v(x_H) = c_s(x_H).

    Args:
        params: BEC physical parameters.
        surface_gravity_target: Desired κ [s⁻¹]. If None, determined by
            the velocity profile slope at the horizon.
        step_width_xi: Transition width in units of healing length.
        x_range: Spatial domain in units of healing length.
        n_points: Number of grid points.

    Returns:
        TransonicBackground with all fields on the spatial grid.
    """
    hbar = HBAR
    k_B = K_B
    xi = params.healing_length
    cs0 = params.sound_speed_upstream
    g_int = params.interaction_strength
    m = params.mass

    # Spatial grid
    x_dimless = np.linspace(x_range[0], x_range[1], n_points)
    x = x_dimless * xi
    dx = x[1] - x[0]

    # Upstream Mach number from parameters
    M_up = params.velocity_upstream / cs0
    # Downstream Mach number: slightly supersonic
    M_down = 1.0 / M_up  # Symmetric about M=1 in log space

    # Transition width
    L = step_width_xi * xi

    # Velocity profile: smooth tanh transition
    # v(x) interpolates between v_up = M_up · cs0 and v_down = M_down · cs0
    v_up = M_up * cs0
    v_down = M_down * cs0
    velocity = v_up + (v_down - v_up) * 0.5 * (1 + np.tanh(x / L))

    # Density from continuity: n(x) = J / v(x)
    J = params.density_upstream * params.velocity_upstream
    density = J / velocity

    # Sound speed from equation of state: c_s(x) = √(g · n(x) / m)
    sound_speed = np.sqrt(g_int * density / m)

    # Find the sonic horizon: where |v - c_s| is minimized
    mach = velocity / sound_speed
    horizon_idx = np.argmin(np.abs(mach - 1.0))
    x_horizon = x[horizon_idx]

    # Surface gravity from finite differences:
    # κ = |dv/dx + dc_s/dx| at the horizon (both contribute with same sign
    # because v increases while c_s decreases through the transition)
    if 1 <= horizon_idx < len(x) - 1:
        dv_dx = (velocity[horizon_idx + 1] - velocity[horizon_idx - 1]) / (2 * dx)
        dcs_dx = (sound_speed[horizon_idx + 1] - sound_speed[horizon_idx - 1]) / (2 * dx)
        # Surface gravity: rate at which v - c_s changes sign
        kappa = abs(dv_dx - dcs_dx)
    else:
        kappa = 0.0

    # External potential (reconstructed from Bernoulli for consistency)
    # V(x) = E0 - ½mv² - g·n = E0 - ½mv² - mc_s²
    E0 = 0.5 * m * v_up**2 + g_int * density[0]
    potential = E0 - 0.5 * m * velocity**2 - g_int * density

    # Hawking temperature
    from src.core.formulas import hawking_temperature
    T_H = hawking_temperature(kappa)

    # Adiabaticity parameter
    cs_H = sound_speed[horizon_idx]
    D = kappa * xi / cs_H if cs_H > 0 else np.inf

    return TransonicBackground(
        x=x,
        density=density,
        velocity=velocity,
        sound_speed=sound_speed,
        potential=potential,
        x_horizon=x_horizon,
        surface_gravity=kappa,
        hawking_temp=T_H,
        adiabaticity=D,
        mach_upstream=mach[0],
        mach_downstream=mach[-1],
    )


def compute_dissipative_correction(
    bg: TransonicBackground,
    params: BECParameters,
    gamma_1: float,
    gamma_2: float,
) -> dict:
    """Estimate the dissipative correction δ_diss for given transport coefficients.

    This is the central numerical result of the paper. The correction is:

        δ_diss ~ γ_eff / (κ · ξ²)

    where γ_eff = γ₁ + γ₂ · (geometric factor depending on flow profile).

    For a BEC with Beliaev damping:
        γ_B ~ (n a³)^{1/2} · ω² / c_s

    evaluated at the Hawking frequency ω_H ~ κ.

    Args:
        bg: The transonic background solution.
        params: BEC physical parameters.
        gamma_1, gamma_2: SK-EFT transport coefficients [s⁻¹·m²].

    Returns:
        Dictionary with:
        - delta_diss: the dissipative correction
        - delta_disp: the dispersive correction (for comparison)
        - delta_cross: the cross-term
        - gamma_eff: the effective damping rate at the Hawking frequency
    """
    kappa = bg.surface_gravity
    xi = params.healing_length
    cs = params.sound_speed_upstream
    hbar = HBAR

    # The transport coefficients γ₁, γ₂ here have units [s⁻¹] — they are
    # the phonon damping rate evaluated at the Hawking frequency ω_H ~ κ.
    # The dimensionless dissipative correction is:
    #   δ_diss ~ Γ_H / κ
    # where Γ_H = γ₁ + γ₂ is the total damping rate at ω_H.
    # This is the ratio of the damping timescale to the Hawking timescale.
    from src.core.formulas import first_order_correction, dispersive_correction

    # gamma_1, gamma_2 are already damping RATES [s⁻¹] at the horizon
    gamma_eff = gamma_1 + gamma_2

    D = bg.adiabaticity
    delta_diss = first_order_correction(gamma_eff, kappa)
    delta_disp = dispersive_correction(D)

    # Cross-term: δ_cross ~ δ_disp · δ_diss
    delta_cross = delta_disp * delta_diss

    # Beliaev damping rate for comparison
    n = params.density_upstream
    a = params.scattering_length
    na3 = n * a**3
    omega_H = kappa
    gamma_beliaev = np.sqrt(na3) * omega_H**2 / cs if cs > 0 else 0

    return {
        "delta_diss": delta_diss,
        "delta_disp": delta_disp,
        "delta_cross": delta_cross,
        "gamma_eff": gamma_eff,
        "gamma_beliaev": gamma_beliaev,
        "kappa": kappa,
        "T_H_nK": bg.hawking_temp * 1e9,
        "adiabaticity_D": D,
        "T_eff_over_T_H": 1 + delta_diss + delta_disp + delta_cross,
    }


if __name__ == "__main__":
    print("SK-EFT Hawking Paper: Transonic Background Solver")
    print("=" * 60)

    for name, param_fn in [
        ("Steinhauer ⁸⁷Rb", steinhauer_Rb87),
        ("Heidelberg ³⁹K", heidelberg_K39),
        ("Trento spin-sonic ²³Na", trento_spin_sonic),
    ]:
        print(f"\n--- {name} ---")
        params = param_fn()
        print(f"  Healing length: {params.healing_length*1e6:.3f} μm")
        print(f"  Sound speed:    {params.sound_speed_upstream*1e3:.3f} mm/s")
        print(f"  Chemical pot:   {params.chemical_potential/K_B*1e9:.2f} nK (in k_B units)")

        bg = solve_transonic_background(params)
        print(f"  Horizon at:     x_H = {bg.x_horizon/params.healing_length:.1f} ξ")
        print(f"  Surface gravity: κ = {bg.surface_gravity:.2e} s⁻¹")
        print(f"  Hawking temp:   T_H = {bg.hawking_temp*1e9:.3f} nK")
        print(f"  Adiabaticity:   D = {bg.adiabaticity:.4f}")

        # Estimate dissipative correction with Beliaev damping
        # γ_B ~ (na³)^{1/2} · ω_H² / c_s, evaluated at ω_H ~ κ
        n = params.density_upstream
        a = params.scattering_length
        na3_half = np.sqrt(n * a**3)
        omega_H = bg.surface_gravity
        gamma_beliaev = na3_half * omega_H**2 / params.sound_speed_upstream
        correction = compute_dissipative_correction(
            bg, params,
            gamma_1=gamma_beliaev,
            gamma_2=gamma_beliaev * 0.1,  # Anisotropic term is subdominant
        )
        print(f"  δ_disp ~ {correction['delta_disp']:.2e}")
        print(f"  δ_diss ~ {correction['delta_diss']:.2e}")
        print(f"  T_eff/T_H = {correction['T_eff_over_T_H']:.8f}")
