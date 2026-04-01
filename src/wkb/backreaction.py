"""Backreaction of Hawking radiation on BEC acoustic black holes.

Acoustic black holes in BEC condensates cool as they radiate Hawking phonons,
approaching extremality (kappa -> 0) asymptotically. This is the opposite of
Schwarzschild black holes and structurally analogous to near-extremal
Reissner-Nordstrom evaporation. The conserved mass flux J = rho * v * A
plays the role of electric charge, enforcing a negative-feedback loop.

The calculation chain:
    1. Compute energy flux F_H from the exact WKB spectrum
    2. Backreaction: energy flux modifies the BEC density and sound speed
    3. Temperature evolution: T_H(t) decreases as the BH loses energy
    4. Approach to extremality: kappa(t) ~ kappa_0 * exp(-t/tau_cool)
    5. Platform-specific timescales for Steinhauer, Heidelberg, Trento

Key physics (Balbinot et al. 2005, 2025):
    - c_s = sqrt(g * n_BEC / m), so as density drops, c_s drops
    - kappa depends on the velocity gradient at the horizon,
      which weakens as the background flow is modified
    - The Hawking luminosity L_H ~ T_H^2, so cooling is self-limiting
    - Exact extremality (kappa = 0) is never reached: analog third law

References:
    - Balbinot, Fagnocchi, Fabbri, Procopio, PRL 94, 161302 (2005)
    - Balbinot, Fagnocchi, Fabbri, Procopio, PRD 71, 064019 (2005)
    - Ciliberto, Balbinot, Fabbri, Pavloff, PRA 112, 063323 (2025)
    - Balbinot, Fabbri, Ciliberto, Pavloff, PRD 112, L121703 (2025)
    - Liberati, Tricella, Trombettoni, Appl. Sci. 10, 8868 (2020)
"""

from dataclasses import dataclass, field

import numpy as np

from src.wkb.spectrum import (
    PlatformParams,
    HawkingSpectrum,
    compute_spectrum,
    planck_occupation,
    steinhauer_platform,
    heidelberg_platform,
    trento_platform,
    ALL_PLATFORMS,
)
from src.core.formulas import (
    damping_rate, decoherence_parameter, fdr_noise_floor, hawking_temperature,
)


# ═══════════════════════════════════════════════════════════════════
# Physical constants (from single source of truth)
# ═══════════════════════════════════════════════════════════════════

from src.core.constants import HBAR as _HBAR, K_B as _K_B, ATOMS


# ═══════════════════════════════════════════════════════════════════
# SI platform parameters for backreaction
# ═══════════════════════════════════════════════════════════════════

@dataclass
class SIPlatformParams:
    """Physical parameters for a BEC platform in SI units.

    These are the dimensional quantities needed for backreaction
    calculations, complementing the natural-unit PlatformParams used
    in the WKB spectrum computation.

    Attributes:
        name: Platform identifier.
        kappa_si: Surface gravity [s^-1].
        c_s_si: Sound speed [m/s].
        xi_si: Healing length [m].
        T_H_si: Hawking temperature [K].
        n_atoms: Total condensate atom number.
        n_1D: Quasi-1D linear density [m^-1].
        mass: Atomic mass [kg].
        chemical_potential: mu = g * n_1D [J].
        bec_lifetime: Experimental BEC lifetime [s].
        description: Human-readable description.
    """
    name: str
    kappa_si: float
    c_s_si: float
    xi_si: float
    T_H_si: float
    n_atoms: int
    n_1D: float
    mass: float
    chemical_potential: float
    bec_lifetime: float
    description: str = ""


def steinhauer_si() -> SIPlatformParams:
    """Steinhauer 87Rb BEC parameters in SI units.

    PROVENANCE WARNING: These SI values differ from constants.EXPERIMENTS['Steinhauer']
    which gives kappa=21.9, c_s=1.151mm/s, T_H=0.027nK via the transonic solver.
    The values here (kappa=290, T_H=0.35nK) match Steinhauer's published results
    (Nature 2019) directly, suggesting the EXPERIMENTS params may use different
    conventions (quasi-1D vs 3D density, different profile width). This discrepancy
    needs reconciliation — see Phase 5 roadmap 9C-4.

    Sources: Steinhauer, Nature 569, 688 (2019); Nature Phys. 17, 362 (2021).
    Deep research: Balbinot backreaction timescale analysis.
    """
    return SIPlatformParams(
        name="Steinhauer_Rb87",
        kappa_si=290.0,
        c_s_si=0.5e-3,
        xi_si=1.5e-6,
        T_H_si=0.35e-9,
        n_atoms=8000,
        n_1D=5e7,
        mass=ATOMS['Rb87']['mass'],
        chemical_potential=3.6e-32,
        bec_lifetime=0.1,
        description="Steinhauer 87Rb waterfall BEC (Technion)",
    )


def heidelberg_si() -> SIPlatformParams:
    """Heidelberg 39K BEC parameters in SI units.

    Sources: Viermann et al., Nature 611, 260 (2022);
    Sparn et al., PRL 133, 260201 (2024).
    Projected transonic flow parameters.
    """
    return SIPlatformParams(
        name="Heidelberg_K39",
        kappa_si=580.0,
        c_s_si=3.0e-3,
        xi_si=0.25e-6,
        T_H_si=0.70e-9,
        n_atoms=100000,
        n_1D=3e7,
        mass=ATOMS['K39']['mass'],
        chemical_potential=5.8e-32,
        bec_lifetime=1.0,
        description="Heidelberg 39K Feshbach-tunable BEC",
    )


def trento_si() -> SIPlatformParams:
    """Trento 23Na spin-sonic BEC parameters in SI units.

    Sources: Berti et al., Comptes Rendus Physique (2025).
    Projected spin-sonic transonic flow parameters.
    """
    return SIPlatformParams(
        name="Trento_Na23",
        kappa_si=200.0,
        c_s_si=1.6e-3,
        xi_si=0.8e-6,
        T_H_si=0.24e-9,
        n_atoms=500000,
        n_1D=1e8,
        mass=ATOMS['Na23']['mass'],
        chemical_potential=2.1e-32,
        bec_lifetime=5.0,
        description="Trento 23Na spin-sonic BEC proposal",
    )


ALL_SI_PLATFORMS = {
    'steinhauer': steinhauer_si,
    'heidelberg': heidelberg_si,
    'trento': trento_si,
}


# ═══════════════════════════════════════════════════════════════════
# Energy flux from the Hawking spectrum
# ═══════════════════════════════════════════════════════════════════

@dataclass
class EnergyFlux:
    """Energy flux through the acoustic horizon from Hawking emission.

    The total energy flux is decomposed into contributions:
        F_total = F_hawking + F_noise
    where F_hawking includes dispersive and dissipative corrections.

    In 1+1D for a single massless scalar field, the Stefan-Boltzmann
    luminosity is L_H = (pi/12) * (k_B * T_H)^2 / hbar. The actual
    flux from the WKB spectrum differs due to EFT corrections.

    Attributes:
        F_total: Total energy flux [W = J/s].
        F_planck: Planck spectrum flux (no corrections) [W].
        F_dispersive: Contribution from dispersive corrections [W].
        F_dissipative: Contribution from dissipative corrections [W].
        F_noise: Contribution from FDR noise floor [W].
        omega_peak: Frequency of peak energy emission [s^-1].
        L_stefan_boltzmann: 1+1D Stefan-Boltzmann luminosity [W].
    """
    F_total: float
    F_planck: float
    F_dispersive: float
    F_dissipative: float
    F_noise: float
    omega_peak: float
    L_stefan_boltzmann: float


def hawking_luminosity_1d(T_H_kelvin: float) -> float:
    """1+1D Stefan-Boltzmann luminosity for a single scalar field.

    L_H = (pi/12) * (k_B * T_H)^2 / hbar

    This is the total power emitted by a 1+1D thermal body at
    temperature T_H through a single channel.

    Args:
        T_H_kelvin: Hawking temperature [K].

    Returns:
        Luminosity [W].
    """
    if T_H_kelvin <= 0:
        return 0.0
    kT = _K_B * T_H_kelvin
    return (np.pi / 12.0) * kT**2 / _HBAR


def compute_energy_flux(
    platform: PlatformParams,
    si_params: SIPlatformParams,
    n_points: int = 100,
    omega_max_factor: float = 8.0,
) -> EnergyFlux:
    """Compute the energy flux through the acoustic horizon.

    Integrates the Hawking spectrum weighted by hbar * omega:

        F = integral d(omega) / (2*pi) * hbar * omega * n(omega)

    using the full WKB spectrum including noise floor and
    EFT corrections through third order.

    The flux is decomposed by computing:
        F_planck: from planck_occupation only
        F_total: from full n_total (including corrections and noise)
        F_dispersive: from the difference due to dispersive corrections
        F_dissipative: from the dissipative contribution
        F_noise: from the noise floor contribution

    Args:
        platform: Natural-unit platform parameters.
        si_params: SI-unit platform parameters.
        n_points: Number of frequency points for integration.
        omega_max_factor: Upper integration limit in units of T_H.

    Returns:
        EnergyFlux with all contributions.
    """
    spectrum = compute_spectrum(
        platform,
        omega_min=0.05,
        omega_max_factor=omega_max_factor,
        n_points=n_points,
    )

    T_H = platform.T_H
    kappa = platform.kappa
    kappa_si = si_params.kappa_si

    # Convert from natural units to SI:
    # In natural units, kappa = 1, so omega_natural = omega_SI / kappa_SI
    # Energy per mode: hbar * omega_SI = hbar * kappa_SI * omega_natural
    # The flux integral in natural units gives a dimensionless number
    # that must be multiplied by (hbar * kappa_SI^2) / (2*pi) to get watts.

    omega_arr = spectrum.omega_array
    d_omega = omega_arr[1] - omega_arr[0] if len(omega_arr) > 1 else 1.0

    # Integrate omega * n(omega) for various contributions
    integrand_total = np.zeros(len(omega_arr))
    integrand_planck = np.zeros(len(omega_arr))
    integrand_noise = np.zeros(len(omega_arr))

    for i, point in enumerate(spectrum.points):
        omega = point.omega
        integrand_total[i] = omega * point.n_total
        integrand_planck[i] = omega * point.n_planck
        integrand_noise[i] = omega * point.n_noise

    # Trapezoidal integration (natural units)
    I_total = np.trapezoid(integrand_total, omega_arr)
    I_planck = np.trapezoid(integrand_planck, omega_arr)
    I_noise = np.trapezoid(integrand_noise, omega_arr)

    # Convert to SI watts: F = hbar * kappa_SI^2 / (2*pi) * I_natural
    conversion = _HBAR * kappa_si**2 / (2.0 * np.pi)
    F_total = conversion * I_total
    F_planck = conversion * I_planck
    F_noise = conversion * I_noise

    # Decompose the non-Planck, non-noise contribution
    F_corrected_hawking = F_total - F_noise
    F_correction = F_corrected_hawking - F_planck

    # Estimate dispersive vs dissipative split from the corrections
    # At leading order: dispersive correction ~ delta_disp * F_planck
    # dissipative correction ~ delta_diss * F_planck
    delta_disp = spectrum.points[len(spectrum.points) // 2].delta_disp
    delta_diss = spectrum.points[len(spectrum.points) // 2].delta_diss
    delta_total = abs(delta_disp) + abs(delta_diss)

    if delta_total > 0:
        F_dispersive = F_correction * abs(delta_disp) / delta_total
        F_dissipative = F_correction * abs(delta_diss) / delta_total
    else:
        F_dispersive = 0.0
        F_dissipative = 0.0

    # Peak emission frequency
    peak_idx = int(np.argmax(integrand_total))
    omega_peak_natural = omega_arr[peak_idx]
    omega_peak_si = omega_peak_natural * kappa_si

    # Stefan-Boltzmann luminosity
    L_sb = hawking_luminosity_1d(si_params.T_H_si)

    return EnergyFlux(
        F_total=F_total,
        F_planck=F_planck,
        F_dispersive=F_dispersive,
        F_dissipative=F_dissipative,
        F_noise=F_noise,
        omega_peak=omega_peak_si,
        L_stefan_boltzmann=L_sb,
    )


# ═══════════════════════════════════════════════════════════════════
# Backreaction evolution
# ═══════════════════════════════════════════════════════════════════

@dataclass
class BackreactionEvolution:
    """Time evolution of the acoustic black hole under backreaction.

    Tracks how the BEC background parameters change as energy is
    radiated away through the Hawking process. The evolution is
    quasi-static (adiabatic): at each timestep, the Hawking spectrum
    is recomputed for the updated background.

    The key result: kappa(t) ~ kappa_0 * exp(-t/tau), corresponding
    to exponential cooling toward extremality.

    Attributes:
        times: Time array [s].
        T_H_values: Hawking temperature at each time [K].
        kappa_values: Surface gravity at each time [s^-1].
        n_BEC_values: Condensate density at each time [m^-1].
        c_s_values: Sound speed at each time [m/s].
        F_H_values: Energy flux at each time [W].
        extremality_parameter: kappa(t)/kappa(0) at each time.
        energy_radiated: Cumulative energy radiated [J].
    """
    times: np.ndarray
    T_H_values: np.ndarray
    kappa_values: np.ndarray
    n_BEC_values: np.ndarray
    c_s_values: np.ndarray
    F_H_values: np.ndarray
    extremality_parameter: np.ndarray
    energy_radiated: np.ndarray


def _sound_speed_from_density(n_1D: float, mass: float, g_int: float) -> float:
    """Compute sound speed from 1D density.

    c_s = sqrt(g_1D * n_1D / m)

    Args:
        n_1D: Quasi-1D linear density [m^-1].
        mass: Atomic mass [kg].
        g_int: 1D interaction strength [J*m].

    Returns:
        Sound speed [m/s].
    """
    if n_1D <= 0 or g_int <= 0:
        return 0.0
    return np.sqrt(g_int * n_1D / mass)


def _kappa_from_density(
    n_1D: float,
    n_1D_0: float,
    kappa_0: float,
    c_s_0: float,
    mass: float,
    g_int: float,
) -> float:
    """Compute surface gravity from modified density.

    The surface gravity depends on the velocity gradient at the
    horizon. Under backreaction, as the density changes, the sound
    speed changes as c_s = sqrt(g * n / m), and the velocity
    gradient at the horizon adjusts to maintain the conserved
    mass flux J = n * v.

    The leading-order scaling is:
        kappa / kappa_0 ~ (c_s / c_s_0)^2 ~ n / n_0

    This follows from kappa ~ (dv/dx - dc_s/dx) at the horizon,
    and both derivatives scale linearly with c_s ~ sqrt(n).

    Args:
        n_1D: Current density [m^-1].
        n_1D_0: Initial density [m^-1].
        kappa_0: Initial surface gravity [s^-1].
        c_s_0: Initial sound speed [m/s].
        mass: Atomic mass [kg].
        g_int: 1D interaction strength [J*m].

    Returns:
        Surface gravity [s^-1].
    """
    if n_1D <= 0 or n_1D_0 <= 0:
        return 0.0
    c_s = _sound_speed_from_density(n_1D, mass, g_int)
    return kappa_0 * (c_s / c_s_0) ** 2


def backreaction_evolution(
    si_params: SIPlatformParams,
    t_max: float | None = None,
    n_steps: int = 500,
) -> BackreactionEvolution:
    """Compute the quasi-static backreaction evolution.

    At each timestep:
        1. Compute the Hawking luminosity L_H ~ (k_B * T_H)^2 / hbar
        2. Energy lost per timestep: dE = L_H * dt
        3. Density change: dn = -dE / (mu * L_condensate)
           where mu is the chemical potential per atom and
           L_condensate is the condensate length
        4. Update c_s, kappa, T_H from the new density

    The quasi-static approximation is valid when tau_BR >> 1/kappa,
    which is overwhelmingly satisfied for macroscopic BECs.

    Uses the analytic approximation from Balbinot et al. (2005):
        kappa(t) ~ kappa_0 * exp(-t/tau_cool)
    but evolves the full coupled equations rather than assuming the
    exponential form.

    Args:
        si_params: SI-unit platform parameters.
        t_max: Maximum evolution time [s]. If None, uses 5 * tau_cool.
        n_steps: Number of time steps.

    Returns:
        BackreactionEvolution with the full time history.
    """
    # Initial state
    kappa_0 = si_params.kappa_si
    c_s_0 = si_params.c_s_si
    n_0 = si_params.n_1D
    mass = si_params.mass
    mu = si_params.chemical_potential
    T_H_0 = si_params.T_H_si

    # Interaction strength from chemical potential: g_int = mu / n_1D
    g_int = mu / n_0 if n_0 > 0 else 0.0

    # Condensate length scale (order of magnitude)
    # L_cond ~ N_atoms / n_1D
    N = si_params.n_atoms
    L_cond = N / n_0 if n_0 > 0 else 1.0

    # Energy per condensate atom
    E_per_atom = mu

    # Total condensate energy
    E_total = N * E_per_atom

    # Initial luminosity for timescale estimate
    L_H_0 = hawking_luminosity_1d(T_H_0)

    # Cooling timescale estimate
    tau_cool = E_total / L_H_0 if L_H_0 > 0 else 1e10

    if t_max is None:
        t_max = 5.0 * tau_cool

    times = np.linspace(0, t_max, n_steps)
    dt = times[1] - times[0] if n_steps > 1 else t_max

    # Arrays for the evolution
    T_H_arr = np.zeros(n_steps)
    kappa_arr = np.zeros(n_steps)
    n_BEC_arr = np.zeros(n_steps)
    c_s_arr = np.zeros(n_steps)
    F_H_arr = np.zeros(n_steps)
    E_radiated_arr = np.zeros(n_steps)

    # Initial conditions
    n_current = n_0
    kappa_current = kappa_0
    c_s_current = c_s_0
    T_H_current = T_H_0
    E_radiated = 0.0

    for i in range(n_steps):
        # Record state
        T_H_arr[i] = T_H_current
        kappa_arr[i] = kappa_current
        n_BEC_arr[i] = n_current
        c_s_arr[i] = c_s_current
        E_radiated_arr[i] = E_radiated

        # Hawking luminosity at current temperature
        L_H = hawking_luminosity_1d(T_H_current)
        F_H_arr[i] = L_H

        if i < n_steps - 1:
            # Energy radiated in this timestep
            dE = L_H * dt

            # Density change: atoms lost from condensate
            # Each atom carries energy ~ mu, so dN = dE / mu
            if E_per_atom > 0:
                dN = dE / E_per_atom
                dn = dN / L_cond if L_cond > 0 else 0.0
            else:
                dn = 0.0

            # Update density (ensure positivity)
            n_current = max(n_current - dn, n_0 * 1e-10)

            # Update sound speed
            c_s_current = _sound_speed_from_density(n_current, mass, g_int)

            # Update surface gravity
            kappa_current = _kappa_from_density(
                n_current, n_0, kappa_0, c_s_0, mass, g_int,
            )

            # Update Hawking temperature
            T_H_current = hawking_temperature(kappa_current)

            # Cumulative energy radiated
            E_radiated += dE

    # Extremality parameter: kappa(t) / kappa(0)
    extremality = kappa_arr / kappa_0

    return BackreactionEvolution(
        times=times,
        T_H_values=T_H_arr,
        kappa_values=kappa_arr,
        n_BEC_values=n_BEC_arr,
        c_s_values=c_s_arr,
        F_H_values=F_H_arr,
        extremality_parameter=extremality,
        energy_radiated=E_radiated_arr,
    )


# ═══════════════════════════════════════════════════════════════════
# Cooling timescale
# ═══════════════════════════════════════════════════════════════════

@dataclass
class CoolingTimescale:
    """Characteristic timescales for acoustic black hole cooling.

    The cooling follows kappa(t) ~ kappa_0 * exp(-t/tau_cool),
    so T_H halves in time t_half = tau_cool * ln(2).

    Attributes:
        tau_cool: Characteristic cooling timescale [s].
        T_H_half_life: Time for T_H to halve [s].
        final_T_H: Asymptotic T_H (formally zero) [K].
        E_total: Total condensate energy [J].
        L_H_initial: Initial Hawking luminosity [W].
        tau_over_lifetime: tau_cool / BEC lifetime.
        is_observable: Whether backreaction is observable within BEC lifetime.
        adiabaticity_ratio: tau_cool * kappa (should be >> 1).
    """
    tau_cool: float
    T_H_half_life: float
    final_T_H: float
    E_total: float
    L_H_initial: float
    tau_over_lifetime: float
    is_observable: bool
    adiabaticity_ratio: float


def cooling_timescale(si_params: SIPlatformParams) -> CoolingTimescale:
    """Compute the cooling timescale for an acoustic black hole.

    tau_cool = E_BEC / L_H
             = N * mu / [(pi/12) * (k_B * T_H)^2 / hbar]

    The adiabatic ratio tau_cool * kappa >> 1 confirms the
    quasi-static approximation is valid.

    Observability criterion: tau_cool / t_BEC < 100, where
    t_BEC is the useful lifetime of the acoustic BH configuration.
    Even tau_cool / t_BEC ~ 100 would show ~1% density change.

    Args:
        si_params: SI-unit platform parameters.

    Returns:
        CoolingTimescale with all diagnostic quantities.
    """
    N = si_params.n_atoms
    mu = si_params.chemical_potential
    T_H = si_params.T_H_si
    kappa = si_params.kappa_si
    t_life = si_params.bec_lifetime

    E_total = N * mu
    L_H = hawking_luminosity_1d(T_H)

    if L_H > 0:
        tau_cool = E_total / L_H
    else:
        tau_cool = float('inf')

    T_H_half_life = tau_cool * np.log(2.0)

    tau_over_lifetime = tau_cool / t_life if t_life > 0 else float('inf')

    # Observable if we can detect ~1% change within the BEC lifetime
    is_observable = tau_over_lifetime < 100.0

    # Adiabaticity ratio: should be >> 1 for quasi-static approximation
    adiabaticity_ratio = tau_cool * kappa

    return CoolingTimescale(
        tau_cool=tau_cool,
        T_H_half_life=T_H_half_life,
        final_T_H=0.0,  # Asymptotically zero (analog third law)
        E_total=E_total,
        L_H_initial=L_H,
        tau_over_lifetime=tau_over_lifetime,
        is_observable=is_observable,
        adiabaticity_ratio=adiabaticity_ratio,
    )


# ═══════════════════════════════════════════════════════════════════
# Platform backreaction summary
# ═══════════════════════════════════════════════════════════════════

@dataclass
class PlatformBackreaction:
    """Complete backreaction analysis for a single BEC platform.

    Attributes:
        platform_name: Platform identifier.
        si_params: SI-unit parameters.
        flux: Energy flux decomposition.
        timescale: Cooling timescale analysis.
        evolution: Time evolution of background fields.
    """
    platform_name: str
    si_params: SIPlatformParams
    flux: EnergyFlux
    timescale: CoolingTimescale
    evolution: BackreactionEvolution


def platform_backreaction(
    platform_key: str,
    evolution_steps: int = 500,
) -> PlatformBackreaction:
    """Compute complete backreaction analysis for one platform.

    Args:
        platform_key: One of 'steinhauer', 'heidelberg', 'trento'.
        evolution_steps: Number of timesteps for the evolution.

    Returns:
        PlatformBackreaction with flux, timescale, and evolution.
    """
    platform_factory = ALL_PLATFORMS[platform_key]
    platform = platform_factory()

    si_factory = ALL_SI_PLATFORMS[platform_key]
    si_params = si_factory()

    flux = compute_energy_flux(platform, si_params)
    timescale = cooling_timescale(si_params)
    evolution = backreaction_evolution(si_params, n_steps=evolution_steps)

    return PlatformBackreaction(
        platform_name=si_params.name,
        si_params=si_params,
        flux=flux,
        timescale=timescale,
        evolution=evolution,
    )


def all_platform_backreaction(
    evolution_steps: int = 200,
) -> dict[str, PlatformBackreaction]:
    """Compute backreaction analysis for all three BEC platforms.

    Returns:
        Dict mapping platform key to PlatformBackreaction.
    """
    results = {}
    for key in ALL_SI_PLATFORMS:
        results[key] = platform_backreaction(key, evolution_steps)
    return results


# ═══════════════════════════════════════════════════════════════════
# Analytic approximations
# ═══════════════════════════════════════════════════════════════════

def rational_cooling_model(
    kappa_0: float,
    tau_cool: float,
    times: np.ndarray,
) -> tuple[np.ndarray, np.ndarray]:
    """Exact rational cooling model for acoustic black hole backreaction.

    The exact solution of d(kappa)/dt = -kappa²/C gives:
        kappa(t) = kappa_0 / (1 + t/tau_cool)

    This is hyperbolic decay (not exponential). The exponential
    approximation kappa ~ kappa_0 exp(-t/tau_cool) is valid only
    for t << tau_cool.

    Lean: backreaction_cooling_monotone (WKBConnection.lean)
    Aristotle: manual

    Args:
        kappa_0: Initial surface gravity [s^-1].
        tau_cool: Cooling timescale [s].
        times: Time array [s].

    Returns:
        Tuple of (kappa_array, T_H_array in Kelvin).
    """
    kappa_arr = kappa_0 / (1.0 + times / tau_cool)
    T_H_arr = hawking_temperature(kappa_arr)
    return kappa_arr, T_H_arr


# Backwards compatibility alias
exponential_cooling_model = rational_cooling_model


def extremality_parameter_analytic(
    t: float | np.ndarray,
    tau_cool: float,
) -> float | np.ndarray:
    """Analytic extremality parameter kappa(t)/kappa(0).

    Uses the exact rational solution:
        kappa(t)/kappa(0) = 1 / (1 + t/tau_cool)

    This approaches zero as t -> infinity but never reaches it,
    implementing the analog of the third law of black hole mechanics.

    Args:
        t: Time [s] (scalar or array).
        tau_cool: Cooling timescale [s].

    Returns:
        Extremality parameter (1 at t=0, -> 0 as t -> inf).
    """
    return 1.0 / (1.0 + t / tau_cool)


def density_depletion_fraction(
    t: float,
    tau_cool: float,
) -> float:
    """Fraction of condensate density depleted by Hawking radiation.

    At leading order, the density change is:
        delta_n / n_0 ~ t / tau_cool  (for t << tau_cool)

    For the exact evolution:
        delta_n / n_0 = 1 - (1 + t/tau_cool)^(-1)

    This fraction must remain small (< 0.1) for the Bogoliubov
    approximation to remain valid.

    Args:
        t: Time [s].
        tau_cool: Cooling timescale [s].

    Returns:
        Fractional density depletion (0 at t=0, -> 1 as t -> inf).
    """
    return 1.0 - 1.0 / (1.0 + t / tau_cool)
