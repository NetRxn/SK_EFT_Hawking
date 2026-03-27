"""Observable Hawking spectrum with exact WKB corrections.

Computes the full phonon occupation number n(omega) as measured in BEC
analog Hawking radiation experiments. Provides platform-specific predictions
for Steinhauer (87Rb), Heidelberg (39K), and Trento (23Na) experiments,
and comparison with the perturbative EFT treatment.

The spectrum includes three contributions:
    n(omega) = n_Hawking(omega) + n_noise(omega)

where:
    n_Hawking = |beta|^2 / (1 - delta_k)  [corrected Hawking occupation]
    n_noise = FDR-mandated noise floor     [environment contribution]

and n_Hawking itself contains:
    - Standard Planck factor at T_H = kappa/(2*pi)
    - Dispersive correction: delta_disp = -(pi/6)*D^2
    - Dissipative correction: delta_diss = Gamma_H/kappa (all EFT orders)
    - UV suppression above omega_max

Lean formalization: WKBConnection.lean — spectrum_thermal_limit,
    spectrum_uv_suppressed

References:
    - de Nova et al., Nature 569, 688 (2019) — Steinhauer Hawking spectrum
    - Sparn et al., PRL 133, 260201 (2024) — Heidelberg analog cosmology
    - Berti et al., Comptes Rendus (2025) — Trento spin-sonic proposal
"""

from dataclasses import dataclass, field

import numpy as np

from src.wkb.connection_formula import (
    exact_connection_formula,
    effective_surface_gravity,
    critical_frequency,
    dispersive_length,
    dissipative_length,
)
from src.wkb.bogoliubov import (
    ModifiedBogoliubov,
    modified_bogoliubov_coefficients,
    decoherence_parameter,
    fdr_noise_floor,
)
from src.core.formulas import damping_rate


# ═══════════════════════════════════════════════════════════════════
# Platform parameters
# ═══════════════════════════════════════════════════════════════════

@dataclass
class PlatformParams:
    """Experimental platform parameters in natural units (c_s=1, kappa=1).

    All three BEC platforms share the same structure but differ in the
    adiabaticity parameter D and dimensionless damping gamma_dim.

    Attributes:
        name: Platform identifier.
        D: Adiabaticity parameter kappa*xi/c_s.
        gamma_dim: Dimensionless damping rate Gamma_Bel/kappa.
        kappa: Surface gravity (= 1 in natural units).
        c_s: Sound speed (= 1 in natural units).
        xi: Healing length (= D in natural units).
        description: Human-readable description.
    """
    name: str
    D: float
    gamma_dim: float
    kappa: float = 1.0
    c_s: float = 1.0
    description: str = ""

    @property
    def xi(self) -> float:
        return self.D * self.c_s / self.kappa

    @property
    def gamma_1(self) -> float:
        """First-order transport coefficient (equal KMS splitting)."""
        return self.gamma_dim / 2.0

    @property
    def gamma_2(self) -> float:
        """First-order transport coefficient (equal KMS splitting)."""
        return self.gamma_dim / 2.0

    @property
    def gamma_2_1(self) -> float:
        """Second-order coefficient (xi/c_s suppressed)."""
        return self.gamma_dim * self.xi / (2.0 * self.c_s)

    @property
    def gamma_2_2(self) -> float:
        """Second-order coefficient (positivity: gamma_2_2 = -gamma_2_1)."""
        return -self.gamma_2_1

    @property
    def T_H(self) -> float:
        """Hawking temperature kappa/(2*pi)."""
        return self.kappa / (2.0 * np.pi)

    @property
    def omega_max(self) -> float:
        """Critical frequency for UV cutoff."""
        return critical_frequency(self.kappa, self.xi, self.c_s)


def steinhauer_platform() -> PlatformParams:
    """Steinhauer 87Rb BEC parameters (Technion)."""
    return PlatformParams(
        name="Steinhauer_Rb87",
        D=0.03,
        gamma_dim=0.003,
        description="Steinhauer 87Rb waterfall BEC (Technion)",
    )


def heidelberg_platform() -> PlatformParams:
    """Heidelberg 39K BEC parameters (Oberthaler group)."""
    return PlatformParams(
        name="Heidelberg_K39",
        D=0.02,
        gamma_dim=0.002,
        description="Heidelberg 39K Feshbach-tunable BEC",
    )


def trento_platform() -> PlatformParams:
    """Trento 23Na spin-sonic BEC parameters (Carusotto group)."""
    return PlatformParams(
        name="Trento_Na23",
        D=0.014,
        gamma_dim=1.4e-5,
        description="Trento 23Na spin-sonic BEC proposal",
    )


ALL_PLATFORMS = {
    'steinhauer': steinhauer_platform,
    'heidelberg': heidelberg_platform,
    'trento': trento_platform,
}


# ═══════════════════════════════════════════════════════════════════
# Spectrum computation
# ═══════════════════════════════════════════════════════════════════

@dataclass
class SpectrumPoint:
    """A single point in the Hawking spectrum.

    Attributes:
        omega: Mode frequency.
        n_total: Total occupation number.
        n_hawking: Hawking contribution (corrected for decoherence).
        n_planck: Standard Planck at T_H (no corrections).
        n_noise: FDR noise floor.
        T_eff: Effective temperature at this frequency.
        delta_disp: Dispersive correction.
        delta_diss: Dissipative correction.
        delta_k: Decoherence parameter.
        uv_suppression: UV suppression factor (1 = no suppression).
        relative_deviation: (n_total - n_planck) / n_planck.
    """
    omega: float
    n_total: float
    n_hawking: float
    n_planck: float
    n_noise: float
    T_eff: float
    delta_disp: float
    delta_diss: float
    delta_k: float
    uv_suppression: float
    relative_deviation: float


@dataclass
class HawkingSpectrum:
    """Full Hawking spectrum with all corrections.

    Attributes:
        platform: Platform parameters used.
        points: List of SpectrumPoint at each frequency.
        omega_array: Frequencies evaluated.
        n_total_array: Total occupation numbers.
        n_planck_array: Standard Planck occupations.
        T_H: Hawking temperature.
        omega_max: Critical frequency (UV cutoff).
        max_deviation: Maximum |relative_deviation| across spectrum.
        detectability: Dict of detectability metrics.
    """
    platform: PlatformParams
    points: list[SpectrumPoint]
    omega_array: np.ndarray
    n_total_array: np.ndarray
    n_planck_array: np.ndarray
    T_H: float
    omega_max: float
    max_deviation: float
    detectability: dict


def planck_occupation(omega: float, T: float) -> float:
    """Standard Planck/Bose-Einstein occupation at temperature T.

    n_BE = 1 / (exp(omega/T) - 1)

    Args:
        omega: Frequency.
        T: Temperature (same units as omega).

    Returns:
        Occupation number.
    """
    if T <= 0 or omega <= 0:
        return 0.0
    x = omega / T
    if x > 500:
        return 0.0
    return 1.0 / (np.exp(x) - 1.0)


def compute_spectrum(
    platform: PlatformParams,
    omega_min: float = 0.1,
    omega_max_factor: float = 5.0,
    n_points: int = 50,
    T_env: float = 0.0,
) -> HawkingSpectrum:
    """Compute the full Hawking spectrum for a given platform.

    Evaluates the exact WKB connection formula at n_points frequencies
    from omega_min*T_H to omega_max_factor*T_H.

    Args:
        platform: Experimental platform parameters.
        omega_min: Minimum frequency in units of T_H.
        omega_max_factor: Maximum frequency in units of T_H.
        n_points: Number of frequency points.
        T_env: Environment temperature.

    Returns:
        HawkingSpectrum with the full spectrum and diagnostics.
    """
    T_H = platform.T_H
    omega_array = np.linspace(omega_min * T_H, omega_max_factor * T_H, n_points)
    om_max = platform.omega_max

    points = []
    n_total_list = []
    n_planck_list = []

    for omega in omega_array:
        # Exact WKB connection formula
        conn = exact_connection_formula(
            omega, platform.kappa, platform.c_s, platform.xi,
            platform.gamma_1, platform.gamma_2,
            platform.gamma_2_1, platform.gamma_2_2,
        )

        # Modified Bogoliubov coefficients
        bog = modified_bogoliubov_coefficients(conn, T_env)

        # Standard Planck for comparison
        n_pl = planck_occupation(omega, T_H)

        # Relative deviation
        rel_dev = (bog.n_total - n_pl) / n_pl if n_pl > 0 else 0.0

        point = SpectrumPoint(
            omega=omega,
            n_total=bog.n_total,
            n_hawking=bog.n_hawking,
            n_planck=n_pl,
            n_noise=bog.n_noise,
            T_eff=bog.T_eff,
            delta_disp=conn.kappa_eff.delta_disp,
            delta_diss=conn.kappa_eff.delta_diss,
            delta_k=conn.delta_k,
            uv_suppression=conn.uv_suppression,
            relative_deviation=rel_dev,
        )
        points.append(point)
        n_total_list.append(bog.n_total)
        n_planck_list.append(n_pl)

    n_total_arr = np.array(n_total_list)
    n_planck_arr = np.array(n_planck_list)

    # Detectability metrics
    deviations = np.array([abs(p.relative_deviation) for p in points])
    max_dev = float(np.max(deviations))

    # Frequency at maximum deviation
    i_max = int(np.argmax(deviations))
    omega_peak_dev = float(omega_array[i_max])

    # Estimate shots needed for detection (3-sigma):
    # Use the dissipative correction at T_H as the target signal,
    # NOT max_deviation (which diverges at high omega where n_Planck -> 0).
    # Precision scales as 1/sqrt(N_shots).
    # Current best: ~30% per-bin (Steinhauer 2019, 7000 shots)
    current_precision = 0.30
    current_shots = 7000

    # Find delta_diss at omega ~ T_H (the physically meaningful signal)
    i_TH = int(np.argmin(np.abs(omega_array - T_H)))
    delta_diss_at_TH = abs(points[i_TH].delta_diss) if i_TH < len(points) else 0.0

    if delta_diss_at_TH > 0:
        required_precision = delta_diss_at_TH / 3.0
        shots_needed = current_shots * (current_precision / required_precision)**2
    else:
        shots_needed = float('inf')

    detectability = {
        'max_deviation': max_dev,
        'delta_diss_at_TH': delta_diss_at_TH,
        'omega_peak_deviation': omega_peak_dev,
        'omega_peak_deviation_over_T_H': omega_peak_dev / T_H,
        'shots_needed_3sigma': shots_needed,
        'feasible': shots_needed < 1e8,  # 10^8 is the upper bound of current technology
    }

    return HawkingSpectrum(
        platform=platform,
        points=points,
        omega_array=omega_array,
        n_total_array=n_total_arr,
        n_planck_array=n_planck_arr,
        T_H=T_H,
        omega_max=om_max,
        max_deviation=max_dev,
        detectability=detectability,
    )


# ═══════════════════════════════════════════════════════════════════
# Perturbative comparison
# ═══════════════════════════════════════════════════════════════════

@dataclass
class PerturbativeComparison:
    """Comparison between exact WKB and perturbative EFT results.

    Attributes:
        omega: Frequency array.
        n_exact: Occupation from exact WKB.
        n_perturbative: Occupation from perturbative EFT.
        n_planck: Standard Planck.
        fractional_difference: (n_exact - n_perturbative) / n_perturbative.
        max_difference: Maximum fractional difference.
        crossover_omega: Frequency where difference exceeds 1%.
    """
    omega: np.ndarray
    n_exact: np.ndarray
    n_perturbative: np.ndarray
    n_planck: np.ndarray
    fractional_difference: np.ndarray
    max_difference: float
    crossover_omega: Optional[float]


def perturbative_spectrum(
    omega: float,
    platform: PlatformParams,
) -> float:
    """Compute perturbative occupation number (from wkb_analysis.py approach).

    This uses the perturbative formula:
        n_pert = 1 / (exp(2*pi*omega/kappa_eff) - 1)
    where kappa_eff = kappa / (1 + delta_total).

    No decoherence, no noise floor, no UV suppression.

    Args:
        omega: Mode frequency.
        platform: Platform parameters.

    Returns:
        Perturbative occupation number.
    """
    keff = effective_surface_gravity(
        omega, platform.kappa, platform.c_s, platform.xi,
        platform.gamma_1, platform.gamma_2,
        platform.gamma_2_1, platform.gamma_2_2,
    )
    T_eff = keff.kappa_eff / (2.0 * np.pi)
    return planck_occupation(omega, T_eff)


def compare_exact_vs_perturbative(
    platform: PlatformParams,
    omega_min: float = 0.1,
    omega_max_factor: float = 8.0,
    n_points: int = 80,
    T_env: float = 0.0,
) -> PerturbativeComparison:
    """Compare exact WKB and perturbative EFT spectra.

    The exact WKB includes:
    - Modified unitarity (delta_k)
    - FDR noise floor (n_noise)
    - UV suppression above omega_max

    The perturbative EFT has none of these.

    Args:
        platform: Platform parameters.
        omega_min: Min frequency in units of T_H.
        omega_max_factor: Max frequency in units of T_H.
        n_points: Number of frequency points.
        T_env: Environment temperature.

    Returns:
        PerturbativeComparison with the full comparison.
    """
    T_H = platform.T_H
    omega_arr = np.linspace(omega_min * T_H, omega_max_factor * T_H, n_points)

    n_exact_list = []
    n_pert_list = []
    n_planck_list = []

    for omega in omega_arr:
        # Exact WKB
        conn = exact_connection_formula(
            omega, platform.kappa, platform.c_s, platform.xi,
            platform.gamma_1, platform.gamma_2,
            platform.gamma_2_1, platform.gamma_2_2,
        )
        bog = modified_bogoliubov_coefficients(conn, T_env)
        n_exact_list.append(bog.n_total)

        # Perturbative
        n_pert_list.append(perturbative_spectrum(omega, platform))

        # Planck
        n_planck_list.append(planck_occupation(omega, T_H))

    n_exact_arr = np.array(n_exact_list)
    n_pert_arr = np.array(n_pert_list)
    n_planck_arr = np.array(n_planck_list)

    # Fractional difference
    with np.errstate(divide='ignore', invalid='ignore'):
        frac_diff = np.where(
            n_pert_arr > 1e-30,
            (n_exact_arr - n_pert_arr) / n_pert_arr,
            0.0,
        )

    max_diff = float(np.max(np.abs(frac_diff)))

    # Find crossover frequency (where difference exceeds 1%)
    crossover = None
    for i, fd in enumerate(frac_diff):
        if abs(fd) > 0.01:
            crossover = float(omega_arr[i])
            break

    return PerturbativeComparison(
        omega=omega_arr,
        n_exact=n_exact_arr,
        n_perturbative=n_pert_arr,
        n_planck=n_planck_arr,
        fractional_difference=frac_diff,
        max_difference=max_diff,
        crossover_omega=crossover,
    )


# ═══════════════════════════════════════════════════════════════════
# All-platform predictions
# ═══════════════════════════════════════════════════════════════════

def platform_predictions(T_env: float = 0.0) -> dict[str, HawkingSpectrum]:
    """Compute Hawking spectra for all three BEC platforms.

    Returns spectra for Steinhauer (87Rb), Heidelberg (39K), and
    Trento (23Na) experiments, enabling direct comparison of
    detectability across platforms.

    Args:
        T_env: Environment temperature (0 for vacuum).

    Returns:
        Dict mapping platform name to HawkingSpectrum.
    """
    results = {}
    for name, factory in ALL_PLATFORMS.items():
        platform = factory()
        spectrum = compute_spectrum(platform, T_env=T_env)
        results[name] = spectrum
    return results


# ═══════════════════════════════════════════════════════════════════
# Summary diagnostics
# ═══════════════════════════════════════════════════════════════════

def spectrum_summary(spectrum: HawkingSpectrum) -> dict:
    """Generate summary diagnostics for a Hawking spectrum.

    Args:
        spectrum: Computed Hawking spectrum.

    Returns:
        Dictionary of diagnostic quantities.
    """
    p = spectrum.platform
    k_H = p.T_H / p.c_s  # horizon wavenumber at T_H
    Gamma_H = damping_rate(
        k_H, p.T_H, p.c_s,
        p.gamma_1, p.gamma_2,
        p.gamma_2_1, p.gamma_2_2,
    )
    dk = decoherence_parameter(Gamma_H, p.kappa)
    n_noise = fdr_noise_floor(dk, p.T_H)

    ell_D = dispersive_length(p.kappa, p.xi, p.c_s)
    ell_diss = dissipative_length(p.kappa, p.c_s, Gamma_H / p.kappa)

    return {
        'platform': p.name,
        'D': p.D,
        'gamma_dim': p.gamma_dim,
        'T_H': p.T_H,
        'omega_max': spectrum.omega_max,
        'omega_max_over_T_H': spectrum.omega_max / p.T_H,
        'delta_diss_at_T_H': Gamma_H / p.kappa,
        'delta_k_at_T_H': dk,
        'n_noise_at_T_H': n_noise,
        'ell_D': ell_D,
        'ell_diss': ell_diss,
        'ell_diss_over_ell_D': ell_diss / ell_D if ell_D > 0 else 0.0,
        'max_deviation': spectrum.max_deviation,
        'shots_needed': spectrum.detectability['shots_needed_3sigma'],
        'feasible': spectrum.detectability['feasible'],
    }
