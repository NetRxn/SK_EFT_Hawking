"""Hawking noise spectrum for graphene Dirac fluid platforms.

Computes the current noise power spectrum S_I(ω) near a sonic horizon
in graphene, adapting the BEC WKB connection formula via the quasi-1D
block-diagonal reduction (DiracFluidMetric.lean).

The key adaptation from BEC:
- c_s → v_F/√2 (conformal Dirac fluid)
- Superluminal Bogoliubov dispersion → subluminal (more robust)
- Transport coefficients from viscosity η/s rather than Beliaev damping
- Detection channel: current noise S_I(ω) rather than density correlations
- Thermal background: Johnson-Nyquist at T_ambient >> T_H

Phase 5w Wave 4.
"""

import numpy as np
from dataclasses import dataclass

from src.core.constants import HBAR, K_B, E_CHARGE, GRAPHENE_PLATFORMS
from src.core.formulas import (
    hawking_temperature,
    dispersive_correction,
    first_order_correction,
    decoherence_parameter,
    fdr_noise_floor,
)
from src.graphene.hawking_predictions import (
    graphene_hawking_prediction,
    graphene_adiabaticity,
    graphene_damping_rate_horizon,
)


@dataclass
class GrapheneSpectrumPoint:
    """Single frequency point in the graphene Hawking noise spectrum."""
    omega: float            # frequency [s⁻¹]
    omega_over_kappa: float # dimensionless frequency
    n_hawking: float        # Hawking occupation (with corrections)
    n_planck: float         # ideal Planck at T_H
    n_thermal: float        # thermal occupation at T_ambient
    S_hawking: float        # Hawking noise PSD [A²/Hz]
    S_thermal: float        # Johnson-Nyquist noise PSD [A²/Hz]
    S_total: float          # total noise PSD [A²/Hz]
    snr_per_bin: float      # S_hawking / S_thermal per frequency bin


@dataclass
class GrapheneNoiseSpectrum:
    """Full noise spectrum prediction for a graphene platform.

    Contains arrays over frequency plus metadata for the detection protocol.
    """
    platform_name: str
    omega: np.ndarray           # [s⁻¹]
    freq_Hz: np.ndarray         # [Hz] = omega/(2π)
    n_hawking: np.ndarray       # Hawking occupation
    n_planck: np.ndarray        # ideal Planck at T_H
    n_thermal: np.ndarray       # thermal at T_ambient
    S_hawking: np.ndarray       # [A²/Hz]
    S_thermal: np.ndarray       # [A²/Hz]
    S_total: np.ndarray         # [A²/Hz]
    snr_per_bin: np.ndarray     # per-bin signal-to-noise

    # Scalar metadata
    T_H_K: float
    T_eff_K: float
    T_ambient_K: float
    kappa: float
    D: float
    delta_disp: float
    delta_diss: float
    omega_H: float              # k_B T_H / ℏ
    Gamma_mr: float             # momentum-relaxation rate

    # Detection protocol
    optimal_freq_Hz: float      # frequency of max SNR
    peak_snr: float             # maximum per-bin SNR
    integration_time_s: float   # time to reach SNR=1 (cumulative)
    freq_window_Hz: tuple       # (f_low, f_high) detection band


def compute_graphene_spectrum(
    platform_name: str,
    n_points: int = 300,
    omega_max_ratio: float = 10.0,
) -> GrapheneNoiseSpectrum:
    """Compute the full current noise spectrum for a graphene platform.

    The noise power spectral density has two components:
    1. Johnson-Nyquist thermal noise: S_JN(ω) = 4 k_B T_amb σ_Q
    2. Hawking excess noise: S_H(ω) ∝ n_Hawking(ω) × σ_Q × ℏω

    The Hawking occupation includes dispersive and dissipative corrections.

    Args:
        platform_name: key in GRAPHENE_PLATFORMS
        n_points: number of frequency bins
        omega_max_ratio: max frequency as multiple of ω_H

    Returns:
        GrapheneNoiseSpectrum with full spectrum and detection protocol
    """
    pred = graphene_hawking_prediction(platform_name)
    plat = GRAPHENE_PLATFORMS[platform_name]

    kappa = pred['kappa_s1']
    c_s = pred['c_s_ms']
    T_H = pred['T_H_K']
    T_eff = pred['T_eff_K']
    T_ambient = plat['T_ambient_K']
    D = pred['D']
    delta_disp = pred['delta_disp']
    delta_diss = pred['delta_diss']
    delta_k = pred['delta_k']
    sigma_Q_SI = plat['sigma_Q_SI']

    omega_H = K_B * T_H / HBAR
    Gamma_mr = plat['Gamma_mr_s1']

    # Frequency grid from 0.01 ω_H to omega_max_ratio × ω_H
    omega = np.linspace(0.01 * omega_H, omega_max_ratio * omega_H, n_points)
    freq_Hz = omega / (2 * np.pi)

    # Hawking occupation: modified Planck with dispersive + dissipative corrections
    # n_Hawking(ω) = 1/(exp(2πω/κ_eff) - 1) / (1 - δ_k) + n_noise
    # where κ_eff = κ(1 + δ_disp + δ_diss)
    kappa_eff = kappa * (1 + delta_disp + delta_diss)
    if kappa_eff > 0:
        beta_sq = 1.0 / (np.exp(2 * np.pi * omega / kappa_eff) - 1.0)
    else:
        # EFT breakdown — set to zero
        beta_sq = np.zeros_like(omega)
    n_noise = fdr_noise_floor(delta_k)
    n_hawking = beta_sq / max(1.0 - delta_k, 1e-30) + n_noise

    # Ideal Planck at T_H (for comparison)
    n_planck = 1.0 / (np.exp(HBAR * omega / (K_B * T_H)) - 1.0)

    # Thermal occupation at T_ambient
    n_thermal = 1.0 / (np.exp(HBAR * omega / (K_B * T_ambient)) - 1.0)

    # Current noise PSD
    # Johnson-Nyquist: S_JN = 4 k_B T σ_Q (white noise in the hydro regime)
    S_thermal = 4 * K_B * T_ambient * sigma_Q_SI * np.ones_like(omega)

    # Hawking noise PSD: excess current noise from pair production
    # S_H(ω) = 2 e² σ_Q ℏω n_Hawking(ω) / (π ℏ)  [quantum noise formula]
    # Simplified: S_H ∝ n_Hawking × ω × σ_Q × (2e²/π)
    S_hawking = (2 * E_CHARGE**2 / np.pi) * sigma_Q_SI * omega * n_hawking

    S_total = S_thermal + S_hawking

    # Per-bin signal-to-noise ratio
    snr_per_bin = S_hawking / S_thermal

    # Detection protocol
    best_idx = np.argmax(snr_per_bin)
    optimal_freq = freq_Hz[best_idx]
    peak_snr = snr_per_bin[best_idx]

    # Integration time to reach cumulative SNR = 1
    # SNR_cumulative = SNR_per_bin × √(Δf × t_int)
    # For SNR_cum = 1: t_int = 1 / (SNR_per_bin² × Δf)
    delta_f = freq_Hz[1] - freq_Hz[0] if len(freq_Hz) > 1 else 1e9
    if peak_snr > 0:
        integration_time = 1.0 / (peak_snr**2 * delta_f)
    else:
        integration_time = np.inf

    # Detection frequency window: where SNR > peak_snr / e
    threshold = peak_snr / np.e
    above = snr_per_bin > threshold
    if np.any(above):
        indices = np.where(above)[0]
        freq_window = (freq_Hz[indices[0]], freq_Hz[indices[-1]])
    else:
        freq_window = (0.0, 0.0)

    return GrapheneNoiseSpectrum(
        platform_name=platform_name,
        omega=omega,
        freq_Hz=freq_Hz,
        n_hawking=n_hawking,
        n_planck=n_planck,
        n_thermal=n_thermal,
        S_hawking=S_hawking,
        S_thermal=S_thermal,
        S_total=S_total,
        snr_per_bin=snr_per_bin,
        T_H_K=T_H,
        T_eff_K=T_eff,
        T_ambient_K=T_ambient,
        kappa=kappa,
        D=D,
        delta_disp=delta_disp,
        delta_diss=delta_diss,
        omega_H=omega_H,
        Gamma_mr=Gamma_mr,
        optimal_freq_Hz=optimal_freq,
        peak_snr=peak_snr,
        integration_time_s=integration_time,
        freq_window_Hz=freq_window,
    )


def detection_protocol_summary(platform_name: str) -> dict:
    """Generate a detection protocol summary for experimentalists.

    Returns a dict suitable for printing or including in a paper/proposal.
    """
    spec = compute_graphene_spectrum(platform_name)

    protocol = {
        'platform': platform_name,
        'T_H_K': spec.T_H_K,
        'T_eff_K': spec.T_eff_K,
        'T_ambient_K': spec.T_ambient_K,
        'D_adiabaticity': spec.D,
        'eft_valid': spec.D < 1,
        'corrections': {
            'delta_disp': spec.delta_disp,
            'delta_disp_pct': spec.delta_disp * 100,
            'delta_diss': spec.delta_diss,
            'delta_diss_pct': spec.delta_diss * 100,
            'dominant': 'dispersive' if abs(spec.delta_disp) > abs(spec.delta_diss) else 'dissipative',
        },
        'detection': {
            'optimal_freq_GHz': spec.optimal_freq_Hz / 1e9,
            'optimal_freq_band': f'{spec.freq_window_Hz[0]/1e9:.1f}–{spec.freq_window_Hz[1]/1e9:.1f} GHz',
            'peak_snr_per_bin': spec.peak_snr,
            'integration_time_s': spec.integration_time_s,
            'feasible': spec.integration_time_s < 3600,
        },
        'comparison_to_BEC': {
            'T_H_ratio': spec.T_H_K / 3.5e-10,  # vs Steinhauer T_H ~ 0.35 nK
            'dispersion_type': 'subluminal (more robust than BEC superluminal)',
        },
        'recommended_measurement': 'Current noise PSD S_I(ω) via Johnson noise thermometry '
                                    '(Kim group, Harvard: 5.5 mK sensitivity)',
    }
    return protocol
