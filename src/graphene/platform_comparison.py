"""Unified multi-platform comparison: BEC, polariton, and graphene.

Generates the publication-ready comparison table for Paper 16 and the
platform integration wave (Phase 5w Wave 8). Three analog gravity
platforms, each with distinct advantages and regimes.

Phase 5w Wave 8.
"""

import numpy as np
from dataclasses import dataclass

from src.core.constants import (
    HBAR, K_B, EXPERIMENTS, POLARITON_PLATFORMS, GRAPHENE_PLATFORMS,
)
from src.core.formulas import hawking_temperature
from src.graphene.hawking_predictions import graphene_hawking_prediction
from src.graphene.wkb_spectrum import detection_protocol_summary
from src.graphene.transport_counting import (
    classify_first_order_conformal_charged,
    wiedemann_franz_lorenz_ratio,
)


@dataclass
class PlatformSummary:
    """Unified summary for one analog gravity platform."""
    name: str
    platform_type: str          # 'BEC', 'polariton', 'graphene'
    causal_speed_ms: float      # c_s or v_F [m/s]
    T_H_K: float                # Hawking temperature [K]
    T_ambient_K: float          # operating temperature [K]
    T_ratio: float              # T_H / T_ambient
    D_adiabaticity: float       # EFT expansion parameter
    delta_disp: float           # dispersive correction
    delta_diss: float           # dissipative correction
    dispersion_type: str        # 'superluminal' or 'subluminal'
    dimensionality: str         # '1+1D' or '2+1D'
    horizon_realized: bool      # has a sonic horizon been created?
    detection_channel: str      # how to observe Hawking radiation
    key_advantage: str
    key_challenge: str


def bec_platform_summaries() -> list:
    """Generate summaries for the three BEC platforms."""
    from src.core.transonic_background import (
        steinhauer_Rb87, heidelberg_K39, trento_spin_sonic,
        solve_transonic_background,
    )

    summaries = []
    factories = {
        'Steinhauer_Rb87': (steinhauer_Rb87, 'Steinhauer ⁸⁷Rb (Technion)', True),
        'Heidelberg_K39': (heidelberg_K39, 'Heidelberg ³⁹K (projected)', False),
        'Trento_Na23': (trento_spin_sonic, 'Trento ²³Na spin-sonic (projected)', False),
    }

    for name, (factory, desc, realized) in factories.items():
        params = factory()
        bg = solve_transonic_background(params)
        T_H = hawking_temperature(bg.surface_gravity)

        summaries.append(PlatformSummary(
            name=name,
            platform_type='BEC',
            causal_speed_ms=params.sound_speed_upstream,
            T_H_K=T_H,
            T_ambient_K=1e-8,  # BEC: ~10 nK
            T_ratio=T_H / 1e-8,
            D_adiabaticity=bg.adiabaticity,
            delta_disp=-(np.pi / 6) * bg.adiabaticity**2,
            delta_diss=0.01,  # order of magnitude for Beliaev
            dispersion_type='superluminal',
            dimensionality='1+1D',
            horizon_realized=realized,
            detection_channel='density-density correlations',
            key_advantage='T_H/T_ambient ~ O(1), quantum regime',
            key_challenge='T_H ~ nK, long integration times',
        ))
    return summaries


def polariton_platform_summaries() -> list:
    """Generate summaries for polariton platforms."""
    summaries = []
    for name, plat in POLARITON_PLATFORMS.items():
        T_H = HBAR * plat['kappa'] / (2 * np.pi * K_B)
        D = plat['D']
        summaries.append(PlatformSummary(
            name=name,
            platform_type='polariton',
            causal_speed_ms=plat['c_s'],
            T_H_K=T_H,
            T_ambient_K=4.0,  # cryostat
            T_ratio=T_H / 4.0,
            D_adiabaticity=D,
            delta_disp=-(np.pi / 6) * D**2,
            delta_diss=plat['Gamma_pol'] / plat['kappa'],
            dispersion_type='superluminal',
            dimensionality='1+1D',
            horizon_realized=True,  # Falque 2025
            detection_channel='luminescence spectroscopy',
            key_advantage='driven-dissipative, optical readout',
            key_challenge='cavity loss competes with Hawking signal',
        ))
    return summaries


def graphene_platform_summaries() -> list:
    """Generate summaries for graphene platforms."""
    summaries = []
    for name, plat in GRAPHENE_PLATFORMS.items():
        if name == 'PN_junction_10nm':
            continue  # Not acoustic horizon
        pred = graphene_hawking_prediction(name)
        summaries.append(PlatformSummary(
            name=name,
            platform_type='graphene',
            causal_speed_ms=plat['c_s'],
            T_H_K=pred['T_H_K'],
            T_ambient_K=plat['T_ambient_K'],
            T_ratio=pred['T_H_over_T_ambient'],
            D_adiabaticity=pred['D'],
            delta_disp=pred['delta_disp'],
            delta_diss=pred['delta_diss'],
            dispersion_type='subluminal',
            dimensionality='2+1D',
            horizon_realized=(name == 'Dean_bilayer_nozzle'),
            detection_channel='current noise S_I(ω)',
            key_advantage='T_H ~ K (10⁹× BEC), subluminal = robust',
            key_challenge='T_ambient >> T_H, thermal background',
        ))
    return summaries


def all_platform_summaries() -> list:
    """Generate summaries for all platforms across all three types."""
    return (bec_platform_summaries() +
            polariton_platform_summaries() +
            graphene_platform_summaries())


def print_comparison_table():
    """Print the unified multi-platform comparison table."""
    summaries = all_platform_summaries()

    print('Unified Analog Gravity Platform Comparison')
    print('=' * 120)
    print(f'{"Platform":<25} {"Type":<10} {"c_s (m/s)":<12} {"T_H (K)":<12} '
          f'{"T_H/T_amb":<10} {"D":<8} {"δ_disp":<10} {"Disp.":<12} '
          f'{"Dim.":<6} {"Horizon?":<9}')
    print('-' * 120)

    for s in summaries:
        print(f'{s.name:<25} {s.platform_type:<10} {s.causal_speed_ms:<12.2e} '
              f'{s.T_H_K:<12.2e} {s.T_ratio:<10.2e} {s.D_adiabaticity:<8.3f} '
              f'{s.delta_disp:<10.2e} {s.dispersion_type:<12} '
              f'{s.dimensionality:<6} {"YES" if s.horizon_realized else "no":<9}')


def graphene_advantage_summary():
    """Print a focused summary of graphene's advantages over BEC and polariton."""
    print('Graphene Dirac Fluid: Advantages for Analog Hawking Radiation')
    print('=' * 70)
    print()
    print('vs. BEC:')
    print('  + T_H ~ 1-10 K (vs ~ nK): 10⁹× larger signal')
    print('  + Subluminal dispersion: Hawking formula MORE robust')
    print('  + Natively relativistic: c_s = v_F/√2 exact (not emergent)')
    print('  + Sonic horizon demonstrated (Dean group, Sept 2025)')
    print('  - T_ambient >> T_H: thermal background dominates')
    print('  - Dissipation window marginal (ω_H/Γ_mr ~ 1.6 for Dean)')
    print()
    print('vs. Polariton:')
    print('  + Thermalized (KMS restored): cleaner EFT expansion')
    print('  + No cavity loss: dissipation from viscosity, not decay')
    print('  + 2+1D: richer transport structure (shear + charge)')
    print('  + Established measurement infrastructure (noise thermometry)')
    print('  - No optical readout (electronic measurement required)')
    print()
    print('Unique to graphene:')
    print('  * WF violation (>200×): independent test of two-channel SK-EFT')
    print('  * η/s → KSS bound: strong-coupling benchmark')
    print('  * Formally verified: 25 Lean 4 theorems, 0 sorry')
