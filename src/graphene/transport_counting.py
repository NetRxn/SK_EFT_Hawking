"""Transport coefficient classification for 2+1D relativistic charged Dirac fluid.

Generalizes the 1+1D BEC counting formula count(N) = floor((N+1)/2) + 1
to 2+1D relativistic hydrodynamics. In higher dimensions there is NO
closed-form counting formula — must enumerate tensor structures per
BRSSS (Baier-Romatschke-Son-Starinets-Stephanov) classification.

The transport coefficients decompose into three independent sectors:
- Tensor (rank-2 traceless symmetric): shear viscosity η, relaxation τ_π, ...
- Vector (rank-1): charge conductivity σ_Q, heat relaxation τ_q, ...
- Scalar (rank-0): bulk viscosity ζ (= 0 for conformal), ...

Conformal symmetry (ε = 2p in 2+1D) sets ζ = 0 and reduces the scalar sector.

Phase 5w Wave 5.

References:
    - BRSSS, JHEP 04, 100 (2008) [arXiv:0712.2451]
    - Kovtun, JHEP 10, 034 (2019) — BDNK first-order stability
    - Diles et al., JHEP 05, 019 (2020) — third-order
    - Lucas & Fong, JPCM 30, 053001 (2018) — Dirac fluid review
    - Jensen et al., SciPost Phys. 5, 053 (2018) — SK transport panoply
"""

from dataclasses import dataclass

import numpy as np

from src.core.constants import K_B, E_CHARGE

# Sommerfeld/Drude Lorenz number L₀ = (π²/3)(k_B/e)² ≈ 2.44e-8 W·Ω·K⁻²,
# equivalently [V²/K²]. The Lorenz NUMBER L = κ/(σT) carries THESE units;
# only the RATIO L/L₀ is dimensionless. (Encodes the units the old
# `wiedemann_franz_lorenz_ratio` docstring mislabelled — R-09.)
L_LORENZ_SOMMERFELD = (np.pi ** 2 / 3.0) * (K_B / E_CHARGE) ** 2  # [V²/K²] = [W·Ω·K⁻²]


@dataclass
class TransportSector:
    """A sector of transport coefficients at a given derivative order."""
    name: str               # 'tensor', 'vector', 'scalar'
    order: int              # derivative order (1, 2, 3)
    dissipative: int        # number of dissipative coefficients
    non_dissipative: int    # number of non-dissipative (thermodynamic) coefficients
    parity_odd: int         # number of parity-odd coefficients (Hall-type)
    coefficients: list      # names of the coefficients
    constraints: list       # constraints that reduce the count
    notes: str = ""


@dataclass
class TransportClassification:
    """Full classification at a given order for a specific fluid type."""
    fluid_type: str         # 'conformal_charged', 'non_conformal_charged', etc.
    dimension: str          # '1+1D' or '2+1D'
    order: int              # derivative order
    sectors: list           # list of TransportSector
    total_dissipative: int
    total_non_dissipative: int
    total_parity_odd: int
    total_independent: int  # after all constraints
    kms_constraints: int    # number of FDR/KMS constraints on noise sector
    notes: str = ""


def bec_1d_counting(N: int) -> int:
    """BEC 1+1D counting formula (existing, for comparison).

    count(N) = floor((N+1)/2) + 1

    Lean: transport_coefficient_count (SecondOrderSK.lean)
    """
    return (N + 1) // 2 + 1


def classify_first_order_conformal_charged() -> TransportClassification:
    """First-order transport for 2+1D conformal charged fluid.

    Result: 2 dissipative coefficients (η, σ_Q), 0 parity-odd (no B field).
    Bulk viscosity ζ = 0 by conformal symmetry (Tr T^μ_μ = 0).
    Thermal conductivity κ is NOT independent — determined by η, σ_Q, EOS.

    This matches the 1+1D BEC count of 2 at first order, but the physical
    content is completely different.
    """
    tensor = TransportSector(
        name='tensor', order=1, dissipative=1, non_dissipative=0, parity_odd=0,
        coefficients=['η (shear viscosity)'],
        constraints=['Conformal: ζ = 0 (would be in scalar sector)'],
    )
    vector = TransportSector(
        name='vector', order=1, dissipative=1, non_dissipative=0, parity_odd=0,
        coefficients=['σ_Q (charge conductivity)'],
        constraints=['κ_thermal determined by σ_Q via constitutive relation'],
        notes='Thermoelectric coefficients (Seebeck, Peltier) follow from '
              'two-component fluid structure, not independent.',
    )
    scalar = TransportSector(
        name='scalar', order=1, dissipative=0, non_dissipative=0, parity_odd=0,
        coefficients=[],
        constraints=['ζ = 0 by conformal symmetry'],
    )
    return TransportClassification(
        fluid_type='conformal_charged',
        dimension='2+1D',
        order=1,
        sectors=[tensor, vector, scalar],
        total_dissipative=2,
        total_non_dissipative=0,
        total_parity_odd=0,
        total_independent=2,
        kms_constraints=2,  # KMS fixes noise kernel for each dissipative coeff
        notes='Matches 1+1D BEC count(1) = 2. Physical content differs: '
              'BEC has γ₁ (bulk) + γ₂ (flow); Dirac has η (shear) + σ_Q (charge).',
    )


def classify_first_order_non_conformal_charged() -> TransportClassification:
    """First-order transport for 2+1D non-conformal charged fluid.

    Result: 3 dissipative coefficients (η, ζ, σ_Q).
    Near CNP, ζ is small (conformal symmetry weakly broken by e-phonon,
    lattice, running coupling).
    """
    tensor = TransportSector(
        name='tensor', order=1, dissipative=1, non_dissipative=0, parity_odd=0,
        coefficients=['η (shear viscosity)'], constraints=[],
    )
    vector = TransportSector(
        name='vector', order=1, dissipative=1, non_dissipative=0, parity_odd=0,
        coefficients=['σ_Q (charge conductivity)'], constraints=[],
    )
    scalar = TransportSector(
        name='scalar', order=1, dissipative=1, non_dissipative=0, parity_odd=0,
        coefficients=['ζ (bulk viscosity)'],
        constraints=[],
        notes='ζ ≈ 0 near CNP (conformal limit), nonzero away from CNP.',
    )
    return TransportClassification(
        fluid_type='non_conformal_charged',
        dimension='2+1D',
        order=1,
        sectors=[tensor, vector, scalar],
        total_dissipative=3,
        total_non_dissipative=0,
        total_parity_odd=0,
        total_independent=3,
        kms_constraints=3,
        notes='1+1D BEC count(1) = 2; non-conformal 2+1D has 3.',
    )


def classify_second_order_conformal_charged() -> TransportClassification:
    """Second-order transport for 2+1D conformal charged fluid.

    The BRSSS classification (adapted to 2+1D with charge) gives 8-12
    independent coefficients. The Haack-Yarom identity
    2ητ_π − 4λ₁ − λ₂ = 0 reduces the tensor sector by 1.

    Compared to 1+1D BEC count(2) = 2, this is dramatically richer.
    """
    tensor = TransportSector(
        name='tensor', order=2, dissipative=4, non_dissipative=0, parity_odd=0,
        coefficients=[
            'τ_π (shear relaxation time)',
            'λ₁ (vorticity-shear coupling)',
            'λ₂ (vorticity coupling)',
            'λ₃ (shear-shear coupling)',
        ],
        constraints=['Haack-Yarom: 2ητ_π − 4λ₁ − λ₂ = 0 (reduces by 1)'],
        notes='After Haack-Yarom: 3 independent tensor coefficients.',
    )
    vector = TransportSector(
        name='vector', order=2, dissipative=4, non_dissipative=0, parity_odd=0,
        coefficients=[
            'τ_J (charge relaxation time)',
            'τ_q (heat flux relaxation time)',
            'ℓ₁ (charge-shear coupling)',
            'ℓ₂ (charge-vorticity coupling)',
        ],
        constraints=[],
        notes='Cross-couplings between charge and heat sectors.',
    )
    scalar = TransportSector(
        name='scalar', order=2, dissipative=2, non_dissipative=0, parity_odd=0,
        coefficients=[
            'κ_curv (curvature coupling)',
            'ξ_bulk (bulk relaxation, suppressed by conformal)',
        ],
        constraints=['Conformal: some scalar structures vanish'],
        notes='Reduced from non-conformal count by conformal Ward identity.',
    )
    return TransportClassification(
        fluid_type='conformal_charged',
        dimension='2+1D',
        order=2,
        sectors=[tensor, vector, scalar],
        total_dissipative=10,
        total_non_dissipative=0,
        total_parity_odd=0,
        total_independent=9,  # 10 - 1 (Haack-Yarom)
        kms_constraints=9,
        notes='1+1D BEC count(2) = 2; 2+1D conformal charged has ~9. '
              'The tensor structure richness comes from SO(2) spatial rotations '
              '(absent in 1+1D).',
    )


def classify_parity_odd_first_order() -> TransportClassification:
    """First-order parity-odd (Hall) transport in 2+1D.

    With a magnetic field B or other parity-breaking source, two
    non-dissipative first-order coefficients appear:
    - η_H (Hall viscosity)
    - σ_H (Hall conductivity)

    These are zero without B field. Deferred to Wave 7 extension.
    """
    tensor = TransportSector(
        name='tensor', order=1, dissipative=0, non_dissipative=0, parity_odd=1,
        coefficients=['η_H (Hall viscosity)'],
        constraints=['Requires parity breaking (B field, strain, etc.)'],
    )
    vector = TransportSector(
        name='vector', order=1, dissipative=0, non_dissipative=0, parity_odd=1,
        coefficients=['σ_H (Hall conductivity)'],
        constraints=['Requires parity breaking'],
    )
    return TransportClassification(
        fluid_type='parity_odd',
        dimension='2+1D',
        order=1,
        sectors=[tensor, vector],
        total_dissipative=0,
        total_non_dissipative=0,
        total_parity_odd=2,
        total_independent=2,
        kms_constraints=0,  # non-dissipative: no FDR constraint
        notes='Zero without B field. Present in strained or gated graphene.',
    )


def comparison_table():
    """Print the comparison table: 1+1D BEC vs 2+1D Dirac fluid."""
    print('Transport Coefficient Comparison: 1+1D BEC vs 2+1D Dirac Fluid')
    print('=' * 75)
    print(f'{"Order":<8} {"1+1D BEC":<20} {"2+1D conformal":<20} {"2+1D non-conf":<15}')
    print('-' * 75)
    print(f'{"1st":<8} {bec_1d_counting(1):<20} {2:<20} {3:<15}')
    print(f'{"2nd":<8} {bec_1d_counting(2):<20} {"~9 (BRSSS+charge)":<20} {"~15-20":<15}')
    print(f'{"3rd":<8} {bec_1d_counting(3):<20} {"~30-50 (est.)":<20} {"~50-80 (est.)":<15}')
    print()
    print('Key difference: 1+1D has scalar sector only (no SO(2) tensor decomposition).')
    print('2+1D has tensor/vector/scalar sectors contributing independently.')
    print('No closed-form counting formula exists for 2+1D.')


def wiedemann_franz_lorenz_ratio(n, n_0, lorenz_peak_ratio):
    """Regularized Wiedemann–Franz Lorenz-ratio profile L/L₀(n) for the
    graphene Dirac fluid near charge neutrality.

    Two-channel hydrodynamics gives, in the CLEAN limit, a thermal
    conductivity κ ∝ (ε+p)²v_F²/(T σ_Q n²) and hence a Lorenz ratio
    L/L₀ = κ/(σ_Q T L₀) that would diverge as n → 0 (Lucas & Fong 2018,
    §3). That divergence is an idealization: every real sample has a finite
    intrinsic/disorder carrier density n₀ — the charge-puddle rms density
    together with the thermally-excited density n_th ~ (k_B T / ℏ v_F)² —
    that REGULARIZES the neutrality-point divergence to a finite peak. This
    is the measured behaviour: a LARGE but FINITE violation, ~10× at 75 K
    (Crossno 2016) and >200× in ultra-clean samples (Majumdar 2025). The
    standard finite-density-regularized two-channel form (κ ∝ 1/(n² + n₀²))
    gives

        L/L₀(n) = 1 + (R_peak − 1) · n₀² / (n² + n₀²),

    which equals R_peak at the neutrality point (n = 0) and recovers the
    Wiedemann–Franz value L/L₀ → 1 (Fermi-liquid regime) as |n| ≫ n₀.

    Dimensionless BY CONSTRUCTION: n and n_0 enter only through the ratio
    n/n_0, so the result carries no Lorenz-number units. (The Lorenz NUMBER
    L = κ/(σT) itself has units [V²/K²] = [W·Ω·K⁻²] — see the module
    constant ``L_LORENZ_SOMMERFELD``; only the ratio L/L₀ is dimensionless.
    The prior version conflated the two and claimed L was dimensionless.)

    Args:
        n: carrier density (any units, consistent with ``n_0``) [m⁻²].
        n_0: intrinsic/disorder regularizing carrier density, > 0 (same
            units as ``n``) [m⁻²]. The charge-puddle rms + thermal density
            scale — a microscopic (sample-dependent) INPUT, not predicted by
            the EFT (cf. σ_Q, which the CGL/FDR framework also takes as an
            input rather than deriving).
        lorenz_peak_ratio: R_peak = L/L₀ at charge neutrality — the measured
            peak violation (e.g. ~10 for Crossno 2016 at 75 K, >200 for the
            ultra-clean Majumdar 2025 samples). > 1 for a WF violation.

    Returns:
        L/L₀(n): the dimensionless Wiedemann–Franz violation ratio. Finite
        for every n, equal to ``lorenz_peak_ratio`` at n = 0 and → 1 as
        |n| → ∞.

    Lean: pending (DiracFluidFDR.lean)
    Source: Lucas & Fong, J. Phys.: Condens. Matter 30, 053001 (2018), §3
        (two-channel hydrodynamic transport); Crossno et al., Science 351,
        1058 (2016) (first WF-violation measurement, ~10×); Majumdar et al.,
        Nat. Phys. 21, 1374 (2025) (>200× in ultra-clean graphene).
    """
    if n_0 <= 0:
        raise ValueError("n_0 (regularizing carrier density) must be > 0")
    x_sq = (n / n_0) ** 2
    return 1.0 + (lorenz_peak_ratio - 1.0) / (1.0 + x_sq)
