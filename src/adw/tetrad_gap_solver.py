"""Scalar NJL gap curves with finite-precision failure propagation.

The integral model shares a threshold, not the positive roots of the
regulated scalar potential. Microscopic ADW identification is uncomputed.
Conditional vestigial metadata below remains a separate model component;
no new physical phase, native result or figure acceptance is supplied.
"""

import numpy as np
from dataclasses import dataclass

from src.core.formulas import (
    tetrad_critical_coupling_integral,
    tetrad_gap_integral,
    tetrad_gap_solution,
    adw_critical_coupling,
    adw_vestigial_critical_coupling,
    adw_quartic_coupling_metric,
    adw_bubble_integral,
)
from src.core.constants import ADW_VESTIGIAL


@dataclass
class GapCurveResult:
    """Result of computing the Δ*(G) curve.

    Attributes:
        G_values: Array of coupling values
        Delta_values: Array of gap solutions Δ*(G)
        G_c: Critical coupling
        Lambda: UV cutoff
        N_f: Number of Dirac fermion species
    """
    G_values: np.ndarray
    Delta_values: np.ndarray
    G_c: float
    Lambda: float
    N_f: int


@dataclass
class PhaseDiagramResult:
    """Phase diagram from the gap equation.

    Attributes:
        gap_curve: The Δ*(G) curve
        G_ves: Vestigial critical coupling (metric orders before tetrad)
        vestigial_window: G_ves < G < G_c (may be exponentially narrow)
        G_c: Tetrad critical coupling
    """
    gap_curve: GapCurveResult
    G_ves: float | None
    vestigial_window: float
    G_c: float


def compute_gap_curve(
    Lambda: float,
    N_f: int = 2,
    G_min_ratio: float = 0.01,
    G_max_ratio: float = 10.0,
    n_points: int = 200,
) -> GapCurveResult:
    """Sample scalar NJL roots; propagate any canonical numerical refusal.

    Nonnegative finite ordered ratios, including zero/equal ranges, and
    positive integer counts including one are valid. No quadrature estimate
    is formed here. Positive endpoint products must be representable.
    Above-cutoff roots are mathematical continuation, not UV/ADW validation.
    """
    from src.core.formulas import _tetrad_njl_real, _tetrad_njl_count, _tetrad_njl_product

    G_min_ratio = _tetrad_njl_real(G_min_ratio, "G_min_ratio")
    G_max_ratio = _tetrad_njl_real(G_max_ratio, "G_max_ratio")
    n_points = _tetrad_njl_count(n_points, "n_points")
    if G_max_ratio < G_min_ratio:
        raise ValueError("coupling ratio range must be ordered")
    G_c = tetrad_critical_coupling_integral(Lambda, N_f)
    G_min = (0.0 if G_min_ratio == 0 else
             _tetrad_njl_product((G_min_ratio, G_c), (), "minimum coupling"))
    G_max = (0.0 if G_max_ratio == 0 else
             _tetrad_njl_product((G_max_ratio, G_c), (), "maximum coupling"))
    G_values = np.linspace(G_min, G_max, n_points)
    Delta_values = np.array([tetrad_gap_solution(G, Lambda, N_f) for G in G_values])
    return GapCurveResult(G_values=G_values, Delta_values=Delta_values,
                          G_c=G_c, Lambda=Lambda, N_f=N_f)


def compute_phase_diagram(
    Lambda: float = ADW_VESTIGIAL['Lambda'],
    N_f: int = ADW_VESTIGIAL['N_f'],
    n_points: int = 200,
) -> PhaseDiagramResult:
    """Compute the full phase diagram: gap curve + vestigial window.

    The vestigial critical coupling G_ves is computed from the RPA
    metric susceptibility (using the analytical result from
    VestigialSusceptibility.lean).

    Args:
        Lambda: UV cutoff (default from ADW_VESTIGIAL constants)
        N_f: Dirac fermion species (default from ADW_VESTIGIAL constants)
        n_points: Points in the gap curve

    Returns:
        PhaseDiagramResult with gap curve and vestigial window
    """
    G_c = tetrad_critical_coupling_integral(Lambda, N_f)
    gap_curve = compute_gap_curve(Lambda, N_f, n_points=n_points)

    # Vestigial window from RPA susceptibility
    u_g = adw_quartic_coupling_metric(N_f)
    G_ves = None
    vestigial_window = 0.0

    if u_g > 0:
        c_D = ADW_VESTIGIAL.get('c_D', 2 * ADW_VESTIGIAL['D']**2)
        try:
            G_ves = adw_vestigial_critical_coupling(G_c, u_g, c_D, Lambda)
            vestigial_window = G_c - G_ves
        except (ValueError, ZeroDivisionError):
            pass

    return PhaseDiagramResult(
        gap_curve=gap_curve,
        G_ves=G_ves,
        vestigial_window=vestigial_window,
        G_c=G_c,
    )


def cross_validate_Gc(
    Lambda: float = ADW_VESTIGIAL['Lambda'],
    N_f: int = ADW_VESTIGIAL['N_f'],
) -> dict:
    """Compare threshold coefficients only, not full models or positive roots.

    Returns:
        Dict with both G_c values and their ratio
    """
    Gc_int = tetrad_critical_coupling_integral(Lambda, N_f)
    Gc_veff = adw_critical_coupling(Lambda, N_f)
    return {
        'G_c_integral': Gc_int,
        'G_c_veff': Gc_veff,
        'ratio': Gc_int / Gc_veff if Gc_veff != 0 else float('inf'),
        'match': abs(Gc_int - Gc_veff) < 1e-10,
        'Lambda': Lambda,
        'N_f': N_f,
    }


def gap_vs_vladimirov_diakonov(Lambda: float, N_f: int = 2) -> dict:
    """Compare 4D gap equation result with Vladimirov-Diakonov 2D result.

    VD found critical coupling |λ₂| ≈ 8.69|λ₁| in 2D for the chiral channel.
    Our 4D tetrad G_c = 8π²/(N_f·Λ²) should be O(1) in lattice units (Λ = π).

    Returns:
        Dict with G_c in lattice units and comparison
    """
    G_c = tetrad_critical_coupling_integral(Lambda, N_f)
    G_c_lattice = G_c * Lambda**2  # G_c in units of Λ⁻²

    return {
        'G_c': G_c,
        'G_c_lattice_units': G_c_lattice,
        'is_order_one': 0.1 < G_c_lattice < 100,
        'VD_2D_ratio': 8.69,  # Vladimirov-Diakonov 2D critical ratio
        'Lambda': Lambda,
        'N_f': N_f,
    }
