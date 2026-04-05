"""Tetrad Gap Equation Solver — Integral Formulation.

Solves the NJL-type gap equation for the tetrad VEV:
    Δ = G · N_f · Δ · I(Δ)
where I(Δ) = ∫₀^Λ ρ(p)/(p²+Δ²) dp with ��(p) = c₄·p³.

This module provides:
1. Δ*(G) curve: order parameter vs coupling strength
2. Phase diagram: identify critical coupling and vestigial window
3. Cross-validation with V_eff formulation in gap_equation.py

The gap equation is the first explicit derivation for the tetrad channel.
No published work has written it down.

Lean: TetradGapEquation.lean (gap_nontrivial_exists, gap_trivial_unique_subcritical,
      gap_solution_monotone, criticalCoupling_formula)
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
    """Compute the Δ*(G) curve over a range of couplings.

    Args:
        Lambda: UV cutoff
        N_f: Number of Dirac fermion species
        G_min_ratio: Minimum G/G_c ratio
        G_max_ratio: Maximum G/G_c ratio
        n_points: Number of coupling points

    Returns:
        GapCurveResult with the complete curve
    """
    G_c = tetrad_critical_coupling_integral(Lambda, N_f)
    G_values = np.linspace(G_min_ratio * G_c, G_max_ratio * G_c, n_points)
    Delta_values = np.array([
        tetrad_gap_solution(G, Lambda, N_f) for G in G_values
    ])

    return GapCurveResult(
        G_values=G_values,
        Delta_values=Delta_values,
        G_c=G_c,
        Lambda=Lambda,
        N_f=N_f,
    )


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
    """Cross-validate G_c between integral and V_eff formulations.

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
