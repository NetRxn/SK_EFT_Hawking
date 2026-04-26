"""Horizon spectrum + falsifier-instance status reports.

Bridges the Lean tracked-hypothesis bundle `H_HorizonBoundaryCondition`
to numerical instance evaluation. For each named MTC:

- Computes log d_max (the F2 area-law leading coefficient anchor).
- Tabulates F1-F5 falsifier-instance status:
    F1 (positivity)         — universal (passes by construction)
    F2 (area-law κ > 0)     — fails iff abelian (log d_max = 0)
    F3 (2nd-law monotonicity) — universal
    F4 (modular invariance) — testable per formalized MTC module
    F5 (anomaly match)      — conjectural across all MTCs (Walker-Wang inflow
                                from ADW Z₂ time-reversal)

Lean cross-references:
- `BHEntropyMicroscopic.HorizonMTCBC` (data carrier)
- `BHEntropyMicroscopic.H_HorizonBoundaryCondition` (Prop bundle)
- `*_falsifier_positivity` ... `*_falsifier_anomalyMatch` (5 falsifier theorems)
"""

from __future__ import annotations

from dataclasses import dataclass, field

from src.core.constants import BH_ENTROPY_PARAMS
from src.core.formulas import mtc_horizon_falsifier_status, mtc_area_law_kappa


@dataclass(frozen=True)
class HorizonMTCInstance:
    """Concrete MTC at the horizon for falsifier-status evaluation."""

    name: str
    num_objects: int
    log_d_max: float
    global_dim_squared: float
    chiral_c_minus_mod8: float | None
    quantum_dimensions: tuple
    is_abelian: bool
    falsifier_status: dict = field(default_factory=dict)


def fibonacci_instance() -> HorizonMTCInstance:
    """Fibonacci MTC instance: 2 anyons {1, τ}, d = {1, φ}, D² = 1 + φ²."""
    inst = HorizonMTCInstance(
        name="Fibonacci",
        num_objects=2,
        log_d_max=BH_ENTROPY_PARAMS["FIBONACCI_LOG_D_MAX"],
        global_dim_squared=BH_ENTROPY_PARAMS["FIBONACCI_GLOBAL_DIM_SQ"],
        chiral_c_minus_mod8=14 / 5,
        quantum_dimensions=(1.0, BH_ENTROPY_PARAMS["FIBONACCI_PHI"]),
        is_abelian=False,
        falsifier_status=mtc_horizon_falsifier_status("Fibonacci"),
    )
    return inst


def ising_instance() -> HorizonMTCInstance:
    """Ising MTC instance: 3 anyons {1, σ, ψ}, d = {1, √2, 1}, D² = 4."""
    return HorizonMTCInstance(
        name="Ising",
        num_objects=3,
        log_d_max=BH_ENTROPY_PARAMS["ISING_LOG_D_MAX"],
        global_dim_squared=BH_ENTROPY_PARAMS["ISING_GLOBAL_DIM_SQ"],
        chiral_c_minus_mod8=BH_ENTROPY_PARAMS["ISING_EDGE_C_MOD8"],
        quantum_dimensions=(1.0, BH_ENTROPY_PARAMS["ISING_D_SIGMA"], 1.0),
        is_abelian=False,
        falsifier_status=mtc_horizon_falsifier_status("Ising"),
    )


def toric_code_instance() -> HorizonMTCInstance:
    """Toric code D(Z_2): 4 anyons {1, e, m, ψ}, d = (1,1,1,1), D² = 4."""
    return HorizonMTCInstance(
        name="ToricCode",
        num_objects=4,
        log_d_max=BH_ENTROPY_PARAMS["TORIC_CODE_LOG_D_MAX"],
        global_dim_squared=BH_ENTROPY_PARAMS["TORIC_CODE_GLOBAL_DIM_SQ"],
        chiral_c_minus_mod8=0.0,
        quantum_dimensions=(1.0, 1.0, 1.0, 1.0),
        is_abelian=True,
        falsifier_status=mtc_horizon_falsifier_status("ToricCode"),
    )


def ds3_instance() -> HorizonMTCInstance:
    """D(S₃): 8 non-abelian anyons; d = (1,1,2,3,3,2,2,2); D² = 36."""
    return HorizonMTCInstance(
        name="DS3",
        num_objects=8,
        log_d_max=BH_ENTROPY_PARAMS["DS3_LOG_D_MAX"],
        global_dim_squared=BH_ENTROPY_PARAMS["DS3_GLOBAL_DIM_SQ"],
        chiral_c_minus_mod8=0.0,
        quantum_dimensions=(1.0, 1.0, 2.0, 3.0, 3.0, 2.0, 2.0, 2.0),
        is_abelian=False,
        falsifier_status=mtc_horizon_falsifier_status("DS3"),
    )


def su2k_instance(k: int) -> HorizonMTCInstance:
    """SU(2)_k MTC instance for level k.

    Quantum dims d_j = sin((2j+1)π/(k+2)) / sin(π/(k+2)), j = 0, ..., k.
    log d_max = log(d_{floor(k/2)}) (the largest quantum dim is at j ≈ k/2).
    """
    import numpy as np

    if k < 1:
        raise ValueError(f"SU(2)_k requires k >= 1 (got {k})")
    j = np.arange(k + 1)
    denom = np.sin(np.pi / (k + 2))
    d = np.sin((j + 1) * np.pi / (k + 2)) / denom
    d_max = float(np.max(d))
    log_d_max = float(np.log(d_max))
    D2 = float(np.sum(d ** 2))
    is_abelian = bool(k == 1)  # k=1 has only j=0, j=1/2 with d=1 each
    quantum_dims = tuple(float(x) for x in d)
    return HorizonMTCInstance(
        name=f"SU(2)_{k}",
        num_objects=k + 1,
        log_d_max=log_d_max,
        global_dim_squared=D2,
        chiral_c_minus_mod8=float(3 * k / (k + 2)),
        quantum_dimensions=quantum_dims,
        is_abelian=is_abelian,
        falsifier_status=mtc_horizon_falsifier_status("SU2k", log_d_max=log_d_max),
    )


def falsifier_status_table() -> dict:
    """Tabulate F1-F5 falsifier status across the Wave 3 MTC zoo.

    Returns
    -------
    dict
        {mtc_name: {F1_positivity, F2_areaLeading, F3_secondLaw,
                    F4_modularInvariance, F5_anomalyMatch, log_d_max,
                    kappa, is_abelian}}.
    """
    table = {}
    for inst in [
        fibonacci_instance(),
        ising_instance(),
        toric_code_instance(),
        ds3_instance(),
        su2k_instance(2),
        su2k_instance(3),
        su2k_instance(4),
        su2k_instance(10),
    ]:
        kappa = mtc_area_law_kappa(inst.log_d_max)
        table[inst.name] = {
            **inst.falsifier_status,
            "log_d_max": inst.log_d_max,
            "kappa": kappa,
            "is_abelian": inst.is_abelian,
        }
    return table
