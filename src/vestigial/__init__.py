"""Vestigial gravity simulation package.

Numerical test of Volovik's vestigial gravity via Monte Carlo simulation
of the ADW-type lattice model. Three phases are distinguished:

    Phase I  (pre-geometric):    <e> = 0,  <ee> = 0
    Phase II (vestigial metric): <e> = 0,  <ee> != 0
    Phase III (full tetrad):     <e> != 0, <ee> != 0

The vestigial phase is physically remarkable because it violates the
Equivalence Principle: the metric exists but the tetrad does not have
a VEV, so bosons and fermions experience different effective gravity.

Modules:
    lattice_model — Lattice Hamiltonian and coupling structure
    mean_field    — Extended mean-field with metric correlator
    monte_carlo   — Metropolis-Hastings sampler (Euclidean pilot)
    phase_diagram — Coupling scan and phase classification
"""

from src.vestigial.lattice_model import (
    LatticeParams,
    TetradSite,
    LatticeConfig,
    create_lattice,
    auxiliary_action,
    tetrad_order_parameter,
    metric_order_parameter,
)
from src.vestigial.mean_field import (
    MeanFieldParams,
    MeanFieldResult,
    mean_field_gap_equation,
    mean_field_metric_correlator,
    vestigial_phase_window,
)
from src.vestigial.monte_carlo import (
    MCParams,
    MCResult,
    metropolis_sweep,
    run_monte_carlo,
)
from src.vestigial.phase_diagram import (
    PhasePoint,
    PhaseDiagramResult,
    scan_coupling,
    classify_phase_point,
)
