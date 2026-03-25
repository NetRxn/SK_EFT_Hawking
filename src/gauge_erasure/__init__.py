"""Non-Abelian Gauge Erasure Theorem.

Formalizes the universal structural argument that non-Abelian gauge degrees
of freedom cannot survive hydrodynamization, while U(1) gauge structure can.

The argument chain:
1. Higher-form symmetries must be Abelian (codimension >1 operators commute)
2. Non-Abelian gauge theories have at most discrete Z_N center symmetries
3. Z_N breaking → domain walls, not Goldstone bosons → no hydrodynamic modes
4. Universal across: standard hydro, fracton hydro, holographic hydro
5. U(1) exception: 1-form Goldstone mechanism (Grozdanov-Hofman-Iqbal)

Lean: GaugeErasure.lean
"""

from src.gauge_erasure.erasure_theorem import (
    GaugeGroup,
    HigherFormSymmetry,
    HydrodynamicFate,
    gauge_erasure_analysis,
    is_abelian,
    center_subgroup,
    higher_form_symmetry_type,
    goldstone_or_domain_wall,
    survives_hydrodynamization,
)
