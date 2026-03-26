"""Chirality Wall Synthesis: TPF vs Golterman-Shamir Compatibility.

Formal analysis of whether the Thorngren-Preskill-Fidkowski (TPF) SPT slab
disentangler evades the Golterman-Shamir (GS) generalized no-go theorem
for chiral lattice fermions.

The analysis chain:
1. Extract GS no-go conditions (lattice translation invariance, finite-range
   Hamiltonian, relativistic continuum limit, complete interpolating fields)
2. Extract TPF construction ingredients (infinite-dimensional rotors,
   not-on-site symmetries, ancilla DOF, extra-dimensional SPT slab)
3. Formally check each GS condition against TPF construction
4. Identify the 4+1D gapped interface conjecture as the critical assumption
5. Assess: conditional breach — if conjecture proven, the wall falls

Key references:
    - Thorngren-Preskill-Fidkowski (Jan 2026): SPT slab disentangler
    - Golterman-Shamir (2024-2026): generalized no-go theorem
    - Butt-Catterall-Hasenfratz (PRL 2025): staggered fermion SMG
    - Hasenfratz-Witzel (Nov 2025): SMG with 16 Weyl fermions
    - Gioia-Thorngren (Mar 2025): topological constraints
    - Seifnashri (Jan 2026): symmetry TFT perspective

Lean: ChiralityWall.lean (planned)
"""

from src.chirality.tpf_gs_analysis import (
    EvasionVerdict,
    NoGoCondition,
    TPFIngredient,
    TPFConstruction,
    NumericalEvidence,
    WallStatus,
    CompatibilityResult,
    gs_conditions,
    tpf_construction,
    numerical_evidence,
    check_compatibility,
    chirality_wall_status,
    conditions_summary,
    evasion_count,
)
