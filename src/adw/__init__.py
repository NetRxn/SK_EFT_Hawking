"""Akama-Diakonov-Wetterich (ADW) Mean-Field Gap Equation.

Tests whether emergent spin-2 gravity can arise from spontaneous tetrad
condensation via the ADW mechanism applied to emergent Dirac fermions.

The calculation chain:
1. Start from Wen's lattice QED model producing emergent Dirac fermions
2. Add the ADW multi-fermion interaction (cosmological term)
3. Perform Hubbard-Stratonovich decomposition with tetrad auxiliary field
4. Integrate out fermions to get effective action S_eff[e]
5. Solve the saddle-point (gap) equation for tetrad VEV
6. Analyze fluctuations: count Nambu-Goldstone modes, identify graviton

Key results:
- Phase diagram: pre-geometric (e=0), vestigial metric (g!=0, e=0),
  full tetrad (e!=0) phases
- Critical coupling G_c = 8pi^2 / (N_f Lambda^2) for tetrad condensation
- Symmetry breaking L_c x L_s -> L_J produces 6 NG modes (absorbed by
  spin connection) + 10 physical DOF (2 massless graviton + 8 massive)
- Four structural obstacles for emergent fermion bootstrap

References:
    - Akama (1978): composite metric from fermion condensate
    - Diakonov (2011): fermionic cosmological term
    - Wetterich (2005): spinor gravity with vierbein as fermion bilinear
    - Vladimirov-Diakonov (2012): lattice mean-field phases
    - Volovik (2024): vestigial gravitational order
    - Maitiniyazi-Matsuzaki-Oda-Yamada (2024): irreversible vierbein postulate
    - Vergeles (2025): unitarity proof (fundamental Grassmann fields)
    - Wen (2006): emergent QED from string-net condensation

Lean formalization: ADWMechanism.lean
"""

from src.adw.wen_model import (
    WenRotorModel,
    EmergentQED,
    VelocityStructure,
    wen_coulomb_phase,
    herbut_terminal_velocity,
)

from src.adw.hubbard_stratonovich import (
    ADWAction,
    TetradField,
    HSDecomposition,
    adw_cosmological_term,
    hubbard_stratonovich_decompose,
    fermion_effective_action,
)

from src.adw.gap_equation import (
    GapEquationParams,
    TetradSolution,
    PhaseType,
    GapEquationResult,
    effective_potential,
    critical_coupling,
    solve_gap_equation,
    classify_phase,
    full_gap_analysis,
)

from src.adw.fluctuations import (
    SymmetryBreakingPattern,
    NGModeType,
    NGMode,
    FluctuationResult,
    lorentz_group_dimension,
    broken_generator_count,
    classify_ng_modes,
    vergeles_mode_counting,
    graviton_identification,
    structural_obstacles,
    full_fluctuation_analysis,
)

from src.adw.ginzburg_landau import (
    GLCoefficients,
    InvariantPolynomial,
    GLPhaseType,
    PhaseClassification,
    GLPhaseDiagram,
    He3Comparison,
    compute_gl_coefficients,
    invariant_polynomials,
    classify_gl_phases,
    compute_phase_diagram,
    he3_comparison,
    gl_free_energy_general,
    independent_invariant_count_real,
    independent_invariant_count_complex,
    FluctuationCorrection,
    compute_fluctuation_corrections,
)
