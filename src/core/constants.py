"""
Single source of truth for physical constants, experimental parameters,
and the Plotly color palette used across the SK-EFT Hawking project.

Every notebook, source module, and test should import from here —
no hardcoded constants elsewhere in the codebase.

Constants follow CODATA 2018 / SI 2019 exact values where applicable.
Atomic data from NIST Atomic Weights and Isotopic Compositions.

Design decisions:
    - We keep ALL experimental parameters in one place so that a single
      correction propagates everywhere automatically.
    - Densities are quasi-1D linear densities [m⁻¹], NOT 3D volume
      densities [m⁻³]. The coupling g₁D and sound speed c_s are computed
      from these in BECParameters.__post_init__().
    - The color palette matches the Phase 1 paper figures and is used
      consistently across all notebooks and visualizations.
"""

import numpy as np


# ════════════════════════════════════════════════════════════════════
# Fundamental physical constants (CODATA 2018 exact values)
# ════════════════════════════════════════════════════════════════════

HBAR = 1.054571817e-34    # Reduced Planck constant [J·s]
K_B = 1.380649e-23        # Boltzmann constant [J/K] (exact in SI 2019)
A_BOHR = 5.29177210903e-11  # Bohr radius [m]


# ════════════════════════════════════════════════════════════════════
# Atomic species data
# Each entry: mass [kg], scattering length [m]
# Sources: NIST, Kempen et al. (2002) for Rb, Falke et al. (2008) for K
# ════════════════════════════════════════════════════════════════════

ATOMS = {
    'Rb87': {
        'label': '⁸⁷Rb',
        'mass': 1.443160648e-25,    # kg (86.909180531 u)
        'a_s': 5.77e-9,             # m (≈ 109 a₀, triplet s-wave)
    },
    'K39': {
        'label': '³⁹K',
        'mass': 6.470076e-26,       # kg (38.96370668 u)
        'a_s': 50e-9,               # m (tunable via Feshbach at 402 G)
    },
    'Na23': {
        'label': '²³Na',
        'mass': 3.8175458e-26,      # kg (22.9897692820 u)
        'a_s': 2.75e-9,             # m (≈ 52 a₀, triplet s-wave)
    },
}


# ════════════════════════════════════════════════════════════════════
# Experimental configurations
# Each entry defines the BEC parameters for a specific experiment.
# Densities are quasi-1D linear densities [m⁻¹].
#
# Note: these parameters, combined with the transonic_background solver,
# fully determine κ, c_s, ξ, D, T_H for each experiment.
# ════════════════════════════════════════════════════════════════════

EXPERIMENTS = {
    'Steinhauer': {
        'description': 'Steinhauer ⁸⁷Rb BEC (Nature Physics 2016)',
        'atom': 'Rb87',
        'density_upstream': 5e7,       # m⁻¹ (quasi-1D linear density)
        'velocity_upstream': 0.85e-3,  # m/s (Mach ~ 0.74)
        'omega_perp': 2 * np.pi * 500, # rad/s (transverse trap)
    },
    'Heidelberg': {
        'description': 'Heidelberg ³⁹K BEC (projected)',
        'atom': 'K39',
        'density_upstream': 3e7,       # m⁻¹
        'velocity_upstream': 3.0e-3,   # m/s (Mach ~ 0.77)
        'omega_perp': 2 * np.pi * 500, # rad/s
    },
    'Trento': {
        'description': 'Trento ²³Na spin-sonic BEC (projected)',
        'atom': 'Na23',
        'density_upstream': 1e8,       # m⁻¹
        'velocity_upstream': 1.6e-3,   # m/s (Mach ~ 0.73)
        'omega_perp': 2 * np.pi * 500, # rad/s
    },
}


# ════════════════════════════════════════════════════════════════════
# Plotly color palette (consistent across all figures)
# ════════════════════════════════════════════════════════════════════

COLORS = {
    'Steinhauer': '#2E86AB',   # steel blue
    'Heidelberg': '#A23B72',   # berry
    'Trento': '#F18F01',       # amber
}


# ════════════════════════════════════════════════════════════════════
# Lean verification registry
# Maps each theorem to its Aristotle run ID and status.
# 40/40 proved, 0 sorry remaining.
# ════════════════════════════════════════════════════════════════════

ARISTOTLE_THEOREMS = {
    # Phase 1 (14)
    'acoustic_metric_determinant': '082e6776',
    'acoustic_metric_inverse': '082e6776',
    'lorentzian_signature': '082e6776',
    'phonon_eom': '082e6776',
    'metric_conformal_factor': 'a87f425a',
    'penrose_diagram_structure': 'a87f425a',
    'sk_positivity': 'a87f425a',
    'firstOrder_uniqueness': 'a87f425a',
    'fdr_from_kms': 'a87f425a',
    'dispersive_bound': 'a87f425a',
    'dissipative_existence': '270e77a0',
    'combined_universality': '270e77a0',
    'kms_optimal': '270e77a0',
    'hawking_temp_universal': '270e77a0',

    # Phase 2 (8)
    'secondOrder_count': 'd61290fd',
    'counting_formula_N2': 'd61290fd',
    'counting_formula_N3': 'd61290fd',
    'full_kms_structure': 'd61290fd',
    'combined_positivity_constraint': 'c4d73ca8',
    'dampingRate_eq_zero_iff': '518636d7',
    'firstOrder_correction_zero_iff': '518636d7',
    'turning_point_shift_nonzero': '518636d7',

    # Round 5 stress tests (13)
    'fdr_sign_flip_breaks_positivity': '3eedcabb',
    'kms_structure_optimal_no_extra': '3eedcabb',
    'relaxed_kms_has_extra_coefficients': '3eedcabb',
    'spatial_parity_eliminates_second_order': '3eedcabb',
    'parity_null_test': '3eedcabb',
    'second_order_requires_broken_parity': '3eedcabb',
    'dispersive_bound_tight': '3eedcabb',
    'spectral_distortion_formula_matches': '3eedcabb',
    'cross_term_bounds': '3eedcabb',
    'dampingRate_eq_zero_iff_strengthened': '518636d7',
    'firstOrder_correction_zero_iff_strengthened': '518636d7',
    'turning_point_shift_nonzero_strengthened': '518636d7',
    'effective_temperature_well_defined': '518636d7',

    # Direction D: CGL Derivation (5)
    'einstein_relation': 'dab8cfc1',
    'secondOrder_cgl_fdr': 'dab8cfc1',
    'cgl_fdr_general': '2ca3e7e6',
    'cgl_fdr_spatial': '2ca3e7e6',
    'cgl_implies_secondOrderKMS': '2ca3e7e6',
}

TOTAL_THEOREMS = len(ARISTOTLE_THEOREMS)
assert TOTAL_THEOREMS == 40, f"Expected 40 theorems, got {TOTAL_THEOREMS}"


# ════════════════════════════════════════════════════════════════════
# Helper: build BECParameters from the constants above
# ════════════════════════════════════════════════════════════════════

def get_bec_parameters(experiment_name: str):
    """
    Construct a BECParameters instance for the named experiment,
    using the centralized constants defined in this module.

    Args:
        experiment_name: One of 'Steinhauer', 'Heidelberg', 'Trento'.

    Returns:
        BECParameters with all fields populated from single-source-of-truth.

    Raises:
        KeyError: If experiment_name is not recognized.
    """
    from src.core.transonic_background import BECParameters

    exp = EXPERIMENTS[experiment_name]
    atom = ATOMS[exp['atom']]

    return BECParameters(
        mass=atom['mass'],
        scattering_length=atom['a_s'],
        density_upstream=exp['density_upstream'],
        velocity_upstream=exp['velocity_upstream'],
        omega_perp=exp['omega_perp'],
    )


def get_all_experiments():
    """
    Return a dict mapping experiment names to (BECParameters, TransonicBackground)
    tuples, computed from the single-source-of-truth constants.

    This is the canonical way to get experimental parameters in notebooks.
    """
    from src.core.transonic_background import solve_transonic_background

    results = {}
    for name in EXPERIMENTS:
        params = get_bec_parameters(name)
        bg = solve_transonic_background(params)
        results[name] = (params, bg)
    return results
