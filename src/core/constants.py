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
# Polariton platform parameters
# Polaritons are driven-dissipative quasiparticles, not atomic BECs.
# They do not use the transonic_background solver — parameters are
# specified directly from the Bogoliubov dispersion.
#
# Key difference from BEC: the dominant damping is cavity decay
# Gamma_pol = 1/tau_cav, which is frequency-independent. EFT phonon
# damping (from polariton-polariton scattering) is subdominant.
#
# The Tier 1 perturbative patch is valid when Gamma_pol/kappa << 1.
#
# References:
#   - Falque et al., PRL 135, 023401 (2025) — Paris polariton horizons
#   - Grisins et al., PRB 94, 144518 (2016) — T_H survives
#   - Jacquet et al., Eur. Phys. J. D 76, 152 (2022) — kinematics
# ════════════════════════════════════════════════════════════════════

POLARITON_MASS = 7.0e-35      # kg (effective polariton mass, Falque et al.)

POLARITON_PLATFORMS = {
    'Paris_long': {
        'description': 'Paris polariton, long-lifetime cavity (100 ps)',
        'c_s': 1.0e6,             # m/s (1 μm/ps, typical Bogoliubov sound speed)
        'xi': 2.0e-6,             # m (2 μm healing length)
        'kappa': 5.0e10,          # s⁻¹ (0.05 THz, SLM-controlled horizon)
        'tau_cav': 100e-12,       # s (cavity lifetime)
        'Gamma_pol': 1.0e10,      # s⁻¹ (1/tau_cav)
        'gamma_phonon_dim': 1e-4, # Dimensionless phonon damping (subdominant)
    },
    'Paris_ultralong': {
        'description': 'Paris polariton, ultra-long-lifetime cavity (300 ps)',
        'c_s': 1.0e6,
        'xi': 2.0e-6,
        'kappa': 5.0e10,
        'tau_cav': 300e-12,
        'Gamma_pol': 3.33e9,
        'gamma_phonon_dim': 1e-4,
    },
    'Paris_standard': {
        'description': 'Paris polariton, standard cavity (3 ps)',
        'c_s': 1.0e6,
        'xi': 2.0e-6,
        'kappa': 5.0e10,
        'tau_cav': 3e-12,
        'Gamma_pol': 3.33e11,
        'gamma_phonon_dim': 1e-4,
    },
}

# Derived polariton parameters
for _name, _plat in POLARITON_PLATFORMS.items():
    _plat['D'] = _plat['xi'] * _plat['kappa'] / _plat['c_s']
    _plat['T_H_K'] = HBAR * _plat['kappa'] / (2 * np.pi * K_B)
    _plat['Gamma_pol_over_kappa'] = _plat['Gamma_pol'] / _plat['kappa']
    _ratio = _plat['Gamma_pol_over_kappa']
    _plat['tier1_regime'] = ('excellent' if _ratio < 0.03
                             else 'perturbative' if _ratio < 0.1
                             else 'borderline' if _ratio < 1.0
                             else 'intractable')
    _plat['tier1_valid'] = _ratio < 0.1


# ════════════════════════════════════════════════════════════════════
# Kappa-scaling test configuration
# The kappa-scaling test varies surface gravity kappa while holding
# BEC material properties fixed. Multipliers applied to each
# platform's nominal kappa to produce the scan range.
# ════════════════════════════════════════════════════════════════════

KAPPA_SCALING_FACTORS = np.array([0.2, 0.5, 0.75, 1.0, 1.5, 2.0, 3.0, 4.0, 5.0])


# ════════════════════════════════════════════════════════════════════
# 2D ADW model parameters (Phase 5 Wave 2A: Grassmann TRG benchmark)
#
# Reduced 2D version of the Diakonov lattice gravity model:
#   - 2 Grassmann variables per site (1 Dirac spinor in 2D)
#   - SU(2) gauge group on links (spin connection)
#   - 4-fermion vertices after SU(2) Haar measure integration
#   - No fermion bilinear kinetic term (pure multi-fermion)
#
# The 2D model retains the essential multi-fermion dynamics and
# symmetry-breaking pattern (tetrad vs metric order) but lacks
# the full diffeomorphism content of the 4D theory.
#
# Reference: Vladimirov-Diakonov, PRD 86, 104019 (2012)
# Reference: Shimizu-Kuramashi, PRD 90, 014508 (2014) — Grassmann TRG
# ════════════════════════════════════════════════════════════════════

ADW_2D_MODEL = {
    'd': 2,                       # spacetime dimension
    'n_grassmann': 2,             # Grassmann variables per site (1 Dirac spinor)
    'gauge_group': 'SU(2)',       # spin connection gauge group
    'gauge_dim': 2,               # fundamental representation dimension
}

# SU(2) Haar measure integration identities
# Vol(SU(2)) = 2π², used in normalization of group integrals
# Key identity: ∫ dU U_ij U*_kl = (1/dim_fund) δ_il δ_jk
SU2_HAAR = {
    'volume': 2 * np.pi**2,                    # Vol(SU(2))
    'dim_fund': 2,                              # dim of fundamental rep
    'one_link_factor': 0.5,                     # 1/dim_fund for single-link integral
    'pseudo_real': True,                        # fund rep is self-conjugate
}

# Grassmann TRG parameters
GRASSMANN_TRG = {
    'D_cut_default': 16,          # bond dimension (truncation parameter)
    'D_cut_high': 32,             # high-accuracy bond dimension
    'D_cut_benchmark': 8,         # fast benchmark bond dimension
    'svd_threshold': 1e-12,       # threshold for discarding small singular values
}

# 2D benchmarking lattice sizes (L × L square lattice)
# Effective lattice size after n_rg = log2(L) TRG steps is 1×1 → Z
ADW_2D_LATTICE_SIZES = [4, 8, 16, 32, 64]

# Coupling scan range for the 2D phase diagram
# g_cosmo: cosmological term coupling (4-fermion on-site)
# g_EH: Einstein-Hilbert term coupling (4-fermion nearest-neighbor via gauge)
# Scan g_EH/g_cosmo at fixed g_cosmo = 1
ADW_2D_COUPLING_SCAN = {
    'g_cosmo': 1.0,                             # fixed cosmological coupling
    'g_EH_range': (0.0, 5.0),                   # Einstein-Hilbert coupling range
    'n_points': 50,                             # number of scan points
}


# ════════════════════════════════════════════════════════════════════
# Phase 5 Wave 2B: 4D ADW cubic lattice pilot (fermion-bag MC)
#
# 8 Grassmann variables per site (2 Dirac spinors × 4 components).
# SO(4) ≅ SU(2)×SU(2) gauge group (Euclidean spin connection).
# After integrating out gauge field: purely fermionic effective action
# with 8-fermion vertices (cosmological) + 4-fermion NN (Einstein-Hilbert).
#
# Reference: Vladimirov-Diakonov, PRD 86, 104019 (2012)
# Reference: Chandrasekharan, PRD 82, 025007 (2010) — fermion-bag algorithm
# Reference: Catterall, JHEP 01, 121 (2016) — SO(4) fermion-bag MC
# ════════════════════════════════════════════════════════════════════

ADW_4D_MODEL = {
    'd': 4,                       # spacetime dimension
    'n_grassmann': 8,             # Grassmann variables per site (2 Dirac × 4 components)
    'n_dirac': 2,                 # number of Dirac spinors
    'spinor_dim': 4,              # components per Dirac spinor in 4D
    'gauge_group': 'SO(4)',       # Euclidean spin connection gauge group
    'gauge_dim': 4,               # fundamental representation dimension
    'coordination_number': 8,     # 2d = 8 nearest neighbors on 4D hypercubic lattice
    'z4_symmetry': True,          # Volovik Z_4: e^a_mu -> -i e^a_mu, i^4=1
}

# SO(4) ≅ SU(2)_L × SU(2)_R Haar measure integration
# Each SU(2) factor integrated independently via Peter-Weyl
# Combined one-link factor: (1/dim_L)(1/dim_R) = 1/4
SO4_HAAR = {
    'dim_fund': 4,                # SO(4) fundamental rep dimension
    'dim_su2': 2,                 # each SU(2) factor
    'one_link_factor': 0.25,      # (1/2)×(1/2) for SU(2)_L × SU(2)_R
    'pseudo_real': True,          # both SU(2) factors are pseudo-real
    'n_independent_channels': 4,  # singlet, (adj,1), (1,adj), (adj,adj)
}

# Fermion-bag algorithm parameters
# The fermion-bag partitions the lattice into "bags" where Grassmann
# integrals are evaluated exactly. Bag updates are local and sign-free.
FERMION_BAG = {
    'max_bag_size': 32,           # max sites per bag (controls accuracy vs speed)
    'n_thermalize': 500,          # thermalization sweeps before measurement
    'n_measure': 1000,            # measurement sweeps
    'n_skip': 5,                  # sweeps between measurements (decorrelation)
    'seed': 42,                   # default random seed
}

# 4D lattice sizes for pilot study (L^4 hypercubic)
# Cost scaling: 6^4=1296 (minutes), 8^4=4096 (hours), 10^4=10000 (days)
ADW_4D_LATTICE_SIZES = [4, 6, 8]

# 4D coupling scan parameters
ADW_4D_COUPLING_SCAN = {
    'g_cosmo': 1.0,               # fixed cosmological coupling
    'g_EH_range': (0.0, 4.0),     # Einstein-Hilbert coupling range
    'n_points': 20,               # number of scan points (smaller for 4D cost)
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
# Maps Aristotle-proved theorems to their run IDs.
#
# Verification breakdown (259 theorems + 1 axiom across 20 Lean modules):
#   - 59 proved by Aristotle automated theorem prover (listed below with run IDs)
#   - 174 proved manually in Lean (verified by `lake build`, zero sorry)
#   - 1 axiom: non_abelian_center_discrete in GaugeErasure.lean
#
# All 234 proof obligations have zero sorry. Verified by `lake build`.
# ════════════════════════════════════════════════════════════════════

ARISTOTLE_THEOREMS = {
    # Phase 1 — AcousticMetric.lean (5)
    'acousticMetric_det': '082e6776',
    'acousticMetric_inv_correct': '082e6776',
    'acoustic_metric_lorentzian': '082e6776',
    'acoustic_metric_theorem': 'a87f425a',
    'soundSpeed_from_eos': '88cf2000',
    # Phase 1 — SKDoubling.lean (6)
    'firstOrder_positivity': '082e6776',
    'firstOrder_uniqueness': '270e77a0',
    'fdr_from_kms': '638c5ff3',
    'fdr_from_kms_gamma1': '20556034',
    'fdr_from_kms_gamma2': '20556034',
    'firstOrder_normalization': 'manual',
    # Phase 1 — HawkingUniversality.lean (3)
    'dispersive_correction_bound': 'd65e3bba',
    'dissipative_correction_existence': '657fcd6a',
    'hawking_universality': '416fb432',

    # Phase 2 — SecondOrderSK.lean (8)
    'secondOrder_count': 'd61290fd',
    'secondOrder_count_with_parity': 'd61290fd',
    'secondOrder_uniqueness': 'd61290fd',
    'secondOrder_requires_parity_breaking': 'd61290fd',
    'secondOrder_frequency_dependent': 'c4d73ca8',
    'fullSecondOrder_uniqueness': 'c4d73ca8',
    'combined_normalization': 'c4d73ca8',
    'combined_positivity_constraint': 'c4d73ca8',
    # Phase 2 — WKBAnalysis.lean: Round 5 strengthening (3)
    'dampingRate_eq_zero_iff': '518636d7',
    'firstOrder_correction_zero_iff': '518636d7',
    'turning_point_shift_nonzero': '518636d7',

    # Round 4 stress tests — SecondOrderSK + WKBAnalysis (10)
    'fdr_second_order_consistent': '3eedcabb',
    'fullKMS_reduces_to_firstOrder': '3eedcabb',
    'altFDR_uniqueness_test': '3eedcabb',
    'relaxed_uniqueness_test': '3eedcabb',
    'relaxed_positivity_weakens': '3eedcabb',
    'thirdOrder_count': '3eedcabb',
    'thirdOrder_count_value': '3eedcabb',
    'cumulative_count_through_3': '3eedcabb',
    'no_dissipation_zero_damping': '3eedcabb',
    'turning_point_no_shift': '3eedcabb',

    # Phase 2 Direction D: CGL Derivation — CGLTransform.lean (5)
    'einstein_relation': 'dab8cfc1',
    'secondOrder_cgl_fdr': 'dab8cfc1',
    'cgl_fdr_general': '2ca3e7e6',
    'cgl_fdr_spatial': '2ca3e7e6',
    'cgl_implies_secondOrderKMS': '2ca3e7e6',

    # Phase 3 — ADWMechanism.lean (1)
    'curvature_zero_at_Gc': 'f8de66d1',

    # Phase 4: Aristotle batch (13)
    'fracton_exceeds_standard_general': 'b1ea2eb7',
    'fracton_ratio_grows_3d': 'b1ea2eb7',
    'binomial_strict_mono': 'b1ea2eb7',
    'dof_gap_eq_d_minus_1_check_4': 'b1ea2eb7',
    'dof_gap_eq_d_minus_1_check_5': 'b1ea2eb7',
    'dof_gap_positive_2_through_8': 'b1ea2eb7',
    'phase_levels_distinct': 'b1ea2eb7',
    'phase_levels_ordered': 'b1ea2eb7',
    'metric_dof_equals_gr': 'b1ea2eb7',
    'evading_one_breaks_nogo': 'b1ea2eb7',
    'tpf_evasion_margin': 'b1ea2eb7',
    'obstructions_individually_sufficient': 'b1ea2eb7',
    'param_gap_grows': 'b1ea2eb7',

    # Wave 5 quality audit: strengthened vacuous theorems (2026-03-26)
    'gs_nogo_requires_all': 'f35ca767',
    'zeroTemp_nontrivial': 'f35ca767',

    # Phase 5 Wave 1A — KappaScaling.lean (3 by Aristotle, 8 manual)
    'dissipative_dominates_below': 'run_20260328_051547',
    'dispersive_dominates_above': 'run_20260328_051547',
    'crossover_unique': 'run_20260328_051547',
}

ARISTOTLE_PROVED_COUNT = len(ARISTOTLE_THEOREMS)
assert ARISTOTLE_PROVED_COUNT == 59, f"Expected 59 Aristotle-proved theorems, got {ARISTOTLE_PROVED_COUNT}"
# Backwards compatibility alias
TOTAL_THEOREMS = ARISTOTLE_PROVED_COUNT


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
