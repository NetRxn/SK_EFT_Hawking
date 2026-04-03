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
        'a_s': 5.31e-9,             # m (100.4 a₀, F=2; van Kempen PRL 88, 093201)
    },
    'K39': {
        'label': '³⁹K',
        'mass': 6.470076e-26,       # kg (38.96370668 u)
        'a_s': 50e-9,               # m (tunable via Feshbach at 402 G; PROJECTED)
    },
    'Na23': {
        'label': '²³Na',
        'mass': 3.8175458e-26,      # kg (22.9897692820 u)
        'a_s': 2.75e-9,             # m (≈ 52 a₀, triplet; Tiesinga 1996)
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
        'description': 'Steinhauer ⁸⁷Rb BEC (Nature 2016/2019)',
        'atom': 'Rb87',
        'density_upstream': 5e7,       # m⁻¹ (quasi-1D, horizon region; Wang 2017 Fig.2)
        'velocity_upstream': 0.41e-3,  # m/s (Mach ~0.75 × c_s; DERIVED, see provenance)
        'omega_perp': 2 * np.pi * 123, # rad/s (Wang PRA 96, 023616, Table II: ν=123 Hz)
    },
    'Heidelberg': {
        'description': 'Heidelberg ³⁹K BEC (PROJECTED — no Hawking expt exists)',
        'atom': 'K39',
        'density_upstream': 3e7,       # m⁻¹ (PROJECTED)
        'velocity_upstream': 3.0e-3,   # m/s (PROJECTED)
        'omega_perp': 2 * np.pi * 500, # rad/s (PROJECTED — unsourced)
    },
    'Trento': {
        'description': 'Trento ²³Na spin-sonic BEC (PROJECTED — theoretical proposal)',
        'atom': 'Na23',
        'density_upstream': 1e8,       # m⁻¹ (PROJECTED)
        'velocity_upstream': 1.6e-3,   # m/s (PROJECTED)
        'omega_perp': 2 * np.pi * 500, # rad/s (PROJECTED — unsourced)
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
    'n_thermalize': 2500,         # thermalization sweeps before measurement
    'n_measure': 5000,            # measurement sweeps
    'n_skip': 5,                  # base decorrelation gap (scaled by L in runner)
    'seed': 42,                   # default random seed
}

# 4D lattice sizes (L^4 hypercubic)
# Cost scaling (vectorized, 10 cores): L=8 ~2min, L=12 ~30min, L=16 ~4-16h
ADW_4D_LATTICE_SIZES = [4, 6, 8, 10, 12, 14, 16]

# 4D coupling scan parameters (Binder crossing section)
# g_EH < 0 = attractive bonds (correct ADW physics: fermion hopping favors
# tetrad alignment). The product-form bond coupling is
# S_bond = -g_eff × (n_x/N)(n_y/N) where g_eff = g_EH/4.
ADW_4D_COUPLING_SCAN = {
    'g_cosmo': 1.0,               # fixed cosmological coupling
    'g_EH_range': (-50.0, 0.0),   # Einstein-Hilbert coupling range (negative = attractive)
    'n_points': 40,               # coupling scan points
}

# 4D finite-size scaling parameters
# g_EH in FSS is passed as g_EH = -ratio (attractive), scanning ratio = |g_EH|
ADW_4D_FSS = {
    'coupling_range': (1.0, 50.0),          # |g_EH| range for FSS scan (mapped to negative g_EH)
    'n_couplings': 40,                      # coupling points
    'sign_check_couplings': [1.0, 5.0, 10.0, 15.0, 20.0, 30.0, 50.0],
    'vestigial_window_threshold': 0.01,     # min Binder crossing separation
    'split_threshold': 0.05,                # min susceptibility peak separation
}

# ════════════════════════════════════════════════════════════════════
# Phase 5 Section 9C-3: Wetterich NJL model (gauge-link-free)
#
# Fierz-complete nearest-neighbor 4-fermion interaction. NO local gauge
# symmetry — SO(4) acts as global flavor. The NJL model provides an
# independent cross-check of vestigial gravity (Option C vs Option B).
#
# Reference: Wetterich, PLB 901, 136223 (2024) — spinor gravity
# Reference: Nambu & Jona-Lasinio, PR 122, 345 (1961) — NJL model
# Reference: Fierz, Z. Phys. 104, 553 (1937) — Fierz rearrangement
# ════════════════════════════════════════════════════════════════════

NJL_MODEL = {
    'd': 4,                       # spacetime dimension
    'n_grassmann': 8,             # Grassmann variables per site (same as ADW)
    'n_fierz_channels': 5,       # S, P, V, A, T (1+1+4+4+6 = 16 = 4²)
    'active_channels': ['scalar', 'pseudoscalar'],  # minimal 2-channel model
    'gauge_group': None,          # NO local gauge symmetry (key difference from ADW)
    'global_symmetry': 'SO(4)',   # flavor symmetry only
    'coordination_number': 8,     # same lattice as ADW
}

# NJL coupling scan — maps to ADW via g_eff = 4 × g_njl
# NJL coupling g > 0 = attractive (same convention as ADW g_EH < 0)
NJL_COUPLING_SCAN = {
    'g_cosmo': 1.0,               # on-site 8-fermion vertex (same as ADW)
    'g_njl_range': (2.0, 15.0),   # NJL coupling range — focused on AF transition region
    'n_points': 40,               # coupling scan points
}

NJL_FSS = {
    'coupling_range': (2.0, 15.0),          # g_njl range for FSS scan — transition region
    'n_couplings': 40,
    'vestigial_window_threshold': 0.01,
    'split_threshold': 0.05,
}


# ════════════════════════════════════════════════════════════════════
# Phase 5 Wave 6: Analytical Vestigial Susceptibility (RPA formalism)
#
# The metric g_μν = δ_{ab} e^a_μ e^b_ν is a composite bilinear of the
# tetrad — a vestigial order parameter. The RPA metric susceptibility
# χ_g⁻¹ = 1/u_g − c_D·Π₀(1/G − 1/G_c) diverges at G_ves < G_c
# whenever the metric-channel quartic coupling u_g > 0.
#
# Reference: Fernandes/Chubukov/Schmalian, Ann. Rev. CMP 10, 133 (2019)
# Reference: Nie/Tarjus/Kivelson, PNAS 111, 7980 (2014)
# Reference: Volovik, JETP Letters 119, 564 (2024) — symmetry identification
# ════════════════════════════════════════════════════════════════════

ADW_VESTIGIAL = {
    'N_f': 2,                     # Dirac fermion species in ADW
    'D': 4,                       # internal SO(4) dimension
    'Lambda': np.pi,              # UV cutoff (lattice: π/a with a=1)
    # Channel multiplicity factors from index contraction:
    #   δ_{ab}δ_{cd}δ^{ac}δ^{bd} = D = 4
    #   Trace channel: c_D = 2D² = 32
    #   Traceless-symmetric: c_D = 2D = 8
    'c_D_trace': 32,              # 2 × D² — scalar (volume) metric channel
    'c_D_traceless': 8,           # 2 × D  — traceless symmetric (graviton) channel
    # Gamma-matrix trace projection onto metric channel:
    #   Tr(γ^a γ^b γ^c γ^d) = 4(δ^{ab}δ^{cd} − δ^{ac}δ^{bd} + δ^{ad}δ^{bc})
    #   Metric projection (symmetric: δ^{ab}δ^{cd} + δ^{ad}δ^{bc}): coefficient = 4×2 = 8
    #   Lorentz projection (antisymmetric: δ^{ac}δ^{bd}): coefficient = −4 (repulsive)
    'gamma_trace_metric_coeff': 8,    # positive → attractive metric channel
    'gamma_trace_lorentz_coeff': -4,  # negative → repulsive Lorentz channel
}

# Vestigial susceptibility scan parameters
ADW_VESTIGIAL_SCAN = {
    'G_over_Gc_range': (0.01, 0.999),   # G/G_c scan range (disordered phase)
    'n_points': 200,                     # fine scan for smooth susceptibility curve
    'u_g_range': (0.01, 2.0),            # quartic coupling range for window plot
    'n_u_g_points': 100,                 # points for u_g sweep
}


# ════════════════════════════════════════════════════════════════════
# Phase 5 Wave 7: Hybrid Gauge-Link + Fermion-Bag MC
#
# First-ever fermion-bag MC with dynamical SO(4) gauge links on a 4D
# hypercubic lattice. SO(4) ≅ (SU(2)_L × SU(2)_R)/Z_2 via quaternion
# pairs for 4× computational speedup.
#
# Reference: Chandrasekharan, PRD 82, 025007 (2010) — fermion-bag
# Reference: Kennedy & Pendleton, PLB 156, 393 (1985) — SU(2) heatbath
# Reference: Creutz, "Quarks, Gluons and Lattices" (1983) — lattice gauge
# Reference: Wilson, PRD 10, 2445 (1974) — plaquette action
# ════════════════════════════════════════════════════════════════════

GAUGE_LINK_MC = {
    'N_f': 2,                     # Dirac fermion species
    'beta_range': (0.0, 10.0),    # Wilson plaquette coupling (β=0 is pure ADW)
    'g_range': (0.0, 20.0),       # four-fermion coupling
    'n_thermalize': 500,          # thermalization sweeps
    'n_measure': 2000,            # measurement sweeps
    'n_skip': 5,                  # decorrelation gap between measurements
    'n_overrelax': 4,             # overrelaxation sweeps per heatbath sweep
    'quaternion_renorm_interval': 50,  # renormalize quaternions every N sweeps
}

SO4_LATTICE = {
    'dim': 4,                     # spacetime dimension
    'n_directions': 4,            # number of link directions per site
    'n_plaquettes_per_link': 6,   # each link in d=4 belongs to 6 plaquettes
    'plaquette_norm': 4.0,        # Tr(I₄) = 4 for SO(4) fundamental
    'quaternion_dim': 4,          # components per SU(2) quaternion
    'link_storage': 8,            # 2 quaternions × 4 floats = 8 floats per link
    'checkerboard': True,         # even/odd checkerboard update ordering
}

# 4D Euclidean Clifford algebra: {γ^a, γ^b} = 2δ^{ab}
# Chiral representation from tensor products of Pauli matrices.
# NOTE: Cl(4,0) ≅ M_2(ℍ) — no faithful real 4×4 rep exists.
#   γ^0, γ^2 are real; γ^1, γ^3 are purely imaginary.
#   det(M_B) ∈ ℝ guaranteed by charge conjugation (C = γ^0 γ^2),
#   NOT by gamma matrices being real.
# Reference: Montvay & Münster, "Quantum Fields on a Lattice" (1994), Ch. 4.4
# Reference: Creutz, "Quarks, Gluons and Lattices" (1983), Ch. 4
EUCLIDEAN_GAMMA_4D = None  # Populated at module load below

def _build_euclidean_gamma_4d():
    """Construct 4D Euclidean gamma matrices from Pauli tensor products.

    γ^0 = σ_1 ⊗ σ_1   (real, Hermitian)
    γ^1 = σ_1 ⊗ σ_2   (imaginary, Hermitian)
    γ^2 = σ_1 ⊗ σ_3   (real, Hermitian)
    γ^3 = σ_2 ⊗ I₂    (imaginary, Hermitian)

    All satisfy {γ^a, γ^b} = 2δ^{ab}, (γ^a)² = I₄, Tr(γ^a) = 0.
    """
    sigma_1 = np.array([[0, 1], [1, 0]], dtype=complex)
    sigma_2 = np.array([[0, -1j], [1j, 0]], dtype=complex)
    sigma_3 = np.array([[1, 0], [0, -1]], dtype=complex)
    I2 = np.eye(2, dtype=complex)
    return np.array([
        np.kron(sigma_1, sigma_1),  # γ^0: real
        np.kron(sigma_1, sigma_2),  # γ^1: imaginary
        np.kron(sigma_1, sigma_3),  # γ^2: real
        np.kron(sigma_2, I2),       # γ^3: imaginary
    ])

EUCLIDEAN_GAMMA_4D = _build_euclidean_gamma_4d()

# Charge conjugation matrix: C = γ^0 · γ^2 = -i(I₂ ⊗ σ_2)
# Satisfies: C γ^a C^{-1} = -(γ^a)^T for all a
# Consequence: det(M_B[U]) ∈ ℝ for U ∈ SO(4) (real gauge group)
CHARGE_CONJUGATION_4D = EUCLIDEAN_GAMMA_4D[0] @ EUCLIDEAN_GAMMA_4D[2]

# ════════════════════════════════════════════════════════════════════
# 8×8 Real Majorana representation of Cl(4,0)
# Source: "The 8×8 Majorana formulation for ADW fermion-bag MC" (deep research)
# Source: Figueroa-O'Farrill, Edinburgh lectures on Majorana spinors
# Source: Wei/Wu/Li/Zhang/Xiang, PRL 116, 250601 (2016) — Kramers positivity
#
# All Γ^a are real, symmetric, 8×8, satisfying {Γ^a,Γ^b} = 2δ^{ab}I₈.
# The commutant of Cl(4,0) in Mat₈(ℝ) is ℍ, spanned by J₁,J₂,J₃.
# J₁ = charge conjugation (C), J₂ = Kramers operator (T).
# Kramers positivity: {J₂, A} = 0 for any A = Σ_a h_a J₁Γ^a ⊗ U
#   → Pf(A) has definite sign → sign-problem-free.
# ════════════════════════════════════════════════════════════════════

def _build_majorana_8x8():
    """Construct 8×8 real Majorana gamma matrices and quaternionic commutant."""
    sigma_1 = np.array([[0.0, 1.0], [1.0, 0.0]])
    sigma_3 = np.array([[1.0, 0.0], [0.0, -1.0]])
    I2 = np.eye(2)
    epsilon = np.array([[0.0, -1.0], [1.0, 0.0]])  # ε = iσ₂ in real form

    # Gamma matrices: Γ^a = tensor products of σ₁, σ₃, I₂
    G1 = np.kron(sigma_1, np.kron(sigma_1, sigma_1))  # σ₁⊗σ₁⊗σ₁
    G2 = np.kron(sigma_3, np.kron(sigma_1, sigma_1))  # σ₃⊗σ₁⊗σ₁
    G3 = np.kron(I2, np.kron(sigma_3, sigma_1))        # I₂⊗σ₃⊗σ₁
    G4 = np.kron(I2, np.kron(I2, sigma_3))              # I₂⊗I₂⊗σ₃
    gammas = np.array([G1, G2, G3, G4])

    # Quaternionic commutant: J_k² = -I₈, J_k^T = -J_k, [J_k, Γ^a] = 0
    J1 = np.kron(epsilon, np.kron(sigma_3, I2))      # ε⊗σ₃⊗I₂
    J2 = np.kron(epsilon, np.kron(sigma_1, sigma_3))  # ε⊗σ₁⊗σ₃
    J3 = np.kron(I2, np.kron(epsilon, sigma_3))       # I₂⊗ε⊗σ₃

    return gammas, J1, J2, J3

MAJORANA_GAMMA_8x8, MAJORANA_J1, MAJORANA_J2, MAJORANA_J3 = _build_majorana_8x8()

# Gauge-link MC scan parameters for phase diagram mapping
GAUGE_LINK_SCAN = {
    'beta_points': [0.0, 0.5, 1.0, 2.0, 3.0, 5.0, 8.0, 10.0],  # Wilson coupling
    'g_points': 20,               # four-fermion coupling points per β slice
    'lattice_sizes': [4, 6, 8],   # L values for finite-size scaling
    'sign_threshold': 0.1,        # minimum ⟨sign⟩ for usable data
}

# ════════════════════════════════════════════════════════════════════
# HS+RHMC parameters (Wave 7C — Hubbard-Stratonovich + Rational HMC)
#
# Replaces fermion-bag algorithm for L≥6. The HS transformation
# decouples the quartic fermion interaction via auxiliary scalar fields
# h^a_{x,μ}, enabling RHMC sampling with O(V·√κ) cost per decorrelated
# sample (vs O(V⁴) for fermion-bag).
#
# Source: Catterall & Schaich, JHEP 07, 057 (2015) — Pfaffian RHMC
# Source: Clark & Kennedy, NPB Proc. Suppl. 129, 850 (2004) — RHMC algorithm
# Source: Omelyan et al., Comp. Phys. Comm. 146, 188 (2002) — integrator
# Source: deep research "HS+RHMC for ADW tetrad condensation..."
# ════════════════════════════════════════════════════════════════════

RHMC_PARAMS = {
    # ── MD trajectory parameters ──
    # tau = total trajectory length, n_md_steps = Omelyan steps, eps = tau/n_md_steps.
    # The Omelyan integrator gives ΔH ~ C·ε² where C depends on the model.
    # At L=2, g=2.0: C ≈ 44 (measured 2026-04-02 via ΔH scaling test).
    # For 75-85% acceptance: need ⟨ΔH⟩ ~ 1, so ε ≈ 1/√C ≈ 0.15.
    # Step size scan at L=2, g=2.0 (2026-04-02): ΔH < 10⁻³ for all eps ≤ 0.2
    #   (L=2 too small for meaningful ΔH — only 128 DOF).
    # At L=4 (2048 DOF): C scales ~linearly with dim, so ΔH ~ 44 × (2048/128) × ε² = 704 ε².
    #   For ΔH ~ 1: ε ≈ 0.04 → n_md_steps = 25 at tau=1.0.
    # Default n_md_steps=10 (eps=0.1) is a starting point; tune per (L, g) in production.
    # Source: Omelyan et al., CPC 146, 188 (2002), Eq. (31)
    'tau': 1.0,                        # MD trajectory length
    'n_md_steps': 10,                  # Omelyan steps (eps = tau/n_md_steps = 0.1)
    'omelyan_lambda': 0.1932,          # Omelyan 2MN optimal parameter
    'force_evals_per_step': 3,         # Omelyan: 3 force evals per step

    # ── Zolotarev rational approximation (x^{-1/4} for Pf = det^{1/4}) ──
    # Three precision levels following the standard multi-precision RHMC strategy:
    # MD forces use cheap low-precision → errors corrected by Metropolis step.
    # Accept/reject uses expensive high-precision → ensures exact sampling.
    # The MISMATCH between MD and MC precision causes a systematic ΔH bias.
    # This bias is O(δ²) where δ is the Zolotarev approx error at MD precision.
    # CRITICAL: the S_PF mismatch between MD and MC poles adds DIRECTLY to ΔH.
    # Measured S_PF vs exact at L=2, κ=164 (2026-04-02):
    #   8 poles: ΔS_PF ≈ 79  → ΔH ≈ 80 (destroys acceptance, h-field unstable)
    #  12 poles: ΔS_PF ≈ 0.3 → ΔH ≈ 0.3 + O(ε²) (marginal)
    #  16 poles: ΔS_PF ≈ 0.03 → negligible (integrator error dominates)
    # Same-poles test (16 for both MD+MC, 2026-04-02):
    #   ΔH ≈ 0.8, acceptance 60%, h-field stable, no mismatch artifacts.
    # For production: use same poles for MD and MC to avoid mismatch.
    # Multi-precision strategy (fewer MD poles) is an OPTIMIZATION that requires
    # careful tuning per (L, g) to ensure ΔS_PF < integrator error.
    # Source: Clark & Kennedy, NPB PS 129, 850 (2004), Section 3
    'n_poles_md': 16,                  # same as MC for reliability (ΔS_PF ≈ 0.03)
    'n_poles_hb': 16,                  # for pseudofermion heat bath
    'n_poles_mc': 16,                  # same as MD — avoids mismatch artifacts

    # ── Spectral range estimation (Lanczos on A†A) ──
    'lanczos_iterations': 20,          # iterations for λ_min/λ_max estimation
    'spectral_safety_low': 0.8,        # safety factor: use 0.8 × λ_min
    'spectral_safety_high': 1.2,       # safety factor: use 1.2 × λ_max

    # ── Multi-shift conjugate gradient ──
    # CG tolerance sets the force accuracy. With cg_tol_md=1e-8:
    #   - Reversibility degrades to ~1e-10 (measured 2026-04-02)
    #   - Acceptable because Metropolis corrects for force errors
    # With cg_tol_md=1e-14: reversibility to machine precision (~1e-15)
    #   - But ~2× more CG iterations → 2× slower forces
    # Production compromise: 1e-8 for MD, 1e-12 for Hamiltonian (accept/reject)
    # Source: Clark & Kennedy, NPB PS 129, 850 (2004) — multi-precision RHMC
    'cg_tol_md': 1e-8,                # CG residual tolerance for MD forces
    'cg_tol_mc': 1e-12,               # CG residual tolerance for Hamiltonian eval
    'cg_max_iter': 5000,              # CG iteration cap

    # ── Production defaults ──
    'n_trajectories': 1000,            # total RHMC trajectories
    'n_thermalize': 200,               # thermalization trajectories
    'n_measure_skip': 5,               # trajectories between measurements
    'target_acceptance': (0.75, 0.85), # optimal Metropolis acceptance range

    # ── Auxiliary field initialization ──
    # h^a_{x,μ} ~ Gaussian(0, √(2g)) at equilibrium.
    # 16V fields total: 4 directions × 4 Lorentz × V sites.
    'h_field_components': 16,          # per site: 4 directions × 4 Lorentz indices
}


# ════════════════════════════════════════════════════════════════════
# Lattice Hamiltonian framework (Wave 3A — chirality wall formalization)
#
# Infrastructure for the GS no-go / TPF evasion formalization.
# The 6 explicit + 3 implicit GS conditions are the mathematical
# targets; the lattice Hamiltonian definitions provide the Lean
# vocabulary for stating them precisely.
# ════════════════════════════════════════════════════════════════════

# GS no-go: 6 explicit conditions + 3 implicit assumptions = 9 total
GS_CONDITIONS = {
    'explicit': {
        'C1': 'lattice_translation_invariance',   # H(k) ∈ C¹(T^d)
        'C2': 'fermion_fields_only',              # no scalar/bosonic ancillas
        'C3': 'relativistic_no_massless_bosons',  # free massless fermions + irrelevant ops
        'C4': 'complete_interpolating_fields',     # retarded/advanced propagators complete
        'C5': 'no_spontaneous_symmetry_breaking',  # global symmetry unbroken
        'C6': 'propagator_zeros_kinematical',      # zeros removable by field redefinition
    },
    'implicit': {
        'I1': 'hamiltonian_formulation',   # continuous time, discrete space
        'I2': 'local_interactions',        # finite-range Hamiltonian
        'I3': 'finite_dim_local_hilbert',  # finite-dimensional local Hilbert space
    },
}

# TPF violations of GS conditions (from deep research analysis)
TPF_VIOLATIONS = {
    'C2': 'bosonic_rotor_ancillas',         # L²(S¹) rotor DOF are bosonic
    'I3': 'infinite_dim_rotor_hilbert',     # L²(S¹) is countably infinite-dim
    'dim': 'extra_dimensional_spt_slab',    # 4+1D SPT slab, not purely D-dim
}
TPF_VIOLATION_COUNT = len(TPF_VIOLATIONS)  # 3 clean violations

# Lattice framework parameters
LATTICE_FRAMEWORK = {
    'd_physical': 4,             # spatial dimension for 3+1D QFT
    'brillouin_period': 2 * np.pi,  # period of BZ torus T^d = (ℝ/2πℤ)^d
    'n_gs_explicit': 6,          # explicit GS conditions
    'n_gs_implicit': 3,          # implicit GS assumptions
    'n_gs_total': 9,             # total GS conditions
    'n_tpf_violations': 3,       # GS conditions cleanly violated by TPF
}


# ════════════════════════════════════════════════════════════════════
# Layer 1 formalization: Categorical infrastructure (Wave 4A)
#
# String-net condensation requires fusion categories — the input data
# for the Levin-Wen model. The output is Z(C) (Drinfeld center),
# which recovers Dijkgraaf-Witten gauge theory when C = Vec_G.
# Mathlib4 provides monoidal/braided/rigid categories + Drinfeld center;
# the missing layers (pivotal → spherical → semisimple → fusion) are
# what Wave 4 builds. This would be the FIRST fusion category
# formalization in any proof assistant.
# ════════════════════════════════════════════════════════════════════

# Categorical hierarchy: what exists vs what we build
CATEGORY_HIERARCHY = {
    'mathlib_existing': [
        'MonoidalCategory',      # full coherence tactic, pentagon axiom
        'BraidedCategory',       # hexagon identities
        'SymmetricCategory',
        'RigidCategory',         # exact pairings, evaluation/coevaluation
        'MonoidalLinear',        # R-linear tensor product
        'MonoidalPreadditive',   # additive tensor product
        'Simple',                # simple objects (mono is iso or zero)
        'SchurLemma',            # finrank End(X) = 1 for simple X
        'DrinfeldCenter',        # Z(C) braided monoidal
    ],
    'wave4a_new': [
        'PivotalCategory',       # double-dual ≅ identity (natural iso)
        'CategoricalTrace',      # left/right traces via pivotal structure
        'SphericalCategory',     # left trace = right trace
        'QuantumDimension',      # d_X = tr(id_X)
        'SemisimpleCategory',    # every object = ⊕ simples
    ],
    'wave4b_new': [
        'FusionCategory',        # rigid+semisimple+k-linear+spherical+fin simples
        'FSymbols',              # associator matrix elements
        'PentagonEquation',      # F-symbol consistency
        'FrobeniusPerronDim',    # Frobenius-Perron dimension
        'GlobalDimension',       # D² = Σ d_i²
    ],
}

# Concrete fusion category examples for verification
FUSION_EXAMPLES = {
    'Vec_Z2': {
        'group': 'Z_2',
        'n_simples': 2,          # {0, 1} = {e, g}
        'simple_labels': ['e', 'g'],
        'quantum_dims': [1, 1],  # all objects have dim 1
        'global_dim_sq': 2,      # D² = 1² + 1² = 2
        'F_symbols_trivial': True,  # all F = 1 (trivial 3-cocycle)
        # Fusion rules N[k][i][j] = δ_{k, i+j mod 2}
        'fusion_rules': [
            [[1, 0], [0, 1]],  # N[0][i][j]: e appears in i⊗j
            [[0, 1], [1, 0]],  # N[1][i][j]: g appears in i⊗j
        ],
    },
    'Vec_Z3': {
        'group': 'Z_3',
        'n_simples': 3,
        'simple_labels': ['e', 'g', 'g2'],
        'quantum_dims': [1, 1, 1],
        'global_dim_sq': 3,
        'F_symbols_trivial': True,
        # N[k][i][j] = δ_{k, (i+j) mod 3}
        'fusion_rules': [
            [[1, 0, 0], [0, 0, 1], [0, 1, 0]],  # N[0]: 0+0=0, 1+2=0, 2+1=0
            [[0, 1, 0], [1, 0, 0], [0, 0, 1]],  # N[1]: 0+1=1, 1+0=1, 2+2=1
            [[0, 0, 1], [0, 1, 0], [1, 0, 0]],  # N[2]: 0+2=2, 1+1=2, 2+0=2
        ],
    },
    'Vec_S3': {
        'group': 'S_3',
        'n_simples': 6,          # one for each group element
        'quantum_dims': [1, 1, 1, 1, 1, 1],
        'global_dim_sq': 6,
        'F_symbols_trivial': False,  # nontrivial H³(S₃, ℂ×)
    },
    'Rep_S3': {
        'group': 'S_3',
        'n_simples': 3,          # trivial(0), sign(1), standard(2, dim=2)
        'simple_labels': ['triv', 'sign', 'std'],
        'quantum_dims': [1, 1, 2],
        'global_dim_sq': 6,      # 1² + 1² + 2² = 6 = |S₃|
        'F_symbols_trivial': False,
        # Fusion rules: triv⊗X=X, sign⊗sign=triv, sign⊗std=std, std⊗std=triv⊕sign⊕std
        'fusion_rules': [
            [[1, 0, 0], [0, 1, 0], [0, 0, 1]],  # N[triv]: triv⊗X = X
            [[0, 1, 0], [1, 0, 0], [0, 0, 1]],  # N[sign]: sign appears in i⊗j
            [[0, 0, 1], [0, 0, 1], [1, 1, 1]],  # N[std]: std appears in i⊗j
        ],
    },
    'Fibonacci': {
        'group': None,           # not a group category
        'n_simples': 2,          # {1(=0), τ(=1)}
        'simple_labels': ['1', 'τ'],
        'quantum_dims': [1, (1 + np.sqrt(5)) / 2],  # golden ratio φ
        'global_dim_sq': (5 + np.sqrt(5)) / 2,      # 1 + φ² = 2 + φ
        'F_symbols_trivial': False,
        # Fusion rules: 1⊗X=X, τ⊗τ = 1⊕τ
        'fusion_rules': [
            [[1, 0], [0, 1]],  # N[1]: unit fusion
            [[0, 1], [1, 1]],  # N[τ]: τ⊗τ contains both 1 and τ
        ],
        # F-matrix: F^{τττ}_τ is the nontrivial 2×2 block
        # F^{τττ}_{τ} = [[φ⁻¹, φ^{-1/2}], [φ^{-1/2}, -φ⁻¹]]
        # where φ = (1+√5)/2. Pentagon equation constrains this uniquely.
        'F_matrix_tau': None,  # computed at import time below
    },
}

# Compute Fibonacci F-matrix (depends on φ)
_phi = (1 + np.sqrt(5)) / 2
FUSION_EXAMPLES['Fibonacci']['F_matrix_tau'] = np.array([
    [1 / _phi, 1 / np.sqrt(_phi)],
    [1 / np.sqrt(_phi), -1 / _phi],
])

# Physics connections: how string-net layers connect to existing codebase
LAYER1_CONNECTIONS = {
    'gauge_erasure': 'Z(C) always non-chiral (c=0 mod 8) → doubled gauge erased at boundary',
    'fracton_hydro': 'Stacked Vec_G string-nets → fracton phases via gauged 1-form symmetry',
    'fracton_nonabelian': 'Cage-net from non-Abelian Vec_G → non-Abelian fracton excitations',
    'chirality_wall': 'Z(C) doubled → intrinsic chirality limitation of string-nets',
}

# Drinfeld double data (Wave 4C — gauge emergence)
# D(G) = k^G ⊗ k[G] with twisted multiplication.
# Simple modules of D(G) ↔ pairs (conjugacy class K, irrep of centralizer C_G(g)).
DRINFELD_DOUBLE = {
    'Z2': {
        'group_order': 2,
        'n_conj_classes': 2,
        'n_simples': 4,        # 2 classes × 2 irreps each (abelian: each centralizer = G)
        'dim_D': 4,            # dim D(G) = |G|² = 4
    },
    'Z3': {
        'group_order': 3,
        'n_conj_classes': 3,
        'n_simples': 9,        # 3 × 3 (abelian)
        'dim_D': 9,
    },
    'S3': {
        'group_order': 6,
        'n_conj_classes': 3,   # {e}, {(12),(13),(23)}, {(123),(132)}
        'centralizer_orders': [6, 2, 3],  # C(e)=S₃, C((12))=⟨(12)⟩, C((123))=⟨(123)⟩
        'irreps_per_class': [3, 2, 3],    # 3 irreps of S₃, 2 of Z/2, 3 of Z/3
        'n_simples': 8,        # 3 + 2 + 3 = 8
        'dim_D': 36,           # |G|² = 36
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
# Maps Aristotle-proved theorems to their run IDs.
#
# Verification breakdown (506 theorems + 2 axioms across 33 Lean modules):
#   - 99 proved by Aristotle automated theorem prover (listed below with run IDs)
#   - 330 proved manually in Lean (verified by `lake build`)
#   - 2 axioms: non_abelian_center_discrete (GaugeErasure.lean),
#               gs_nogo_axiom (GoltermanShamir.lean)
#
# ZERO sorry across entire project. Verified by `lake build`.
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

    # Phase 5 Wave 3A — LatticeHamiltonian.lean (7 by Aristotle)
    'translation_invariant_double_shift': 'run_20260328_132925',
    'finite_range_bloch_is_finite_sum': 'run_20260328_132925',
    'rotor_hilbert_not_finite_dim': 'run_20260328_132925',
    'round_not_continuous_at_half': 'run_20260328_132925',
    'integers_not_finite': 'run_20260328_132925',
    'hermitian_diagonal_real': 'run_20260328_132925',
    'hermitian_trace_real': 'run_20260328_132925',

    # Phase 5 Wave 3B — GoltermanShamir.lean (3 by Aristotle)
    'tpf_violates_C2': 'run_20260328_142342',
    'tpf_outside_gs_scope': 'run_20260328_142342',
    'c1_implies_i2': 'run_20260328_142342',

    # Phase 5 Wave 3B+ — GoltermanShamir.lean strengthening (3 by Aristotle)
    'c2_fock_dim_power_of_two': 'run_20260328_151228',
    'tpf_escapes_by_bosonic_and_infinite': 'run_20260328_151228',
    'tpf_bosonic_exceeds_fock': 'run_20260328_151228',

    # Phase 5 Wave 3C — GoltermanShamir.lean fock_space_finite_dim (1 by Aristotle)
    'fock_space_finite_dim': 'run_20260328_170451',

    # Phase 5 Wave 4A — KLinearCategory.lean (4 by Aristotle)
    'tensor_preserves_nonzero': 'run_20260329_094416',
    'unit_totalDim_one': 'run_20260329_094416',
    'simples_nonempty': 'run_20260329_094416',
    'simple_indecomposable': 'run_20260329_094416',

    # Phase 5 Wave 4A — SphericalCategory.lean (7 by Aristotle)
    'quantum_dim_unit': 'run_20260329_094416',
    'quantum_dim_tensor': 'run_20260329_094416',
    'quantum_dim_dual': 'run_20260329_094416',
    'trace_smul': 'run_20260329_094416',
    'trace_zero': 'run_20260329_094416',
    'double_mate_comp': 'run_20260329_094416',
    'golden_ratio_eq': 'run_20260329_094416',

    # Phase 5 Wave 4B — FusionExamples.lean (7 by Aristotle)
    'vecZ2_assoc': 'run_20260329_205113',
    'vecZ3_assoc': 'run_20260329_205113',
    'repS3_assoc': 'run_20260329_205113',
    'fib_assoc': 'run_20260329_205113',
    'fib_F_involutory': 'run_20260329_205113',
    'fib_is_chiral': 'run_20260329_205113',
    'fibonacci_dim_not_integer': 'run_20260329_205113',

    # Phase 5 Wave 4C — VecG.lean (6 by Aristotle)
    'day_unit_left': 'run_20260329_211117',
    'day_unit_right': 'run_20260329_211117',
    'day_assoc': 'run_20260329_211117',
    'simple_tensor': 'run_20260329_211117',
    'day_dim_multiplicative': 'run_20260329_211117',
    'simpleGraded_invertible': 'run_20260329_211117',

    # Phase 5 Wave 4C — DrinfeldDouble.lean (2 by Aristotle)
    'ddMul_one_left': 'run_20260329_211117',
    'ddMul_one_right': 'run_20260329_211117',

    # Phase 5 Section 9C — FractonFormulas.lean (45 by Aristotle)
    'symmetric_tensor_components': '4528aa2b',
    'charge_scalar_one_component': '4528aa2b',
    'dipole_d_components': '4528aa2b',
    'quadrupole_3d_six_components': '4528aa2b',
    'hockey_stick_charge_count': '4528aa2b',
    'charge_count_at_least_linear': '4528aa2b',
    'total_conserved_with_momentum_energy': '4528aa2b',
    'dipole_quadratic_dispersion': '4528aa2b',
    'dipole_k4_damping': '4528aa2b',
    'standard_linear_dispersion': '4528aa2b',
    'damping_twice_dispersion': '4528aa2b',
    'dispersion_power_strict_mono': '4528aa2b',
    'subdiffusive_relaxation': '4528aa2b',
    'ucd_standard': '4528aa2b',
    'ucd_dipole': '4528aa2b',
    'ucd_quadrupole': '4528aa2b',
    'ucd_unbounded': '4528aa2b',
    'ucd_grows_even': '4528aa2b',
    'transport_count_total': '4528aa2b',
    'positivity_constrains_dissipative': '4528aa2b',
    'retention_ratio_exceeds_one': '4528aa2b',
    'retention_ratio_diverges': '4528aa2b',
    'fragmentation_bits_positive': '4528aa2b',
    'standard_hydro_info_constant': '4528aa2b',
    'xcube_grows_linearly': '4528aa2b',
    'fragmentation_dominates_standard_1d': '4528aa2b',
    'fracton_dof_4d_spacetime': '4528aa2b',
    'graviton_dof_4d_is_2': '4528aa2b',
    'extra_dof_4d': '4528aa2b',
    'dof_gap_equals_d_minus_1': '4528aa2b',
    'dof_gap_always_positive': '4528aa2b',
    'bootstrap_diverges_all_high_orders': '4528aa2b',
    'five_bootstrap_obstructions': '4528aa2b',
    'bootstrap_gap_is_structural': '4528aa2b',
    'spin1_instability_at_cubic': '4528aa2b',
    'commutator_order_mismatch': '4528aa2b',
    'commutator_order_ratio': '4528aa2b',
    'param_gap_quadratic_growth': '4528aa2b',
    'param_mismatch_general': '4528aa2b',
    'ym_four_independent_obstructions': '4528aa2b',
    'no_fracton_ym_compatibility': '4528aa2b',
    'wxy_scalar_not_vector': '4528aa2b',
    'dispersion_matches_charge_scaling': '4528aa2b',
    'dof_gap_cross_check': '4528aa2b',
    'obstruction_counts_distinct': '4528aa2b',

    # Phase 5 Section 9C — WetterichNJL.lean (18 by Aristotle)
    'fierz_completeness': '4528aa2b',
    'fierz_equals_spinor_sq': '4528aa2b',
    'fierz_channel_count': '4528aa2b',
    'fierz_channel_dims_positive': '4528aa2b',
    'njl_scalar_nonneg': '4528aa2b',
    'njl_scalar_monotone': '4528aa2b',
    'njl_scalar_upper_bound': '4528aa2b',
    'njl_pseudoscalar_half_filling_zero': '4528aa2b',
    'chirality_factor_bounded': '4528aa2b',
    'njl_pseudoscalar_sign_at_empty': '4528aa2b',
    'njl_bond_weight_decomposition': '4528aa2b',
    'njl_total_at_half_filling': '4528aa2b',
    'njl_bond_weight_symmetric': '4528aa2b',
    'njl_vector_nonneg': '4528aa2b',
    'vector_variance_bound': '4528aa2b',
    'njl_adw_correspondence': '4528aa2b',
    'njl_adw_positivity': '4528aa2b',
    'njl_to_g_EH': '4528aa2b',

    # Phase 5 Section 9C — SO4Weingarten.lean (14 by Aristotle)
    'weingarten_2nd_factor': 'run_20260331_103403',
    'weingarten_2nd_so4': 'run_20260331_103403',
    'weingarten_4th_so4_pair': 'run_20260331_103403',
    'weingarten_epsilon_so4': 'run_20260331_103403',
    'adjoint_channel_suppressed': 'run_20260331_103403',
    'fundamental_channel_nonneg': 'run_20260331_103403',
    'adjoint_channel_nonneg': 'run_20260331_103403',
    'total_bond_nonneg': 'run_20260331_103403',
    'attractive_bond_action_nonpos': 'run_20260331_103403',
    'so4_fundamental_dim': 'run_20260331_103403',
    'so4_tensor_product_decomp': 'run_20260331_103403',
    'planck_nonneg': 'run_20260331_103403',
    'exp_gt_one_of_pos': 'run_20260331_103403',
    'planck_monotone': 'run_20260331_103403',
    # Wave 6 — VestigialSusceptibility (16 theorems, Aristotle 9e2251cd)
    'gamma_trace_metric_positive': '9e2251cd',
    'gamma_trace_lorentz_negative': '9e2251cd',
    'metric_dominates_lorentz': '9e2251cd',
    'u_g_positive': '9e2251cd',
    'u_g_positive_adw': '9e2251cd',
    'bubble_integral_monotone': '9e2251cd',
    'bubble_integral_diverges': '9e2251cd',
    'bubble_integral_positive': '9e2251cd',
    'susceptibility_diverges': '9e2251cd',
    'vestigial_before_tetrad': '9e2251cd',
    'vestigial_r_e_star_pos': '9e2251cd',
    'vestigial_window_exponential': '9e2251cd',
    'vestigial_window_vanishes': '9e2251cd',
    'trace_channel_multiplicity': '9e2251cd',
    'traceless_channel_multiplicity': '9e2251cd',
    'vestigial_ordering_sufficient': '9e2251cd',
    # Wave 7A — QuaternionGauge (10 theorems, Aristotle fb657b4d)
    'quaternion_norm_mul': 'fb657b4d',
    'quaternion_left_identity': 'fb657b4d',
    'quaternion_conjugate_inverse': 'fb657b4d',
    'so4_dimension': 'fb657b4d',
    'su2_su2_dimension': 'fb657b4d',
    'plaquette_trace_bound': 'fb657b4d',
    'plaquette_action_nonneg': 'fb657b4d',
    'plaquette_action_identity': 'fb657b4d',
    'heatbath_weight_integrable': 'fb657b4d',
    'heatbath_detailed_balance': 'fb657b4d',
    # Wave 7B — GaugeFermionBag (9 theorems, Aristotle fb657b4d)
    'tetrad_gauge_covariant': 'fb657b4d',
    'metric_gauge_invariant': 'fb657b4d',
    'metric_from_tetrad_sq': 'fb657b4d',
    'bag_weight_real': 'fb657b4d',
    'determinant_rank1_update': 'fb657b4d',
    'vestigial_implies_nonzero_variance': 'fb657b4d',
    'metric_nonneg': 'fb657b4d',
    'binder_gaussian': 'fb657b4d',
    'binder_ordered': 'fb657b4d',
    # HubbardStratonovichRHMC.lean — 22 theorems, all manual proofs (2026-04-02)
    'hs_gaussian_identity_zero': 'manual',
    'hs_gaussian_action_nonneg': 'manual',
    'su2_closed_form_exp': 'manual',
    'su2_exp_unit_quaternion_identity': 'manual',
    'omelyan_second_order_symplectic': 'manual',
    'omelyan_time_reversible': 'manual',
    'zolotarev_exponential_convergence': 'manual',
    'partial_fraction_positivity': 'manual',
    'rhmc_hamiltonian_nonneg': 'manual',
    'rhmc_detailed_balance': 'manual',
    'hs_fermion_matrix_antisymmetric': 'manual',
    'kramers_holds_hs_matrix': 'manual',
    'multishift_cg_shared_krylov': 'manual',
    'bipartite_nearest_neighbor_zero_diagonal': 'manual',
    'ata_block_diag': 'manual',
    'even_odd_spectrum_identical': 'manual',
    'even_odd_cg_equivalence': 'manual',
    'multishift_krylov_shift_invariance': 'manual',
    'multishift_residual_collinearity': 'manual',
    'even_odd_force_equivalence': 'manual',
    'complex_pseudofermion_pfaffian': 'manual',
    'heatbath_a_trick_covariance': 'manual',
}

ARISTOTLE_PROVED_COUNT = len(ARISTOTLE_THEOREMS)
assert ARISTOTLE_PROVED_COUNT == 233, f"Expected 233 Aristotle-proved theorems, got {ARISTOTLE_PROVED_COUNT}"
# Backwards compatibility alias
TOTAL_THEOREMS = ARISTOTLE_PROVED_COUNT


# ════════════════════════════════════════════════════════════════════
# Parameter Provenance Registry (imported from src.core.provenance)
#
# Every value in EXPERIMENTS, ATOMS, and POLARITON_PLATFORMS must have
# a corresponding entry in PARAMETER_PROVENANCE that traces it to a
# specific published source (paper, table/figure, page).
#
# See Pipeline Invariant 8 and CHECK 15 in validate.py.
# ════════════════════════════════════════════════════════════════════

from src.core.provenance import PARAMETER_PROVENANCE  # noqa: E402


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
