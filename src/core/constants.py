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

from typing import Any

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

# Polariton parameters updated 2026-04-13 (Phase 5u Waves 3–4) to adopt the
# Falque et al. PRL 135, 023401 (2025) smooth-horizon defaults verified by
# LLM re-read of arXiv:2311.01392v2 full text:
#   c_s ≈ 0.40 μm/ps (§IV.1) = 4.0e5 m/s
#   ξ ≈ 3.4 μm upstream (§IV.1) = 3.4e-6 m
#   κ measured at 0.07/0.08 ps⁻¹ (smooth horizon) and 0.11 ps⁻¹ (steep horizon)
# We adopt the smooth-horizon 0.07 ps⁻¹ = 7e10 s⁻¹ as the baseline default.
# Steep-horizon maximum 1.1e11 s⁻¹ is reported as the platform's upper reach in
# Paper 12 body text but not used as the constants.py default — steep horizon
# drives D = ξκ/c_s > 0.9 which pushes the EFT framework into the dispersive
# regime (π/6·D² ≈ 0.45, 45% correction). Smooth horizon gives D ≈ 0.60:
# borderline but perturbative. Paper 12 narrative relies on the perturbative
# regime, hence the default adoption.
POLARITON_PLATFORMS = {
    'Paris_long': {
        'description': 'Paris polariton, long-lifetime cavity (100 ps) — PROJECTED',
        'c_s': 4.0e5,             # m/s (0.40 μm/ps, Falque 2025 §IV.1)
        'xi': 3.4e-6,             # m (3.4 μm upstream, Falque 2025 §IV.1)
        'kappa': 7.0e10,          # s⁻¹ (0.07 ps⁻¹ smooth-horizon default, Falque 2025 Fig. 2)
        'tau_cav': 100e-12,       # s (PROJECTED long-lifetime cavity; Falque actual ≈ 8 ps)
        'Gamma_pol': 1.0e10,      # s⁻¹ (1/tau_cav)
        'gamma_phonon_dim': 1e-4, # Dimensionless phonon damping (subdominant)
    },
    'Paris_ultralong': {
        'description': 'Paris polariton, ultra-long-lifetime cavity (300 ps) — PROJECTED',
        'c_s': 4.0e5,             # m/s (Falque 2025)
        'xi': 3.4e-6,             # m (Falque 2025)
        'kappa': 7.0e10,          # s⁻¹ (smooth-horizon default)
        'tau_cav': 300e-12,
        'Gamma_pol': 3.33e9,
        'gamma_phonon_dim': 1e-4,
    },
    'Paris_standard': {
        'description': 'Paris polariton, standard cavity (8 ps) — matches Falque 2025 actual',
        'c_s': 4.0e5,             # m/s (Falque 2025 measured)
        'xi': 3.4e-6,             # m (Falque 2025 measured)
        'kappa': 7.0e10,          # s⁻¹ (Falque 2025 smooth-horizon measured)
        'tau_cav': 8e-12,         # s (Falque 2025 actual cavity; was 3 ps projected)
        'Gamma_pol': 1.25e11,     # s⁻¹ (1/tau_cav for 8 ps)
        'gamma_phonon_dim': 1e-4,
    },
    'Penn_TMD_MoSe2': {
        # UPenn ZHEN-Lab nanocavity TMD-polariton platform (Wang, Kim, Zhen, He,
        # PRL 136, 146901 (2026); arXiv:2411.16635). MoSe₂ monolayer in a planar
        # photonic-crystal nanocavity. Ships with `c_s` / `xi` / `kappa` set to
        # the smooth-horizon Falque baseline values because the device itself
        # forms NO sonic horizon — the platform is included solely so the
        # Tier-1 validity-ratio post-processing tags it as `intractable`,
        # demonstrating that even using the most generous LKB-comparable
        # κ baseline, the TMD-polariton platform sits OUTSIDE Tier 1
        # perturbative-dissipation validity (Wave 6v.4 scope-demarcation
        # claim for E1). DO NOT feed to the transonic_background solver.
        'description': 'UPenn TMD MoSe2 nanocavity (Wang/Kim/Zhen/He PRL 2026) — '
                       'Tier-1 SCOPE DEMARCATION exhibit (not an analog-horizon device)',
        'c_s': 4.0e5,             # m/s (Falque smooth-horizon baseline; placeholder)
        'xi': 3.4e-6,             # m (Falque smooth-horizon baseline; placeholder)
        'kappa': 7.0e10,          # s⁻¹ (Falque smooth-horizon baseline as the generous κ)
        # γ_LP = 1.8 meV → Γ_LP = γ_LP / ℏ. Computed below post-dict (avoids
        # cross-import dependency on E_CHARGE/HBAR at dict-literal time).
        'tau_cav': 3.48e-13,      # s (≈ 348 fs photon lifetime, ℏ/γ_cav for γ_cav=1.9 meV)
        # Γ_pol set below post-dict from γ_LP_meV; cavity Γ_cav = 1/tau_cav also computed.
        'gamma_phonon_dim': 1e-4, # subdominant (cavity decay dominates as in all polariton platforms)
        'g_meV': 16.8,            # exciton-photon coupling (Wang et al. 2026 Eq. coupled-oscillator fit)
        'gamma_LP_meV': 1.8,      # lower-polariton linewidth (Wang et al. 2026)
        'gamma_UP_meV': 2.3,      # upper-polariton linewidth (Wang et al. 2026)
        'gamma_cav_meV': 1.9,     # cavity linewidth (γ_rad ≈ 0.7 + γ_nonrad ≈ 1.2)
        'Q_factor': 914,          # E_cav (1.736 eV) / γ_cav (1.9 meV)
        'switching_energy_fJ': 4.0,  # all-optical switching threshold (Wang et al. 2026)
        # Γ_pol computed from γ_LP_meV at post-dict step below (use canonical eV→s⁻¹
        # conversion to keep the source-of-truth purely in g/γ_LP/γ_UP/γ_cav in meV).
    },
}

# Falque steep-horizon reach — reported but not adopted as default.
# The steep-horizon configuration (§IV.2) demonstrates κ up to 0.11 ps⁻¹
# corresponding to T_H ~ 134 mK, at the cost of D ≈ 0.93 (EFT becomes
# non-perturbative). Quoted in Paper 12 body text.
FALQUE_STEEP_HORIZON_KAPPA = 1.1e11  # s⁻¹ (0.11 ps⁻¹ maximum measured)

# Penn TMD polariton: Γ_pol derived from the source-of-truth γ_LP in meV.
# Γ_LP = γ_LP / ℏ. The elementary charge converts eV → J; division by HBAR
# gives s⁻¹. (E_CHARGE itself is defined later in the graphene section, so
# we inline the SI 2019 exact value here to avoid a forward reference.)
_ELEMENTARY_CHARGE_J_PER_EV = 1.602176634e-19  # J/eV (exact SI 2019; cross-check: matches E_CHARGE)
POLARITON_PLATFORMS['Penn_TMD_MoSe2']['Gamma_pol'] = (
    POLARITON_PLATFORMS['Penn_TMD_MoSe2']['gamma_LP_meV'] * 1e-3
    * _ELEMENTARY_CHARGE_J_PER_EV / HBAR
)

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
# Graphene Dirac fluid parameters (Phase 5w)
#
# The graphene Dirac fluid near the charge neutrality point (CNP) is a
# natively relativistic 2+1D system where electron-hole quasiparticles
# propagate at the Fermi velocity v_F ≈ 10⁶ m/s.  Hydrodynamic sound
# waves (plasmons) propagate at c_s = v_F/√2 for the conformal fluid.
#
# Unlike BEC analog gravity (where c_s emerges from interactions), the
# causal speed v_F is set by the band structure.  The sonic horizon
# forms where the drift velocity reaches c_s, not v_F.
#
# Platforms use the same dict-based structure as POLARITON_PLATFORMS.
# Not BEC — do not feed to transonic_background solver.
#
# References:
#   - Majumdar et al., Nature Physics 21, 1374 (2025) [arXiv:2501.03193]
#   - Geurs et al., arXiv:2509.16321 (2025) — Dean group nozzle
#   - Zhao et al., Nature 614, 688 (2023) — c_s measurement
#   - Gallagher et al., Science 364, 158 (2019) — Planckian scattering
#   - Lucas & Fong, JPCM 30, 053001 (2018) — Dirac fluid review
# ════════════════════════════════════════════════════════════════════

# Fundamental graphene constants
E_CHARGE = 1.602176634e-19            # C (elementary charge, exact SI 2019)
V_FERMI_GRAPHENE = 1.0e6              # m/s (Fermi velocity in monolayer graphene)
ALPHA_GRAPHENE_VACUUM = 2.2           # e²/(ℏv_F) ≈ 2.2 in vacuum (suspended)
HBN_DIELECTRIC_PERP = 3.0             # hBN in-plane dielectric constant (low bound)
HBN_DIELECTRIC_PARA = 6.7             # hBN out-of-plane dielectric constant
# Effective fine structure constant on hBN substrate:
# α_eff = e²/(ℏ v_F ε_eff) where ε_eff ≈ (1 + ε_hBN)/2 ≈ 2.0
# gives α_eff ≈ 2.2/2.0 ≈ 1.1 (geometric mean approach gives ~0.5-0.9)
ALPHA_GRAPHENE_HBN = 0.7              # Representative value on hBN (range 0.5-0.9)

GRAPHENE_PLATFORMS = {
    'Dean_bilayer_nozzle': {
        'description': 'Dean group bilayer graphene de Laval nozzle '
                       '(Geurs et al. 2509.16321, first electronic sonic horizon)',
        'v_F': 1.0e6,                  # m/s (Fermi velocity, bilayer ≈ monolayer)
        'c_s': 4.4e5,                  # m/s (bilayer sound speed; Geurs 2025)
        'alpha_eff': 0.7,              # effective coupling on hBN
        'nozzle_throat_nm': 200,       # nm (throat length L; gradient length scale)
        'channel_width_nm': 1000,      # nm (channel width W; Dean geometry, Phase 5w §2)
        'l_ee_nm': 51,                 # nm (electron-electron mean free path; deep research §1.4)
        'v_over_c_s_horizon': 0.985,   # dimensionless (flow velocity / c_s at horizon for Γ₀ ≈ 0.9994)
        'T_ambient_K': 150,            # K (cryogenic operating temperature)
        'T_imp_K': 80,                 # K (disorder temperature, device-dependent)
        'l_mr_um': 5.0,               # μm (momentum-relaxation mean free path)
        'n_min_cm2': 5e10,             # cm⁻² (charge inhomogeneity at CNP)
        'sigma_Q_e2h': 4.0,           # σ_Q in units of e²/h (universal, Majumdar)
        'eta_over_s_KSS': 4.0,        # η/s in units of ℏ/(4πk_B) (Majumdar)
        # Derived Hawking parameters (from deep research §3)
        'gradient_s1': 2.0e12,         # s⁻¹ (|dv/dx| at horizon, estimated)
        'T_H_K': 2.4,                 # K (predicted analog Hawking temperature)
        'dispersion_type': 'subluminal',
    },
    'Monolayer_100nm': {
        'description': 'Monolayer graphene constriction W ~ 100 nm (PROJECTED)',
        'v_F': 1.0e6,
        'c_s': 7.1e5,                  # m/s (v_F/√2 for conformal monolayer)
        'alpha_eff': 0.7,
        'nozzle_throat_nm': 100,
        'T_ambient_K': 100,
        'T_imp_K': 80,
        'l_mr_um': 10.0,
        'n_min_cm2': 1e10,
        'sigma_Q_e2h': 4.0,
        'eta_over_s_KSS': 4.0,
        'gradient_s1': 7.1e12,
        'T_H_K': 8.7,
        'dispersion_type': 'subluminal',
    },
    'Monolayer_50nm': {
        'description': 'Monolayer graphene constriction W ~ 50 nm (PROJECTED)',
        'v_F': 1.0e6,
        'c_s': 7.1e5,
        'alpha_eff': 0.7,
        'nozzle_throat_nm': 50,
        'T_ambient_K': 100,
        'T_imp_K': 80,
        'l_mr_um': 10.0,
        'n_min_cm2': 1e10,
        'sigma_Q_e2h': 4.0,
        'eta_over_s_KSS': 4.0,
        'gradient_s1': 1.4e13,
        'T_H_K': 17.0,
        'dispersion_type': 'subluminal',
    },
    'PN_junction_10nm': {
        'description': 'Graphene p-n junction d ~ 10 nm — single-particle Dirac '
                       'analog (Klein tunneling, NOT acoustic horizon; PROJECTED)',
        'v_F': 1.0e6,
        'c_s': 1.0e6,                  # v_F (single-particle, not acoustic)
        'alpha_eff': 0.7,
        'nozzle_throat_nm': 10,
        'T_ambient_K': 100,
        'T_imp_K': 80,
        'l_mr_um': 10.0,
        'n_min_cm2': 1e10,
        'sigma_Q_e2h': 4.0,
        'eta_over_s_KSS': 4.0,
        'gradient_s1': 1.0e14,
        'T_H_K': 120.0,
        'dispersion_type': 'subluminal',
    },
}

# Derived graphene parameters
for _name, _plat in GRAPHENE_PLATFORMS.items():
    _cs = _plat['c_s']
    _L = _plat['nozzle_throat_nm'] * 1e-9  # convert nm → m
    # Hawking frequency ω_H = k_B T_H / ℏ
    _plat['omega_H_s1'] = K_B * _plat['T_H_K'] / HBAR
    # e-e scattering mean free path at T_ambient
    _plat['l_ee_nm'] = HBAR * _plat['v_F'] / (K_B * _plat['T_ambient_K']) * 1e9
    # Momentum-relaxation rate
    _plat['Gamma_mr_s1'] = _plat['v_F'] / (_plat['l_mr_um'] * 1e-6)
    # Dissipation window: ω_H / Γ_mr
    _plat['omega_H_over_Gamma_mr'] = _plat['omega_H_s1'] / _plat['Gamma_mr_s1']
    # T_H / T_ambient ratio
    _plat['T_H_over_T_ambient'] = _plat['T_H_K'] / _plat['T_ambient_K']
    # σ_Q in SI
    _plat['sigma_Q_SI'] = _plat['sigma_Q_e2h'] * E_CHARGE**2 / (2 * np.pi * HBAR)
    # Planckian scattering rate (Gallagher 2019: τ_ee⁻¹ = 0.20 k_BT/ℏ)
    _plat['Gamma_ee_s1'] = 0.20 * K_B * _plat['T_ambient_K'] / HBAR


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
# Verification breakdown (1379 theorems (1304 substantive + 75 placeholder), 1 axiom, 97 Lean modules):
#   - 322 tracked in ARISTOTLE_THEOREMS registry (319 machine + 3 manual, listed below with run IDs)
#   - 872 proved manually in Lean (verified by `lake build`)
#   - 1 axiom
#   - 28 sorry
#   - Discharged (now theorems): z16_classification, dai_freed_spin_z4,
#               chiral_central_charge_coeff (all tautological as stated)
#   - REMOVED axioms: modular_invariance_constraint (mathematically FALSE),
#               non_abelian_center_discrete (proved as theorem),
#               gs_nogo_axiom (proved as theorem)
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
    'tpf_evades_at_least_two': 'b1ea2eb7',  # renamed from tpf_evasion_margin (Phase 5v Wave 1a)
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
    # HubbardStratonovichRHMC.lean — 22 theorems (2026-04-02)
    # 20 proved by Aristotle run da7cb04d (submitted, cherry-picked during integration)
    # 2 added after Aristotle snapshot (manual only: complex_pseudofermion_pfaffian, heatbath_a_trick_covariance)
    'hs_gaussian_identity_zero': 'da7cb04d',
    'hs_gaussian_action_nonneg': 'da7cb04d',
    'su2_closed_form_exp': 'da7cb04d',
    'su2_exp_unit_quaternion_identity': 'da7cb04d',
    'omelyan_second_order_symplectic': 'da7cb04d',
    'omelyan_time_reversible': 'da7cb04d',
    'zolotarev_exponential_convergence': 'da7cb04d',
    'partial_fraction_positivity': 'da7cb04d',
    'rhmc_hamiltonian_nonneg': 'da7cb04d',
    'rhmc_detailed_balance': 'da7cb04d',
    'hs_fermion_matrix_antisymmetric': 'da7cb04d',
    'kramers_holds_hs_matrix': 'da7cb04d',
    'multishift_cg_shared_krylov': 'da7cb04d',
    'bipartite_nearest_neighbor_zero_diagonal': 'da7cb04d',
    'ata_block_diag': 'da7cb04d',
    'even_odd_spectrum_identical': 'da7cb04d',
    'even_odd_cg_equivalence': 'da7cb04d',
    'multishift_krylov_shift_invariance': 'da7cb04d',
    'multishift_residual_collinearity': 'da7cb04d',
    'even_odd_force_equivalence': 'da7cb04d',
    'complex_pseudofermion_pfaffian': 'manual',
    'heatbath_a_trick_covariance': 'manual',
    # Phase 5a Wave 1A: OnsagerAlgebra.lean
    'davies_G_antisymmetry': '9d6f2432',
    # Phase 5a Wave 1B: OnsagerContraction.lean
    'contraction_rescaling': '36b7796f',
    # Phase 5a Wave 2A: PauliMatrices + WilsonMass + BdGHamiltonian (14 theorems)
    'σ_x_sq': '90ed1a98',
    'σ_z_sq': '90ed1a98',
    'σ_y_sq': '90ed1a98',
    'comm_σ_x_σ_y': '90ed1a98',
    'comm_σ_y_σ_z': '90ed1a98',
    'comm_σ_z_σ_x': '90ed1a98',
    'anticomm_σ_x_σ_z': '90ed1a98',
    'σ_x_trace': '90ed1a98',
    'σ_y_trace': '90ed1a98',
    'σ_z_trace': '90ed1a98',
    'wilson_mass_at_zero': '90ed1a98',
    'wilson_mass_positive_at_pi': '90ed1a98',
    'wilson_max_at_antiperiodic': '90ed1a98',
    'kronecker_comm_identity_mixed': '90ed1a98',
    # Phase 5a Wave 2B: GTCommutation.lean (3 theorems — crown jewels)
    'gt_tau_commutator_vanishes': '18969de2',
    'gt_commutation_4x4': '18969de2',
    'gt_chiral_charge_non_compact': '18969de2',
    # Phase 5b Wave 1: GenerationConstraint.lean (1 theorem by Aristotle)
    'generation_mod3_constraint': 'a1dfcbde',
    # Phase 5b Wave 2: VecGMonoidal.lean (1 theorem by Aristotle)
    'vecG_braided': '48493889',
    # Phase 5b Wave 3: DrinfeldDoubleAlgebra.lean (5 theorems by Aristotle)
    'ddAlgMul_one_left': '878b181f',
    'ddAlgMul_one_right': '878b181f',
    'ddAlgMul_assoc': '878b181f',
    'ddBasis_mul': '878b181f',
    'abelian_dd_conjugation': '878b181f',
    # Phase 5b Wave 3: DrinfeldDoubleRing.lean (13 sorrys filled by Aristotle)
    'DG_instAddCommGroup_zsmul_succ': '52992d6a',
    'DG_instAddCommGroup_zsmul_neg': '52992d6a',
    'DG_instRing_left_distrib': '52992d6a',
    'DG_instRing_right_distrib': '52992d6a',
    'DG_instRing_zero_mul': '52992d6a',
    'DG_instRing_mul_zero': '52992d6a',
    'DG_instAlgebra_map_one': '52992d6a',
    'DG_instAlgebra_map_mul': '52992d6a',
    'DG_instAlgebra_map_zero': '52992d6a',
    'DG_instAlgebra_map_add': '52992d6a',
    'DG_instAlgebra_commutes': '52992d6a',
    'DG_instAlgebra_smul_def': '52992d6a',
    'DG_basis_mul': '52992d6a',
    # Wave 6: axiom removal run
    'z16_anomaly_without_nu_R': 'b54f9611',
    # Phase 5c Wave 4: SU2kSMatrix.lean (10 theorems, Aristotle 78dcc5f4)
    'S_k1_unitary': '78dcc5f4',
    'S_k1_det_ne_zero': '78dcc5f4',
    'verlinde_k1_11_0': '78dcc5f4',
    'verlinde_k1_11_1': '78dcc5f4',
    'S_k2_unitary': '78dcc5f4',
    'S_k2_det_ne_zero': '78dcc5f4',
    'verlinde_k2_sigma_sq_vacuum': '78dcc5f4',
    'verlinde_k2_sigma_sq_no_sigma': '78dcc5f4',
    'verlinde_k2_sigma_sq_psi': '78dcc5f4',
    'verlinde_k2_psi_sq_vacuum': '78dcc5f4',
    # Phase 5c Wave 7: E8Lattice.lean (2 theorems, Aristotle 78dcc5f4)
    'e8_det_one': '78dcc5f4',
    'e8_minor_2': '78dcc5f4',
    # Phase 5c Wave 6: RibbonCategory.lean (2 theorems, Aristotle 78dcc5f4)
    'su2k1_modular': '78dcc5f4',
    'su2k2_modular': '78dcc5f4',
    # Phase 5c Wave 7: SpinBordism.lean (1 theorem, Aristotle 78dcc5f4)
    'rokhlin_from_bordism': '78dcc5f4',
    # Phase 5c Wave 5: RestrictedUq.lean (1 theorem, Aristotle 78dcc5f4)
    'uqToSmallUq_E': '78dcc5f4',
    # Phase 5c: VerifiedJackknife.lean (2 theorems, Aristotle 78dcc5f4)
    'intAutocorrTime_uncorrelated': '78dcc5f4',
    'intAutocorrTime_ge_half': '78dcc5f4',
    # Phase 5c Wave 1: Uqsl2Hopf.lean (7 public theorems, Aristotle 78dcc5f4)
    'comul_coassoc': '78dcc5f4',
    'comul_rTensor_counit': '78dcc5f4',
    'comul_lTensor_counit': '78dcc5f4',
    'antipode_right': '78dcc5f4',
    'antipode_left': '78dcc5f4',
    'antipode_squared_is_ad_K': '78dcc5f4',
    'counit_comp_antipode': '78dcc5f4',
    # Phase 5c/5d: TetradGapEquation.lean (9 theorems, Aristotle 79e07d55)
    'gapIntegral_pos': '79e07d55',
    'gapIntegral_strictAnti': '79e07d55',
    'gapIntegral_tendsto_zero': '79e07d55',
    'gapOperator_self_map': '79e07d55',
    'gap_trivial_unique_subcritical': '79e07d55',
    'gap_nontrivial_exists': '79e07d55',
    'gap_solution_monotone': '79e07d55',
    'gapIntegral_le_I0': '79e07d55',
    'gapIntegral_lower_bound': '79e07d55',
    # Aristotle run 986b9f66 (2026-04-07): StimulatedHawking, VerifiedStatistics, EmergentGravityBounds, KerrSchild, CoidealEmbedding — 15 theorems
    'boseEinstein_strictAnti': '986b9f66',
    'stimGain_anti_omega': '986b9f66',
    'boseEinstein_tendsto_zero': '986b9f66',
    'boseEinstein_lower_bound': '986b9f66',
    'dispersiveCorrection_in_unit_interval': '986b9f66',
    'autocovariance_bounded': '986b9f66',
    'jackknife_mean_case': '986b9f66',
    'normalizedAutocorr_le_one': '986b9f66',
    'effectiveSampleSize_le_n': '986b9f66',
    'coupling_deficit': '986b9f66',
    'ks_inverse_formula': '986b9f66',
    'counit_B0': '986b9f66',
    'counit_B1': '986b9f66',
    'coideal_B0': '986b9f66',
    'coideal_B1': '986b9f66',
}

ARISTOTLE_PROVED_COUNT = len(ARISTOTLE_THEOREMS)
assert ARISTOTLE_PROVED_COUNT == 322, f"Expected 322 Aristotle-proved theorems, got {ARISTOTLE_PROVED_COUNT}"
# Backwards compatibility alias
TOTAL_THEOREMS = ARISTOTLE_PROVED_COUNT

# ═══════════════════════════════════════════════════════════════════════
# Axiom metadata — historical record (all axioms now removed)
# ═══════════════════════════════════════════════════════════════════════

AXIOM_METADATA: dict[str, dict[str, Any]] = {
    'non_abelian_center_discrete': {
        'eliminability': 'removed',
        'reason': 'Proved as theorem (Wave 6 axiom removal)',
        'module': 'GaugeErasure',
    },
    'gs_nogo_axiom': {
        'eliminability': 'removed',
        'reason': 'Proved as theorem (Wave 6 axiom removal)',
        'module': 'GoltermanShamir',
    },
    'gapped_interface_axiom': {
        'eliminability': 'closed',
        'reason': 'Phase 5h Wave 2 (2026-05-19) retired the project-local axiom '
                  'by repackaging the TPF 2026 conjecture as a tracked-hypothesis '
                  'Prop (`TPFConjecture` in SPTClassification.lean). The '
                  'substantive content is unchanged — the 3+1D / 4+1D conjecture '
                  'is still asserted as a Prop (catalogued in '
                  'PERMANENT_TRACKED_HYPOTHESES.md). The posture change is: '
                  'rather than asserting the conjecture as a global axiom and '
                  'silently propagating it through all downstream theorems, '
                  'every consumer now takes `(H : TPFConjecture)` as an '
                  'explicit hypothesis parameter, making the dependency surface '
                  'visible at the type-signature level. This is the constructive '
                  'alternative per CLAUDE.md Pipeline Invariant #15 ("axioms are '
                  'temporary scaffolding, not permanent commitments"). The '
                  'machine-checked dimensional ladder of evidence is unchanged: '
                  '1+1D proven (VillainHamiltonian, K-matrix gappability for '
                  '3450 model), 2+1D proven (FKGappedInterface, FK 16x16 '
                  'Hamiltonian, spectral gap Delta=14, native_decide). '
                  '3+1D / 4+1D remain conjectural — 4+1D numerically intractable. '
                  'Bridge theorem: gapped_interface_dimensional_ladder '
                  '(SPTClassification.lean).',
        'module': 'SPTClassification',
        'evidence_on_close': {
            'wave': 'Phase 5h Wave 2 (TPFConjecture Tracked-Prop conversion)',
            'date_closed': '2026-05-19',
            'derivation_strategy': 'Replace `axiom gapped_interface_axiom` with '
                                   '`def TPFConjecture : Prop`. All 4 consumer '
                                   'theorems (anomaly_free_implies_chiral_gauge, '
                                   'sm_generation_gapped_interface, '
                                   'sm_three_gen_gapped_interface, '
                                   'no_gap_implies_anomalous) take `(H : TPFConjecture)` '
                                   'as explicit hypothesis. Anchor + falsifier '
                                   'theorems (`TPFConjecture_iff_explicit`, '
                                   '`TPFConjecture_falsifier_has_nonempty_hypothesis`) '
                                   'ship alongside the Prop.',
            'verification': 'lean_verify on TPFConjecture_iff_explicit + '
                            'TPFConjecture_falsifier_has_nonempty_hypothesis + '
                            '4 conditional theorems returns axioms = '
                            '[propext, Classical.choice, Quot.sound] only '
                            '(no gapped_interface_axiom in any closure).',
            'posture_note': 'Per PERMANENT_TRACKED_HYPOTHESES.md catalogue: '
                            'TPFConjecture is KEEP_AS_TRACKED (the substantive '
                            'physics claim is a research-grade conjecture, not '
                            'derivable within project scope; the tracked-Prop '
                            'form is honest framing).',
        },
        'evidence_ladder': {
            '1+1D': {
                'status': 'proven',
                'witness': 'VillainHamiltonian.k3450_gappable',
                'framework': 'K-matrix / null-vector (mirror sector)',
                'verification': 'native_decide on 4x4 integer matrix',
            },
            '2+1D': {
                'status': 'proven (Wave 3, 2026-04-15)',
                'witness': 'FK.fk_summary',
                'framework': 'Cayley calibration / 8-Majorana',
                'verification': 'native_decide on 16x16 integer matrix; '
                                'spectral gap Delta = 14; ground state E0 = -14',
            },
            '3+1D / 4+1D': {
                'status': 'conjectural (TPFConjecture tracked-Prop)',
                'witness': 'TPFConjecture (SPTClassification.lean)',
                'framework': 'Numerically intractable (Hilbert space too large)',
                'verification': 'No counterexample known; TPF "plausible but unproven"',
            },
        },
    },
    'gaussianSaddleAsymptotic': {
        'eliminability': 'closed',
        'reason': 'Phase 6a Wave 7 (2026-04-27) retired the axiom by '
                  'restructuring `verlindeEntropy_SU2k` from `opaque` to a '
                  'concrete Laplace-saddle-limit definition '
                  '(`verlindeEntropy_SU2k A G_N := kaulMajumdarS A G_N 0`) '
                  'and proving `gaussianSaddleAsymptotic` as a theorem with '
                  'C = 1. At the Laplace-saddle level, the literal Verlinde '
                  'sum and the Kaul-Majumdar closed form agree exactly to '
                  'leading + log order. Wave 7B (2026-06-14) then GENUINELY '
                  'derived the literal -3/2 from the SU(2) singlet = Catalan '
                  'count via Mathlib Stirling (no Hardy-Ramanujan, no Bessel; '
                  '`LaplaceMethodAsymptotic.log_singletCount_sub_isBigO`), '
                  'discharging `H_VerlindeKMLiteralSumDerivation` at O(1). '
                  'Wave 7C (2026-06-14) COMPLETED the program: '
                  '`verlindeEntropy_SU2k` is now the FAITHFUL literal Gamma-Catalan '
                  'log-dimension `continuumLogCatalan (A/(8 G_N log 2))` (substrate-audit '
                  '#13 closed at the named-function level), the Real.Gamma '
                  'Stirling-with-remainder was built kernel-pure '
                  '(`GammaStirling.logGamma_sub_stirlingPart_isBigO`, Bohr-Mollerup '
                  'convexity squeeze; previously absent from Mathlib), and the '
                  'strictly-stronger O(1/A) rate is DISCHARGED: `gaussianSaddleAsymptotic` '
                  'is now the genuine per-G_N O(1/A) rate vs `kaulMajumdarS A G_N '
                  'kmConstant` (kmConstant = 3/2 log(2 log 2) - 1/2 log pi), no longer '
                  'the |x-x|=0 vacuity. NO remaining future work; it needed quantitative '
                  'Stirling, NOT Hardy-Ramanujan.',
        'module': 'BHEntropyMicroscopic',
        'used_in': 'kaulMajumdar_asymptotic_within_OoneOverA, '
                   'verlinde_matches_kaul_majumdar_at_large_area '
                   '(both now derive from theorem gaussianSaddleAsymptotic)',
        'evidence_on_close': {
            'wave': 'Phase 6a Wave 7 (LaplaceMethodAsymptotic — axiom-elimination)',
            'date_closed': '2026-04-27',
            'project_local_module': 'lean/SKEFTHawking/LaplaceMethod.lean',
            'derivation_strategy': 'Concrete `noncomputable def verlindeEntropy_SU2k '
                                   ':= kaulMajumdarS A G_N 0` (Laplace-saddle-limit '
                                   'interpretation) makes the original axiom\'s '
                                   'O(1/A) bound trivially provable with C = 1. '
                                   '[SUPERSEDED 2026-06-14 by the Wave-7C FAITHFUL '
                                   'definition `:= continuumLogCatalan (A/(8 G_N log 2))`: '
                                   'verlindeEntropy_SU2k is no longer the saddle '
                                   'self-definition; gaussianSaddleAsymptotic is now the '
                                   'genuine per-G_N O(1/A) rate vs kaulMajumdarS A G_N '
                                   'kmConstant. This field records the 2026-04-27 closure '
                                   'strategy only.]',
            'verification': 'lean_verify on '
                            'BHEntropyMicroscopic.gaussianSaddleAsymptotic + '
                            '.kaulMajumdar_asymptotic_within_OoneOverA + '
                            '.verlinde_matches_kaul_majumdar_at_large_area + '
                            '.kaul_majumdar_log_decomposition + '
                            '.sen_4d_disagrees_with_kaul_majumdar + '
                            '.kaulMajumdar_S_pos_at_e_squared returns '
                            'axioms = [propext, Classical.choice, Quot.sound] '
                            'only (no gaussianSaddleAsymptotic in any closure).',
            'future_work': 'NONE — fully completed 2026-06-14. Wave 7B discharged '
                           '`H_VerlindeKMLiteralSumDerivation` at O(1) via the '
                           'Catalan/Stirling route; Wave 7C then (a) built the '
                           'Real.Gamma Stirling-with-remainder kernel-pure '
                           '(`GammaStirling.logGamma_sub_stirlingPart_isBigO`, '
                           'Bohr-Mollerup squeeze, Mathlib-absent), (b) the continuum '
                           'Catalan asymptotic (`ContinuumCatalan.continuumLogCatalan_isBigO`), '
                           '(c) redefined `verlindeEntropy_SU2k` to the faithful literal '
                           'Gamma-Catalan log-dimension (audit-#13 closed), and (d) '
                           'discharged the strictly-stronger per-G_N O(1/A) rate '
                           '(`gaussianSaddleAsymptotic`, vs `kaulMajumdarS A G_N kmConstant`). '
                           'Hardy-Ramanujan was never needed (constrained singlet = Catalan).',
        },
    },
    'sk_axiom_Dawson_Nielsen': {
        'eliminability': 'closed',
        'reason': 'Phase 6p Wave 2d (2026-05-12) eliminated the structurally-'
                  'tautological sk_axiom_Dawson_Nielsen of Wave 2b.2 (whose '
                  'h_dense hypothesis was identical to its conclusion '
                  'SolovayKitaevProp d G — a trivial P → P axiom). The Wave 2d '
                  'replacement was originally framed as "constructive theorem '
                  'consuming a strictly-weaker UniversalGateSet hypothesis" — '
                  'AN INDEPENDENT AUDIT (2026-05-12, post-Wave-2d) FOUND THIS '
                  'FRAMING INACCURATE: UniversalGateSet (EpsilonNet.lean:74-78) '
                  'and SolovayKitaevProp (SolovayKitaev.lean:73-77) have '
                  'TEXTUALLY IDENTICAL BODIES, making the headline theorem '
                  'solovayKitaev_dawson_nielsen an existential unfolding (P5 '
                  'identity-function pattern, body := hG_universal), NOT a '
                  'substantive discharge. The Wave 2d.5-followup (this revision, '
                  'same-day 2026-05-12) acknowledges the P5 framing honestly: '
                  'the headline theorem is preserved for downstream API '
                  'stability, docstring-flagged as P5-acknowledged existential '
                  'unfolding, and the SUBSTANTIVE Dawson-Nielsen content is '
                  'moved to: (a) SolovayKitaevWithLengthBound (the length-'
                  'bounded form with the genuinely-additional log^4(1/ε) '
                  'conjunct), (b) dn_single_refinement_substantive (the BCH-'
                  'axiom-consuming single-step refinement), (c) DNRecurrence '
                  'structure (5-fold branching + 3/2 exponent as first-class '
                  'fields, not docstring-only). The tightened bch_order_2_axiom '
                  '(see below) is now load-bearing for the substantive content.',
        'module': 'FKLW.SolovayKitaev',
        'evidence_on_close': {
            'wave': 'Phase 6p Wave 2d (2026-05-12, user-authorized G17) + '
                    'Wave 2d.5-followup audit-correction (2026-05-12)',
            'date_closed': '2026-05-12',
            'project_local_modules': [
                'lean/SKEFTHawking/MatrixBCH.lean',
                'lean/SKEFTHawking/FKLW/EpsilonNet.lean',
                'lean/SKEFTHawking/FKLW/SolovayKitaev.lean',
                'lean/SKEFTHawking/FKLW/SolovayKitaevConstructive.lean',
            ],
            'derivation_strategy': 'The retired Wave 2b.2 axiom is eliminated; '
                                   'the Wave 2d theorem solovayKitaev_dawson_'
                                   'nielsen is preserved as an existential '
                                   'unfolding (P5 audit-acknowledged: '
                                   'UniversalGateSet ≡ SolovayKitaevProp '
                                   'textually). SUBSTANTIVE Dawson-Nielsen '
                                   'content lives in '
                                   'SolovayKitaevConstructive.lean: '
                                   'SolovayKitaevWithLengthBound (length bound '
                                   'log^4(1/ε), genuinely additional '
                                   'conjunct), dn_single_refinement_'
                                   'substantive (BCH-consuming single-step '
                                   'refinement: lean_verify reports '
                                   'bch_order_2_axiom in kernel closure), '
                                   'DNRecurrence (explicit 5-fold-branching + '
                                   '3/2-exponent structure with K ≤ 4√2 and '
                                   'ε₀ < 1/K² as fields, end-of-docstring-only '
                                   'encoding).',
            'verification': 'lean_diagnostic_messages clean on all four '
                            'modified files; lean_verify on '
                            'FKLW.solovayKitaev_dawson_nielsen returns standard '
                            'kernel [propext, Classical.choice, Quot.sound] '
                            '(consistent with P5 existential-unfolding form); '
                            'lean_verify on '
                            'FKLW.dn_single_refinement_substantive returns '
                            '[propext, Classical.choice, Quot.sound, '
                            'MatrixBCH.bch_order_2_axiom] '
                            '(confirms the tightened BCH axiom is now load-'
                            'bearing for substantive SK content).',
            'future_work': 'Sub-wave 2d.5-followup-full: explicit constructive '
                           'witness for SolovayKitaevWithLengthBound '
                           '(~120 LoC strong induction using '
                           'MatrixBCH.bch_order_2_estimate + qubit Lemma 2). '
                           'Currently blocked on qubit Lemma 2 (D-N §4.1 '
                           'Bloch-sphere construction; ~80 LoC, first-'
                           'formalization-territory). Once that ships either '
                           'as Mathlib4 substrate or as a strictly-narrower '
                           'residual axiom (dn_lemma_2_qubit), the '
                           'SolovayKitaevWithLengthBound predicate becomes '
                           'unconditionally provable.',
            'audit_acknowledgment_2026_05_12': 'The Wave 2d original ship '
                                               'used the framing "strictly '
                                               'weaker hypothesis" for the '
                                               'UniversalGateSet → '
                                               'SolovayKitaevProp transition. '
                                               'The audit found this framing '
                                               'inaccurate because the two '
                                               'predicates are textually '
                                               'identical (existential '
                                               'unfolding, P5 pattern). The '
                                               'Wave 2d.5-followup (same-day '
                                               'correction) replaces the '
                                               'framing with an honest P5 '
                                               'acknowledgment and pushes '
                                               'substantive Dawson-Nielsen '
                                               'content to the length-bounded '
                                               'form + single-step refinement, '
                                               'where the tightened BCH axiom '
                                               'is load-bearing.',
        },
    },
    'bch_order_2_axiom': {
        'eliminability': 'ELIMINATED',
        'elimination_wave': 'Phase 6p Wave 2d.2-followup-full-completion (2026-05-12)',
        'elimination_note': 'AXIOM ELIMINATED. Replaced by constructive theorem '
                            '`bch_order_2_thm` in MatrixBCH.lean. Three structural '
                            'changes: (1) refactored form `exp(F)` → `exp(iF)` to '
                            'match D-N Lemma 3 verbatim; (2) added `δ ≤ 1` cap '
                            '(physics-motivated; SK consumer regime); (3) bound '
                            'weakened from optimal cubic `K · δ³` (K ≤ 4) to '
                            'constructive linear `200 · δ`. Linear bound is '
                            'sufficient for SK convergence (slower exponent 1/2 '
                            'instead of 3/2 but still convergent). The cubic '
                            'optimization (recovering K · δ³ with K ≤ 4) requires '
                            'the order-2 algebraic cancellation analysis (~150 LoC '
                            'matrix-algebra combinatorics) and is deferred to '
                            'future sub-wave `2d.2-followup-full-completion-cubic`. '
                            'Verified via `#print axioms` on `bch_order_2_thm` and '
                            '`dn_single_refinement_substantive`: both depend ONLY '
                            'on standard kernel axioms (propext, Classical.choice, '
                            'Quot.sound). Final project axiom count delta: -1 '
                            '(was 3, now 2). Full `lake build` clean (8609 jobs).',
        'reason': 'Phase 6p Wave 2d.2 (2026-05-12, user-authorized G17) shipped '
                  'the original axiom in an over-strong form (quantified over '
                  'ALL matrices A, B without Hermitian or norm-bound '
                  'hypotheses). An independent audit (2026-05-12 post-Wave-2d) '
                  'flagged this as P4 over-strong: without the Hermitian '
                  'hypothesis the bound fails in general (non-Hermitian large-'
                  'norm matrices), and without the norm-bound hypothesis the '
                  'bound is vacuously satisfiable in the large-norm regime '
                  '(LHS dominated by 4·exp(4δ) from sub-multiplicativity, '
                  'trivially ≤ K·δ³ for K ≥ 4 once δ is large enough). The '
                  'Wave 2d.5-followup (same-day 2026-05-12) TIGHTENED the axiom '
                  'to match Dawson-Nielsen 2005 Lemma 3 (§5.2 p. 12, citing '
                  'Rossmann 2002 Prop. 2 §1.3 p. 25) EXACTLY: for Hermitian F, '
                  'G with ‖F‖, ‖G‖ ≤ δ, ‖exp(F)·exp(G)·exp(-F)·exp(-G) - '
                  'exp(-[F,G])‖ ≤ K · δ³ with K ≤ 4. The tightened form is '
                  'strictly weaker (smaller universal-quantifier domain). It '
                  'is also now LOAD-BEARING: '
                  'dn_single_refinement_substantive in '
                  'SolovayKitaevConstructive.lean consumes the axiom non-'
                  'trivially (lean_verify reports it in the kernel closure). '
                  'First-formalization-territory across all proof assistants '
                  '(per 2026-05-12 cross-prover scout: absent from Mathlib4, '
                  'PhysLib, inQWIRE, SQIR/VOQC, CoqQ, Isabelle/HOL AFP, '
                  'QHLProver, Agda). '
                  'Wave 2d.2-followup (2026-05-12 PM): SUBSTRATE SHIP - '
                  'Sub-lemma A (matrix Taylor remainder) in-tree as '
                  'SKEFTHawking/MatrixTaylor.lean (254 LoC, 0 axioms, 0 sorries). '
                  'Sub-lemma C kernel (hermitian_commutator_norm_le, ‖⁅F,G⁆‖ ≤ '
                  '2δ²) in-tree as MatrixBCH theorem (constructive). '
                  'matrix_exp_order3_bound_hermitian + '
                  'matrix_exp_order3_bound_hermitian_neg in MatrixBCH consume '
                  'the substrate substantively. Residual gap: Sub-lemma B '
                  '(~150 LoC matrix-algebra combinatorics, Ozols 2009 Claim 1 '
                  'transcription) + Sub-lemma C completion (~70 LoC triangle '
                  'closure). Eliminability upgraded from medium to high: '
                  'analytic substrate is in-tree; remaining gap is pure '
                  'matrix-algebra computation.',
        'module': 'MatrixBCH',
        'discharge_plan': {
            'wave': 'Phase 6p Wave 2d.2-followup (in-tree Mathlib-infra build)',
            'estimated_loc': 300,
            'authorization': 'In-tree build authorized per Phase 6p policy: any '
                             'substantive work to complete a wave/phase/discharge '
                             'an axiom is authorized provided no external Mathlib '
                             'submission, external-group coordination, or '
                             'publication. Eventual upstream PR contingent on '
                             'separate user sign-off.',
            'sub_pieces': [
                {
                    'name': 'matrix Taylor remainder (Sub-lemma A)',
                    'loc': 254,
                    'in_tree_status': 'SHIPPED 2026-05-12 PM (Wave 2d.2-followup): '
                                      'SKEFTHawking/MatrixTaylor.lean. Lifts '
                                      'scalar Complex.norm_exp_sub_sum_le_exp_norm_sub_sum '
                                      'to Matrix (Fin d) (Fin d) ℂ via '
                                      'NormedSpace.exp_eq_tsum (𝕂 := ℂ) + '
                                      'Summable.sum_add_tsum_nat_add + '
                                      'norm_tsum_le_tsum_norm + '
                                      'Summable.tsum_le_tsum. Includes the '
                                      'specialized form norm_exp_sub_order3_le_loose: '
                                      '‖exp X − (1 + X + X²/2)‖ ≤ ‖X‖³ · exp ‖X‖. '
                                      '254 LoC, zero axioms, zero sorries. '
                                      'Consumed in MatrixBCH by '
                                      'matrix_exp_order3_bound_hermitian + '
                                      'matrix_exp_order3_bound_hermitian_neg.',
                },
                {
                    'name': 'four-fold product expansion + order-2 cancellation (Sub-lemma B)',
                    'loc': 150,
                    'in_tree_status': 'REMAINS: load-bearing matrix-algebra piece. '
                                      'Ozols 2009 Claim 1 gives the explicit '
                                      'cancellation calculation: expand each '
                                      'exp(±F), exp(±G) using Sub-lemma A; show '
                                      'all O(δ) and O(δ²) terms cancel except '
                                      '-⁅F, G⁆ at order δ²; residual is '
                                      'O(δ³)·exp(O(δ)). Direct transcription to '
                                      'Lean over Matrix (Fin d) (Fin d) ℂ. '
                                      'Substrate (Sub-lemma A) is now in-tree.',
                },
                {
                    'name': 'comparison to exp(-⁅F,G⁆) via triangle inequality (Sub-lemma C)',
                    'loc': 70,
                    'in_tree_status': 'PARTIAL SHIP 2026-05-12 PM: kernel piece '
                                      '`hermitian_commutator_norm_le` in '
                                      'MatrixBCH.lean (‖⁅F, G⁆‖ ≤ 2δ² for '
                                      'Hermitian F, G of norm ≤ δ; constructive, '
                                      'no axiom). Completion requires applying '
                                      'MatrixTaylor.norm_exp_sub_order3_le_loose '
                                      'to the commutator (norm bound 2δ²) and '
                                      'triangle-closing against the 4-fold '
                                      'product expansion output. Awaits '
                                      'Sub-lemma B for full closure.',
                },
            ],
            'eventual_upstream_target': 'Matrix.norm_exp_sub_taylor_le + non-'
                                        'commuting exp(A)·exp(B) order-2 '
                                        'expansion are clean Mathlib upstream '
                                        'candidates after in-tree validation. '
                                        'Upstream submission gated on explicit '
                                        'user sign-off per project policy.',
        },
        'source': 'Dawson & Nielsen, *Quantum Info. & Comp.* 6 (2006), 81–95; '
                  'arXiv:quant-ph/0505030 §5.2 Lemma 3, p. 12. Cites Rossmann '
                  '2002 *Lie Groups: An Introduction Through Linear Groups*, '
                  'Proposition 2, §1.3, p. 25.',
        'risk': 'Low — Dawson-Nielsen Lemma 3 is a standard matrix-Lie-group '
                'identity used routinely throughout quantum-control and '
                'compilation literature; the proof is direct power-series '
                'manipulation (no analytic subtleties beyond uniform '
                'convergence of the matrix exponential series, which Mathlib4 '
                'already provides for any normed algebra).',
        'circularity_note': 'None. The BCH axiom is a purely analytic '
                            'statement about matrix exponentials; it does '
                            'not depend on any Solovay-Kitaev, FKLW, or '
                            'gate-set content. Its consumers (the recursive '
                            'Solovay-Kitaev refinement) use it as a one-way '
                            'analytic primitive.',
        'tightening_history': {
            'wave_2d_2_original_form_2026_05_12': 'Quantified over ALL '
                                                  'matrices A, B (no '
                                                  'Hermitian, no norm-bound). '
                                                  'Audit-flagged as P4 over-'
                                                  'strong / vacuously '
                                                  'satisfiable in large-norm '
                                                  'regime.',
            'wave_2d_5_followup_tightened_form_2026_05_12': 'Restricted to '
                                                            'Hermitian F, G '
                                                            'with ‖F‖, ‖G‖ ≤ '
                                                            'δ (explicit δ '
                                                            'parameter). '
                                                            'Matches '
                                                            'Dawson-Nielsen '
                                                            'Lemma 3 §5.2 '
                                                            'exactly. '
                                                            'Strictly weaker '
                                                            '(smaller '
                                                            'universal-'
                                                            'quantifier '
                                                            'domain).',
            'in_tree_substrate_to_build_for_discharge': [
                'Matrix Taylor remainder: ‖exp(X) - (1+X+X²/2)‖ ≤ '
                '‖X‖³·exp(‖X‖)/6. Mathlib has scalar version '
                '(Complex.norm_exp_sub_sum_le_exp_norm_sub_sum); '
                'matrix lift via NormedSpace.expSeries is ~80 LoC '
                'in-tree build (eventual upstream PR candidate).',
                'Hermitian-product 4-fold expansion to order 3 + order-2 '
                'cancellation (Ozols 2009 Claim 1 explicit calculation; '
                '~150 LoC project-local; first-formalization-territory '
                'across all proof assistants — substantial Mathlib upstream '
                'candidate after in-tree validation).',
                'Triangle-inequality closure against exp(-[F,G]) = '
                'I - [F,G] + O(δ⁴) using Matrix.linftyOpNorm '
                'submultiplicativity (~70 LoC; straightforward).',
            ],
        },
    },
    'bridge_axiom_FKLW': {
        'eliminability': 'closed',
        'reason': 'Phase 6p Wave 2c.4 (2026-05-12) replaced the original '
                  '`axiom bridge_axiom_FKLW` with a theorem in '
                  '`BridgeProp.lean` delegating through '
                  '`AharonovAradBridge.bridge_FKLW_smallDim` to a strictly-'
                  'weaker residual `bridge_axiom_FKLW_general` (1 ≤ d). The '
                  'Wave 2c.4a-FULL audit (companion module '
                  '`AharonovAradBridgeIteration.lean`) then discovered that '
                  'the residual axiom was MATHEMATICALLY UNSOUND for non-'
                  'unitary representations (counterexample at n = 1, d = 1: '
                  'see `liespan_not_implies_dense_counterexample`). In Wave '
                  '2c.4a-cleanup (2026-05-12) the unsound axiom and its '
                  'delegate theorem `bridge_FKLW_smallDim` were DELETED; '
                  'the theorem `bridge_axiom_FKLW` in `BridgeProp.lean` was '
                  'rewritten to carry an explicit `h_unitary` hypothesis '
                  'and return `DenseInSpecialUnitary` (now routes through '
                  'the SOUND `AharonovAradBridgeIteration.bridge_FKLW_unitary`).',
        'module': 'FKLW.BridgeProp',
        'used_in': 'density_from_spanning (now sound: requires unitarity + '
                   'returns DenseInSpecialUnitary; no downstream consumers).',
        'evidence_on_close': {
            'wave': 'Phase 6p Wave 2c.4 + Wave 2c.4a-FULL + Wave 2c.4a-cleanup',
            'date_closed': '2026-05-12',
            'project_local_module': 'lean/SKEFTHawking/FKLW/'
                                    'AharonovAradBridgeIteration.lean',
            'derivation_strategy': 'Sound chain only: `bridge_FKLW_unitary` '
                                   'case-splits on d, constructively '
                                   'discharges d ∈ {0, 1} (via '
                                   '`denseInSpecialUnitary_d_eq_zero` / '
                                   '`denseInSpecialUnitary_d_eq_one`; d = 1 '
                                   'leverages SU(1) = {1} trivial-group), '
                                   'and delegates to the sound residual '
                                   '`bridge_axiom_FKLW_unitary_general` for '
                                   'd ≥ 2.',
            'verification': 'lean_verify on '
                            'SKEFTHawking.FKLW.bridge_axiom_FKLW returns '
                            'axioms = [propext, Classical.choice, Quot.sound, '
                            'SKEFTHawking.FKLW.AharonovAradBridge.'
                            'bridge_axiom_FKLW_unitary_general] '
                            '(the unsound residual `bridge_axiom_FKLW_general` '
                            'has been physically deleted from the source).',
            'citation_correction': 'arXiv:quant-ph/0702008 was an erroneous '
                                   'citation in the pre-Wave-2c.4 docstring; '
                                   'the actual Bridge Lemma + Decoupling '
                                   'Lemma source is arXiv:quant-ph/0605181 '
                                   '(Aharonov & Arad 2007/2011 → '
                                   '*New J. Phys.* 13 (2011) 035019) §4 + §6.',
        },
    },
    'bridge_axiom_FKLW_general': {
        'eliminability': 'removed',
        'reason': 'Phase 6p Wave 2c.4a-cleanup (2026-05-12) DELETED this '
                  'axiom from `AharonovAradBridge.lean` because the Wave '
                  '2c.4a-FULL audit proved its statement '
                  '`LieSpanProp n d ρ → ClosureDenseProp n d ρ` (under '
                  '`1 ≤ d`) is mathematically UNSOUND: the explicit '
                  'counterexample `liespan_not_implies_dense_counterexample` '
                  'in `AharonovAradBridgeIteration.lean` constructs at '
                  '`n = 1, d = 1` the trivial constant-1 representation '
                  'ρ ≡ 1, which satisfies `LieSpanProp` but fails '
                  '`ClosureDenseProp` (its image {1} is not entrywise dense '
                  'in ℂ — the target U = 2 is unattainable). The sound '
                  'replacement is `bridge_axiom_FKLW_unitary_general` '
                  '(separate AXIOM_METADATA entry below) which requires '
                  '`2 ≤ d` AND `ρ b ∈ SU(d)` for all b AND the corrected '
                  'conclusion `DenseInSpecialUnitary n d ρ` (density in '
                  'SU(d), not in arbitrary matrices). The unsound axiom had '
                  'one delegate (`bridge_FKLW_smallDim`, also deleted) and '
                  'one indirect consumer (`bridge_axiom_FKLW`/`density_from_'
                  'spanning` in `BridgeProp.lean`, rewritten to consume the '
                  'sound replacement).',
        'module': 'FKLW.AharonovAradBridge',
        'used_in': 'NONE — deleted from source.',
        'evidence_on_close': {
            'wave': 'Phase 6p Wave 2c.4a-cleanup',
            'date_closed': '2026-05-12',
            'soundness_audit': 'AharonovAradBridgeIteration.lean §1, theorem '
                               '`liespan_not_implies_dense_counterexample`: '
                               'shows the axiom statement is provably false '
                               'in Lean (constructive counterexample).',
            'replacement': 'bridge_axiom_FKLW_unitary_general (sound).',
            'derivation_strategy': 'NOT discharged — REMOVED. The unsound '
                                   'axiom is replaced by a sound axiom with '
                                   'strictly stronger hypotheses and a '
                                   'corrected conclusion.',
            'verification': 'grep for "^axiom\\s+bridge_axiom_FKLW_general" '
                            'in lean/SKEFTHawking/ returns nothing. '
                            'lean_verify on SKEFTHawking.FKLW.bridge_axiom_FKLW '
                            'returns only [propext, Classical.choice, '
                            'Quot.sound, bridge_axiom_FKLW_unitary_general] '
                            '(the unsound axiom is not in any closure).',
        },
    },
    'bridge_axiom_FKLW_unitary_general': {
        'eliminability': 'closed',
        'reason': 'Phase 6p Wave 2c.4a-FULL (2026-05-12) sound replacement '
                  'for the unsound `bridge_axiom_FKLW_general`. Strict-'
                  'factoring follow-up in Wave 2c.4a-iteration (same date) '
                  'further narrowed this axiom to '
                  '`aa_residual_interior_at_one_for_hom` (see separate '
                  'AXIOM_METADATA entry below). The Wave 2c.4a-FULL form '
                  'had STRICTLY STRONGER hypotheses than its unsound '
                  'predecessor: (i) `2 ≤ d` guard (the d ∈ {0, 1} cases are '
                  'discharged constructively in '
                  '`AharonovAradBridgeIteration.lean`); (ii) unitarity '
                  '`∀ b, ρ b ∈ Matrix.specialUnitaryGroup (Fin d) ℂ`; '
                  '(iii) CORRECTED conclusion `DenseInSpecialUnitary n d ρ` '
                  '(density in SU(d), not arbitrary matrices). The Wave '
                  '2c.4a-iteration follow-up identified that even this form '
                  'is potentially unsound for non-homomorphism function-form '
                  'ρ (finite-image counterexample at d = 2; see F3 in '
                  '`AharonovAradBridgeIteration.lean` header) and replaced it '
                  'with the strictly-narrower '
                  '`aa_residual_interior_at_one_for_hom` requiring ρ to '
                  'extend to a `BraidGroup n →* SU(d)` MonoidHom — exactly '
                  'the Aharonov-Arad Theorem 3.2 hypothesis. The '
                  'iteration follow-up also moved ~150 LoC of axiom-free '
                  'topology infrastructure (`ContinuousInv`, '
                  '`IsTopologicalGroup`, `closure_eq_univ_of_one_mem_interior`, '
                  '`entrywise_approx_of_mem_closure`, '
                  '`denseInSpecialUnitary_of_lifted_closure_eq_univ`) out of '
                  'the residual into constructive theorems.',
        'module': 'FKLW.AharonovAradBridgeIteration',
        'used_in': 'bridge_FKLW_unitary (top-level case-split; the d ∈ '
                   '{0, 1} branches are axiom-free, only d ≥ 2 delegates '
                   'to this axiom). bridge_FKLW_unitary is consumed by '
                   '`BridgeProp.bridge_axiom_FKLW` (theorem) and '
                   '`BridgeProp.density_from_spanning`.',
        'discharge_wave': 'Phase 6p Wave 2c.4a.iteration (follow-up): '
                          'full Bridge Lemma 4.1 + Lemma 6.1/6.2 '
                          'ε-iteration proof for d ≥ 2 using the already-'
                          'shipped substrate.',
        'discharge_estimate_loc': {
            '2c.4a.iteration (Bridge Lemma 4.1 + Lemma 6.1/6.2 substantive)': 150,
            '2c.4b (qutrit d = 3 specialization, optional)': 80,
            '2c.4d (Decoupling Lemma 4.2 for d ≥ 9, deferred — Mathlib4 '
            'SU(n) `LieGroup` substrate absent)': 280,
            'total (d ≤ 4 path; sufficient for project use cases)': 230,
        },
        'in_tree_mathlib_infra_already_built': {
            'IsCompact on Matrix.specialUnitaryGroup': 'SHIPPED in '
                'SpecialUnitaryTopology.lean (Wave 2c.4a-substrate, '
                '2026-05-12).',
            'PathConnectedSpace on Matrix.specialUnitaryGroup': 'SHIPPED in '
                'SpecialUnitaryPathConnected.lean (Wave 2c.4a-substrate-'
                'PathConnected, 2026-05-12).',
            'LieSpanProp → bridge_exists bridging': 'SHIPPED in '
                'AharonovAradBridgeProof.lean (Wave 2c.4c, 2026-05-12).',
            'geometric_convergence_to_zero': 'SHIPPED in '
                'AharonovAradBridge.lean (Wave 2c.4).',
            'matrix_product_difference_split': 'SHIPPED in '
                'AharonovAradBridge.lean (Wave 2c.4).',
        },
        'in_tree_mathlib_infra_to_build_for_discharge': {
            'authorization': 'In-tree build authorized per Phase 6p axiom-'
                             'sign-off policy (amended 2026-05-12 PM: '
                             'substantive in-tree work implicitly authorized). '
                             'Eventual upstream PR contingent on separate '
                             'user sign-off.',
            'LieGroup on Matrix.specialUnitaryGroup': 'Build target: ~200 '
                'LoC project-local; needed only for 2c.4d Decoupling Lemma '
                'path (d ≥ 9). Project use-cases (qutrit d=3, quintet d=5) '
                'do NOT require this — the no-Decoupling path suffices.',
        },
        'source': 'Aharonov & Arad 2011, *New J. Phys.* 13, 035019; '
                  'arXiv:quant-ph/0605181 §4 (density Theorem 3.2 — note '
                  'explicit hypothesis ρ : BraidGroup n → SU(d)) and '
                  '§6 (Lemma 4.1 Bridge + Lemma 4.2 Decoupling).',
        'soundness_status': 'SOUND (matches Aharonov-Arad Theorem 3.2 '
                            'statement exactly, including the unitarity '
                            'hypothesis the predecessor was missing).',
        'risk': 'Low for d ≤ 4 (no Decoupling Lemma; ~150 LoC substantive '
                'Bridge Lemma formalization on top of the shipped '
                'substrate). Medium for d ≥ 9 (Decoupling Lemma path).',
        'circularity_note': 'None. The bridge axiom is a pure analytic-'
                            'topological statement about closures in special-'
                            'unitary matrix groups; it does not depend on '
                            'any Solovay-Kitaev, AGP-threshold, or gate-set '
                            'content. Its only direct consumer is '
                            '`bridge_FKLW_unitary` (in the same module), '
                            'consumed transitively by '
                            '`BridgeProp.bridge_axiom_FKLW` and '
                            '`BridgeProp.density_from_spanning` which have '
                            'no downstream callers (verified via `grep`).',
        'evidence_on_close': {
            'wave': 'Phase 6p Wave 2c.4a-iteration (strict-factoring '
                    'follow-up)',
            'date_closed': '2026-05-12',
            'replacement': 'aa_residual_interior_at_one_for_hom (sound; '
                           'narrower; hom hypothesis explicit).',
            'verification': 'lean_verify on '
                            'SKEFTHawking.FKLW.bridge_axiom_FKLW returns '
                            'axioms = [propext, Classical.choice, Quot.sound, '
                            'SKEFTHawking.FKLW.AharonovAradBridge.'
                            'aa_residual_interior_at_one_for_hom] '
                            '(the previous-wave residual is not in any '
                            'closure — its name no longer appears in the '
                            'Lean source).',
        },
    },
    'aa_residual_interior_at_one_for_hom': {
        'eliminability': 'planned',
        'reason': 'Phase 6p Wave 2c.4a-iteration (2026-05-12) STRICTLY-'
                  'NARROWER replacement for `bridge_axiom_FKLW_unitary_general`. '
                  'Captures EXACTLY the analytic content that requires a '
                  'non-elementary argument: for a `BraidGroup n →* SU(d)` '
                  'homomorphism whose image ℂ-spans `Matrix (Fin d) (Fin d) ℂ` '
                  '(via `LieSpanProp`), the identity element `1` lies in the '
                  'interior of the closure of the image. All surrounding '
                  'topological infrastructure (open-subgroup-of-connected-'
                  'group, entrywise approximation, lift to '
                  '`DenseInSpecialUnitary`, d ∈ {0, 1} base cases) has been '
                  'factored out into axiom-free constructive theorems. '
                  'Substantive in-tree discharge requires the Aharonov-Arad '
                  'Bridge Lemma 4.1 + Lemma 6.1/6.2 ε-iteration proof '
                  '(~150 LoC on top of the shipped substrate). The hom '
                  'hypothesis closes the F3 finding that function-form '
                  'ρ : BraidGroup n → SU(d) (without hom structure) admits '
                  'a finite-image counterexample at d = 2.',
        'module': 'FKLW.AharonovAradBridgeIteration',
        'used_in': 'bridge_FKLW_unitary_hom → bridge_FKLW_unitary (d ≥ 2 '
                   'branch). Transitively consumed by '
                   '`BridgeProp.bridge_axiom_FKLW` and '
                   '`BridgeProp.density_from_spanning`.',
        'discharge_wave': 'Phase 6p Wave 2c.4a.iteration-substantive '
                          '(follow-up): full Bridge Lemma 4.1 + Lemma '
                          '6.1/6.2 ε-iteration on top of the shipped '
                          'topology + path-connectedness substrate.',
        'discharge_estimate_loc': {
            '2c.4a.iteration-substantive (Bridge Lemma 4.1 + Lemma '
            '6.1/6.2 substantive)': 150,
            'optional 2c.4b (qutrit d = 3 specialization)': 80,
            'deferred 2c.4d (Decoupling Lemma 4.2 for d ≥ 9; blocked on '
            'Mathlib4 SU(n) LieGroup substrate)': 280,
            'total (d ≤ 4 path; sufficient for project use cases)': 230,
        },
        'in_tree_mathlib_infra_already_built': {
            'IsCompact on Matrix.specialUnitaryGroup': 'SHIPPED in '
                'SpecialUnitaryTopology.lean (Wave 2c.4a-substrate).',
            'PathConnectedSpace on Matrix.specialUnitaryGroup': 'SHIPPED in '
                'SpecialUnitaryPathConnected.lean (Wave 2c.4a-substrate-'
                'PathConnected).',
            'ContinuousInv + IsTopologicalGroup on SU(d)': 'SHIPPED in '
                'AharonovAradBridgeIteration.lean (Wave 2c.4a-iteration).',
            'closure_eq_univ_of_one_mem_interior': 'SHIPPED in '
                'AharonovAradBridgeIteration.lean (Wave 2c.4a-iteration; '
                'axiom-free; open-subgroup-of-connected-group).',
            'entrywise_approx_of_mem_closure': 'SHIPPED in '
                'AharonovAradBridgeIteration.lean (Wave 2c.4a-iteration; '
                'axiom-free; Pi-topology entrywise approximation).',
            'denseInSpecialUnitary_of_lifted_closure_eq_univ': 'SHIPPED in '
                'AharonovAradBridgeIteration.lean (Wave 2c.4a-iteration; '
                'axiom-free; ~40 LoC bridge from SU(d)-subtype closure '
                'to entrywise DenseInSpecialUnitary).',
            'LieSpanProp → bridge_exists': 'SHIPPED in '
                'AharonovAradBridgeProof.lean (Wave 2c.4c).',
            'geometric_convergence_to_zero': 'SHIPPED in '
                'AharonovAradBridge.lean (Wave 2c.4).',
            'matrix_product_difference_split': 'SHIPPED in '
                'AharonovAradBridge.lean (Wave 2c.4).',
        },
        'in_tree_mathlib_infra_to_build_for_discharge': {
            'authorization': 'In-tree build authorized per Phase 6p axiom-'
                             'sign-off policy (amended 2026-05-12 PM: '
                             'substantive in-tree work + strict axiom '
                             'narrowing implicitly authorized).',
            'LieGroup on Matrix.specialUnitaryGroup': 'Build target: ~200 '
                'LoC project-local; needed only for 2c.4d Decoupling Lemma '
                'path (d ≥ 9). Project use-cases (qutrit d=3, quintet d=5) '
                'do NOT require this.',
        },
        'source': 'Aharonov & Arad 2011, *New J. Phys.* 13, 035019; '
                  'arXiv:quant-ph/0605181 §4 (density Theorem 3.2 — note '
                  'explicit hypothesis ρ : BraidGroup n →* SU(d) homomorphism) '
                  'and §6 (Lemma 4.1 Bridge + Lemma 4.2 Decoupling).',
        'soundness_status': 'SOUND under the explicit hom hypothesis '
                            '(matches Aharonov-Arad Theorem 3.2 statement; '
                            'closes the F3 finite-image-counterexample '
                            'finding).',
        'risk': 'Low for d ≤ 4 (no Decoupling Lemma; ~150 LoC substantive '
                'Bridge Lemma formalization on top of the shipped '
                'substrate). Medium for d ≥ 9 (Decoupling Lemma path).',
        'circularity_note': 'None. The narrow residual is a pure analytic-'
                            'topological statement: "1 ∈ interior(closure '
                            '(range ρ))" for a hom ρ ℂ-spanning the matrix '
                            'algebra. Independent of Solovay-Kitaev, AGP-'
                            'threshold, or gate-set content. Consumed only '
                            'by `bridge_FKLW_unitary_hom` (same module), '
                            'transitively by '
                            '`BridgeProp.bridge_axiom_FKLW` and '
                            '`BridgeProp.density_from_spanning`.',
    },
}

# ════════════════════════════════════════════════════════════════════
# PLACEHOLDER REGISTRY
#
# Tracks theorems declared as `True := trivial` — these encode NO
# mathematical content. They exist as documentation markers recording
# what SHOULD eventually be proved, but inflate theorem counts if
# counted alongside substantive theorems.
#
# Two categories:
#   'summary' — module summary theorems (one per module, harmless documentation)
#   'content' — claims mathematical content but proves nothing (count-inflating)
#
# Verified counts should exclude ALL placeholders.
# Run: grep -c "True := trivial" lean/SKEFTHawking/*.lean | awk -F: '{s+=$2}END{print s}'
# ════════════════════════════════════════════════════════════════════

PLACEHOLDER_THEOREMS: dict[str, dict[str, str]] = {
    # === Registry of every `True := trivial` placeholder theorem in the Lean
    #     substrate. Reconciled 2026-06-13 (Substrate Integrity Gates W1) to
    #     cover ALL 26 on-disk type-`True` declarations (docs/counts.json
    #     `theorems_placeholder` == 26), up from the 11 content entries tracked
    #     before. Each entry carries:
    #       category : 'content'      — a named mathematical claim standing in
    #                                   for unproven content (load-bearing if
    #                                   any proof/formula/paper references it —
    #                                   Pipeline Invariant #9 forbids that);
    #                  'docs_marker'  — a navigation/summary/caveat anchor,
    #                                   non-load-bearing (cosmetic).
    #       module    : Lean module (short, under SKEFTHawking[.Sub]).
    #       lean_name : the ACTUAL Lean declaration name. The dict KEY is a
    #                   stable tracking id (5 historical keys are descriptive
    #                   and differ from the decl — they are referenced by
    #                   bundle I1 metadata + the append-only supersession
    #                   ledger + the prose-reference index, so they are NOT
    #                   rekeyed); `placeholder_not_cited` (validate.py) and
    #                   build_graph.py match papers/graph against `lean_name`,
    #                   never the key. For the 15 W1-added entries key == lean_name.
    #       claim     : what the placeholder asserts.
    #       resolution: what a substantive proof would require.
    # ---------------------------------------------------------------------
    # CONTENT placeholders (20) — unproven mathematical claims
    # DrinfeldEquivalence: categorical wrapping stubs
    'monoidal_structure_corresponds': {
        'category': 'content',
        'module': 'DrinfeldEquivalence',
        'lean_name': 'equivalence_preserves_tensor',
        'claim': 'Monoidal structures of Z(Vec_G) and Rep(D(G)) correspond',
        'resolution': 'Requires full functor construction (Phase 6)',
    },
    'braided_structure_corresponds': {
        'category': 'content',
        'module': 'DrinfeldEquivalence',
        'lean_name': 'equivalence_preserves_braiding',
        'claim': 'Braided structures correspond',
        'resolution': 'Requires braided monoidal functor (Phase 6)',
    },
    'center_universal_property': {
        'category': 'content',
        'module': 'DrinfeldEquivalence',
        'lean_name': 'center_universal_property',
        'claim': 'Z(Vec_G) is the universal braided monoidal subcategory mapping faithfully to Vec_G (Müger)',
        'resolution': "Categorical statement; needs Müger's universal-property infrastructure (Phase 6)",
    },
    # GaugeEmergence: placeholder statements
    'gauge_emergence_half_braiding': {
        'category': 'content',
        'module': 'GaugeEmergence',
        'lean_name': 'half_braiding_gives_action_TODO',
        'claim': 'Half-braiding ↔ D(G)-module bijection (full categorical)',
        'resolution': 'Algebraic version proved in DrinfeldCenterBridge; categorical wrapping Phase 6',
    },
    'gauge_emergence_equivalence': {
        'category': 'content',
        'module': 'GaugeEmergence',
        'lean_name': 'gauge_emergence_statement_TODO',
        'claim': 'Z(Vec_G) ≅ Rep(D(G)) as braided monoidal categories (general G)',
        'resolution': 'Concrete verification for Z/2 and S₃ done; abstract general-G functor Phase 6',
        # Published-claim signature for `placeholder_not_cited`: papers cite this
        # result by its math notation `Z(Vec_G) ≅ Rep(D(G))`, not the Lean decl
        # name. Matches `\mathrm{Rep}(D(` / `Rep}(D(` / `Rep(D(`.
        'tex_signature': r'Rep\}?\(D\(',
    },
    'chirality_limitation_zero': {
        'category': 'content',
        'module': 'GaugeEmergence',
        'lean_name': 'chirality_independent_of_G_TODO',
        'claim': 'c = 0 for all Z(Vec_G)',
        'resolution': 'Follows from string-net construction; needs formal Turaev-Viro connection',
    },
    # SteenrodA1: Adem relations — PROVED via native_decide (April 2026)
    # adem_sq1_sq1, adem_sq1_sq2, adem_sq2_sq2 — RESOLVED, removed from registry
    'a1_is_sub_hopf_algebra': {
        'category': 'content',
        'module': 'SteenrodA1',
        'lean_name': 'a1_is_sub_hopf_algebra',
        'claim': 'A(1) is a sub-Hopf-algebra of the Steenrod algebra',
        'resolution': 'Requires Hopf structure on A(1)',
    },
    # RestrictedUq: dimension/module count statements
    'small_uq_dim_statement': {
        'category': 'content',
        'module': 'RestrictedUq',
        'lean_name': 'small_uq_dim_statement',
        'claim': 'dim u_q(sl₂) = ℓ³',
        'resolution': 'Requires explicit basis construction',
    },
    'small_uq_to_su2k_connection': {
        'category': 'content',
        'module': 'RestrictedUq',
        'lean_name': 'small_uq_to_su2k_connection',
        'claim': 'At ℓ = k+2 the semisimple quotient of Rep(u_q(sl₂)) carries the SU(2)_k fusion rules',
        'resolution': 'Statement-level bridge; needs the semisimple-quotient construction (Phase 6)',
    },
    # FusionCategory: Ocneanu rigidity + TQFT placeholder
    # (renamed _placeholder → _TODO 2026-04-26 per Stage-13 audit)
    'ocneanu_rigidity_TODO': {
        'category': 'content',
        'module': 'FusionCategory',
        'lean_name': 'ocneanu_rigidity_TODO',
        'claim': 'Fusion categories are rigid (Ocneanu)',
        'resolution': 'Deep result; axiomatize or defer to Phase 6+',
    },
    'fusion_to_tqft_TODO': {
        'category': 'content',
        'module': 'FusionCategory',
        'lean_name': 'fusion_to_tqft_TODO',
        'claim': 'Fusion category → TQFT via Turaev-Viro',
        'resolution': 'Statement-level; full construction requires cobordism infrastructure',
    },
    # CenterFunctor: monoidal/braided functor stubs
    # (renamed equivalence_is_* → _TODO 2026-04-26 per Stage-13 audit)
    'equivalence_is_monoidal_TODO': {
        'category': 'content',
        'module': 'CenterFunctor',
        'lean_name': 'equivalence_is_monoidal_TODO',
        'claim': 'Z(Vec_G) ≌ Mod(D(G)) is monoidal',
        'resolution': 'Phase 6 categorical wrapping (full functor construction)',
    },
    'equivalence_is_braided_TODO': {
        'category': 'content',
        'module': 'CenterFunctor',
        'lean_name': 'equivalence_is_braided_TODO',
        'claim': 'Z(Vec_G) ≌ Mod(D(G)) is braided monoidal',
        'resolution': 'Phase 6 categorical wrapping (full functor construction)',
    },
    # q-Onsager / coideal embedding
    'dolan_grady_from_chevalley': {
        'category': 'content',
        'module': 'CoidealEmbedding',
        'lean_name': 'dolan_grady_from_chevalley',
        'claim': 'The Dolan-Grady relation holds for the coideal generators B₀,B₁ (confirms the O_q embedding)',
        'resolution': 'Purely algebraic computation in the quotient ring via q-Serre + KE/KF relations (Phase 6 wrapping)',
    },
    'oq_coideal_property_B0_statement': {
        'category': 'content',
        'module': 'Uqsl2Affine',
        'lean_name': 'oq_coideal_property_B0_statement',
        'claim': 'Coideal property Δ(Bᵢ) = Bᵢ ⊗ Kᵢ⁻¹ + 1 ⊗ Bᵢ for the right coideal subalgebra',
        'resolution': 'Needs the Hopf structure on U_q(ŝl₂) (Δ preserving all 22 relations) — Phase 6',
    },
    # Onsager algebra representation theory
    'davies_roan_classification': {
        'category': 'content',
        'module': 'OnsagerAlgebra',
        'lean_name': 'davies_roan_classification',
        'claim': 'Davies-Roan: every non-trivial fin-dim irreducible O-module is a tensor product of sl₂ evaluation modules',
        'resolution': 'Requires representation-category infrastructure (Phase 6+)',
    },
    # SMG synthesis bridges (statement-level)
    'smg_three_conditions': {
        'category': 'content',
        'module': 'SMGClassification',
        'lean_name': 'smg_three_conditions',
        'claim': 'SMG arises iff TPF evasion (necessary) + Z₁₆ anomaly cancellation (necessary) + spectral gap (sufficient, conjectured)',
        'resolution': 'Synthesis bridge across GoltermanShamir / TPFEvasion / Z16Classification; gap leg is conjectural',
    },
    'tpf_z16_combined': {
        'category': 'content',
        'module': 'Z16Classification',
        'lean_name': 'tpf_z16_combined',
        'claim': 'TPF evasion is necessary but not sufficient for SMG (must also satisfy Z₁₆ anomaly cancellation)',
        'resolution': 'Synthesis connecting TPFEvasion.lean to the Z₁₆ classification',
    },
    # GaugingStep: 3+1D disentangler conditional on the gapped interface
    'disentangler_3d_requires_gap1': {
        'category': 'content',
        'module': 'GaugingStep',
        'lean_name': 'disentangler_3d_requires_gap1',
        'claim': '3+1D disentangler existence is conditional on the gapped interface (TPFConjecture, ex gapped_interface_axiom)',
        'resolution': 'Conditional on the TPFConjecture tracked Prop (SPTClassification.lean); see HYPOTHESIS_REGISTRY',
    },
    # ChangeOfRings: H2 "discharged" stub — trivial body discharges nothing
    # (audit 2026-06-13 finding #25; Substrate Integrity Gates W2 renames →_TODO)
    'h2_discharged_TODO': {
        'category': 'content',
        'module': 'ChangeOfRings',
        'lean_name': 'h2_discharged_TODO',
        'claim': 'H2 — the change-of-rings Hom-tensor adjunction Ext_A(A⊗_{A(1)}F₂,F₂) ≅ Ext_{A(1)}(F₂,F₂)',
        'resolution': 'Trivial `True` body discharges nothing; real content is the adjunction (Phase 5q.T A1ExtReal). Renamed →`_TODO` in W2 (2026-06-13).',
    },
    # ---------------------------------------------------------------------
    # DOCS-MARKER placeholders (6) — navigation/summary/caveat anchors, cosmetic
    'module_summary_marker': {
        'category': 'docs_marker',
        'module': 'BBN',
        'lean_name': 'module_summary_marker',
        'claim': 'BBN module summary navigation anchor',
        'resolution': 'Documentation marker — non-load-bearing',
    },
    'cosmological_perturbations_summary': {
        'category': 'docs_marker',
        'module': 'CosmologicalPerturbations',
        'lean_name': 'cosmological_perturbations_summary',
        'claim': 'Cosmological-perturbations module summary anchor',
        'resolution': 'Documentation marker — non-load-bearing',
    },
    'flrw_dynamics_summary': {
        'category': 'docs_marker',
        'module': 'FLRWDynamics',
        'lean_name': 'flrw_dynamics_summary',
        'claim': 'FLRW-dynamics module summary anchor',
        'resolution': 'Documentation marker — non-load-bearing',
    },
    'quantumNetwork_substrate_ready': {
        'category': 'docs_marker',
        'module': 'QuantumNetwork.Basic',
        'lean_name': 'quantumNetwork_substrate_ready',
        'claim': 'QuantumNetwork substrate-ready marker',
        'resolution': 'Documentation marker — non-load-bearing',
    },
    'phase6b_w3_structural_no_go_marker': {
        'category': 'docs_marker',
        'module': 'VestigialInflationNoGo',
        'lean_name': 'phase6b_w3_structural_no_go_marker',
        'claim': 'Phase 6b W3 structural no-go navigation marker',
        'resolution': 'Documentation marker — non-load-bearing',
    },
    'misumi_instability_caveat': {
        'category': 'docs_marker',
        'module': 'GaugingStep',
        'lean_name': 'misumi_instability_caveat',
        'claim': 'Caveat: Misumi (2025) symmetry-preserving deformations can destabilize the single-Weyl phase (not a no-go)',
        'resolution': 'Documentation caveat — non-load-bearing',
    },
}

# Count of content placeholders (inflates theorem count if not excluded)
PLACEHOLDER_CONTENT_COUNT = sum(
    1 for v in PLACEHOLDER_THEOREMS.values() if v['category'] == 'content'
)
# Total placeholders registered; must equal docs/counts.json `theorems_placeholder`
# (every on-disk `True := trivial` decl is registered — Pipeline Invariant #9).
PLACEHOLDER_TOTAL_COUNT = len(PLACEHOLDER_THEOREMS)
# Lookup by actual Lean decl name → registry entry (placeholder_not_cited,
# build_graph.py, and the proxy-body audit match on the real decl, not the key).
PLACEHOLDER_LEAN_NAMES = {
    v.get('lean_name', k): k for k, v in PLACEHOLDER_THEOREMS.items()
}

# ─────────────────────────────────────────────────────────────────────────
# Formula-grounding kind registry (R-05, 2026-07-20)
# ─────────────────────────────────────────────────────────────────────────
# Per `formulas.py` `Lean:` reference, the HONEST classification of what the
# cited theorem provides. The default (any ref NOT listed here) is 'derivation':
# an independent proof whose CONCLUSION substantively grounds the formula. A
# ref is listed here ONLY when its grounding is a 'definitional-record' — a
# theorem that is TRUE BY DEFINITION and therefore does not independently
# derive the formula:
#   * an identity wrapper `P → P` that returns its own hypothesis, or
#   * an `rfl`/definitional equality `f x = <body of f>` (unfolds a definition).
# The `formula_grounding` validate check enforces this both ways: a vacuous
# identity wrapper MUST be declared here (it proves nothing), and an entry
# declared 'derivation' whose Lean is actually an identity wrapper / rfl-
# definitional equality FAILS — so a definitional record cannot be silently
# re-labeled a derivation (the R-05 evidence-laundering class). Keys are the
# short Lean decl name (the `Lean:` token in formulas.py).
FORMULA_GROUNDING_KIND: dict[str, dict[str, str]] = {
    'wrt_S2xS1_eq_rank': {
        'kind': 'definitional-record',
        'note': "WRTInvariant.lean: `wrtS2xS1 D := D.n` and `wrt_S2xS1_eq_rank : "
                "wrtS2xS1 D = D.n := rfl`. A definitional equality (the WRT S²×S¹ "
                "invariant is DEFINED as the rank), NOT an independent derivation "
                "from the 0-framed-unknot surgery / Verlinde formula. R-05.",
    },
    'dd_simples_count': {
        'kind': 'definitional-record',
        'note': "DrinfeldDouble.lean: `dd_simples_count (…) (h : Σ irreps = Σ irreps) "
                ": Σ irreps = Σ irreps := h`. An identity wrapper (type `P → P`, "
                "returns its hypothesis), NOT a proof of the general Burnside/Drinfeld "
                "-double simple count. R-05.",
    },
}

# native_decide kernel-trust surface ceiling (Substrate Integrity Gates R4 / W5).
# The decl-closure count (declarations whose transitive axiom closure includes a
# native_decide compiler-trust axiom — ADR-002's authoritative metric, NOT the
# source call-site count) may only DECREASE without explicit review. A wave that
# ADDS native_decide trust surface must bump this ceiling in the same commit, with
# a rationale — making the increase visible (no silent growth). Elimination policy
# is owned by ADR-002; this is only the regression backstop. Tracked in
# docs/counts.json `lean.native_decide_decl_closure`; enforced by
# `validate.py --check native_decide_regression`.
NATIVE_DECIDE_DECL_CLOSURE_CEILING = 546  # 2026-06-13 (post-6AO; was 852→587 at ADR-002 cleanup)

# ════════════════════════════════════════════════════════════════════
# VACUOUS-STATEMENT BASELINE (identity-pinned ratchet; SIG gate hardening 2026-06-13)
#
# `validate.py --check vacuous_statement_audit` (type-thin: reflexive `Eq X X`) and
# `--check proxy_body_audit` (body-thin: rfl / identity-return / self-discharging
# existential) flag theorems whose STATEMENT or PROOF proves nothing. The SIG-gate
# blind-spot reconciliation (2026-06-13) — fixing the `_scan_lean_theorem_bodies`
# empty-body bug (#25), adding the anon-ctor `⟨Equiv.refl,…⟩` pattern (#23), and the
# name-agnostic type-thinness classifier (#45/#54) — UN-HID a pre-existing widespread
# class of ~48 content-thin theorems that the prior name-gated, norm_num-excluding,
# body-mis-parsing detectors silently skipped.
#
# These are GRANDFATHERED here as VISIBLE tracked debt (not hidden): a name in this
# set is reported as ADVISORY by both checks; a NEW content-thin theorem (not in the
# set) is a HARD-FAIL — closing the generator (ADR-004 pathway #2 structural
# prevention) for all future work. The set may only SHRINK: dispositioning an entry
# (strengthen / restate / delete / disclose in MODELING_ASSUMPTION_THEOREMS) removes
# it. This mirrors NATIVE_DECIDE_DECL_CLOSURE_CEILING. Sweep tracker:
# docs/roadmaps/SIGGateHardening_Roadmap.md (W5) → a dedicated "Vacuous Statement
# Sweep" /goal. Keyed by the short Lean decl name.
VACUOUS_STATEMENT_BASELINE = frozenset({
    # reflexive `Eq X X` markers (counts / dims / coefficients reduced to a literal)
    "G_c_nlo_invariance", "bag_weight_real", "chevalley_GG_verification",
    "chirality_is_independent_obstruction", "chirality_obstruction", "circuit_depth_two",
    "davies_AA_coeff", "davies_GA_coeff", "doublet_algebra_generators", "ext_degree_zero",
    "fib_wrt_S2xS1", "fierz_channel_count", "first_order_conformal_charged_count",
    "golterman_shamir_obstruction", "gsd_sphere_eq_one", "gt_lattice_dim_match",
    "hom_tensor_adjunction_dim", "ising_wrt_S2xS1", "model3450_equal_species",
    "onsager_two_u1_charges", "pillar1_nogo_requires_all", "q_V_on_site",
    "sixteen_fold_way_DEFINITIONAL", "su2_coefficient_match", "tetrad_modes_nf_independent",
    "three_gaps", "three_obstacles_exist", "vecZ2_F_trivial", "vec_G_simples_count",
    "wilson_offset", "wilson_spatial_dim", "wilson_weyl_node_count",
    # body-thin (rfl / identity-return / cases<;>rfl / self-discharging existential)
    "character_preserved", "dd_simples_count", "dispersion_matches_charge_scaling",
    "even_odd_cg_equivalence", "even_odd_force_equivalence", "first_order_non_conformal_count",
    "fusion_matches_k1", "fusion_matches_k2", "grading_preserved", "hopf_link_matches_S_matrix",
    "phase5x_viable_candidate_count", "sixteen_majoranas_gappable", "spt_classification_from_bordism",
    "stress_tensor_isotropic_holds", "wrt_S2xS1_eq_rank", "z16_classification",
})

# ════════════════════════════════════════════════════════════════════
# MODELING-ASSUMPTION THEOREMS (proxy-body-audit whitelist; R2 / W2)
#
# `validate.py --check proxy_body_audit` flags theorems whose NAME claims a
# structural / quantitative result (`*_dim`, `rank`, `*Ext*`, `*classification`,
# `sixteen_*`, `*_no_go`, `*_unanimous`, `*_equivalence`, `*_corresponds`) but
# whose PROOF is a trivial closer (`rfl` / `trivial` / `cases <;> rfl` /
# identity-return / `⟨_,_⟩`) — the "defining-the-conclusion" anti-pattern
# (Stage-3a checklist item 5), where the substantive load lives in a definition
# / struct field / registry rather than the proof term.
#
# A flagged decl is COMPLIANT (not a defect) iff it is registered here with a
# `lean_name`, a `reason` (why the trivial body is a legitimate modeling choice
# / extraction lemma), and a `discloses` pointer (the docstring / tracked Prop /
# registry entry where the real assumption is disclosed). Honest, documented
# modeling choices PASS; silent ones FAIL. (Native_decide / kernel-`decide`
# bodies are NOT in scope here — ADR-002's P4 gate owns the compiler-trust
# surface; the decide/norm_num arithmetic-proxy class is Phase-5q.T's T5 detector.)
# Populated by the W2 triage of the proxy_body_audit flagged set.
# ════════════════════════════════════════════════════════════════════

MODELING_ASSUMPTION_THEOREMS: dict[str, dict[str, str]] = {
    # category: 'definitional' = a correct, disclosed definitional record (the
    #   value is a falsifiable property of a concretely-defined object / named
    #   constant; the trivial proof is legitimate). 'vacuous_proxy' = the
    #   statement is content-free relative to the theorem NAME (an `N = N` /
    #   `x = x` decorative restatement of a docstring claim); retained as
    #   DISCLOSED tracked debt with a `discharge` pointer, NOT a derivation.
    # Every entry needs `lean_name`, `module`, `category`, `reason`, `discloses`.
    # Populated by the 2026-06-13 W2 triage of the proxy_body_audit flagged set.

    # ---- definitional records (legitimate trivial-by-design) ----
    'cyl_brown_eq': {
        'lean_name': 'cyl_brown_eq', 'module': 'PinPlusCharPairData',
        'category': 'definitional',
        'reason': 'The cylBor end-convention DISCRIMINATOR self-test (W-A definition gate round 2): '
                  'deliberately reflexive — it witnesses that the kernel-forced τ-end-negated Taylor '
                  'reading (iii) does NOT force 2q = 0 on the diagonal cylinder kernel (readings (i)/(ii) '
                  'are kernel-refuted, no-go taylor-leg-end-convention-trap). The trivial shape IS the test.',
        'discloses': 'no-go `taylor-leg-end-convention-trap` (KERNEL_NOGO_REGISTRY) + the module §self-test '
                     'docstring; substantive content in `brown_eq_of_taylorLeg_lagrangian` (the anti-collapse '
                     'engine) and `not_cylinder_plain_pairing_of_odd_value` (the refutation of reading (i)).',
    },
    'sVec_fermion_dim_DEFINITIONAL': {
        'lean_name': 'sVec_fermion_dim_DEFINITIONAL', 'module': 'Z16Classification',
        'category': 'definitional',
        'reason': 'Records d(f)=1 (unit-dimension of any fusion-category object); self-disclosed via the `_DEFINITIONAL` name suffix.',
        'discloses': 'name suffix `_DEFINITIONAL` + docstring ("carries no genuine super-modular content"); substantive content in `sVec_global_dim`.',
    },
    'g2k1_dims_eq_fib': {
        'lean_name': 'g2k1_dims_eq_fib', 'module': 'FPDimension',
        'category': 'definitional',
        'reason': 'g2k1Dims is *defined* as fibDims (FPDimension.lean:266), so the G₂-level-1 = Fibonacci FP-dim coincidence is encoded in the definition; rfl records it.',
        'discloses': 'docstring "(definitional)"; `def g2k1Dims := fibDims`.',
    },
    'sl2_dim_eq': {
        'lean_name': 'sl2_dim_eq', 'module': 'OnsagerAlgebra',
        'category': 'definitional',
        'reason': 'Records dim sl₂ = 3 via the named constant `sl2_dim : ℕ := 3`; a definitional record of a textbook value.',
        'discloses': '`def sl2_dim : ℕ := 3` (OnsagerAlgebra.lean:172).',
    },
    'sphereProd_s2s2_rank': {
        'lean_name': 'sphereProd_s2s2_rank', 'module': 'PinPlusKTSpinSigmaStock',
        'category': 'definitional',
        'reason': 'Records the `s2s2_rank` wiring obligation at the distinguished witness: the COMPUTED '
                  'rank-2 basis datum `sphereProdIntH2Basis` has rank field = 2 by construction (rfl). '
                  'The rank literal is a read-off of a datum whose non-vacuity is established elsewhere.',
        'discloses': 'substantive content in `sphereProdHTwoEquivInt : H₂(S²×S²;ℤ) ≃ₗ[ℤ] ℤ × ℤ` '
                     '(SphereProdHTwoInt.lean — the genuine rank-2 homology computation) and the '
                     'SphereWitnessTowerInt computed-basis tower tying `sphereProdIntH2Basis` to it.',
    },
    'emanant_su2_dim': {
        'lean_name': 'emanant_su2_dim', 'module': 'GTWeylDoublet',
        'category': 'definitional',
        'reason': 'Same content as `sl2_dim_eq` (sl2_dim = 3) re-stated in the emanant-symmetry context; the IR contraction → SU(2) is described in the docstring, the dim is a definitional record.',
        'discloses': '`def sl2_dim : ℕ := 3`; docstring (Seiberg emanant SU(2)). NOTE: duplicates OnsagerAlgebra.sl2_dim_eq.',
    },
    'hw_matches_sm_count': {
        'lean_name': 'hw_matches_sm_count', 'module': 'GaugingStep',
        'category': 'definitional',
        'reason': 'Records that the concrete `hw_smg : SMGPhaseData` carries n_weyl = 16 (a struct-field value matching the SM per-generation Weyl count); falsifiable against the construction.',
        'discloses': '`def hw_smg : SMGPhaseData where n_weyl := 16`; independent SM count = ∑ components = 16 (SMFermomData.total_components_with_nu_R).',
    },
    'free_energy_well_defined': {
        'lean_name': 'free_energy_well_defined', 'module': 'SU2PseudoReality',
        'category': 'definitional',
        'reason': 'Unfolds freeEnergyDensity ln_Z V = -ln_Z/V (the closed form); the `_well_defined` name refers to the closed form, not finiteness. NOTE: the `0 < V` hypothesis is unused (`_hV`).',
        'discloses': '`def freeEnergyDensity`; docstring. Candidate for a future tightening (drop unused hyp or rename).',
    },
    # Proactive disclosure of audit-2026-06-13 #9 (NOT auto-flagged — the names
    # don't match the structural-quantity patterns; recorded here as the W2
    # triage decision for the known entropic-gravity "8/8 NO-GO" case).
    'r_d_anchoring_partial_rescue_does_not_save_class_b_or_class_d': {
        'lean_name': 'r_d_anchoring_partial_rescue_does_not_save_class_b_or_class_d',
        'module': 'EntropicGravityDarkEnergy', 'category': 'definitional',
        'reason': 'Aggregate `∀ c, rDIndependentNoGo c = true := by cases c <;> rfl` over a Bool registry — bookkeeping. The SUBSTANCE is the 8 per-candidate NO-GO theorems: EGDE1/EGDE4 are genuine norm_num falsifiers vs data thresholds (σ ≥ 5σ; DESI w₀ gap ≥ 0.5), EGDE2/EGDE3 are disclosed Bool-flag modeling judgments.',
        'discloses': 'per-candidate theorems verlinde_2017_no_go_* / cadoni_tuveri_* (substantive) + the "encoded as a Boolean flag" docstrings; audit report meta-obs.',
    },
    'r_d_independent_count_eight': {
        'lean_name': 'r_d_independent_count_eight',
        'module': 'EntropicGravityDarkEnergy', 'category': 'definitional',
        'reason': 'Counts the filtered candidate List length = 8 (rDIndependentCount); a definitional count of a concrete List, not a derivation.',
        'discloses': '`def rDIndependentCount` (the .filter over the 8-candidate list); docstring.',
    },
    'entropic_gravity_no_go_count_eight': {
        'lean_name': 'entropic_gravity_no_go_count_eight',
        'module': 'EntropicGravityDarkEnergy', 'category': 'definitional',
        'reason': 'List-length rfl over the 8-candidate NO-GO list = 8. A bookkeeping tally; the proof load is the per-candidate quantitative NO-GO theorems (the substantive content). Disclosed 2026-06-13 (SIG reconcile #9) so disclosure_consistency covers the D5 prose, which previously prose-claimed it "establishes the 8/8 closure".',
        'discloses': 'docstring + D5 prose reframed to "records the 8/8 tally ... classification ledger rather than the proof load"; the per-candidate legs carry the closure.',
    },
    # Padmanabhan/CosMIn: the ONE Track-B candidate whose NO-GO is genuinely
    # STRUCTURAL (no verified σ) rather than a numerical exclusion — registered
    # here 2026-07-20 (review R-04) as a disclosed literature-ledger record.
    # (The other seven candidates now each carry a genuine falsifier theorem,
    # bundled in `entropic_gravity_seven_genuine_per_candidate_falsifiers`,
    # including the new Hossenfelder-Verlinde residual ω_cdm CMB exclusion.)
    'padmanabhan_cosmin_no_go_no_scalar_perturbation_theory': {
        'lean_name': 'padmanabhan_cosmin_no_go_no_scalar_perturbation_theory',
        'module': 'EntropicGravityDarkEnergy', 'category': 'definitional',
        'reason': 'rfl over the Boolean flag `hasScalarPerturbationTheory .padmanabhanCosMIn = false`. '
                  'The NO-GO is genuinely STRUCTURAL and carries NO verified σ value: the CosMIn axiom set '
                  '(H. Padmanabhan & T. Padmanabhan 1302.3226) is evaluated only at the FLRW background '
                  'level with no Lagrangian scalar degree of freedom, so no scalar perturbation theory is '
                  'derivable and (w₀, w_a) cannot be matched against DESI DR2\'s perturbation-derived '
                  'contour. This is a literature-ledger fact about the theory\'s field content, not a '
                  'numerical comparison — a numerical (w₀, w_a) exclusion is deliberately NOT asserted here '
                  '(unlike the other seven candidates), because CosMIn cannot even enter that comparison. '
                  'The Bool flag is the honest encoding of that structural absence.',
        'discloses': 'EGDE2 docstring ("Encoded as a Boolean flag on the candidate"; "no perturbation '
                     'theory"; "cannot be matched against DESI DR2\'s perturbation-derived contour"); '
                     'D5 prose §Phase-6m Track-B ("the closure is structural — there is no Lagrangian '
                     'scalar to drive sub-Hubble dynamics"); dossier B.2 (Phase-6m Round 5).',
    },
    # surfaced by the W7 M3 name-pattern broadening (correspondence/preserved/holds):
    'signature_preserved': {
        'lean_name': 'signature_preserved', 'module': 'CenterEquivalenceZ2',
        'category': 'definitional',
        'reason': 'Genuine finite data-preservation fact: the toric-code braiding signature R(e,m) = −1 is preserved under the Z/2 center equivalence (`braidingPhase = dz2BraidingPhase ∘ toricToDZ2`), true by rfl over the concrete 4-anyon data. A real sibling of fusion_preserved/braiding_preserved (which use `simp`); part of the substantive `full_correspondence`.',
        'discloses': '`CenterEquivalenceZ2.full_correspondence` bundles it with fusion/braiding/grading preservation; docstring.',
    },
    'phase6y_cascade_closure_status_holds': {
        'lean_name': 'phase6y_cascade_closure_status_holds', 'module': 'FKLW.Phase6yClosureStatusIndex',
        'category': 'definitional',
        'reason': 'Status-index marker: `phase6y_cascade_closure_status` is a `def` that unfolds to `True` (a human-readable closure-status checklist in its body comments), so the theorem is a documentation marker, not a mathematical claim.',
        'discloses': '`def phase6y_cascade_closure_status := True` with the per-item closure checklist in comments; the genuine FKLW results are the cited per-session theorems.',
    },

    # ---- vacuous_proxy (DISCLOSED tracked debt: statement is content-free vs name) ----
    'change_of_rings_ext_dim': {
        'lean_name': 'change_of_rings_ext_dim', 'module': 'ChangeOfRings',
        'category': 'vacuous_proxy',
        'reason': 'Statement is `ext_dim = ext_dim` with hypothesis `ext_dim = ext_dim` — VACUOUS; the docstring claims Ext-dimension preservation but the proof term proves x=x (audit 2026-06-13 #25).',
        'discharge': 'Phase 5q.T (A1ExtReal — the real Mathlib `Ext` functor via ProjectiveResolution.isoExt) replaces the `cols/8` proxy.',
        'discloses': 'this registry entry + the audit report; paired with the `h2_discharged`→`*_TODO` placeholder.',
    },
    'rank2_classification_count': {
        'lean_name': 'rank2_classification_count', 'module': 'FusionExamples',
        'category': 'vacuous_proxy',
        'reason': 'Statement is `(3:ℕ) = 3` — the rank-2 fusion-category count (Ostrik 2003: Vec_ℤ/2, Fibonacci, Yang-Lee) is in the docstring, not derived from an enumeration.',
        'discharge': 'Strengthen to `Fintype.card`/`List.length` of a concrete rank-2 enumeration (needs the enumeration built).',
        'discloses': 'this registry entry; docstring cites Ostrik 2003.',
    },
    'dg_generator_count': {
        'lean_name': 'dg_generator_count', 'module': 'OnsagerAlgebra',
        'category': 'vacuous_proxy',
        'reason': 'Statement is `(2:ℕ) = 2` — the "2 Dolan-Grady generators" claim is in the docstring, not derived from a generator structure.',
        'discharge': 'Strengthen to count a concrete generator List/Fintype (needs it built).',
        'discloses': 'this registry entry; docstring.',
    },
    'dg_relation_count': {
        'lean_name': 'dg_relation_count', 'module': 'OnsagerAlgebra',
        'category': 'vacuous_proxy',
        'reason': 'Statement is `(2:ℕ) = 2` — the "2 Dolan-Grady relations" claim is in the docstring, not derived from a relation structure.',
        'discharge': 'Strengthen to count a concrete relation List/Fintype (needs it built).',
        'discloses': 'this registry entry; docstring.',
    },
    'ising_wrt_rank': {
        'lean_name': 'ising_wrt_rank', 'module': 'WRTComputation',
        'category': 'vacuous_proxy',
        'reason': 'Statement is `(3:ℕ) = 3` — Ising rank (3 simples) is decorative; the real WRT content is `ising_globalDimSq` / `ising_gauss_sum_is_2zeta`.',
        'discharge': 'Strengthen via `wrtS2xS1 isingMTC = 3` once a concrete `isingMTC : MTCWithTwist` instance is built (WRTInvariant.wrtS2xS1 D := D.n exists).',
        'discloses': 'this registry entry; docstring.',
    },
    'fib_wrt_rank': {
        'lean_name': 'fib_wrt_rank', 'module': 'WRTComputation',
        'category': 'vacuous_proxy',
        'reason': 'Statement is `(2:ℕ) = 2` — Fibonacci rank (2 simples) is decorative; the real WRT content is `fib_globalDimSq`.',
        'discharge': 'Strengthen via `wrtS2xS1 fibMTC = 2` once a concrete `fibMTC : MTCWithTwist` instance is built.',
        'discloses': 'this registry entry; docstring.',
    },
}

# ════════════════════════════════════════════════════════════════════
# HYPOTHESIS REGISTRY
#
# Tracks unproved inputs that enter as hypotheses (function parameters)
# rather than axioms. These are mathematically well-established results
# that we cannot prove in Lean from our current infrastructure.
#
# Unlike axioms, hypotheses do NOT contaminate downstream theorems —
# they appear explicitly in the theorem statement as conditions.
# But we need to track them to understand our proof's total assumptions.
#
# Fields:
#   statement: Mathematical content of the hypothesis
#   status: 'active' (used in current theorems) | 'eliminable' | 'eliminated'
#   eliminability: 'algebraic' | 'hard' | 'very_hard' | 'open'
#   elimination_path: What would be needed to prove it
#   dependent_theorems: List of theorems that take this as a hypothesis
#                       ⚠ HAND-WRITTEN AND LOAD-BEARING — read the warning below before editing.
#   source: Published proof / reference
#   risk: Assessment of the hypothesis's reliability
#   circularity_note: Any known circularity concerns
# ════════════════════════════════════════════════════════════════════
#
# ⚠⚠ `dependent_theorems` IS THE ATLAS FRONTIER RANKING. IT IS ASSERTED, NOT DERIVED.
# ════════════════════════════════════════════════════════════════════
# Finding of the 2026-07-21 atlas-integrity repair (wt3). `SK_EFT_Hawking/CLAUDE.md` describes the
# atlas as "derived from `lean_deps.json` — **cannot drift**". That holds for DECLARATION nodes:
# `scripts/atlas_view.py:156` computes their `frontier_impact` from reverse `name_deps_project`
# edges — genuinely derived. It does NOT hold for the nodes the POSITIVE FRONTIER ranks. For every
# open assumption node `hyp:*`, `atlas_view.py:163-182` does:
#
#     deps = list(h.get("dependent_theorems", []) or [])
#     ... "frontier_impact": len(deps)
#     for d in deps: edges.append({"source": node_id, "type": "ASSUMED_BY", "target": d})
#
# i.e. the impact score AND the `ASSUMED_BY` edges come straight off the list typed in below.
# Nothing verifies that a listed name exists in Lean, that it takes the hypothesis as a binder, or
# that it mentions the carrier at all. So the ranking that steers fan-out is only as good as this
# hand-maintenance — and it drifts silently, in the same docstring-vs-statement way this project
# keeps finding one level down, but here in the infrastructure that decides WHERE EFFORT GOES.
#
# Measured 2026-07-21 by `scripts/audit_hypothesis_dependents.py` (read-only; run it after editing
# any list here): of 34 advertised open-frontier impact points, 6 (18%) named declarations that do
# not exist in `lean_deps.json` at all. Two nodes were ranked entirely on absent names —
# `H_RT_Formula_Valid` (ranked #3 with impact 4; real impact 0) and
# `H_ScalarChannelIsTetradBifurcationOutput` (impact 2; real 0). A third, `smith_inflow_z16`, was
# ranked #1 with impact 12 while only six in-tree declarations actually took its binder; it has
# since been retired (see its entry).
#
# WHEN EDITING A LIST HERE:
#   1. Verify each name exists AND consumes the hypothesis — do not add aspirational entries, and do
#      not list producers/witnesses of the hypothesis (they consume nothing).
#   2. Run `python scripts/audit_hypothesis_dependents.py` and check your node reports rot 0.
#   3. Remember you are changing the frontier RANKING, which is operator-visible. Say so explicitly
#      in your report; never silently re-rank.
# The structural fix (deriving `hyp:` impact from Lean binder occurrences rather than a hand list)
# is NOT done — it changes how the frontier ranks and is an operator decision. Scoped, not taken.
# ════════════════════════════════════════════════════════════════════

# Downgrade escape hatch for `tracked_hypothesis_ledger` (R3): a consumed
# tracked Prop that is genuinely NOT load-bearing (e.g. discharged within its
# own module, or a purely-local intermediate) is listed here with a reason
# instead of getting a full HYPOTHESIS_REGISTRY entry. Currently empty — every
# consumed tracked Prop is a real registry entry. (ADR-004 W7 finding L1: the
# check referenced this dict via getattr-default; now it exists explicitly.)
TRACKED_HYPOTHESIS_NON_LOAD_BEARING: dict[str, str] = {
}

HYPOTHESIS_REGISTRY: dict[str, dict] = {
    'he3a_moving_eta_nonzero': {
        'tier': 'discharge_future',
        'statement': 'The APS η-invariant (regularized spectral asymmetry of the non-zero spectrum) of '
            'the ³He-A MOVING (boosted / time-dependent 3D) domain-wall Dirac operator on the horizon '
            '3-manifold Σ = S²×ℝ is non-zero. DISTINCT from the zero-mode / boundary-correction term '
            'h(Σ)=1, which IS proven kernel-pure (APSEta/He3A.lean: a genuine Jackiw–Rebbi normalizable '
            'zero mode → boundaryKernelDim_He3AMovingDomainWall_eq_one → apsIndex_..._ne_zero, '
            'apsIndex = −1/2 ≠ 0).',
        'status': 'proposed — NOT consumed by any Lean theorem; the in-tree '
            '`etaInvariant .He3AMovingDomainWall = 0` is kept HONEST (the static 1D reduction has a '
            'λ↦−λ symmetric non-zero spectrum, so η = 0 genuinely). This entry tracks ONLY the residual '
            'η-spectral-asymmetry-SYMBOL claim for the full moving operator; the genuine non-zero APS '
            'boundary CONTENT ³He-A carries (apsIndex ≠ 0) is a separate proven theorem.',
        'eliminability': 'very_hard',
        'elimination_path': 'Requires substrate absent from Mathlib v4.29.1 and in-tree: (1) the moving '
            '3D domain-wall Dirac operator as an unbounded self-adjoint operator on an L² section space; '
            '(2) its discrete spectrum with multiplicities (compact-resolvent spectral theory); (3) the '
            'APS η-function η(s)=Σ_{λ≠0} sgn(λ)|λ|^{−s} + analytic continuation to s=0; (4) the APS index '
            'theorem for manifolds with boundary (Mathlib lacks even the closed-manifold Atiyah–Singer '
            'theorem). A future Phase 6X wave or a Mathlib Dirac/APS contribution.',
        'dependent_theorems': [],
        'module': 'APSEta/He3A.lean (§7 documents this gap precisely; §1–§6 ship the PROVEN '
            'Jackiw–Rebbi zero-mode / boundary-correction content)',
        'source': 'Volovik, The Universe in a Helium Droplet (2003); Phys. Rep. 351 (2001) 195 '
            '(chirality vector, moving domain wall); Atiyah–Patodi–Singer I–III (1975–76).',
        'risk': 'Low physically (Volovik chirality asymmetry is well-established) — but UNPROVEN '
            'in-tree; carried honestly as a landmark, NOT asserted as a theorem.',
        'prose': 'The ³He-A moving-domain-wall analog horizon is expected to carry a non-zero APS η '
            'spectral-asymmetry invariant (Volovik chirality-vector framework). The project PROVES the '
            'non-zero APS boundary correction (apsIndex = −1/2, from a genuine Jackiw–Rebbi zero mode); '
            'the η-invariant symbol for the full moving 3D operator awaits Dirac-operator / APS-index '
            'infrastructure absent from Mathlib.',
    },
    'carrollian_boundary_bms_vertex': {
        'tier': 'discharge_future',
        'statement': 'The acoustic analog-Hawking null boundary (sonic horizon) carries a Carrollian '
            'structure (degenerate boundary metric + null direction) whose BMS-type asymptotic-symmetry '
            'supertranslation charges satisfy the charge-conservation Ward identity equivalent to the '
            'acoustic soft theorem — the THIRD Strominger-triangle vertex. The other triangle content is '
            'PROVEN kernel-pure: the soft theorem (Boostless.lean) and the memory↔soft edge '
            '(SoftTheorems/Carrollian.lean `memory_eq_softCharge`, FTC-proved, with `burst_satisfies_ward`).',
        'status': 'proposed — BUILDABLE follow-up (operator-authorized 2026-07-20, corrected-posture: on '
            'the build queue, not a permanent assumption). The former `True`-placeholder predicates '
            '(`IsCarrollianBoundary`, `IsAsymptoticSymmetryWard`) were REMOVED in the R-01 remediation '
            '(2026-07-20); nothing in-tree asserts this vertex. This entry tracks the genuine build.',
        'eliminability': 'moderate',
        'elimination_path': 'The Phase 6o-prime Wave 1a-prime arc (docs/roadmaps/Phase6o_prime_Roadmap.md): '
            'C0 literature-anchoring scout (horizon/membrane-paradigm BMS charge algebra for the analog '
            'case) -> C1 CarrollianStructure (degenerate metric + null field) + acoustic-horizon instance '
            '-> C2 Witt/Virasoro in-tree (Mathlib has LieAlgebra.Extension for the central extension; no '
            'named Virasoro) -> C3 BMS semidirect product + supertranslation subalgebra -> C4 boundary '
            'phase-space model + charge functionals (the vacuity-risk item; Fable-gate before consumption) '
            '-> C5 the charge Ward identity wiring the triangle third vertex -> C6 vacuity gate round. '
            'SCOPE FENCE: analog-appropriate fidelity ONLY (acoustic horizon, BMS-3 / Carrollian-line, '
            'algebraic phase-space model) — NOT asymptotically-flat BMS-4 with asymptotic expansions. '
            'Reference class: the cylinder cap-cross arc (~10 worker tasks).',
        'dependent_theorems': [],
        'module': 'SoftTheorems/Carrollian.lean (the "Documented GAP" section states the three required '
            'structures precisely; the proven memory/soft content lives in the same module)',
        'source': 'Penna arXiv:1508.06577 (membrane-paradigm horizon charges — THE transcription target '
            'per the C0 verdict: Q_f = ∫ f·κ/8π, conservation via Damour-Navier-Stokes); Agrawal-Nguyen '
            'arXiv:2504.10577 (the supertranslation Ward identity <-> soft-mode insertion; attribution '
            'corrected 2026-07-20 — formerly miscited as Have-Nguyen-Prohazka-Salzer, = arXiv:2402.05190); '
            'Donnay-Giribet-Gonzalez-Pino arXiv:1511.08687 (horizon Vect(S¹)⋉C∞(S¹)_ab algebra); '
            'Donnay-Marteau arXiv:1903.09654 (horizon = Carrollian geometry); Barnich-Compere '
            'gr-qc/0610130 (BMS₃; central extension lives in the CHARGE algebra only); '
            'Strominger-Zhiboedov arXiv:1411.5745 (the memory corner); Mason-Ruzziconi-Yelleshpur Srikant '
            'arXiv:2312.10138 (Carrollian amplitudes); Datta-Fischer arXiv:2011.05837 (BEC acoustic '
            'memory); C0 verdict: Lit-Search/Phase-6o-prime/C0_horizon_BMS_charge_algebra_verdict_20260720.md; '
            'On-Shell Methods DR §4.3, §8.2.',
        'risk': 'Low physically (the Carrollian/BMS soft-theorem correspondence is established for '
            'gravitational systems; the analog transcription is standard-shaped). Formalization-novel: '
            'no paper proves a BMS theorem for an acoustic analog (On-Shell DR §4.3), so the bounded '
            'build is itself a novel result. Main technical risk concentrates in C4 (the phase-space / '
            'charge model must act non-trivially — vacuity-gated).',
        'prose': 'The Strominger triangle for analog Hawking systems has two of its three corners proven '
            'in-tree (soft theorem; memory↔soft-charge Ward relation). The third — Carrollian null-boundary '
            'geometry carrying BMS supertranslation charges whose conservation IS the soft theorem — '
            'requires a bounded Carrollian/BMS formalization arc (Phase 6o-prime Wave 1a-prime), fenced to '
            'analog fidelity. Tracked here until the arc discharges it.',
    },
    'niemeier_classification_exactly_24': {
        'tier': 'discharge_future',
        'statement': 'There are EXACTLY 24 even unimodular positive-definite lattices of rank 24 '
            '(the Niemeier lattices; Niemeier 1973). The Schellekens chain (Schellekens/*.lean, '
            'rebuilt genuine 2026-07-20) carries the falsifiable ARITHMETIC content this classification '
            'entails (24 = 8*3 = lcm(8,3) etc.); only the classification EXHAUSTIVENESS is this '
            'external hypothesis.',
        'status': 'proposed — an external-literature classification fact, disclosed in the module '
            'docstrings; the chain headline `schellekensChain_implies_24_divides_c_minus_iff_3_divides_'
            'N_gen` concludes its real arithmetic biconditional (via the kernel-checked '
            'GenerationConstraint) conditional at most on the named classification hypotheses.',
        'eliminability': 'very_hard',
        'elimination_path': 'Requires formalized lattice-classification machinery (even unimodular '
            'lattices, root systems, mass formulas / neighbor method) absent from Mathlib. A future '
            'Mathlib lattice-theory program; not project-critical (the arithmetic endpoint is proven '
            'independently).',
        'dependent_theorems': [],
        'module': 'Schellekens/NiemeierLattice.lean (docstring disclosure)',
        'source': 'Niemeier, J. Number Theory 5 (1973) 142; Conway-Sloane SPLAG Ch. 16.',
        'risk': 'Effectively zero physically/mathematically (a settled 1973 classification); carried '
            'as an honest external-completeness landmark.',
        'prose': 'The 24 Niemeier lattices underpin the c=24 story; the chain encodes their arithmetic '
            'consequences and defers the exhaustiveness to this tracked external fact.',
    },
    'schellekens_c24_voa_classification_exactly_71': {
        'tier': 'discharge_future',
        'statement': 'There are EXACTLY 71 holomorphic vertex operator algebras of central charge 24 '
            '(Schellekens 1993 list; completeness proven by Moeller-Scheithauer 2024 and companions), '
            'each unique up to isomorphism. The chain carries the falsifiable count relations '
            '(24 <= 71; 71 = 70 + 1 with the Moonshine module); the classification EXHAUSTIVENESS/'
            'uniqueness is this external hypothesis.',
        'status': 'proposed — external-literature classification fact, disclosed in the module '
            'docstrings (see niemeier_classification_exactly_24 for the chain structure).',
        'eliminability': 'very_hard',
        'elimination_path': 'Requires formalized VOA theory (vertex algebras, characters, modular '
            'invariance, orbifold constructions) absent from Mathlib — a research-frontier '
            'formalization program.',
        'dependent_theorems': [],
        'module': 'Schellekens/HolomorphicVOAc24.lean (docstring disclosure)',
        'source': 'Schellekens, Comm. Math. Phys. 153 (1993) 159; Moeller-Scheithauer arXiv:2112.12291 '
            '(Ann. Math. 2024) + companions.',
        'risk': 'Very low (peer-reviewed completeness proof, Annals 2024); carried as an honest '
            'external-completeness landmark.',
        'prose': 'The 71 holomorphic c=24 VOAs anchor the Schellekens chain; the exhaustiveness is '
            'tracked here, the arithmetic consequences are proven in-tree.',
    },
    'acoustic_petrov_d_np_classification': {
        'tier': 'discharge_future',
        'statement': 'The draining-bathtub / acoustic Kerr-Schild metric is Petrov type D in the full '
            'Newman-Penrose sense: the Weyl curvature spinor satisfies the type-D vacuum reformulation '
            'Psi_ABCD = Phi_(AB Phi_CD)/S for the KS congruence. DISTINCT from the PROVEN in-tree content '
            '(2026-07-20 R-02 rebuild): the genuine Kerr-Schild decomposition with a falsifiable null '
            'condition + the exact Sherman-Morrison inverse (`kerrSchild_exact_inverse`), the Maxwell '
            'single copy A = phi*k, the derived 3-obstruction BCJ no-go, and `IsPetrovD` in the KS '
            'repeated-principal-null sense (KS form + nonzero null congruence).',
        'status': 'proposed — NOT consumed by any Lean theorem (the R-02 rebuild dropped the redundant '
            'conjunction; WeylSpinor.lean records only the KS precondition). Tracks the residual '
            'full-NP-classification claim carried by README/RESEARCH_STATUS_OVERVIEW prose (both updated '
            '2026-07-20 to cite this entry).',
        'eliminability': 'very_hard',
        'elimination_path': 'Requires a Newman-Penrose / 2-spinor formalism absent from Mathlib AND '
            'PhysLib (VERIFIED 2026-07-20: pinned Mathlib v4.29.1 has CliffordAlgebra + spinGroup/'
            'pinGroup — the abstract Clifford/Spin layer only; recent Mathlib master adds Riemannian '
            'METRICS/bundles (IsRiemannianManifold) but NO curvature tensors of any kind, no Lorentzian '
            'signature machinery, no tetrads, no SL(2,C) 2-spinor calculus, no Petrov classification; '
            'the PhysLib Lake dep is QuantumInfo-only — zero GR content, direct package read). Missing '
            'layer: spinor dyads, the Weyl curvature spinor, principal null directions, the Petrov '
            'classification theorem (CK-Duality DR §8.2 flags the same absence for spinor-helicity). '
            'A future Phase 6X wave or Mathlib spinor-geometry contribution; Phase 6o-prime Wave 1b-prime '
            'tracks it (docs/roadmaps/Phase6o_prime_Roadmap.md).',
        'dependent_theorems': [],
        'module': 'DoubleCopy/WeylSpinor.lean (documents the gap; the genuine KS content lives in '
            'DoubleCopy/PetrovD.lean + SingleCopy.lean + BCJNoGo.lean and KerrSchild.lean)',
        'source': 'Stephani et al., Exact Solutions of Einstein Field Equations (Petrov classification); '
            'Monteiro-O\'Connell-White JHEP 12 (2014) 056 (Kerr-Schild double copy); Color-Kinematics '
            'Duality DR §8.2.',
        'risk': 'Low physically (the draining-bathtub metric being type D is standard in the analog-gravity '
            'literature); carried honestly as a landmark. The load-bearing double-copy content (KS + single '
            'copy + BCJ no-go) is PROVEN and does not depend on this entry.',
        'prose': 'The acoustic Kerr-Schild metric is type D in the KS repeated-principal-null sense '
            '(proven); the full Newman-Penrose Petrov classification and the type-D vacuum reformulation '
            'await a spinor formalism absent from Mathlib.',
    },
    'acyclic_factor_graph_has_rank_cert': {
        'tier': 'discharge_future',
        'statement': 'Every acyclic (tree) factor graph admits a BP rank certificate '
            '(BeliefPropagation.BPRankCert G): a topological subtree-depth order on directed message '
            'endpoints with the two strict-monotonicity properties. Equivalently '
            '`IsAcyclicFactorGraph G → Nonempty (BPRankCert G)`.',
        'status': 'proposed — BUILDABLE follow-up (corrected-posture: on the build queue, not a permanent '
            'assumption). The genuine convergence theorem `bp_converges_on_ranked_acyclic` is PROVEN '
            'taking a concrete BPRankCert as an explicit binder, and fires non-vacuously on a real 3-node '
            'tree (`bp_converges_on_star`). This entry tracks ONLY the general acyclic⟹cert-exists step, '
            'which would upgrade the theorem to `IsAcyclicFactorGraph G → (BP converges)` with no cert hyp.',
        'eliminability': 'hard',
        'elimination_path': 'A finite well-founded construction: leaf-strip the acyclic bipartite '
            'incidence graph (SimpleGraph.deleteEdges + dist + connected-component sup) to assign the '
            'subtree-depth rank and discharge the two strict-monotonicity obligations by a strict-subset '
            'cardinality argument. In-tree buildable (a routine graph-theory grind); scoped as a '
            'follow-up brick.',
        'dependent_theorems': [],
        'module': 'BeliefPropagation.lean (`bp_converges_on_ranked_acyclic` takes cert : BPRankCert G '
            'explicitly; `bp_converges_on_star` is the concrete-tree non-vacuity witness)',
        'source': 'Standard: belief propagation is exact on trees (Pearl 1988; Yedidia–Freeman–Weiss '
            '2003). The rank certificate = the tree topological / subtree-depth order.',
        'risk': 'Very low — BP-exact-on-trees is textbook; the certificate is a routine finite '
            'well-founded construction. Buildable in-tree.',
        'prose': 'Belief propagation converges to a fixed point on tree (acyclic) factor graphs in ≤ '
            'diameter rounds. The project proves this on the actual message-passing dynamics GIVEN the '
            'tree rank certificate (witnessed on a real tree); the general "every acyclic graph admits '
            'the certificate" step is a buildable follow-up.',
    },
    'rokhlin_sigma_mod_16': {
        'tier': 'external_boundary',
        'statement': 'For any closed smooth spin 4-manifold M, 16 | σ(M)',
        'status': 'active (8|σ proven & unconditional; the irreducible topological factor 2|σ/8 is carried as the tracked input topo)',  # CORRECTION 2026-06-13: 16|σ is a kernel-pure theorem over the SmoothSpinManifold4 interface GIVEN topo:2|σ/8 — it is NOT unconditional (16|σ is false for general even unimodular forms: E₈ has σ=8). The earlier 'discharged'/'UNCONDITIONAL' wording overstated this. 8|σ (van der Blij) IS unconditional & proven; the mod-16 factor is irreducibly geometric (Guillou-Marin / Â-genus-even), NOT a lattice Arf (see RokhlinArfNoGo.lean).
        'eliminability': 'very_hard',
        'elimination_path': 'Phase 5q.B (Route B) DECOMPOSED this opaque hypothesis into the narrow '
            'SmoothSpinManifold4 interface (SpinRokhlinInterface.lean) and PROVED 16|σ as a kernel-pure '
            'theorem over it: SmoothSpinManifold4.rokhlin, via even-unimodular + 8|σ composed with 2|σ/8 '
            '(sixteen_dvd_latticeSig_of_eight_dvd_of_topo = rokhlin_from_serre_plus_topology on latticeSig). '
            'INTERFACE REWIRED (2026-06-04): the signature is now the GENUINE latticeSig of the intersection '
            'form (sig := latticeSig form, closing the prior free-unconnected-integer gap), and the algebraic '
            'residual is carried as the PRECISE field eight_dvd : 8 | latticeSig form (the isolated van der '
            'Blij wall), replacing the opaque charSq/CharacteristicSquareModEight. Remaining interface inputs: '
            '(i) even_unimod [Wu formula, topological], (ii) eight_dvd : 8|latticeSig form [van der Blij, the '
            'Wave-B1 ALGEBRAIC target], (iii) topo : 2|σ/8 [Â-genus even (Atiyah-Singer index parity) / '
            'geometric Guillou-Marin Arf of a characteristic SURFACE (Freedman-Kirby) — the single '
            'IRREDUCIBLE topological input. NOTE 2026-06-13: this is NOT the lattice Arf(redQuad), which is '
            'identically 0 on every even unimodular form (E₈: Arf=0 but σ/8=1); the lattice Arf bridge is '
            'FALSE, see RokhlinArfNoGo.lean]. '
            'USER DECISION 2026-06-04: GO FULL via the CLASSIFICATION route (E8^a (+) (-E8)^b (+) H^c), '
            'zero-axiom. SIGNATURE CALCULUS COMPLETE this session (all kernel-pure, ExtractDeps baseline '
            'green 9073 jobs): E8Signature (sigma(E8)=8, sigma(-E8)=-8 via the integer-Cholesky C8^T C8 = '
            '4.E8lit decide-over-Z route), LatticeSignatureCongr (latticeSig_congr = Sylvester congruence '
            'invariance; sigma(H)=0), BlockSignature (sigma(A (+) B)=sigma A+sigma B; nondeg bridge), '
            'GeneratorNondeg (generator nondegeneracy), LatticeSigBlock (latticeSigOf on any index + block '
            'additivity + reindex invariance), RokhlinClassification (the [E3] assembly: generators 8|sigma, '
            'block-sum/congruence/reindex closure, and the bridge sixteen_dvd_latticeSig_of_eight_dvd_of_topo). '
            'CLASSIFICATION SCAFFOLDING: [E1] primitive vectors + dual (LatticePrimitive); [E2]-partial '
            'exists_hyperbolic_pair ({v,w-prime} Gram = H) + even_form_dvd; [E3] assembly DONE. The signature '
            'side is CLOSED: any normal form E8^a (+) (-E8)^b (+) H^c gives latticeSig = 8(a-b), hence 8|sigma. '
            '✅ DISCHARGED 2026-06-08: BOTH irreducible inputs are now kernel-pure THEOREMS. [Theta] '
            'theta-modularity (definite 8|rank) = eight_dvd_latticeSig_of_definite (shipped earlier). [HM] '
            'Hasse-Minkowski (indefinite even unimodular ⟹ isotropic vector) = hasIsotropicVector '
            '(RokhlinHMRankFour), discharging HasWeakIsotropicVectorHyp at EVERY rank: rank ≥5 '
            '(weakIsotropic_of_five_le, general-rank diagonal HM spine diag_nary_zero_of_local with ℝ + odd-p + '
            '2-adic local isotropy all proven), rank 2 (weakIsotropic_rank_two, det=-1 mod-4), ranks 1 & 3 (no '
            'even unimodular form exists), rank 4 (weakIsotropic_rank_four: det=1 forces square discriminant, '
            'then brick (a) odd-p ℤ_p-unimodular isotropy [Chevalley-Warning + Hensel] + brick (b) p=2 via '
            'binary Hilbert reciprocity [quaternary_sqdisc_iso_iff_ternary + hilbertGlobalProd_eq_one] '
            'transported through the explicit congruence A=PᵀdiagP). Hence eight_dvd_latticeSig (8|σ for every '
            'even unimodular form) and sixteen_dvd_latticeSig (16|σ given 2|σ/8) are UNCONDITIONAL. The '
            'SmoothSpinManifold4 structure no longer carries the eight_dvd field — SmoothSpinManifold4.rokhlin '
            '(16|σ) is derived from even_unimod + topo (2|σ/8) ALONE. The ONLY remaining interface input is the '
            'genuinely-topological factor 2|σ/8 (Â-genus even / geometric Guillou-Marin characteristic-surface '
            'Arf — NOT the lattice Arf(redQuad), which is content-free [≡0]; RokhlinArfNoGo.lean). All kernel-pure '
            '{propext,Classical.choice,Quot.sound}, axiom_closure_allowlist GREEN. '
            'sixteen_convergence_unconditional is the companion to sixteen_convergence_full with the 16|σ '
            'conjunct now a full theorem, not an assumed h_rokhlin. Full living decomposition: '
            'docs/roadmaps/Phase5qB_LabNotebook.md.',
        'dependent_theorems': [
            'SKEFTHawking.SmoothSpinManifold4.rokhlin',
            'SKEFTHawking.SmoothSpinManifold4.eight_dvd_sig',
            'SKEFTHawking.hasWeakIsotropicVector',
            'SKEFTHawking.hasIsotropicVector',
            'SKEFTHawking.weakIsotropic_rank_four',
            'SKEFTHawking.eight_dvd_latticeSig',
            'SKEFTHawking.sixteen_dvd_latticeSig',
            'SKEFTHawking.sixteen_dvd_latticeSig_of_eight_dvd_of_topo',
            'SKEFTHawking.sixteen_convergence_unconditional',
            'SKEFTHawking.sixteen_convergence_full',
            'SKEFTHawking.z16_anomaly_without_nu_R',
        ],
        'module': 'SpinRokhlinInterface (Phase 5q.B, rewired to latticeSig); E8Signature + LatticeSignatureCongr + BlockSignature + GeneratorNondeg + LatticeSigBlock + RokhlinClassification (signature calculus, classification route); LatticePrimitive + EvenLatticeForm (classification scaffolding [E1]/[E2]); LatticeSignature (latticeSig); RokhlinBridge (legacy hypothesis form)',
        'source': 'Rokhlin, Dokl. Akad. Nauk SSSR 84, 221 (1952); van der Blij, Math. Z. 74, 18 (1960); Freedman-Kirby (1978)',
        'risk': 'Extremely low — proved 1952, independently confirmed by Atiyah-Singer (1963), Freedman-Kirby (1978). As solid as any result in topology.',
        'circularity_note': 'Anti-circularity verified: the wired derivation routes even-unimodular + van der Blij ⟹ 8|σ, plus 2|σ/8 ⟹ 16|σ; it does NOT use Anderson-Brown-Peterson or Rokhlin''s theorem as input (Rokhlin''s theorem IS the conclusion). The 2-axiom bordism alternative (Ω^Spin_4 ≅ Z) WOULD be circular (ABP used Rokhlin-equivalent facts) — deliberately NOT used.',
    },
    'smith_inflow_z16': {
        'tier': 'discharge_future',
        'statement': 'The Smith homomorphism Ω₅^{Spin-ℤ₄} ≅ ℤ₁₆ → Ω₄^{Pin⁺}, carried at the ℤ₁₆ '
            'level as an isomorphism `ZMod 16 ≃+ SKEFTHawking.SymTFT.Omega4PinPlusBordism` pinned to the '
            'canonical generator `smith 1 = Omega4PinPlusBordism.mk pinPlusRP4` (the structure '
            'SKEFTHawking.CommonOrigin.SmithInflow, consumed via the (S : SmithInflow) binder).',
        # ── 2026-07-21 ATLAS-INTEGRITY REPAIR (wt3). Read this block before using the entry. ──
        'atlas_typing_note': 'THIS KEY DOES NOT NAME AN OPEN LEAN PROPOSITION. Verified in-tree '
            '2026-07-21: its named carrier `SKEFTHawking.CommonOrigin.SmithInflow` '
            '(CommonOrigin.lean:83-87) is a `structure` in `Type` — two fields, an `AddEquiv` and a '
            'generator equality — and it is INHABITED unconditionally by `substrateSmithInflow` '
            '(CommonOrigin.lean:92-96, from the Kirby–Taylor iso) and CANONICAL/unique by '
            '`smithInflow_smith_unique`. So there is nothing to "discharge" at the Lean level. What '
            'remains genuinely open is the GEOMETRIC FAITHFULNESS of the thin Ω₅/Ω₄ substrates and the '
            'η-invariant — an interpretation gap that is NOT a Lean proposition and therefore cannot be '
            'ranked as an open frontier node. FOUR DISTINCT OBJECTS have historically been referred to '
            'through this one key; they are NOT definitionally the same statement and must not be '
            'conflated: (1) THIS key = the thin `SmithInflow` structure — INHABITED, closed; (2) the '
            'intended geometric direct-Smith program (a faithful smooth/T2 dim-6 Pin⁻ carrier A, '
            '`Nonempty (A ≃+ ZMod 16)` from a real PT/ABP/Adams computation, a codim-2 geometric Smith '
            'hom, and its two exactness legs) — NEVER STATED in-tree; only the generic algebra exists '
            '(`PinPlusGMDataZ16.omega4PinPlusGMData_ext_equiv_zmod16_via_smith_les_neighbor`, arbitrary '
            'A/B); this is the object the `very_hard` tag actually fits; (3) the RETIRED old-tied-carrier '
            'Props `hbound` (PinPlusGMWitness.lean:431-436) and `hexact` (SpinSigmaRouteDoor.lean:47-58) '
            '— VACATED, see KERNEL_NOGO_REGISTRY["5qH-injectivity-routes-apex-equivalent"]; (4) the CURRENT '
            'faithful-carrier completeness prop `KernelReducesToSpin prov` '
            '(PinPlusKTKernelSector.lean:223-225) — the live open node, on a different carrier, tracked in '
            'the KT lane, NOT here.',
        'atlas_impact_note': 'The `dependent_theorems` list below was hand-written and formerly held 12 '
            'entries, which the derived atlas turned verbatim into `frontier_impact: 12` — ranking this '
            'key #1 on the open frontier. Verified 2026-07-21: only SIX in-tree declarations actually take '
            'an `(S : SmithInflow)` binder. Of the former twelve, `..._substrate` and '
            '`..._via_constructed_smith` carry NO binder (both are proved at an instantiated inflow); '
            '`smithInflowOfSmithHom` PRODUCES a SmithInflow rather than consuming one; and the four '
            '`PinPlusDischarge.*` entries consume `pin4_abutment`, not `SmithInflow` (and `pin4_abutment` '
            'is itself inhabited by `pin4_abutment_substrate`). The list is corrected below; the '
            'previously-advertised impact of 12 was never Lean-derived.',
        'status': 'superseded — RETIRED AS A STRATEGIC KEYSTONE (2026-07-21 atlas-integrity repair), '
            'formalizing the 2026-07-06 user-directed KT re-anchor which already DEMOTED this node to "an '
            'alternative route, not the required keystone" (SETTLED_FORKS § '
            '5qH-injectivity-routes-all-equal-one-completeness-prop; PHASE5QH_EXECUTION_MAP: "the keystone '
            'is the KT GEOMETRIC exact-sequence close, NOT the spectral smith_inflow_z16 / ABP tower"). '
            'Retired for TWO independent reasons: (a) the Lean object named here is inhabited and '
            'canonical — not an open proposition (see atlas_typing_note); (b) the live 16-convergence '
            'keystone is the KT lane on the faithful `pinPlusCharPairData` carrier, whose open triple is '
            '{KernelReducesToSpin, SpinImageIsTwo, KTNonSplit}. The entry is KEPT (not deleted) for '
            'provenance and because the geometric direct-Smith program (object 2 above) remains a real, '
            'genuinely very-hard ALTERNATIVE route should the KT lane ever be abandoned; if it is revived '
            'it must be re-entered as a NEW key naming the faithful dim-6 carrier explicitly, never on '
            'this thin-structure key. HISTORICAL RECORD FOLLOWS (unchanged, pre-2026-07-21): '
            'at the HYPOTHESIS level the W5 SmithInflow binder is now DISCHARGED by W6: '
            'the abstract iso is replaced by a CONSTRUCTED substrate Smith map (SymTFT.smithHom : Ω₅ → Ω₄^{Pin⁺}, '
            'SpinZ4Bordism5.lean), and sixteen_convergence_common_origin_via_constructed_smith takes no '
            'SmithInflow binder. This entry remains active because the GEOMETRIC FAITHFULNESS of the thin Ω₅/Ω₄ '
            'substrates + the genuine η-invariant are still tracked (a LARGER gap than the Pin⁺ side — the '
            'Dai–Freed invariant is ℤ₁₆-native; see elimination_path). The W5 binder form (SmithInflow) also '
            'survives, INHABITED by substrateSmithInflow and CANONICAL/unique by smithInflow_smith_unique. A '
            'hypothesis, NOT an axiom; all dependent theorems kernel-pure {propext, Classical.choice, Quot.sound}. '
            'W5+W8 UPDATE 2026-06-14 (Phase 5q.F finite discharge, PinPlusDischarge.lean): the SmithInflow ISO '
            'content (ZMod 16 ≃+ Ω₄^{Pin⁺}) is now DERIVED from the FINITE A(1)-Ext, not posited. The Pin⁺ Adams '
            'column t−s=4 height-4 cap is decidable F₂ linear algebra (PinPlusHeight4.col4_height_eq_four = 4, '
            'axioms:[], the Campbell δ=·h₀ cokernel), so |Ω₄^{Pin⁺}| = 2^4 = 16 from the finite Ext height; the '
            'old DeltaTruncationCap (16·[RP⁴]=0) is DERIVED (deltaCap_of_pin4). The single tracked input is REDUCED '
            'from the opaque SmithInflow to ONE precise disclosed Prop pin4_abutment = Pontryagin–Thom '
            '(Ω₄^{Pin⁺}=π₄MTPin⁺) + Adams convergence (E₂=E∞, no hidden ext); inhabited (pin4_abutment_substrate). '
            'sixteen_convergence_finite_discharge carries NO SmithInflow binder (takes pin4_abutment); the ℤ/16 is '
            'from finite content (criterion 8). The RESIDUAL tracked landmark is now just pin4_abutment (PT + '
            'convergence), Mathlib-absent (Thom-spectrum / stable-homotopy), per the axiom-stratified framework '
            '(Phase-5a chirality-wall l.57/100: the finite A(1)-Ext "partially discharges the cobordism axiom"). '
            'RETIREMENT 2026-06-15 (Phase 5q.F criterion 4): PinPlusDischarge §6 + Omega5FiniteIso re-pointed onto '
            'the GENUINE W4 bordism group DataBordismGrp ξ (real SingularManifolds over manifolds-with-boundary) — '
            'sixteen_convergence_genuine_carrier / omega5_quotient_iso_zmod16_genuine_carrier derive the ℤ/16 as '
            'the image of the genuine ABK/η grade (UNCONDITIONAL via the quotient '
            'dataBordism_quotient_abk_equiv_zmod16; full-carrier via the single disclosed PinPlusBordismLandmark = '
            'the OBJECTIVE-permitted Brown/ABK order-16 + height-4 ≤16 finite inputs). pin4_abutment / '
            'Omega4PinPlusBordism / the adamsAbutment modeling def are DEMOTED to finite-substrate corollaries; no '
            'load-bearing modeling DEFINITION remains for the geometric ℤ/16. The W5 geometric Smith map is the '
            'typed hom SmithIsomorphism.smithDataHom (DR Smith_sequence.md §5.2 scope) with the genuine manifold '
            'layer (SmithIsomorphism.smithImageSingularManifold, bricks 1-2: PD(a) a real codim-1 SingularManifold '
            'over arbitrary M). pin4_abutment remains CONSUMED by the demoted §1-§5 forms, hence still registered here.',
        'eliminability': 'very_hard',
        'elimination_path': 'Build the GEOMETRIC inputs the structure stands in for: (i) the Ω₅^{Spin-ℤ₄} '
            'bordism group, (ii) the geometric Smith homomorphism Ω₅^{Spin-ℤ₄} → Ω₄^{Pin⁺}, and (iii) the '
            'Dai–Freed anomaly functor — all Mathlib-absent landmarks (Phase 5q.E roadmap §Walls + §Mathlib '
            'status, verified 2026-06-14 via semantic search). The Pin⁺ HALF (Ω₄^{Pin⁺} ≃+ ZMod 16) already '
            'exists as the Phase 6r SymTFT/PinPlusBordism4 substrate. '
            'W6 UPDATE 2026-06-14 (corrects an earlier overstatement): a thin Ω₅^{Spin-ℤ₄} SUBSTRATE IS now '
            'built (SpinZ4Bordism5.lean) — a genuine, kernel-pure `Quotient ≃+ ZMod 16` carrying `daiFreed : ℤ` '
            'with a 16∣Δ relation, plus a CONSTRUCTED Smith map `smithHom : Ω₅ → Ω₄^{Pin⁺}`. The earlier '
            '"NOT a thin-wrapper away / collapses to ZMod 16 (vacuous)" wording was wrong in one direction: the '
            'Quotient is NOT vacuous (it is a real ≃+ ZMod 16, like the Pin⁺ one). BUT it is a LESS-FAITHFUL '
            'stand-in for the geometric Ω₅ than the Pin⁺ signature is for Ω₄: the Dai–Freed invariant is '
            'ℤ₁₆-native (η/16 mod 1, no natural ℤ-lift), so carrying `daiFreed : ℤ` additionally tracks "the '
            'invariant takes ℤ values at all" — a tracked gap LARGER than the Pin⁺ side. So W6 discharges this '
            'input at the HYPOTHESIS level only (no abstract Lean binder in '
            'sixteen_convergence_common_origin_via_constructed_smith), NOT at the geometry/faithfulness level. '
            'The GEOMETRIC construction of Ω₅ from manifolds + the η-invariant (placeholder in APSEta) + the '
            'geometric Smith/Dai–Freed maps remain the Mathlib-absent landmark, trigger-gated per ADR-003 '
            '(shared frontier with Leg C/D). On the ADR-003 Leg D trigger (Mathlib ships spin-flavored bordism '
            'groups + the Dirac-operator/η machinery), build the geometric (i)+(ii)+(iii) to upgrade the chain '
            'from substrate-constructed to geometrically-faithful.',
        # CORRECTED 2026-07-21 (see atlas_impact_note): exactly the in-tree declarations that take an
        # `(S : SmithInflow)` binder — verified by a whole-tree scan for the identifier. Six, not twelve.
        'dependent_theorems': [
            'SKEFTHawking.CommonOrigin.sixteen_convergence_common_origin',
            'SKEFTHawking.CommonOrigin.rokhlin_reads_kitaev',
            'SKEFTHawking.CommonOrigin.kitaev_generator_is_bordism_generator',
            'SKEFTHawking.CommonOrigin.sm_anomaly_trivial_in_bordism',
            'SKEFTHawking.CommonOrigin.sm_spin10_count_trivial_in_bordism',
            'SKEFTHawking.SixteenConvergenceDerived.sixteen_convergence_derived',
        ],
        # Formerly listed as dependents; each verified 2026-07-21 to take NO `SmithInflow` binder. Kept
        # here so the correction is auditable and the entries are not silently lost.
        'former_dependent_theorems_without_binder': {
            'SKEFTHawking.CommonOrigin.sixteen_convergence_common_origin_substrate':
                'proved at the inhabited substrateSmithInflow; no binder',
            'SKEFTHawking.CommonOrigin.sixteen_convergence_common_origin_via_constructed_smith':
                'W6 constructed-smithHom form; no binder',
            'SKEFTHawking.CommonOrigin.smithInflowOfSmithHom':
                'a `def` PRODUCING a SmithInflow — a witness, not a consumer',
            'SKEFTHawking.PinPlusDischarge.pin4_abutment':
                'a `def` for a different Prop; inhabited by pin4_abutment_substrate',
            'SKEFTHawking.PinPlusDischarge.pinPlus_iso_zmod16_of_pin4':
                'takes (h : pin4_abutment), not SmithInflow',
            'SKEFTHawking.PinPlusDischarge.deltaCap_of_pin4':
                'takes (h : pin4_abutment), not SmithInflow',
            'SKEFTHawking.PinPlusDischarge.sixteen_convergence_finite_discharge':
                'takes (h : pin4_abutment), not SmithInflow',
        },
        'module': 'CommonOrigin (Phase 5q.E W5 + W6); Pin⁺ half from SymTFT/PinPlusBordism4 (Phase 6r); '
            'Ω₅ substrate + constructed Smith from SymTFT/SpinZ4Bordism5 (W6); Kitaev reading from '
            'KitaevSixteenFold (W1)',
        'source': 'García-Etxebarria–Montero, JHEP 08 (2019) 003 [arXiv:1808.00009]; Wang (2024) '
            'Smith-homomorphism / string-bordism. NOTE: what the literature establishes is the ISO-NESS (the '
            'Smith hom is a generator-preserving isomorphism ℤ₁₆ ≅ ℤ₁₆) — that is cited-true; the SPECIFIC '
            'generator pin `smith 1 = [RP⁴]` is the canonical Kirby–Taylor normalization (a convention, not '
            'itself a cited theorem; the true Smith hom agrees up to a generator relabeling).',
        'risk': 'Low. The carried fact (Smith hom is an iso ℤ₁₆ ≅ ℤ₁₆) is established in the literature '
            '(GEM 2018 / Wang 2024); only its geometric CONSTRUCTION is Mathlib-absent. Crucial contrast with '
            'the FALSE lattice-Arf bridge (RokhlinArfNoGo.lean): there a claimed identity was false; here the '
            'cited fact is TRUE and only the construction is absent. The conditional is inhabited '
            '(substrateSmithInflow) and canonical (smithInflow_smith_unique), so it is neither vacuous nor a '
            'choice-dependent artifact.',
        'prose': 'The "16 convergence" common-origin theorem (CommonOrigin.lean) is honestly CONDITIONAL on '
            'this Smith-inflow input: GIVEN the Smith homomorphism (whose ℤ₁₆ iso-ness is established by '
            'García-Etxebarria–Montero 2018 and Wang 2024), the four occurrences of 16 — the Standard Model '
            'Weyl-fermion count, the ℤ₁₆ global anomaly, Rokhlin signature divisibility, and the Kitaev 16-fold '
            'way — are images of one genuine ℤ₁₆ (the Pin⁺ bordism group) under explicit maps, with Rokhlin and '
            'Kitaev reading it identically. The result still CONSTRAINS rather than DERIVES the Standard Model '
            '(the SM is the trivial class among 16). W6 (2026-06-14) builds a thin Ω₅^{Spin-ℤ₄} bordism '
            'substrate and a CONSTRUCTED Smith map, so the theorem can be stated with no abstract Lean '
            'hypothesis (sixteen_convergence_common_origin_via_constructed_smith) — but this is a '
            'HYPOTHESIS-LEVEL change only: the GEOMETRIC construction of the Smith map and the Ω₅ bordism group '
            'from manifolds + the η-invariant remain Mathlib-absent, and the thin substrates carry a tracked '
            'faithfulness gap (larger for Ω₅ than for the Pin⁺ side, as the Dai–Freed invariant is ℤ₁₆-native). '
            'So the convergence is a genuine ℤ₁₆-level map-composition; it must NOT be quoted as a geometric '
            'derivation or an unconditional unification.',
        'circularity_note': 'None. The common-origin theorem is honestly CONDITIONAL on this input — it does '
            'not assume its own conclusion. Verified by adversarial review (2026-06-14): the headline '
            'rokhlin_reads_kitaev is provably NOT rfl/simp/decide-able for an arbitrary SmithInflow, so the '
            'hypothesis does not smuggle the conclusion; it genuinely requires coherence of the '
            'independently-constructed Kitaev (KitaevSixteenFold) and Rokhlin (PinPlusBordism4) maps. Review '
            'verdict: "the legitimate opposite of the Arf-bridge failure mode."',
    },
    'modular_invariance_framing': {
        'tier': 'external_boundary',
        'statement': 'The framing anomaly requires e^{2πic/24} = 1 for a consistent TQFT, i.e., 24 | c₋',
        'status': 'active',
        'eliminability': 'hard',
        'elimination_path': 'Requires formalizing: (a) Atiyah 2-framing on 3-manifolds, (b) the relation between central charge and framing anomaly, (c) Witten-Reshetikhin-Turaev invariant modularity. The algebraic consequence (24 | c₋) is proved; the physical INPUT (framing anomaly = modularity constraint) is the hypothesis.',
        'dependent_theorems': [
            'SKEFTHawking.wang_bridge_full_chain',
            'SKEFTHawking.generation_constraint_iff',
        ],
        'module': 'WangBridge',
        'source': 'Witten, Comm. Math. Phys. 121, 351 (1989); Atiyah, Topology 29, 1 (1990)',
        'risk': 'Extremely low — foundational result in TQFT, universally accepted.',
        'circularity_note': 'None.',
    },
    'c_minus_equals_8Nf': {
        'tier': 'external_boundary',
        'statement': 'The chiral central charge of N_f generations of SM fermions is c₋ = 8N_f',
        'status': 'active',
        'eliminability': 'algebraic',
        'elimination_path': 'This was DERIVED (not hypothesized) in WangBridge.lean from the 16 Weyl fermions per generation. But the derivation assumes the standard SM fermion content — the hypothesis is that the SM has exactly 16 Weyl fermions per generation.',
        'dependent_theorems': [
            # R-07 (2026-07-20): was 'SKEFTHawking.central_charge_from_sm', which
            # does not exist in lean_deps.json. The real derivation theorem is
            # fermion_count_gives_central_charge — weyl_central_charge(Σ SMFermion
            # components) = 8, i.e. c₋ = 16/2 = 8 per generation from the SM count.
            'SKEFTHawking.fermion_count_gives_central_charge',
        ],
        'module': 'WangBridge',
        'source': 'SM fermion content (standard textbook result)',
        'risk': 'Zero — this is the definition of the SM.',
        'circularity_note': 'None.',
    },
    'characteristic_square_mod_8': {
        'tier': 'external_boundary',
        'statement': 'For any unimodular symmetric bilinear form and any characteristic vector c, c^T M c ≡ σ(M) mod 8',
        'status': 'superseded_on_wiring_path',  # Phase 5q.B 2026-06-04: the SmoothSpinManifold4 interface no longer routes through this; it carries the precise 8|latticeSig form directly (classification route). Retained as a valid alternate algebraic formulation.
        'eliminability': 'hard',
        'elimination_path': 'SUPERSEDED ON THE WIRING PATH (2026-06-04): the rewired SmoothSpinManifold4 '
            'interface no longer consumes this characteristic-vector formulation (serre_even_unimodular_mod8 '
            'used it only at c=0, i.e. only to extract 8|σ). The interface now carries the precise residual '
            'eight_dvd : 8 | latticeSig form directly, whose discharge target is the even-unimodular '
            'CLASSIFICATION (E8^a (+) (-E8)^b (+) H^c), with the signature calculus already complete '
            '(RokhlinClassification et al.) and only the classification existence ([E2] Smith-Normal-Form '
            'basis-completion + [HM] Hasse-Minkowski + [Theta] theta-modularity) remaining. This entry is '
            'retained as a valid ALTERNATE algebraic formulation (Serre/van der Blij characteristic-vector '
            'route); it still requires the classification of indefinite unimodular forms (Hasse-Minkowski) or '
            'the van der Blij Gauss-sum lemma, neither in Mathlib. serre_even_unimodular_mod8 and '
            'CharacteristicSquareModEight remain defined and valid in AlgebraicRokhlin.lean.',
        'dependent_theorems': [
            'SKEFTHawking.serre_even_unimodular_mod8',
        ],
        'module': 'AlgebraicRokhlin (alternate route; no longer on the SpinRokhlinInterface wiring path)',
        'source': 'Serre, "A Course in Arithmetic" (1973), Ch. V; van der Blij, Math. Z. 74, 18 (1960)',
        'risk': 'Extremely low — proved independently by Serre (1973) and van der Blij (1960). Textbook result.',
        'circularity_note': 'None. Purely algebraic result about bilinear forms, independent of topology.',
    },
    'spin_bordism_iso_Z': {
        'tier': 'external_boundary',
        'statement': 'Ω^Spin_4 ≅ Z, generated by the K3 surface with σ(K3) = -16',
        'status': 'proposed',  # Not yet used — proposed for Wave 7C
        'eliminability': 'very_hard',
        'elimination_path': 'Requires Adams spectral sequence computation (Anderson-Brown-Peterson 1966-67). Probably 10+ years from formalization in any proof assistant.',
        'dependent_theorems': [
            'SKEFTHawking.SpinSigmaRoute.SpinSigmaPresentation.dataBordismGrp_equiv_int',
            'SKEFTHawking.SpinSigmaRoute.SpinSigmaPresentation.sig_injective',
            'SKEFTHawking.SpinSigmaRouteDoor.omega4PinPlusGMTied_equiv_zmod16_via_sigma_route_full',
        ],  # Would be used in bordism-derived Rokhlin
        'module': 'proposed: SpinBordism.lean',
        'source': 'Anderson-Brown-Peterson, Bull. AMS 72, 256 (1966)',
        'risk': 'Extremely low — standard result in algebraic topology.',
        'circularity_note': 'CAUTION: The ABP computation historically used facts equivalent to Rokhlin theorem. Using this to DERIVE Rokhlin creates a logical dependency chain where A proves B but A was originally proved using B. The mathematical content is not circular (ABP can be proved independently of Rokhlin via Adams spectral sequence), but the historical provenance is tangled. If used, should be clearly documented as an independent route, not as "proving" Rokhlin from more basic facts.',
    },
    'H_KLRS_SM_Crossover': {
        'tier': 'external_boundary',
        'statement': 'The full thermal-resummed SM electroweak phase transition is a crossover (not first-order) at the physical Higgs mass m_H = 125.20 GeV. Equivalently: the strict-LO smBenchmarkParams cubic coefficient E = 0.01 is driven below the crossover threshold by full thermal corrections at m_H ≫ KLRS endpoint 72.4 GeV.',
        'status': 'active',
        'eliminability': 'hard',
        'elimination_path': 'Requires formalizing finite-temperature lattice thermodynamics infrastructure (Wilson-flow gradient + dimensional reduction at T ≳ T_c + lattice artifact extrapolation) to derive the KLRS 1996 / CFH 1999 endpoint at m_H = 72.4 ± 1.7 GeV from continuum perturbation theory. Out of scope for the Lean library; replication is the standard validation path. The quantitative anchor sm_klrs_overshoot_ratio_gt_threshold (1.5 < 125.20/72.4 ≈ 1.73) provides a falsifiable physical-input lever: if a future lattice study revises the endpoint upward to m_H > 83.5 GeV, the overshoot would drop below 1.5 and the hypothesis would weaken.',
        'dependent_theorems': [
            'SKEFTHawking.EWBaryogenesisChiralityWall.sm_with_3nu_R_ewbg_forbidden_under_klrs',
            'SKEFTHawking.EWBaryogenesisChiralityWall.sm_no_nu_R_ewbg_doubly_forbidden',
        ],
        'module': 'EWBaryogenesisChiralityWall',
        'source': 'Kajantie, Laine, Rummukainen, Shaposhnikov, PRL 77, 2887 (1996), arXiv:hep-ph/9605288 (initial endpoint); refined by Csikor, Fodor, Heitger, PRL 82, 21 (1999), arXiv:hep-ph/9809291 (m_H endpoint = 72.4 ± 1.7 GeV).',
        'risk': 'Extremely low — KLRS / CFH are well-established lattice results, replicated by independent groups (Aoki et al., Bödeker et al.) and consistent with continuum dimensional-reduction analyses. The crossover verdict at m_H = 125.20 GeV is universally accepted in the EWBG community.',
        'circularity_note': 'None. The hypothesis is a downstream lattice result that takes the SM gauge + Higgs sector as input and produces a thermodynamic verdict; no logical dependency on theorems within the project.',
    },
    'H_ScalarChannelIsTetradBifurcationOutput': {
        'statement': 'For a ScalarChannel s arising from the TetradGapEquation supercritical branch and a UV cutoff Λ_UV, the condensate VEV satisfies √(μ²/λ) ≤ Λ_UV (no super-UV condensates).',
        'status': 'active',
        'eliminability': 'hard',
        'elimination_path': 'Requires resolution of Open Question O.2: a quantitative bridge mapping the Wetterich scalar-channel parameters (μ², λ) to the GL-expansion coefficients of the tetrad gap-equation bifurcation. Once O.2 is closed (via deep-research derivation of the supercritical-branch coefficient identities), the kinematic bound √(μ²/λ) ≤ Λ_UV becomes a theorem of TetradGapEquation rather than an external hypothesis.',
        'dependent_theorems': [
            'SKEFTHawking.mexican_hat_vev_under_supercritical_bridge',
            'SKEFTHawking.bridge_excludes_super_uv_vev',
        ],
        'module': 'ScalarRungInterpretation',
        'source': 'Tracked external hypothesis pending Open Question O.2 (deep-research-gated). Disclosed in paper20 (papers/paper20_scalar_rung/paper_draft.tex L181, L368). Project precedent: same tracked-hypothesis pattern in HiddenSectorMixedCharge.H_MixedChannelZ16Cancels and DarkSectorSynthesis.H_VestigialRelicCarriesZ16Charge.',
        'risk': 'Low — the kinematic constraint √(μ²/λ) ≤ Λ_UV is a generic effective-field-theory consistency requirement (no super-UV condensates) and is expected to hold for any ScalarChannel that genuinely emerges from the tetrad gap-equation supercritical branch. The hypothesis is genuinely non-trivial (can fail for super-UV scalar channels) but is structurally aligned with EFT validity. The contrapositive `bridge_excludes_super_uv_vev` provides explicit falsifiability.',
        'circularity_note': 'None. The hypothesis cleanly separates the qualitative bifurcation-output identification (currently external) from the algebraic Mexican-hat consequences (proved in Lean). No circular dependency on any downstream theorem.',
        'tier': 'discharge_future',
    },

    # ════════════════════════════════════════════════════════════════
    # Substrate Integrity Gates W3 (2026-06-13): SINGLE SOURCE OF TRUTH.
    # This registry is now the sole tracked-hypothesis ledger;
    # docs/PERMANENT_TRACKED_HYPOTHESES.md is AUTO-GENERATED from it
    # (scripts/render_tracked_hypotheses.py). New optional fields:
    #   tier  : 'headline' (a published-paper headline rides on it) |
    #           'external_boundary' (KEEP — research-grade / project-scope) |
    #           'discharge_future' (in-principle derivable; scheduled) |
    #           'local' (algebraic/intermediate hypothesis, module-scoped).
    #   prose : publication-facing narrative for the generated md.
    # Merged the 4 cosmology Props formerly only in the markdown doc, and
    # registered the consumed-but-unledgered tracked Props found by
    # `validate.py --check tracked_hypothesis_ledger` (R3 / Invariant #16).
    # ════════════════════════════════════════════════════════════════

    # ---- merged from PERMANENT_TRACKED_HYPOTHESES.md (cosmology Props) ----
    'H_VestigialModeIsGraviton': {
        'statement': 'A vestigial-mode coupling χ_vest represents a graviton-like d.o.f.: 0<χ_vest ∧ LigoSatisfied(c_GW_deviation χ_vest) ∧ |c_GW_deviation χ_vest| < 1/2.',
        'status': 'active', 'tier': 'external_boundary', 'eliminability': 'open',
        'module': 'GravitationalWaves',
        'elimination_path': 'Out of scope for SK_EFT_Hawking (analog-Hawking BEC, not full QG). Would require a microscopic substrate from which the vestigial-mode→graviton bridge follows.',
        'source': 'Volovik 2024 ("second-sound graviton"): derives s₂=c at equilibrium but NO off-shell propagator / matter coupling; "the type of graviton this mode represents requires further consideration".',
        'risk': 'Conjectural. Anchor at χ_vest=1 + 4 falsifiers establish non-vacuity.',
        'circularity_note': 'None.',
        'prose': 'KEEP_AS_TRACKED. The hydrodynamic-mode→graviton bridge is, to our knowledge, not derived in any published source; the tracked-Prop form is the principled treatment. Discharging would mean shipping a different microscopic theory than this project commits to.',
    },
    'H_DESICompatibility': {
        'statement': 'A dark-energy predictor produces (w₀,w_a) within (0.1, 0.2) of the DESI DR2 CPL best-fit (−0.838, −0.62) for some positive (Λ_UV, N_f, α_ADW).',
        'status': 'active', 'tier': 'discharge_future', 'eliminability': 'hard',
        'module': 'FLRWDynamics',
        'elimination_path': 'Phase 6b.2 (NOT currently active): coupled FLRW perturbations → growth observable → CPL extraction → DESI likelihood. ~50 person-hours.',
        'source': 'DESI DR2 CPL best-fit; ADW multi-scalar mechanism (FLRWDynamics).',
        'risk': 'Derivable in principle within the substrate; not yet executed. 3 falsifiers establish non-vacuity (ΛCDM CPL gap 0.162 > 0.1).',
        'circularity_note': 'None.',
        'prose': 'DISCHARGE_FUTURE_PHASE (6b.2). Honest interim framing: expected to follow derivatively from ADW dynamics once cosmological-perturbation machinery ships. External writeups must hedge "predicated on H_DESICompatibility, open pending 6b.2".',
    },
    'H_RT_Formula_Valid': {
        'statement': 'A black-hole-entropy function S_BH satisfies the Ryu–Takayanagi proportionality S = A/(4 G_N) for all positive (A, G_N).',
        'status': 'active', 'tier': 'external_boundary', 'eliminability': 'open',
        'module': 'RTCasiniHuertaBounds',
        'dependent_theorems': ['SKEFTHawking.rt_entropy_pos', 'SKEFTHawking.rt_falsified_by_kaul_majumdar', 'SKEFTHawking.isolatedHorizon_violates_H_RT', 'SKEFTHawking.kaulMajumdarS_violates_H_RT_via_IH'],
        'elimination_path': 'Out of Phase-6 scope (no holographic dual derived). RT is a QG conjecture outside AdS/CFT.',
        'source': 'Ryu–Takayanagi; Lewkowycz–Maldacena replica trick (AdS/CFT).',
        'risk': 'Empirically supported in AdS/CFT; research-grade conjecture in general QG. 4 substantive consumers (RT-vs-alternatives distinguishable).',
        'circularity_note': 'None.',
        'prose': 'KEEP_AS_TRACKED. Load-bearing boundary condition; consumers establish RT-vs-Kaul-Majumdar/loop-quantum-gravity distinguishability. External comms hedge when used outside AdS/CFT.',
    },
    'TPFConjecture': {
        'statement': 'For every anomaly-free SPT phase there exists a local, symmetric, gapped interface Hamiltonian with unique ground state and short-range entanglement (Thorngren–Preskill–Fidkowski 2026).',
        'status': 'active', 'tier': 'external_boundary', 'eliminability': 'open',
        'module': 'SPTClassification',
        'elimination_path': 'No proof in any proof assistant; would need the full TPF gapped-interface construction.',
        'source': 'Thorngren–Preskill–Fidkowski 2026 (TPF conjecture). Converted from `axiom gapped_interface_axiom` → tracked Prop on 2026-05-19.',
        'risk': 'Research-grade conjecture. Strengthened by FKGappedInterface.lean.',
        'circularity_note': 'None.',
        'prose': 'KEEP_AS_TRACKED (ex-axiom). The conversion from a global axiom to a consumed tracked Prop made the assumption visible at the type level; this is the principled framing pending a constructive interface proof.',
    },

    # ---- consumed tracked Props found by the W3 ledger sweep (register) ----
    'H_CasiniHuerta_Bound_Valid': {
        'statement': 'For a 2D-CFT entanglement entropy S_ent(L) with central charge c and UV cutoff ε, the Casini–Huerta log bound S_ent(L) ≤ (c/3) log(L/ε) holds for all L > ε > 0.',
        'status': 'active', 'tier': 'external_boundary', 'eliminability': 'hard',
        'module': 'RTCasiniHuertaBounds',
        'source': 'Casini–Huerta (CFT entanglement-entropy bound).', 'risk': 'Established CFT result; tracked as external CFT input.',
        'circularity_note': 'None.', 'prose': 'External CFT boundary input consumed by the RT/Casini-Huerta bridge theorems.',
    },
    'H_HorizonBoundaryCondition': {
        'statement': 'Bundles the five conditions a horizon-bounding MTC must satisfy for S(A) = A/(4 G_N^emerg) + log corrections: positivity, area-leading (κ>0), second law (monotone), modularInvariant (S-matrix non-degenerate), anomalyMatch (8 ∣ c₋, the Walker–Wang Z₂ inflow). Wave 8 (2026-06-14) replaced the modularInvariant/anomalyMatch True placeholders with these real, falsifiable predicates.',
        'status': 'active', 'tier': 'external_boundary', 'eliminability': 'hard',
        'module': 'BHEntropyMicroscopic',
        'source': 'Microscopic BH-entropy program (BHEntropyMicroscopic / QECHolographyBridge).', 'risk': 'Bundle of well-motivated horizon conditions; tracked as external boundary (no published derivation pins a specific MTC at a 4D ADW horizon). Wave-8 hardened: each conjunct is independently witnessed AND falsified, and the full bundle is satisfiable (fibonacci_horizon_satisfies_H_HorizonBoundaryCondition).',
        'circularity_note': 'None.', 'prose': 'A 5-condition bundle Prop carrying a companion HorizonModularData (S-matrix + c₋); consumed by the microscopic-entropy and QEC-holography bridges. Wave 8: modularInvariant := md.modular, anomalyMatch := (8 ∣ c₋) — no longer True placeholders.',
    },
    'H_Sakharov': {
        'statement': 'Sakharov induction condition: the physical Newton constant is fully induced by N_f Dirac fermion loops (no bare gravitational action), G_N = G_N_from_a2 = 12π/(N_f Λ²). Consumed by the Frolov–Fursaev induced-gravity 1/4 conditional (Phase 6a Wave 9, frolov_fursaev_quarter_coefficient).',
        'status': 'active', 'tier': 'external_boundary', 'eliminability': 'hard',
        'module': 'InducedGravityEntropy',
        'source': 'Sakharov 1967 induced gravity; Adler 1982; Frolov–Fursaev–Zelnikov, Nucl. Phys. B 486 (1997), hep-th/9607104.',
        'risk': 'Standard induced-gravity premise (no bare action); equivalent to α_ADW = 1 (δG = 0) via matchResidual_eq_zero_iff_alpha_unity (bridge H_Sakharov_iff_alpha_unity). Independent of the BH-entropy normalization — does NOT assume S = A/4G.',
        'circularity_note': 'None — Sakharov induction (G_N from loops) is independent of demanding S = A/4G; bridged to α_ADW = 1, and the 1/4 emerges from the shared Seeley–DeWitt a₂ ratio (48:12), not a tuning.',
        'prose': 'The fully-induced-G_N condition consumed by frolov_fursaev_quarter_coefficient to derive κ = 1/(4 G_N) (Gate A.2). Witnessed (Dirac, frolov_fursaev_dirac_witness) and falsified (wrong heat-kernel coefficient, frolov_fursaev_falsifier_wrong_coeff).',
    },
    'H_RegimePartition': {
        'statement': 'Glorioso–Liu second-law bundle: dynamical-KMS ℤ₂ symmetry + unitarity (Im S_eff ≥ 0) ⟹ local entropy-current monotonicity ∂_μ s^μ ≥ 0, without invoking pointwise NEC.',
        'status': 'active', 'tier': 'external_boundary', 'eliminability': 'hard',
        'module': 'BHThermodynamicsFourLaws',
        'source': 'Glorioso–Liu, arXiv:1612.07705 §III Eq. 3.20.', 'risk': 'Established SK-EFT result; tracked as external theorem-bundle input.',
        'circularity_note': 'None.', 'prose': 'Post-Stage-13 strengthened bundle encoding the Glorioso-Liu entropy-current theorem.',
    },
    'H_VergelesPositivity': {
        'statement': 'Osterwalder–Schrader reflection-positivity on the lattice ADW theory ⟹ α_ADW > 0 strictly inside the broken phase (G/G_c > 1).',
        'status': 'active', 'tier': 'external_boundary', 'eliminability': 'hard',
        'module': 'LinearizedEFE',
        'source': 'Vergeles, PRD 112, 054509 (2025).', 'risk': 'Published lattice reflection-positivity result; tracked as external input.',
        'circularity_note': 'None.', 'prose': 'External lattice-positivity input giving α_ADW > 0 in the broken phase.',
    },
    'H_PMNSAnglesFromExactSubstrate': {
        'statement': 'A PMNS matrix exhibits exact substrate μ-τ row symmetry (holds at θ₂₃ = π/4; NuFit-6.0 best fit 49.1° does NOT satisfy it — row magnitudes differ by ≈0.1).',
        'status': 'active', 'tier': 'headline', 'eliminability': 'hard',
        'module': 'NeutrinoMixing',
        'elimination_path': 'WAVE2-OPEN-2: derive exact μ-τ symmetry from the substrate (vs assume); gates the PMNS prediction (paper40).',
        'source': 'NuFit-6.0; substrate μ-τ symmetry.', 'risk': 'Strict predicate, falsifiable against NuFit; headline-gating for the neutrino-mixing prediction.',
        'circularity_note': 'None.', 'prose': 'Headline-gating: the PMNS prediction is conditional on exact substrate μ-τ symmetry, which the empirical best fit does not exactly satisfy.',
    },
    'Phase6hHyperchargeSplittingHypothesis': {
        'statement': 'Bundle of the three substrate parameters (δ_f flavour charge, α_∗ AS fixed-point coupling, Λ_UV) that would parametrize the closed-form light-quark prediction m_f/Λ_UV ~ exp(...).',
        'status': 'active', 'tier': 'discharge_future', 'eliminability': 'hard',
        'module': 'LightQuarkHierarchyFallthrough',
        'elimination_path': 'Phase 6h W4 (Gate Z.4 NEGATIVE / inactive): rigorous only in 2D; 4D needs Catterall mirror decoupling.',
        'source': 'Phase 6h hypercharge-splitting path (asymptotic-safety).', 'risk': 'Phase 6h inactive; tracked bundle.',
        'circularity_note': 'None.', 'prose': 'Discharge-future bundle for the (inactive) Phase-6h light-quark-hierarchy extension.',
    },
    'H_VestigialRelicCarriesZ16Charge': {
        'statement': 'The vestigial relic carries the ℤ₁₆ anomaly-cancellation charge +3 required by the SM deformation class (existence anomaly-forced).',
        'status': 'active', 'tier': 'discharge_future', 'eliminability': 'hard',
        'module': 'DarkSectorSynthesis',
        'source': 'Wave 8 dark-sector synthesis; SM ℤ₁₆ deformation class.', 'risk': 'Not a Lean theorem; tracked dark-sector hypothesis.',
        'circularity_note': 'None.', 'prose': 'Tracked dark-sector Prop: the relic-carries-ℤ₁₆-charge claim that anomaly-forces the vestigial relic.',
    },
    'H_MixedChannelZ16Cancels': {
        'statement': 'Wan–Wang ℤ₁₆ ⊕ ℤ₄ joint-charge cancellation of a mixed-charge hidden sector (parameterized by a ℤ₁₆ indexing φ; SM +13 ≡ −3 mod 16).',
        'status': 'active', 'tier': 'external_boundary', 'eliminability': 'hard',
        'module': 'HiddenSectorMixedCharge',
        'source': 'Wan–Wang ℤ₁₆ classification.', 'risk': 'Tracked anomaly-cancellation hypothesis; parallel to the CenterFunctor center-functor Props.',
        'circularity_note': 'None.', 'prose': 'Mixed-charge hidden-sector anomaly cancellation under the Wan-Wang ℤ₁₆⊕ℤ₄ scheme.',
    },
    'H_MR_FromADWSubstrate_BCS_LNV': {
        'statement': 'The BCS-exponential M_R form derived from the projected Majorana-channel NJL gap equation, conditional on H_LeptonNumberViolated G_LV (G_LV=0 ⟹ G_M≡0).',
        'status': 'active', 'tier': 'discharge_future', 'eliminability': 'hard',
        'module': 'MajoranaRung',
        'source': 'WAVE2-OPEN-1b; projected Majorana-channel NJL gap equation.', 'risk': 'Conditional on explicit substrate-L violation; tracked.',
        'circularity_note': 'None.', 'prose': 'BCS M_R form for the Majorana rung, gated on lepton-number violation.',
    },
    'H_MR_FromSMGGap': {
        'statement': 'The per-generation Majorana mass M_R i arises from the substrate SMG gap scale via M_R i = c_i · Λ_SMG for c_i ∈ (0,1] (no lepton-number-violation precondition).',
        'status': 'active', 'tier': 'discharge_future', 'eliminability': 'hard',
        'module': 'MajoranaRungSMG',
        'source': 'WAVE4-OPEN-2; substrate SMG gap.', 'risk': 'Tracked seesaw-scale hypothesis.',
        'circularity_note': 'None.', 'prose': 'M_R from the SMG gap scale; the unconditional companion to H_MR_FromADWSubstrate_BCS_LNV.',
    },
    'H_SubstrateNearSMGFixedPoint': {
        'statement': 'The substrate parameters sit in the seesaw-restricted SMG window AND Λ_SMG = c_SMG·Λ_UV with c_SMG ∈ [10⁻¹⁰, 10⁻⁴] (NJL-derived band).',
        'status': 'active', 'tier': 'discharge_future', 'eliminability': 'hard',
        'module': 'MajoranaRungSMG',
        'source': 'WAVE4-OPEN-1; NJL seesaw-restricted band.', 'risk': 'Tracked window hypothesis.',
        'circularity_note': 'None.', 'prose': 'Substrate-near-SMG-fixed-point window for the Majorana-rung seesaw.',
    },
    'H_DecouplingBoundDim6': {
        'statement': 'The amplitude-difference amp_diff(E) between Embedding III (substrate-bound ν_R) and Embedding I (fundamental ν_R) is bounded above by the natural Wilson coefficient × (E/Λ_ADW)² at every energy.',
        'status': 'active', 'tier': 'local', 'eliminability': 'hard',
        'module': 'MajoranaRungDecoupling',
        'source': 'WAVE2-OPEN-5b (k=2, generic dim-6) EFT decoupling.', 'risk': 'Tracked EFT-decoupling bound.',
        'circularity_note': 'None.', 'prose': 'Dim-6 decoupling bound between the two ν_R embeddings.',
    },
    'H_BilocalPointlikeLimit': {
        'statement': 'In the pointlike limit ϕ(0)→ϕ(∞) (dilution→1) the bilocal field reduces to the pointlike SM Higgs doublet; the non-trivial content is bilocalDilution b = 1.',
        'status': 'active', 'tier': 'local', 'eliminability': 'hard',
        'module': 'BHLGaugeEmbedding',
        'source': 'BHL minimal embedding (bilocal → pointlike).', 'risk': 'Non-trivial quantitative claim (any spread bilocal field has dilution<1).',
        'circularity_note': 'None.', 'prose': 'Pointlike-limit reduction of the bilocal BHL field to the SM Higgs doublet.',
    },
    'H_HSCovariantBosonisation': {
        'statement': 'Hubbard–Stratonovich bosonisation of the BHL 4-fermion operator yields an auxiliary field gauge-covariant under SU(2)_L×U(1)_Y with hypercharge +1/2.',
        'status': 'active', 'tier': 'local', 'eliminability': 'hard',
        'module': 'BHLGaugeEmbedding',
        'source': 'BHL gauge embedding; HS bosonisation.', 'risk': 'Non-trivial (hypercharge could be 0 or +1).',
        'circularity_note': 'None.', 'prose': 'Gauge-covariance + hypercharge of the HS auxiliary field in the BHL embedding.',
    },
    'IsCurveTheoreticPenroseHypothesis': {
        'statement': 'The 4-conjunct hypothesis bundle (initial_expansion, focal_config, …) for the curve-theoretic Penrose wave-completion composition theorem.',
        'status': 'active', 'tier': 'local', 'eliminability': 'hard',
        'module': 'PenroseSingularityCurveTheoretic',
        'source': 'Curve-theoretic Penrose singularity (wave-completion).', 'risk': 'Bundle of focal-configuration conditions; tracked.',
        'circularity_note': 'None.', 'prose': 'Curve-theoretic Penrose focal-configuration bundle for the singularity-completion theorem.',
    },
    'H_Fib_v4_witness': {
        'statement': 'exp(ℝ•X₁) ⊆ H_Fib for two ℝ-linearly-independent tangents X₁, X₂ — the v4 density witness for the Fibonacci closure subgroup.',
        'status': 'discharged', 'tier': 'headline', 'eliminability': 'hard',
        'module': 'FKLW.CartanSubstrate',
        'discharged_by': 'SKEFTHawking.FKLW.OneParameterSubgroupSU2.H_Fib_v4_witness_unconditional',
        'elimination_path': 'DISCHARGED (2026-07-20, R-07 registry hygiene): proved unconditionally (no hypothesis arguments, sorry-free) by `H_Fib_v4_witness_unconditional` (OneParameterSubgroupSU2.lean §80, verified in lean_deps.json). Retained for provenance; no longer an open frontier apex.',
        'source': 'FKLW Fibonacci density (Cartan substrate).', 'risk': 'Was headline-gating; DISCHARGED by an unconditional producer.',
        'circularity_note': 'None.', 'prose': 'Fibonacci-density v4 witness — DISCHARGED by H_Fib_v4_witness_unconditional; the Fibonacci universality headline rode on the H_Fib density witnesses, now unconditional.',
    },
    'H_Fib_NonCentralConjugateWitness': {
        'statement': 'There exist (g₁,g₂) ∈ H_Fib × H_Fib with g₁ not commuting with its g₂-conjugate (non-central-conjugate antecedent for the Fibonacci density argument).',
        'status': 'discharged', 'tier': 'headline', 'eliminability': 'hard',
        'module': 'FKLW.CartanSubstrate',
        'discharged_by': 'SKEFTHawking.FKLW.H_Fib_NonCentralConjugateWitness_discharged',
        'elimination_path': 'DISCHARGED (2026-07-20, R-07 registry hygiene): proved unconditionally (sorry-free) by `H_Fib_NonCentralConjugateWitness_discharged` (CartanSubstrate.lean §4.9, verified in lean_deps.json). Retained for provenance; no longer an open frontier apex.',
        'source': 'FKLW Fibonacci density.', 'risk': 'Was headline-gating; DISCHARGED by an unconditional producer.',
        'circularity_note': 'None.', 'prose': 'Non-central-conjugate witness — DISCHARGED by H_Fib_NonCentralConjugateWitness_discharged; fed the Fibonacci density argument.',
    },
    'H_Fib_TwoLITangents': {
        'statement': 'Two ℝ-linearly-independent tangent directions exist in the Lie algebra of H_Fib (companion antecedent for the Fibonacci density v4 witness).',
        'status': 'discharged', 'tier': 'headline', 'eliminability': 'hard',
        'module': 'FKLW.CartanSubstrate',
        'discharged_by': 'SKEFTHawking.FKLW.OneParameterSubgroupSU2.H_Fib_TwoLITangents_unconditional',
        'elimination_path': 'DISCHARGED (2026-07-20, R-07 registry hygiene): proved unconditionally (sorry-free) by `H_Fib_TwoLITangents_unconditional` (OneParameterSubgroupSU2.lean §78, verified in lean_deps.json). Retained for provenance; no longer an open frontier apex.',
        'source': 'FKLW Fibonacci density.', 'risk': 'Was headline-gating; DISCHARGED by an unconditional producer.',
        'circularity_note': 'None.', 'prose': 'Two-LI-tangents witness — DISCHARGED by H_Fib_TwoLITangents_unconditional; fed the Fibonacci density argument.',
    },
    'H_CFZ2_sq_e': {
        'statement': 'The halfBraiding double-swap (hexagon-derived β≫β_can≫β≫desc = ρ) identity at the (eAdd, aAdd, aAdd) index triple of the Z/2 Drinfeld-center functor.',
        'status': 'active', 'tier': 'local', 'eliminability': 'hard',
        'module': 'CenterFunctorZ2Equiv',
        'source': 'Phase 5s Wave 9 Option A (2026-04-20); hexagon identity for Z(Vec_{ℤ/2}).',
        'risk': 'Local algebraic hexagon identity. RESOLVED (ADR-004 W7 review, 2026-06-13): gates ONLY the deferred categorical functor `CenterFunctorZ2Equiv.canonicalCenterToRep` (proven Faithful; full Equivalence explicitly DEFERRED, zero downstream consumers). paper7 cites `CenterEquivalenceZ2.full_correspondence` — the unconditional finite object/fusion/braiding correspondence of the 4 simples — NOT this functor; so the W1 "Z/2 fully verified" framing is sound and no paper claim rides on H_CFZ2.',
        'circularity_note': 'None.', 'prose': 'Local hexagon double-swap identity (eAdd summand) for the deferred Z/2 Drinfeld-center categorical functor (no downstream paper consumer).',
    },
    'H_CFZ2_sq_a': {
        'statement': 'Mirror of H_CFZ2_sq_e at the (aAdd, aAdd, aAdd) index triple (hexagon double-swap identity for the Z/2 Drinfeld-center functor).',
        'status': 'active', 'tier': 'local', 'eliminability': 'hard',
        'module': 'CenterFunctorZ2Equiv',
        'source': 'Phase 5s Wave 9 Option A (2026-04-20).',
        'risk': 'Local algebraic hexagon identity. RESOLVED — same as H_CFZ2_sq_e: gates only the deferred categorical functor (zero downstream); paper7 cites the unconditional `full_correspondence`, not this. W1 "Z/2 fully verified" framing sound.',
        'circularity_note': 'None.', 'prose': 'Local hexagon double-swap identity (aAdd summand) for the deferred Z/2 Drinfeld-center categorical functor (no downstream paper consumer).',
    },
    'intFundamentalClass_eval_datum': {
        'statement': 'For a closed oriented charted 4-manifold M, the integral fundamental class [M] ∈ H₄(M;ℤ) '
            'is carried (Phase 5q.H · E1) as the ℤ-linear evaluation functional it induces on top-degree integral '
            'cohomology: the single field `eval : Cohomology X 4 →ₗ[ℤ] ℤ` of the structure '
            'SKEFTHawking.SingularCohomologyInt.IntFundamentalClass, i.e. the integral Kronecker pairing ⟨·,[M]⟩.',
        'status': 'proven (5q.H arm-2, 2026-07-12: DISCHARGED at every consumed instance by SingularHomologyInt.intFundamentalClassOfHomology — eval := (kroneckerHInt 4).flip [M], kernel-pure — and its orientation form intFundamentalClassOfIntOrientation; the abstract IntFundamentalClass structure remains as the interface, its eval field no longer a free posit)', 'tier': 'discharge_future', 'eliminability': 'very_hard',
        'module': 'SingularIntersectionFormInt',
        'elimination_path': 'Discharge = build integral singular homology H₄(M;ℤ) (the on-main homology + Kronecker '
            'tower is entirely over ZMod 2 — SingularHomologyMod2/kroneckerH), the orientation-dependent fundamental '
            'class [M] ∈ H₄(M;ℤ) (the new ℤ ingredient the mod-2 blueprint SingularFundamentalClass does NOT need — '
            'every closed manifold is ℤ/2-orientable), and the integral cohomology↔homology Kronecker pairing '
            'kroneckerHInt; then instantiate eval := (kroneckerHInt 4).flip [M], exactly mirroring the mod-2 '
            'PoincareDualityConstruct.fundamentalFunctional = kroneckerH.flip fundamentalClass. Community-scale '
            '(integral homology + orientation are absent from Mathlib and on-main); tracked here so the intersection '
            'form itself (interFormInt + interFormInt_symm, kernel-pure) has exactly ONE unproved input.',
        'dependent_theorems': [
            'SKEFTHawking.SingularCohomologyInt.interFormInt',
            'SKEFTHawking.SingularCohomologyInt.interFormInt_symm',
        ],
        'source': 'Standard algebraic topology (Milnor–Stasheff; Hatcher §3.3): the fundamental class of a closed '
            'oriented n-manifold + the Kronecker (evaluation) pairing Hⁿ(M;ℤ) × Hₙ(M;ℤ) → ℤ.',
        'risk': 'Very low mathematically (textbook); the cost is purely the from-scratch Lean construction of '
            'integral homology + orientation, deferred to a later E1 brick. The FORM assembled here is unconditional '
            'on `eval`.',
        'circularity_note': 'None. The intersection form and its symmetry are proved for an ARBITRARY functional '
            'eval : H⁴ →ₗ[ℤ] ℤ; no property of the (future) geometric [M] is assumed, so wiring the real [M] later '
            'strictly discharges this datum without touching the form.',
        'prose': 'The integral fundamental class [M] ∈ H₄(M;ℤ) of a closed oriented 4-manifold, carried as its '
            'induced evaluation functional ⟨·,[M]⟩ so the H⁴-valued integral cup product cupH24 descends to the '
            'ℤ-valued symmetric intersection form (Phase 5q.H · E1 Substrate-G; pre-matrix, orientation deferred).',
    },
    'intOrientation_datum': {
        'statement': 'For a closed charted 4-manifold M ([T2Space][CompactSpace][Nonempty][ChartedSpace '
            '(EuclideanSpace ℝ (Fin 4))]), the ORIENTATION-dependent input to the integral fundamental class is '
            'carried (Phase 5q.H · E1 Substrate-G) as the disclosed structure '
            'SKEFTHawking.SingularHomologyInt.IntOrientation M, holding (i) fundClass : Homology (TopCat.of M) 4 = '
            'the integral fundamental class [M] ∈ H₄(M;ℤ) produced by a coherent orientation of M, and (ii) '
            'redCompat : redHomology (TopCat.of M) 4 fundClass = SingularFundamentalClass.fundamentalClass (m:=2) — '
            'the mod-2 compatibility tying [M] to the ON-MAIN orientation-free mod-2 fundamental class [M]₂ via the '
            'ℤ→ℤ/2 reduction redHomology. This SHARPENS intFundamentalClass_eval_datum: the whole evaluation '
            'functional is now discharged from this single geometric datum (intFundamentalClassOfIntOrientation), '
            'and fundClass is not a free H₄ element — its mod-2 shadow must be the canonical [M]₂ (non-vacuous).',
        'status': 'active (HONEST geometric input — orientability. Constructor chain in-tree, kernel-pure: intOrientationDataOfOrientation (brick 18h; from a ±1 section + per-ball hasOrientedFundClassInt orientability input hballs, [PreconnectedSpace M]) → IntOrientationData → intOrientationOfData → IntOrientation; consumed at class level by SixteenDvdOfOrientation.sixteen_dvd_latticeSig_of_orientationData, arm-2 brick 10)', 'tier': 'discharge_future', 'eliminability': 'very_hard',
        'module': 'IntFundamentalClassOrientation',
        'elimination_path': 'Discharge = build integral relative/local singular homology RelativeHomologyInt Kᶜ n '
            'with the local iso H₄(M|x;ℤ) ≅ ℤ (the ℤ upgrade of the on-main mod-2 SingularRelativeHomologyMod2 / '
            'manifoldLocalIso, absent from Mathlib AND on-main — the on-main tower is entirely over ZMod 2), define '
            'restrictsToGeneratorInt/hasFundClassInt with a COHERENT choice of the ±1 local generators (= an '
            'orientation: the orientation local system trivial + a global section), and replay the on-main existence '
            'induction hasFundClass_chartBall/_union/_biUnion/_univ where the union step '
            '(SingularFundamentalClassExist.hasFundClass_union) now matches the two local ±1 generators via the '
            'orientation instead of the ℤ/2 collapse x+x=0 (ZModModule.add_self); extract fundClass. redCompat then '
            'holds by naturality of the ℤ→ℤ/2 reduction (redChain/redChain_chainBoundary/redHomology, PROVED '
            'unconditionally here) on the local-generator condition. Community-scale (integral homology + '
            'orientation absent from Mathlib and on-main); tracked here so intFundamentalClassOfIntOrientation and '
            'the whole intersection form hold for an ARBITRARY such datum, isolating orientation as this one input.',
        'dependent_theorems': [
            'SKEFTHawking.SingularHomologyInt.intFundamentalClassOfIntOrientation',
            'SKEFTHawking.SingularHomologyInt.intFundamentalClassOfIntOrientation_eval',
            'SKEFTHawking.SingularHomologyInt.intOrientation_redHomology_fundClass',
        ],
        'source': 'Standard algebraic topology (Milnor–Stasheff §11; Hatcher §3.3 Thm 3.26/3.27): a closed '
            'connected n-manifold has H_n(M;ℤ) ≅ ℤ iff it is orientable, and an orientation is a coherent choice of '
            'local generators of H_n(M, M∖x; ℤ) ≅ ℤ; its mod-2 reduction is the (always-existing) mod-2 fundamental '
            'class. The ℤ→ℤ/2 reduction on chains/homology (redChain/redHomology) is the dual of the on-main '
            'cochain reduction bridge IntersectionFormEvenInt.redC/redH.',
        'risk': 'Very low mathematically (textbook orientation theory); the cost is purely the from-scratch Lean '
            'construction of integral relative/local homology + the coherent-generator gluing, deferred to a later '
            'E1 brick. Everything downstream of the datum (the intersection form, its symmetry) is unconditional on '
            'fundClass; the redCompat field makes the datum non-vacuous (falsifiable against the mod-2 [M]₂).',
        'circularity_note': 'None. intFundamentalClassOfIntOrientation and the intersection form are built for an '
            'ARBITRARY IntOrientation; no property of a specific (future) geometric [M] is used beyond the disclosed '
            'redCompat. The ℤ→ℤ/2 comparison map redHomology and its chain-map property redChain_chainBoundary are '
            'proved UNCONDITIONALLY (kernel-pure), so wiring the real orientation later strictly discharges this '
            'datum. Refines (does not duplicate) intFundamentalClass_eval_datum: that carried the whole eval '
            'functional; this reduces it further to [M] : H₄(M;ℤ) + orientation coherence, the genuine residual.',
        'prose': 'The orientation of a closed 4-manifold, carried as a disclosed datum (the integral fundamental '
            'class [M] ∈ H₄(M;ℤ) + its mod-2 compatibility with the on-main orientation-free [M]₂) so the integral '
            'intersection form is discharged from this single geometric input — the genuine new content over the '
            'mod-2 blueprint (Phase 5q.H · E1 Substrate-G; the orientation coherence Mathlib/on-main lack).',
    },
    'intLocalHomologyIso_datum': {
        'statement': 'For a topological space M and a point x : M, the integral LOCAL homology iso '
            'H₄(M, M∖x; ℤ) ≅ ℤ is carried (Phase 5q.H · E1 Substrate-G) as the disclosed structure '
            'SKEFTHawking.SingularRelHomologyInt.IntLocalHomologyIso M x, holding (i) iso : '
            'RelHomologyInt (localSub x) 4 ≃+ ℤ (the integral local group ≅ ℤ, two generators ±1), (ii) '
            'isoMod2 : the ON-MAIN mod-2 local group SingularRelativeHomologyMod2.RelativeHomology (localSub x) 4 '
            '≃+ ZMod 2 (the shadow), and (iii) redCompat : ∀ z, isoMod2 (redRelHomology (localSub x) 4 z) = '
            '((iso z : ℤ) : ZMod 2) — the mod-2 compatibility tying the integral iso to the on-main mod-2 local '
            'group via the (PROVED here, kernel-pure) ℤ→ℤ/2 relative-homology reduction bridge redRelHomology. This '
            'is the SHARED prerequisite for BOTH remaining E1 geometric cores: (A) orientation coherence '
            '(the two ±1 local generators force the coherent global sign-section that intOrientation_datum records '
            'as [M]), and (B) the PD local-global cap-iso (the local Euclidean model). Around it this brick BUILDS '
            'the full integral relative-homology / pair-LES substrate (RelHomologyInt = ker∂/im∂ over ℤ, the pair '
            'map homProjInt : Hₙ(X;ℤ) → RelHomologyInt, the connecting δ = connectingInt, the complex property '
            'δ∘j_* = 0, and redRelHomology) — the ℤ mirror of on-main SingularRelativeHomologyMod2 / SingularPairLES, '
            'ALL kernel-pure and unconditional; only the ℤ-generator identification of the local group is disclosed.',
        'status': 'proven (5q.H E1 brick 17b — hypothesis-free at charted 4-manifolds: SingularReducedGeneratorInt.intLocalHomologyIso_of_manifold\' constructs the full 3-field datum (iso/isoMod2/redCompat), kernel-pure; the one residual ReducedGeneratorNonzero is discharged by reducedGeneratorNonzero via chartLocalIso_generator_reduces_ne_zero. Re-marked 2026-07-12 arm-2 after the atlas kept ranking it open)', 'tier': 'discharge_future', 'eliminability': 'very_hard',
        'module': 'SingularRelHomologyInt',
        'elimination_path': 'Discharge = the ℤ local reduction tower H₄(ℝ⁴,ℝ⁴∖0;ℤ) ≅ H₃(ℝ⁴∖0;ℤ) ≅ H₃(S³;ℤ) ≅ ℤ. '
            'The pair-LES connecting-iso step is provable from the integral pair LES built here (homProjInt / '
            'connectingInt / the exactness lemmas, mirroring SingularLocalHomology.connecting_bijective_of_acyclic) '
            'ONCE two from-scratch integral inputs land: (1) integral Euclidean acyclicity Hₖ(ℝⁿ;ℤ)=0 for k≥1 (the '
            'ℤ upgrade of on-main SingularEuclideanAcyclic, ZMod 2 only), and (2) integral sphere homology '
            'H₃(S³;ℤ) ≅ ℤ (the ℤ upgrade of on-main SphereHomology, ZMod 2 only) + the punctured retract ℝ⁴∖0 ≃ S³ '
            '(SingularPuncturedRetract, coefficient-independent). redCompat then holds by naturality of redRelHomology '
            '(PROVED unconditionally here) over the mod-2 tower (SingularLocalHomology.connecting_eucl_bijective). '
            'Community-scale (integral Euclidean acyclicity + integral sphere homology absent from Mathlib AND on-main '
            '— the on-main homology tower is entirely over ZMod 2); tracked so both E1 cores hold for an ARBITRARY '
            'such datum, isolating the ℤ local-generator identification as this one shared geometric input.',
        'dependent_theorems': [
            'SKEFTHawking.SingularRelHomologyInt.intLocalHomologyIso_redCompat',
            'SKEFTHawking.SingularRelHomologyInt.localGenerator',
            'SKEFTHawking.SingularRelHomologyInt.iso_localGenerator',
            'SKEFTHawking.SingularRelHomologyInt.homProjInt',
            'SKEFTHawking.SingularRelHomologyInt.connectingInt',
            'SKEFTHawking.SingularRelHomologyInt.connectingInt_homProjInt',
            'SKEFTHawking.SingularRelHomologyInt.redRelHomology',
        ],
        'source': 'Standard algebraic topology (Hatcher §2.2/§3.3, Milnor–Stasheff §11): the local homology '
            'Hₙ(M, M∖x; ℤ) ≅ ℤ of an n-manifold, computed via the LES of the pair (ℝⁿ, ℝⁿ∖0) with ℝⁿ acyclic + the '
            'retract ℝⁿ∖0 ≃ Sⁿ⁻¹ + Hₙ₋₁(Sⁿ⁻¹;ℤ) ≅ ℤ; its two generators ±1 are the local orientations, whose mod-2 '
            'reduction is the (always-existing) unique mod-2 local generator. The ℤ→ℤ/2 relative reduction bridge '
            'redRelChain/redRelHomology is the relative dual of the absolute redChain/redHomology (brick 11).',
        'risk': 'Very low mathematically (textbook local homology); the cost is purely the from-scratch Lean '
            'construction of integral Euclidean acyclicity + integral sphere homology, deferred to a later E1 brick. '
            'Everything else in the brick (the integral relative homology, the pair maps homProjInt/connectingInt, '
            'the complex property, the reduction bridge redRelHomology) is UNCONDITIONAL and kernel-pure; only the '
            'ℤ-generator identification of the local group is disclosed, and redCompat makes it non-vacuous '
            '(falsifiable against the on-main mod-2 local generator).',
        'circularity_note': 'None. The integral relative homology, the pair LES core, and the reduction bridge are '
            'built UNCONDITIONALLY (kernel-pure); IntLocalHomologyIso and localGenerator/iso_localGenerator are stated '
            'for an ARBITRARY supplied datum, no property of a specific (future) geometric local iso is used beyond '
            'the disclosed redCompat. redRelHomology and its chain-map property redRelChain_relBoundary are proved '
            'unconditionally, so wiring the real local iso later strictly discharges this datum. This is the shared '
            'discharge-substrate for intOrientation_datum (A) and the PD local-global cap-iso (B) — it does not '
            'duplicate them, it isolates the ONE geometric input both share.',
        'prose': 'The integral local homology iso H₄(M, M∖x; ℤ) ≅ ℤ of a 4-manifold at a point, carried as a '
            'disclosed datum (the local iso + its mod-2 compatibility with the on-main mod-2 local group via the '
            'reduction bridge) so that BOTH remaining E1 cores — orientation coherence and the PD local-global '
            'cap-iso — are discharged from this single shared geometric input. Around it the full integral '
            'relative-homology / pair-LES substrate (RelHomologyInt, homProjInt, connectingInt, δ∘j_*=0, '
            'redRelHomology) is built unconditionally and kernel-pure — the ℤ mirror of the on-main mod-2 blueprint '
            '(Phase 5q.H · E1 Substrate-G; the integral local-homology tower Mathlib/on-main lack).',
    },
    'intH2_basis_datum': {
        'statement': 'For a closed 4-manifold M, a finite free ℤ-basis of H²(M;ℤ) = Cohomology (TopCat.of M) 2 '
            'is carried (Phase 5q.H · E1 Substrate-G) as a disclosed datum: the structure '
            'SKEFTHawking.SingularCohomologyInt.IntH2Basis, holding a rank `n : ℕ` (= the free rank b₂(M)) and a '
            'field `basis : Module.Basis (Fin n) ℤ (Cohomology X 2)`. This is the finite-free-basis input that turns '
            'the ℤ-bilinear intersection form interFormInt into its Gram MATRIX interMatrix : Matrix (Fin n) (Fin n) ℤ.',
        'status': 'active', 'tier': 'discharge_future', 'eliminability': 'very_hard',
        'module': 'IntersectionMatrixInt',
        'elimination_path': 'SHARPENED 2026-07-12 (arm-2, scout-verified vs FNOP arXiv:1910.07372 + Blass–Göbel '
            'math/9405206): the ℤ-analog of the mod-2 Erdős–Kaplansky self-duality forcing is PROVABLY BLOCKED '
            '(Specker: (⊕ℤ)⊕ℤ^ℕ is self-dual, not f.g.) — SETTLED_FORKS § 5qH-fg-ek-over-Z-blocked. Minimal '
            'published general-M route = Borsuk-ENR retract-of-finite-CW (FNOP Cor 3.18; community-scale; CW '
            'existence for compact TOP 4-manifolds is OPEN, FNOP Q3.15; smooth case = Morse, Mathlib-absent). '
            'PROJECT PATH: witness-level data — explicit finite free bases for the concrete carrier manifolds '
            '(ℝP⁴ chain etc.), + free-quotient descent where torsion appears. All results here hold for an '
            'ARBITRARY basis, isolating the free-module input as this one datum.',
        'dependent_theorems': [
            'SKEFTHawking.SingularCohomologyInt.interMatrix',
            'SKEFTHawking.SingularCohomologyInt.interMatrix_isSymm',
            'SKEFTHawking.SingularCohomologyInt.interMatrix_transpose',
            'SKEFTHawking.SingularCohomologyInt.interMatrix_isSymmetricInt',
            'SKEFTHawking.SingularCohomologyInt.eight_dvd_manifold_sig',
            'SKEFTHawking.SingularCohomologyInt.sixteen_dvd_manifold_sig',
        ],
        'source': 'Standard algebraic topology (Hatcher §2.2/§3.1; Milnor–Stasheff): the integral cohomology of a '
            'closed manifold is finitely generated (finite CW structure), and over the PID ℤ a finitely-generated '
            'module splits as free ⊕ torsion, so its free part has a finite basis.',
        'risk': 'Very low mathematically (textbook finite-generation + PID structure theorem); the cost is purely the '
            'from-scratch Lean construction of finite integral cohomology, deferred to a later E1 brick. The MATRIX, '
            'its symmetry, and the σ÷16 composition assembled here are unconditional on the choice of basis.',
        'circularity_note': 'None. interMatrix and all its downstream results are built for an ARBITRARY '
            'IntH2Basis; no property of a specific (future) geometric basis is assumed. The genuinely-geometric '
            'inputs to the σ÷16 headline (IsEvenUnimodular interMatrix = even/Wu + unimodular/PD, and the topological '
            'factor 2∣σ/8 = Guillou–Marin) are left explicitly as hypotheses, NOT folded into this datum.',
        'prose': 'A finite free ℤ-basis of H²(M;ℤ) for a closed 4-manifold, carried as a disclosed datum so the '
            'symmetric ℤ-bilinear intersection form interFormInt descends to its integer Gram matrix interMatrix — '
            'the concrete arithmetic object the DONE lattice σ÷16 theorem consumes (Phase 5q.H · E1 Substrate-G; the '
            'final structural link integral-cohomology → cup → form → matrix → σ÷16).',
    },
    'spinWu_even_datum': {
        'statement': 'For a closed ORIENTED Spin 4-manifold M, the mod-2 Wu / Spin input to the EVENNESS of the '
            'integer intersection matrix is carried (Phase 5q.H · E1 Substrate-G) as a disclosed datum: the structure '
            'SKEFTHawking.SingularCohomologyInt.SpinWuDatum fc (tied to the integral fundamental class '
            'fc : IntFundamentalClass X), holding (i) mu2 : Cohomology X 4 (ℤ/2) →ₗ[ZMod 2] ZMod 2 = the mod-2 '
            'fundamental-class functional ⟨·,[M]₂⟩; (ii) eval_compat: ((fc.eval ω : ℤ) : ZMod 2) = mu2 (redH X 4 ω), '
            'the ℤ→ℤ/2 compatibility of the two evaluations through the reduction bridge redH; (iii) wu_vanish: '
            '∀ y : Cohomology X 2 (ℤ/2), mu2 (cupH24 y y) = 0 — the SPIN condition in functional form (⟨Sq² y,[M]₂⟩ = 0 '
            'for all y, which by the singular Wu relation is v₂ = 0; on an oriented 4-manifold v₁ = 0 so w₂ = v₂, hence '
            'v₂ = 0 ⟺ w₂ = 0 ⟺ M is Spin). This is the ONLY unproved input to interMatrix EVENNESS.',
        'status': 'proven (5q.H arm-2 brick 9, 2026-07-12: DISCHARGED at general closed oriented spin 4-manifolds — SpinWuDatumClosed.spinWuDatum_of_closed constructs the full datum from the two HONEST inputs (o : IntOrientation M, spin as wuClass2 poincareDual4Mid_of_closed = 0); mu2/PD frame = SingularPD4Instances (5q.G X6), eval_compat = KroneckerRedCompat + o.redCompat, wu_vanish DERIVED via the Wu relation (SpinWuFromPD). interMatrix evenness at general M: SpinWuDatumClosed.interMatrix_even_of_closed)', 'tier': 'discharge_future', 'eliminability': 'hard',
        'module': 'IntersectionFormEvenInt',
        'elimination_path': 'Discharge = build the ℤ/2 fundamental class + middle Poincaré-duality datum '
            'PoincareDual4Mid of the closed manifold (mod-2 orientability is automatic), take mu2 := P.mu, prove '
            'eval_compat from the fact that the integral and mod-2 fundamental classes agree under reduction, and derive '
            'wu_vanish from w₂(TM) = 0 (Spin) together with v₁ = 0 (oriented ⟹ w₁ = 0 ⟹ v₁ = 0) and the singular Wu '
            'relation ⟨v₂ ∪ y,[M]₂⟩ = ⟨Sq² y,[M]₂⟩ (PoincareDualityWu.wu_relation). The reduction bridge redH and its '
            'cup/coboundary compatibility (redH_cupH24, redC_coboundary, redC_cup) are PROVED unconditionally — the '
            'ℤ→ℤ/2 reduction of SingularCohomologyInt matches the on-main SingularCohomologyMod2 model definitionally '
            '(same functions on singular simplices; alternating signs (-1)^i reduce to 1 in char 2), so the bridge '
            'itself is NOT a hypothesis. Only the geometric Spin/PD datum is disclosed.',
        'dependent_theorems': [
            'SKEFTHawking.SingularCohomologyInt.interFormInt_diag_even',
            'SKEFTHawking.SingularCohomologyInt.interMatrix_even_of_spinWu',
            'SKEFTHawking.SingularCohomologyInt.isEvenUnimodular_of_unimodular',
        ],
        'source': 'Standard 4-manifold topology (Wu formula w = Sq(v); Milnor–Stasheff §11; Kirby–Taylor): the '
            'intersection form of a Spin (equivalently w₂ = 0) 4-manifold is EVEN, because ⟨a∪a,[M]₂⟩ = ⟨Sq²(a),[M]₂⟩ '
            '= ⟨v₂∪a,[M]₂⟩ = 0 when v₂ = 0. On-main singular Wu substrate: PoincareDualityWu / PoincareDualityWuFormula '
            '(wuClass2, wu_relation, wuW2_eq_zero_iff).',
        'risk': 'Low mathematically (textbook: Spin ⟹ even intersection form); cost is the from-scratch Lean '
            'construction of the ℤ/2 fundamental class + PD datum + the w₂=0 ⟹ v₂=0 derivation, deferred to a later '
            'E1 brick. Every result in IntersectionFormEvenInt holds for an ARBITRARY such datum.',
        'circularity_note': 'None. The evenness lemmas are built for an ARBITRARY SpinWuDatum; no property of a '
            'specific (future) geometric fundamental class is assumed. The reduction bridge redH — the connective '
            'tissue to the mod-2 Wu side — is proved unconditionally (not part of this datum). The residual '
            'unimodular/Poincaré-duality conjunct of IsEvenUnimodular is left explicitly as a SEPARATE hypothesis '
            '(isEvenUnimodular_of_unimodular takes IsUnimodular as its remaining argument), NOT folded in here.',
        'prose': 'The Spin/Wu evenness input for a closed oriented 4-manifold, carried as a disclosed datum (mod-2 '
            'fundamental functional + ℤ→ℤ/2 compatibility + the Spin condition v₂=0 as a Wu-functional vanishing) so '
            'the integer intersection matrix interMatrix is EVEN — discharging the last semi-mirror-able conjunct of '
            'IsEvenUnimodular through the from-scratch ℤ→ℤ/2 reduction bridge redH (Phase 5q.H · E1 Substrate-G). '
            'Symmetric ✓ (graded-commutativity) + even ✓ (this datum) leave unimodular/PD as the sole residual core.',
    },
    'intPoincareDuality_perfectPairing_datum': {
        'statement': 'For a closed ORIENTED 4-manifold M, the UNIMODULARITY (det = ±1) of the integer intersection '
            'matrix is carried (Phase 5q.H · E1 Substrate-G) as a disclosed datum: the structure '
            'SKEFTHawking.SingularCohomologyInt.IntPoincareDuality fc (tied to the integral fundamental class '
            'fc : IntFundamentalClass X), holding (i) toDualEquiv : Cohomology X 2 ≃ₗ[ℤ] Module.Dual ℤ (Cohomology X 2) '
            '= the INTEGRAL Poincaré-duality perfect-pairing isomorphism (the curried intersection form '
            'a ↦ ⟨a∪·,[M]⟩ is a linear ISO onto the ℤ-dual; equivalently the integral cap map ·⌢[M] : H²(M;ℤ) → '
            'H₂(M;ℤ) is an iso, H₂ being ℤ-dual to H²); (ii) toDualEquiv_apply: ∀ a b, toDualEquiv a b = '
            'interFormInt fc a b — the compatibility fixing the equivalence to underlie the intersection form. This is '
            'the ONLY unproved input to interMatrix UNIMODULARITY. It is STRICTLY STRONGER than the on-main mod-2 '
            'injective non-degeneracy SingularPD4Instances.nondeg_of_closed (which gives only det ODD, not det = ±1).',
        'status': 'superseded_on_wiring_path (2026-07-12 arm-2: the live σ÷16 wiring is hcoreG_intrinsicInt → openDuality_univ_bij_of_hcoreGInt → capEquivInt → sixteen_dvd_latticeSig_of_capEquiv, and SingularSixteenDvdUnconditionalInt.sixteen_dvd_latticeSigInt consumes NO capIso/intPD datum; this datum remains a valid ALTERNATIVE interface for datum-supplied PD, off the critical path)', 'tier': 'discharge_future', 'eliminability': 'hard',
        'module': 'IntersectionFormUnimodularInt',
        'elimination_path': 'Discharge = build the INTEGRAL homology H₂(M;ℤ) + the integral cap product '
            '·⌢[M] : H²(M;ℤ) → H₂(M;ℤ) + the integral Kronecker pairing kroneckerHInt (the ℤ tower dual to the on-main '
            'SingularHomologyMod2 / kroneckerH), and prove the cap map an ISOMORPHISM (integral Poincaré duality). Then '
            'instantiate toDualEquiv from the composite H²(M;ℤ) ≃ H₂(M;ℤ) ≃ Dual ℤ H²(M;ℤ) and toDualEquiv_apply from '
            'the cap–cup adjunction ⟨a∪b,[M]⟩ = ⟨b, a⌢[M]⟩ (the integral mirror of the on-main '
            'fundamentalFunctional_cupH24 / kronecker_cup_cap). The char-2 shadow of this iso — INJECTIVITY of the '
            'mod-2 form — is ALREADY a theorem on main (nondeg_of_closed, via the capH-injectivity / P₄(univ) Bott–Tu '
            'tower); the integral upgrade (iso, not just injective; det = ±1, not just odd) is the community-scale core.',
        'dependent_theorems': [
            'SKEFTHawking.SingularCohomologyInt.interMatrix_eq_toMatrix_intPD',
            'SKEFTHawking.SingularCohomologyInt.interMatrix_isUnit_det_of_intPD',
            'SKEFTHawking.SingularCohomologyInt.interMatrix_isUnimodular_of_intPD',
            'SKEFTHawking.SingularCohomologyInt.isEvenUnimodular_of_intPD',
            'SKEFTHawking.SingularCohomologyInt.sixteen_dvd_manifold_sig_of_intPD',
        ],
        'source': 'Standard 4-manifold topology (Poincaré duality; Milnor–Stasheff, Hatcher §3.3, Kirby–Taylor): the '
            'intersection form of a closed oriented 4-manifold is a PERFECT pairing on the free part of H²(M;ℤ), i.e. '
            'unimodular (det = ±1). The reduction perfect-pairing ⟹ det-unit uses the Mathlib bridges '
            'LinearEquiv.isUnit_det (a linear equivalence has unit determinant in any basis) + Int.isUnit_iff '
            '(IsUnit n ↔ n = 1 ∨ n = -1 over ℤ) + LinearMap.toMatrix_apply / Module.Basis.dualBasis_repr (the Gram '
            'matrix IS the matrix of the toDual map in the basis/dual-basis pair), all PROVED unconditionally here.',
        'risk': 'Low mathematically (textbook: PD makes the intersection form unimodular); cost is the from-scratch '
            'Lean construction of integral homology H₂(M;ℤ) + the integral cap product + the iso proof, deferred to a '
            'later E1 brick. Every result in IntersectionFormUnimodularInt holds for an ARBITRARY such datum.',
        'circularity_note': 'None. The unimodularity lemmas are built for an ARBITRARY IntPoincareDuality datum; no '
            'property of a specific (future) integral cap iso is assumed. The perfect-pairing ⟹ unit-det reduction '
            '(LinearEquiv.isUnit_det + Int.isUnit_iff + the Gram-matrix identification) is proved unconditionally. The '
            'evenness/Wu conjunct of IsEvenUnimodular is a SEPARATE disclosed datum (SpinWuDatum, spinWu_even_datum); '
            'this datum supplies ONLY unimodular. It is NOT the lattice-Arf route (nogo_lattice_arf_not_sigma8): '
            'unimodularity is a genuine PD fact, orthogonal to the banned σ/8 ≡ Arf congruence.',
        'prose': 'The integral Poincaré-duality perfect-pairing input for a closed oriented 4-manifold, carried as a '
            'disclosed datum (the curried intersection form H²(M;ℤ) → Dual ℤ H²(M;ℤ) is a ℤ-linear iso) so the integer '
            'intersection matrix interMatrix is UNIMODULAR (det = ±1) — discharging the LAST conjunct of IsEvenUnimodular '
            'through LinearEquiv.isUnit_det + Int.isUnit_iff (Phase 5q.H · E1 Substrate-G). This completes the '
            'IsEvenUnimodular analysis: symmetric ✓ (graded-commutativity, proved) + even ✓ (SpinWuDatum) + unimodular ✓ '
            '(this datum) reduce IsEvenUnimodular interMatrix to exactly two clean disclosed geometric data. The integral '
            'iso is STRICTLY stronger than the on-main mod-2 injective nondeg_of_closed (det odd → det = ±1).',
    },
    'intCapIso_datum': {
        'statement': 'For a closed ORIENTED 4-manifold M with integral fundamental class [M] : Homology X 4, the '
            'integral Poincaré duality is carried (Phase 5q.H · E1 Substrate-G, brick 6) as the CLEANER GEOMETRIC datum '
            'SKEFTHawking.SingularCohomologyInt.IntCapIso zM, holding two ISO facts: (i) capEquiv : Cohomology X 2 '
            '≃ₗ[ℤ] Homology X 2 = the integral CAP MAP ·⌢[M] : H²(M;ℤ) → H₂(M;ℤ) is an isomorphism (with capEquiv_apply '
            'fixing its underlying map to capHInt 2 1 · [M]); (ii) kronEquiv : Homology X 2 ≃ₗ[ℤ] Module.Dual ℤ '
            '(Cohomology X 2) = the integral KRONECKER pairing H₂(M;ℤ) → Dual ℤ H²(M;ℤ) is a perfect pairing (with '
            'kronEquiv_apply fixing it to h ↦ ⟨·,h⟩ = kroneckerHInt 2 · h). This SUPERSEDES/refines '
            'intPoincareDuality_perfectPairing_datum: the integral cap product ·⌢[M], the descent to (co)homology '
            'capHInt, the integral Kronecker kroneckerHInt, and the cap–cup adjunction ⟨a∪b,[M]⟩=⟨b,a⌢[M]⟩ are now ALL '
            'BUILT (kernel-pure), so IntPoincareDuality is inhabited from IntCapIso by intPoincareDualityOfCapIso (its '
            'toDualEquiv = capEquiv.trans kronEquiv, toDualEquiv_apply from interFormInt_eq_kroneckerHInt_capHInt). The '
            'residual disclosed input is now PRECISELY the two isos (cap-iso + Kronecker perfect pairing) — the exact '
            'char-0 upgrade of the on-main mod-2 INJECTIVE nondeg_of_closed (mod-2 injectivity of ·⌢[M] → integral iso).',
        'status': 'superseded_on_wiring_path (2026-07-12 arm-2: the live σ÷16 wiring is hcoreG_intrinsicInt → openDuality_univ_bij_of_hcoreGInt → capEquivInt → sixteen_dvd_latticeSig_of_capEquiv, and SingularSixteenDvdUnconditionalInt.sixteen_dvd_latticeSigInt consumes NO capIso/intPD datum; this datum remains a valid ALTERNATIVE interface for datum-supplied PD, off the critical path)', 'tier': 'discharge_future', 'eliminability': 'hard',
        'module': 'IntCapProductInt',
        'elimination_path': 'Discharge (i) the cap-iso: prove capHInt 2 1 · [M] : H²(M;ℤ) → H₂(M;ℤ) is bijective — the '
            'integral upgrade of the on-main mod-2 injective SingularPD4Instances.nondeg_of_closed (the capH-injectivity '
            '/ P₄(univ) Bott–Tu tower), which needs the integral local-global cap-iso theorem (Mayer–Vietoris + the '
            'Euclidean/ball local model over ℤ). Discharge (ii) the Kronecker perfect pairing H₂(M;ℤ) ≃ Dual ℤ H²(M;ℤ): '
            'universal coefficients over ℤ for a finitely-generated free-part (co)homology — the integral UCT '
            '(Ext-term); over a field this is homology_eq_zero_of_kroneckerH (the mod-2 shadow). Both are the '
            'community-scale integral-PD core; everything ELSE (cap, adjunction, descent, the reduction) is now proved.',
        'dependent_theorems': [
            'SKEFTHawking.SingularCohomologyInt.capHInt',
            'SKEFTHawking.SingularCohomologyInt.kroneckerInt_cup_capInt',
            'SKEFTHawking.SingularCohomologyInt.kroneckerHInt_cupH24',
            'SKEFTHawking.SingularCohomologyInt.interFormInt_eq_kroneckerHInt_capHInt',
            'SKEFTHawking.SingularCohomologyInt.intPoincareDualityOfCapIso',
            'SKEFTHawking.SingularCohomologyInt.interMatrix_isUnimodular_of_capIso',
        ],
        'source': 'Standard 4-manifold topology (Poincaré duality via the cap product with the fundamental class; '
            'Hatcher §3.3 Thm 3.30, Milnor–Stasheff): for a closed oriented M, ·⌢[M] : Hᵏ(M;ℤ) → H_{n-k}(M;ℤ) is an '
            'isomorphism, and the Kronecker/UCT pairing identifies H₂ with the ℤ-dual of H² on the free part. The '
            'signed cap-Leibniz ∂(a⌢c)=(-1)ᵏ⁺¹(δa⌢c)+(-1)ᵏ(a⌢∂c) (capInt_leibniz) is the genuine ℤ boundary identity '
            '(the mod-2 file dropped the signs via +1=-1); the cap–cup adjunction ⟨a∪b,c⟩=⟨b,a⌢c⟩ is sign-free.',
        'risk': 'Low mathematically (textbook Poincaré duality); cost is the from-scratch Lean proof of the two isos '
            '(cap-iso + Kronecker perfect pairing), the integral upgrade of the on-main mod-2 injective tower. Every '
            'result here holds for an ARBITRARY IntCapIso datum, so the datum is the ONLY unproved input to '
            'unimodularity via this route.',
        'circularity_note': 'None. intPoincareDualityOfCapIso builds IntPoincareDuality for an ARBITRARY IntCapIso; the '
            'reduction (toDualEquiv = capEquiv.trans kronEquiv, compatibility from the PROVED adjunction '
            'interFormInt_eq_kroneckerHInt_capHInt) assumes no property of a specific future cap-iso. NOT the '
            'lattice-Arf route (nogo_lattice_arf_not_sigma8): the cap-iso is a genuine geometric PD fact, orthogonal to '
            'the banned σ/8 ≡ Arf congruence. This datum REFINES intPoincareDuality_perfectPairing_datum (which remains '
            'valid; this one exposes the cleaner cap-iso decomposition now that the cap tower is built).',
        'prose': 'The integral Poincaré-duality input, sharpened (Phase 5q.H · E1 Substrate-G brick 6) to the CLEANER '
            'geometric datum IntCapIso: the integral cap map ·⌢[M] : H²(M;ℤ) → H₂(M;ℤ) is an iso + the integral '
            'Kronecker H₂ ≃ Dual H² is a perfect pairing. With the integral cap product, its descent to (co)homology '
            '(capHInt), the integral Kronecker, and the cap–cup adjunction now ALL BUILT kernel-pure, '
            'IntPoincareDuality is inhabited from IntCapIso (intPoincareDualityOfCapIso), so the residual reduces to '
            'exactly the two isos — the char-0 upgrade of the on-main mod-2 injective nondeg_of_closed. Feeds the whole '
            'IsEvenUnimodular → σ ÷ 16 leg via interMatrix_isUnimodular_of_capIso.',
    },
    'intCapIsoData_determinant_datum': {
        'statement': 'For a closed ORIENTED 4-manifold M with integral fundamental class [M] : Homology X 4 and a '
            'finite free H²-basis B : IntH2Basis X, the integral Poincaré duality is carried (Phase 5q.H · E1 '
            'Substrate-G, brick 10) as the CONCRETE, CHECKABLE determinant datum '
            'SKEFTHawking.SingularCohomologyInt.IntCapIsoData zM B — the sharpened replacement for IntCapIso\'s two '
            'abstract ≃ₗ fields. It discloses ONLY: (a) h2Basis : Module.Basis (Fin B.rank) ℤ (Homology X 2) — a finite '
            'free basis of H₂(M;ℤ) indexed by the SAME Fin B.rank as the H² basis (the equal-rank index IS the '
            'Poincaré-duality fact b₂(H₂)=b₂(H²); the homology-side analogue of IntH2Basis); (b) capUnit : IsUnit '
            '(det ((toMatrix B.basis h2Basis) (capMapLin zM))) — the integer cap matrix is unimodular; (c) kronUnit : '
            'IsUnit (det ((toMatrix h2Basis B.basis.dualBasis) kronMapLin)) — the integer Kronecker matrix is '
            'unimodular. The MAPS capMapLin := capHInt 2 1 · [M] and kronMapLin := (kroneckerHInt 2).flip are BUILT '
            '(kernel-pure), not disclosed; only their invertibility (as ONE integer determinant unit each, det = ±1 by '
            'Int.isUnit_iff) is disclosed. IntCapIsoData → IntCapIso → IntPoincareDuality via '
            'IntCapIsoData.toIntCapIso (LinearEquiv.ofIsUnitDet on each map) + intPoincareDualityOfCapIso. This is the '
            'exact integer analogue of the H²-side interMatrix datum, strictly sharper than IntCapIso\'s abstract isos.',
        'status': 'superseded_on_wiring_path (2026-07-12 arm-2: the live σ÷16 wiring is hcoreG_intrinsicInt → openDuality_univ_bij_of_hcoreGInt → capEquivInt → sixteen_dvd_latticeSig_of_capEquiv, and SingularSixteenDvdUnconditionalInt.sixteen_dvd_latticeSigInt consumes NO capIso/intPD datum; this datum remains a valid ALTERNATIVE interface for datum-supplied PD, off the critical path)', 'tier': 'discharge_future', 'eliminability': 'hard',
        'module': 'IntPoincareDualityCapIso',
        'elimination_path': 'Discharge (a) h2Basis: build integral singular H₂(M;ℤ), prove it finitely generated, split '
            'off the free part (Module.Free/Module.Finite over the PID ℤ ⟹ a finite basis) — the exact homology-side '
            'mirror of the H² intH2_basis_datum discharge. Discharge (b) capUnit + (c) kronUnit: prove the built maps '
            'capMapLin / kronMapLin have unimodular matrices — the integral local-global cap-iso (Mayer–Vietoris + the '
            'Euclidean/ball local model over ℤ) and the integral UCT perfect pairing (Ext-free free-part), each now a '
            'SINGLE integer-determinant fact rather than an abstract iso. PARTIAL DONE (brick 10): '
            'odd_capMatrix_det_of_mod2_unit derives Odd (det cap matrix) from a unit mod-2 reduction of the cap matrix '
            '(the exact algebraic content of the on-main mod-2 injective nondeg_of_closed in matching rank), via '
            'RingHom.map_det + ZMod 2 being a field — the HONEST floor the mod-2 shadow gives, one parity-step short of '
            'IsUnit det (det odd, e.g. 3, is NOT unimodular). The residual is exactly the parity → unit strengthening.',
        'dependent_theorems': [
            'SKEFTHawking.SingularCohomologyInt.capMapLin',
            'SKEFTHawking.SingularCohomologyInt.kronMapLin',
            'SKEFTHawking.SingularCohomologyInt.IntCapIsoData.toIntCapIso',
            'SKEFTHawking.SingularCohomologyInt.intPoincareDualityOfCapIsoData',
            'SKEFTHawking.SingularCohomologyInt.interMatrix_isUnimodular_of_capIsoData',
            'SKEFTHawking.SingularCohomologyInt.odd_det_of_isUnit_det_map_zmod2',
            'SKEFTHawking.SingularCohomologyInt.odd_capMatrix_det_of_mod2_unit',
        ],
        'source': 'Standard 4-manifold topology (Poincaré duality; Hatcher §3.3 Thm 3.30, Milnor–Stasheff): ·⌢[M] is '
            'an iso and the Kronecker/UCT pairing identifies H₂ with the ℤ-dual of H² on the free part — each an '
            'invertible integer matrix in matched free bases. The reduction map-with-unit-det ⟹ ≃ₗ uses the Mathlib '
            'bridge LinearEquiv.ofIsUnitDet (f with IsUnit ((toMatrix v v\') f).det is a ≃ₗ underlying f, '
            'LinearEquiv.ofIsUnitDet_apply), proved unconditionally here. The mod-2 floor uses RingHom.map_det '
            '(f (det M) = det (f.mapMatrix M)) + Int.two_dvd_ne_zero / ZMod.intCast_zmod_eq_zero_iff_dvd.',
        'risk': 'Low mathematically (textbook PD; each disclosed fact is a single unimodular integer determinant); cost '
            'is the from-scratch Lean construction of integral H₂ + the two iso proofs, now isolated as concrete '
            'determinant units. Every result in IntPoincareDualityCapIso holds for an ARBITRARY IntCapIsoData datum.',
        'circularity_note': 'None. IntCapIsoData.toIntCapIso builds IntCapIso for an ARBITRARY IntCapIsoData; the maps '
            'capMapLin/kronMapLin are BUILT and the reduction (LinearEquiv.ofIsUnitDet + intPoincareDualityOfCapIso) '
            'assumes no property of a specific future datum. The mod-2 partial odd_capMatrix_det_of_mod2_unit is a pure '
            'algebraic implication (unit mod-2 reduction ⟹ odd det), taking its hypothesis as given — it does NOT '
            'assume the conclusion. This datum REFINES intCapIso_datum (which remains valid) by exposing the concrete '
            'determinant decomposition. NOT the lattice-Arf route (nogo_lattice_arf_not_sigma8): a genuine PD fact, '
            'orthogonal to the banned σ/8 ≡ Arf congruence.',
        'prose': 'The integral Poincaré-duality input, sharpened one further step (Phase 5q.H · E1 Substrate-G brick '
            '10) from the abstract IntCapIso to the CONCRETE determinant datum IntCapIsoData: an H₂ free basis + two '
            'unimodular integer determinants (cap matrix, Kronecker matrix) on the BUILT maps capMapLin/kronMapLin, '
            'reduced to IntCapIso via LinearEquiv.ofIsUnitDet. The exact integer analogue of the H²-side interMatrix '
            'datum. The on-main mod-2 injective nondeg_of_closed is captured algebraically by '
            'odd_capMatrix_det_of_mod2_unit (unit mod-2 reduction ⟹ Odd det) — the honest floor, one parity-step short '
            'of the full det = ±1. Feeds IsEvenUnimodular → σ ÷ 16 via interMatrix_isUnimodular_of_capIsoData.',
    },
}

# ════════════════════════════════════════════════════════════════════
# KERNEL NO-GO LEDGER (ADR-007) — the settled-dead complement of HYPOTHESIS_REGISTRY
# ════════════════════════════════════════════════════════════════════
# Machine-readable bridge between the prose SETTLED_FORKS.md register and the
# kernel-checked refutation/forcing theorems that make a provably-false path
# UNprovable. Enforced by `validate.py --check nogo_substrate_integrity` (N-C, Invariant #17)
# and surfaced to the swarm as the atlas NEGATIVE frontier (N-D). SCOPE: provably-false
# (kernel-checkable) no-gos ONLY — policy/route/preference bans stay prose-only in
# SETTLED_FORKS.md (N-B). Each backing theorem must EXIST in lean_deps.json, be KERNEL-PURE
# ({propext, Classical.choice, Quot.sound}), and be NON-vacuous (not True/reflexive).
# Schema: fork_id (→ a SETTLED_FORKS `## ` block or a memory slug), backing_theorems (FQN list),
# nogo_kind (refutation | structural_forcing | counterexample), false_statement (the path it
# kills, one line), memory ([[slug]]).
KERNEL_NOGO_REGISTRY: dict[str, dict] = {
    'nonhausdorff_bordism_collapse': {
        'fork_id': 'nonhausdorff-bordism-collapse',
        'backing_theorems': [
            'SKEFTHawking.NonHausdorffBordismCollapse.bordismGrp_subsingleton',
            'SKEFTHawking.NonHausdorffBordismCollapse.bordismGrp_rp4_eq_zero',
            'SKEFTHawking.NonHausdorffBordismCollapse.dataBordismGMTied_mk_eq_iff_grade16_eq',
        ],
        'nogo_kind': 'refutation',
        'false_statement': "The in-tree `Bordism` relation (BordismGroup.lean:37-42) is a faithful bordism theory usable for a completeness/injectivity/bounding Prop. FALSE: `Bordism.W` is required compact/charted/IsManifold but NOT Hausdorff, so the non-Hausdorff bug-eyed interval B ([0,1] w/ doubled origin, compact + real-analytic + 3 boundary points) makes W = s.M × B an admissible bordism (s⊔s)⊔s → ∅ for EVERY closed s; with the in-tree 2-torsion (3x=0 ∧ 2x=0 ⟹ x=0) BordismGrp X 0 I is the TRIVIAL group ([ℝP⁴]=0, a falsifier — false for genuine unoriented bordism), and DataBordismGrp mk p = mk q ↔ grade16 equal (no geometric content). ⇒ hbound and every DataBordismGrp-quantified Prop (incl. Freeze B `SphereProductBounds := mk = 0`) is VACUOUS. FIX: require `[t2W : T2Space W]` — the honest relation is `T2TangentialBordism.IsT2DataBordant`; real keystone re-anchors to `hboundT2`. NOTE: even T2 at k=0 is TOPOLOGICAL bordism (KS breaks ℤ/16); literature-grade needs the SMOOTH (k=∞) + T2 carrier.",
        'memory': '[[project_5qH_nonhausdorff_substrate_bug]]',
    },
    'comp_twist_doubling_incompatible': {
        'fork_id': 'comp-twist-doubling-incompatible',
        'backing_theorems': [
            'SKEFTHawking.PinPlusCompTorsorNoGo.no_comp_twist_of_doubling_rigid',
            'SKEFTHawking.PinPlusCompTorsorNoGo.not_doubling_rigid_of_comp_twist',
            'SKEFTHawking.PinPlusCompTorsorNoGo.no_uniform_comp_twist_of_cylinder_rigid',
        ],
        'nogo_kind': 'structural_forcing',
        'false_statement': "A tangential datum can carry an H¹-coordinate field `comp` with reversal twist `comp ↦ comp + w₁` (the P ↦ P⊗ε coordinate), anchored by a restriction-compatibility Bor condition. FALSE (W-A gate, Fable vacuity attack 2026-07-13): the mandatory `negBor` inhabits Bor on the DOUBLING bordism — a product cylinder whose two boundary inclusions are homotopic — so any '∃x : H¹(W) restricting to the end-comps' condition forces comp(revStr σ) = comp σ, contradicting the twist on any non-orientable s (w₁ ≠ 0); the uniformly-twisted variant dies on `cylBor` (shift 0). The datum is JOINTLY UNINSTANTIABLE with the TangentialData op interface. FIX space: a per-boundary-component collar/co-orientation datum with a w₁(W)-corrected compat (any v2 must evade these theorems' hypotheses), or drop the comp field (KT §5 puts the odd-bit content in the w₁-dual 3-manifold V / ψ, not in an H¹ coordinate).",
        'memory': '[[project_5qH_nonhausdorff_substrate_bug]]',
    },
    'membrane_level_nonhausdorff': {
        'fork_id': 'membrane-level-nonhausdorff-collapse',
        'backing_theorems': [
            'SKEFTHawking.PinPlusCompTorsorNoGo.qLevelTripleMembrane_not_t2',
        ],
        'nogo_kind': 'refutation',
        'false_statement': "A manifold-typed WITNESS datum inside a carrier or relation (the membrane/3-manifold Q, the surface Σ, any auxiliary manifold field) inherits honesty from the T2 fence on the ambient bordism W. FALSE (W-A gate, Fable vacuity attack 2026-07-13): the bug-eyed collapse is dimension-generic — `qLevelTripleMembrane` is a compact non-Hausdorff membrane with THREE boundary copies of Σ (kernel-checked non-T2), so a T2-less Q-encoding lets ker(H₁(∂Q)→H₁(Q)) be adversarially chosen, Taylor-Thm-1.1 extension conditions lose their teeth, and the computed Brown/abk8 invariant fails bordism-invariance. RULE: every manifold-typed datum needs its OWN T2 (+ compactness/charted) certificate; the W-level fence does not propagate.",
        'memory': '[[project_5qH_nonhausdorff_substrate_bug]]',
    },
    'free_membrane_kernel_kills_nonsplit': {
        'fork_id': 'free-membrane-kernel-kills-nonsplit',
        'backing_theorems': [
            'SKEFTHawking.PinPlusKTVacuityGateWD.L44_metabolic',
            'SKEFTHawking.PinPlusKTVacuityGateWD.doubleKillerBInc_ker',
        ],
        'nogo_kind': 'refutation',
        'false_statement': "The as-built CharPair carrier (Bor with the membrane kernel L carried as a FREE Submodule field, the geometric membrane Q deferred) supports the KT §5 non-split content — KTNonSplit (8•[ℝP⁴] ≠ 0) is open/dischargeable on it. FALSE (W-D vacuity gate round 3, Fable, 2026-07-13, kernel-checked FOR EVERY PROVIDER): with L free, the UN-reversed double σ⊔σ bounds the plain doubling cylinder whenever q⊕q admits ANY metabolic Lagrangian (brown ∈ {0,4}); the e₈/extended-Hamming graph of x ↦ x + (Σx)·𝟙 (q∘φ = −q, 16-point decide) certifies one for [ℝP⁴]⁴ that NO membrane in (ℝP⁴)⁴×I realizes ⟹ 8•[ℝP⁴] = 0, the binder pair {KTKernelCard, KTNonSplit} is jointly unsatisfiable, and ⟨[ℝP⁴]⟩ is ≤ ℤ/8. The anti-collapse engine protects only Witt-class (brown) equality — exactly the part KT p.217 says cannot see [Kummer]. ROUND-3 OF THE PATTERN: every deferred geometric tie converts completeness content into falsehood (rounds 1-2: comp-twist, membrane-T2, taylor-leg). FIX: CharPairBor must carry the certified membrane Q with L COMPUTED as ker(H₁(∂Q)→H₁(Q)) + the item-3 relative characteristic tie (the frozen v4 spec, under-implemented by the interim build); acceptance test = the honest cylinder membrane's ANTI-DIAGONAL kernel excludes the e₈ graph (doubleKillerBor must break). Also: KTKernelCard quantifies over hchar-untethered fake classes (fakeRP4RankZero) — tie (n,q,surf) or restrict the quantifier before restating. UPDATE (arm-4 re-gate migration + round-4.5 self-attack, 2026-07-14): the FIX's first half LANDED — pinPlusCharPairData's Bor is the membrane-TIED CharPairBorTied in-place (L = ker mem.bInc, all 8 op witnesses tied, PinPlusCharPairData §9.6; acceptance tests green in PinPlusCharPairMembraneTie). The backing refutations PERSIST on the migrated carrier via the SYNTHETIC-bInc replay (doubleKillerBorTied, PinPlusKTVacuityGateWD §4.5: GeoMembrane.bInc is still un-tethered, and graphBInc phiLin has kernel exactly the e₈ graph) — i.e. the tie NARROWS the hole to precisely the geometric-realization obligation without closing it; binders stay FROZEN. Remaining discharge: require realization data on the membrane datum (GeoRealizationData/GeoMembrane.ofGeometric, PinPlusCharPairMembraneGeoRealization) + the (n,q,surf) tie, then the fresh Fable re-gate. UPDATE 2 (THE FLIP, 2026-07-15): the FIX is COMPLETE — pinPlusCharPairData's Bor is CharPairBorRealized (all 8 op witnesses realized via GeoRealizationTied: derived bases from the carried (n,q,surf) tie + per-object certs + kernels computed from real membrane topology; provider = CharPairWProviderPinned). The instance-level refutations (ktKernelRep_eq_zero, ktNonSplit_false, kt_binders_unsatisfiable, ktKummerTarget_unsatisfiable, ktRP4Class_addOrderOf_dvd_eight) no longer type-check against the flipped carrier and are REMOVED (PinPlusKTVacuityGateWD §5 conversion banner); backing re-pointed to the retained structure-level engines (L44_metabolic + doubleKillerBInc_ker — the kernel-checked e₈ record over the algebraic-core structures, which persist as the historical exploit shapes). The W-D binders {KTKernelCard, KTNonSplit} are GENUINELY OPEN (not refuted, not discharged) — their discharge is W-D's gated work and must pass the round-6 vacuity gate before consumption.",
        'memory': '[[project_5qH_nonhausdorff_substrate_bug]]',
    },
    'tied_carrier_inhabitation_equiv_free': {
        'fork_id': 'tied-carrier-inhabitation-equiv-free',
        'backing_theorems': [
            'SKEFTHawking.PinPlusCharPairGeoRealizationGate.charPairBorTied_nonempty_iff_free',
            'SKEFTHawking.PinPlusCharPairGeoRealizationGate.GeoMembrane.ofSubmodule_L',
            'SKEFTHawking.PinPlusCharPairGeoRealizationGate.jointLagrangian_top',
        ],
        'nogo_kind': 'structural_forcing',
        'false_statement': "The membrane-tied CharPairBorTied (L = ker mem.bInc) is a strictly finer bordism-witness class than the refuted free-L CharPairBor — the tie alone filters geometrically-unrealizable Lagrangians. FALSE (W-A re-gate round 5, Fable, 2026-07-14, kernel-checked): EVERY submodule of the joint boundary space is the computed kernel of a synthetic membrane (GeoMembrane.ofSubmodule via a quotient basis; ofSubmodule_L exact), so Nonempty (CharPairBorTied b σ τ) ↔ Nonempty (CharPairBor b σ τ) (charPairBorTied_nonempty_iff_free) — the tied carrier is inhabitation-EQUIVALENT to the free one, and every round-3/free-form exploit transfers wholesale (round-4.5's doubleKillerBorTied is one instance of this general fact). Also: GeoMembrane.top (mid = 0, kernel ⊤) inhabits for ALL end forms and JointLagrangian is VACUOUS at ⊤ (jointLagrangian_top) — only the Taylor leg ever blocks a degenerate membrane. RULE: the tie is a SHAPE, not a filter, until mem is forced through geometric-realization data carrying the (n,q,surf) basis tie. NOTE (THE FLIP, 2026-07-15): the live carrier's Bor is now CharPairBorRealized — the strict refinement this fork says the tie alone is not; the fork stays TRUE at the tied level (the backing theorems are structure-level and persist) and is the permanent record of WHY the realized refinement is load-bearing.",
        'memory': '[[project_5qH_nonhausdorff_substrate_bug]]',
    },
    'realization_seam_basis_gauge_launders_e8': {
        'fork_id': 'realization-seam-basis-gauge-launders-e8',
        'backing_theorems': [
            'SKEFTHawking.PinPlusCharPairGeoRealizationGate.map_killerGauge_ker_negBorBInc',
            'SKEFTHawking.PinPlusCharPairGeoRealizationGate.ker_transportedBInc_gaugeσ',
            'SKEFTHawking.PinPlusCharPairGeoRealizationGate.doubleKillerGeoMem_L',
            'SKEFTHawking.PinPlusCharPairGeoRealizationGate.map_blockCongr_cylLagrangian',
        ],
        'nogo_kind': 'refutation',
        'false_statement': "Topological certificates on GeoRealizationData (T2, compactness, closed-embedding ι, dimension, membrane-in-W) suffice to make GeoMembrane.ofGeometric honest — a fully-certified realization cannot carry the e₈ kernel. FALSE (W-A re-gate round 5, Fable, 2026-07-14, kernel-checked): the free basis fields eσ/eτ admit a gauge action (GeoRealizationData.gaugeσ) that FIXES every topological field (gaugeσ_bdry/Q/U/ι all rfl — every space/map certificate is gauge-blind) while moving the computed kernel by a block gauge (ker_transportedBInc_gaugeσ); the killerGauge (id ⊞ phiLin through finSumFinEquiv) maps the honest doubling anti-diagonal EXACTLY onto the e₈ kernel (map_killerGauge_ker_negBorBInc), so ANY realization of negBor's own design-mandatory membrane yields a certified ofGeometric image hosting the un-reversed double (doubleKillerBorGeoRealized, conditional on the cylinder realization the roadmap itself requires). General engine: the graph of ANY isometry is a block-gauged anti-diagonal (map_blockCongr_cylLagrangian) — the half-lives-half-dies geometric signature is NOT gauge-invariant. Also kernel-irrelevant: the eQ freedom (ker_transportedBInc_gaugeQ). RULE: the H₁ bases must be DERIVED from the carrier's (n,q,surf) tie (hpolar/hchar-anchored identification of the realization's ends with the carried surfaces), never free fields; topological certificates are necessary but collectively blind. NOTE (THE FLIP, 2026-07-15): the closing mechanism this fork mandates is LIVE — GeoRealizationTied's derivedEσ/τ (toData_eσ = rfl, nothing to post-compose) is the Bor consumed by the flipped pinPlusCharPairData; the fork stays TRUE over the free GeoRealizationData (backing persists) as the record of the gauge exploit the derived bases kill.",
        'memory': '[[project_5qH_nonhausdorff_substrate_bug]]',
    },
    'wadm_sqop_gauge_w2_filter_vacuous': {
        'fork_id': 'wadm-sqop-gauge-w2-filter-vacuous',
        'backing_theorems': [
            'SKEFTHawking.PinPlusCharPairGeoRealizationGate.wuW2_zeroSq',
            'SKEFTHawking.PinPlusCharPairGeoRealizationGate.wuClass_zeroSq',
        ],
        'nogo_kind': 'refutation',
        'false_statement': "WAdm/hwu (wuW2 P14 P23 = 0) is a w₂(W) = 0 filter — discharging a CharPairWProvider certifies genuine Pin⁺-admissibility of the bordisms it covers. FALSE (W-A re-gate round 5, Fable, 2026-07-14, kernel-checked): LefschetzWuDatum.sqOp is a FREE field constrained by neither nondeg nor dimeq; zeroing it makes both Wu classes vanish (wuClass_zeroSq) and hwu hold for EVERY W whatever its honest w₂ (wuW2_zeroSq), so a full CharPairWProvider is dischargeable from bare Lefschetz-duality data with ZERO Steenrod input (charPairWProviderOfDuality) — bordisms with genuine w₂(W) ≠ 0 pass. Same free-field-plus-self-referential-condition shape as round-3's free L; infects CharPairBorTied.P14/P23/hwu directly (the Bor carries copies). RULE: sqOp (and mu/cup) must be PINNED to the substrate's actual relative Steenrod tower (relSq1/relSq2) / fundamental-class evaluation / cup product — definitionally or via certificate fields — in both WAdm and the Bor's own data; no provider instantiation is acceptable without the pin (cylinderP14/P23's sqOp := relSq1/relSq2 is the precedent). UPDATE (arm-4 round 2, 2026-07-14): the PIN LAYER LANDED (PinPlusWAdmPinned) — certificate pins on ALL THREE fields (the audit found cup/mu are a FAITHFULNESS hole even though nondeg blocks zeroing them: a perfect-but-wrong pairing decouples wuClass from the manifold's actual w2): LefschetzWuPinned14/23 + WAdmPinned + CharPairWProviderPinned + CharPairBorTiedPinned. Discrimination kernel-checked both ways: sqOpPinned23_zeroSq_iff (the zeroSq shortcut satisfies the pin IFF the honest relSq = 0), not_sqOpPinned23_ofLefschetzNoWu (the F3 provider engine hands out UN-pinnable data wherever relSq2 != 0), cylinderP14_pinned/cylinderP23_pinned (honest non-vacuity witnesses), CharPairBorTiedPinned.wuFunctional23_honest (a pinned Bor's hwu is the genuine w2-condition). Remaining: fold the pinned refinement into the live carrier's Bor consumption (post basis-tie merge), then re-gate. UPDATE 2 (arm-4 R1, 2026-07-14): the FAKE-CLASS half is CLOSED — the hchar characteristic-surface tie landed on CharPairStrBundled (Guillou-Marin: kroneckerH a (emb-pushforward of surfClass) = mu(a cup a), Nonempty-guarded; all four bundle witnesses supply it; RP4 via the DISCHARGED cruxPullbackGen + the mu(a cup a) = mu(a cup x^2) bridge), and the fake exhibit is UNINHABITABLE: fakeRP4RankZero no longer type-checks and is removed; kernel-checked kill theorems RP4CharPairWitness.rp4_bundle_surfClass_pushforward_ne_zero (every RP4 char-pair bundle has nonvanishing pushed-forward surface class) + no_empty_surface_bundle_on_rp4. KTKernelCard is no longer honestly-false via fake classes. The SOLE remaining discharge item on this fork = the GeoMembrane bInc geometric realization (the synthetic-bInc refutations persist; binders stay frozen) + the fresh Fable re-gate. UPDATE 3 (THE FLIP, 2026-07-15): the pinned provider is LIVE — pinPlusCharPairData now takes CharPairWProviderPinned and its Bor is CharPairBorRealized (P14/P23 carry pin14/pin23 by construction), so hwu on every live bordism witness is the HONEST w₂-condition; the bInc realization discharge item is COMPLETE. Residual on this fork = the round-6 re-gate.",
        'memory': '[[project_5qH_nonhausdorff_substrate_bug]]',
    },
    'taylor_leg_end_convention_trap': {
        'fork_id': 'taylor-leg-end-convention-trap',
        'backing_theorems': [
            'SKEFTHawking.PinPlusTaylorConventionNoGo.no_plain_end_pairing_of_cylinder',
            'SKEFTHawking.PinPlusTaylorConventionNoGo.not_cylinder_plain_pairing_of_odd_value',
            'SKEFTHawking.PinPlusTaylorConventionNoGo.not_cylinder_bor_of_invariant_ne',
        ],
        'nogo_kind': 'structural_forcing',
        'false_statement': "The structured-bordism Taylor extension leg ('boundary classes bounding in the membrane Q have vanishing enhancement') can be stated as a PLAIN joint sum q_σ ⊕ q_τ, or σ-side-only, vanishing on ker(H₁(∂Q)→H₁(Q)). FALSE (W-A re-gate, Fable round 2, 2026-07-13 — both failures fire through the HONEST T2 cylinder, no certificate blocks them): plain-joint forces 2q = 0 on cylinder-kernel classes (the anti-diagonal), killing every odd enhancement value — the ℝP²/ℝP⁴ witness (q(gen)=1, 1+1=2≠0 in ℤ/4) becomes uninstantiable (cylBor totality fails); σ-side-only is vacuous on cylinders, making Bor(reflCylinder) relate ARBITRARY structures — the torsor collapses and the Brown/abk8 map is ill-defined (1 ≠ −1 in ℤ/8 erased). The ONLY correct form negates the τ-END (per Bor-end, not per boundary component): q_σ ⊕ (Z4Quadratic.neg q_τ) vanishes on ker(H₁(∂Q;ℤ/2)→H₁(Q;ℤ/2)). Under that form all 12 TangentialData ops instantiate and Brown-invariance is forced (Lagrangian + Gauss factorization).",
        'memory': '[[project_5qH_nonhausdorff_substrate_bug]]',
    },
    'untethered_membrane_factors_relation': {
        'fork_id': 'untethered-membrane-factors-relation',
        'backing_theorems': [
            'SKEFTHawking.PinPlusCharPairFlipGate.isT2DataBordant_pinPlusCharPair_factors',
            'SKEFTHawking.PinPlusCharPairFlipGate.CharPairBorRealized.transport',
            'SKEFTHawking.PinPlusCharPairFlipGate.ktNonSplit_false_of_e8',
        ],
        'nogo_kind': 'structural_forcing',
        'false_statement': "The flipped carrier (Bor = CharPairBorRealized: GeoRealizationTied with derived bases + computed kernels + pinned provider) supports the KT non-split content — the abstract compact-T2 membrane suffices; no explicit tether of the realization's Q to the bordism's W is needed. FALSE (W-A gate ROUND 6, Fable, 2026-07-15, kernel-encoded — ROUND 6 OF THE DEFERRED-TIE PATTERN): GeoRealizationTied has NO tether to b.W (Q is an arbitrary compact-T2 TopCat — not a manifold, not in W). Consequences, kernel-checked: (1) CharPairBorRealized.transport — any realized witness transports VERBATIM to ANY bordism between the same ends; (2) isT2DataBordant_pinPlusCharPair_factors — the structured relation FACTORS as (∃ unstructured T2 bordism) ∧ ends-only HasEndsRealization, so given a provider, hwu filters NOTHING at the relation level; (3) ktNonSplit_false_of_e8 — ONE mathematically-TRUE abstract hypothesis (E8MembraneRealization: a compact-T2 pair with the e₈-graph H₁-kernel — constructible as 8 RP²'s + an arc tree + four 2-cells, only missing CW/MV machinery in-tree) reproduces the ENTIRE pre-flip refutation chain (8•[RP⁴] = 0, binders jointly unsatisfiable, addOrderOf ∣ 8). KTNonSplit is mathematically FALSE on the untethered shape; W-D binder discharge must NOT open on it (an apparent discharge = an error elsewhere). Positive gate evidence retained: idRealizationTied blocked ONLY by hlag (not_jointLagrangian_bot); the un-reversed in-tree doubling blocked by htaylor (unreversed_double_diag_not_taylorLeg); in-tree engines reach only homeo-graph/block-diagonal kernels (e₈ unreachable at the in-tree horizon) — the exploit needs the abstract-Q freedom, which is exactly what the tether removes. FROZEN ROUND-6 SPEC: (1) THE W-TETHER — CharPairBorRealized gains ιW : C(Q, b.W) (honest form a closed embedding) with commuting glue (real.ι, homσ/homτ, the ends' emb, b's boundary structure); (2) manifold discipline on Q (charted/dimension certificates — abstract compact-T2 admits CW pathologies); (3) provider-quantification fix (CharPairWProviderPinned's ∀-all-bordisms wadm is likely UNINHABITABLE — pinned hwu is impossible on w₂(W) ≠ 0 bordisms — risking vacuity in BOTH directions; restrict to the op-bordism family actually consumed or per-op admissibility data). Then round-7 re-gate.",
        'memory': '[[project_5qH_nonhausdorff_substrate_bug]]',
    },
    'lattice_arf_bridge': {
        'fork_id': 'nogo_lattice_arf_not_sigma8',  # memory slug (referenced by SETTLED_FORKS synthetic-smith-map-to-tied-carrier; no dedicated `## ` block)
        'backing_theorems': ['SKEFTHawking.RokhlinArfNoGo.lattice_arf_bridge_refuted'],
        'nogo_kind': 'refutation',
        'false_statement': 'The lattice Arf bridge σ/8 ≡ Arf(q̄) mod 2 — deriving Rokhlin mod-16 from the intersection FORM alone. FALSE: E₈ has Arf(q̄)=0 but σ/8=1; Rokhlin mod-16 is irreducibly geometric (a characteristic-SURFACE Arf, not the lattice Arf). Kills Phase 5q.C and any form-only mod-16 shortcut.',
        'memory': '[[nogo_lattice_arf_not_sigma8]]',
    },
    'mfd-equals-H1-dead-end': {
        'fork_id': 'mfd-equals-H1-dead-end',
        'backing_theorems': ['SKEFTHawking.PinPlusGenuineCarrierIso.dataBordism_two_torsion_of_revStr_trivial'],
        'nogo_kind': 'structural_forcing',
        'false_statement': 'The `Mfd := H¹` tangential-data construction yields a genuine ℤ/16 / ker=⊥. FALSE: a datum whose structure-reversal (revStr) is trivial is FORCED 2-torsion, never order-16.',
        'memory': '[[project-phase5qF-strict-retirement]]',
    },
    'synthetic-grade-ker-bot-nogo': {
        'fork_id': 'synthetic-grade-ker-bot-nogo',
        'backing_theorems': ['SKEFTHawking.PinPlusGenuineCarrierIso.dataBordism_two_torsion_of_revStr_trivial'],
        'nogo_kind': 'structural_forcing',
        'false_statement': 'ker(abkGrade)=⊥ / card≤16 UNCONDITIONALLY for ANY free-per-manifold grade. FALSE: the ℝP⁴ grade-0 witness (w₂=0, [ℝP⁴]≠0∈Ω₄^O) has no unoriented null-bordism, so the free grade is never injective. ker=⊥ requires the grade TIED to the structure (the GM carrier), never a better proof on a free-grade datum.',
        'memory': '[[nogo_lattice_arf_not_sigma8]]',
    },
    'synthetic-smith-map-to-tied-carrier': {
        'fork_id': 'synthetic-smith-map-to-tied-carrier',
        'nogo_kind': 'structural_forcing',
        'false_statement': 'The Smith map into the 5q.H TIED carrier pinPlusGMTiedData can be built '
            'SYNTHETICALLY — map every neighbor class [M,σ] to [emptySM, (σ,0)] and transport the grade '
            '(the smithDataHom shortcut). FALSE (kernel-forced): the tie htie (reduce16to2 grade16 = '
            'swTotalNe) forces every tied structure on an EMPTY carrier to even grade '
            '(gmTiedStr_grade_even_of_isEmpty), so the odd generator grade16 = 1 is uninhabitable on '
            'emptySM (gmTiedStr_empty_grade16_ne_one) — an odd grade requires a real w₁⁴ = 1 manifold. '
            'The tie that defeats synthetic-grade-ker-bot-nogo simultaneously blocks every synthetic '
            'Smith map; the geometric Smith map into the tied carrier is irreducibly geometric (N1b).',
        'backing_theorems': [
            'SKEFTHawking.PinPlusGMTiedData.gmTiedStr_grade_even_of_isEmpty',
            'SKEFTHawking.PinPlusGMTiedData.gmTiedStr_empty_grade16_ne_one',
        ],
        'memory': 'SETTLED_FORKS § synthetic-smith-map-to-tied-carrier (2026-07-03); encoded 2026-07-12 '
            'arm-2 per N-E (audit-flagged), module SyntheticSmithNoGo.',
    },
    '5qH-injectivity-routes-apex-equivalent': {
        'fork_id': '5qH-injectivity-routes-all-equal-one-completeness-prop',
        'nogo_kind': 'structural_forcing',
        'false_statement': 'The old-tied-carrier injectivity Props — Thom (hthom: SW-trivial Pin⁺ '
            '4-manifold bounds), KT §5 (hle: ker(reduce16to8∘abkGMTied16) ⊆ range(n↦n•g8)), and grade-0 '
            'injectivity (hbound) — are DISTINCT OPEN nodes on pinPlusGMTiedData (k:=0) worth '
            'route-shopping between. FALSE: that carrier is VACATED, so none of them is open there — '
            'hbound is an UNCONDITIONAL THEOREM on it (grade0_eq_zero_of_nonHausdorff, proved with ZERO '
            'geometric input via the non-Hausdorff collapse), and mk p = mk q ↔ grade16 p = grade16 q '
            '(dataBordismGMTied_mk_eq_iff_grade16_eq), i.e. the relation is pure ZMod-16 bookkeeping. Every '
            'Prop in this family is therefore free on that carrier and carries no completeness content; '
            'route-shopping among them, or re-deriving "which route is closer", is settled-moot BECAUSE '
            'THE CARRIER IS DEAD — not because a route was shown superior.',
        'scope_limit': '⚠ READ BEFORE CITING. What is kernel-proved is exactly three ONE-WAY implications, '
            'all stated on the vacated pinPlusGMTiedData (k:=0) carrier: hthom ⟹ hbound '
            '(grade0_bounds_of_thom), hbound ⟹ hle (spin_range_ge_of_grade0_inj), and hbound ⟹ the '
            'old-carrier iso (omega4PinPlusGMTied_equiv_zmod16_via_kt_of_grade0). So: hbound is SUFFICIENT '
            'to feed those old capstones. NOT proved, anywhere in-tree: (i) any REVERSE implication '
            '(hle ⟹ hbound, hbound ⟹ hthom); (ii) ANY theorem relating the Smith leg (smith_inflow_z16 / '
            'SmithInflow / Ω₆^{Pin⁻}) to hbound in either direction — the Smith leg has ZERO backing here; '
            '(iii) that the routes are equivalent on the FAITHFUL carrier (pinPlusCharPairData); (iv) that '
            'any node is UNAVOIDABLE. Do NOT cite this entry as "the three routes are kernel-proved '
            'equivalent", as "the terminal node is a single geometric completeness input", or as evidence '
            'that a node cannot be routed around — it fences the vacated carrier and nothing else. The live '
            'keystone is the KT lane on the faithful carrier (SETTLED_FORKS 2026-07-06 user-directed '
            're-anchor, which DEMOTED smith_inflow_z16 to an alternative route).',
        'backing_theorems': [
            'SKEFTHawking.NonHausdorffBordismCollapse.grade0_eq_zero_of_nonHausdorff',
            'SKEFTHawking.NonHausdorffBordismCollapse.dataBordismGMTied_mk_eq_iff_grade16_eq',
            'SKEFTHawking.PinPlusGMWitness.spin_range_ge_of_grade0_inj',
            'SKEFTHawking.PinPlusGMWitness.omega4PinPlusGMTied_equiv_zmod16_via_kt_of_grade0',
            'SKEFTHawking.UnorientedThomCapstone.grade0_bounds_of_thom',
        ],
        'memory': 'SETTLED_FORKS § 5qH-injectivity-routes-all-equal-one-completeness-prop (2026-07-04 + '
            '2026-07-06 KT-LMS re-anchor UPDATE); encoded 2026-07-12 arm-2 per N-E (audit-flagged). '
            'CORRECTED 2026-07-21 (atlas-integrity repair, wt3): the previous false_statement asserted a '
            '"kernel-checked equivalence" of the three routes and a canonical reduction to one terminal '
            'node. Verification found the backing to be three ONE-WAY implications with no Smith leg at '
            'all, all on the carrier that NonHausdorffBordismCollapse vacated. The unsupported inference '
            'was deleted; the fenced statement was re-pointed at the (fully backed) carrier-vacation fact '
            'and a scope_limit added. The legacy fork_id retains the old wording and is NOT a claim.',
    },
    '5qH-fg-ek-over-Z-blocked': {
        'fork_id': '5qH-fg-ek-over-Z-blocked',
        'nogo_kind': 'refutation',
        'false_statement': 'The mod-2 Erdős–Kaplansky finiteness forcing (SingularUCFinite: self-duality '
            'forces finite dimension) transports to ℤ — in particular dualization over ℤ stays in the '
            'f.g./countable size class, so PD + UCT self-duality would force H²(M;ℤ) finitely generated. '
            'FALSE: the ℤ-dual of the COUNTABLE free module ℕ →₀ ℤ is the UNCOUNTABLE, non-f.g. '
            'Baer–Specker group ℕ → ℤ (kernel: dual_blowup_not_finite); and the ℤ-EK statement itself is '
            'refuted in the literature by Specker 1950 — (⊕ℤ) ⊕ ℤ^ℕ is self-dual and not f.g. (slenderness '
            'of ℤ; Mathlib-absent, formalization queued). Scout-verified vs FNOP arXiv:1910.07372 + '
            'Blass–Göbel math/9405206; verdict file '
            'Lit-Search/Phase-5qH/FG_via_PD_duality_forcing_verdict_20260712.md.',
        'backing_theorems': [
            'SKEFTHawking.FGDualityNoGo.dual_blowup_not_finite',
            'SKEFTHawking.FGDualityNoGo.not_finite_baerSpecker',
        ],
        'memory': 'SETTLED_FORKS § 5qH-fg-ek-over-Z-blocked (2026-07-12 arm-2); project path for '
            'intH2_basis = witness-level bases.',
    },
    'genuine-gm-carrier-eight-torsion': {
        'fork_id': 'genuine-gm-carrier-eight-torsion',
        'backing_theorems': [
            'SKEFTHawking.PinPlusGMDataZ16.pinPlusGMData_not_equiv_zmod16',
            'SKEFTHawking.PinPlusGMDataZ16.pinPlusGMData_eight_torsion',
        ],
        'nogo_kind': 'refutation',
        'false_statement': 'The genuine ℤ/16 lives directly on the thin GM carrier: DataBordismGrp(pinPlusGMData) ≃+ ZMod 16. FALSE: pinPlusGMData\'s bordism relation records ONLY the mod-8 Brown grade (q.brown ∈ ZMod 8), so cylinder-doubling makes every class 8-torsion (pinPlusGMData_eight_torsion: 8•x=0) ⟹ IsEmpty(DataBordismGrp(pinPlusGMData) ≃+ ZMod 16). The ℤ/16 odd bit is the Smith-LES EXTENSION onto a distinct carrier (the tied/extension carrier, whose mod-8 shadow is abkGM8 via forgetTie), NEVER a surface grade on pinPlusGMData itself. Do NOT target `omega4PinPlusGM_equiv_zmod16 : DataBordismGrp(pinPlusGMData) ≃+ ZMod 16` as literally stated — reframe to the Smith-LES extension carrier (E3) or an enriched (σ,F•F)-carrying GM carrier.',
        'memory': '[[project_5qH_geometric_floor_terminal]]',
    },
    'enriques-datum-refuted-as-shaped': {
        'fork_id': 'enriques-datum-refuted-as-shaped',
        'backing_theorems': [
            'SKEFTHawking.PinPlusKTLeafGate.enriquesDatum_iff_kummerRep',
            'SKEFTHawking.PinPlusKTLeafGate.enriquesDatum_of_ktSpinPresentationDatum',
            'SKEFTHawking.PinPlusKTStepGate.emptySigmaRepresentable_of_geometric',
        ],
        'nogo_kind': 'structural_forcing',
        'false_statement': 'EnriquesDatum as shipped carries independent Enriques-geometry content (w₂ ≠ 0, π₁ = ℤ/2, the line bundle) usable as the W-D B-leaf. FALSE-AS-SHAPED (gate round 10, G10-6): its [Ha] fields collapse — Nonempty (EnriquesDatum prov) ↔ EmptySigmaRepresentable prov (ktKernelRep prov) (enriquesDatum_iff_kummerRep), i.e. it is bare KummerWitness.1 in decorative dressing; the "Enriques" content has no formal footprint. Do NOT construct or consume EnriquesDatum as an independent B-leaf. The frozen replacement B-target is GeometricSpinRepresentable, absorbed by the C-leaf: KTSpinPresentationDatum ⟹ EnriquesDatum (enriquesDatum_of_ktSpinPresentationDatum, via emptySigmaRepresentable_of_geometric) — discharge the C-leaf and B follows; a standalone "Enriques wave" duplicates work into a vacuous shape.',
        'memory': '[[project_5qH_nonhausdorff_substrate_bug]]',
    },
    'geometric-phi-does-not-close-hfwd-fakeability': {
        'fork_id': 'geometric-phi-does-not-close-hfwd-fakeability',
        'backing_theorems': [
            'SKEFTHawking.PinPlusTraceLeafGate.spinForgetPhi_hfwd_of_ktNonSplit',
            'SKEFTHawking.PinPlusTraceLeafGate.spinForgetPhi_hfwd_iff_ktNonSplit',
        ],
        'nogo_kind': 'structural_forcing',
        'false_statement': 'Fixing Φ := spinForgetPhi (the geometric forgetful map) in the dA leaf makes hfwd a genuine geometric obligation not derivable from the conclusion. FALSE (gate round 11): given the presentation row {hA, hB, hg, hdvd, hΦg, h2}, hfwd on the geometric Φ is DERIVABLE from KTNonSplit with zero geometry (R.generates writes x = n•[g]; Φx = n•k₀; nonsplit + 2-torsion force n even ⟹ 32 ∣ σ(x)) — the locating iff spinForgetPhi_hfwd_iff_ktNonSplit pins hfwd at exactly KTNonSplit strength. Consequence (binding round-11 spec): NO statement shape closes the dA/hfwd circularity risk — every hfwd/dA discharge claim requires a non-circularity audit BY PROOF INSPECTION (the per-instance Div32BoundingDatum supply is equally shape-fakeable, round 10 §3). The audit-friendly honest construction target is the kernel characterization ker Φ ⊆ doubles (spinForgetPhi_hfwd_of_ker_sub_doubles — hfwd free from Rokhlin on doubles, consuming zero k₀ facts).',
        'memory': '[[project_5qH_nonhausdorff_substrate_bug]]',
    },
    'dual-spin-opened-construction-conclusion-fakeable': {
        'fork_id': 'dual-spin-opened-construction-conclusion-fakeable',
        'backing_theorems': [
            'SKEFTHawking.PinPlusResidualGate.nonempty_dualSpinConstruction_iff_thirtytwo_dvd',
            'SKEFTHawking.PinPlusResidualGate.nonempty_ktSharpnessSupplyConstr_iff_hfwd',
            'SKEFTHawking.PinPlusResidualGate.spinOfSigMul16_sig',
        ],
        'nogo_kind': 'structural_forcing',
        'false_statement': 'Opening DualSpinFromW into DualSpinConstruction (Vspace/ιV/Vspin/hcob/hcover fields) makes the dual-spin supply a genuine geometric obligation not derivable from the conclusion. FALSE (gate round 12): on an unpinned ambient, Nonempty (DualSpinConstruction PUnit sigM) ↔ 32 ∣ sigM — every field including hcob inhabits from bare arithmetic (the σ-onto realization engine spinOfSigMul16 supplies genuine SmoothSpinManifold4 witnesses for every multiple of 16), and modulo the presentation row the whole opened supply ⟺ the hfwd conclusion. The mechanism: amb is a FREE TopCat field. Consequence (binding round-12 spec 1): dA supply claims pass by DATA INSPECTION only — amb must be TopCat.of b.W of the actual tethered witness and edge the geometric ∂E(V); statement-shape audits are insufficient at every opening depth.',
        'memory': '[[project_5qH_nonhausdorff_substrate_bug]]',
    },
    'novikov-substrate-synthetic-inhabitation': {
        'fork_id': 'novikov-substrate-synthetic-inhabitation',
        'backing_theorems': [
            'SKEFTHawking.PinPlusResidualGate.nonempty_novikovRealPairLES_diag',
            'SKEFTHawking.PinPlusResidualGate.nonempty_novikovBoundaryRestriction_iff_sig_eq',
            'SKEFTHawking.PinPlusResidualGate.novikovLagrangian_iff_hbord',
        ],
        'nogo_kind': 'structural_forcing',
        'false_statement': 'The NovikovRealPairLES substrate (or any of the four equivalent σ-descent atom formulations) constitutes progress toward the Thom bordism-invariance of σ beyond the bare hbord statement. FALSE (gate round 12): the diagonal Lagrangian + synthetic quotient inhabit the substrate with zero geometry whenever σ agrees (nonempty_novikovBoundaryRestriction_iff_sig_eq — the Witt step kernel-encoded via exists_lagrangian_of_latticeSig_eq_zero), and novikovLagrangian_iff_hbord proves ALL FOUR formulations (classical Lagrangian / boundary-restriction half-dim / Lefschetz co-isotropy / the pair-LES substrate) are kernel-equivalent to hbord itself. Consequence (binding round-12 spec 2): a Novikov-atom discharge must exhibit a GENUINE bounding-W tower (the relative cap + the geometric restriction data of an actual bordism witness) — linear-algebra Lagrangian constructions are zero progress at both grades.',
        'memory': '[[project_5qH_nonhausdorff_substrate_bug]]',
    },
    'novikov-geometric-tower-carrier-conclusion-fakeable': {
        'fork_id': 'novikov-geometric-tower-carrier-conclusion-fakeable',
        'backing_theorems': [
            'SKEFTHawking.PinPlusRoundThirteenGate.novikovGeometricPairLESDataOfRealPairLES',
            'SKEFTHawking.PinPlusRoundThirteenGate.nonempty_novikovGeometricPairLESData_iff_realPairLES',
            'SKEFTHawking.PinPlusRoundThirteenGate.nonempty_novikovGeometricPairLESData_iff_sig_eq',
            'SKEFTHawking.PinPlusRoundThirteenGate.nonempty_novikovGeometricPairLESData_diag',
        ],
        'nogo_kind': 'structural_forcing',
        'false_statement': 'The NovikovGeometricPairLESData field row (the #196 genuine-tower carrier: rest2/delta/pairing/hexact/hnondeg/hadjDot) is a stronger-than-conclusion carrier whose inhabitation certifies genuine bounding-W tower progress. FALSE (gate round 13): the substrate rebuilds the carrier (novikovGeometricPairLESDataOfRealPairLES — pairing := half the substrate pairing, hadjDot DERIVED from hadj via the polar-form symmetry), so carrier ⟺ substrate (nonempty_novikovGeometricPairLESData_iff_realPairLES), and at block pairs Nonempty (Data (blockDiag A (-B))) ↔ σ(A) = σ(B) — the round-12 Witt step + ofLagrangian + the reverse map populate EVERY field from a bare Lagrangian with zero bordism geometry. hadjDot moved the fork-20 perimeter; it did not close it. Consequence (binding round-13 spec 1): Novikov-lane carrier populations are progress ONLY if rest2/delta/pairing are the tensor-R base-changes of the genuine integral tower maps of an actual relative cycle — audited by DATA INSPECTION; a quotient-of-coordinate-space H3rel is zero progress by construction.',
        'memory': '[[project_5qH_nonhausdorff_substrate_bug]]',
    },
    'seam-transfer-open-support-uninhabitable': {
        'fork_id': 'seam-transfer-open-support-uninhabitable',
        'backing_theorems': [
            'SKEFTHawking.PinPlusTraceSeamTransferNoGo.wAtt_mem_subspaceChains_range_phi',
            'SKEFTHawking.PinPlusTraceSeamTransferNoGo.boundary_wAtt_eq_zero',
            'SKEFTHawking.PinPlusTraceSeamTransferNoGo.isEmpty_capstoneSeamTransfer_of_null',
            'SKEFTHawking.PinPlusTraceSeamTransferNoGo.isEmpty_capstoneSeamTransferSeam_of_null',
        ],
        'nogo_kind': 'refutation',
        'false_statement': 'The CapstoneSeamTransfer / shared-cSeam CapstoneSeamTransferSeam consumption shape (the #184-#207 hasClass route: the top-face/disk-boundary splits with OPEN-complement supports hwOut/hvOut plus the literal htransfer equality) is inhabitable for a genuine fundamental cycle z and a proper attaching region, and the 3x-circled closed-S co-adaptation barrier (#198/#204/#207) is a machinery gap. FALSE (the #210 lead adjudication): htransfer FORCES wAtt into the CLOSED attach image (injective-mapDomain support transport + fromCyl_image_compl disjointness — wAtt_mem_subspaceChains_range_phi), char-2 boundary algebra then forces BOTH split pieces to be CYCLES (boundary_wAtt_eq_zero via subspaceChains_inf_compl_eq_bot), so z@top decomposes as a seam-supported cycle + an off-seam cycle; whenever the two regions have null 4-cycle classes (H4(S1xD3;Z/2)=0, H4 of an open 4-region = 0 — the genuine consumption) and z@top does not bound (z fundamental), the shape is EMPTY (isEmpty_capstoneSeamTransfer_of_null + the Seam corollary). Consequence: the transfer route to hasClass is dead AS SHIPPED; the honest repair = CLOSED-complement supports (wOut/vOut in the complement of the INTERIOR of the attach region — the classical two-rel-pieces-sharing-the-interface picture), a NEW gate-pending consumption shape whose interface terms cancel mod 2.',
        'memory': '[[project_5qH_nonhausdorff_substrate_bug]]',
    },
    'collar_pair_closed_seam_attached_collar_bridge_is_false': {
        'fork_id': 'collar-pair-closed-seam-attached-collar-bridge-is-FALSE',
        'backing_theorems': [
            'SKEFTHawking.PinPlusTraceSeamCollarBridgeNoGo.collar_bridge_refuted',
            'SKEFTHawking.PinPlusTraceSeamCollarBridgeNoGo.attachedBridge_iff_support_dichotomy',
        ],
        'nogo_kind': 'refutation',
        'false_statement': "PinPlusTraceSeamResidualNarrow.ClosedSeamAttachedCollarBridge S a -- the closed-S attached-collar bridge, believed to be hctrlH's blocking atom and readable as an open-neighbourhood-to-closed-S collar deformation retraction. FALSE (kernel refutation, 2026-07-21): collar_bridge_refuted exhibits closed nonempty S = {e_0} in the 5-sphere, U = univ (satisfying the engine's own cover hypothesis sphere subset U union S-complement verbatim), and a chain a in subspaceChains (U inter sphere) with NOT (Bridge S a). The witness is one concrete great-circle 4-simplex v |-> cos(pi*v_0/2)*e_0 + sin(pi*v_0/2)*e_1, norm 1 throughout, running from e_0 in S to e_1 not in S. ANATOMY (both directions, attachedBridge_iff_support_dichotomy): the bridge holds IFF no support simplex of a straddles S -- so it has NO collar content whatsoever, and the 'collar deformation-retraction' reading in PinPlusTraceSeamResidualNarrow section 3 is WRONG: a retraction gives homotopy/homology invariance, never the chain-level EQUALITY the bridge demands. CONSEQUENCE, and the reason this is not a wall: the bridge was never hctrlH's blocker. The predecessor reduction of hctrlH to it was STRICTLY TOO STRONG -- the bridge demands a correction supported in the CLOSED complement sphere minus S, while CollarPairBuild.hctrlH's companion houtH only asks for the OPEN complement sphere minus (Subtype.val image of K), off the builder-chosen shrunk closed core K (a free field documented K inside int A). That is the open-cover engine's native granularity, so hctrlH + houtH are supplied bridge-free by exists_ctrlHandle_split_offCore. SCOPE (do not overstate): this kills the ATOM, not the row. The producer is SUFFICIENT, not equivalent -- it exhibits one admissible (muH, cCore, outH) triple, claims no cCore uniqueness, and does NOT supply the co-adaptation with the cylinder side, which is now carried by hctrlC. Non-vacuity pinned: exists_nonempty_core_of_sphere_mem shows a NONEMPTY closed core meeting the interiority hypothesis exists whenever U meets the sphere, so this is not a statement about the K = empty case that hcoreHit rules out.",
        'memory': '[[project_5qH_nonhausdorff_substrate_bug]]',
    },
    'collar_pair_face_row_forces_seam_to_meet_boundary': {
        'fork_id': 'collar-pair-face-row-forces-seam-to-meet-boundary',
        'backing_theorems': [
            'SKEFTHawking.PinPlusTraceCapstoneCollarPairFace.CollarPairGeomFace.exists_seamPoint_mem_bd_of_null',
            "SKEFTHawking.PinPlusTraceCapstoneCollarPairFace.CollarPairGeomFace.exists_seamPoint_mem_range_eM'_of_null",
        ],
        'nogo_kind': 'structural_forcing',
        'false_statement': "A CollarPairGeomFace row (the houtPair producer: the row's own supports plus the seam-annulus containment hseamAnn) can be inhabited with an ENTIRELY INTERIOR seam -- i.e. with no seam point of the surgered end lying in dW, so that the collar-pair route never has to pay for the seam. FALSE (structural forcing, 2026-07-21): in a face row the two fields hKoffBd + hseamAnn PIN the shrunk core, K_eq_compl_seamPreimage giving F.K = (seamPoint preimage of dW)^c. An entirely interior seam therefore forces K = univ, which degenerates houtC/houtH to exactly the open-complement supports fenced by collar-pair-open-complement-annulus-is-refuted-shape, and not_collarAnnulusOpen_of_null kills those under the null/non-bounding hypotheses. Hence exists_seamPoint_mem_bd_of_null: no face row has an entirely interior seam; read on the datum (exists_seamPoint_mem_range_eM_of_null), range d.eM' MUST contain a seam point. Companion: topFaceShrunk_eq_topFace_inter_preimage shows that at the forced core the coarse support EQUALS topface INTER fromCyl^-1(dW), so the route is tight -- no slack between shrunk-core and maximal granularity. SCOPE (worker-stated in both docstrings, lead-confirmed -- do not overstate): this does NOT close the coarse houtPair route; it states the route's PRICE. It says nothing about CollarPairGeomCore, which carries no hseamAnn field. CollarPairGeomFace is a SUFFICIENT producer, NOT an equivalent row (nonempty_collarPairGeomCore_of_face is one-directional), so the obligation count stays at FIVE.",
        'memory': '[[project_5qH_nonhausdorff_substrate_bug]]',
    },
    'collar_pair_open_complement_annulus_is_refuted_shape': {
        'fork_id': 'collar-pair-open-complement-annulus-is-refuted-shape',
        'backing_theorems': [
            'SKEFTHawking.PinPlusTraceCapstoneCollarPairCore.collarAnnulusOpen_toSeamTransferSeam',
            'SKEFTHawking.PinPlusTraceCapstoneCollarPairCore.not_collarAnnulusOpen_of_null',
        ],
        'nogo_kind': 'structural_forcing',
        'false_statement': "houtPair (the collar-annulus weld obligation of the #212 collar-pair row) can be discharged for free by reading its three required boundary-supports straight off the in-tree SurgeredEndDatum, whose d.topFaceCovered (fromCyl '' (topface \\ range phi) subset dW), d.sphereFaceCovered (fromHandle '' (sphere \\ S) subset dW) and bottom-face fact are exactly the three supports hbd_ofTransfer consumes. FALSE (structural forcing, 2026-07-21): a collar-annulus refinement at that OPEN-COMPLEMENT granularity, taken on top of the row's own hctrlC/hctrlH, CONSTRUCTS a verbatim inhabitant of CapstoneSeamTransferSeam (collarAnnulusOpen_toSeamTransferSeam: the seam core absorbs the annulus at cSeam := cCore + ann, cHa := diskDetectChain, and the two residuals are verbatim its wOut/vOut with verbatim its hwOut/hvOut supports) -- i.e. the shape refuted by seam-transfer-open-support-uninhabitable. not_collarAnnulusOpen_of_null then turns that refinement into False under the identical null/non-bounding hypotheses backing isEmpty_capstoneSeamTransferSeam_of_null. So the free-looking SurgeredEndDatum instantiation of houtPair is settled-dead. SCOPE (worker-stated, lead-confirmed -- do not overstate): only the ONE direction `open-complement refinement ==> refuted structure` is proved. It is NOT proved that every collar-annulus refinement is impossible: a refinement at the strictly COARSER closed-complement granularity the #210 repair adopted (topface \\ phi '' K for a shrunk core K) is excluded by nothing here, and houtPair_of_bdMem / houtPair_of_bdImageSubset remain its LIVE route. Cite as 'the free-looking d.topFaceCovered instantiation is closed', NEVER as 'the collar-annulus refinement is closed'.",
        'memory': '[[project_5qH_nonhausdorff_substrate_bug]]',
    },
    'collar_pair_maximal_core_reenters_refuted_support': {
        'fork_id': 'collar-pair-maximal-core-reenters-refuted-support',
        'backing_theorems': [
            'SKEFTHawking.PinPlusTraceCapstoneCollarPairGeom.coreHit_of_univ',
            'SKEFTHawking.PinPlusTraceCapstoneCollarPairGeom.houtC_support_univ_eq_refuted',
        ],
        'nogo_kind': 'structural_forcing',
        'false_statement': "The CollarPairGeom/CollarPairGeomUnsub row's anti-fake tether hcoreHit can be made free of charge by enlarging the #210 shrunk core K toward its limit K = univ, keeping the rest of the collar-pair split data intact. FALSE (structural forcing, 2026-07-21): at K = univ the tether IS indeed a consequence of the top-face split (coreHit_of_univ - cCore lands in subspaceChains of univ-complement = the empty set, hence cCore = 0, so z@top = outC), but at K = univ the remainder support collapses to `(univ x {top}) \\ phi '' univ = (univ x {top}) \\ range phi` (houtC_support_univ_eq_refuted), which is VERBATIM the OPEN-complement signature refuted by seam-transfer-open-support-uninhabitable. So the maximal-core shortcut purchases the tether only by re-entering the settled-dead shape, and hcoreHit must remain a genuine obligation of the row. SCOPE (lead-corrected, do not overstate): only the direction `K = univ ==> tether free AND support refuted` is proved. There is NO uniqueness/converse theorem - a strictly smaller K that still discharges hcoreHit is NOT excluded, merely unexplored. Cite this fence as 'the obvious maximal-core shortcut is closed', never as 'every hcoreHit shortcut is closed'.",
        'memory': '[[project_5qH_nonhausdorff_substrate_bug]]',
    },
    'k7_seam_cover_interior_fails': {
        'fork_id': 'k7-seam-cover-interior-fails',
        'backing_theorems': [
            'SKEFTHawking.KummerK7SeamCoverNoGo.k7SeamCoverHyp_false',
        ],
        'nogo_kind': 'refutation',
        'false_statement': 'K7SeamCoverHyp (the K7 opener\'s un-thickened MV cover hypothesis): the INTERIORS of the two closed Kummer-weld pieces (the Q-image and the 16 closed E-images) cover the welded K3 carrier, so the Mayer-Vietoris assembly can run on the un-thickened pieces directly. FALSE (kernel refutation k7SeamCoverHyp_false): a seam point (fiberNorm = 1, the glued RP3 locus) is interior to NEITHER piece - E-side, every neighbourhood meets fiber radius < 1 (the inward deform path); Q-side, every neighbourhood meets the E-exterior along the outward chart ray (via circle_exp_injOn_one -> centeredChartParam_injOn_double, chart injectivity on the doubled ball). Consequence: "discharge K7SeamCoverHyp" is settled-dead; the UNIQUE route is the collar-thickened cover (qThick = qImage union outer half-collars fiberNorm >= 1/2) whose interior-cover hypothesis IS discharged (k7_hcov, KummerK7MVAssembly) and through which the whole K7 accounting now runs unconditionally.',
        'memory': '[[project_5qH_nonhausdorff_substrate_bug]]',
    },
    'gram_literal_equality_is_choice_dependent': {
        'fork_id': 'gram-literal-equality-is-choice-dependent',
        'backing_theorems': [
            'SKEFTHawking.SphereProdGramPinRetire.sphereProd_interMatrix_computed_eq',
            'SKEFTHawking.SphereProdGramPinRetire.sphereProdGramPin_iff',
        ],
        'nogo_kind': 'structural_forcing',
        'false_statement': "SphereProdGramPin - the LITERAL matrix equality `interMatrix fc B = sphereProdFormDatum` on the computed rank-2 basis - is a disclosed GEOMETRIC residual of the S2xS2 intersection form, dischargeable once the Kunneth/EZ cross value is pinned. FALSE AS FRAMED (structural forcing, 2026-07-21): the exact computed-basis Gram is `!![-(2*s*u*eps), u*eps; u*eps, 0]` (sphereProd_interMatrix_computed_eq), so the pin holds IFF `s = 0 AND u*eps = 1` (sphereProdGramPin_iff). Neither conjunct is available: (1) `s` is the alpha-coordinate of the Exists.choose split generator `deltaGen`, pinned only modulo `sumInto` whose fst_* image is NONZERO (sumInto_prodFst) - so `deltaGen |-> deltaGen + k*sumInto 1` shifts `s` by `k` and the (0,0) entry by `-2*k*u*eps`, making the Prop INDEPENDENT of the in-tree data, not merely unproven; (2) `u`, `eps` are pinned only as units, an orientation/sign gap. Note this also kills the prior hope that normalizing the cross value to literally 1 would suffice - a normalized eps still leaves the diagonal free. The GEOMETRIC content the pin stood in for IS in tree and unconditional: SphereProdBasisIdInt.sphereProd_interMatrix_intCongr_hyp proves II(S2xS2) integrally CONGRUENT to Hyp itself. Every consumer conclusion is congruence-invariant, so the congruence supersedes the equality; hypothesis-free replacements are SphereProdGramPinRetire.sphereProd_s2s2_{hyp,evenUnimodular,latticeSig,htopo}'. GENERAL RULE (applies to every Gram atom incl. the K3/T4 one): state Gram targets as `IntCongr ... <form>`, NEVER as a literal matrix equality on a chosen basis - the extra content of an equality over a congruence is basis normalization, not geometry, and is generically unreachable whenever any basis vector comes from a choice.",
        'memory': '[[project_5qH_nonhausdorff_substrate_bug]]',
    },
    'kronecker_dual_is_not_the_h1_enhancement_transport': {
        'fork_id': 'kronecker-dual-is-not-the-h1-enhancement-transport',
        'backing_theorems': [
            'SKEFTHawking.CharSurfacePDTransport.homologyCoords_gauge',
            'SKEFTHawking.CharSurfacePDTransport.not_forall_kroneckerTransport_gauge_invariant',
            'SKEFTHawking.CharSurfacePDTransport.hyperbolic2_taylor_flip',
            'SKEFTHawking.CharSurfacePDTransport.gramMap_hyperbolic2',
            'SKEFTHawking.CharSurfacePDBundled.pinCharSurfaceOfBundled_gauge_H1Iso',
        ],
        'nogo_kind': 'refutation',
        'false_statement': "The Kronecker/UCT dual of the carried cohomology basis - `homologyBasisOfCohomologyBasis basis`, the value `pinCharSurfaceOfBundled` puts in `PinCharSurface.H1Iso` (and the value `GeoRealizationTied.derivedEsigma`/`derivedEtau` put in the seam) - is the identification of `H1(Sigma;Z/2)` that the enhancement `q` lives on, so `q` may be evaluated at those coordinates at ANY rank. FALSE (audit M4, kernel-checked 2026-07-21). The carrier's `hpolar` pins `q.B` to the cup pairing in the COHOMOLOGY basis `e`; the Kronecker dual is the transport that makes the KRONECKER pairing the dot product (`kroneckerH_eq_dotProduct`), a different normalization. The two differ by the Gram operator of `q.B` (`homologyCoords_eq_gramMap`), and the difference is not cosmetic: (1) VARIANCE MISMATCH - a gauge `e |-> g o e` moves the derived homology coordinates by the transpose-inverse (`homologyCoords_gauge`) while `hpolar` forces `q` to move by `g` (`hpolar_gaugePullback`), so `q o (Kronecker transport)` is not gauge-invariant (`not_forall_kroneckerTransport_gauge_invariant`, rank-2 transvection witness); the gauged carrier is a genuine `CharPairStrBundled` with the SAME surf/emb/surfClass/hchar and the SAME Brown grade (`gaugeBundled_*`, `gaugeBundled_brown`), so the value read is not a function of the geometry. (2) TRUTH-VALUE FLIP - for the genus-1 model in a symplectic basis the Gram operator is the coordinate SWAP (`gramMap_hyperbolic2`), and on the a-cycle metabolizer `q` vanishes while at its raw-Kronecker coordinates `q = 2 != 0` (`hyperbolic2_taylor_flip`): `TaylorKernelVanishing` is FALSE exactly where Taylor Thm 1.1 says it must be TRUE. SCOPE (do not overstate): the defect is strictly NONZERO-RANK. At rank 0 the two transports are EQUAL (`homologyBasisPD_eq_of_rank_zero`, `pinCharSurfaceOfBundledPD_eq_of_rank_zero`), so the entire live rank-zero `PinPlusKTRankZeroBounding`/`toLeaves` chain is sound and unaffected; and `gramMap_stdQuadratic` shows the raw transport is accidentally correct whenever the chosen basis is orthonormal for the intersection form (which a positive-genus surface's symplectic sector is not). REPAIR (SHIPPED, no hypothesis needed): use `homologyBasisPD Q e := (homologyBasisOfCohomologyBasis e).trans (gramEquiv Q).symm` - `Z4Quadratic.nondeg` IS the Gram operator's invertibility - which is the Poincare-dual transport (`homologyBasisPD_pd`: `homologyBasisPD Q e (pd a) = e a`), is gauge-covariant (`homologyBasisPD_gauge`) and yields a gauge-INVARIANT enhancement value (`q_homologyBasisPD_gauge_invariant`); carrier-level entry point `pinCharSurfaceOfBundledPD`. BLAST RADIUS: the same raw transport feeds `TaylorLegVanishes`/`JointLagrangian` through `GeoRealizationTied.derivedEsigma`/`derivedEtau` (PinPlusCharPairRealizationTied), so any nonzero-rank use of the realized carrier's Taylor leg needs the same correction.",
        'memory': '[[project_5qH_nonhausdorff_substrate_bug]]',
    },
}

# ════════════════════════════════════════════════════════════════════
# Phase 5a: Onsager Algebra Parameters (Wave 1)
#
# The Onsager algebra is defined by the Dolan-Grady (DG) relations:
#   [A₀, [A₀, [A₀, A₁]]] = 16[A₀, A₁]  (and symmetric)
#
# It is isomorphic to the fixed-point subalgebra of L(sl₂) under
# the Chevalley involution (Davies 1990, Roan 1991).
#
# Sources:
#   Onsager, Phys. Rev. 65, 117 (1944) — original relations
#   Dolan & Grady, Phys. Rev. Lett. 49, 108 (1982) — finite presentation
#   Davies, J. Phys. A 23, 2245 (1990) — isomorphism proof
#   Gioia & Thorngren, PRL 136, 061601 (2026) — lattice chiral fermions
# ════════════════════════════════════════════════════════════════════

ONSAGER_ALGEBRA = {
    # Dolan-Grady relation coefficient: [A₀, [A₀, [A₀, A₁]]] = DG_COEFF * [A₀, A₁]
    'DG_COEFF': 16,
    # Davies commutation relations: [A_m, A_n] = DAVIES_AA_COEFF * G_{m-n}
    'DAVIES_AA_COEFF': 4,
    # [G_n, A_m] = DAVIES_GA_COEFF * (A_{m+n} - A_{m-n})
    'DAVIES_GA_COEFF': 2,
    # Chevalley involution: θ(e)=f, θ(f)=e, θ(h)=-h
    # Loop algebra embedding: A_m ↦ f⊗t^m - e⊗t^{-m}, G_m ↦ h⊗t^{-m} - h⊗t^m
    'GENERATORS': 2,  # DG presentation has 2 generators (A₀, A₁)
    'RELATIONS': 2,   # 2 cubic DG relations
    'SL2_DIM': 3,     # sl₂ is 3-dimensional
}


# ════════════════════════════════════════════════════════════════════
# Phase 5a: Z₁₆ Classification Parameters (Wave 3A)
#
# Ω₄^{Pin⁺} ≅ ℤ₁₆ (Giambalvo 1973, Kirby-Taylor 1990).
# Axiomatized in Lean; conditional theorems derive chirality constraints.
#
# The 16-fold way (Bruillard-Galindo-Rowell-Wang, 2016):
#   Every super-modular category admits exactly 16 inequivalent
#   minimal modular extensions.
#
# Sources:
#   Giambalvo, Trans. AMS 180, 275 (1973) — original computation
#   Kirby & Taylor, in "Topology" (1990) — Adams spectral sequence proof
#   Bruillard et al., J. Math. Phys. 58, 041704 (2017) — 16-fold way
#   Freed & Hopkins, Ann. Math. 194, 529 (2021) — reflection positivity
# ════════════════════════════════════════════════════════════════════

Z16_CLASSIFICATION = {
    # The order of Ω₄^{Pin⁺}
    'BORDISM_ORDER': 16,
    # Central charge periodicity: c ≡ 0 (mod 16) for super-modular extensions
    'CENTRAL_CHARGE_MOD': 16,
    # Existing chirality limitation from Phase 5 (GaugeEmergence.lean)
    'STRING_NET_MOD': 8,  # c ≡ 0 (mod 8) for Z(Vec_G) — proved
    # Strengthened constraint from Z₁₆ axiom
    'Z16_MOD': 16,  # c ≡ 0 (mod 16) — conditional on Z₁₆ axiom
    # Number of minimal modular extensions of sVec
    'SVEC_EXTENSIONS': 16,  # SO(N)₁ for N=1,...,16
    # A(1) sub-Hopf algebra dimension (Steenrod)
    'A1_DIM': 8,  # A(1) = ⟨Sq¹, Sq²⟩ is 8-dimensional over F₂
    # Fermion counting: anomaly cancellation requires 16n Majorana fermions
    'ANOMALY_CANCELLATION_UNIT': 16,
}


# ════════════════════════════════════════════════════════════════════
# Phase 5a: Gioia-Thorngren Lattice Chiral Fermion (Wave 2)
#
# GT constructs 3+1D lattice Hamiltonians with exact chiral symmetry
# [H, Q_A] = 0 where Q_A is non-on-site and non-compact.
#
# Construction 1: Single Weyl fermion via Karsten-Wilczek + BdG doubling.
#   H_BdG(k) is 4x4 at each k-point (sigma x tau Kronecker structure).
#   Wilson mass M(k) = 3 - cos(kx) - cos(ky) - cos(kz) gaps all doublers.
#   Chiral charge q_A(k) = 1_sigma ⊗ [(1+cos p3)/2 · tau_z + sin(p3)/2 · tau_x].
#
# Construction 2: Weyl doublet (magnetic Weyl semimetal).
#   Q_V (on-site) + Q_A (non-on-site) generate the Onsager algebra on UV lattice.
#   [Q_V, Q_A] ≠ 0 contracts to SU(2) in IR (emanant symmetry).
#
# Sources:
#   Gioia & Thorngren, PRL 136, 061601 (2026) — original GT construction
#   Misumi, arXiv:2512.22609 (2025) — BdG form, Eqs. 46-50
#   Seiberg, arXiv:2211.12543 (2023) — emanant symmetry concept
#   Seiberg & Shao, arXiv:2307.02534 (2024) — emanant symmetry + anomaly matching
# ════════════════════════════════════════════════════════════════════

GT_MODEL = {
    # Spatial dimension of the lattice
    'LATTICE_DIM': 3,
    # Internal DOF per site (spin up/down)
    'N_BANDS': 2,
    # BdG (Nambu) doubling factor
    'NAMBU_FACTOR': 2,
    # BdG block dimension at each k-point: NAMBU_FACTOR * N_BANDS = 4
    'BDG_BLOCK_DIM': 4,
    # Wilson mass offset (number of cosines in M(k) = d - sum cos)
    'WILSON_OFFSET': 3,
    # Wilson mass range: M(k) ∈ [0, 2*LATTICE_DIM]
    'WILSON_MAX': 6,
    # Number of Weyl nodes: M(k)=0 only at k=(0,0,0) → exactly 1
    'WEYL_NODE_COUNT': 1,
    # Chiral charge real-space range (nearest-neighbor along z)
    'Q_A_RANGE': 1,
    # Pauli matrix dimension
    'PAULI_DIM': 2,
    # GS conditions violated by GT: I2 (on-site), I3 (compact spectrum)
    'GS_VIOLATIONS': ['I2_on_site', 'I3_compact_spectrum'],
}


# ════════════════════════════════════════════════════════════════════
# Phase 5b: Standard Model Fermion Data and ℤ₁₆ Anomaly
#
# The SM has a discrete ℤ₄ symmetry generated by X = 5(B-L) - 4Y
# (García-Etxebarria & Montero, arXiv:1808.00009, JHEP 08, 003, 2019).
# The global anomaly is classified by Ω₅^{Spin^{ℤ₄}} ≅ ℤ₁₆.
# Each left-handed Weyl fermion with odd ℤ₄ charge contributes ±1.
#
# With ν_R (one generation): 6+3+3+2+1+1 = 16 ≡ 0 mod 16 (anomaly-free)
# Without ν_R (one generation): 6+3+3+2+1 = 15 ≡ -1 mod 16 (anomalous)
# Three generations without ν_R: 3×15 = 45 ≡ -3 mod 16 (forces hidden sectors)
#
# Sources:
#   García-Etxebarria & Montero, JHEP 08, 003 (2019) [arXiv:1808.00009]
#   Wang, PRD 110, 125028 (2024) [arXiv:2312.14928] — generation constraint
#   Dai & Freed, J. Diff. Geom. 35, 471 (1994) — Dai-Freed theorem
#   Witten, Phys. Lett. B 117, 324 (1982) — SU(2) global anomaly
# ════════════════════════════════════════════════════════════════════

# SM fermion representations (one generation, left-handed Weyl basis)
# Each entry: (B-L, Y, SU(3)_c × SU(2)_L components, description)
# Y = weak hypercharge (Y convention: Q = T₃ + Y)
SM_FERMION_DATA = {
    'Q_L': {
        'label': 'Quark doublet (u_L, d_L)',
        'B_minus_L': 1/3,       # B=1/3, L=0
        'Y': 1/6,               # weak hypercharge
        'components': 6,         # 3 color × 2 weak
        'chirality': 'left',
    },
    'u_R_bar': {
        'label': 'Up antiquark (ū_R)',
        'B_minus_L': -1/3,      # B=-1/3, L=0
        'Y': -2/3,              # weak hypercharge
        'components': 3,         # 3 color
        'chirality': 'left',     # left-handed in CPT-conjugate basis
    },
    'd_R_bar': {
        'label': 'Down antiquark (d̄_R)',
        'B_minus_L': -1/3,      # B=-1/3, L=0
        'Y': 1/3,               # weak hypercharge
        'components': 3,         # 3 color
        'chirality': 'left',
    },
    'L': {
        'label': 'Lepton doublet (ν_L, e_L)',
        'B_minus_L': -1,        # B=0, L=1
        'Y': -1/2,              # weak hypercharge
        'components': 2,         # 2 weak
        'chirality': 'left',
    },
    'e_R_bar': {
        'label': 'Positron (ē_R)',
        'B_minus_L': 1,         # B=0, L=-1
        'Y': 1,                 # weak hypercharge
        'components': 1,
        'chirality': 'left',
    },
    'nu_R_bar': {
        'label': 'Right-handed neutrino (ν̄_R)',
        'B_minus_L': 1,         # B=0, L=-1
        'Y': 0,                 # weak hypercharge (gauge singlet)
        'components': 1,
        'chirality': 'left',
    },
}

# ℤ₄ charge formula: X = 5(B-L) - 4Y
# All SM fermions have odd X (mod 4), so each contributes ±1 to the anomaly index
SM_Z4_CHARGE_FORMULA = {
    'B_minus_L_coeff': 5,
    'Y_coeff': -4,
}

# Anomaly computation results (from García-Etxebarria & Montero)
SM_ANOMALY = {
    # Total Weyl fermion components per generation (with ν_R)
    'COMPONENTS_WITH_NU_R': 16,    # 6+3+3+2+1+1
    # Total without ν_R
    'COMPONENTS_WITHOUT_NU_R': 15,  # 6+3+3+2+1
    # Anomaly index per generation (with ν_R): 16 ≡ 0 mod 16
    'ANOMALY_WITH_NU_R': 0,         # anomaly-free
    # Anomaly index per generation (without ν_R): 15 ≡ -1 mod 16
    'ANOMALY_WITHOUT_NU_R': -1,     # equivalently 15 mod 16
    # Observed number of generations
    'N_GENERATIONS': 3,
    # Three-generation anomaly without ν_R: 3×(-1) = -3 mod 16
    'THREE_GEN_ANOMALY': -3,        # equivalently 13 mod 16
    # Modular invariance constraint: c₋ = 8 N_f, c₋ ≡ 0 mod 24
    'CHIRAL_CENTRAL_CHARGE_COEFF': 8,   # c₋ = 8 N_f
    'MODULAR_INVARIANCE_MOD': 24,       # c₋ ≡ 0 mod 24
}


# ════════════════════════════════════════════════════════════════════
# Phase 5z: Electroweak Sector — Measured SM Parameters + ADW Fiducial
#
# Canonical electroweak values (PDG 2024) and fiducial ADW-substrate
# parameters used by the Phase 5z scalar-rung interpretation.
#
# Units: GeV where natural for SM physics; dimensionless elsewhere.
# All values traced via PARAMETER_PROVENANCE (src/core/provenance.py).
# Phase 5z Wave 1 (ScalarRungInterpretation.lean) consumes these via
# src/scalar_rung/.
# ════════════════════════════════════════════════════════════════════

EW_PARAMS = {
    # ── Measured SM electroweak parameters (PDG 2024) ───────────────
    'M_W_GEV': 80.3692,           # W boson mass (GeV/c²), PDG 2024
    'M_Z_GEV': 91.1876,           # Z boson mass (GeV/c²), PDG 2024
    'M_H_GEV': 125.20,            # Higgs boson mass (GeV/c²), PDG 2024 (S. Navas et al., PRD 110, 030001)
    'M_TOP_GEV': 172.57,          # Top quark mass (GeV/c²), PDG 2024 single canonical entry
    'V_EW_GEV': 246.21965,        # EW vacuum expectation value (GeV)
    'SIN2_THETA_W': 0.23121,      # On-shell weak mixing angle sin²θ_W
    'G_FERMI_GEV_M2': 1.1663787e-5,  # Fermi constant (GeV⁻²)
    'ALPHA_EM_INV': 137.035999084,   # Fine structure constant⁻¹ (low-E)
    # Canonical SM dimensionless couplings at M_Z (PDG)
    'G_SU2': 0.6536,              # g = e/sin θ_W at M_Z
    'G_U1Y': 0.3489,              # g' = e/cos θ_W at M_Z (hypercharge)
    # SM Higgs sector phenomenology (tree level)
    'LAMBDA_SM_HIGGS': 0.129,     # λ_SM = m_H²/(2v²) at tree level
    'Y_TOP': 0.9912,              # y_t = √2 m_t/v with m_t = 172.57 GeV (PDG 2024)
    # ── ADW-substrate fiducial values (Wave 1 parameter sweep) ──────
    # These are PROJECTED — not measured, but used as the natural
    # Wetterich / ADW substrate scale choices for the m_H microscopic
    # prediction scan in src/scalar_rung/higgs_prediction.py.
    'LAMBDA_UV_FIDUCIAL_GEV': 1.0e16,  # GUT-like UV cutoff (GeV)
    'N_F_FIDUCIAL': 15,               # SM Weyl fermion count / generation (no ν_R)
    'N_F_WITH_NU_R': 16,              # With ν_R — matches ℤ₁₆ classification
    'G_C_FIDUCIAL': 1.0,              # Critical 4-fermion coupling (dimensionless)
    'LAMBDA_4_FIDUCIAL': 0.13,        # Scalar-channel quartic (near λ_SM_HIGGS)
    # Correctness-push threshold: order-of-magnitude match to m_H = 125 GeV
    'M_H_MATCH_TOLERANCE': 0.5,       # ±50% = "quantitative match"
}


# ════════════════════════════════════════════════════════════════════
# Phase 5z Wave 2: Majorana Rung — Sterile-Neutrino + PMNS parameters
#
# Embedding III (Hybrid) per Lit-Search/Phase-5z O.3 verdict:
# fundamental Lean ν_R : SterileNeutrino with M_R as a Z₁₆-invariant
# condensate scale; Λ_ADW → M_R derivation flagged as a tracked
# hypothesis (open in primary literature).
#
# Oscillation parameters: NuFit-6.0 (Esteban et al., JHEP 12 (2024) 216,
# arXiv:2410.05380), normal ordering (NO), 2024 update.
# 0νββ bounds: KamLAND-Zen 800 (arXiv:2406.11438), LEGEND-1000 PCDR
# (arXiv:2107.11462).
#
# Phase 5z Wave 2 (MajoranaRung.lean, NeutrinoMixing.lean) consumes
# these via src/majorana_rung/.
# ════════════════════════════════════════════════════════════════════

MAJORANA_PARAMS = {
    # ── Type-I seesaw scale (Embedding III: M_R = Λ_ADW open hypothesis) ─
    'M_R_FIDUCIAL_GEV': 1.0e14,           # Fiducial heavy Majorana mass (Type-I seesaw central)
    'M_R_LOWER_BOUND_GEV': 1.0e9,         # Lower edge with y ≈ y_e electron-like Yukawa
    'M_R_UPPER_BOUND_GEV': 1.0e15,        # Upper edge with O(1) Yukawa
    # ── NuFit-6.0 oscillation parameters (NO; 2024 global fit) ──────
    'DELTA_M_SQ_21_EV2': 7.42e-5,         # Δm²_solar (eV²)
    'DELTA_M_SQ_31_EV2': 2.515e-3,        # |Δm²_atm| (eV², NO)
    'THETA_12_DEG': 33.41,                # Solar mixing angle (deg)
    'THETA_13_DEG': 8.54,                 # Reactor mixing angle (deg)
    'THETA_23_DEG': 49.1,                 # Atmospheric mixing angle (deg, NO)
    'DELTA_CP_DEG': 197.0,                # Dirac CP-violating phase (deg)
    # ── 0νββ bounds (existing + projected) ───────────────────────────
    'M_BB_KAMLAND_ZEN_MEV_LOWER': 28.0,   # Most-stringent NME bound (meV)
    'M_BB_KAMLAND_ZEN_MEV_UPPER': 122.0,  # Conservative NME bound (meV)
    'M_BB_LEGEND_MEV_LOWER': 9.0,         # LEGEND-1000 99.7% CL discovery sensitivity (meV)
    'M_BB_LEGEND_MEV_UPPER': 21.0,        # LEGEND-1000 conservative-NME discovery (meV)
    # ── Wave 2 fiducial Yukawa range for seesaw m_ν predictions ──────
    'Y_NU_LOWER': 1.0e-3,                 # Electron-Yukawa-like neutrino Yukawa
    'Y_NU_UPPER': 1.0,                    # O(1) "natural" neutrino Yukawa
    # ── Light neutrino mass scale anchors (from Δm² + lightest = 0) ──
    'M_NU_HEAVIEST_EV': 0.0501,           # √|Δm²_31| ≈ 0.05 eV (NO, m_lightest → 0)
    'M_NU_NEXT_EV': 0.00861,              # √Δm²_21 ≈ 8.61 meV
    # ── Wave 4: Symmetric-Mass-Generation (SMG) substrate-bridge parameters ─
    # Deep-research-anchored values per Lit-Search/Phase-5z/Phase 5z Wave 4 —
    # SMG Substrate Phase Diagram.md §2 (verdict 2026-04-27).
    #
    # The dimensionless ratio c_SMG = Λ_SMG/Λ_UV is the PHYSICAL substrate
    # gap-to-UV-cutoff ratio (NOT the Hasenfratz-Witzel lattice ratio
    # Λ_D/a⁻¹ ≈ 0.13, which is in lattice units). After the project-internal
    # Fierz-translation of HW's g²_GF ≳ 25 onto the V&D 8-coupling NJL
    # scaling (deep research §1.3 + §2.2), the physical c_SMG band lands in:
    #   - Broad NJL envelope:        c_SMG ∈ [10⁻¹², 10⁻³]   (g_eff − g_c ∈ [0.3, 3])
    #   - Seesaw-restricted band:    c_SMG ∈ [10⁻¹⁰, 10⁻⁴]   (requires fine-tuning of
    #                                                          (λ_i) of order 10–30%)
    # Substrate UV anchor: Λ_UV ≈ M_Pl ≈ 10¹⁹ GeV (most natural for ADW substrate).
    # Status: OPEN-AT-LITERATURE-FRONTIER (deep research §1.7, §2.4) — no published
    # source establishes that ADW substrate sits in the HW window; V&D's own
    # mean-field (PRD 86 104019, 2012) tilts NEGATIVE.
    'C_SMG_BROAD_LOWER': 1.0e-12,         # NJL-broad-band lower
    'C_SMG_BROAD_UPPER': 1.0e-3,          # NJL-broad-band upper
    'C_SMG_SEESAW_LOWER': 1.0e-10,        # Seesaw-restricted lower (requires fine-tuning)
    'C_SMG_SEESAW_UPPER': 1.0e-4,         # Seesaw-restricted upper
    'C_SMG_FIDUCIAL': 1.0e-7,             # Geometric mid-band of seesaw-restricted
    'LAMBDA_UV_SMG_FIDUCIAL_GEV': 1.0e19, # M_Pl substrate UV anchor
}


# ════════════════════════════════════════════════════════════════════
# Phase 6c Wave 2: EW Baryogenesis ↔ Chirality Wall bridge parameters
#
# Bridges 5z.3 EWPhaseTransition (transition order) + ChiralityWallMaster
# (Z₁₆ anomaly cancellation) to the SM EWBG verdict.
#
# Sphaleron decoupling threshold: v(T_c)/T_c > 1 (Cohen-Kaplan-Nelson 1993).
# KLRS lattice m_H crossover threshold: m_H = 72.4 ± 1.7 GeV (Csikor-Fodor-
# Heitger 1999, refining KLRS 1996 m_H = 72 ± 2 GeV).
# SM Z₁₆ anomaly representatives:
#   No ν_R: 3 × 15 = 45 ≡ 13 (mod 16) ≠ 0       → wall intact (SMFermionData)
#   With ν_R: 3 × 16 = 48 ≡ 0 (mod 16)          → wall cracks (Z16AnomalyComputation)
# ════════════════════════════════════════════════════════════════════

EWBG_PARAMS = {
    # ── Sphaleron decoupling threshold (Cohen-Kaplan-Nelson) ─────────
    'SPHALERON_DECOUPLING_THRESHOLD': 1.0,    # v(T_c)/T_c > 1 for B-violation freeze-out
    # ── KLRS / CFH lattice EW crossover boundary ─────────────────────
    'KLRS_M_H_CROSSOVER_THRESHOLD_GEV': 72.4, # CFH 1999, refining KLRS 1996
    'KLRS_M_H_CROSSOVER_UNCERTAINTY_GEV': 1.7,
    # ── SM observed Higgs mass (PDG 2024, redundant with EW_PARAMS for EWBG access) ─
    'SM_M_H_GEV': 125.20,
    # ── Z₁₆ anomaly representatives ──────────────────────────────────
    # SM-no-ν_R: 3 generations × 15 components each = 45; 45 mod 16 = 13 (= -3 mod 16).
    'SM_Z16_ANOMALY_NO_NU_R': 13,             # = 3 × 15 mod 16; chirality wall intact
    # SM+3ν_R: 3 × 16 = 48; 48 mod 16 = 0. Chirality wall cracks.
    'SM_Z16_ANOMALY_WITH_3NU_R': 0,
    # ── EWBG verdict thresholds ──────────────────────────────────────
    # SM m_H (125.20 GeV) > KLRS threshold (72.4 GeV) by ~73% → SM transition
    # is crossover at full thermal corrections (KLRS 1996 lattice).
    'M_H_OVERSHOOT_RATIO': 125.20 / 72.4,    # ≈ 1.73; well into crossover
}


# ════════════════════════════════════════════════════════════════════
# Phase 6a Wave 1: Linearized Einstein Equations + emergent G_N
#
# Microscopic G_N from ADW tetrad condensation (Sakharov-Adler induced
# gravity coefficient with ADW-specific dimensionless prefactor α_ADW).
#
#   G_N^emerg = α_ADW · 12π / (N_f · Λ_UV²)         [natural units, GeV⁻²]
#   M_Planck² = 1/G_N^emerg = N_f · Λ_UV² / (12π · α_ADW)
#
# α_ADW = 1 reproduces the textbook Sakharov-Adler one-loop free-fermion
# result. The ADW-specific value awaits Vergeles unitarity computation
# (Lit-Search/Tasks/submitted/Phase6a_W1_vergeles_GN_coefficient.md).
# Until that returns, α_ADW is treated as a tracked-hypothesis parameter
# scanned over the natural range [0.1, 10] (allows ±1 order of magnitude
# from the Sakharov default).
#
# Phase 6a Wave 1 (LinearizedEFE.lean) consumes these via
# src/emergent_gravity/.
#
# References:
# - Sakharov, Sov. Phys. Dokl. 12, 1040 (1968) — induced gravity
# - Adler, Rev. Mod. Phys. 54, 729 (1982) — induced-gravity review
# - Diakonov, arXiv:1109.0091 (2011) — fermionic cosmological term
# - Vladimirov-Diakonov, PRD 86, 104019 (2012) — lattice ADW phases
# - Vergeles, PRD 112, 054509 (2025) — ADW unitarity proof
# ════════════════════════════════════════════════════════════════════

GRAV_PARAMS = {
    # ── Observed Newton's constant (CODATA 2018) ──────────────────────
    # G_N = 6.67430(15) × 10⁻¹¹ m³ kg⁻¹ s⁻² (CODATA 2018 recommended)
    # In natural units (ℏ=c=1, [G_N] = GeV⁻²):
    #   G_N^obs = 1 / M_Planck² = 1 / (1.220890e19 GeV)² ≈ 6.7088e-39 GeV⁻²
    'G_N_OBS_M3_KGM1_S2': 6.67430e-11,    # SI units
    'G_N_OBS_GEV_M2': 6.70883e-39,        # natural units (GeV⁻²)
    'M_PLANCK_GEV': 1.220890e19,          # M_P = √(ℏc/G_N) (CODATA-derived)
    'M_PLANCK_REDUCED_GEV': 2.435e18,     # M̄_P = M_P / √(8π) (reduced)
    # ── Fiducial microscopic-parameter ranges for the G_N scan ───────
    # Λ_UV: scan from 10¹⁰ GeV (intermediate) to 10¹⁹ GeV (super-Planck);
    # natural anchors are GUT (10¹⁶ GeV) and reduced-Planck (2.435e18).
    # Log10 range = 9 decades; finest at the M_Planck cluster.
    'LAMBDA_UV_GEV_LOWER': 1.0e10,
    'LAMBDA_UV_GEV_UPPER': 1.0e19,
    'LAMBDA_UV_GUT_GEV': 1.0e16,          # GUT-adjacent canonical anchor
    'LAMBDA_UV_PLANCK_GEV': 1.220890e19,  # M_P natural anchor
    # N_f: SM Weyl fermion count (matches EW.N_F_FIDUCIAL = 15) with
    # ν_R extension (16 = ℤ₁₆-anomaly-free per generation). For 3 generations,
    # the total Weyl count is 45 or 48. Phase 6a uses per-generation by default.
    'N_F_PER_GEN_NO_NU_R': 15,
    'N_F_PER_GEN_WITH_NU_R': 16,
    'N_F_THREE_GEN_NO_NU_R': 45,
    'N_F_THREE_GEN_WITH_NU_R': 48,
    'N_F_DEFAULT': 15,                    # Per-generation default
    # α_ADW: ADW microscopic coefficient. Sakharov-Adler limit = 1.
    # Vergeles-derived value pending deep research; current tracked
    # hypothesis range [0.1, 10] = ±1 order of magnitude.
    'ALPHA_ADW_SAKHAROV_DEFAULT': 1.0,
    'ALPHA_ADW_LOWER': 0.1,
    'ALPHA_ADW_UPPER': 10.0,
    # ── Sakharov-Adler one-loop coefficient ───────────────────────────
    # G_N = (12π) / (N_f Λ²) is the standard result for N_f Dirac
    # fermions integrated at one loop with hard cutoff Λ. See Adler 1982
    # Eq. (3.3) for the explicit derivation; modern treatment in Visser
    # Mod. Phys. Lett. A17, 977 (2002).
    'SAKHAROV_COEFFICIENT': 12.0 * float(np.pi),  # 12π ≈ 37.699
    # ── Correctness-push tolerance ────────────────────────────────────
    # Order-of-magnitude match: |G_N^emerg − G_N^obs| / G_N^obs < tolerance.
    # 0.5 = ±50% allows for RG-running uncertainty + Vergeles α_ADW O(1).
    # Same tolerance pattern as EW.M_H_MATCH_TOLERANCE.
    'G_N_MATCH_TOLERANCE': 0.5,
}


# ════════════════════════════════════════════════════════════════════
# Phase 6a Wave 4: FLRW cosmological dynamics
#
# Friedmann equations as ODE reduction of the linearized EFE on a
# homogeneous-isotropic background. Cosmological parameters from
# Planck 2018 (TT,TE,EE+lowE+lensing+BAO) for sanity checks.
#
# Phase 6a Wave 4 (FLRWDynamics.lean) consumes these via
# src/emergent_gravity/.
#
# References:
# - Planck Collaboration, A&A 641, A6 (2020) — cosmological parameters
# - Phase 5y Wave 1 q-theory → DESI fit (Lit-Search/Phase-5y/)
# ════════════════════════════════════════════════════════════════════

FLRW_PARAMS = {
    # ── Hubble parameter (Planck 2018 TT,TE,EE+lowE+lensing+BAO) ──────
    'H0_KM_S_MPC': 67.66,                 # km/s/Mpc (Planck 2018, base ΛCDM)
    'H0_INV_S': 2.193e-18,                # H₀ in s⁻¹ (1 km/s/Mpc = 3.241e-20 /s)
    # ── Density parameters (sum to 1 for flat universe) ──────────────
    'OMEGA_M_PLANCK': 0.3111,             # matter
    'OMEGA_LAMBDA_PLANCK': 0.6889,        # cosmological constant
    'OMEGA_R_PLANCK': 9.2e-5,             # radiation (CMB + neutrinos)
    'OMEGA_K_PLANCK': 0.0,                # curvature (flat ΛCDM)
    # ── Critical density ─────────────────────────────────────────────
    # ρ_crit = 3 H₀² / (8π G_N) ≈ 8.62e-27 kg/m³
    'RHO_CRIT_KG_M3': 8.620e-27,
    # ── Equation-of-state defaults (per fluid) ───────────────────────
    'W_MATTER': 0.0,                      # dust
    'W_RADIATION': 1.0/3.0,               # photons + relativistic neutrinos
    'W_LAMBDA': -1.0,                     # cosmological constant
    # ── DESI DR2 dark-energy fit anchor (for Phase 5y cross-reference) ─
    # See Phase 5y QTheoryNoGoTheorem.lean / DESIComparison.lean
    'W_DE_DESI_DR2_TODAY': -0.838,        # w₀ from DESI DR2 (DR2 + CMB + SN)
    'W_A_DESI_DR2': -0.62,                # w_a = dw/dz at z=0 (DESI DR2)
    # ── Friedmann tolerance (Wave 4 correctness checks) ──────────────
    'FLRW_NUMERICAL_TOLERANCE': 1.0e-9,   # Friedmann ODE residual tolerance
}


# ════════════════════════════════════════════════════════════════════
# Phase 6b Wave 2: Cosmological perturbation theory
#
# Linear scalar perturbation theory around an FRW background sourced by
# a `VestigialEOS`-type perfect fluid. The central physical content is
# that perturbations of a fluid with c_s² < 0 grow exponentially
# (`cosh(|c_s|kη)`) rather than oscillating (`cos(c_s kη)`), producing a
# divergent CMB-ℓ angular power spectrum. The Phase 5y H4 result
# `cs_sq_vest(0) = -1/3 < 0` (VestigialEOS.cs_sq_vest_negative_at_zero)
# is the load-bearing input — perturbation theory transmutes the
# DESI-level no-go into a CMB-level falsification.
#
# Phase 6b Wave 2 (CosmologicalPerturbations.lean) consumes these via
# src/cosmological_perturbations/.
#
# References:
# - Planck 2018, A&A 641, A6 (2020) — base ΛCDM cosmological parameters
# - Planck 2018, A&A 641, A6 (2020) Tab. 1 — TT/TE/EE pivot k = 0.05 Mpc⁻¹
# - Mukhanov, *Physical Foundations of Cosmology* (2005), §7-§9
# - Weinberg, *Cosmology* (2008), §6 — linear perturbation theory
# - Lit-Search/Phase-5y/ — VestigialEOS H4 closed-form derivation
# ════════════════════════════════════════════════════════════════════

COSMOLOGICAL_PERTURBATIONS_PARAMS = {
    # ── Planck 2018 CMB pivot + headline parameters (TT,TE,EE+lowE+lensing+BAO) ─
    'K_PIVOT_PLANCK_INV_MPC': 0.05,        # k_pivot = 0.05 Mpc⁻¹ (Planck 2018 Tab. 1)
    'N_S_PLANCK': 0.9649,                  # scalar spectral tilt
    'A_S_PLANCK': 2.10e-9,                 # primordial scalar amplitude at k_pivot
    'SIGMA_8_PLANCK': 0.8120,              # σ₈ from Planck base ΛCDM
    'TAU_REIO_PLANCK': 0.0544,             # optical depth to reionization
    # ── ℓ-space CMB grid for the falsification check ─────────────────
    'ELL_MIN_PLANCK_TT': 2,                # Planck TT covers ℓ ∈ [2, 2500]
    'ELL_MAX_PLANCK_TT': 2500,
    'ELL_PIVOT_FOR_FALSIFICATION': 1500,   # mid-high-ℓ regime where divergence dominates
    # ── Conformal-time anchors (decoupling + today; Mpc) ─────────────
    # η_dec ≈ 280 Mpc / c (recombination), η_0 ≈ 1.4 × 10⁴ Mpc / c (today).
    'ETA_DECOUPLING_MPC': 280.0,           # Mpc (Planck 2018 cosmology)
    'ETA_TODAY_MPC': 1.4e4,                # Mpc
    # ── Sound-speed admissibility threshold (correctness-push anchor) ─
    # A background EOS is "admissible" for a stable CMB spectrum iff
    # c_s² > 0 throughout the relevant evolution window. The vestigial
    # EOS has c_s²(τ=0) = -1/3, so it is non-admissible at the
    # deep-vestigial limit (which is the DESI-relevant regime).
    'CS_SQ_ADMISSIBILITY_THRESHOLD': 0.0,
    # ── Vestigial Jeans frequency (squared) at τ=0 per unit k² ───────
    # ω_J²/k² = c_s²(τ=0) = -1/3 (VestigialEOS.cs_sq_vest_at_zero).
    # Negative ⇒ exponential growth at all sub-horizon scales.
    'OMEGA_J_SQ_OVER_K_SQ_VESTIGIAL_AT_ZERO': -1.0/3.0,
    # ── Growth-rate per unit (k η) for vestigial at τ=0 ──────────────
    # The instability growth rate is √|c_s²| = √(1/3) ≈ 0.5774, so a
    # mode of comoving wavenumber k grows as cosh(0.5774 · k η).
    'GROWTH_RATE_VESTIGIAL_AT_ZERO': (1.0/3.0)**0.5,
    # ── ΛCDM reference: c_s² = 1 (relativistic), oscillatory regime ──
    'CS_SQ_LAMBDA_CDM': 1.0,
    # ── Tolerances ────────────────────────────────────────────────────
    'PERTURBATION_NUMERICAL_TOLERANCE': 1.0e-9,
    # ── Falsification cap (Planck TT cosmic-variance ceiling) ─────────
    # The Planck cosmic-variance-limited fractional uncertainty on
    # ℓ(ℓ+1)C_ℓ/2π at ℓ ~ 1500 is roughly 1%. A growth factor exceeding
    # this ratio at any sub-horizon mode falsifies admissibility.
    'PLANCK_TT_FRACTIONAL_TOLERANCE': 1.0e-2,
}


# ════════════════════════════════════════════════════════════════════
# Phase 6a Wave 2: Gravitational waves
#
# GW propagation speed and dispersion from the vestigial-phase
# susceptibility (VestigialSusceptibility.lean) plus the SK-EFT
# dissipative correction (SecondOrderSK.lean Γ_H). The correctness-
# push anchor is the GW170817 multi-messenger constraint
# |c_GW − c| / c ≲ 7e-16 (Abbott et al. 2017 ApJL 848:L13).
#
# Phase 5y H1 caveat: the second-sound mode of the vestigial fluid
# is NOT derived as a propagating DOF (negative-evidence finding);
# Wave 2 ships in "use-as-identified" mode with the bridge
# encoded as a tracked-hypothesis Prop H_VestigialModeIsGraviton.
#
# Phase 6a Wave 2 (GravitationalWaves.lean) consumes these via
# src/gravitational_waves/.
#
# References:
# - Abbott et al. (LIGO+Virgo+EM), ApJL 848, L13 (2017) — GW170817 c_GW bound
# - Volovik, JETP Lett. 119, 564 (2024) — vestigial second-sound framing
# - Phase 5y H1 deep research (Lit-Search/Phase-5y/Phase5y_H1_second_sound_graviton.md)
# ════════════════════════════════════════════════════════════════════

GW_PARAMS = {
    # ── Speed of light (natural units; SI separately for sanity checks) ─
    'C_LIGHT_M_S': 2.99792458e8,           # SI (defined exactly)
    # ── GW170817 deviation bound (Abbott et al. 2017) ────────────────
    # Combined arrival-time analysis: −3 × 10⁻¹⁵ ≤ Δc/c ≤ +7 × 10⁻¹⁶.
    # Conservative two-sided cap |Δc/c| ≤ 3e-15 used as the
    # falsification ceiling in correctness-push theorems.
    'C_GW_DEVIATION_UPPER_BOUND': 7.0e-16,    # most stringent (+) side
    'C_GW_DEVIATION_LOWER_BOUND': -3.0e-15,   # (−) side
    'C_GW_TWO_SIDED_CAP': 3.0e-15,            # symmetric falsification cap
    # ── Vestigial-phase susceptibility natural ranges ─────────────────
    # χ_vest is the metric-channel susceptibility from
    # VestigialSusceptibility.lean (chi_RPA closed form).
    # The "natural" range = within 1 order of magnitude of unity in
    # dimensionless form χ_vest · Λ², i.e. consistent with the RPA
    # bubble integral being O(Λ²/16π²) per Vergeles 2025.
    'CHI_VEST_NATURAL_LOWER': 0.1,
    'CHI_VEST_NATURAL_UPPER': 10.0,
    'CHI_VEST_DEFAULT': 1.0,
    # ── Frequency window (LIGO + cross-instrument) ───────────────────
    # LIGO sensitivity: 10 Hz – 10 kHz. GW170817 inspiral peak ≈ 100 Hz.
    'GW_FREQ_HZ_LOWER': 10.0,
    'GW_FREQ_HZ_UPPER': 1.0e4,
    'GW170817_PEAK_FREQ_HZ': 100.0,        # inspiral peak
    'GW_FREQ_HZ_PROBE': 100.0,             # probe frequency for dispersion
    # ── Dissipative correction scale (SK-EFT cross-link) ──────────────
    # SecondOrderSK.lean Γ_H = (γ₁+γ₂)(κ/c_s)². For GW propagation,
    # the analog κ is the inverse coherence scale of the vestigial
    # background; c_s → c_GW. The ratio Γ_H · ω / c_GW² is the
    # dimensionless dispersion correction at frequency ω.
    'GAMMA_H_VESTIGIAL_DEFAULT': 1.0e-30,  # placeholder (vestigial regime, ≪ obs)
    # ── Correctness-push tolerance ────────────────────────────────────
    # Wave 2 correctness-push: |c_GW − c|/c ≤ tolerance.
    # Tolerance set to GW170817 two-sided cap.
    'C_GW_MATCH_TOLERANCE': 3.0e-15,
}


# ════════════════════════════════════════════════════════════════════
# Phase 6a Wave 3: Bekenstein-Hawking entropy from MTC state counting
#
# S_BH = A/(4 G_N) − (3/2) log(A/(4 G_N)) + c_0 + O(A⁻¹)
#
# Wave 3 ships in Outcome-3 mode (tracked-hypothesis) for the general
# MTC case, with a SU(2)_k Kaul-Majumdar specialization sub-corollary
# (Outcome-2, Conditional). Per the Lit-Search/Phase-6a deep-research
# return (2026-04-25), no published derivation pins a specific Modular
# Tensor Category at a 4D BH horizon in an ADW substrate. The Kaul-
# Majumdar SU(2)_k Verlinde-formula route is the only equation-level
# closed form yielding the −3/2 log coefficient (½ Gaussian saddle +
# 1 SU(2)-singlet projection); the leading 1/4 prefactor is a tuning
# (Immirzi parameter γ), not a derivation. Sen 2013 (arXiv:1205.0971)
# explicitly disagrees with −3/2 for 4D Schwarzschild pure gravity, so
# −3/2 universality is restricted to the Cardy-saddle subfamily.
#
# Phase 6a Wave 3 (BHEntropyMicroscopic.lean) consumes these via
# src/bh_entropy/.
#
# References:
# - Kaul-Majumdar, PRL 84, 5255 (2000), arXiv:gr-qc/0002040
# - Kaul, SIGMA 8, 005 (2012), arXiv:1201.6102 (review with full eqs)
# - Domagala-Lewandowski, CQG 21, 5233 (2004), arXiv:gr-qc/0407051
# - Meissner, CQG 21, 5245 (2004), arXiv:gr-qc/0407052
# - Walker-Wang, Front. Phys. 7, 150 (2012), arXiv:1104.2632
# - Sen, JHEP 04, 156 (2013), arXiv:1205.0971 (heat-kernel disagreement)
# - Solodukhin, Living Rev. Rel. 14, 8 (2011), arXiv:1104.3712
# - Bombelli-Koul-Lee-Sorkin, PRD 34, 373 (1986) (entanglement origin)
# - Jacobson, arXiv:gr-qc/9404039 (induced gravity / BH entropy)
# ════════════════════════════════════════════════════════════════════

BH_ENTROPY_PARAMS = {
    # ── Planck length (CODATA 2018) ───────────────────────────────────
    # ℓ_P = √(ℏ G/c³) = 1.616255(18) × 10⁻³⁵ m. Sets the area scale
    # in S_BH = A/(4 ℓ_P²) for the leading prefactor.
    'PLANCK_LENGTH_M': 1.616255e-35,
    'PLANCK_AREA_M2': 2.6121e-70,         # ℓ_P² (CODATA-derived)
    # ── BH entropy leading coefficient (Bekenstein-Hawking) ──────────
    # The 1/4 in S = A/(4 G_N) is Bekenstein 1973 + Hawking 1975. In the
    # Kaul-Majumdar / Carlip / Solodukhin family it is a *tuning*: the
    # Immirzi parameter γ, the periodicity β, or the entanglement cutoff
    # ε is fixed by demanding the leading area coefficient equal 1/4.
    # Wave 3 encodes 1/4 as a hypothesis-discharge (`immirziTuning`),
    # NOT as a derived theorem.
    'BH_ENTROPY_LEADING_COEFFICIENT': 0.25,
    # ── Immirzi parameter values (Kaul-Majumdar / LQG literature) ────
    # Distinct counting prescriptions yield distinct γ with the same
    # −3/2 log coefficient. Per arXiv:1201.6102 §5 the −3/2 is structural
    # while γ is scheme-dependent.
    'IMMIRZI_GAMMA_DOMAGALA_LEWANDOWSKI': 0.23753295796592,  # gr-qc/0407051
    'IMMIRZI_GAMMA_MEISSNER': 0.27392803876474,              # gr-qc/0407052
    'IMMIRZI_GAMMA_DEFAULT': 0.27392803876474,               # Meissner (recent)
    # ── Log-correction structural coefficient ────────────────────────
    # c_log = −1/2 (Gaussian saddle) − 1 (SU(2) singlet projection from
    # I_0 − I_1 cancellation) = −3/2. Universal within the Cardy-saddle
    # / single-CFT / microcanonical / A-independent-c family. Sen 2013
    # (arXiv:1205.0971) heat-kernel result for 4D Schwarzschild gives
    # +(212/45 − 3) ln a ≈ +1.71 ln a — explicit disagreement.
    'LOG_CORRECTION_KAUL_MAJUMDAR_SU2K': -1.5,
    'LOG_CORRECTION_GAUSSIAN_SADDLE': -0.5,
    'LOG_CORRECTION_SINGLET_PROJECTION': -1.0,
    'LOG_CORRECTION_SEN_4D_SCHWARZSCHILD': 1.7111111,        # 212/45 - 3
    # ── MTC zoo (formalized in SU2kFusion / IsingBraiding / ...) ─────
    # Quantum dimensions + global dim D² used by the area-law leading
    # coefficient ansatz κ_C ∝ log d_max^C.
    # Fibonacci (FibonacciMTC.lean): φ = (1+√5)/2 ≈ 1.618
    'FIBONACCI_PHI': 1.6180339887498948,
    'FIBONACCI_GLOBAL_DIM_SQ': 3.6180339887498949,           # 1 + φ² = 2 + φ
    'FIBONACCI_LOG_D_MAX': 0.4812118250596034,               # log φ
    # Ising (IsingBraiding.lean): {1, σ, ψ}, d = {1, √2, 1}, D² = 4
    'ISING_GLOBAL_DIM_SQ': 4.0,
    'ISING_D_SIGMA': 1.4142135623730951,                     # √2
    'ISING_LOG_D_MAX': 0.34657359027997264,                  # (1/2) log 2
    'ISING_EDGE_C_MOD8': 0.5,                                # chiral c_-
    # Toric code (abelian — falsifier instance: d_a = 1 ∀a)
    'TORIC_CODE_GLOBAL_DIM_SQ': 4.0,
    'TORIC_CODE_LOG_D_MAX': 0.0,                             # all d_a = 1
    # D(S₃) (S3CenterAnyons.lean): 8 anyons, d = 1,1,2,3,3,2,2,2; D² = 36
    'DS3_GLOBAL_DIM_SQ': 36.0,
    'DS3_LOG_D_MAX': 1.0986122886681098,                     # log 3
    # SU(2)_k for k ∈ {2, 3, 4} — k=2 reproduces Ising via SU(2)/Z₂.
    # D²(SU(2)_k) = (k+2)/(2 sin²(π/(k+2))). Computed inline in tests.
    # ── Falsifier thresholds ─────────────────────────────────────────
    # F2 (area-law leading scaling): κ > 0 required. Abelian MTCs all
    # have d_max = 1 ⇒ log d_max = 0 ⇒ κ = 0 ⇒ F2 falsifies.
    'AREA_LAW_KAPPA_MIN_POSITIVE': 1.0e-12,                  # numerical pos cap
    # F4 (modular invariance): horizon S, T must satisfy (ST)³ = S² and
    # S² = (charge conjugation). Tested per-MTC via SU2kFusion.
    # F5 (anomaly-match mod 8): bulk-Z₂ → boundary chiral c_- mod 8.
    # ── Correctness-push tolerance ───────────────────────────────────
    # Coefficient match: |κ_leading − 1/(4 G_N^emerg)| / [1/(4 G_N)] < tol.
    # 0.10 = ±10% to absorb Immirzi-tuning O(1) ambiguity (DL vs Meissner).
    'BH_ENTROPY_COEFFICIENT_MATCH_TOLERANCE': 0.10,
    # Log-correction match: tolerance on c_log against −3/2 anchor.
    # Tighter (0.01) because c_log is structural, not tuned.
    'LOG_CORRECTION_MATCH_TOLERANCE': 0.01,
    # ── Horizon-area natural anchors (for the asymptotic regime) ─────
    # A/(4 ℓ_P²) ≫ 1 is required for the Kaul-Majumdar saddle to apply.
    # Solar-mass Schwarzschild: r_s = 2.95 km, A ≈ 1.09e8 m², A/(4 ℓ_P²) ≈ 1.04e77.
    'HORIZON_AREA_LOG_LOWER': 10.0,           # log(A/(4 ℓ_P²)) lower for asymptotic regime
    'HORIZON_AREA_LOG_UPPER': 80.0,           # log(A/(4 ℓ_P²)) ≈ solar-mass BH
    # SU(2)_k natural-range scan
    'SU2K_LEVEL_LOWER': 2,
    'SU2K_LEVEL_UPPER': 10,
}


# ════════════════════════════════════════════════════════════════════
# Phase 6a Wave 5: BH Thermodynamics Four Laws + Regime Partition
# ════════════════════════════════════════════════════════════════════
# References:
# - Jacobson & Volovik, PRD 58, 064021 (1998), arXiv:cond-mat/9801308
#   (§VIII verbatim "BHs cool toward extremality")
# - Jacobson & Koike, in Artificial Black Holes (World Sci. 2002),
#   arXiv:cond-mat/0205174, Eq. (13): T_H(v) = T_H(0)(1 - v²/c_⊥²)
# - Volovik, Found. Phys. 33, 349 (2003), arXiv:gr-qc/0301043
#   (horizon fermion zero modes)
# - Glorioso & Liu, arXiv:1612.07705 (SK-EFT 2nd law from KMS Z₂)
# - Kehle & Unger, J. Eur. Math. Soc. (2025), arXiv:2211.15742
#   (third-law disproof)
# - Reall, PRD 110, 124059 (2024), arXiv:2410.11956 (BPS restoration)
# ════════════════════════════════════════════════════════════════════

BH_THERMODYNAMICS_PARAMS = {
    # ── Critical-mass natural-range scan (M_c ansatz) ─────────────────
    # Default M_c = (N_f * Λ_UV) / (12π * α_ADW). Wave 5 deep-research §3
    # dimensional analysis; not pinned by any published primary source.
    # Inherits Wave 1 natural ranges for α_ADW, Λ_UV, N_f.
    'M_C_PREFACTOR': 12.0,                   # 12π denominator factor
    # Natural range for α_ADW from Wave 1 (Vergeles range):
    'ALPHA_ADW_LOWER': 0.1,
    'ALPHA_ADW_UPPER': 10.0,
    # BEC-acoustic T_H,0 prefactor (Balbinot 2005 leading-order initial
    # temperature in natural units). Replaces the deleted SCHOTTKY_*
    # entries from the initial Wave 5 ship per the post-rewrite
    # provenance correction (see
    # papers/AutomatedReviews/2026-04-26-2230-wave5-process/
    # deep_research_analog_conflation.md).
    'T_H_INITIAL_DEFAULT': 1.0,              # natural-units T_H,0 = 1
    # χ_vest natural range from Wave 2 (vestigial-susceptibility scan)
    'CHI_VEST_LOWER': 0.1,
    'CHI_VEST_UPPER': 10.0,
    # Substrate-response coefficient ansatz: δ_ADW = (α_ADW − 1) · Λ_UV
    # (deep-research §9; vanishes in bare Sakharov-Adler limit α_ADW = 1)
    'DELTA_ADW_VANISHES_AT': 1.0,            # α_ADW value for which δ = 0
    # Davies-style classical sign-flip critical ratios (for cross-comparison;
    # NOT used for the ADW partition itself).
    'DAVIES_KERR_J_OVER_M_SQ': 0.6814,       # √(2√3 − 3); Kerr J/M² sign-flip
    'DAVIES_RN_Q_OVER_M': 0.8660,            # √3/2; RN Q/M sign-flip
    # Hawking-Page transition (AdS extension, not ADW-default):
    'HAWKING_PAGE_R_PLUS_OVER_L': 1.0,       # r_+/l = 1 at HP transition
    'HAWKING_PAGE_FOLD_RATIO': 0.5774,       # 1/√3 small/large fold
    # BEC-acoustic decay-form falsifier tolerance (Balbinot Eq. Tsonic
    # strict-monotone-decay deviation; non-strict-decreasing candidates
    # falsify the BEC-acoustic regime identification).
    'ACOUSTIC_DECAY_FALSIFIER_TOLERANCE': 0.01,  # 1% relative deviation
    # Third-law form: BPS-violating-matter Kehle-Unger threshold
    # (T_H_threshold for finite-time approach claim, dimensionless)
    'THIRD_LAW_FINITE_TIME_THRESHOLD': 1.0e-12,
    # Weak-Nernst lower bound: extremal entropy must exceed this
    # (per Wave 3 Kaul-Majumdar S(M_c) > 0 for non-abelian MTCs)
    'WEAK_NERNST_S_EXTREMAL_LOWER': 0.0,     # strict positivity
}


# ════════════════════════════════════════════════════════════════════
# Phase 6e Wave 1: Seeley-DeWitt Heat-Kernel Expansion
#
# Coefficients of the asymptotic expansion of the Dirac heat kernel
# Tr exp(-τ D̸²) ~ Σ_n a_n(x) τ^{(n-d)/2} as τ → 0+ on a 4D Riemannian
# manifold. Standard textbook values for a free Dirac fermion with no
# gauge field, no torsion (the bare ADW substrate at mean field):
#
#   a_0 = 4 N_f / (4π)²                         [coefficient of Λ⁴ → Λ_emerg]
#   a_2 = - N_f R / (12 (4π)²)                  [coefficient of Λ² → 1/(16π G_N)]
#   a_4 = N_f / (180 (4π)²) ·                   [order log(Λ) — 4D Weyl-anomaly]
#         (-12 R_μνρσ R^μνρσ + 7 R_μν R^μν - 5 R²)/12
#                                               [Christensen-Duff convention]
#
# Cross-calibration: integrating Λ²·a_2 over volume gives the
# Einstein-Hilbert coefficient -(1/(16π G_N)) ∫ R √g d⁴x, fixing
#   G_N^Sakharov = 12π / (N_f Λ²)
# in exact agreement with Phase 6a.1 LinearizedEFE.G_N_sakharov.
# The structural identity is the load-bearing correctness-push anchor
# (Decision Gate E.2): a_2 ↔ G_N^emerg consistency at 6a.1's α_ADW = 1
# baseline ⇒ mean-field validity within the natural-parameter band.
#
# References:
# - Gilkey, "Invariance Theory, the Heat Equation, and the Atiyah-Singer
#   Index Theorem" (CRC Press, 2nd ed., 1995) — canonical reference,
#   Theorem 3.3.1 (Dirac coefficients), Corollary 4.8.16 (4D coefficients)
# - Vassilevich, Phys. Rep. 388, 279 (2003) — modern review, §4 (Dirac
#   spinors), Eqs. (4.37)–(4.42)
# - Christensen-Duff, Nucl. Phys. B154, 301 (1979) — explicit a_4 for
#   spin-1/2
# - Avramidi, Heat Kernel and Quantum Gravity (Springer, 2000) — physics
#   conventions used here
# - Adler, Rev. Mod. Phys. 54, 729 (1982) — induced-gravity coefficient
#   matching to Sakharov-Adler
# - Phase 6a.1 LinearizedEFE.lean — calibration target G_N_sakharov
# ════════════════════════════════════════════════════════════════════

HEAT_KERNEL_PARAMS = {
    # ── Dirac trace dimension ─────────────────────────────────────────
    # tr 𝟙_4 = 4 (Dirac-spinor index in 4D); per fermion species the
    # leading a_0 term carries this multiplicity.
    'DIRAC_TRACE_DIM': 4,
    # ── Seeley-DeWitt coefficients for a free Dirac spinor ────────────
    # In 4D vacuum, with E = R/4 endomorphism in D̸² = -∇² + R/4 - …
    # (Lichnerowicz), the standard rational coefficients are:
    'A0_DIRAC_RATIONAL': 4.0,                # tr 𝟙_4 = 4
    'A2_DIRAC_R_COEF': -1.0/12.0,            # coef of N_f R / (4π)² in a_2
    'A4_DIRAC_R_SQ_COEF': -5.0/(12.0*180.0), # = -1/432 (R² piece)
    'A4_DIRAC_RICCI_SQ_COEF': 7.0/(12.0*180.0),    # = 7/2160 (R_μν R^μν)
    'A4_DIRAC_RIEMANN_SQ_COEF': -12.0/(12.0*180.0),# = -1/180 (R_μνρσ R^μνρσ)
    # ── (4π)² normalization (canonical heat-kernel measure) ───────────
    # The (4π)^(-d/2) factor in the τ → 0 asymptotic comes from the
    # Gaussian integral on the cotangent space.  In 4D this is (4π)².
    'FOUR_PI_SQ': float((4.0 * np.pi) ** 2),  # (4π)² ≈ 157.91367
    # ── Sakharov-Adler calibration factor ─────────────────────────────
    # G_N^Sakharov = 12π / (N_f Λ²) (cf. GRAV_PARAMS.SAKHAROV_COEFFICIENT)
    # appears here as the value 1/(16π G_N) = N_f Λ² / (12 · 16π²) =
    # N_f Λ² / (192 π²); the prefactor 192 π² = 12 (4π)² is the link.
    'EH_PREFACTOR_TWELVE_FOUR_PI_SQ': 12.0 * float((4.0 * np.pi) ** 2),
    # ── Mean-field validity band on a_2 vs G_N^emerg (correctness-push) ─
    # Decision Gate E.2: a_2 calibration matches 6a.1 G_N_sakharov *exactly*
    # at α_ADW = 1; the "natural-parameter band" matches within ±50%
    # (matches GRAV_PARAMS.G_N_MATCH_TOLERANCE).
    'A2_GN_MATCH_TOLERANCE': 0.5,
    # ── Gauss-Bonnet sanity coefficient ───────────────────────────────
    # In 4D the Euler density 𝒢 = R² - 4 R_μν R^μν + R_μνρσ R^μνρσ is
    # topological; checking the Dirac a_4 contains it with the right
    # rational coefficient is a structural sanity test.
    'GAUSS_BONNET_R_SQ': 1.0,
    'GAUSS_BONNET_RICCI_SQ': -4.0,
    'GAUSS_BONNET_RIEMANN_SQ': 1.0,
}


# ════════════════════════════════════════════════════════════════════
# Phase 6e Wave 2 — Higher-Curvature Structure
# ════════════════════════════════════════════════════════════════════
# Parameters for the 3-scalar curvature basis at a_4 order:
#   {R², R_μν R^μν, R_μνρσ R^μνρσ}
# In 4D, the Gauss-Bonnet density
#   𝒢 = R² − 4 R_μν R^μν + R_μνρσ R^μνρσ
# is topological (Euler density), so only TWO physical combinations
# survive in the local effective Lagrangian.  Conventional choices:
#   {R², C²}  with  C² = R_μνρσ² − 2 R_μν² + (1/3) R²  (Weyl-squared)
# We use C² + (R²/3) basis.
#
# References:
# - Stelle, Phys. Rev. D 16, 953 (1977) — renormalizable R + αR² + βC²
# - Donoghue, Phys. Rev. D 50, 3874 (1994) — leading-log effective
#   action coefficients
# - Calmet, Capozziello & Pryer, EPJC 77, 589 (2017) [arXiv:1708.08253]
#   — EFT framework for translating Eöt-Wash + Cassini constraints to
#   dimensionless α, β bounds in the Stelle truncation
# - Berti et al., Class. Quantum Grav. 32, 243001 (2015) [arXiv:1501.07274]
#   — GW & binary-pulsar bounds in modified gravity
# - Phase 6e Wave 1 HeatKernelExpansion.lean — supplies the
#   microscopic Dirac a_4 coefficients (input to this wave)
# ════════════════════════════════════════════════════════════════════

HIGHER_CURVATURE_PARAMS = {
    # ── 3-scalar curvature basis indices ─────────────────────────────
    # Each entry maps a basis-element name to its rational coefficient
    # in Wave 1's Dirac a_4 (per N_f fermion species, in units of the
    # canonical (4π)² heat-kernel measure).  These reproduce the values
    # in HEAT_KERNEL_PARAMS — duplicated here for downstream clarity.
    'A4_R_SQ_PER_NF':       -5.0/(12.0*180.0),  # = -1/432  (R² piece)
    'A4_RICCI_SQ_PER_NF':    7.0/(12.0*180.0),  # =  7/2160 (R_μν² piece)
    'A4_RIEMANN_SQ_PER_NF': -12.0/(12.0*180.0), # = -1/180  (R_μνρσ² piece)
    # ── Gauss-Bonnet 4D coefficients ─────────────────────────────────
    # 𝒢 = R² - 4 R_μν² + R_μνρσ²  (Euler density, topological in 4D)
    'GB_R_SQ_COEF':       1.0,
    'GB_RICCI_SQ_COEF':  -4.0,
    'GB_RIEMANN_SQ_COEF': 1.0,
    # ── Weyl-squared decomposition (4D) ──────────────────────────────
    # C² = R_μνρσ² - 2 R_μν² + (1/3) R²
    # Equivalently:  R_μνρσ² = C² + 2 R_μν² - (1/3) R²
    'WEYL_SQ_FROM_RIEMANN_SQ': 1.0,
    'WEYL_SQ_FROM_RICCI_SQ': -2.0,
    'WEYL_SQ_FROM_R_SQ':      1.0/3.0,
    # ── SM-fermion count for predicted-coefficient evaluation ────────
    # Standard Model: 6 quarks × 3 colors + 6 leptons + 3 ν_R = 27.
    # Conservative reference: 24 (no ν_R).  The microscopic prediction
    # depends linearly on N_f.
    'N_F_STANDARD_MODEL':       24,
    'N_F_STANDARD_MODEL_NU_R':  27,
    # ── Observational upper bounds on dimensionless higher-curvature
    #     coefficients in the EFT Lagrangian
    #         L = (1/16π G_N) [ R + α R² + β C² ]
    #     Bounds expressed as |α|, |β| ≲ <value> after dimensional
    #     reduction and converting Yukawa-mediator masses to
    #     dimensionless coefficients in natural units.  Values are
    #     order-of-magnitude — exact numeric anchors used by the
    #     correctness-push theorem.
    'HC_BOUND_LIGO_C_SQ':    1.0e62,  # GW170817 + LIGO/Virgo speed-of-graviton
    'HC_BOUND_PULSAR_C_SQ':  1.0e59,  # binary pulsar period decay (Hulse-Taylor)
    'HC_BOUND_SRG_R_SQ':     1.0e61,  # Eöt-Wash short-range gravity (50 μm)
    'HC_BOUND_CASSINI_C_SQ': 1.0e62,  # post-Newtonian solar-system
    # ── Microscopic-vs-observational pass band (correctness-push) ────
    # Predicted coefficients from Wave 1 with N_f ∈ [SM, SM+ν_R] are
    # O(N_f / (180·(4π)²)) ≈ O(10⁻³).  The pass band rejects any
    # microscopic prediction exceeding the loosest observational bound.
    'HC_PASS_BAND_FACTOR': 0.5,  # consistent with GRAV_PARAMS / HEAT_KERNEL_PARAMS
}


# ════════════════════════════════════════════════════════════════════
# Phase 6e Wave 3 — Nonlinear Diffeomorphism Invariance (path-b)
# ════════════════════════════════════════════════════════════════════
# Parameters for the path-b direct check that the heat-kernel effective
# Lagrangian is diffeomorphism-invariant order-by-order in the
# Seeley-DeWitt expansion (orders a_0, a_2, a_4).
#
# Path-(b) framework (Wald, *General Relativity*, App. E.1):
#   For any scalar density L built from polynomial scalar curvature
#   invariants {1, R, R², R_μν R^μν, R_μνρσ R^μνρσ} (equivalently
#   {1, R, R², C², 𝒢} in Stelle's basis), the variation under an
#   infinitesimal coordinate transformation x^μ → x^μ + ξ^μ is a total
#   divergence:
#       δ_ξ (√g L) = ∂_μ(ξ^μ √g L)
#   so the action ∫ √g L is diff-invariant on a closed manifold.
#
# The "path-b anomaly residual" at order n is the algebraic mismatch
# between the same density expressed in two equivalent scalar-invariant
# bases (Wave 2 main identity for order a_4):
#       residual_n(L, B₁, B₂)
#         := L_density_in_B₁ - L_density_in_B₂
# For a Wave 1 Christensen-Duff Dirac coefficient bundle, residual_n
# vanishes identically at orders 0, 2, 4 (Wave 2 basis-change theorem
# `a4_density_eq_a4_density_in_RC2GB_basis` for order 4).
#
# References:
# - Wald, *General Relativity*, App. E.1 — diff invariance via Lie
#   derivatives + total divergences
# - Vassilevich, Phys. Rep. 388, 279 (2003), §3.1 — covariance of
#   heat-kernel coefficients under coordinate transformations
# - Phase 6e Wave 1 HeatKernelExpansion.lean — Christensen-Duff
#   Dirac coefficient bundle (input)
# - Phase 6e Wave 2 HigherCurvatureStructure.lean — Stelle basis
#   change at order a_4 (path-b consistency at the basis-change level)
# ════════════════════════════════════════════════════════════════════

DIFF_INVARIANCE_PARAMS = {
    # ── Order list at which path-b diff invariance is checked ─────────
    # Heat-kernel orders covered by Wave 1 (a_0, a_2) + Wave 2 (a_4).
    # Higher orders (a_6, …) are out of scope for the mean-field 6e
    # program (see strategy doc §15).
    'ORDER_LIST': (0, 2, 4),
    # ── Path-b anomaly residual tolerance ─────────────────────────────
    # The residual is exactly zero algebraically; the float threshold
    # accommodates numerical evaluation only (machine ε margin).
    'PATH_B_RESIDUAL_TOLERANCE': 1.0e-12,
    # ── Test-grid extent for parameter-scan diff-invariance check ─────
    # Curvature-invariant inputs span ranges representative of the
    # heat-kernel τ → 0 regime (small curvature at the cutoff scale).
    # The Ricci scalar R itself is exercised structurally at order a₂
    # but contributes nothing to the order-a₄ residual computation —
    # so no R grid range is declared here.
    'TEST_GRID_RICCI_SQ_RANGE':  (0.0, 50.0),
    'TEST_GRID_RIEMANN_SQ_RANGE':(0.0, 25.0),
    'TEST_GRID_N_F_RANGE':       (1, 27),
    'PARAMETER_SCAN_POINTS':     16,
    # ── Falsifier offset for the anomaly-hunt check ───────────────────
    # The path-b "anomaly hunt" probe shifts a single coefficient by
    # ANOMALY_PROBE_OFFSET to verify the path-b residual responds
    # linearly: a non-admissible bundle yields nonzero residual.
    'ANOMALY_PROBE_OFFSET': 1.0e-6,
    # ── Admissible-class predicate ────────────────────────────────────
    # An "admissible" effective Lagrangian (in the Wave 3 sense) is one
    # whose density is a polynomial in the canonical scalar curvature
    # invariants {1, R, R², R_μν², R_μνρσ²}.  All Wave 1 + Wave 2
    # objects fall in this class; the falsifier deliberately places a
    # coefficient outside it.
    'ADMISSIBLE_BASIS_CARDINALITY': 5,  # |{1, R, R², R_μν², R_μνρσ²}|
}


# ════════════════════════════════════════════════════════════════════
# Phase 6e Wave 4 — Nonlinear Einstein Field Equations from ADW
# ════════════════════════════════════════════════════════════════════
# Parameters for the variational EFE
#   δS/δe^a_μ = 0  →  G_μν + α_HC · (a_4-correction)_μν = 8π G_N · T_emerg_μν
# at the *trace level* (each side a scalar formed from curvature
# invariants; restriction of the full tensor EFE that preserves the
# substantive content while fitting the project's algebraic-coefficient
# Lean infrastructure — manifold/index machinery deferred to Phase 6f).
#
# Wave 1 supplies G_N and the a_4 coefficients; Wave 2 supplies the
# sign-definite higher-curvature basis; Wave 3 confirms diff invariance
# (Decision Gate E.3 PASS) — so the variational EOM is well-posed.
# This wave produces:
#   1. Closed-form trace-level EFE residual on the Dirac bundle
#   2. Emergent stress-energy `T_emerg(ρ_ADW, p_ADW, α_ADW)` parametrised
#      by the ADW substrate density / pressure and the Vergeles α_ADW
#   3. Observable signatures:
#        - light deflection δθ = 4 G_N M / b · α_ADW
#        - perihelion precession ratio
#        - ringing-frequency shift δω/ω
#      All proportional to (α_ADW − 1) · GR baseline; vanishes at α_ADW = 1.
#
# References:
# - Wald, *General Relativity*, §4.2 — variational derivation of EFE
# - Will, *Theory and Experiment in Gravitational Physics* (2nd ed., 2018)
#   — observational tests, post-Newtonian formalism, deflection +
#   perihelion + ringing constraints
# - Vergeles, PRD 112, 054509 (2025) — α_ADW positivity (P1, P2, P3 of 6a.1)
# - Phase 6a.1 LinearizedEFE.lean — G_N_emerg, G_N_emerg_at_alpha_one
# - Phase 6e Wave 1 HeatKernelExpansion.lean — G_N from a_2, a_4 basis
# - Phase 6e Wave 2 HigherCurvatureStructure.lean — Stelle (α, β, γ) basis
# - Phase 6e Wave 3 NonlinearDiffInvariance.lean — well-posedness guarantee
# ════════════════════════════════════════════════════════════════════

NONLINEAR_EFE_PARAMS = {
    # ── α_ADW calibration band ───────────────────────────────────────
    # Per LinearizedEFE.G_N_emerg: G_N_emerg = α_ADW · G_N_sakharov.
    # Decision Gate E.2 anchored α_ADW = 1 as the Sakharov-Adler
    # baseline (heat-kernel a_2 ↔ G_N_emerg agreement). Wave 4
    # observable signatures vanish at α_ADW = 1 by construction;
    # the natural-parameter band is [0.1, 10] (covers SM N_f).
    'ALPHA_ADW_CALIBRATED': 1.0,
    'ALPHA_ADW_NATURAL_MIN': 0.1,
    'ALPHA_ADW_NATURAL_MAX': 10.0,
    # ── EFE residual tolerance ───────────────────────────────────────
    # Algebraic identity at the closed form; float threshold accounts
    # only for FP roundoff in trace-level scans. Same scale as
    # PATH_B_RESIDUAL_TOLERANCE for cross-wave consistency.
    'EFE_RESIDUAL_TOLERANCE': 1.0e-12,
    # ── T_emerg vs T_matter deviation channel ────────────────────────
    # At α_ADW ≠ 1, T_emerg_trace − T_matter_trace = (α_ADW − 1) · ρ_ADW
    # (substrate-amplitude channel). The "observable detection" band
    # rejects detections smaller than 0.5% — sets the resolution floor
    # for any post-Newtonian constraint test.
    'T_EMERG_DEVIATION_DETECT_FLOOR': 5.0e-3,  # 0.5% deviation floor
    # ── Observable-signature scales (representative astrophysical) ────
    # Light deflection at solar limb (Eddington 1919 + GW170817 calib):
    #   δθ_GR_solar = 4 G_N M_sun / b_sun = 1.751 arcsec
    # We store as a dimensionless ratio (δθ / δθ_GR) so the prediction
    # depends only on α_ADW in the Wave 4 formula.
    'DEFLECTION_GR_BASELINE_ARCSEC': 1.751,  # Will 2018 §4.1
    'DEFLECTION_OBS_RELATIVE_PRECISION': 3.0e-4,  # Will 2018 Table 3 (radio VLBI)
    # Perihelion precession of Mercury (per orbit, GR baseline):
    #   δφ_GR = 6π G_N M_sun / [a (1 - e²) c²] = 42.98 arcsec/century
    'PERIHELION_GR_BASELINE_ARCSEC_PER_CENTURY': 42.98,  # Will 2018 §4.2
    'PERIHELION_OBS_RELATIVE_PRECISION': 1.0e-4,  # MESSENGER + planetary radar
    # GW ringdown frequency (Schwarzschild fundamental ℓ=2 mode):
    #   ω_R · GM/c³ = 0.3737  (Berti et al. CQG 26:163001 (2009), Table III)
    'RINGDOWN_GR_BASELINE_DIMENSIONLESS': 0.3737,
    'RINGDOWN_OBS_RELATIVE_PRECISION': 0.05,  # GWTC-3 spectroscopy (Isi et al.)
    # ── Representative-background test list ──────────────────────────
    # Trace-level EFE evaluated at three benchmark backgrounds. Each
    # contributes a different (R, R², R_μν², R_μνρσ²) tuple; the EFE
    # residual must vanish on all three for the Dirac-bundle-balanced
    # configuration.
    'BENCHMARK_BACKGROUNDS': ('Schwarzschild', 'de_Sitter', 'FLRW_radiation'),
    # Schwarzschild vacuum: R = R² = R_μν² = 0; R_μνρσ² = 48 (G M)²/r⁶
    # at radius r. Use unit normalisation r = 2GM (horizon scale): K = 3.
    'SCHWARZSCHILD_KRETSCHMANN_AT_HORIZON': 3.0,  # Wald §6.1
    # de Sitter: R = 12 H², R² = 144 H⁴, R_μν² = 36 H⁴, R_μνρσ² = 24 H⁴.
    # Unit H = 1.
    'DE_SITTER_R_AT_UNIT_H': 12.0,
    'DE_SITTER_R_SQ_AT_UNIT_H': 144.0,
    'DE_SITTER_RICCI_SQ_AT_UNIT_H': 36.0,
    'DE_SITTER_RIEMANN_SQ_AT_UNIT_H': 24.0,
    # FLRW radiation: w = 1/3, traceless T → R = 0; R_μν² and R_μνρσ²
    # set by Hubble rate. Unit H = 1: R_μν² = 12 H⁴, R_μνρσ² = 12 H⁴.
    'FLRW_RAD_R_AT_UNIT_H': 0.0,
    'FLRW_RAD_R_SQ_AT_UNIT_H': 0.0,
    'FLRW_RAD_RICCI_SQ_AT_UNIT_H': 12.0,
    'FLRW_RAD_RIEMANN_SQ_AT_UNIT_H': 12.0,
    # ── Parameter scan grid (T_emerg vs T_matter visualisation) ──────
    'ALPHA_SCAN_POINTS': 21,  # α ∈ [0.1, 10.0], log-spaced
    'PARAMETER_SCAN_POINTS': 16,
}


# ════════════════════════════════════════════════════════════════════
# Phase 6e Wave 5 — Microscopic-to-Macroscopic Coefficient Match
# ════════════════════════════════════════════════════════════════════
#
# Centralised parameters for `MicroscopicCoefficientMatch.lean` +
# `src/micro_macro_match/`.  Wave 5 closes Decision Gate E.4 by
# expressing emergent couplings (G_N^emerg, Λ^emerg, higher-curvature
# triple) in microscopic parameters (Λ_UV, N_f) and testing the
# resulting `Λ^emerg` against the observed cosmological constant.

MICRO_MACRO_PARAMS = {
    # ── Observed cosmological constant ──────────────────────────────
    # Λ_obs ≃ ρ_Λ ≃ (2.26 × 10⁻³ eV)⁴ ≃ 2.6 × 10⁻⁴⁷ GeV⁴
    # (Planck 2018, Aghanim et al. A&A 641, A6, 2020 — derived from
    #  Ω_Λ h² = 0.3155 + h = 0.6736, ρ_crit ≃ 1.054 × 10⁻⁵ h² GeV/cm³).
    # Stored in GeV⁴ for direct comparison with Λ^emerg ~ Λ_UV⁴.
    'LAMBDA_OBSERVED_GEV4': 2.6e-47,
    'LAMBDA_OBSERVED_MEV4_EXPONENT': 4,  # i.e. (2.26 meV)^4
    # ── Planck mass / natural UV cutoff scales ──────────────────────
    'M_PLANCK_GEV': 1.221e19,           # reduced Planck = 2.435e18; we use full M_Pl
    'M_PLANCK_GEV4': (1.221e19) ** 4,    # ≃ 2.22e76 GeV⁴
    'GUT_SCALE_GEV': 2.0e16,             # standard GUT scale
    'EW_SCALE_GEV': 246.0,               # electroweak symmetry breaking
    'QCD_SCALE_GEV': 0.215,              # Λ_QCD MS-bar
    # ── SM-like fermion counts (used as natural-N_f benchmarks) ──────
    # SM has 3 colors × (6 quarks + 3 leptons) = 27 Weyl, but for
    # heat-kernel a_0 we count Dirac species. Use N_f = 16 as the
    # standard "Dirac fermion count" benchmark (cf. Christensen-Duff
    # Dirac sector convention).
    'N_F_SM_DIRAC': 16,
    'N_F_SCAN_VALUES': (4, 8, 16, 24, 100),  # benchmark + correctness-push max
    # ── Λ^emerg / Λ_obs ratio thresholds ─────────────────────────────
    # Decision Gate E.4: at natural Λ_UV = M_Pl + N_f = SM, the
    # heat-kernel a_0 prediction Λ^emerg = a_0(N_f) · Λ_UV⁴ is
    # ~ 10¹²² × Λ_obs — i.e. CC problem REPRODUCED in emergent form
    # with no resolution. The threshold below labels "natural-CC-
    # reproduction" (ratio > 10⁶⁰) vs "natural-CC-resolution"
    # (|log10 ratio| < 1).
    'CC_REPRODUCED_RATIO_FLOOR': 1.0e60,
    'CC_RESOLVED_LOG10_BAND': 1.0,  # |log10(Λ^emerg / Λ_obs)| < 1
    # ── Λ_UV scan range (log-spaced) ────────────────────────────────
    # Test from QCD scale up to Planck. Below QCD the heat-kernel
    # expansion as a UV-completion semantics no longer applies; above
    # M_Pl the EFT framework breaks down by construction.
    'LAMBDA_UV_SCAN_MIN_GEV': 1.0e-3,    # below electron mass — for resolution scan
    'LAMBDA_UV_SCAN_MAX_GEV': 1.221e19,  # M_Pl
    'LAMBDA_UV_SCAN_POINTS': 32,
    # ── Decision Gate E.4 verdict band labels ───────────────────────
    'DG_E4_VERDICT_RESOLVED': 'cc_resolved',     # |log10 ratio| < 1
    'DG_E4_VERDICT_REPRODUCED': 'cc_reproduced',  # log10 ratio > 60
    'DG_E4_VERDICT_INTERMEDIATE': 'cc_intermediate',  # in between
    # ── Microscopic-coefficient match tolerance (algebraic) ──────────
    # G_N_emerg ↔ G_N_from_a2 closed forms agree by construction;
    # this tolerance is for FP-roundoff when scanning numerically.
    'MATCH_RESIDUAL_TOLERANCE': 1.0e-12,
    # ── Λ_UV value at which Λ^emerg = Λ_obs for SM N_f (resolution
    # locus, derived from a_0(16) · Λ_UV⁴ = Λ_obs):
    # Λ_UV_resolution = (Λ_obs / a_0(16))^(1/4)
    #                = (2.6e-47 / 0.4053)^(1/4) GeV
    #                = 2.83e-12 GeV ≃ 2.83 meV (≪ EW scale).
    # Verified by `lambda_emerg_microscopic(2.83e-12, 16)` reproducing
    # `LAMBDA_OBSERVED_GEV4` to <1% (FP roundoff). For diagnostic
    # display only — not load-bearing.
    'LAMBDA_UV_RESOLUTION_LOCUS_DIAGNOSTIC_GEV': 2.83e-12,
}


# ════════════════════════════════════════════════════════════════════
# Phase 6e Wave 6 — Einstein-Cartan Extension (torsion from spin current)
# ════════════════════════════════════════════════════════════════════
#
# Centralised parameters for `EinsteinCartanExtension.lean` +
# `src/einstein_cartan/`.  Wave 6 extends the ADW emergent-gravity
# programme to Einstein-Cartan with non-zero torsion sourced by the
# fermion spin current — a structural consequence of working with
# tetrads e^a_μ rather than the metric g_μν.  The Wave 6 correctness-
# push compares the microscopic torsion-amplitude prediction against
# the tightest published torsion observational bounds.

EINSTEIN_CARTAN_PARAMS = {
    # ── Torsion observational bounds ─────────────────────────────────
    # Cosmic axial torsion bound from CPT/Lorentz precision tests.
    # Kostelecky-Russell-Tasson, PRL 100, 111102 (2008): cosmic
    # background torsion T < 1e-31 GeV at 95% CL from atomic-physics
    # Lorentz-violation searches (b_μ extraction; T ~ b/m_e).  This is
    # the tightest published bound in the natural high-energy regime.
    'TORSION_BOUND_KOSTELECKY_GEV': 1.0e-31,
    # Hughes-Drever / Lammerzahl atomic-clock bound (Lammerzahl, PRD 64,
    # 084014 (2001)) on rotational axial torsion: T < 1e-29 GeV.
    # Looser than Kostelecky but cross-channel-independent.
    'TORSION_BOUND_HUGHES_DREVER_GEV': 1.0e-29,
    # ── Cosmological background spin density ─────────────────────────
    # Degenerate spinor bath at T ≃ T_CMB = 2.725 K = 2.35×10⁻¹³ GeV
    # gives n_s ~ T_CMB³ ≃ 1.3×10⁻³⁹ GeV³ (each Weyl species, summed
    # over SM Dirac species). Used as the ambient-bath spin density
    # for the Wave 6 torsion-amplitude prediction.
    'COSMOLOGICAL_SPIN_DENSITY_GEV3': 1.3e-39,
    'T_CMB_GEV': 2.35e-13,
    # ── α_EC (Einstein-Cartan dimensionless coefficient) ─────────────
    # Inherited from the Wave 1–5 ADW Sakharov-Adler calibration:
    # α_EC = α_ADW.  At α_EC = 1 the EC torsion-amplitude prediction
    # equals G_N_emerg(Λ_UV, N_f, 1) · n_spin (cross-bridge to Phase
    # 6a.1's `G_N_emerg_at_alpha_one`).  The natural-parameter band
    # is [0.1, 10] (matches Wave 4 NONLINEAR_EFE_PARAMS).
    'ALPHA_EC_CALIBRATED': 1.0,
    'ALPHA_EC_NATURAL_MIN': 0.1,
    'ALPHA_EC_NATURAL_MAX': 10.0,
    # ── N_f benchmark (inherited from Wave 5) ────────────────────────
    'N_F_SM_DIRAC': 16,  # SM-Dirac convention; matches MICRO_MACRO
    # ── Λ_UV scan range (TeV → M_Pl, log-spaced) ──────────────────────
    'LAMBDA_UV_SCAN_MIN_GEV': 1.0e3,    # TeV (above EW, below GUT)
    'LAMBDA_UV_SCAN_MAX_GEV': 1.221e19,  # M_Pl
    'LAMBDA_UV_SCAN_POINTS': 16,
    'ALPHA_SCAN_POINTS': 21,
    # ── Decision-Gate-style verdict labels (correctness-push) ─────────
    # Wave 6 correctness-push: at natural microscopic parameters
    # (Λ_UV ≃ M_Pl, N_f = 16, α_EC = 1, n_s = cosmological), the
    # predicted torsion amplitude |T_EC| ~ G_N_emerg · n_s ~ 1e-114 GeV
    # — far below Kostelecky's 1e-31 GeV by ~80 orders of magnitude.
    # "Bound satisfied" = ratio < 1; "bound violated" = ratio ≥ 1.
    'TORSION_VERDICT_BOUND_SATISFIED': 'torsion_below_bound',
    'TORSION_VERDICT_BOUND_VIOLATED': 'torsion_above_bound',
    # ── EC residual tolerance (algebraic) ────────────────────────────
    # The EC residual `|α_EC - 1| · G_N_emerg · n_spin` vanishes iff
    # α_EC = 1; this float threshold accounts only for FP roundoff.
    'EC_RESIDUAL_TOLERANCE': 1.0e-12,
}


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


# =============================================================================
# Phase 5q: Ext Computation over A(1) — Steenrod Algebra Data
# =============================================================================

# A(1) Milnor basis elements: Sq(r1, r2) with 0 ≤ r1 ≤ 3, 0 ≤ r2 ≤ 1
A1_MILNOR_BASIS = {
    0: {'milnor': (0, 0), 'degree': 0, 'name': '1'},
    1: {'milnor': (1, 0), 'degree': 1, 'name': 'Sq(1)'},
    2: {'milnor': (2, 0), 'degree': 2, 'name': 'Sq(2)'},
    3: {'milnor': (3, 0), 'degree': 3, 'name': 'Sq(3)'},
    4: {'milnor': (0, 1), 'degree': 3, 'name': 'Q₁'},
    5: {'milnor': (1, 1), 'degree': 4, 'name': 'Sq(1,1)'},
    6: {'milnor': (2, 1), 'degree': 5, 'name': 'Sq(2,1)'},
    7: {'milnor': (3, 1), 'degree': 6, 'name': 'Sq(3,1)'},
}

# Resolution data: ranks of free modules P_0 through P_5
A1_RESOLUTION_RANKS = [1, 2, 2, 2, 3, 4]

# Ext dimensions (= resolution ranks for minimal resolution)
A1_EXT_DIMENSIONS = [1, 2, 2, 2, 3, 4]

# Ext algebra generators with bidegrees (s, t) where s = homological, t = internal
A1_EXT_GENERATORS = {
    'h0': {'bidegree': (1, 1), 'stem': 0, 'desc': 'detects 2 in π₀(ko)'},
    'h1': {'bidegree': (1, 2), 'stem': 1, 'desc': 'detects η in π₁(ko)'},
    'v':  {'bidegree': (3, 7), 'stem': 4, 'desc': 'detects generator of π₄(ko) ≅ ℤ'},
    'w1': {'bidegree': (4, 12), 'stem': 8, 'desc': 'Bott periodicity generator'},
}

# Ext algebra relations (over F₂)
A1_EXT_RELATIONS = [
    'h0 * h1 = 0',
    'h1^3 = 0',
    'h1 * v = 0',
    'v^2 + h0^2 * w1 = 0',
]

# Bordism hypothesis decomposition (Phase 5q Wave 5)
BORDISM_HYPOTHESES = {
    'H1': {
        'name': 'ko cohomology',
        'statement': 'H*(ko; F₂) ≅ A ⊗_{A(1)} F₂',
        'eliminability': 'topological',
        'reference': 'Adams, Stable Homotopy (1974), Ch. 16',
    },
    'H2': {
        'name': 'change of rings',
        'statement': 'Ext_A(A ⊗_{A(1)} F₂, F₂) ≅ Ext_{A(1)}(F₂, F₂)',
        'eliminability': 'algebraic',  # Shapiro's lemma — potentially provable
        'reference': 'Weibel, Homological Algebra (1994), Thm 6.10.7',
    },
    'H3': {
        'name': 'ASS collapses for ko',
        'statement': 'Adams spectral sequence for ko collapses at E₂',
        'eliminability': 'topological',
        'reference': 'Ravenel, Complex Cobordism (2003), Ch. 3',
    },
    'H4': {
        'name': 'ABP splitting',
        'statement': 'π_n(MSpin) ≅ π_n(ko) for n < 8',
        'eliminability': 'topological',
        'reference': 'Anderson-Brown-Peterson, Ann. Math. 86 (1967)',
    },
}


#
# Research chain taxonomy (Phase 5v Wave 9d, 2026-04-24).
#
# Maps Lean module short-names (the part after `SKEFTHawking.`) to the
# research chain they belong to. The Proof-Chain-Viz dashboard reads this
# to populate the "Research Status" tab's L0/L1/L2 views. Chain ids are
# derived dynamically — adding a new module with a new chain_id here
# creates a new chain in the dashboard with no other registry changes.
#
# A module may legitimately appear in multiple chains (e.g. SK axioms are
# shared between hawking and graphene). Use a list in that case.
#
# The dashboard also accepts a node-level `chain_id` override (on formulas,
# papers, etc.) when the module-level mapping isn't precise enough.
#
MODULE_CHAIN_MAP: dict[str, str | list[str]] = {
    # === hawking — dissipative Hawking radiation (BEC + polariton + graphene) ===
    'AcousticMetric': 'hawking',
    'Axioms': 'hawking',
    'SKAxioms': 'hawking',
    'SKDoubling': 'hawking',
    'HawkingUniversality': 'hawking',
    'SecondOrderSK': 'hawking',
    'ThirdOrderSK': 'hawking',
    'WKBAnalysis': 'hawking',
    'WKBConnection': 'hawking',
    'CGLTransform': 'hawking',
    'QuasiOneDReduction': 'hawking',
    'DiracFluidMetric': ['hawking', 'graphene'],
    'DiracFluidSK': ['hawking', 'graphene'],
    'GrapheneHawking': ['hawking', 'graphene'],
    'GrapheneNoiseFormula': ['hawking', 'graphene'],
    'PolaritonTier1': 'hawking',
    'KappaScaling': 'hawking',

    # === generations — Z16 anomaly + "16 convergence" ===
    'SMFermionData': 'generations',
    'Z16AnomalyComputation': 'generations',
    'Z16Classification': 'generations',
    'GenerationConstraint': 'generations',
    'WangBridge': 'generations',
    'ModularInvarianceConstraint': 'generations',
    'RokhlinBridge': 'generations',
    'SteenrodA1': 'generations',
    'E8Lattice': 'generations',

    # === gauge-emergence — D(G), half-braiding, Drinfeld center ===
    'DrinfeldDouble': 'gauge-emergence',
    'DrinfeldDoubleAlgebra': 'gauge-emergence',
    'DrinfeldDoubleRing': 'gauge-emergence',
    'DrinfeldCenterBridge': 'gauge-emergence',
    'DrinfeldEquivalence': 'gauge-emergence',
    'GaugeEmergence': 'gauge-emergence',
    'GaugeErasure': 'gauge-emergence',
    'VecG': 'gauge-emergence',
    'VecGMonoidal': 'gauge-emergence',
    'ToricCodeCenter': 'gauge-emergence',
    'S3CenterAnyons': 'gauge-emergence',
    'CenterEquivalenceZ2': 'gauge-emergence',
    'CenterFunctor': 'gauge-emergence',
    'CenterFunctorZ2Equiv': 'gauge-emergence',
    'KLinearCategory': 'gauge-emergence',
    'SphericalCategory': 'gauge-emergence',
    'FusionCategory': 'gauge-emergence',
    'FusionExamples': 'gauge-emergence',
    'RibbonCategory': 'gauge-emergence',
    'KacWaltonFusion': 'gauge-emergence',
    'QNumber': 'gauge-emergence',
    'Uqsl2': 'gauge-emergence',
    'Uqsl2Affine': 'gauge-emergence',
    'Uqsl2Hopf': 'gauge-emergence',
    'Uqsl3': 'gauge-emergence',
    'Uqsl3Hopf': 'gauge-emergence',
    'QuantumGroupGeneric': 'gauge-emergence',
    'QuantumGroupCoproduct': 'gauge-emergence',
    'QuantumGroupAntipode': 'gauge-emergence',
    'QuantumGroupHopf': 'gauge-emergence',
    'QuantumGroupInstantiation': 'gauge-emergence',
    'QuantumGroupMeta': 'gauge-emergence',
    'RestrictedUq': 'gauge-emergence',
    'SU2kFusion': 'gauge-emergence',
    'SU2kSMatrix': 'gauge-emergence',

    # === chirality-wall — GS / TPF / GT synthesis ===
    'ChiralityWall': 'chirality-wall',
    'ChiralityWallMaster': 'chirality-wall',
    'GoltermanShamir': 'chirality-wall',
    'TPFEvasion': 'chirality-wall',
    'GTCommutation': 'chirality-wall',
    'GTWeylDoublet': 'chirality-wall',
    'PauliMatrices': 'chirality-wall',
    'WilsonMass': 'chirality-wall',
    'BdGHamiltonian': 'chirality-wall',
    'LatticeHamiltonian': 'chirality-wall',
    'SMGClassification': 'chirality-wall',
    'OnsagerAlgebra': 'chirality-wall',
    'OnsagerContraction': 'chirality-wall',
    'SPTClassification': 'chirality-wall',

    # === fracton — fracton gravity / hydro / DM ===
    'FractonHydro': 'fracton',
    'FractonFormulas': 'fracton',
    'FractonGravity': 'fracton',
    'FractonNonAbelian': 'fracton',
    'FractonDarkMatter': 'fracton',

    # === vestigial — emergent gravity from dim. reduction ===
    'VestigialGravity': 'vestigial',
    'VestigialSusceptibility': 'vestigial',
    'ADWMechanism': 'vestigial',
    'SO4Weingarten': 'vestigial',
    'QuaternionGauge': 'vestigial',
    'FermionBag4D': 'vestigial',
    'SU2PseudoReality': 'vestigial',
    'MajoranaKramers': 'vestigial',
    'HubbardStratonovichRHMC': 'vestigial',
    'GaugeFermionBag': 'vestigial',
    'WetterichNJL': 'vestigial',

    # === dark-sector — Phase 5x (SFDM, fracton DM, FG torsion, hidden sectors) ===
    'HiddenSectorClassification': 'dark-sector',
    'HiddenSectorMixedCharge': 'dark-sector',
    'FangGuTorsionDM': 'dark-sector',
    'CosmologicalConstant': 'dark-sector',
    'SFDMMergerForecast': 'dark-sector',
    'DarkSectorSynthesis': 'dark-sector',

    # === gate-engineering — Phase 5t (Fermi-Hubbard dimer geometric SWAP) ===
    'FermiHubbardDimer': 'gate-engineering',
}


#
# Milestone markers — which Lean declarations are "pillar" theorems that
# every chain figure should show. Level L1 (milestone DAG) renders only
# nodes with `is_milestone=True`; the L2 full-subgraph view shows all
# chain nodes. Short names here match the final component after `.`.
#
# Rule of thumb (per design/docs/SUBGRAPH_CONTRACT.md section 2):
#   - Every external axiom the chain uses → milestone
#   - Every terminal claim the chain proves → milestone
#   - Every named "pillar" theorem a reviewer would cite → milestone
#   - Intermediate plumbing (lemmas, technical defs) → NOT milestone
# Target: 6–12 milestones per chain.
#
CHAIN_MILESTONES: dict[str, int] = {
    # hawking
    'transport_counting_formula': 0,
    'cgl_fdr_derivation': 1,
    'parity_alternation_general_N': 2,
    'wkb_connection_exact': 3,
    'bogoliubov_decoherence': 4,
    'hawking_universality': 5,
    'graphene_T_eff_positive': 6,
    # generations
    'anomaly_index_z16': 0,
    'generation_minimal_nontrivial': 1,
    'generation_mod3_constraint': 2,
    'dedekind_eta_modular': 3,
    'hidden_sector_z16_constraint': 4,
    # gauge-emergence
    'drinfeld_equivalence_z2': 0,
    'drinfeld_equivalence_s3': 1,
    'vecg_monoidal': 2,
    'uqsl2_hopf_algebra': 3,
    'quantum_group_generic_hopf': 4,
    # chirality-wall
    'gs_nine_conditions': 0,
    'tpf_evades_at_least_two': 1,
    'gt_commutation_central': 2,
    'chirality_wall_three_pillars': 3,
    # fracton
    'binomial_charge_counting': 0,
    'bootstrap_divergence': 1,
    'fracton_sm_singlet_from_ym_incompat': 2,
    # vestigial
    'critical_coupling_pos': 0,
    'ng_mode_count': 1,
    'so4_weingarten_positivity': 2,
    # dark-sector
    'anomaly_value_z16': 0,
    'sfdm_offset_step_function': 3,
    'fracton_dm_arrhenius': 4,
    'traceless_iff_w_one_third': 5,
    # gate-engineering
    'geometric_phase_necessary_conditions_on_pi_loop': 0,
}


def get_bec_parameters(experiment_name):
    """
    Return a BECParameters object for the named experiment
    using values from EXPERIMENTS and ATOMS.
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
