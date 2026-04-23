"""Phase 5x Wave 7: Fracton Dark Matter Phenomenology.

Computational companion to ``lean/SKEFTHawking/FractonDarkMatter.lean``.

Implements, for the p-wave dipole-superfluid / gapless-U(1) fracton
candidate dark-matter scenario:

- **BBN stability windows** — Arrhenius (gapped scenario, M_d ≳ 10 MeV)
  vs condensate (p-wave scenario, μ ≳ 1 MeV), with explicit ratio
  computation and classification.
- **Arrhenius lifetime** ``τ(T) = τ₀ · exp(M_d / T)`` and comparison
  against the radiation-era Hubble rate ``H(T) = 1.66 √g_* · T² / M_Pl``.
- **Phenomenological signatures** — σ_eff = 0 (Bullet Cluster), w = 0
  pressureless dust (arXiv:2503.14496), z = 4 subdiffusion, sound
  speed c_s² < 1 (structure formation), Pretko always-attractive
  graviton coupling, Weinberg-Witten bypass via Lorentz breaking.
- **SM-singlet status** — inherited from the Lean-verified
  ``FractonNonAbelian.no_fracton_is_ym_compatible``; the module
  exposes a boolean flag rather than re-deriving it.
- **Structured assessment** — ``assess_fracton_dm_status`` returns the
  W1b → Drilldown "VIABLE (conditional)" verdict with the surviving
  empirical and structural hooks.

Physics references
------------------
- Pretko, PRD 96, 024051 (2017) — fracton-graviton always attractive
- Pretko, PRB 96, 115102 (2017) — finite-T screening of U(1) fractons
- Shen et al., PRR 4, L032008 (2022) — gapped 3D fracton no-go at T>0
- Kapustin-Spodyneiko, PRB 106, 245125 (2022) — dipole SSB in d≥3
- Jensen-Raz, PRL 132, 071603 (2024) — large-N p-wave phase
- Głódkowski et al., arXiv:2401.01877 (2024) — p-wave hydrodynamics
- Feistl-Schraven-Warzel, arXiv:2601.23078 (2026) — multipole MW
- arXiv:2503.14496 (2025) — relativistic fractons → pressureless dust

Deep research (read in full before editing):
- Lit-Search/Phase-5x/Fracton Dark Matter  Phenomenological Assessment.md
- Lit-Search/Phase-5x/5x-Fracton DM Kinetic Stability  Deep Drilldown …/Fracton-DM-Kinetic-Stability-Drilldown.md
- Lit-Search/Phase-5x/5x-Gapless Fracton Liquid Stability at Finite Temperature …/Fracton-DM-Thermal-Stability-Assessment.md

Lean anchors
------------
- FractonDarkMatter.fracton_nogo_exemption (13a)
- FractonDarkMatter.fracton_lifetime_arrhenius (13c)
- FractonDarkMatter.fracton_bbn_condensate_sufficient (13d)
- FractonDarkMatter.fracton_bullet_sigma_zero (Sig1)
- FractonDarkMatter.fracton_sm_singlet_from_ym_incompat (Sig2)
- FractonDarkMatter.fracton_cosmo_dust_pressureless (Sig3)
- FractonDarkMatter.fracton_gravity_attractive (Sig4)
- FractonDarkMatter.fracton_ww_bypass (Sig5)
- FractonDarkMatter.fracton_z4_subdiffusion_preserved (Sig6)
- FractonDarkMatter.fracton_sound_speed_subluminal (Sig7)
- FractonDarkMatter.fracton_viable_arrhenius_window (ViableA)
- FractonDarkMatter.fracton_viable_pwave_window (ViableB)
- FractonNonAbelian.no_fracton_is_ym_compatible (Sig2 root)
- FractonFormulas.dipole_k4_damping (Sig6 root)
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from enum import Enum

#: Canonical BBN temperature, in MeV.
T_BBN_MeV = 0.1

#: Arrhenius BBN lower bound on the dipole gap, in MeV.
#:
#: From M_d/T_BBN > ln(M_Pl²/(1.66·√g_* · T_BBN²)) ≈ 105, i.e.
#: M_d ≳ 10.5 MeV. Conservative rounded value.
M_D_ARRHENIUS_BBN_MeV = 10.0

#: Condensate BBN lower bound on the chemical potential, in MeV.
#:
#: From the condensate condition μ > T_BBN ≈ 0.1–1 MeV. Conservative
#: value at the MeV scale.
MU_CONDENSATE_BBN_MeV = 1.0

#: Gapped-scenario Arrhenius viable window upper edge, in MeV.
#:
#: Drilldown summary: 100 GeV = 1e5 MeV.
ARRHENIUS_WINDOW_UPPER_MeV = 1.0e5

#: p-wave condensate viable window conservative upper edge, in MeV.
#:
#: Drilldown summary: ~TeV, chosen as 10 TeV = 1e7 MeV conservatively
#: (the formal upper bound is ~M_Pl, but production constraints and
#: N_eff cap practical viability near MeV-TeV).
PWAVE_WINDOW_UPPER_MeV = 1.0e7

#: Dipole subdiffusion dynamical exponent z = 4.
Z_SUBDIFFUSION = 4

#: Bullet Cluster σ/m upper bound in cm²/g.
SIGMA_BULLET_CLUSTER_CM2_PER_G = 1.25

#: Effective isolated-fracton σ/m. Zero at leading order (dipole
#: conservation + locality). Subleading dipole-dipole is ~1e-40 cm²/g,
#: effectively zero on Bullet Cluster scales.
SIGMA_EFF_FRACTON_CM2_PER_G = 0.0

#: Fracton-dust pressureless equation-of-state coefficient w = p/ρ = 0
#: on FRW (arXiv:2503.14496).
EOS_FRACTON_DUST = 0.0

#: Pretko fracton-graviton coupling sign (+1 = always attractive, via
#: PRD 96, 024051 2017).
FRACTON_GRAVITON_COUPLING_SIGN = 1

#: SM-singlet flag from the Lean-verified YM incompatibility theorem
#: (`FractonNonAbelian.no_fracton_is_ym_compatible`). Fracton DM
#: cannot carry non-Abelian charges, hence no SM SU(3)_c / SU(2)_L.
FRACTON_IS_SM_SINGLET = True

#: Conservative sound-speed-squared bound for the mobile-dipole sector
#: on scales > 100 km (Pretko 2017, deep research §1.3).
CS_SQ_DIPOLE_BOUND = 0.5


class FractonDMPhase(str, Enum):
    """Thermodynamic phase classification (matches Lean enum)."""

    #: Gapped 3D fracton topological order (X-cube, Haah). Destroyed
    #: at T > 0 in d = 3 by Shen et al. 2022.
    GAPPED_TOPO = "GappedTopo"
    #: Gapless U(1) rank-2 tensor-gauge phase (Pretko 2017). Smooth
    #: finite-T crossover; kinetic stability via exp(M_d/2T) screening.
    GAPLESS_U1 = "GaplessU1"
    #: p-wave dipole superfluid (Kapustin-Spodyneiko 2022, Jensen-Raz
    #: 2024). Thermodynamically stable at all T > 0 in d = 3. Immobile
    #: fractons, mobile dipoles. Drilldown preferred candidate.
    PWAVE_CONDENSATE = "PWaveCondensate"
    #: s-wave dipole superfluid: both U(1) charge + dipole SSB.
    #: Forbidden at T > 0 in d ≤ 4 by Kapustin-Spodyneiko.
    SWAVE_CONDENSATE = "SWaveCondensate"


def arrhenius_lifetime(M_d_MeV: float, T_MeV: float, tau_0_s: float = 1.0) -> float:
    """Arrhenius fracton-matter lifetime ``τ = τ₀ · exp(M_d / T)``.

    Appropriate for the gapped (type I) fracton scenario. Returns
    seconds if ``tau_0_s`` is in seconds.

    Lean: ``FractonDarkMatter.fracton_lifetime_arrhenius``.
    """
    if M_d_MeV <= 0 or T_MeV <= 0 or tau_0_s <= 0:
        raise ValueError("M_d_MeV, T_MeV, tau_0_s must all be positive")
    return tau_0_s * math.exp(M_d_MeV / T_MeV)


def haah_superexponential_lifetime(
    M_d_MeV: float, T_MeV: float, tau_0_s: float = 1.0, c: float = 1.0
) -> float:
    """Haah-type superexponential lifetime ``τ = τ₀ · exp(c (M_d/T)²)``.

    For type II (fractal operator) fracton phases. Relaxes the BBN
    Arrhenius bound from ~10 MeV to ~1 MeV.
    """
    if M_d_MeV <= 0 or T_MeV <= 0 or tau_0_s <= 0 or c <= 0:
        raise ValueError("all arguments must be positive")
    return tau_0_s * math.exp(c * (M_d_MeV / T_MeV) ** 2)


def hubble_radiation_era_inv_MeV(T_MeV: float, g_star: float = 10.75) -> float:
    """Inverse Hubble rate in the radiation era, in MeV⁻¹.

    ``H(T) = 1.66 · √g_* · T² / M_Pl``. Returns ``H⁻¹`` in natural
    MeV⁻¹ units using ``M_Pl = 1.22e22 MeV``.

    Default ``g_star = 10.75`` is the SM relativistic d.o.f. count at
    T_BBN (Kolb-Turner Table 3.1).
    """
    if T_MeV <= 0:
        raise ValueError("T_MeV must be positive")
    if g_star <= 0:
        raise ValueError("g_star must be positive")
    M_Pl_MeV = 1.22e22  # reduced Planck mass ≈ 2.4e21 MeV, total ≈ 1.22e22
    H = 1.66 * math.sqrt(g_star) * T_MeV**2 / M_Pl_MeV
    return 1.0 / H


def arrhenius_md_bbn_lower_bound_MeV(
    T_BBN_MeV_local: float = T_BBN_MeV, g_star: float = 10.75
) -> float:
    """Arrhenius log-Hubble lower bound on M_d from BBN survival.

    From ``M_d / T_BBN > ln(M_Pl² / (1.66 √g_* · T_BBN²))``, returns
    the implied M_d floor in MeV. Default inputs give ~10.5 MeV (the
    canonical "10 MeV" Arrhenius window lower edge).
    """
    if T_BBN_MeV_local <= 0:
        raise ValueError("T_BBN_MeV_local must be positive")
    if g_star <= 0:
        raise ValueError("g_star must be positive")
    M_Pl_MeV = 1.22e22
    ratio_log = math.log(
        M_Pl_MeV**2 / (1.66 * math.sqrt(g_star) * T_BBN_MeV_local**2)
    )
    return ratio_log * T_BBN_MeV_local


def arrhenius_survives_bbn(
    M_d_MeV: float, T_BBN_MeV_local: float = T_BBN_MeV, g_star: float = 10.75
) -> bool:
    """Return True if an Arrhenius fracton phase with gap ``M_d`` survives BBN.

    Condition: ``τ(T_BBN) > H⁻¹(T_BBN)``, which reduces to ``M_d / T_BBN
    > log(M_Pl² / (1.66 √g_* · T_BBN²))``.

    Lean: ``FractonDarkMatter.fracton_lifetime_arrhenius``.
    """
    floor = arrhenius_md_bbn_lower_bound_MeV(T_BBN_MeV_local, g_star)
    return M_d_MeV >= floor


def condensate_cold(mu_MeV: float, T_MeV: float) -> bool:
    """Return True if the p-wave condensate is "cold" at this epoch.

    Condition ``μ > T``. For T_BBN ≈ 0.1 MeV this requires μ ≳ MeV —
    roughly 100× weaker than the Arrhenius Hubble-barrier constraint.

    Lean: ``FractonDarkMatter.fracton_bbn_condensate_sufficient``.
    """
    if mu_MeV <= 0 or T_MeV <= 0:
        raise ValueError("mu_MeV and T_MeV must be positive")
    return mu_MeV > T_MeV


def condensate_lower_bound_at_epoch_MeV(T_MeV: float) -> float:
    """Return the condensate-scenario lower bound on μ at temperature T_MeV.

    For "cold" DM behavior the guard factor is ~100 in conventional
    Boltzmann thermodynamics; the deep research takes μ > T as the
    binding condition (Drilldown §II). We report the factor-1 bound.
    """
    if T_MeV <= 0:
        raise ValueError("T_MeV must be positive")
    return T_MeV


def fracton_subdiffusion_core_radius_estimate(
    M_d_eV: float, M_fracton_eV: float, rho_c_MeV4: float, G_Newton_invMeV2: float
) -> float:
    """Deep-research §2.1 core-radius estimate ``r_c ~ √(M_d / (G ρ_c M_f))``.

    Returns the core radius in natural units (MeV⁻¹). Fracton DM yields
    kpc-scale cores for ``M_d / M_f ~ 10⁻³ – 10⁻²``. Parametric — not a
    full Boltzmann analysis — but confirms core formation is the stable
    outcome of dipole-conserving dynamics.
    """
    if M_d_eV <= 0 or M_fracton_eV <= 0 or rho_c_MeV4 <= 0 or G_Newton_invMeV2 <= 0:
        raise ValueError("all arguments must be positive")
    M_d_MeV = M_d_eV * 1e-6
    M_f_MeV = M_fracton_eV * 1e-6
    return math.sqrt(M_d_MeV / (G_Newton_invMeV2 * rho_c_MeV4 * M_f_MeV))


def fracton_dust_eos() -> float:
    """Pressureless fracton-dust equation of state w = 0 (arXiv:2503.14496).

    Lean: ``FractonDarkMatter.fracton_cosmo_dust_pressureless``.
    """
    return EOS_FRACTON_DUST


def bullet_cluster_passes() -> bool:
    """σ_eff = 0 ≤ 1.25 cm²/g Bullet Cluster bound.

    Lean: ``FractonDarkMatter.fracton_bullet_cluster_satisfied``.
    """
    return SIGMA_EFF_FRACTON_CM2_PER_G <= SIGMA_BULLET_CLUSTER_CM2_PER_G


def fracton_gravity_attractive() -> bool:
    """Pretko 2017 always-attractive fracton-graviton coupling.

    Lean: ``FractonDarkMatter.fracton_gravity_attractive``.
    """
    return FRACTON_GRAVITON_COUPLING_SIGN > 0


def fracton_ww_bypass_applies(lorentz_covariant_stress_tensor: bool = False) -> bool:
    """Return True if the Weinberg-Witten theorem's assumption fails.

    WW requires a Lorentz-covariant stress tensor; fracton EFT has
    none (framid field breaks Lorentz boost), so WW does not apply to
    fracton emergent gravity.

    Lean: ``FractonDarkMatter.fracton_ww_bypass``.
    """
    ww_requires = True
    return lorentz_covariant_stress_tensor != ww_requires


def z4_subdiffusion_preserved_in_phase(phase: FractonDMPhase) -> bool:
    """Return True if the z = 4 subdiffusion transport survives in this phase.

    Per Głódkowski et al. (2024) the p-wave phase retains ``ω ~ -ik⁴``
    at finite T. GaplessU1 also has kinetically preserved z = 4 below
    the screening length. Gapped and s-wave phases are excluded at
    T > 0 in 3D; the question of "preservation" is moot there.

    Lean: ``FractonDarkMatter.fracton_z4_subdiffusion_preserved`` (for
    the p-wave case, building on FractonFormulas.dipole_k4_damping).
    """
    return phase in {FractonDMPhase.PWAVE_CONDENSATE, FractonDMPhase.GAPLESS_U1}


def fracton_viable_at_epoch(
    phase: FractonDMPhase, scale_MeV: float, T_MeV: float
) -> bool:
    """Return True if the (phase, scale, T) triple is cosmologically viable.

    Mirrors the Lean ``is_viable_at_epoch`` classifier:

    - Gapped / gapless-U(1): M_d ≥ 100 · T (Arrhenius)
    - p-wave: μ > T (condensate)
    - s-wave: always excluded at T > 0 in 3D.

    Lean: ``FractonDarkMatter.is_viable_at_epoch``.
    """
    if scale_MeV <= 0 or T_MeV <= 0:
        raise ValueError("scale_MeV and T_MeV must be positive")
    if phase in {FractonDMPhase.GAPPED_TOPO, FractonDMPhase.GAPLESS_U1}:
        return scale_MeV >= 100.0 * T_MeV
    if phase is FractonDMPhase.PWAVE_CONDENSATE:
        return scale_MeV > T_MeV
    return False  # SWaveCondensate


@dataclass(frozen=True)
class FractonDMCandidate:
    """Single fracton DM candidate with (phase, scale, label)."""

    phase: FractonDMPhase
    scale_MeV: float
    label: str

    def viable_at(self, T_MeV: float) -> bool:
        return fracton_viable_at_epoch(self.phase, self.scale_MeV, T_MeV)


#: Drilldown "scenario B" p-wave condensate witness at the BBN lower
#: edge. The Drilldown preferred case.
DRILLDOWN_PWAVE_1MeV = FractonDMCandidate(
    phase=FractonDMPhase.PWAVE_CONDENSATE,
    scale_MeV=MU_CONDENSATE_BBN_MeV,
    label="p-wave condensate @ μ=1 MeV (Drilldown preferred)",
)

#: Original Phase 5x "scenario A" gapped Arrhenius window lower edge.
#: Still viable but a factor 10 above the condensate case.
ARRHENIUS_GAPPED_10MeV = FractonDMCandidate(
    phase=FractonDMPhase.GAPPED_TOPO,
    scale_MeV=M_D_ARRHENIUS_BBN_MeV,
    label="gapped Arrhenius @ M_d=10 MeV",
)

#: Excluded scenario: eV-scale gapped fracton fails BBN kinetic stability
#: (pre-W1b "spectacularly long CMB lifetime" did not survive BBN — this
#: was the Phase 5x W1b correction).
EXCLUDED_GAPPED_EV = FractonDMCandidate(
    phase=FractonDMPhase.GAPPED_TOPO,
    scale_MeV=1e-6,  # 1 eV = 1e-6 MeV
    label="gapped @ M_d=1 eV (excluded by BBN)",
)


@dataclass(frozen=True)
class FractonDMAssessment:
    """Structured summary of the W7 fracton DM viability case.

    Reports:

    - Which of the 4 phase options are cosmologically viable at T_BBN
    - The two BBN lower bounds (Arrhenius vs condensate) and their ratio
    - Key phenomenological signatures (SM singlet, σ = 0, w = 0, z = 4,
      gravity attractive, WW bypass)
    - Surviving empirical hooks: core-cusp, Bullet, diversity (HSF)
    - Remaining open questions (production mechanism is the top gap)
    """

    arrhenius_bbn_lower_MeV: float
    condensate_bbn_lower_MeV: float
    arrhenius_condensate_ratio: float
    viable_phases_at_bbn: tuple[str, ...]
    excluded_phases_at_bbn: tuple[str, ...]
    signatures_verified: dict[str, bool]
    surviving_empirical_hooks: tuple[str, ...]
    remaining_open_questions: tuple[str, ...]
    z_subdiffusion: int = Z_SUBDIFFUSION
    sm_singlet_from_lean: bool = FRACTON_IS_SM_SINGLET
    w_dust: float = EOS_FRACTON_DUST


def assess_fracton_dm_status() -> FractonDMAssessment:
    """Structured Drilldown-era fracton DM viability assessment.

    Returns the W1b → Drilldown "VIABLE (conditional)" case:
    p-wave condensate thermodynamically stable at T > 0 in d = 3
    (Kapustin-Spodyneiko), μ ≳ 1 MeV suffices at BBN, z = 4 preserved
    (Głódkowski), σ_eff = 0 (Bullet trivial), SM singlet from YM
    incompatibility (Lean-verified), w = 0 dust (arXiv:2503.14496).
    """
    arrhenius_floor = arrhenius_md_bbn_lower_bound_MeV()
    condensate_floor = MU_CONDENSATE_BBN_MeV
    ratio = arrhenius_floor / condensate_floor

    viable = (
        "PWaveCondensate (thermodynamic, μ≳1 MeV — Drilldown preferred)",
        "GaplessU1 (kinetic, M_d≳10 MeV Arrhenius)",
        "GappedTopo (kinetic, M_d≳10 MeV Arrhenius — pre-W1b baseline)",
    )
    excluded = (
        "SWaveCondensate (Kapustin-Spodyneiko: forbidden in d ≤ 4)",
        "GappedTopo @ M_d ≲ keV (Shen 2022 no-go at T > 0; plus BBN)",
        "All scenarios with M_d ≲ T_BBN/100 (Arrhenius; eV-scale excluded)",
    )

    signatures = {
        "sm_singlet_from_ym_incompatibility": FRACTON_IS_SM_SINGLET,
        "bullet_sigma_zero": bullet_cluster_passes(),
        "pressureless_dust_eos": math.isclose(fracton_dust_eos(), 0.0),
        "z4_subdiffusion_pwave_preserved":
            z4_subdiffusion_preserved_in_phase(FractonDMPhase.PWAVE_CONDENSATE),
        "graviton_always_attractive": fracton_gravity_attractive(),
        "weinberg_witten_bypass_lorentz_breaking":
            fracton_ww_bypass_applies(lorentz_covariant_stress_tensor=False),
        "sound_speed_subluminal": CS_SQ_DIPOLE_BOUND < 1.0,
    }

    hooks = (
        "Bullet Cluster trivially satisfied (σ_eff = 0 from dipole "
        "conservation; Lean: fracton_bullet_sigma_zero)",
        "Core-cusp resolved by z = 4 subdiffusion → flat central density "
        "(deep research §2.1; Lean: fracton_z4_subdiffusion_preserved)",
        "Halo diversity explained by Hilbert-space fragmentation (no "
        "baryonic feedback required; deep research §2.3)",
        "SM singlet derived from Lean-verified YM incompatibility "
        "(FractonNonAbelian.no_fracton_is_ym_compatible), not assumed",
        "p-wave condensate thermodynamically stable at all T > 0 in d = 3 "
        "(Kapustin-Spodyneiko; Drilldown §I)",
        "Dark QCD UV completion places Λ_dark ~ MeV–GeV naturally "
        "(Drilldown §VIII)",
    )

    gaps = (
        "Production mechanism for p-wave condensate (Drilldown §X top "
        "remaining gap — no freeze-in / freeze-out study yet)",
        "Full 3+1D fracton structure-formation simulation (all density "
        "profiles analytical/qualitative)",
        "Nonlinear fracton-GR coupling (only linearized Pretko 2017 known)",
        "First-order p→s transition dynamics if Kapustin-Spodyneiko "
        "suppression weakens at sub-leading 1/N",
        "Explicit dipole-symmetry-breaking portals beyond gravity (latter "
        "negligible at (H₀/M_d)² ~ 1e-60)",
    )

    return FractonDMAssessment(
        arrhenius_bbn_lower_MeV=arrhenius_floor,
        condensate_bbn_lower_MeV=condensate_floor,
        arrhenius_condensate_ratio=ratio,
        viable_phases_at_bbn=viable,
        excluded_phases_at_bbn=excluded,
        signatures_verified=signatures,
        surviving_empirical_hooks=hooks,
        remaining_open_questions=gaps,
    )


__all__ = [
    # Constants
    "T_BBN_MeV",
    "M_D_ARRHENIUS_BBN_MeV",
    "MU_CONDENSATE_BBN_MeV",
    "ARRHENIUS_WINDOW_UPPER_MeV",
    "PWAVE_WINDOW_UPPER_MeV",
    "Z_SUBDIFFUSION",
    "SIGMA_BULLET_CLUSTER_CM2_PER_G",
    "SIGMA_EFF_FRACTON_CM2_PER_G",
    "EOS_FRACTON_DUST",
    "FRACTON_GRAVITON_COUPLING_SIGN",
    "FRACTON_IS_SM_SINGLET",
    "CS_SQ_DIPOLE_BOUND",
    # Types
    "FractonDMPhase",
    "FractonDMCandidate",
    "FractonDMAssessment",
    # Functions
    "arrhenius_lifetime",
    "haah_superexponential_lifetime",
    "hubble_radiation_era_inv_MeV",
    "arrhenius_md_bbn_lower_bound_MeV",
    "arrhenius_survives_bbn",
    "condensate_cold",
    "condensate_lower_bound_at_epoch_MeV",
    "fracton_subdiffusion_core_radius_estimate",
    "fracton_dust_eos",
    "bullet_cluster_passes",
    "fracton_gravity_attractive",
    "fracton_ww_bypass_applies",
    "z4_subdiffusion_preserved_in_phase",
    "fracton_viable_at_epoch",
    "assess_fracton_dm_status",
    # Canonical witnesses
    "DRILLDOWN_PWAVE_1MeV",
    "ARRHENIUS_GAPPED_10MeV",
    "EXCLUDED_GAPPED_EV",
]
