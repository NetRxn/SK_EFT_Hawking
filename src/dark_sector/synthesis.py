"""Phase 5x Wave 8 — Dark Sector Synthesis and Cross-Connections.

Python companion to ``lean/SKEFTHawking/DarkSectorSynthesis.lean``. This
module consumes the shipped Phase 5x Python modules (``z16_hidden_sector``,
``adw_cosmological_constant``, ``fracton_dm``) and produces a structured
cross-connection assessment used by the Wave 8 memo and, downstream, by
the Paper 17 narrative.

No new physics: every claim here is either a cross-check against a Lean
theorem in ``DarkSectorSynthesis.lean`` or a structured report of
already-shipped Phase 5x data.

Lean refs
---------
- ``CC3 fg_torsion_vs_fracton_dust_eos_distinct``
- ``CC4 adw_cc_vs_fracton_dm_eos_distinct``
- ``CC4' adw_cc_vs_fg_torsion_eos_distinct``
- ``CC5 cored_profile_mechanisms_distinct``
- ``CC7 torsion_channels_distinct_sources_distinct``
- ``phase5x_candidates_viability_matrix``
- ``Rank1 empirical_hook_ranking_strict``

Aristotle: manual (no Aristotle-proved content).
Source: Phase 5x Wave 8 deliverables; roadmap
``docs/roadmaps/Phase5x_Roadmap.md`` §Wave 8.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Mapping

from src.dark_sector.adw_cosmological_constant import (
    assess_cosmological_constant_status,
)
from src.dark_sector.fracton_dm import (
    DRILLDOWN_PWAVE_1MeV,
    FractonDMPhase,
    assess_fracton_dm_status,
)
from src.dark_sector.z16_hidden_sector import (
    DM_CANDIDATE_MATRIX,
    DMCandidate,
)


# ---------------------------------------------------------------------------
# 1. Canonical equation-of-state coefficients per sector
# ---------------------------------------------------------------------------


#: Fang-Gu torsion-DM tree-level EoS with traceless T^μν (W4).
#: Matches Lean ``DarkSectorSynthesis.eos_fg_traceless``.
EOS_FG_TRACELESS: float = 1.0 / 3.0

#: ADW cosmological-constant sector EoS (W3).
#: Matches Lean ``DarkSectorSynthesis.eos_cosmological_constant``.
EOS_COSMOLOGICAL_CONSTANT: float = -1.0

#: Fracton dust EoS (W7).
#: Matches Lean ``DarkSectorSynthesis.eos_fracton = eos_fracton_dust``.
EOS_FRACTON: float = 0.0


def eos_pairs_all_distinct() -> bool:
    """Return True iff the three canonical EoS coefficients are pairwise
    distinct. Python cross-check for Lean CC3 + CC4 + CC4'.
    """
    return (
        EOS_FG_TRACELESS != EOS_FRACTON
        and EOS_COSMOLOGICAL_CONSTANT != EOS_FRACTON
        and EOS_COSMOLOGICAL_CONSTANT != EOS_FG_TRACELESS
    )


# ---------------------------------------------------------------------------
# 2. Emergent-gravity DM kinds and collective invisibility
# ---------------------------------------------------------------------------


class EmergentGravityDMKind(str, Enum):
    """Phase 5x canonical DM candidate kinds (all SM-singlet)."""

    Z16_TOPOLOGICAL_T0 = "Z16Topological_T0"
    Z16_SINGLET_S0 = "Z16Singlet_S0"
    Z16_MIXED_C1 = "Z16Mixed_C1"
    FG_TORSION = "FGTorsion"
    FRACTON_PWAVE = "FractonPWave"


#: Conservative log10 bound on the direct-detection cross-section in cm²
#: per kind. Matches Lean ``DarkSectorSynthesis.direct_detection_sigma_log10_cap``.
#: -999 encodes "no local operator / no perturbative coupling" (T-0, fracton).
DIRECT_DETECTION_SIGMA_LOG10_CAP: Mapping[EmergentGravityDMKind, int] = {
    EmergentGravityDMKind.Z16_TOPOLOGICAL_T0: -999,
    EmergentGravityDMKind.Z16_SINGLET_S0: -50,
    EmergentGravityDMKind.Z16_MIXED_C1: -50,
    EmergentGravityDMKind.FG_TORSION: -90,
    EmergentGravityDMKind.FRACTON_PWAVE: -999,
}

#: LZ / XENONnT sensitivity floor (log10 cm²). Any candidate with a cap
#: below this is invisible to current direct-detection experiments.
DIRECT_DETECTION_CURRENT_FLOOR_LOG10: int = -48

#: Visibility threshold used by CC2. Every Phase 5x emergent-gravity
#: candidate has a cap below this threshold.
INVISIBLE_THRESHOLD_LOG10: int = -50


def is_invisible_to_direct_detection(kind: EmergentGravityDMKind) -> bool:
    """Return True iff ``kind``'s σ_DD cap is at or below the invisibility
    threshold. Python cross-check for Lean CC2
    ``emergent_gravity_dm_invisible_collective``.
    """
    return DIRECT_DETECTION_SIGMA_LOG10_CAP[kind] <= INVISIBLE_THRESHOLD_LOG10


def all_emergent_gravity_dm_invisible() -> bool:
    """Return True iff all five kinds satisfy the invisibility bound."""
    return all(is_invisible_to_direct_detection(k) for k in EmergentGravityDMKind)


# ---------------------------------------------------------------------------
# 3. Cored-profile mechanism taxonomy
# ---------------------------------------------------------------------------


class CoredProfileMechanism(str, Enum):
    """Mechanisms that can produce cored galactic DM density profiles."""

    SOLITON_CONDENSATE = "SolitonCondensate"  # SFDM (Berezhiani-Khoury)
    Z4_SUBDIFFUSION = "Z4Subdiffusion"  # fracton DM (W7)
    NFW_PSEUDO_CUSP = "NFWPseudoCusp"  # standard CDM (cuspy, not cored)


#: Mechanism → produces cored profile. Matches Lean
#: ``DarkSectorSynthesis.produces_cored_profile``.
PRODUCES_CORED_PROFILE: Mapping[CoredProfileMechanism, bool] = {
    CoredProfileMechanism.SOLITON_CONDENSATE: True,
    CoredProfileMechanism.Z4_SUBDIFFUSION: True,
    CoredProfileMechanism.NFW_PSEUDO_CUSP: False,
}


def cored_mechanisms_are_distinct() -> bool:
    """Python cross-check for Lean CC5 ``cored_profile_mechanisms_distinct``."""
    return (
        CoredProfileMechanism.SOLITON_CONDENSATE
        != CoredProfileMechanism.Z4_SUBDIFFUSION
    )


# ---------------------------------------------------------------------------
# 4. Two-torsion-channel independence
# ---------------------------------------------------------------------------


class TorsionChannel(str, Enum):
    """Lorentz-irreducible components of the torsion tensor."""

    ANTISYMMETRIC = "Antisymmetric"
    TRACE = "Trace"
    PURE_TENSOR = "PureTensor"


class TorsionSource(str, Enum):
    """Physics origins of a torsion contribution considered in Phase 5x."""

    DIRAC_AXIAL = "DiracAxial"  # Boos-Hehl Einstein-Cartan
    FG_LOOP_THETA = "FGLoopTheta"  # Fang-Gu e-loop θ-term
    NO_SOURCE = "NoSource"


#: Mapping torsion source → Lorentz-irreducible channel. Matches Lean
#: ``DarkSectorSynthesis.channel_of_source``. Dirac axial current sources
#: totally antisymmetric torsion (Kibble-Sciama-Hehl); FG e-loop θ-term
#: sources trace-vector torsion (FG 2021 Eq. (3.6)).
CHANNEL_OF_SOURCE: Mapping[TorsionSource, TorsionChannel] = {
    TorsionSource.DIRAC_AXIAL: TorsionChannel.ANTISYMMETRIC,
    TorsionSource.FG_LOOP_THETA: TorsionChannel.TRACE,
    TorsionSource.NO_SOURCE: TorsionChannel.PURE_TENSOR,
}


def torsion_sources_distinct_imply_channels_distinct() -> bool:
    """Python cross-check for Lean CC7
    ``torsion_channels_distinct_sources_distinct``: over all ordered
    pairs of distinct sources, the assigned channels differ.
    """
    sources = list(TorsionSource)
    return all(
        CHANNEL_OF_SOURCE[s1] != CHANNEL_OF_SOURCE[s2]
        for s1 in sources
        for s2 in sources
        if s1 is not s2
    )


# ---------------------------------------------------------------------------
# 5. Synthesis structure and candidate matrix
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class DarkSectorCandidate:
    """Phase 5x dark-sector DM candidate record for the Wave 8 matrix.

    ``basic_viability`` aggregates the Phase 5x verdict for this
    candidate:

    - T-0, S-0, C-1 → True (W2 + W2b viable)
    - FG torsion    → False (W4 kinematically obstructed at CDM level)
    - Fracton p-wave → True (W7 Drilldown VIABLE conditional)
    """

    kind: EmergentGravityDMKind
    label: str
    basic_viability: bool
    verdict_source: str


CANDIDATE_T0 = DarkSectorCandidate(
    kind=EmergentGravityDMKind.Z16_TOPOLOGICAL_T0,
    label="T-0: K-gauge TQFT (Wang Ultra-Unification)",
    basic_viability=True,
    verdict_source="W2 + deep research: PREFERRED when ν_R absent",
)
CANDIDATE_S0 = DarkSectorCandidate(
    kind=EmergentGravityDMKind.Z16_SINGLET_S0,
    label="S-0: 3 sterile Weyl fermions",
    basic_viability=True,
    verdict_source="W2 three_singlets_satisfy_hidden_sector",
)
CANDIDATE_C1 = DarkSectorCandidate(
    kind=EmergentGravityDMKind.Z16_MIXED_C1,
    label="C-1: Wan-Wang 7+1 mixed-charge (dark SU(3), 8 flavors)",
    basic_viability=True,
    verdict_source="W2b Track X c1_wan_wang_joint_constraint",
)
CANDIDATE_FG = DarkSectorCandidate(
    kind=EmergentGravityDMKind.FG_TORSION,
    label="FG torsion DM (uncondensed e-loops)",
    basic_viability=False,
    verdict_source="W4 fg_cdm_obstruction (tree-level w=1/3 kinematic)",
)
CANDIDATE_FRACTON_PWAVE = DarkSectorCandidate(
    kind=EmergentGravityDMKind.FRACTON_PWAVE,
    label="Fracton p-wave dipole superfluid @ μ=1 MeV",
    basic_viability=True,
    verdict_source="W7 Drilldown: VIABLE conditional (p-wave phase, Dark QCD UV)",
)


#: The five canonical Phase 5x candidates in roadmap-order.
PHASE5X_CANDIDATE_MATRIX: tuple[DarkSectorCandidate, ...] = (
    CANDIDATE_T0,
    CANDIDATE_S0,
    CANDIDATE_C1,
    CANDIDATE_FG,
    CANDIDATE_FRACTON_PWAVE,
)


def count_viable_phase5x_candidates() -> int:
    """Number of ``basic_viability`` candidates in the Phase 5x matrix.

    Cross-check for Lean ``phase5x_viable_candidate_count``.
    """
    return sum(1 for c in PHASE5X_CANDIDATE_MATRIX if c.basic_viability)


# ---------------------------------------------------------------------------
# 6. Empirical-hook ranking
# ---------------------------------------------------------------------------


class EmpiricalHook(str, Enum):
    """The five post-W1b empirical hooks identified by Phase 5x."""

    MERGER_SONIC_BOOM = "MergerSonicBoom"  # #1 (W1b Task 9)
    FRACTON_CORE_CUSP = "FractonCoreCusp"  # #2 (W7 Drilldown)
    EP_VIOLATION_STEP = "EPViolationSTEP"  # #3 (vestigial relics, Phase 6)
    DESI_DR3 = "DESIDeR3"  # #4 (W1b Task 7)
    DIRECT_NUCLEAR_RECOIL = "DirectNuclearRecoil"  # #5


#: Hook → priority score (higher = more detectable + sooner). Matches
#: Lean ``DarkSectorSynthesis.hook_priority``.
HOOK_PRIORITY: Mapping[EmpiricalHook, int] = {
    EmpiricalHook.MERGER_SONIC_BOOM: 5,
    EmpiricalHook.FRACTON_CORE_CUSP: 4,
    EmpiricalHook.EP_VIOLATION_STEP: 3,
    EmpiricalHook.DESI_DR3: 2,
    EmpiricalHook.DIRECT_NUCLEAR_RECOIL: 1,
}


def ranked_empirical_hooks() -> tuple[EmpiricalHook, ...]:
    """Hooks sorted high → low priority (Paper 17 Table 4 ordering)."""
    return tuple(sorted(EmpiricalHook, key=lambda h: -HOOK_PRIORITY[h]))


def merger_outranks_direct_detection() -> bool:
    """Cross-check for Lean Rank2 ``merger_outranks_direct_detection``."""
    return (
        HOOK_PRIORITY[EmpiricalHook.MERGER_SONIC_BOOM]
        > HOOK_PRIORITY[EmpiricalHook.DIRECT_NUCLEAR_RECOIL]
    )


# ---------------------------------------------------------------------------
# 7. Cross-connection matrix
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class CrossConnection:
    """A single Phase 5x cross-connection between two (or more) waves.

    Mirrors the roadmap Wave 8 "Cross-Connections Identified by Deep
    Research" table.
    """

    connection_id: str
    waves: tuple[str, ...]
    strength: str  # "High" / "Medium-High" / "Medium" / "Conceptual" / "Thematic"
    summary: str
    lean_backing: str  # Name of the corresponding Lean theorem or "memo-only"


CROSS_CONNECTION_MATRIX: tuple[CrossConnection, ...] = (
    CrossConnection(
        connection_id="Z16_x_fracton",
        waves=("W2", "W7"),
        strength="Medium",
        summary=(
            "Fracton DM is SM-gauge-singlet (YM incompatibility), so it is "
            "compatible with any ℤ₁₆ hidden sector. T-0 (TQFT, zero particles) "
            "can coexist with fracton extended objects."
        ),
        lean_backing="hidden_sector_fracton_compatible",
    ),
    CrossConnection(
        connection_id="Z16_x_vestigial",
        waves=("W2", "W6"),
        strength="Medium-High",
        summary=(
            "If vestigial relics carry the +3 mod 16 anomaly charge, decay "
            "via ℤ₁₆-preserving channels is obstructed. Existence of the "
            "charge is a Phase 6 hypothesis (needs coset homotopy + bordism)."
        ),
        lean_backing="z16_vestigial_stability_under_hypothesis",
    ),
    CrossConnection(
        connection_id="ADW_CC_x_SFDM",
        waves=("W3", "W5"),
        strength="Conceptual",
        summary=(
            "Volovik residual Λ ~ T⁴ mechanism and SFDM condensate may share "
            "a common fermionic-vacuum substrate. No quantitative link."
        ),
        lean_backing="memo-only (W5 not yet shipped)",
    ),
    CrossConnection(
        connection_id="FG_x_ADW_vestigial",
        waves=("W4", "W6"),
        strength="High",
        summary=(
            "Two independent torsion channels coexist in the tetrad phase: "
            "Dirac axial current (antisymmetric, Boos-Hehl) and FG loop-θ "
            "(trace, Fang-Gu). Their irreducible decomposition is orthogonal."
        ),
        lean_backing="torsion_channels_distinct_sources_distinct",
    ),
    CrossConnection(
        connection_id="SFDM_x_fracton",
        waves=("W5", "W7"),
        strength="Medium",
        summary=(
            "Both produce cored galactic profiles but via orthogonal "
            "mechanisms: SFDM from soliton condensate vs fracton from z=4 "
            "subdiffusion. Distinguishable by outer-halo profile."
        ),
        lean_backing="cored_profile_mechanisms_distinct",
    ),
    CrossConnection(
        connection_id="EoS_distinctness",
        waves=("W3", "W4", "W7"),
        strength="High",
        summary=(
            "The three Phase 5x stress-energy sectors have pairwise distinct "
            "EoS: w_Λ = -1 (CC sector), w_FG = 1/3 (radiation-like traceless), "
            "w_fracton = 0 (pressureless dust). No two sectors coincide."
        ),
        lean_backing="fg_torsion_vs_fracton_dust_eos_distinct (+CC4, +CC4')",
    ),
    CrossConnection(
        connection_id="collective_invisibility",
        waves=("W2", "W4", "W7"),
        strength="Thematic",
        summary=(
            "Every Phase 5x emergent-gravity DM candidate is invisible to "
            "nuclear-recoil direct detection: T-0 has no local ops; FG σ ~ "
            "10⁻⁹⁰ cm²; fracton σ_eff = 0; S-0/S-1/C-1 all below current LZ."
        ),
        lean_backing="emergent_gravity_dm_invisible_collective",
    ),
)


# ---------------------------------------------------------------------------
# 8. Overall assessment report
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class DarkSectorSynthesisAssessment:
    """Structured report of the Phase 5x Wave 8 synthesis.

    Fields
    ------
    viable_candidate_count : int
        Number of basic-viable Phase 5x candidates (CC matrix passes).
    all_invisible : bool
        True iff every Phase 5x emergent-gravity DM candidate is
        invisible to direct detection at the ``INVISIBLE_THRESHOLD_LOG10``
        threshold.
    eos_all_distinct : bool
        True iff the three canonical EoS coefficients are pairwise
        distinct.
    cored_mechanisms_distinct : bool
        True iff soliton-condensate and z=4-subdiffusion mechanisms
        are distinct.
    torsion_channels_independent : bool
        True iff distinct torsion sources map to distinct channels.
    top_hook : EmpiricalHook
        Rank-1 empirical hook (expected: MERGER_SONIC_BOOM).
    cross_connection_count : int
        Number of cross-connection records in
        ``CROSS_CONNECTION_MATRIX``.
    lean_backed_connection_count : int
        Number of cross-connections that have a Lean theorem backing.
    """

    viable_candidate_count: int
    all_invisible: bool
    eos_all_distinct: bool
    cored_mechanisms_distinct: bool
    torsion_channels_independent: bool
    top_hook: EmpiricalHook
    cross_connection_count: int
    lean_backed_connection_count: int


def assess_dark_sector_synthesis() -> DarkSectorSynthesisAssessment:
    """Structured report of the Phase 5x Wave 8 synthesis.

    Every field is computed from the module-level constants + shipped
    Phase 5x data. Intended as a single-entry-point for the Wave 8 memo
    and for Paper 17 Table generation.
    """
    return DarkSectorSynthesisAssessment(
        viable_candidate_count=count_viable_phase5x_candidates(),
        all_invisible=all_emergent_gravity_dm_invisible(),
        eos_all_distinct=eos_pairs_all_distinct(),
        cored_mechanisms_distinct=cored_mechanisms_are_distinct(),
        torsion_channels_independent=torsion_sources_distinct_imply_channels_distinct(),
        top_hook=ranked_empirical_hooks()[0],
        cross_connection_count=len(CROSS_CONNECTION_MATRIX),
        lean_backed_connection_count=sum(
            1
            for c in CROSS_CONNECTION_MATRIX
            if not c.lean_backing.startswith("memo-only")
        ),
    )


# ---------------------------------------------------------------------------
# 9. Convenience re-exports for downstream callers (W9)
# ---------------------------------------------------------------------------


def phase5x_upstream_wave_reports() -> dict[str, object]:
    """Bundle the upstream-wave structured reports in one call.

    Used by the W9 Paper 17 draft pipeline to get every Phase 5x input
    in a single ``dict`` without re-importing from each submodule.
    """
    return {
        "cosmological_constant": assess_cosmological_constant_status(),
        "fracton_dm": assess_fracton_dm_status(),
        "fracton_preferred_witness": DRILLDOWN_PWAVE_1MeV,
        "z16_dm_candidate_matrix": DM_CANDIDATE_MATRIX,
    }


def z16_candidate_by_tag(tag: str) -> DMCandidate:
    """Fetch a Z16 DM candidate from the matrix by tag."""
    return DM_CANDIDATE_MATRIX[tag]


def dm_phase_label_for_fracton_pwave() -> str:
    """Human-readable label for the preferred Drilldown fracton phase."""
    assert DRILLDOWN_PWAVE_1MeV.phase is FractonDMPhase.PWAVE_CONDENSATE
    return DRILLDOWN_PWAVE_1MeV.label
