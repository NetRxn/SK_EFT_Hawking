"""Non-Abelian Gauge Erasure Theorem: algebraic argument and analysis.

Encodes the universal structural theorem that non-Abelian gauge degrees of
freedom cannot survive hydrodynamization. The argument is purely algebraic,
resting on properties of higher-form symmetries and the distinction between
Goldstone bosons and domain walls.

The logical chain:
    (i)   Hydrodynamic modes arise from spontaneously broken continuous symmetries
          via the Goldstone theorem.
    (ii)  In gauge theories, the relevant symmetries are higher-form (p-form)
          symmetries, where charged operators are supported on p-dimensional
          submanifolds.
    (iii) For p ≥ 1, these operators have codimension ≥ 1 in space, so they
          necessarily commute → higher-form symmetry groups must be Abelian.
    (iv)  Non-Abelian gauge theories (SU(N), SO(N), etc.) have at most a
          discrete Z_N center symmetry, not a continuous higher-form symmetry.
    (v)   Spontaneous breaking of a discrete symmetry produces domain walls
          (topological defects), not Goldstone bosons (gapless modes).
    (vi)  Therefore: no non-Abelian gauge hydrodynamic modes.
    (vii) Contrast: U(1) gauge theory has a continuous magnetic 1-form symmetry
          U(1)^{(1)}. Its spontaneous breaking produces the photon as a
          1-form Goldstone boson (Grozdanov-Hofman-Iqbal photonization theorem).

This holds universally across:
    - Standard (Müller-Israel-Stewart) hydrodynamics
    - Fracton hydrodynamics (dipole conservation doesn't help: color charges
      are covariantly conserved, not ordinarily conserved)
    - Holographic hydrodynamics (N=4 SYM: even non-confining, all color-singlet)

References:
    - Grozdanov-Hofman-Iqbal: photonization theorem, U(1) survival
    - Hofman-Iqbal: higher-form symmetry hydrodynamics framework
    - Torrieri (2020): non-Abelian obstruction in fluids
    - Nastase-Sonnenschein (2025): non-Abelian Clebsch closure
    - Gaiotto-Kapustin-Seiberg-Willett (2015): generalized global symmetries

Lean: GaugeErasure.lean
"""

from dataclasses import dataclass
from enum import Enum
from typing import Optional


# ═══════════════════════════════════════════════════════════════════
# Group classification
# ═══════════════════════════════════════════════════════════════════

class GaugeGroupType(Enum):
    """Classification of gauge group by Abelianness."""
    ABELIAN = "abelian"           # U(1), Z_N
    NON_ABELIAN = "non_abelian"   # SU(N), SO(N), Sp(N), ...
    DISCRETE = "discrete"         # Z_N (center of SU(N))
    TRIVIAL = "trivial"           # {e}


@dataclass
class GaugeGroup:
    """A gauge group with its algebraic properties.

    Attributes:
        name: Human-readable name (e.g., "SU(3)", "U(1)")
        rank: Rank of the group (N for SU(N))
        is_abelian: Whether the group is Abelian
        is_continuous: Whether the group is continuous (Lie group) vs discrete
        center: The center subgroup (Z_N for SU(N), U(1) for U(1))
        dim: Dimension of the group as a manifold (N²-1 for SU(N), 1 for U(1))
    """
    name: str
    rank: int
    is_abelian: bool
    is_continuous: bool
    center: str  # description of center subgroup
    dim: int

    @property
    def group_type(self) -> GaugeGroupType:
        if not self.is_continuous:
            return GaugeGroupType.DISCRETE
        if self.is_abelian:
            return GaugeGroupType.ABELIAN
        return GaugeGroupType.NON_ABELIAN


# Standard gauge groups
def su(N: int) -> GaugeGroup:
    """SU(N) gauge group."""
    if N < 2:
        raise ValueError(f"SU(N) requires N ≥ 2, got {N}")
    return GaugeGroup(
        name=f"SU({N})",
        rank=N,
        is_abelian=False,
        is_continuous=True,
        center=f"Z_{N}",
        dim=N**2 - 1,
    )


def u1() -> GaugeGroup:
    """U(1) gauge group."""
    return GaugeGroup(
        name="U(1)",
        rank=1,
        is_abelian=True,
        is_continuous=True,
        center="U(1)",  # U(1) is its own center
        dim=1,
    )


def so(N: int) -> GaugeGroup:
    """SO(N) gauge group."""
    if N < 3:
        raise ValueError(f"SO(N) requires N ≥ 3 for non-Abelian, got {N}")
    center = "Z_2" if N % 2 == 1 else "Z_2 × Z_2" if N % 4 == 0 else "Z_4"
    return GaugeGroup(
        name=f"SO({N})",
        rank=N,
        is_abelian=False,
        is_continuous=True,
        center=center,
        dim=N * (N - 1) // 2,
    )


# ═══════════════════════════════════════════════════════════════════
# Higher-form symmetry analysis
# ═══════════════════════════════════════════════════════════════════

class HigherFormSymmetry(Enum):
    """Type of higher-form symmetry available."""
    CONTINUOUS_1FORM = "continuous_1form"   # U(1): magnetic 1-form symmetry
    DISCRETE_1FORM = "discrete_1form"      # SU(N): Z_N 1-form center symmetry
    NONE = "none"                           # No higher-form symmetry


class HydrodynamicFate(Enum):
    """What happens to gauge DOF upon hydrodynamization."""
    GOLDSTONE_BOSON = "goldstone_boson"     # Continuous symmetry → Goldstone
    DOMAIN_WALL = "domain_wall"             # Discrete symmetry → domain wall
    ERASURE = "erasure"                      # No surviving hydrodynamic mode
    SURVIVAL = "survival"                    # U(1): photon as 1-form Goldstone


def is_abelian(group: GaugeGroup) -> bool:
    """Check if a gauge group is Abelian.

    Lean: is_abelian_def
    """
    return group.is_abelian


def center_subgroup(group: GaugeGroup) -> str:
    """Return the center subgroup of a gauge group.

    For SU(N): center = Z_N
    For U(1): center = U(1) (the whole group)
    For SO(N): center = Z_2 or Z_2 × Z_2

    Lean: center_subgroup
    """
    return group.center


def higher_form_symmetry_type(group: GaugeGroup) -> HigherFormSymmetry:
    """Determine the type of higher-form symmetry available.

    Key theorem (Gaiotto et al. 2015, Hofman-Iqbal):
    Higher-form symmetries must be Abelian because operators on
    codimension >1 submanifolds necessarily commute.

    For U(1): continuous magnetic 1-form symmetry U(1)^{(1)}
    For SU(N): discrete Z_N 1-form center symmetry
    For SO(N): discrete Z_2 (or Z_2 × Z_2) 1-form center symmetry

    Lean: higher_form_abelian
    """
    if group.is_abelian and group.is_continuous:
        return HigherFormSymmetry.CONTINUOUS_1FORM
    elif not group.is_abelian and group.is_continuous:
        return HigherFormSymmetry.DISCRETE_1FORM
    else:
        return HigherFormSymmetry.NONE


def goldstone_or_domain_wall(symmetry: HigherFormSymmetry) -> HydrodynamicFate:
    """Determine whether symmetry breaking produces Goldstone bosons or domain walls.

    Goldstone theorem: spontaneous breaking of a continuous symmetry →
    gapless Nambu-Goldstone bosons (hydrodynamic modes).

    For discrete symmetries: breaking → topological defects (domain walls),
    NOT Goldstone bosons. Domain walls are not hydrodynamic modes.

    Lean: goldstone_requires_continuous
    """
    if symmetry == HigherFormSymmetry.CONTINUOUS_1FORM:
        return HydrodynamicFate.GOLDSTONE_BOSON
    elif symmetry == HigherFormSymmetry.DISCRETE_1FORM:
        return HydrodynamicFate.DOMAIN_WALL
    else:
        return HydrodynamicFate.ERASURE


def survives_hydrodynamization(group: GaugeGroup) -> bool:
    """Does this gauge group produce surviving hydrodynamic modes?

    The main theorem: only Abelian gauge groups survive.
    Non-Abelian → Z_N center → domain walls → erasure.
    U(1) → continuous 1-form → Goldstone → photon survives.

    Lean: gauge_erasure_theorem

    Returns:
        True if gauge DOF produce hydrodynamic modes, False otherwise.
    """
    sym = higher_form_symmetry_type(group)
    fate = goldstone_or_domain_wall(sym)
    return fate in (HydrodynamicFate.GOLDSTONE_BOSON, HydrodynamicFate.SURVIVAL)


# ═══════════════════════════════════════════════════════════════════
# Full analysis
# ═══════════════════════════════════════════════════════════════════

@dataclass
class GaugeErasureResult:
    """Complete analysis of a gauge group's hydrodynamic fate."""
    group: GaugeGroup
    is_abelian: bool
    higher_form_type: HigherFormSymmetry
    fate: HydrodynamicFate
    survives: bool
    explanation: str


def gauge_erasure_analysis(group: GaugeGroup) -> GaugeErasureResult:
    """Perform complete gauge erasure analysis for a given gauge group.

    This implements the full logical chain of the theorem:
    group → Abelian? → higher-form symmetry type → Goldstone/domain wall → fate

    Args:
        group: The gauge group to analyze.

    Returns:
        GaugeErasureResult with complete analysis.
    """
    abelian = is_abelian(group)
    hf_type = higher_form_symmetry_type(group)
    fate = goldstone_or_domain_wall(hf_type)
    survives = survives_hydrodynamization(group)

    if survives:
        explanation = (
            f"{group.name} is Abelian → has continuous magnetic 1-form symmetry "
            f"U(1)^{{(1)}} → spontaneous breaking produces 1-form Goldstone "
            f"boson (the photon) → gauge DOF survive hydrodynamization. "
            f"(Grozdanov-Hofman-Iqbal photonization theorem)"
        )
    else:
        if not abelian:
            explanation = (
                f"{group.name} is non-Abelian → higher-form symmetries must be "
                f"Abelian (codimension >1 operators commute) → only discrete "
                f"center symmetry {group.center} available → spontaneous breaking "
                f"of {group.center} produces domain walls, not Goldstone bosons → "
                f"no hydrodynamic modes → gauge DOF erased upon hydrodynamization. "
                f"Universal across standard, fracton, and holographic hydro."
            )
        else:
            explanation = (
                f"{group.name} has no relevant higher-form symmetry → "
                f"no hydrodynamic modes from gauge sector."
            )

    return GaugeErasureResult(
        group=group,
        is_abelian=abelian,
        higher_form_type=hf_type,
        fate=fate,
        survives=survives,
        explanation=explanation,
    )


# ═══════════════════════════════════════════════════════════════════
# Standard Model analysis
# ═══════════════════════════════════════════════════════════════════

def standard_model_analysis() -> dict[str, GaugeErasureResult]:
    """Analyze the Standard Model gauge group SU(3) × SU(2) × U(1).

    Result:
    - SU(3)_c (QCD): ERASED — Z_3 center → domain walls, no gluon hydro modes
    - SU(2)_L (weak): ERASED — Z_2 center → domain walls, no W/Z hydro modes
    - U(1)_Y (hypercharge): SURVIVES — continuous 1-form → photon is Goldstone

    After electroweak symmetry breaking (SU(2)_L × U(1)_Y → U(1)_EM):
    - Only U(1)_EM survives as a hydrodynamic mode (the photon)
    - The massive W±, Z bosons do not produce hydrodynamic modes
    """
    return {
        'SU(3)_c': gauge_erasure_analysis(su(3)),
        'SU(2)_L': gauge_erasure_analysis(su(2)),
        'U(1)_Y': gauge_erasure_analysis(u1()),
    }


# ═══════════════════════════════════════════════════════════════════
# N=4 SYM decisive test
# ═══════════════════════════════════════════════════════════════════

def n4_sym_analysis() -> GaugeErasureResult:
    """Analyze N=4 SU(N) Super-Yang-Mills as the decisive test case.

    N=4 SYM is non-confining at ALL couplings (it is conformal).
    Color-charged states exist in the spectrum at all coupling strengths.
    Yet holographic hydrodynamics (via AdS/CFT) involves EXCLUSIVELY
    color-singlet operators.

    This is the decisive evidence: even when confinement does NOT erase
    color charges, hydrodynamization still does. The gauge erasure is
    structural (from higher-form symmetry commutativity), not dynamical
    (from confinement).

    Returns:
        GaugeErasureResult for SU(N) in N=4 SYM context.
    """
    # N=4 SYM is typically studied with SU(N) gauge group
    # The large-N limit is the holographic case
    group = su(4)  # Representative; result holds for any N ≥ 2
    result = gauge_erasure_analysis(group)
    result.explanation += (
        " N=4 SYM is the decisive test: non-confining at all couplings, "
        "yet holographic hydro involves only color-singlet operators. "
        "Erasure is structural, not from confinement."
    )
    return result
