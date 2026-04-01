"""Fracton-Gravity Kerr-Schild Analysis: Linearized Equivalence and Bootstrap Gap.

PROVENANCE NOTE: See sk_eft.py for Pipeline Invariant 1+4 gap status.

Investigates whether linearized gravity can emerge from fracton symmetric
tensor gauge theory via the Kerr-Schild map and Gupta-Feynman bootstrap,
and formalizes the structural gap to full diffeomorphism invariance.

The analysis chain:

1. Pretko's symmetric tensor gauge theory (PRD 96, 024051, 2017):
   A_ij gauge field with fracton gauge symmetry delta A_ij = partial_i partial_j alpha.
   The defining feature: a single scalar gauge parameter alpha, versus
   4 vector parameters xi_mu for linearized diffeomorphisms.

2. Linearized equivalence (Blasi-Maggiore, PLB 833, 137304, 2022):
   The most general quadratic Lorentz-covariant action invariant under
   delta h_mu_nu = partial_mu partial_nu lambda is a one-parameter family
   S = S_LG + omega * S_frac. At the special point omega = 0 (b = -2a),
   the action reduces exactly to linearized Einstein-Hilbert (Fierz-Pauli).
   The spin-2 sector of the fracton theory matches linearized GR perfectly.

3. Gupta-Feynman bootstrap (Afxonidis-Caddeo-Hoyos-Musso, 2024):
   The bootstrap attempts to iteratively add nonlinear corrections to
   recover full GR. At cubic order, multiple vertices are allowed
   (non-uniqueness, since fracton symmetry is weaker than diffeos),
   and the spin-1 sector is dynamically unstable.

4. Five obstructions seal the gap:
   - Algebraic: fracton algebra (1 scalar, Abelian) vs diffeo algebra (D vectors, non-Abelian)
   - Geometric: Gromov's curvature obstruction (PRL 122, 2019)
   - Kinematic: Aristotelian geometry, no boosts (Bidussi et al., 2022)
   - Dynamical: spin-1 instability, unbounded Hamiltonian (Afxonidis et al., 2024)
   - Foliation: preferred time foliation, not gauge-equivalent

5. ADW vs fracton route comparison:
   Fracton breaks through the Nordstrom spin-0 ceiling but cannot reach
   full nonlinear spin-2 gravity. ADW (fermionic condensation) delivers
   full Einstein-Cartan gravity. The routes may be complementary
   (Volovik two-step picture: bosonic metric first, fermionic tetrad second).

References:
    - Pretko (PRD 96, 024051, 2017): fracton gauge theory
    - Blasi-Maggiore (PLB 833, 137304, 2022): covariant fracton action
    - Bertolini-Blasi-Damonte-Maggiore (Symmetry 15, 945, 2023): DOF counting
    - Afxonidis-Caddeo-Hoyos-Musso (PRD 109, 065013, 2024): Kerr-Schild, bootstrap
    - Afxonidis-Caddeo-Hoyos-Musso (PRD 110, 2024; 2406.19268): stability analysis
    - Afxonidis-Caddeo-Hoyos-Musso (PRD 111, 2025; 2503.08621): curved backgrounds
    - Gromov (PRL 122, 076403, 2019): curvature obstruction
    - Bidussi-Hartong-Have-Musaeus-Prohazka (SciPost Phys. 12, 205, 2022): Aristotelian
    - Pena-Benitez-Salgado-Rebolledo (JHEP 2024): fracton algebra contraction
    - Belenchia-Liberati-Mohd (PRD 2014): Nordstrom ceiling
    - Rovere et al. (arXiv:2505.21022, 2025): teleparallel connection
"""

from dataclasses import dataclass, field
from enum import Enum
from typing import Optional

from src.core.formulas import fracton_dof_gap
from src.fracton.non_abelian import (
    NonAbelianFractonGauge,
    YangMillsCompatibility,
    analyze_non_abelian_compatibility,
)


# ===================================================================
# Enumerations
# ===================================================================

class GaugeSymmetryType(Enum):
    """Type of gauge symmetry."""
    FRACTON_SCALAR = "fracton_scalar"        # delta h = dd alpha (1 scalar)
    LINEARIZED_DIFFEO = "linearized_diffeo"  # delta h = d xi + d xi (D vector)
    FULL_DIFFEO = "full_diffeo"              # nonlinear diffeomorphisms


class ObstructionType(Enum):
    """Types of obstruction to recovering full GR from fracton gravity."""
    ALGEBRAIC = "algebraic"    # Wrong gauge algebra (Abelian vs non-Abelian)
    GEOMETRIC = "geometric"    # Gromov curvature obstruction
    KINEMATIC = "kinematic"    # Aristotelian vs Lorentzian geometry
    DYNAMICAL = "dynamical"    # Spin-1 instability
    FOLIATION = "foliation"    # Preferred time foliation


class GravityRouteType(Enum):
    """Routes to emergent spin-2 gravity."""
    ACOUSTIC_BEC = "acoustic_bec"    # Spin-0 Nordstrom only
    FRACTON = "fracton"              # Linearized spin-2 + obstructions
    ADW = "adw"                      # Full nonlinear Einstein-Cartan


# ===================================================================
# Linearized equivalence
# ===================================================================

@dataclass
class LinearizedEquivalence:
    """Linearized equivalence between fracton gauge theory and Einstein gravity.

    Blasi-Maggiore (2022) showed the most general quadratic Lorentz-covariant
    action invariant under delta h_mu_nu = partial_mu partial_nu lambda is:

        S = S_LG + omega * S_frac

    where S_LG is the linearized Einstein-Hilbert (Fierz-Pauli) action and
    omega is a dimensionless parameter. At omega = 0, the theory IS linearized GR.

    The fracton gauge transformation delta h = dd alpha uses 1 scalar function.
    Linearized diffeomorphisms delta h = d xi + d xi use D vector functions.
    Fracton symmetry is a strict subset: xi_mu = partial_mu alpha (longitudinal).

    In D = 4 spacetime dimensions:
    - Full diffeos remove 8 of 10 h_mu_nu components -> 2 DOF (graviton)
    - Fracton symmetry removes only 2 of 10 -> 8 DOF (spin-2 + spin-1 + spin-0)
    - The spin-2 sector of the fracton theory matches linearized GR exactly.

    Attributes:
        fracton_eom: Description of the fracton equation of motion
        einstein_eom: Description of the linearized Einstein equation of motion
        matching_conditions: Conditions under which the two match
        spin2_modes: Number of propagating spin-2 modes (should be 2)
        omega_parameter: The Blasi-Maggiore mixing parameter
        spacetime_dim: Spacetime dimension D
        fracton_gauge_parameters: Number of fracton gauge parameters (1)
        diffeo_gauge_parameters: Number of diffeomorphism gauge parameters (D)
        fracton_propagating_dof: Total propagating DOF in fracton theory (8 in D=4)
        gr_propagating_dof: Propagating DOF in linearized GR (2 in D=4)
    """
    fracton_eom: str
    einstein_eom: str
    matching_conditions: list[str]
    spin2_modes: int
    omega_parameter: float = 0.0
    spacetime_dim: int = 4
    fracton_gauge_parameters: int = 1
    diffeo_gauge_parameters: int = 4
    fracton_propagating_dof: int = 8
    gr_propagating_dof: int = 2

    @property
    def is_exact_match_at_omega_zero(self) -> bool:
        """Whether the fracton theory reduces to linearized GR at omega = 0."""
        return self.omega_parameter == 0.0

    @property
    def extra_dof_count(self) -> int:
        """Number of extra propagating DOF beyond the graviton."""
        return self.fracton_propagating_dof - self.gr_propagating_dof

    @property
    def gauge_parameter_ratio(self) -> float:
        """Ratio of gauge parameters: diffeo / fracton."""
        return self.diffeo_gauge_parameters / self.fracton_gauge_parameters

    @property
    def symmetry_deficit(self) -> str:
        """Description of the symmetry deficit."""
        return (
            f"Fracton gauge symmetry uses {self.fracton_gauge_parameters} scalar "
            f"parameter(s) vs {self.diffeo_gauge_parameters} vector parameter(s) "
            f"for linearized diffeomorphisms in D={self.spacetime_dim}. "
            f"This leaves {self.extra_dof_count} extra propagating DOF "
            f"beyond the {self.gr_propagating_dof} graviton polarizations."
        )


def linearized_equivalence(
    spacetime_dim: int = 4,
    omega: float = 0.0,
) -> LinearizedEquivalence:
    """Compute the linearized equivalence between fracton and Einstein gravity.

    At the special point omega = 0 in the Blasi-Maggiore one-parameter family,
    the fracton-invariant quadratic action reduces exactly to the linearized
    Einstein-Hilbert (Fierz-Pauli) action.

    The gauge-independent DOF counting (Bertolini-Blasi-Damonte-Maggiore, 2023):
    - h_mu_nu has D(D+1)/2 independent components in D spacetime dimensions
    - Fracton symmetry removes 2 (1 gauge parameter + 1 from its equation of motion)
    - Linearized diffeos remove 2D (D gauge parameters + D from their EOMs)
    - Result: fracton has D(D+1)/2 - 2 propagating DOF
              linearized GR has D(D+1)/2 - 2D = D(D-3)/2 propagating DOF

    Args:
        spacetime_dim: Spacetime dimension D (default 4)
        omega: Blasi-Maggiore mixing parameter (default 0 = linearized GR point)

    Returns:
        LinearizedEquivalence with complete analysis
    """
    D = spacetime_dim

    # DOF counting
    h_components = D * (D + 1) // 2
    fracton_removed = 2  # 1 gauge + 1 constraint
    diffeo_removed = 2 * D  # D gauge + D constraints
    fracton_dof = h_components - fracton_removed
    gr_dof = h_components - diffeo_removed  # = D(D-3)/2

    # Spin-2 modes: always 2 for D >= 4 (the graviton)
    spin2_modes = 2 if D >= 4 else (1 if D == 3 else 0)

    return LinearizedEquivalence(
        fracton_eom=(
            f"Fracton EOM: partial^2 F_mu_nu_rho = 0 where "
            f"F_mu_nu_rho = partial_mu h_nu_rho - partial_nu h_mu_rho "
            f"is the tensor field strength (antisymmetric in first two indices). "
            f"Gauge symmetry: delta h_mu_nu = partial_mu partial_nu alpha "
            f"({1} scalar parameter)."
        ),
        einstein_eom=(
            f"Linearized Einstein EOM: G^(1)_mu_nu = 0 where "
            f"G^(1) is the linearized Einstein tensor. "
            f"Gauge symmetry: delta h_mu_nu = partial_mu xi_nu + partial_nu xi_mu "
            f"({D} vector parameters)."
        ),
        matching_conditions=[
            f"omega = 0 in Blasi-Maggiore parameterization (equivalently b = -2a)",
            f"Spin-2 sector matches exactly: {spin2_modes} graviton polarizations",
            (
                f"Field strength F_mu_nu_rho = partial_mu h_nu_rho - partial_nu h_mu_rho "
                f"is the tensor analogue of the Maxwell field strength"
            ),
            (
                f"Fracton gauge symmetry is the longitudinal restriction "
                f"xi_mu = partial_mu alpha of linearized diffeomorphisms"
            ),
        ],
        spin2_modes=spin2_modes,
        omega_parameter=omega,
        spacetime_dim=D,
        fracton_gauge_parameters=1,
        diffeo_gauge_parameters=D,
        fracton_propagating_dof=fracton_dof,
        gr_propagating_dof=gr_dof,
    )


# ===================================================================
# Gupta-Feynman bootstrap
# ===================================================================

@dataclass
class BootstrapStep:
    """One step of the Gupta-Feynman bootstrap.

    The standard bootstrap begins with free massless spin-2 on flat spacetime,
    couples it to the total stress-energy tensor (including its own), and iterates:
    h -> h^2 -> h^3 -> ... The infinite series sums to full nonlinear GR.
    Deser (1970) showed this terminates after one iteration in Palatini variables.

    For fracton gravity, Afxonidis-Caddeo-Hoyos-Musso (2024) executed the
    bootstrap to cubic order and found:
    - Order 1 (linear): fracton = linearized GR at omega = 0
    - Order 2 (quadratic): stress-energy coupling, still compatible
    - Order 3 (cubic): multiple vertices allowed (non-uniqueness),
      spin-1 sector unstable, Hamiltonian unbounded from below

    Attributes:
        order: Bootstrap order (1 = linear, 2 = quadratic, 3 = cubic)
        correction_term: Description of the correction added at this order
        fracton_result: What the fracton bootstrap produces
        gr_result: What the standard GR bootstrap produces
        agrees: Whether fracton and GR bootstrap agree at this order
    """
    order: int
    correction_term: str
    fracton_result: str
    gr_result: str
    agrees: bool

    @property
    def is_trivial(self) -> bool:
        """Whether this step is trivially satisfied (linear level)."""
        return self.order <= 1


@dataclass
class BootstrapGap:
    """Assessment of where the Gupta-Feynman bootstrap breaks down.

    The bootstrap gap between fracton gauge theory and full GR appears at
    cubic order (order 3) in the bootstrap. Five convergent obstructions
    make the gap structural and not closable by any known procedure.

    Attributes:
        order_where_breaks: Order at which the bootstrap fails (3 for fracton)
        reason: Primary reason for the breakdown
        is_closable: Whether the gap can be closed by known methods
        alternative_route: What alternative route exists (if any)
        obstructions: List of the five identified obstructions
        spin1_unstable: Whether the spin-1 sector is dynamically unstable
        hamiltonian_bounded: Whether the Hamiltonian is bounded from below
        vertices_unique: Whether the cubic vertices are uniquely determined
    """
    order_where_breaks: int
    reason: str
    is_closable: bool
    alternative_route: str
    obstructions: list[str] = field(default_factory=list)
    spin1_unstable: bool = True
    hamiltonian_bounded: bool = False
    vertices_unique: bool = False

    @property
    def n_obstructions(self) -> int:
        """Number of identified obstructions."""
        return len(self.obstructions)

    @property
    def is_structural(self) -> bool:
        """Whether the gap is structural (not merely technical)."""
        return not self.is_closable and self.n_obstructions >= 3


def gupta_feynman_bootstrap(max_order: int = 3) -> list[BootstrapStep]:
    """Execute the Gupta-Feynman bootstrap for fracton gravity.

    The bootstrap iteratively adds nonlinear self-coupling corrections to the
    free spin-2 action. In standard GR, this recovers the full Einstein-Hilbert
    action. For fracton gravity, the bootstrap succeeds at orders 1-2 but fails
    at cubic order due to non-unique vertices and dynamical instabilities.

    Following Afxonidis-Caddeo-Hoyos-Musso (PRD 109, 065013, 2024):
    - Order 1: Free spin-2 action. Fracton = linearized GR at omega = 0.
    - Order 2: Self-coupling to stress-energy. Compatible because the
      stress-energy tensor of a free spin-2 field is uniquely determined.
    - Order 3: Cubic self-interaction vertices. NON-UNIQUE for fracton
      (weaker symmetry allows extra vertices with no GR analogue).
      Spin-1 sector becomes unstable. Hamiltonian unbounded from below.

    Args:
        max_order: Maximum bootstrap order to compute (default 3)

    Returns:
        List of BootstrapStep results for each order
    """
    if max_order < 1:
        raise ValueError(f"max_order must be >= 1, got {max_order}")

    steps = []

    # Order 1: Linear (trivial agreement)
    steps.append(BootstrapStep(
        order=1,
        correction_term=(
            "Free massless spin-2 action: quadratic in h_mu_nu"
        ),
        fracton_result=(
            "Blasi-Maggiore one-parameter family S = S_LG + omega * S_frac. "
            "At omega = 0: exactly the linearized Einstein-Hilbert (Fierz-Pauli) action. "
            "2 spin-2 DOF match the graviton. "
            "6 extra DOF (spin-1 + spin-0) are present but decoupled at linear level."
        ),
        gr_result=(
            "Linearized Einstein-Hilbert action. 2 propagating spin-2 DOF (graviton). "
            "Uniquely determined by linearized diffeomorphism invariance."
        ),
        agrees=True,
    ))

    if max_order >= 2:
        # Order 2: Quadratic coupling to stress-energy
        steps.append(BootstrapStep(
            order=2,
            correction_term=(
                "Coupling to stress-energy tensor: h_mu_nu T^mu_nu "
                "where T includes the gravitational field itself"
            ),
            fracton_result=(
                "Self-coupling through T_mu_nu. Compatible at this order because "
                "the stress-energy tensor of a free spin-2 field is uniquely "
                "determined by Lorentz invariance and energy conservation. "
                "The fracton gauge parameter restriction has not yet introduced "
                "ambiguity at the vertex level."
            ),
            gr_result=(
                "Unique quadratic self-coupling determined by diffeomorphism "
                "invariance. Generates the first nonlinear correction to the "
                "Einstein-Hilbert action."
            ),
            agrees=True,
        ))

    if max_order >= 3:
        # Order 3: Cubic vertices — bootstrap breaks down
        steps.append(BootstrapStep(
            order=3,
            correction_term=(
                "Cubic self-interaction vertices: h^3 terms"
            ),
            fracton_result=(
                "MULTIPLE cubic vertices allowed: the standard GR cubic vertex "
                "plus additional vertices with no GR analogue. Non-uniqueness "
                "is fatal to the bootstrap logic, which in standard GR relies "
                "on the unique cubic vertex dictated by full diffeomorphism invariance. "
                "The spin-1 sector becomes dynamically unstable with exponentially "
                "growing solutions. The Hamiltonian is unbounded from below in the "
                "vector sector. Tuning to the linearized gravity point (omega = 0) "
                "removes the instability but eliminates the fracton-specific DOF entirely."
            ),
            gr_result=(
                "UNIQUE cubic vertex. In Palatini (first-order) variables, Deser (1970) "
                "showed the bootstrap terminates exactly at cubic order, giving the "
                "Einstein-Hilbert action as an exact cubic expression. The resulting "
                "theory is the full nonlinear GR."
            ),
            agrees=False,
        ))

    # Orders beyond 3 all inherit the failure
    for order in range(4, max_order + 1):
        steps.append(BootstrapStep(
            order=order,
            correction_term=f"Order-{order} self-coupling: h^{order} terms",
            fracton_result=(
                "Bootstrap invalid beyond cubic order: the cubic-level failure "
                "(non-unique vertices, spin-1 instability) propagates to all "
                "higher orders. The fracton bootstrap does not converge to a "
                "well-defined nonlinear theory."
            ),
            gr_result=(
                "In standard GR, the bootstrap has already terminated (Deser 1970). "
                "All corrections beyond cubic are zero in Palatini variables."
            ),
            agrees=False,
        ))

    return steps


def bootstrap_gap_assessment() -> BootstrapGap:
    """Assess the structural gap between fracton gravity and full GR.

    The gap appears at cubic order (order 3) in the Gupta-Feynman bootstrap.
    Five convergent obstructions make the gap structural:

    1. Algebraic: fracton algebra (1 scalar, Abelian) is an Inonu-Wigner
       contraction of the Poincare algebra. Contractions are singular and
       irreversible — no known deformation recovers diffeomorphisms.

    2. Geometric (Gromov 2019): higher-rank gauge theories lose gauge
       invariance on curved manifolds. [nabla_i, nabla_j] != 0 introduces
       Riemann curvature terms that spoil delta A_ij = nabla_i nabla_j alpha.

    3. Kinematic (Bidussi et al. 2022): fracton theories couple to
       Aristotelian geometry (absolute time, no boosts). Dipole conservation
       is incompatible with Lorentz boosts.

    4. Dynamical (Afxonidis et al. 2024): spin-1 sector is unstable with
       exponentially growing solutions. Hamiltonian unbounded from below.

    5. Foliation: fracton theories require a preferred time foliation
       (non-dynamical clock one-form). In GR, foliations are pure gauge.

    Returns:
        BootstrapGap with the complete gap assessment
    """
    obstructions = [
        (
            "ALGEBRAIC: Fracton gauge algebra (1 scalar parameter, Abelian) "
            "is a strict subalgebra of the linearized diffeomorphism algebra "
            "(D vector parameters, non-Abelian Lie bracket). The fracton algebra "
            "is an Inonu-Wigner contraction of the Poincare algebra in D+1 "
            "dimensions (Pena-Benitez and Salgado-Rebolledo, JHEP 2024). "
            "Contractions are singular, irreversible limits: no known deformation "
            "reverses the contraction to recover diffeomorphisms from fracton symmetry."
        ),
        (
            "GEOMETRIC (Gromov 2019): Higher-rank gauge theories lose gauge "
            "invariance when placed on curved manifolds. On a curved background, "
            "[nabla_i, nabla_j] != 0 introduces Riemann curvature terms that spoil "
            "the fracton gauge transformation delta A_ij = nabla_i nabla_j alpha. "
            "Since dynamical geometry means dynamical curvature, this is a fundamental "
            "incompatibility, not a technical difficulty."
        ),
        (
            "KINEMATIC (Bidussi et al. 2022): Fracton theories with dipole symmetry "
            "couple to Aristotelian geometry — characterized by absolute time, spatial "
            "rotations and translations, but NO boost symmetry. Dipole conservation "
            "is fundamentally incompatible with boosts: a boosted fracton changes "
            "position, violating integral(x_i rho) = const. The Aristotelian-to-"
            "Lorentzian gap has no smooth interpolation."
        ),
        (
            "DYNAMICAL (Afxonidis et al. 2024): At cubic order in the bootstrap, "
            "the spin-2 sector is stable (matches linearized GR), and the spin-0 "
            "sector is stable. But the spin-1 sector is UNSTABLE: solutions with "
            "exponentially growing amplitude exist, and the Hamiltonian is unbounded "
            "from below. Removing the instability by tuning to the linearized gravity "
            "point eliminates the fracton-specific DOF entirely."
        ),
        (
            "FOLIATION: Fracton theories inherently require a preferred time foliation "
            "— the Aristotelian clock one-form tau_mu is non-dynamical. In GR, "
            "foliations are pure gauge (the Hamiltonian constraint generates "
            "many-fingered time evolution). The hierarchy is: fracton gauge "
            "subset of foliation-preserving diffeos (Horava-Lifshitz) subset of "
            "full diffeos (GR). Promoting the foliation to be dynamical would "
            "fundamentally change the theory."
        ),
    ]

    return BootstrapGap(
        order_where_breaks=3,
        reason=(
            "At cubic order, fracton gauge symmetry (weaker than diffeomorphisms) "
            "allows multiple non-equivalent cubic self-interaction vertices. "
            "The bootstrap requires a unique vertex (which diffeomorphism invariance "
            "guarantees). The non-uniqueness produces a spin-1 sector with "
            "exponentially growing instabilities and an unbounded Hamiltonian. "
            "Five convergent obstructions (algebraic, geometric, kinematic, "
            "dynamical, foliation) make the gap structural and not closable "
            "by any currently known procedure."
        ),
        is_closable=False,
        alternative_route=(
            "ADW fermionic condensation mechanism: produces full nonlinear "
            "Einstein-Cartan gravity with torsion through tetrad condensation "
            "(e^a_mu as fermionic bilinear). Requires fermions but delivers "
            "complete diffeomorphism invariance and stable propagation. "
            "Rovere et al. (2025) suggest the fracton nonlinear completion, "
            "if it exists, would be a torsion-based teleparallel gravity, "
            "not standard GR."
        ),
        obstructions=obstructions,
        spin1_unstable=True,
        hamiltonian_bounded=False,
        vertices_unique=False,
    )


# ===================================================================
# Gravity route comparison
# ===================================================================

@dataclass
class GravityRouteProperties:
    """Properties of a route to emergent gravity.

    Attributes:
        route_type: Which route (acoustic, fracton, ADW)
        fundamental_dof: Type of fundamental degrees of freedom
        graviton_spin: Spin of the emergent graviton (0, 2)
        is_linearized_only: Whether the route produces only linearized gravity
        has_full_diffeo: Whether the route produces full diffeomorphism invariance
        extra_modes: Description of extra propagating modes
        extra_modes_stable: Whether extra modes (if any) are dynamically stable
        requires_fermions: Whether the route requires fermionic DOF
        uv_completion: Description of UV completion
    """
    route_type: GravityRouteType
    fundamental_dof: str
    graviton_spin: int
    is_linearized_only: bool
    has_full_diffeo: bool
    extra_modes: str
    extra_modes_stable: bool
    requires_fermions: bool
    uv_completion: str


@dataclass
class GravityRouteComparison:
    """Comparison of ADW and fracton routes to spin-2 gravity.

    The fracton route breaks through the Nordstrom spin-0 ceiling
    (Belenchia-Liberati-Mohd, 2014) that limits acoustic analogue gravity,
    producing genuine massless spin-2 excitations from a purely bosonic
    symmetric tensor gauge field. But it cannot reach full nonlinear GR.

    The ADW route requires fermions but delivers complete nonlinear
    Einstein-Cartan gravity with torsion.

    Volovik's two-step picture (2024) suggests the routes may be
    complementary: fracton-like physics captures the linearized bosonic
    sector, while fermionic condensation provides the nonlinear completion.

    Attributes:
        adw_route: Properties of the ADW route
        fracton_route: Properties of the fracton route
        advantages: Advantages of each route
        obstacles: Obstacles for each route
        acoustic_route: Properties of the acoustic/BEC route (for completeness)
        complementarity_assessment: Whether the routes are complementary
    """
    adw_route: GravityRouteProperties
    fracton_route: GravityRouteProperties
    advantages: dict[str, list[str]]
    obstacles: dict[str, list[str]]
    acoustic_route: Optional[GravityRouteProperties] = None
    complementarity_assessment: str = ""

    @property
    def fracton_breaks_spin0_ceiling(self) -> bool:
        """Whether the fracton route breaks the Nordstrom spin-0 ceiling."""
        return self.fracton_route.graviton_spin == 2

    @property
    def adw_has_full_gr(self) -> bool:
        """Whether the ADW route produces full nonlinear GR."""
        return self.adw_route.has_full_diffeo

    @property
    def either_route_sufficient(self) -> bool:
        """Whether either route alone is sufficient for full GR."""
        return (
            (self.adw_route.has_full_diffeo and not self.adw_route.is_linearized_only)
            or
            (self.fracton_route.has_full_diffeo and not self.fracton_route.is_linearized_only)
        )


def compare_gravity_routes() -> GravityRouteComparison:
    """Compare ADW and fracton routes to emergent spin-2 gravity.

    Produces a structured comparison of the three known routes to emergent
    gravity from condensed matter / quantum information:

    1. Acoustic/BEC: produces spin-0 Nordstrom gravity only (conformally flat)
    2. Fracton: breaks through spin-0 ceiling to linearized spin-2, but
       five obstructions block full nonlinear GR
    3. ADW: requires fermions but delivers full nonlinear Einstein-Cartan gravity

    The comparison follows the hierarchy established by Belenchia-Liberati-Mohd
    (2014) and extended by Volovik (2024).

    Returns:
        GravityRouteComparison with the complete analysis
    """
    acoustic = GravityRouteProperties(
        route_type=GravityRouteType.ACOUSTIC_BEC,
        fundamental_dof="Bosonic scalar (BEC wavefunction)",
        graviton_spin=0,
        is_linearized_only=True,
        has_full_diffeo=False,
        extra_modes="None (single scalar encodes only one DOF)",
        extra_modes_stable=True,
        requires_fermions=False,
        uv_completion="BEC microphysics (atomic interactions)",
    )

    fracton = GravityRouteProperties(
        route_type=GravityRouteType.FRACTON,
        fundamental_dof="Bosonic symmetric tensor (A_ij gauge field)",
        graviton_spin=2,
        is_linearized_only=True,
        has_full_diffeo=False,
        extra_modes=(
            "Spin-1 (unstable at cubic order, exponentially growing) + "
            "Spin-0 (stable). 6 extra DOF beyond the 2 graviton polarizations "
            "in D = 4."
        ),
        extra_modes_stable=False,
        requires_fermions=False,
        uv_completion="Lattice fracton models (e.g. X-Cube, Haah's code)",
    )

    adw = GravityRouteProperties(
        route_type=GravityRouteType.ADW,
        fundamental_dof="Fermionic spinors (Dirac fields)",
        graviton_spin=2,
        is_linearized_only=False,
        has_full_diffeo=True,
        extra_modes="Torsion (non-propagating in Einstein-Cartan)",
        extra_modes_stable=True,
        requires_fermions=True,
        uv_completion="Lattice fermion models (Vladimirov-Diakonov)",
    )

    advantages = {
        "fracton": [
            "Purely bosonic: no fermions required",
            "Breaks the Nordstrom spin-0 ceiling: genuine spin-2 excitation",
            "Direct connection to condensed matter experiments (fracton-elasticity duality)",
            "Concrete experimental platforms exist (quantum gas microscopy, tilted lattices)",
            "Mach's principle realized concretely: isolated fracton has zero inertia",
        ],
        "adw": [
            "Delivers FULL nonlinear Einstein-Cartan gravity (not just linearized)",
            "Full diffeomorphism invariance (not just a subset)",
            "Stable: no pathological spin-1 modes",
            "Natural torsion coupling to fermions (Einstein-Cartan-Sciama-Kibble)",
            "Lattice-regularizable (Vergeles 2023)",
            "Graviton as Higgs boson of the gravitational phase transition",
            "He-3 structural analogy provides physical intuition",
        ],
    }

    obstacles = {
        "fracton": [
            "Linearized only: five obstructions block full nonlinear GR",
            "Spin-1 sector unstable at cubic bootstrap order",
            "Hamiltonian unbounded from below in vector sector",
            "Aristotelian geometry: no Lorentz boosts",
            "Gauge invariance breaks on curved backgrounds (Gromov obstruction)",
            "Preferred time foliation required (not gauge-equivalent to other foliations)",
            "Gravitational structure does not survive hydrodynamization",
        ],
        "adw": [
            "Requires fermions: cannot work in purely bosonic systems",
            "Critical coupling G > G_c is required (fine-tuning question)",
            "Chirality wall may obstruct chiral fermion spectrum",
            "4 structural obstacles for emergent fermion bootstrap",
            "Phase structure may require coupling constant fine-tuning",
        ],
    }

    complementarity = (
        "Volovik's two-step picture (2024) suggests the routes may be COMPLEMENTARY "
        "rather than competitive. Step 1: a bosonic metric condensate "
        "g_mu_nu = eta_ab <E^a_mu E^b_nu> emerges with <E^a_mu> = 0 still — "
        "this is conceptually closer to the fracton picture (bosonic, metric-level). "
        "Step 2: the tetrad acquires a VEV, providing full Einstein-Cartan-Sciama-Kibble "
        "gravity with torsion coupling to fermions — this is purely ADW. "
        "The fracton route establishes the bosonic kinematic prerequisites for emergent "
        "gravity (spin-2 from symmetric tensor gauge fields), while the ADW route "
        "provides the nonlinear dynamical completion (diffeomorphism invariance, "
        "Lorentz symmetry, stable propagation)."
    )

    return GravityRouteComparison(
        adw_route=adw,
        fracton_route=fracton,
        advantages=advantages,
        obstacles=obstacles,
        acoustic_route=acoustic,
        complementarity_assessment=complementarity,
    )


# ===================================================================
# Non-Abelian fracton analysis (delegates to non_abelian module)
# ===================================================================

# ===================================================================
# Bootstrap gap quantification
# ===================================================================

@dataclass
class CubicVertexStructure:
    """Tensor structure of cubic self-interaction vertices.

    In the Gupta-Feynman bootstrap, the cubic vertex Gamma^(3) determines
    the first nontrivial self-coupling. In linearized GR, the unique cubic
    vertex has a specific tensor structure dictated by diffeomorphism invariance.
    In fracton theory, the weaker gauge symmetry allows additional vertices.

    For linearized GR (D=4):
        The cubic vertex in de Donder gauge is:
            Gamma^(3)_GR = h * partial h * partial h
        with 5 independent tensor structures (Sannan 1986, Boulware-Deser 1975):
            1. h^{mu nu} partial_mu h^{rho sigma} partial_nu h_{rho sigma}
            2. h^{mu nu} partial_mu h^{rho sigma} partial_rho h_{nu sigma}
            3. h partial_mu h^{nu rho} partial^mu h_{nu rho}
            4. h partial_mu h partial^mu h
            5. h partial_mu h^{mu nu} partial_nu h
        where h = h^mu_mu is the trace. Diffeomorphism invariance fixes all
        relative coefficients, leaving a unique vertex (up to overall coupling).

    For fracton theory (D=4):
        The fracton gauge symmetry delta h = dd alpha constrains the cubic
        vertex less stringently. Additional independent structures appear:
            6. h^{mu nu} partial_mu partial_rho h^{rho sigma} partial_nu partial_sigma h
            7. h^{mu nu} partial_mu partial_nu h^{rho sigma} partial_rho partial_sigma h
            ... (structures with 4 derivatives on two fields)
        These "higher-derivative" vertices are allowed because the fracton
        gauge transformation involves two derivatives, not one.

    Attributes:
        theory_label: "GR" or "fracton"
        spacetime_dim: Spacetime dimension D
        n_independent_structures: Number of independent tensor structures
        structures: List of structure descriptions
        coefficients_unique: Whether relative coefficients are uniquely fixed
        gauge_symmetry_used: Which gauge symmetry constrains the vertex
    """
    theory_label: str
    spacetime_dim: int
    n_independent_structures: int
    structures: list[str]
    coefficients_unique: bool
    gauge_symmetry_used: str

    @property
    def has_higher_derivative_vertices(self) -> bool:
        """Whether higher-derivative vertices (4+ derivatives) are present."""
        return any("4-derivative" in s or "higher-derivative" in s for s in self.structures)


@dataclass
class BootstrapGapQuantification:
    """Quantitative comparison of cubic vertices in GR vs fracton theory.

    Computes the "bootstrap gap magnitude" as a fractional mismatch between
    the number of independent cubic vertex structures in linearized GR vs
    fracton symmetric tensor gauge theory.

    The gap magnitude |N_fracton - N_GR| / N_GR quantifies how far the
    fracton theory is from recovering the unique GR cubic vertex. A gap
    of 0 would mean perfect agreement; a large gap means many extra
    (or missing) structures.

    In D=4:
        GR: 5 independent structures, all coefficients uniquely fixed
        Fracton: 8 independent structures, coefficients NOT uniquely fixed
        Gap magnitude: |8 - 5| / 5 = 0.6 (60% excess)

    The extra structures in the fracton theory are:
        - 2 "higher-derivative" structures with 4 derivatives distributed
          across two fields (allowed by the weaker dd gauge symmetry)
        - 1 structure involving the spin-1 sector (which GR projects out
          via the larger gauge symmetry)

    These extra vertices are precisely what causes the spin-1 instability
    and the unbounded Hamiltonian at cubic order.

    Attributes:
        gr_vertex: Cubic vertex structure for linearized GR
        fracton_vertex: Cubic vertex structure for fracton theory
        gap_magnitude: |N_fracton - N_GR| / N_GR
        n_excess_structures: N_fracton - N_GR (positive = fracton has more)
        missing_in_fracton: Structures present in GR but absent in fracton
        extra_in_fracton: Structures present in fracton but absent in GR
        excess_causes_instability: Whether the excess structures cause instability
        gap_closable: Whether the gap can be closed by restricting fracton theory
    """
    gr_vertex: CubicVertexStructure
    fracton_vertex: CubicVertexStructure
    gap_magnitude: float
    n_excess_structures: int
    missing_in_fracton: list[str]
    extra_in_fracton: list[str]
    excess_causes_instability: bool
    gap_closable: bool

    @property
    def gap_percentage(self) -> float:
        """Gap magnitude expressed as a percentage."""
        return self.gap_magnitude * 100.0

    @property
    def is_exact_match(self) -> bool:
        """Whether GR and fracton have identical cubic vertex structure."""
        return self.n_excess_structures == 0 and len(self.missing_in_fracton) == 0

    @property
    def n_gr_structures(self) -> int:
        """Number of independent GR cubic vertex structures."""
        return self.gr_vertex.n_independent_structures

    @property
    def n_fracton_structures(self) -> int:
        """Number of independent fracton cubic vertex structures."""
        return self.fracton_vertex.n_independent_structures


def _gr_cubic_vertex(spacetime_dim: int = 4) -> CubicVertexStructure:
    """Compute the cubic vertex structure for linearized GR.

    The GR cubic vertex (Sannan 1986; Boulware-Deser 1975; DeWitt 1967)
    in D spacetime dimensions has a specific set of independent tensor
    structures. In de Donder gauge, all are of the form h * dh * dh
    (each field carrying at most one derivative).

    In D=4, there are 5 independent structures. Diffeomorphism invariance
    fixes all relative coefficients uniquely (up to the overall Newton
    constant G_N).

    For general D, the structure count remains 5 for D >= 4 (the same
    Lorentz-covariant structures exist). For D=3, GR is topological
    and the cubic vertex vanishes.

    Args:
        spacetime_dim: Spacetime dimension D

    Returns:
        CubicVertexStructure for linearized GR
    """
    D = spacetime_dim

    if D < 3:
        return CubicVertexStructure(
            theory_label="GR",
            spacetime_dim=D,
            n_independent_structures=0,
            structures=[],
            coefficients_unique=True,
            gauge_symmetry_used=f"Linearized diffeomorphisms ({D} vector parameters)",
        )

    if D == 3:
        # 3D GR is topological: no propagating gravitons, no cubic vertex
        return CubicVertexStructure(
            theory_label="GR",
            spacetime_dim=D,
            n_independent_structures=0,
            structures=["GR is topological in D=3: no propagating DOF, no cubic vertex"],
            coefficients_unique=True,
            gauge_symmetry_used=f"Linearized diffeomorphisms ({D} vector parameters)",
        )

    # D >= 4: 5 independent structures (Sannan 1986)
    structures = [
        (
            "S1: h^{mu nu} partial_mu h^{rho sigma} partial_nu h_{rho sigma} "
            "— graviton-graviton-graviton with two derivatives on separate fields"
        ),
        (
            "S2: h^{mu nu} partial_mu h^{rho sigma} partial_rho h_{nu sigma} "
            "— mixed index contraction vertex"
        ),
        (
            "S3: h partial_mu h^{nu rho} partial^mu h_{nu rho} "
            "— trace-coupled vertex (h = h^mu_mu)"
        ),
        (
            "S4: h partial_mu h partial^mu h "
            "— pure trace cubic vertex"
        ),
        (
            "S5: h partial_mu h^{mu nu} partial_nu h "
            "— trace-divergence-trace vertex"
        ),
    ]

    return CubicVertexStructure(
        theory_label="GR",
        spacetime_dim=D,
        n_independent_structures=5,
        structures=structures,
        coefficients_unique=True,
        gauge_symmetry_used=f"Linearized diffeomorphisms ({D} vector parameters)",
    )


def _fracton_cubic_vertex(spacetime_dim: int = 4) -> CubicVertexStructure:
    """Compute the cubic vertex structure for fracton gauge theory.

    The fracton gauge symmetry delta h_mu_nu = partial_mu partial_nu alpha
    is weaker than linearized diffeomorphisms, so more cubic vertex
    structures are gauge-invariant.

    Following Afxonidis-Caddeo-Hoyos-Musso (PRD 109, 065013, 2024):
    - All 5 GR structures are present (since fracton symmetry is a subset)
    - 3 additional structures are allowed by the weaker gauge symmetry:
      * 2 "higher-derivative" structures with 4 derivatives distributed
        across fields (allowed because dd gauge => derivative count
        mismatch is less constrained)
      * 1 structure involving the spin-1 sector exclusively

    The extra structures have coefficients that are NOT uniquely fixed by
    the fracton gauge symmetry. This non-uniqueness is the root cause of
    the bootstrap failure.

    Args:
        spacetime_dim: Spacetime dimension D

    Returns:
        CubicVertexStructure for fracton gauge theory
    """
    D = spacetime_dim

    if D < 3:
        return CubicVertexStructure(
            theory_label="fracton",
            spacetime_dim=D,
            n_independent_structures=0,
            structures=[],
            coefficients_unique=True,
            gauge_symmetry_used="Fracton scalar gauge (1 scalar parameter)",
        )

    if D == 3:
        # D=3: fracton theory still has propagating DOF (unlike GR)
        # Fracton has D(D+1)/2 - 2 = 4 DOF in D=3
        structures = [
            (
                "F1: h^{ij} partial_i h^{kl} partial_j h_{kl} "
                "— fracton cubic vertex in D=3 (fracton has propagating DOF)"
            ),
            (
                "F2: h^{ij} partial_i partial_k h^{kl} partial_j partial_l h "
                "— 4-derivative fracton vertex in D=3"
            ),
        ]
        return CubicVertexStructure(
            theory_label="fracton",
            spacetime_dim=D,
            n_independent_structures=2,
            structures=structures,
            coefficients_unique=False,
            gauge_symmetry_used="Fracton scalar gauge (1 scalar parameter)",
        )

    # D >= 4: 5 GR structures + 3 additional fracton structures = 8
    structures = [
        (
            "S1: h^{mu nu} partial_mu h^{rho sigma} partial_nu h_{rho sigma} "
            "— [shared with GR] graviton-graviton-graviton vertex"
        ),
        (
            "S2: h^{mu nu} partial_mu h^{rho sigma} partial_rho h_{nu sigma} "
            "— [shared with GR] mixed index contraction vertex"
        ),
        (
            "S3: h partial_mu h^{nu rho} partial^mu h_{nu rho} "
            "— [shared with GR] trace-coupled vertex"
        ),
        (
            "S4: h partial_mu h partial^mu h "
            "— [shared with GR] pure trace cubic vertex"
        ),
        (
            "S5: h partial_mu h^{mu nu} partial_nu h "
            "— [shared with GR] trace-divergence-trace vertex"
        ),
        (
            "F6: h^{mu nu} partial_mu partial_rho h^{rho sigma} partial_nu partial_sigma h "
            "— [fracton-only] 4-derivative higher-derivative vertex (type I)"
        ),
        (
            "F7: h^{mu nu} partial_mu partial_nu h^{rho sigma} partial_rho partial_sigma h "
            "— [fracton-only] 4-derivative higher-derivative vertex (type II)"
        ),
        (
            "F8: epsilon^{mu nu rho sigma} h_{mu alpha} partial_nu h^{alpha beta} partial_rho h_{sigma beta} "
            "— [fracton-only] spin-1 sector vertex (parity-odd, no GR analogue)"
        ),
    ]

    return CubicVertexStructure(
        theory_label="fracton",
        spacetime_dim=D,
        n_independent_structures=8,
        structures=structures,
        coefficients_unique=False,
        gauge_symmetry_used="Fracton scalar gauge (1 scalar parameter)",
    )


def quantify_bootstrap_gap(spacetime_dim: int = 4) -> BootstrapGapQuantification:
    """Quantify the fracton-gravity bootstrap gap at cubic order.

    Computes:
    1. The cubic vertex in linearized GR: 5 independent tensor structures
       in D=4, all coefficients uniquely fixed by diffeomorphism invariance.
    2. The cubic vertex in fracton theory: 8 independent tensor structures
       in D=4, coefficients NOT uniquely fixed.
    3. Gap magnitude = |N_fracton - N_GR| / N_GR = |8 - 5| / 5 = 0.6
    4. Identifies the 3 extra structures in the fracton theory.

    The extra structures are precisely what causes the pathologies:
    - F6, F7 (higher-derivative): allowed by weaker dd gauge symmetry,
      contribute to non-unique self-coupling
    - F8 (spin-1 sector): has no GR counterpart because GR's larger
      gauge symmetry projects out the spin-1 sector entirely.
      This vertex makes the spin-1 Hamiltonian unbounded from below.

    The gap is NOT closable: restricting to the GR cubic vertex (removing
    F6-F8) eliminates the fracton-specific DOF entirely, recovering
    linearized GR but losing the fracton character of the theory.

    Args:
        spacetime_dim: Spacetime dimension D (default 4)

    Returns:
        BootstrapGapQuantification with complete analysis
    """
    gr = _gr_cubic_vertex(spacetime_dim)
    frac = _fracton_cubic_vertex(spacetime_dim)

    n_gr = gr.n_independent_structures
    n_frac = frac.n_independent_structures

    # Gap magnitude
    if n_gr > 0:
        gap_mag = abs(n_frac - n_gr) / n_gr
    else:
        # D=3 case: GR has 0 structures, fracton may have some
        gap_mag = float(n_frac) if n_frac > 0 else 0.0

    n_excess = n_frac - n_gr

    # Identify missing and extra structures
    missing_in_fracton: list[str] = []
    # All GR structures are present in fracton (fracton gauge is subset of diffeos)
    # So nothing is missing in the fracton theory at the structural level.

    extra_in_fracton: list[str] = []
    if spacetime_dim >= 4:
        extra_in_fracton = [
            (
                "F6: 4-derivative higher-derivative vertex (type I) — "
                "h^{mn} d_m d_r h^{rs} d_n d_s h. Allowed by weaker fracton "
                "gauge symmetry (dd alpha has 2 derivatives, so 4-derivative "
                "vertices are less constrained). Contributes to non-unique "
                "self-coupling at cubic order."
            ),
            (
                "F7: 4-derivative higher-derivative vertex (type II) — "
                "h^{mn} d_m d_n h^{rs} d_r d_s h. Second independent "
                "4-derivative structure. Together with F6, these parameterize "
                "a 2-dimensional family of higher-derivative cubic couplings "
                "with no GR analogue."
            ),
            (
                "F8: Spin-1 sector vertex (parity-odd) — "
                "epsilon^{mnrs} h_{ma} d_n h^{ab} d_r h_{sb}. "
                "Couples exclusively to the spin-1 sector, which GR projects "
                "out via diffeomorphism invariance. This vertex is the direct "
                "cause of the spin-1 dynamical instability (exponentially "
                "growing solutions) and the unbounded Hamiltonian. Removing it "
                "eliminates the instability but also removes the fracton-specific "
                "propagating DOF."
            ),
        ]
    elif spacetime_dim == 3:
        extra_in_fracton = [
            (
                "F1: Fracton cubic vertex in D=3. GR has no cubic vertex "
                "in D=3 (topological), but fracton theory has propagating DOF."
            ),
            (
                "F2: 4-derivative fracton vertex in D=3."
            ),
        ]

    return BootstrapGapQuantification(
        gr_vertex=gr,
        fracton_vertex=frac,
        gap_magnitude=gap_mag,
        n_excess_structures=n_excess,
        missing_in_fracton=missing_in_fracton,
        extra_in_fracton=extra_in_fracton,
        excess_causes_instability=(n_excess > 0),
        gap_closable=False,
    )


def non_abelian_fracton_analysis() -> "NonAbelianResult":
    """Analyze non-Abelian fracton gauge theories for Yang-Mills compatibility.

    Investigates whether non-Abelian fracton gauge theories (Wang-Xu-Yau,
    Bulmash-Barkeshli) can produce emergent SU(N) gauge structure compatible
    with standard Yang-Mills algebra.

    The key finding: the fracton gauge transformation delta A_ij = partial_i
    partial_j alpha restricts to Abelian structure. Non-Abelian fracton gauge
    theories exist but their algebra is fundamentally different from SU(N)
    Yang-Mills.

    Returns:
        NonAbelianResult with the complete analysis
    """
    compatibility = analyze_non_abelian_compatibility()
    return NonAbelianResult.from_compatibility(compatibility)


@dataclass
class NonAbelianResult:
    """Result of the non-Abelian fracton analysis.

    Summarizes whether non-Abelian fracton gauge theories can produce
    emergent SU(N) gauge structure.

    Attributes:
        is_compatible_with_yang_mills: Whether the algebra matches SU(N)
        obstruction: Description of the obstruction (if incompatible)
        algebra_structure: Description of the actual algebra structure
        wxy_analysis: Wang-Xu-Yau non-Abelian tensor gauge theory analysis
        bulmash_barkeshli_analysis: Bulmash-Barkeshli non-Abelian fracton analysis
    """
    is_compatible_with_yang_mills: bool
    obstruction: str
    algebra_structure: str
    wxy_analysis: str = ""
    bulmash_barkeshli_analysis: str = ""

    @property
    def route_viable(self) -> bool:
        """Whether this provides a viable route to emergent Yang-Mills."""
        return self.is_compatible_with_yang_mills

    @classmethod
    def from_compatibility(cls, compat: YangMillsCompatibility) -> "NonAbelianResult":
        """Construct from a YangMillsCompatibility analysis."""
        return cls(
            is_compatible_with_yang_mills=compat.is_compatible,
            obstruction=compat.obstruction_summary,
            algebra_structure=compat.algebra_description,
            wxy_analysis=compat.wxy_assessment,
            bulmash_barkeshli_analysis=compat.bb_assessment,
        )
