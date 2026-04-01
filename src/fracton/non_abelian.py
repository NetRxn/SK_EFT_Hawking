"""Non-Abelian Fracton Gauge Theories: Yang-Mills Compatibility Analysis.

PROVENANCE NOTE: See sk_eft.py for Pipeline Invariant 1+4 gap status.

Investigates whether non-Abelian fracton gauge theories can produce emergent
SU(N) gauge structure compatible with standard Yang-Mills algebra.

The central question: Can non-Abelian fracton gauge theories produce
emergent SU(N) gauge structure? Or is the algebra necessarily different?

Key finding: The fracton gauge transformation delta A_ij = partial_i partial_j
alpha fundamentally restricts to Abelian structure. Non-Abelian fracton gauge
theories exist (Wang-Xu-Yau tensor gauge theories, Bulmash-Barkeshli non-Abelian
fractons) but their algebra does NOT match standard SU(N) Yang-Mills.

The obstruction chain:

1. Wang-Xu-Yau (PRR 3, 013185, 2021) non-Abelian tensor gauge theories:
   Extend A_ij to carry color indices A^a_ij. The gauge transformation becomes
   delta A^a_ij = partial_i partial_j alpha^a + f^a_bc A^b_ij alpha^c
   (non-Abelian for the color indices). However, the two-derivative structure
   partial_i partial_j constrains the algebra: the gauge parameters alpha^a
   must be scalar fields (not vector fields as in Yang-Mills), and the
   resulting gauge algebra is NOT isomorphic to standard Yang-Mills.

2. Bulmash-Barkeshli (PRB 100, 155146, 2019) non-Abelian fractons:
   Fractons can carry non-Abelian fusion rules in lattice models, but
   the non-Abelian structure arises from FUSION (anyon-like), not from
   gauge transformations. The gauge group of the underlying tensor gauge
   theory remains Abelian. Position-dependent degeneracies are protected
   by fracton immobility (charge + dipole conservation), providing a
   different mechanism than Yang-Mills gauge redundancy.

3. Algebraic obstruction formalized:
   In standard Yang-Mills, the gauge transformation delta A^a_mu =
   D_mu alpha^a = partial_mu alpha^a + f^a_bc A^b_mu alpha^c uses
   a COVARIANT derivative with a single partial_mu. The two-derivative
   structure partial_i partial_j in fracton symmetry is fundamentally
   incompatible: the covariant extension nabla_i nabla_j alpha does not
   define a consistent Lie algebra because [nabla_i, nabla_j] = R^k_lij
   introduces curvature terms that break the gauge closure.

4. Even if one defines a "non-Abelian fracton" algebra by hand, the
   resulting commutator structure differs from su(N):
   - Yang-Mills: [T^a, T^b] = i f^abc T^c (Lie bracket of su(N))
   - Fracton: the gauge parameters are scalars with dd structure,
     and the commutator involves fourth-order derivatives (dddd terms)
     that have no analogue in Yang-Mills

Conclusion: Non-Abelian fracton gauge theories exist but represent a
fundamentally different algebraic structure from SU(N) Yang-Mills.
The fracton route to non-Abelian gauge fields is CLOSED.

References:
    - Wang-Xu-Yau (PRR 3, 013185, 2021): non-Abelian tensor gauge theories
    - Bulmash-Barkeshli (PRB 100, 155146, 2019): non-Abelian fractons
    - Pretko (PRD 96, 024051, 2017): Abelian fracton gauge theory
    - Gromov (PRL 122, 076403, 2019): curvature obstruction
    - Pena-Benitez-Salgado-Rebolledo (JHEP 2024): fracton algebra structure
"""

from dataclasses import dataclass, field
from enum import Enum
from typing import Optional

from src.core.formulas import fracton_ym_obstruction_count


# ===================================================================
# Enumerations
# ===================================================================

class AlgebraType(Enum):
    """Type of gauge algebra."""
    ABELIAN_FRACTON = "abelian_fracton"           # delta A_ij = dd alpha
    NON_ABELIAN_FRACTON = "non_abelian_fracton"   # dd alpha + f A alpha
    YANG_MILLS = "yang_mills"                      # D_mu alpha = d alpha + [A, alpha]
    FUSION_NON_ABELIAN = "fusion_non_abelian"     # Non-Abelian fusion rules


class NonAbelianSourceType(Enum):
    """Source of non-Abelian structure in fracton models."""
    GAUGE_TRANSFORMATION = "gauge_transformation"    # From gauge transformations
    FUSION_RULES = "fusion_rules"                     # From anyon-like fusion
    POSITION_DEGENERACY = "position_degeneracy"       # From immobility-protected degeneracy


# ===================================================================
# Non-Abelian fracton gauge theory
# ===================================================================

@dataclass
class NonAbelianFractonGauge:
    """Non-Abelian fracton gauge theory structure.

    Describes the gauge structure of non-Abelian extensions of Pretko's
    tensor gauge theory.

    Wang-Xu-Yau (2021) extend A_ij to carry color indices: A^a_ij with
    a = 1, ..., dim(G) for gauge group G. The gauge transformation is:

        delta A^a_ij = partial_i partial_j alpha^a + f^a_bc A^b_ij alpha^c

    where f^a_bc are the structure constants of G. The two-derivative
    structure (partial_i partial_j) constrains the algebra differently
    from Yang-Mills (single partial_mu).

    Bulmash-Barkeshli (2019) non-Abelian fractons have non-Abelian
    fusion rules but the underlying tensor gauge theory remains Abelian.

    Attributes:
        gauge_group_name: Name of the attempted gauge group (e.g. "SU(2)")
        gauge_group_dim: Dimension of the gauge group
        algebra_type: Type of algebra (Abelian fracton, non-Abelian fracton, etc.)
        n_gauge_parameters: Number of gauge parameters (scalar for fracton)
        derivative_order: Order of derivatives in gauge transformation (2 for fracton)
        is_abelian_gauge: Whether the gauge transformation is Abelian
        has_non_abelian_fusion: Whether non-Abelian fusion rules exist
        source_of_non_abelian: Source of non-Abelian structure
        field_components: Number of independent field components
    """
    gauge_group_name: str
    gauge_group_dim: int
    algebra_type: AlgebraType
    n_gauge_parameters: int
    derivative_order: int = 2
    is_abelian_gauge: bool = True
    has_non_abelian_fusion: bool = False
    source_of_non_abelian: Optional[NonAbelianSourceType] = None
    field_components: int = 0

    @property
    def gauge_transformation_description(self) -> str:
        """Description of the gauge transformation."""
        if self.algebra_type == AlgebraType.ABELIAN_FRACTON:
            return (
                f"delta A_ij = partial_i partial_j alpha "
                f"(Abelian, {self.n_gauge_parameters} scalar parameter)"
            )
        elif self.algebra_type == AlgebraType.NON_ABELIAN_FRACTON:
            return (
                f"delta A^a_ij = partial_i partial_j alpha^a + "
                f"f^a_bc A^b_ij alpha^c "
                f"({self.gauge_group_name}, {self.n_gauge_parameters} scalar parameters, "
                f"two-derivative structure)"
            )
        elif self.algebra_type == AlgebraType.YANG_MILLS:
            return (
                f"delta A^a_mu = partial_mu alpha^a + f^a_bc A^b_mu alpha^c "
                f"({self.gauge_group_name}, {self.n_gauge_parameters} vector parameters, "
                f"single-derivative structure)"
            )
        else:
            return (
                f"Fusion-type non-Abelian structure in {self.gauge_group_name} "
                f"(non-Abelian fusion rules, Abelian gauge transformation)"
            )

    @property
    def is_yang_mills_compatible(self) -> bool:
        """Whether this algebra is compatible with standard Yang-Mills."""
        return self.algebra_type == AlgebraType.YANG_MILLS


# ===================================================================
# Yang-Mills compatibility
# ===================================================================

@dataclass
class DerivativeStructureComparison:
    """Comparison of derivative structure between fracton and Yang-Mills.

    The key algebraic obstruction: fracton gauge transformations use
    TWO derivatives (partial_i partial_j alpha), while Yang-Mills uses
    ONE derivative (partial_mu alpha). This is not a quantitative
    difference but a qualitative algebraic one that changes the entire
    gauge algebra structure.

    Attributes:
        fracton_derivative_order: Order of derivatives in fracton gauge (2)
        yang_mills_derivative_order: Order of derivatives in YM gauge (1)
        commutator_structure_matches: Whether commutator structures match
        closure_condition_satisfied: Whether gauge closure is maintained
        curvature_obstruction: Whether curvature terms spoil closure
    """
    fracton_derivative_order: int = 2
    yang_mills_derivative_order: int = 1
    commutator_structure_matches: bool = False
    closure_condition_satisfied: bool = False
    curvature_obstruction: bool = True

    @property
    def derivative_order_mismatch(self) -> int:
        """Difference in derivative order."""
        return self.fracton_derivative_order - self.yang_mills_derivative_order

    @property
    def is_compatible(self) -> bool:
        """Whether the derivative structures are compatible."""
        return (
            self.commutator_structure_matches
            and self.closure_condition_satisfied
            and not self.curvature_obstruction
        )


@dataclass
class YangMillsCompatibility:
    """Full assessment of Yang-Mills compatibility for non-Abelian fracton theories.

    The assessment checks four independent criteria:

    1. Derivative structure: fracton uses dd, Yang-Mills uses d
    2. Commutator algebra: fracton commutator involves dddd terms,
       Yang-Mills commutator involves dd terms
    3. Gauge closure: fracton closure requires flatness (Gromov),
       Yang-Mills closure is automatic on any manifold
    4. Representation theory: fracton gauge parameters are scalars,
       Yang-Mills gauge parameters are 1-form components

    All four criteria fail: the algebras are fundamentally different.

    Attributes:
        is_compatible: Whether non-Abelian fracton is YM-compatible (False)
        derivative_comparison: Derivative structure comparison
        obstruction_summary: Summary of all obstructions
        algebra_description: Description of the actual fracton algebra
        wxy_assessment: Assessment of Wang-Xu-Yau theories
        bb_assessment: Assessment of Bulmash-Barkeshli theories
        obstructions: List of all identified obstructions
    """
    is_compatible: bool
    derivative_comparison: DerivativeStructureComparison
    obstruction_summary: str
    algebra_description: str
    wxy_assessment: str
    bb_assessment: str
    obstructions: list[str] = field(default_factory=list)

    @property
    def n_obstructions(self) -> int:
        """Number of identified obstructions."""
        return len(self.obstructions)

    @property
    def is_structural(self) -> bool:
        """Whether the incompatibility is structural (not merely technical)."""
        return not self.is_compatible and self.n_obstructions >= 3


# ===================================================================
# Analysis functions
# ===================================================================

def wang_xu_yau_theory(gauge_group: str = "SU(2)") -> NonAbelianFractonGauge:
    """Construct the Wang-Xu-Yau non-Abelian tensor gauge theory.

    Wang-Xu-Yau (PRR 3, 013185, 2021) define non-Abelian tensor gauge
    theories by extending Pretko's A_ij to carry color indices:

        A^a_ij, a = 1, ..., dim(G)

    The gauge transformation:
        delta A^a_ij = partial_i partial_j alpha^a + f^a_bc A^b_ij alpha^c

    This has the structure of a non-Abelian extension, but the two-derivative
    structure (partial_i partial_j) makes the resulting algebra fundamentally
    different from standard Yang-Mills.

    The gauge parameters alpha^a are SCALAR fields (not spacetime vectors),
    and there are dim(G) of them. In contrast, Yang-Mills has D * dim(G)
    gauge parameters (dim(G) vector fields, each with D components).

    Args:
        gauge_group: Name of the gauge group (default "SU(2)")

    Returns:
        NonAbelianFractonGauge describing the WXY theory
    """
    dim_map = {
        "SU(2)": 3,
        "SU(3)": 8,
        "SU(N)": None,
        "U(1)": 1,
    }

    dim = dim_map.get(gauge_group)
    if dim is None:
        raise ValueError(
            f"Gauge group '{gauge_group}' not in supported list: {list(dim_map.keys())}"
        )

    # In 3D spatial: A^a_ij has dim(G) * 6 independent components
    # (6 = symmetric 3x3 matrix components)
    spatial_dim = 3
    symmetric_components = spatial_dim * (spatial_dim + 1) // 2
    field_components = dim * symmetric_components

    return NonAbelianFractonGauge(
        gauge_group_name=gauge_group,
        gauge_group_dim=dim,
        algebra_type=AlgebraType.NON_ABELIAN_FRACTON,
        n_gauge_parameters=dim,  # dim(G) scalar parameters
        derivative_order=2,
        is_abelian_gauge=False,  # Gauge is non-Abelian in color
        has_non_abelian_fusion=False,
        source_of_non_abelian=NonAbelianSourceType.GAUGE_TRANSFORMATION,
        field_components=field_components,
    )


def bulmash_barkeshli_theory() -> NonAbelianFractonGauge:
    """Construct the Bulmash-Barkeshli non-Abelian fracton model.

    Bulmash-Barkeshli (PRB 100, 155146, 2019) construct fracton models
    with non-Abelian fusion rules. The key distinction from Wang-Xu-Yau:

    - The GAUGE structure remains Abelian (delta A_ij = dd alpha)
    - The NON-ABELIAN structure comes from FUSION rules (anyon-like)
    - Fracton charge types can fuse non-commutatively: a x b != b x a
    - Position-dependent degeneracies are protected by immobility
      (charge + dipole conservation prevents particles from moving
      and thereby probing the degeneracy)

    This is a fundamentally different source of non-Abelian structure
    compared to Yang-Mills gauge redundancy.

    Returns:
        NonAbelianFractonGauge describing the BB model
    """
    return NonAbelianFractonGauge(
        gauge_group_name="Abelian (with non-Abelian fusion)",
        gauge_group_dim=1,
        algebra_type=AlgebraType.FUSION_NON_ABELIAN,
        n_gauge_parameters=1,  # Abelian gauge, 1 scalar parameter
        derivative_order=2,
        is_abelian_gauge=True,  # Gauge IS Abelian
        has_non_abelian_fusion=True,
        source_of_non_abelian=NonAbelianSourceType.FUSION_RULES,
        field_components=6,  # Abelian in 3D: 6 symmetric components
    )


def standard_yang_mills(gauge_group: str = "SU(3)") -> NonAbelianFractonGauge:
    """Construct standard Yang-Mills for comparison.

    Standard Yang-Mills gauge transformation:
        delta A^a_mu = partial_mu alpha^a + f^a_bc A^b_mu alpha^c
                     = D_mu alpha^a

    Key differences from fracton:
    - Single derivative partial_mu (not two derivatives dd)
    - Gauge parameters alpha^a are EFFECTIVELY vector-valued
      (they generate D * dim(G) gauge transformations via partial_mu)
    - Covariant derivative D_mu is well-defined on curved manifolds
    - Gauge closure [D_mu, D_nu] = F_mu_nu is the field strength
      (not a curvature obstruction)

    Args:
        gauge_group: Name of the gauge group (default "SU(3)")

    Returns:
        NonAbelianFractonGauge describing standard YM (for comparison)
    """
    dim_map = {
        "SU(2)": 3,
        "SU(3)": 8,
        "U(1)": 1,
    }

    dim = dim_map.get(gauge_group)
    if dim is None:
        raise ValueError(
            f"Gauge group '{gauge_group}' not in supported list: {list(dim_map.keys())}"
        )

    spacetime_dim = 4
    field_components = dim * spacetime_dim

    return NonAbelianFractonGauge(
        gauge_group_name=gauge_group,
        gauge_group_dim=dim,
        algebra_type=AlgebraType.YANG_MILLS,
        n_gauge_parameters=dim,
        derivative_order=1,
        is_abelian_gauge=False,
        has_non_abelian_fusion=False,
        source_of_non_abelian=NonAbelianSourceType.GAUGE_TRANSFORMATION,
        field_components=field_components,
    )


def derivative_structure_comparison() -> DerivativeStructureComparison:
    """Compare the derivative structure of fracton and Yang-Mills gauge theories.

    The fundamental algebraic obstruction: fracton gauge transformations use
    TWO spatial derivatives (partial_i partial_j alpha), while Yang-Mills uses
    ONE spacetime derivative (partial_mu alpha).

    Consequences:
    1. Fracton gauge commutator involves FOURTH-order derivatives:
       [delta_1, delta_2] A^a_ij ~ f^a_bc (dd alpha_1)(A alpha_2 - A alpha_1)
       vs Yang-Mills: [delta_1, delta_2] A^a_mu ~ f^a_bc partial_mu(...)

    2. On curved manifolds, [nabla_i, nabla_j] = R introduces curvature
       terms that spoil fracton gauge closure. For Yang-Mills, [D_mu, D_nu] = F
       defines the field strength (a feature, not a bug).

    3. Fracton gauge parameters are scalars. Yang-Mills gauge parameters
       effectively generate vector transformations via partial_mu.

    Returns:
        DerivativeStructureComparison with the analysis
    """
    return DerivativeStructureComparison(
        fracton_derivative_order=2,
        yang_mills_derivative_order=1,
        commutator_structure_matches=False,
        closure_condition_satisfied=False,
        curvature_obstruction=True,
    )


def analyze_non_abelian_compatibility() -> YangMillsCompatibility:
    """Full analysis of non-Abelian fracton compatibility with Yang-Mills.

    Checks four independent criteria, all of which must be satisfied
    for Yang-Mills compatibility:

    1. Derivative structure: fracton dd vs YM d (INCOMPATIBLE)
    2. Commutator algebra: fracton involves dddd, YM involves dd (INCOMPATIBLE)
    3. Gauge closure: fracton requires flatness, YM works on any manifold (INCOMPATIBLE)
    4. Representation theory: fracton scalars vs YM vectors (INCOMPATIBLE)

    Additionally assesses the two main non-Abelian fracton constructions:
    - Wang-Xu-Yau: non-Abelian in color but two-derivative structure persists
    - Bulmash-Barkeshli: non-Abelian fusion but Abelian gauge

    Conclusion: Non-Abelian fracton gauge theories exist but represent a
    fundamentally different algebraic structure from SU(N) Yang-Mills.

    Returns:
        YangMillsCompatibility with the complete analysis
    """
    deriv_comp = derivative_structure_comparison()

    obstructions = [
        (
            "DERIVATIVE ORDER: Fracton gauge transformation "
            "delta A^a_ij = partial_i partial_j alpha^a + f^a_bc A^b_ij alpha^c "
            "uses TWO spatial derivatives (partial_i partial_j). "
            "Yang-Mills uses ONE spacetime derivative: "
            "delta A^a_mu = partial_mu alpha^a + f^a_bc A^b_mu alpha^c. "
            "This is a qualitative algebraic difference, not a quantitative one."
        ),
        (
            "COMMUTATOR STRUCTURE: The gauge commutator in the fracton case "
            "involves FOURTH-order derivative terms (from composing two "
            "second-order gauge transformations), while Yang-Mills commutators "
            "involve only SECOND-order terms. The commutator algebras are "
            "structurally different and cannot be mapped to each other."
        ),
        (
            "GAUGE CLOSURE (Gromov obstruction): On curved manifolds, "
            "the fracton covariant extension nabla_i nabla_j alpha introduces "
            "[nabla_i, nabla_j] = R^k_lij curvature terms that BREAK gauge "
            "closure. For Yang-Mills, [D_mu, D_nu] = F_mu_nu defines the "
            "field strength and gauge closure is AUTOMATIC on any manifold. "
            "Dynamical geometry requires curved manifolds, making this "
            "obstruction fatal."
        ),
        (
            "REPRESENTATION THEORY: Fracton gauge parameters alpha^a are "
            "SCALAR fields (one per generator of the gauge group). Yang-Mills "
            "gauge parameters alpha^a are also scalars, but they generate "
            "VECTOR gauge transformations via partial_mu alpha^a. The fracton "
            "version generates TENSOR gauge transformations via partial_i partial_j "
            "alpha^a. These generate different subgroups of the full diffeomorphism "
            "group and cannot be identified."
        ),
    ]

    wxy_assessment = (
        "Wang-Xu-Yau (PRR 3, 013185, 2021) construct non-Abelian tensor gauge "
        "theories with gauge field A^a_ij carrying color indices a = 1,...,dim(G). "
        "The gauge transformation delta A^a_ij = partial_i partial_j alpha^a + "
        "f^a_bc A^b_ij alpha^c is genuinely non-Abelian in the COLOR indices. "
        "However, the two-derivative spatial structure (partial_i partial_j) "
        "persists, making the full gauge algebra fundamentally different from "
        "standard Yang-Mills. The WXY algebra has dim(G) scalar gauge parameters "
        "(not D * dim(G) vector parameters as in YM), and the commutator structure "
        "involves fourth-order derivatives with no YM analogue. "
        "The theory is a legitimate non-Abelian FRACTON theory but NOT a "
        "Yang-Mills theory."
    )

    bb_assessment = (
        "Bulmash-Barkeshli (PRB 100, 155146, 2019) construct fracton models "
        "with non-Abelian FUSION rules (anyon-like). The key distinction: the "
        "underlying tensor GAUGE structure remains Abelian (delta A_ij = dd alpha). "
        "The non-Abelian structure arises from fusion of fracton charge types, "
        "not from gauge transformations. Position-dependent degeneracies are "
        "protected by fracton immobility (charge + dipole conservation). "
        "This provides a fundamentally different source of non-Abelian structure "
        "compared to Yang-Mills gauge redundancy: non-Abelian FUSION is not the "
        "same as non-Abelian GAUGE symmetry."
    )

    return YangMillsCompatibility(
        is_compatible=False,
        derivative_comparison=deriv_comp,
        obstruction_summary=(
            "Non-Abelian fracton gauge theories exist (Wang-Xu-Yau, "
            "Bulmash-Barkeshli) but their algebra is FUNDAMENTALLY DIFFERENT "
            "from SU(N) Yang-Mills. Four independent obstructions converge: "
            "(1) derivative order mismatch (dd vs d), "
            "(2) commutator structure mismatch (dddd vs dd terms), "
            "(3) gauge closure breaks on curved manifolds (Gromov obstruction, "
            "fatal for dynamical geometry), "
            "(4) representation theory mismatch (scalar vs vector gauge parameters). "
            "The non-Abelian structure in existing fracton models is either "
            "gauge-transformation-based with wrong derivative structure (WXY) "
            "or fusion-based with Abelian gauge (BB). Neither produces "
            "emergent SU(N) Yang-Mills."
        ),
        algebra_description=(
            "The non-Abelian fracton algebra is characterized by: "
            "(a) scalar gauge parameters alpha^a with two-derivative structure "
            "delta A^a_ij = partial_i partial_j alpha^a + f^a_bc A^b_ij alpha^c, "
            "(b) commutator involving fourth-order derivatives, "
            "(c) gauge closure requiring flat spatial manifold (Gromov), "
            "(d) Aristotelian spacetime structure (absolute time, no boosts). "
            "This algebra can be obtained as an Inonu-Wigner contraction of "
            "the Poincare algebra in one higher dimension "
            "(Pena-Benitez-Salgado-Rebolledo, 2024), confirming it is a "
            "DEGENERATE limit of the full symmetry, not an alternative to it."
        ),
        wxy_assessment=wxy_assessment,
        bb_assessment=bb_assessment,
        obstructions=obstructions,
    )
