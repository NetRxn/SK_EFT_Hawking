"""Fracton Hydrodynamics Layer 2: Alternative UV-Retentive Hydrodynamics.

Formalizes the string-membrane-net -> fracton -> SK-EFT chain as a rigorous
alternative Layer 2, and quantifies how much more UV information fracton
hydrodynamics preserves compared to standard Navier-Stokes hydrodynamics.

The key chain:
    1. Stacked 2+1D string-net models (Wen) -> type-I fracton phases
       via gauging diagonal 1-form symmetry (Gorantla-Prem-Tantivasadakarn-Williamson)
    2. Fracton phases have charge + dipole + higher multipole conservation
    3. SK-EFT for fracton hydro (Glorioso-Huang-Lucas, JHEP 2023):
       quadratic sound omega ~ k^2, subdiffusive damping omega ~ k^4
    4. Hilbert space fragmentation preserves exponentially more initial
       state information than standard hydrodynamization

Information retention comparison:
    - Standard NS hydro: O(d+2) conserved charges -> O(1) macroscopic parameters
    - Fracton hydro (n-th multipole): C(n+d, d) exact charges
    - Strong HSF (1D): >= O(L) bits preserved (Sala et al.)

Gauge information assessment:
    - Standard hydro erases all non-Abelian gauge DOF (gauge erasure theorem)
    - Fracton hydro preserves more through fragmentation patterns, NOT as
      conventional gauge field DOF but as multipole/fragmentation structure
    - The GKSW commutativity argument does not apply to subsystem symmetries
    - However, no demonstration of non-Abelian survival at finite temperature exists

Modules:
    sk_eft: Fracton SK-EFT transport coefficients and symmetry structure
    information_retention: UV information comparison between fracton and standard hydro
    gravity_connection: Fracton-gravity Kerr-Schild analysis, bootstrap gap, route comparison
    non_abelian: Non-Abelian fracton gauge theories and Yang-Mills compatibility

References:
    - Gorantla-Prem-Tantivasadakarn-Williamson (PRB 112, 125124, 2025)
    - Glorioso-Huang-Lucas (JHEP 05, 022, 2023)
    - Guo-Glorioso-Lucas (PRL 129, 150603, 2022)
    - Sala et al. (PRX 10, 011047, 2020)
    - Bulmash-Barkeshli (PRB 100, 155146, 2019)
    - Hart-Lucas-Nandkishore (PRE 105, 044103, 2022)
"""

from src.fracton.sk_eft import (
    FractonSymmetry,
    MultipoleCharge,
    FractonTransportCoefficients,
    FractonSKAction,
    FractonDispersionRelation,
    FractonSKAxiomCheck,
    classify_symmetry,
    compute_transport_coefficients,
    fracton_dispersion,
    verify_sk_axioms,
    upper_critical_dimension,
)
from src.fracton.information_retention import (
    StandardHydroInfo,
    FractonHydroInfo,
    FragmentationData,
    InformationComparison,
    GaugeInformationAssessment,
    GaugeCoarsegrainingResult,
    standard_hydro_charges,
    fracton_hydro_charges,
    information_ratio,
    hilbert_space_fragmentation,
    gauge_information_assessment,
    gauge_coarsegraining_example,
    compare_information_retention,
)
from src.fracton.gravity_connection import (
    LinearizedEquivalence,
    BootstrapStep,
    BootstrapGap,
    BootstrapGapQuantification,
    CubicVertexStructure,
    GravityRouteComparison,
    GravityRouteProperties,
    NonAbelianResult,
    linearized_equivalence,
    gupta_feynman_bootstrap,
    bootstrap_gap_assessment,
    quantify_bootstrap_gap,
    compare_gravity_routes,
    non_abelian_fracton_analysis,
)
from src.fracton.non_abelian import (
    NonAbelianFractonGauge,
    YangMillsCompatibility,
    DerivativeStructureComparison,
    analyze_non_abelian_compatibility,
    wang_xu_yau_theory,
    bulmash_barkeshli_theory,
    standard_yang_mills,
    derivative_structure_comparison,
)

__all__ = [
    # SK-EFT
    "FractonSymmetry",
    "MultipoleCharge",
    "FractonTransportCoefficients",
    "FractonSKAction",
    "FractonDispersionRelation",
    "FractonSKAxiomCheck",
    "classify_symmetry",
    "compute_transport_coefficients",
    "fracton_dispersion",
    "verify_sk_axioms",
    "upper_critical_dimension",
    # Information retention
    "StandardHydroInfo",
    "FractonHydroInfo",
    "FragmentationData",
    "InformationComparison",
    "GaugeInformationAssessment",
    "GaugeCoarsegrainingResult",
    "standard_hydro_charges",
    "fracton_hydro_charges",
    "information_ratio",
    "hilbert_space_fragmentation",
    "gauge_information_assessment",
    "gauge_coarsegraining_example",
    "compare_information_retention",
    # Gravity connection (3A)
    "LinearizedEquivalence",
    "BootstrapStep",
    "BootstrapGap",
    "BootstrapGapQuantification",
    "CubicVertexStructure",
    "GravityRouteComparison",
    "GravityRouteProperties",
    "NonAbelianResult",
    "linearized_equivalence",
    "gupta_feynman_bootstrap",
    "bootstrap_gap_assessment",
    "quantify_bootstrap_gap",
    "compare_gravity_routes",
    "non_abelian_fracton_analysis",
    # Non-Abelian fracton (3B)
    "NonAbelianFractonGauge",
    "YangMillsCompatibility",
    "DerivativeStructureComparison",
    "analyze_non_abelian_compatibility",
    "wang_xu_yau_theory",
    "bulmash_barkeshli_theory",
    "standard_yang_mills",
    "derivative_structure_comparison",
]
