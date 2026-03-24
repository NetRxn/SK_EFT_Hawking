"""Second-order SK-EFT analysis (Phase 2).

Extends the Phase 1 first-order result (2 transport coefficients, constant
δ_diss) to second order in the derivative expansion, introducing frequency-
dependent corrections and WKB mode analysis.

Modules:
    enumeration: Transport coefficient counting at arbitrary EFT order.
    coefficients: Data structures and action constructors for second-order SK-EFT.
    wkb_analysis: WKB mode analysis through the dissipative horizon.
"""

from src.second_order.enumeration import (
    DerivIndex,
    OrderAnalysis,
    analyze_order,
    fdr_relations,
    count_imaginary_monomials,
)
from src.second_order.coefficients import (
    FirstOrderCoeffs,
    SecondOrderCoeffs,
    FullCoeffs,
    hawking_correction_first_order,
    hawking_correction_second_order,
    effective_temperature,
    spectral_distortion,
)
from src.second_order.wkb_analysis import (
    TransonicProfile,
    WKBParameters,
    BogoliubovResult,
    connection_formula,
    compute_hawking_spectrum,
    extract_corrections,
)

__all__ = [
    # Enumeration
    "DerivIndex",
    "OrderAnalysis",
    "analyze_order",
    "fdr_relations",
    "count_imaginary_monomials",
    # Coefficients
    "FirstOrderCoeffs",
    "SecondOrderCoeffs",
    "FullCoeffs",
    "hawking_correction_first_order",
    "hawking_correction_second_order",
    "effective_temperature",
    "spectral_distortion",
    # WKB
    "TransonicProfile",
    "WKBParameters",
    "BogoliubovResult",
    "connection_formula",
    "compute_hawking_spectrum",
    "extract_corrections",
]
