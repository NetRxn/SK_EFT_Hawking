"""Phase 6c Wave 3 — Equivalence-Principle classification of Phase 5x DM mechanisms.

Python mirror of `lean/SKEFTHawking/EquivalencePrinciple.lean`.

Subpackage scope:
- `mechanism_classifier`: classifies six Phase 5x DM-related mechanisms
  (vestigial differential coupling; vestigial relics STEP-class;
  Fang-Gu torsion DM; fracton subdiffusion; SFDM Thomas-Fermi;
  hidden-sector ℤ₁₆ singlet) into WEP/EEP/SEP × ViolatesEP matrix.
  Two violators (both vestigial-phase phenomena), four non-violators.

Primary references:
- VestigialGravity.lean (Phase 4 W2): `ep_violation_in_vestigial`
- ClassificationTableDark.lean (Phase 5y W7): `MicroscopeStatus.violated`
- DarkSectorSynthesis.lean (Phase 5x W8): η ~ 10⁻¹⁸ STEP-class
- Touboul et al., PRL 119, 231101 (2017): MICROSCOPE η < 10⁻¹⁵
"""

from .mechanism_classifier import (
    EPLevel,
    EPMechanism,
    violation_level,
    violates_at,
    satisfies_at,
    EP_VIOLATION_MATRIX,
    MICROSCOPE_BOUND,
    STEP_TARGET,
    VESTIGIAL_PHASE_ETA_MAX,
    VESTIGIAL_RELICS_ETA,
)

__all__ = [
    "EPLevel",
    "EPMechanism",
    "violation_level",
    "violates_at",
    "satisfies_at",
    "EP_VIOLATION_MATRIX",
    "MICROSCOPE_BOUND",
    "STEP_TARGET",
    "VESTIGIAL_PHASE_ETA_MAX",
    "VESTIGIAL_RELICS_ETA",
]
