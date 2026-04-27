"""Code-distance proxy `d_C := log d_max` for MTC substrates.

Mirrors `HPCode.codeDistance` from `QECHolographyBridge.lean`. The
code-distance proxy reuses the W3 area-law leading coefficient
`κ_C = log d_max` as the topological-shielding scale of the encoded
logical qubit.
"""

from __future__ import annotations

import math
from dataclasses import dataclass


@dataclass(frozen=True)
class MTCSpectrum:
    """A modular tensor category's quantum-dimension spectrum.

    Fields:
        name: Identifier ("fibonacci", "ising", "su3_k2", ...).
        quantum_dims: Tuple of per-object quantum dimensions; the first
            entry is required to be the unit object's `d=1`.
    """

    name: str
    quantum_dims: tuple[float, ...]

    def __post_init__(self) -> None:
        if not self.quantum_dims:
            raise ValueError("MTC spectrum cannot be empty")
        if not math.isclose(self.quantum_dims[0], 1.0):
            raise ValueError(
                f"First quantum dim must be unit (=1.0), got {self.quantum_dims[0]}"
            )
        for d in self.quantum_dims:
            if d <= 0:
                raise ValueError(f"Quantum dimensions must be positive, got {d}")

    @property
    def d_max(self) -> float:
        """Maximum quantum dimension over simple objects."""
        return max(self.quantum_dims)


_PHI = (1.0 + math.sqrt(5.0)) / 2.0  # golden ratio
_SQRT2 = math.sqrt(2.0)

FIBONACCI_SPECTRUM = MTCSpectrum(
    name="fibonacci",
    quantum_dims=(1.0, _PHI),
)

ISING_SPECTRUM = MTCSpectrum(
    name="ising",
    quantum_dims=(1.0, _SQRT2, 1.0),  # 1, σ, ψ
)

SU3K2_SPECTRUM = MTCSpectrum(
    name="su3_k2_fibonacci_subsector",
    # vac + adj sub-sector forms a Fibonacci MTC by the
    # Hirono-Tanizaki SU(3)_k=2 ↔ Z_3 + Fibonacci decomposition.
    # We track the {vac, adj} Fibonacci-like sector here as a witness
    # MTC; the full 6-simple-object spectrum is not used in W4 numerics.
    quantum_dims=(1.0, _PHI),
)

TRIVIAL_ABELIAN_SPECTRUM = MTCSpectrum(
    name="trivial_abelian",
    quantum_dims=(1.0,),
)


def global_dim_sq(spectrum: MTCSpectrum) -> float:
    """Global dimension squared `D² = Σ d_a²`.

    Mirrors `HorizonMTCBC.globalDimSq` from `BHEntropyMicroscopic.lean`.
    """
    return sum(d * d for d in spectrum.quantum_dims)


def code_distance(spectrum: MTCSpectrum) -> float:
    """Code-distance proxy `d_C := log d_max`.

    Vanishes precisely when the substrate is abelian (`d_max = 1`).
    Mirrors `HPCode.codeDistance` from `QECHolographyBridge.lean`.
    """
    return math.log(spectrum.d_max)


def code_distance_admissible(spectrum: MTCSpectrum) -> bool:
    """Admissibility check: `d_C > 0` iff `d_max > 1` (non-abelian).

    Mirrors `HPCode.code_distance_scaling_matches_anyonic_fusion_iff_fusion_in_admissible_class.1`
    from the Lean module (the biconditional is now the first conjunct of the
    correctness-push, post-2026-04-28 cross-wave strengthening).
    """
    return code_distance(spectrum) > 0.0
