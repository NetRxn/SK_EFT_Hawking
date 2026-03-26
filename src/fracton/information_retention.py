"""Information Retention: Fracton vs Standard Hydrodynamics.

Quantifies how much UV (microscopic) information is preserved after
hydrodynamization in fracton vs standard Navier-Stokes hydrodynamics.

The key comparison:

Standard NS hydrodynamics:
    - Conserves energy E, momentum P_i (d components), particle number N
    - Total: d + 2 conserved charges
    - At late times: O(1) macroscopic parameters (T, u^i, mu)
    - All other information is erased by dissipation

Fracton hydrodynamics:
    - Conserves charge Q + dipole D_i + ... up to n-th multipole
    - Total multipole charges: C(n + d, d) (binomial coefficient)
    - With Hilbert space fragmentation: exponentially many Krylov
      subsectors, each preserving additional independent information
    - Even at "late times", distinguishable initial states scale as
      O(L^d) or O(exp(L)) depending on fragmentation strength

Hilbert space fragmentation (Sala et al., PRX 2020):
    - Dipole-conserving models fragment into exponentially many
      Krylov subsectors
    - Frozen states grow as ~(4/3)^L in 1D spin-1 models
    - Strong fragmentation: dim(K_max) / dim(H_{q,p}) -> 0 exponentially
    - Each Krylov sector label is an independently preserved bit

Gauge information assessment:
    - Standard hydro erases non-Abelian gauge DOF (gauge erasure theorem)
    - Fracton hydro preserves more information through fragmentation
    - But this information is NOT encoded as gauge field DOF
    - Rather, it is encoded as multipole/fragmentation structure
    - The GKSW commutativity argument does not apply to subsystem symmetries
    - Subsystem symmetry operators are rigid and geometry-dependent,
      not topologically deformable
    - Conclusion: fracton hydro carries partial non-Abelian information
      through fragmentation patterns, not conventional gauge transport

References:
    - Sala et al. (Phys. Rev. X 10, 011047, 2020): HSF
    - Hart-Lucas-Nandkishore (PRE 105, 044103, 2022): harmonic moments
    - Schmitz-Ma-Nandkishore-Parameswaran: X-Cube recoverable information
    - Stephen-Hart-Nandkishore (PRL 132, 040401, 2024): robust HSF
    - Bulmash-Barkeshli (PRB 100, 155146, 2019): non-Abelian fractons
    - Wang-Xu-Yau (PRR 3, 013185, 2021): non-Abelian tensor gauge theories
"""

from dataclasses import dataclass, field
from enum import Enum
from math import comb, log2, factorial
from typing import Optional

import numpy as np


# ═══════════════════════════════════════════════════════════════════
# Standard hydrodynamics
# ═══════════════════════════════════════════════════════════════════

@dataclass
class StandardHydroInfo:
    """Information content of standard Navier-Stokes hydrodynamics.

    Standard NS hydro conserves:
        - Energy: 1 charge
        - Momentum: d charges (one per spatial dimension)
        - Particle number: 1 charge
        - Total: d + 2 conserved charges

    At late times, all microscopic information beyond these d + 2
    extensive quantities is erased by dissipation. The macroscopic
    state is parameterized by O(1) intensive fields: temperature T,
    velocity u^i, chemical potential mu.

    Attributes:
        spatial_dim: Number of spatial dimensions d
        conserved_charges: Total conserved charge count = d + 2
        info_bits: Information content in bits (= log2 of distinguishable
            macroscopic states, effectively d + 2 real numbers)
        has_energy: Whether energy is conserved
        has_momentum: Whether momentum is conserved
        has_particle_number: Whether particle number is conserved
    """
    spatial_dim: int
    has_energy: bool = True
    has_momentum: bool = True
    has_particle_number: bool = True

    def __post_init__(self):
        if self.spatial_dim < 1:
            raise ValueError(
                f"Spatial dimension must be >= 1, got {self.spatial_dim}"
            )

    @property
    def conserved_charges(self) -> int:
        """Number of conserved charges: d + 2 for standard hydro."""
        n = 0
        if self.has_energy:
            n += 1
        if self.has_momentum:
            n += self.spatial_dim
        if self.has_particle_number:
            n += 1
        return n

    @property
    def info_bits(self) -> float:
        """Information content: number of conserved charges.

        Each conserved charge contributes one independent extensive
        thermodynamic parameter needed to specify the macroscopic state.
        This is the natural measure of retained information: how many
        real numbers characterize the late-time state.
        """
        return float(self.conserved_charges)

    @property
    def macroscopic_parameters(self) -> list[str]:
        """List of macroscopic parameters at late times."""
        params = []
        if self.has_energy:
            params.append("T (temperature)")
        if self.has_momentum:
            for i in range(self.spatial_dim):
                params.append(f"u_{i+1} (velocity)")
        if self.has_particle_number:
            params.append("mu (chemical potential)")
        return params


def standard_hydro_charges(d: int) -> StandardHydroInfo:
    """Construct standard hydro info for d spatial dimensions.

    Standard NS hydro conserves d + 2 charges:
    1 (energy) + d (momenta) + 1 (particle number) = d + 2

    Args:
        d: Number of spatial dimensions

    Returns:
        StandardHydroInfo with d + 2 conserved charges
    """
    return StandardHydroInfo(spatial_dim=d)


# ═══════════════════════════════════════════════════════════════════
# Fracton hydrodynamics
# ═══════════════════════════════════════════════════════════════════

@dataclass
class FragmentationData:
    """Hilbert space fragmentation data for a fracton system.

    Hilbert space fragmentation (HSF) occurs when dipole-conserving
    models with local interactions break the Hilbert space into
    exponentially many dynamically disconnected Krylov subsectors.

    Key results:
        - Frozen states grow as ~(4/3)^L for 1D spin-1 models
        - Under strong fragmentation, dim(K_max)/dim(H) -> 0 exponentially
        - Preserved bits scale as O(L) from Krylov sector labels
        - X-Cube model: 6L - 3 logical qubits (O(L))
        - Haah's code: number-theoretic in L

    Attributes:
        system_size: Linear system size L
        spatial_dim: Number of spatial dimensions d
        n_frozen_states: Number of frozen (one-dimensional Krylov) states
        n_krylov_sectors: Total number of Krylov subsectors
        largest_sector_fraction: dim(K_max) / dim(H_{q,p})
        preserved_bits: Lower bound on preserved information bits
        fragmentation_type: "weak" or "strong"
    """
    system_size: int
    spatial_dim: int = 1
    n_frozen_states: Optional[int] = None
    n_krylov_sectors: Optional[int] = None
    largest_sector_fraction: Optional[float] = None
    preserved_bits: float = 0.0
    fragmentation_type: str = "strong"

    @property
    def is_strongly_fragmented(self) -> bool:
        """Strong fragmentation: largest sector is vanishing fraction."""
        if self.largest_sector_fraction is not None:
            return self.largest_sector_fraction < 0.5
        return self.fragmentation_type == "strong"


@dataclass
class FractonHydroInfo:
    """Information content of fracton hydrodynamics.

    Fracton hydro conserves dramatically more than standard hydro:

    Exact multipole charges:
        Sum_{n=0}^{N} C(n + d - 1, n) = C(N + d, d)
        This is the number of independent components of all
        symmetric tensors up to rank N in d dimensions.

    Harmonic moments (Hart-Lucas-Nandkishore):
        In 2D with isotropic dipole conservation, infinitely many
        harmonic multipole charges Q_m = integral (x + iy)^m rho
        are exactly conserved at the linear level. Nonlinear
        corrections are dangerously irrelevant (power-law decay
        with increasing exponent).

    Hilbert space fragmentation:
        Exponentially many Krylov subsectors, each an independent
        constraint. For 1D spin-1 models: >= log2((4/3)^L) = O(L) bits.
        X-Cube model: 6L - 3 logical qubits.

    Attributes:
        spatial_dim: Number of spatial dimensions d
        max_multipole_order: Highest conserved multipole N
        exact_multipole_charges: C(N + d, d) exact charges
        has_harmonic_moments: Whether infinite harmonic moments exist
        fragmentation: Hilbert space fragmentation data (if computed)
        has_momentum: Whether momentum is conserved
        has_energy: Whether energy is conserved
    """
    spatial_dim: int
    max_multipole_order: int
    has_harmonic_moments: bool = False
    fragmentation: Optional[FragmentationData] = None
    has_momentum: bool = True
    has_energy: bool = True

    def __post_init__(self):
        if self.spatial_dim < 1:
            raise ValueError(
                f"Spatial dimension must be >= 1, got {self.spatial_dim}"
            )
        if self.max_multipole_order < 0:
            raise ValueError(
                f"max_multipole_order must be >= 0, got {self.max_multipole_order}"
            )

    @property
    def exact_multipole_charges(self) -> int:
        """Number of exactly conserved multipole charges: C(N + d, d).

        This is the total number of independent components of all
        symmetric tensors from rank 0 through rank N in d dimensions.

        For N = 0: C(d, d) = 1 (just charge)
        For N = 1: C(1 + d, d) = d + 1 (charge + dipole)
        For N = 2: C(2 + d, d) = (d+1)(d+2)/2
        """
        return comb(self.max_multipole_order + self.spatial_dim,
                     self.spatial_dim)

    @property
    def conserved_charges(self) -> int:
        """Total conserved charges including momentum and energy."""
        n = self.exact_multipole_charges
        if self.has_momentum:
            n += self.spatial_dim
        if self.has_energy:
            n += 1
        return n

    @property
    def info_bits(self) -> float:
        """Lower bound on preserved information.

        Three contributions:
        1. Exact multipole charges: C(N+d, d) + momentum + energy
        2. Harmonic moments: countably infinite (but quasi-conserved)
        3. Fragmentation: O(L^d) bits for strong HSF

        The dominant contribution at large L is fragmentation.
        Without fragmentation, the baseline is the conserved charge count.
        """
        bits = float(self.conserved_charges)

        if self.fragmentation is not None:
            bits = max(bits, self.fragmentation.preserved_bits)

        return bits

    @property
    def fragmentation_sectors(self) -> Optional[int]:
        """Number of Krylov subsectors (if fragmentation data available)."""
        if self.fragmentation is not None:
            return self.fragmentation.n_krylov_sectors
        return None


def fracton_hydro_charges(
    d: int,
    max_multipole: int,
    system_size: Optional[int] = None,
    include_fragmentation: bool = True,
) -> FractonHydroInfo:
    """Construct fracton hydro info for d dimensions with n-pole conservation.

    Args:
        d: Number of spatial dimensions
        max_multipole: Highest conserved multipole order N
            N=0: standard charge conservation
            N=1: charge + dipole (minimal fracton)
            N=2: charge + dipole + quadrupole
        system_size: Linear system size L (needed for fragmentation)
        include_fragmentation: Whether to compute fragmentation data

    Returns:
        FractonHydroInfo with complete information analysis
    """
    fragmentation = None
    if include_fragmentation and system_size is not None and max_multipole >= 1:
        fragmentation = hilbert_space_fragmentation(
            system_size=system_size,
            spatial_dim=d,
            multipole_order=max_multipole,
        )

    # Harmonic moments exist in 2D with isotropic dipole conservation
    has_harmonics = (d == 2 and max_multipole >= 1)

    return FractonHydroInfo(
        spatial_dim=d,
        max_multipole_order=max_multipole,
        has_harmonic_moments=has_harmonics,
        fragmentation=fragmentation,
    )


# ═══════════════════════════════════════════════════════════════════
# Hilbert space fragmentation
# ═══════════════════════════════════════════════════════════════════

def hilbert_space_fragmentation(
    system_size: int,
    spatial_dim: int = 1,
    multipole_order: int = 1,
) -> FragmentationData:
    """Compute Hilbert space fragmentation data.

    For dipole-conserving 1D spin-1 models (Sala et al., PRX 2020):
        - Frozen states grow as ~(4/3)^L
        - Preserved bits >= log2((4/3)^L) = L * log2(4/3) ~ 0.415 * L
        - Strong fragmentation: largest sector fraction -> 0 exponentially

    For X-Cube model (Schmitz et al.):
        - Logical qubits = 6L - 3
        - Each is independently preserved

    For higher dimensions, fragmentation scales as O(L^d) bits
    from the subsystem symmetry structure.

    Args:
        system_size: Linear system size L
        spatial_dim: Number of spatial dimensions d
        multipole_order: Multipole conservation order n

    Returns:
        FragmentationData with computed bounds
    """
    if system_size < 1:
        raise ValueError(f"System size must be >= 1, got {system_size}")

    L = system_size
    d = spatial_dim

    if d == 1:
        # 1D dipole-conserving spin-1 model (Sala et al.)
        # Frozen states: ~(4/3)^L
        # Use logarithmic computation to avoid overflow for large L
        log_frozen = L * np.log(4.0 / 3.0)
        if log_frozen < 700:  # safe for float64
            n_frozen = int(round(np.exp(log_frozen)))
        else:
            n_frozen = None  # too large to represent as int

        # Preserved bits: at least log2 of frozen state count
        bits = L * log2(4.0 / 3.0)  # ~ 0.415 * L

        # Largest sector fraction decays exponentially: (3/4)^L
        # Use logarithm to avoid overflow
        log_frac = L * np.log(3.0 / 4.0)
        if log_frac > -700:
            largest_frac = np.exp(log_frac)
        else:
            largest_frac = 0.0  # exponentially small

        return FragmentationData(
            system_size=L,
            spatial_dim=d,
            n_frozen_states=n_frozen,
            largest_sector_fraction=largest_frac,
            preserved_bits=bits,
            fragmentation_type="strong",
        )
    else:
        # Higher-dimensional generalization
        # X-Cube (d=3): 6L - 3 logical qubits
        # General fracton: O(L^{d-1}) from subsystem symmetry constraints
        if d == 3:
            bits = float(6 * L - 3)  # X-Cube formula
        else:
            # Scale as L^{d-1} (number of independent subsystem constraints)
            bits = float(L ** (d - 1))

        return FragmentationData(
            system_size=L,
            spatial_dim=d,
            preserved_bits=bits,
            fragmentation_type="strong",
        )


# ═══════════════════════════════════════════════════════════════════
# Information comparison
# ═══════════════════════════════════════════════════════════════════

@dataclass
class InformationComparison:
    """Comparison of information retention between standard and fracton hydro.

    The key metric is the retention ratio:
        ratio = (fracton info bits) / (standard info bits)

    For large systems with strong fragmentation, this diverges:
    fracton preserves O(L^d) bits vs O(1) for standard hydro.

    Attributes:
        standard: Standard hydro information
        fracton: Fracton hydro information
        retention_ratio: fracton.info_bits / standard.info_bits
        exact_charge_ratio: fracton multipole charges / standard charges
        fragmentation_factor: Additional bits from HSF (0 if no HSF)
    """
    standard: StandardHydroInfo
    fracton: FractonHydroInfo

    @property
    def retention_ratio(self) -> float:
        """Ratio of preserved information: fracton / standard."""
        std_bits = self.standard.info_bits
        frac_bits = self.fracton.info_bits
        if std_bits == 0:
            return float('inf')
        return frac_bits / std_bits

    @property
    def exact_charge_ratio(self) -> float:
        """Ratio of exact conserved charges: fracton / standard."""
        std = self.standard.conserved_charges
        frac = self.fracton.conserved_charges
        if std == 0:
            return float('inf')
        return frac / std

    @property
    def fragmentation_factor(self) -> float:
        """Additional information from Hilbert space fragmentation.

        This is the fragmentation-specific information beyond the
        exact multipole charges. When fragmentation dominates,
        this grows as O(L^d) while multipole charges are O(1).
        """
        if self.fracton.fragmentation is None:
            return 0.0
        return max(
            0.0,
            self.fracton.fragmentation.preserved_bits
            - float(self.fracton.conserved_charges)
        )


def information_ratio(
    d: int,
    max_multipole: int,
    system_size: Optional[int] = None,
) -> InformationComparison:
    """Compute the information retention ratio between fracton and standard hydro.

    Args:
        d: Spatial dimension
        max_multipole: Highest conserved multipole order in fracton system
        system_size: Linear system size (for fragmentation computation)

    Returns:
        InformationComparison with complete analysis
    """
    std = standard_hydro_charges(d)
    frac = fracton_hydro_charges(
        d=d,
        max_multipole=max_multipole,
        system_size=system_size,
    )
    return InformationComparison(standard=std, fracton=frac)


def compare_information_retention(
    spatial_dims: list[int] | None = None,
    multipole_orders: list[int] | None = None,
    system_size: int = 100,
) -> list[dict]:
    """Compute information retention comparison across dimensions and multipole orders.

    Produces a structured table comparing standard and fracton hydro
    information retention for various parameter combinations.

    Args:
        spatial_dims: List of spatial dimensions to compare (default: [1, 2, 3])
        multipole_orders: List of multipole orders (default: [0, 1, 2, 5, 10])
        system_size: System size for fragmentation (default: 100)

    Returns:
        List of dicts with comparison data for each (d, n) combination
    """
    if spatial_dims is None:
        spatial_dims = [1, 2, 3]
    if multipole_orders is None:
        multipole_orders = [0, 1, 2, 5, 10]

    results = []
    for d in spatial_dims:
        for n in multipole_orders:
            comparison = information_ratio(
                d=d,
                max_multipole=n,
                system_size=system_size,
            )
            results.append({
                "spatial_dim": d,
                "multipole_order": n,
                "standard_charges": comparison.standard.conserved_charges,
                "fracton_multipole_charges": comparison.fracton.exact_multipole_charges,
                "fracton_total_charges": comparison.fracton.conserved_charges,
                "standard_info_bits": comparison.standard.info_bits,
                "fracton_info_bits": comparison.fracton.info_bits,
                "retention_ratio": comparison.retention_ratio,
                "exact_charge_ratio": comparison.exact_charge_ratio,
                "fragmentation_factor": comparison.fragmentation_factor,
                "has_harmonic_moments": comparison.fracton.has_harmonic_moments,
            })

    return results


# ═══════════════════════════════════════════════════════════════════
# Gauge information assessment
# ═══════════════════════════════════════════════════════════════════

class GaugeInfoMechanism(Enum):
    """Mechanism by which gauge information could be preserved."""
    CONVENTIONAL_TRANSPORT = "conventional_transport"
    FRAGMENTATION_PATTERNS = "fragmentation_patterns"
    MULTIPOLE_STRUCTURE = "multipole_structure"
    POSITION_DEPENDENT_DEGENERACY = "position_dependent_degeneracy"
    SUBSYSTEM_SYMMETRY = "subsystem_symmetry"


@dataclass
class GaugeInformationAssessment:
    """Assessment of whether fracton hydro can carry non-Abelian gauge information.

    Central question: Can fracton hydrodynamics preserve information that
    encodes non-Abelian gauge structure, despite the gauge erasure theorem
    ruling this out for standard hydrodynamics?

    Answer: PARTIALLY. Through fragmentation patterns, not conventional
    gauge transport.

    The argument:

    1. Standard hydro erases non-Abelian gauge DOF (gauge erasure theorem):
       - Higher-form symmetries must be Abelian (GKSW)
       - Non-Abelian groups have only discrete center Z_N
       - Discrete breaking -> domain walls, not Goldstone modes
       - No hydrodynamic modes -> gauge DOF are erased

    2. Fracton hydro DOES NOT transport gauge information conventionally:
       - Color charges are covariantly conserved, not ordinarily conserved
       - Fracton conservation laws (charge, dipole) apply to ordinary
         (not covariant) charges
       - The gauge erasure obstruction still applies to the gauge sector

    3. But fracton hydro DOES preserve more information via:
       - Hilbert space fragmentation locks states into Krylov sectors
       - Each sector label is an independently preserved bit
       - Fragmentation patterns can encode information about the
         initial state that INDIRECTLY contains gauge structure
       - Non-Abelian fracton models (Bulmash-Barkeshli) have
         position-dependent degeneracies protected by immobility
       - Subsystem symmetries evade the GKSW commutativity argument

    4. Critical gap: no finite-temperature analysis exists for
       non-Abelian fracton models. The survival mechanism is
       demonstrated at zero temperature but unproven at finite T.

    Attributes:
        conventional_transport: Whether conventional gauge transport works
        fragmentation_encoding: Whether fragmentation can encode gauge info
        gksw_evasion: Whether the GKSW commutativity argument is evaded
        finite_temperature_proven: Whether survival is proven at finite T
        overall_assessment: Summary assessment string
        mechanisms: Which mechanisms contribute to information retention
    """
    conventional_transport: bool
    fragmentation_encoding: bool
    gksw_evasion: bool
    finite_temperature_proven: bool
    overall_assessment: str
    mechanisms: list[GaugeInfoMechanism] = field(default_factory=list)

    @property
    def carries_gauge_info(self) -> str:
        """Whether fracton hydro carries non-Abelian gauge information.

        Returns one of: "yes", "no", "partially"
        """
        if self.conventional_transport:
            return "yes"
        if self.fragmentation_encoding or self.gksw_evasion:
            return "partially"
        return "no"

    @property
    def confidence_level(self) -> str:
        """Confidence in the assessment.

        "high" if supported by rigorous results,
        "medium" if supported by lattice models but no finite-T proof,
        "low" if speculative
        """
        if self.finite_temperature_proven:
            return "high"
        if self.fragmentation_encoding and self.gksw_evasion:
            return "medium"
        return "low"


def gauge_information_assessment() -> GaugeInformationAssessment:
    """Assess whether fracton hydro can carry non-Abelian gauge information.

    This encodes the central finding of the fracton Layer 2 analysis:
    fracton hydro preserves non-Abelian gauge information PARTIALLY,
    through fragmentation patterns and multipole structure, NOT through
    conventional gauge transport.

    The assessment follows the argument chain:
    1. Gauge erasure theorem blocks conventional transport (established)
    2. Subsystem symmetries evade GKSW commutativity (rigorous)
    3. Fragmentation preserves exponentially more initial-state info (proven)
    4. But no finite-T analysis of non-Abelian fracton models exists (gap)

    Returns:
        GaugeInformationAssessment with the complete analysis
    """
    return GaugeInformationAssessment(
        conventional_transport=False,
        fragmentation_encoding=True,
        gksw_evasion=True,
        finite_temperature_proven=False,
        overall_assessment=(
            "Fracton hydrodynamics preserves non-Abelian gauge information "
            "PARTIALLY through fragmentation patterns and multipole structure, "
            "NOT through conventional gauge field transport. "
            "The gauge erasure theorem (GKSW commutativity -> Abelian higher-form "
            "symmetries -> no non-Abelian Goldstone modes) still blocks conventional "
            "gauge transport. However, three mechanisms provide a genuine structural "
            "loophole: (1) subsystem symmetries are not higher-form symmetries and "
            "evade the GKSW commutativity argument; (2) Hilbert space fragmentation "
            "locks exponentially many initial-state bits into dynamically disconnected "
            "Krylov sectors; (3) non-Abelian fracton models (Bulmash-Barkeshli) have "
            "position-dependent degeneracies protected by immobility. The information "
            "is encoded differently: not as gauge field DOF but as fragmentation/"
            "multipole structure. Critical gap: no demonstration of non-Abelian "
            "information surviving fracton hydrodynamization at finite temperature "
            "exists. The loophole is conceptually compelling and supported by lattice "
            "model evidence, but mathematically unproven as a mechanism for "
            "non-Abelian survival in the hydrodynamic limit."
        ),
        mechanisms=[
            GaugeInfoMechanism.FRAGMENTATION_PATTERNS,
            GaugeInfoMechanism.MULTIPOLE_STRUCTURE,
            GaugeInfoMechanism.POSITION_DEPENDENT_DEGENERACY,
            GaugeInfoMechanism.SUBSYSTEM_SYMMETRY,
        ],
    )
