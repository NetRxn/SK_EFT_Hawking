"""Fracton SK-EFT: Transport Coefficients and Symmetry Structure.

PROVENANCE NOTE: Fracton formulas are self-contained and do not yet
have canonical versions in formulas.py or Lean theorem references.
This is a known Pipeline Invariant 1+4 gap. When fracton physics is
formalized in Lean, these formulas should migrate to formulas.py.

Implements the Schwinger-Keldysh effective field theory for fracton
hydrodynamics following Glorioso-Huang-Lucas (JHEP 05, 022, 2023).

The fracton SK-EFT differs from standard SK-EFT in three key ways:

1. Conservation laws: charge Q, dipole moment D, momentum P with
   the non-trivial commutator [D, P] = iQ. This forces the momentum
   susceptibility to diverge as rho ~ n^2/k^2 at finite charge density.

2. Dispersion relation: quadratic sound omega = +/- sqrt(a/chi) k^2
   with subdiffusive damping omega ~ +/- c k^2 - i Gamma k^4, versus
   linear sound omega = +/- c_s k in standard hydro.

3. Transport coefficients: 4 dissipative (s1, s2, t1, t2) + 2 Hall-like
   (d1, d2) + 4 thermodynamic (b, a1, a2, a3) at leading order for
   isotropic PT-symmetric systems, following the Glorioso-Huang-Lucas
   classification.

The SK axioms (normalization, positivity, dynamical KMS) apply identically
to fracton and standard hydro. The key structural difference is in the
field content and symmetry transformations.

Higher multipole conservation (Guo-Glorioso-Lucas, PRL 2022):
   n-pole conservation forces the MSR Hamiltonian to depend on
   d^{n+1}_x pi, giving:
   - Dispersion: omega ~ k^{n+1}
   - Upper critical dimension: d_c = 2(1+n) for n even, 2n for n odd
   - Sound speed scaling: c ~ k^n

References:
    - Glorioso-Huang-Lucas (JHEP 05, 022, 2023): fracton SK-EFT
    - Guo-Glorioso-Lucas (PRL 129, 150603, 2022): multipole MSR
    - Pretko (PRD 96, 024051, 2017): fracton gauge theory
    - Gromov-Lucas-Nandkishore: fracton hydrodynamics review
"""

from dataclasses import dataclass, field
from enum import Enum
from typing import Optional

import numpy as np
from math import comb

from src.core.formulas import (
    fracton_charge_components,
    fracton_total_charges,
    fracton_dispersion_power,
    fracton_damping_power,
)


# ═══════════════════════════════════════════════════════════════════
# Symmetry classification
# ═══════════════════════════════════════════════════════════════════

class ConservationType(Enum):
    """Type of conservation law. Used only as metadata by MultipoleCharge.conservation_type."""
    CHARGE = "charge"           # Q = integral rho
    DIPOLE = "dipole"           # D_i = integral x_i rho
    QUADRUPOLE = "quadrupole"   # Q_ij = integral x_i x_j rho
    MULTIPOLE = "multipole"     # General n-th multipole
    MOMENTUM = "momentum"       # P_i
    ENERGY = "energy"           # E


@dataclass
class MultipoleCharge:
    """A conserved multipole charge.

    The n-th multipole moment is Q_{i1...in} = integral x_{i1}...x_{in} rho.
    Charge is n=0, dipole is n=1, quadrupole is n=2, etc.

    Attributes:
        order: Multipole order n (0=charge, 1=dipole, 2=quadrupole, ...)
        spatial_dim: Spatial dimension d
        n_components: Number of independent components = C(n+d-1, n)
        conservation_type: Classification label
    """
    order: int
    spatial_dim: int

    def __post_init__(self):
        if self.order < 0:
            raise ValueError(f"Multipole order must be >= 0, got {self.order}")
        if self.spatial_dim < 1:
            raise ValueError(f"Spatial dimension must be >= 1, got {self.spatial_dim}")

    @property
    def n_components(self) -> int:
        """Number of independent symmetric tensor components.

        For an n-th rank symmetric tensor in d dimensions:
        C(n + d - 1, n) = (n + d - 1)! / (n! (d-1)!)
        """
        return comb(self.order + self.spatial_dim - 1, self.order)

    @property
    def conservation_type(self) -> ConservationType:
        if self.order == 0:
            return ConservationType.CHARGE
        elif self.order == 1:
            return ConservationType.DIPOLE
        elif self.order == 2:
            return ConservationType.QUADRUPOLE
        else:
            return ConservationType.MULTIPOLE

    @property
    def label(self) -> str:
        """Human-readable label."""
        names = {0: "charge", 1: "dipole", 2: "quadrupole",
                 3: "octupole", 4: "hexadecapole"}
        base = names.get(self.order, f"{self.order}-pole")
        return f"{base} ({self.n_components} components in {self.spatial_dim}D)"


@dataclass
class FractonSymmetry:
    """Symmetry structure of a fracton hydrodynamic system.

    Attributes:
        charge_conservation: Whether total charge Q is conserved
        dipole_conservation: Whether dipole moment D_i is conserved
        max_multipole_order: Highest conserved multipole order
        spatial_dim: Spatial dimension d
        momentum_conservation: Whether momentum is conserved
        energy_conservation: Whether energy is conserved
        has_pt_symmetry: Whether the system has parity-time symmetry
        is_isotropic: Whether the system has full rotational symmetry
    """
    charge_conservation: bool
    dipole_conservation: bool
    max_multipole_order: int  # 0 = charge only, 1 = charge + dipole, etc.
    spatial_dim: int = 3
    momentum_conservation: bool = True
    energy_conservation: bool = True
    has_pt_symmetry: bool = True
    is_isotropic: bool = True

    def __post_init__(self):
        if self.dipole_conservation and not self.charge_conservation:
            raise ValueError(
                "Dipole conservation requires charge conservation: "
                "[D, P] = iQ implies D conservation needs Q to be defined"
            )
        if self.max_multipole_order >= 1 and not self.dipole_conservation:
            raise ValueError(
                f"max_multipole_order={self.max_multipole_order} implies "
                "dipole_conservation=True"
            )
        if self.max_multipole_order < 0:
            raise ValueError(
                f"max_multipole_order must be >= 0, got {self.max_multipole_order}"
            )

    @property
    def conserved_multipoles(self) -> list[MultipoleCharge]:
        """List of all conserved multipole charges."""
        return [
            MultipoleCharge(order=n, spatial_dim=self.spatial_dim)
            for n in range(self.max_multipole_order + 1)
        ]

    @property
    def total_multipole_charges(self) -> int:
        """Total number of conserved multipole charge components.

        Sum_{n=0}^{N} C(n + d - 1, n) = C(N + d, d)

        This is a key result: the total grows as a polynomial in N
        (the highest multipole order), much faster than O(1).
        """
        return comb(self.max_multipole_order + self.spatial_dim,
                     self.spatial_dim)

    @property
    def total_conserved_charges(self) -> int:
        """Total conserved charges including momentum and energy."""
        n = self.total_multipole_charges
        if self.momentum_conservation:
            n += self.spatial_dim
        if self.energy_conservation:
            n += 1
        return n

    @property
    def dp_commutator_nontrivial(self) -> bool:
        """Whether [D, P] = iQ is active (finite charge density)."""
        return self.dipole_conservation and self.momentum_conservation

    @property
    def description(self) -> str:
        """Human-readable symmetry description."""
        parts = []
        if self.charge_conservation:
            parts.append("charge")
        if self.dipole_conservation:
            parts.append("dipole")
        if self.max_multipole_order >= 2:
            parts.append(f"up to {self.max_multipole_order}-pole")
        if self.momentum_conservation:
            parts.append("momentum")
        if self.energy_conservation:
            parts.append("energy")
        return f"Conservation: {', '.join(parts)} in {self.spatial_dim}D"


def classify_symmetry(
    max_multipole: int = 1,
    spatial_dim: int = 3,
    has_momentum: bool = True,
    has_energy: bool = True,
    is_isotropic: bool = True,
    has_pt: bool = True,
) -> FractonSymmetry:
    """Classify the symmetry structure of a fracton system.

    Args:
        max_multipole: Highest conserved multipole order
            0 = standard charge conservation only
            1 = charge + dipole (minimal fracton)
            2 = charge + dipole + quadrupole
            n = up to n-th multipole
        spatial_dim: Spatial dimension
        has_momentum: Whether momentum is conserved
        has_energy: Whether energy is conserved
        is_isotropic: Whether the system is isotropic
        has_pt: Whether PT symmetry holds

    Returns:
        FractonSymmetry with the classified structure.
    """
    return FractonSymmetry(
        charge_conservation=True,
        dipole_conservation=(max_multipole >= 1),
        max_multipole_order=max_multipole,
        spatial_dim=spatial_dim,
        momentum_conservation=has_momentum,
        energy_conservation=has_energy,
        has_pt_symmetry=has_pt,
        is_isotropic=is_isotropic,
    )


# ═══════════════════════════════════════════════════════════════════
# Transport coefficients
# ═══════════════════════════════════════════════════════════════════

@dataclass
class FractonTransportCoefficients:
    """Transport coefficients for fracton SK-EFT at leading dissipative order.

    Following Glorioso-Huang-Lucas (JHEP 2023), the transport tensor
    s_{ibjc} carries spatial (i,j) and vielbein (b,c) indices. For
    isotropic PT-symmetric systems, this decomposes into:

    Dissipative (4 coefficients, all >= 0 from positivity):
        s1, s2: Viscosity-type dissipation from E_{a,ib} E_{a,jc}
        t1, t2: Dipole dissipation from DeltaU_{a,ib} DeltaU_{a,jc}

    Non-dissipative / Hall-like (2 coefficients, sign unconstrained):
        d1, d2: From cross-terms L_beta e_{ib} DeltaU_{a,jc}

    Thermodynamic (4 parameters):
        b: Inverse temperature (from equilibrium pressure)
        a1, a2, a3: Equation-of-state parameters

    Note: No simple counting formula analogous to count(N) = floor((N+1)/2) + 1
    exists because the transport tensor carries two types of indices whose
    independent structures depend on symmetries (Glorioso-Huang-Lucas).

    Attributes:
        s1: First viscosity-type dissipative coefficient (>= 0)
        s2: Second viscosity-type dissipative coefficient (>= 0)
        t1: First dipole dissipative coefficient (>= 0)
        t2: Second dipole dissipative coefficient (>= 0)
        d1: First Hall-like coefficient (sign unconstrained)
        d2: Second Hall-like coefficient (sign unconstrained)
        b: Equilibrium inverse temperature
        a1: First equation-of-state parameter
        a2: Second equation-of-state parameter
        a3: Third equation-of-state parameter
        symmetry: The underlying fracton symmetry structure
    """
    s1: float  # viscosity dissipation 1
    s2: float  # viscosity dissipation 2
    t1: float  # dipole dissipation 1
    t2: float  # dipole dissipation 2
    d1: float  # Hall-like 1
    d2: float  # Hall-like 2
    b: float   # inverse temperature
    a1: float  # EOS param 1
    a2: float  # EOS param 2
    a3: float  # EOS param 3
    symmetry: FractonSymmetry = field(
        default_factory=lambda: classify_symmetry(max_multipole=1)
    )

    def __post_init__(self):
        if self.s1 < 0:
            raise ValueError(f"s1 must be >= 0 (positivity), got {self.s1}")
        if self.s2 < 0:
            raise ValueError(f"s2 must be >= 0 (positivity), got {self.s2}")
        if self.t1 < 0:
            raise ValueError(f"t1 must be >= 0 (positivity), got {self.t1}")
        if self.t2 < 0:
            raise ValueError(f"t2 must be >= 0 (positivity), got {self.t2}")
        if self.b <= 0:
            raise ValueError(f"b (inverse temperature) must be > 0, got {self.b}")

    @property
    def n_dissipative(self) -> int:
        """Number of dissipative transport coefficients."""
        return 4

    @property
    def n_hall(self) -> int:
        """Number of Hall-like (non-dissipative) transport coefficients."""
        return 2

    @property
    def n_thermodynamic(self) -> int:
        """Number of thermodynamic equation-of-state parameters."""
        return 4

    @property
    def n_total(self) -> int:
        """Total number of independent transport parameters at leading order."""
        return self.n_dissipative + self.n_hall + self.n_thermodynamic

    @property
    def total_dissipation(self) -> float:
        """Sum of all dissipative coefficients."""
        return self.s1 + self.s2 + self.t1 + self.t2


def compute_transport_coefficients(
    symmetry: FractonSymmetry,
    s1: float = 1.0,
    s2: float = 1.0,
    t1: float = 1.0,
    t2: float = 1.0,
    d1: float = 0.0,
    d2: float = 0.0,
    temperature: float = 1.0,
    a1: float = 1.0,
    a2: float = 0.0,
    a3: float = 0.0,
) -> FractonTransportCoefficients:
    """Construct fracton transport coefficients with given symmetry.

    The Glorioso-Huang-Lucas classification gives 4 dissipative + 2 Hall
    + 4 thermodynamic coefficients for isotropic PT-symmetric systems.

    Args:
        symmetry: The fracton symmetry structure
        s1, s2: Viscosity-type dissipation (must be >= 0)
        t1, t2: Dipole dissipation (must be >= 0)
        d1, d2: Hall-like coefficients (sign unconstrained)
        temperature: Temperature (used to set inverse temperature b)
        a1, a2, a3: Equation-of-state parameters

    Returns:
        FractonTransportCoefficients
    """
    return FractonTransportCoefficients(
        s1=s1, s2=s2, t1=t1, t2=t2,
        d1=d1, d2=d2,
        b=1.0 / temperature,
        a1=a1, a2=a2, a3=a3,
        symmetry=symmetry,
    )


# ═══════════════════════════════════════════════════════════════════
# SK effective action
# ═══════════════════════════════════════════════════════════════════

@dataclass
class FractonSKAction:
    """The Schwinger-Keldysh effective action for fracton hydrodynamics.

    The SK doubled-field structure introduces:
        X^i_s: coordinate fields nonlinearly realizing translations
        phi^s_i: vector fields for dipole shifts (phi_i -> phi_i + c_i)
        phi^s: scalar field for charge conservation
            transforming as phi -> phi + a - c_i X^i under dipole shifts

    The transformation phi -> phi + a - c_i X^i encodes [D, P] = iQ.

    The r-a basis decomposes into:
        chi_r = (chi_1 + chi_2)/2  (average / classical)
        chi_a = chi_1 - chi_2       (difference / noise)

    The complete Lagrangian at leading dissipative order:
        L = L_eq + L^(1) + L_bar^(1) + L^(2)

    where:
        L_eq: equilibrium (pressure, charge density, etc.)
        L^(2): noise/fluctuation (proportional to s, t coefficients)
        L^(1): dissipation (fixed by dynamical KMS from L^(2))
        L_bar^(1): Hall-like, non-dissipative (d coefficients)

    Attributes:
        coefficients: The transport coefficient set
        has_equilibrium: Whether the equilibrium part is included
        has_dissipation: Whether dissipative terms are included
        has_noise: Whether noise/fluctuation terms are included
        has_hall: Whether Hall-like terms are included
    """
    coefficients: FractonTransportCoefficients
    has_equilibrium: bool = True
    has_dissipation: bool = True
    has_noise: bool = True
    has_hall: bool = True

    @property
    def symmetry(self) -> FractonSymmetry:
        return self.coefficients.symmetry

    @property
    def field_content(self) -> dict[str, str]:
        """Description of the dynamical fields in the SK-EFT."""
        d = self.symmetry.spatial_dim
        return {
            "X_r^i": f"Coordinate fields ({d} components, classical)",
            "X_a^i": f"Coordinate fields ({d} components, noise)",
            "phi_r_i": f"Dipole vector fields ({d} components, classical)",
            "phi_a_i": f"Dipole vector fields ({d} components, noise)",
            "phi_r": "Charge scalar field (classical)",
            "phi_a": "Charge scalar field (noise)",
        }

    @property
    def n_dynamical_fields(self) -> int:
        """Total number of dynamical field components (SK doubled)."""
        d = self.symmetry.spatial_dim
        # X^i: d, phi_i: d, phi: 1, each doubled for SK
        return 2 * (d + d + 1)

    def lagrangian_noise(
        self,
        E_a: np.ndarray,
        DeltaU_a: np.ndarray,
    ) -> float:
        """Evaluate the noise part of the Lagrangian: L^(2).

        NOTE: Only L^(2) (noise) is implemented. L_eq, L^(1), L_bar^(1)
        are not yet implemented. This method is not called in the live path.

        -i beta_0 L^(2) = s_{ibjc} E_{a,ib} E_{a,jc}
                         + t_{ibjc} DeltaU_{a,ib} DeltaU_{a,jc}

        For isotropic systems, the tensor contractions reduce to:
        -i beta_0 L^(2) = s1 * |E_a|^2 + s2 * (Tr E_a)^2
                         + t1 * |DeltaU_a|^2 + t2 * (Tr DeltaU_a)^2

        Args:
            E_a: The noise-sector strain field (flattened).
            DeltaU_a: The noise-sector combined field (flattened).

        Returns:
            The noise Lagrangian density value (scalar).
        """
        c = self.coefficients
        E2 = float(np.sum(E_a**2))
        DU2 = float(np.sum(DeltaU_a**2))
        TrE = float(np.sum(E_a))
        TrDU = float(np.sum(DeltaU_a))

        return -1j * c.b * (c.s1 * E2 + c.s2 * TrE**2
                            + c.t1 * DU2 + c.t2 * TrDU**2)


# ═══════════════════════════════════════════════════════════════════
# Dispersion relation
# ═══════════════════════════════════════════════════════════════════

@dataclass
class FractonDispersionRelation:
    """Dispersion relation for fracton hydrodynamics.

    Standard hydro: omega = +/- c_s k - i Gamma k^2 (linear sound)
    Fracton hydro:  omega = +/- c_2 k^2 - i Gamma_4 k^4 (quadratic sound)

    The quadratic dispersion follows from the [D, P] = iQ commutator
    which forces the momentum susceptibility chi ~ n^2/k^2 to diverge.
    Combined with the charge compressibility, this gives:
        omega^2 = (a / chi) k^4 = a_eff k^4

    With energy conservation, the universality class changes:
    subdiffusive k^4 decay becomes diffusive k^2 decay for the
    energy mode, but the sound modes retain their quadratic character.

    Attributes:
        c2: Quadratic sound speed coefficient (omega = c2 * k^2)
        gamma4: Subdiffusive damping coefficient (Gamma_4 * k^4)
        multipole_order: n for n-pole conservation (1 = dipole)
        spatial_dim: Spatial dimension d
    """
    c2: float      # quadratic sound speed: omega_sound = c2 * k^2
    gamma4: float  # subdiffusive damping: Im(omega) = -gamma4 * k^4
    multipole_order: int = 1
    spatial_dim: int = 3

    @property
    def dispersion_power(self) -> int:
        """Power of k in the dispersion relation: omega ~ k^{n+1}."""
        return self.multipole_order + 1

    @property
    def damping_power(self) -> int:
        """Power of k in the damping: Im(omega) ~ k^{2(n+1)}."""
        return 2 * (self.multipole_order + 1)

    def omega(self, k: float | np.ndarray) -> complex | np.ndarray:
        """Compute the complex frequency for given wavenumber.

        omega = c2 * k^{n+1} - i * gamma4 * k^{2(n+1)}

        (positive branch only)

        Args:
            k: Wavenumber (or array of wavenumbers)

        Returns:
            Complex frequency omega(k)
        """
        n = self.multipole_order
        k_arr = np.asarray(k, dtype=float)
        real_part = self.c2 * np.abs(k_arr)**(n + 1)
        imag_part = -self.gamma4 * np.abs(k_arr)**(2 * (n + 1))
        return real_part + 1j * imag_part

    def relaxation_timescale(self, wavelength: float) -> float:
        """Characteristic relaxation time at a given wavelength.

        tau = 1 / (gamma4 * k^{2(n+1)}) where k = 2pi/lambda

        This scales as lambda^{2(n+1)}, giving anomalously slow
        relaxation compared to standard diffusive tau ~ lambda^2.

        Args:
            wavelength: Spatial wavelength lambda

        Returns:
            Relaxation timescale tau
        """
        k = 2 * np.pi / wavelength
        n = self.multipole_order
        if self.gamma4 == 0:
            return float('inf')
        return 1.0 / (self.gamma4 * k**(2 * (n + 1)))


def fracton_dispersion(
    coeffs: FractonTransportCoefficients,
    charge_density: float = 1.0,
) -> FractonDispersionRelation:
    """Compute the fracton dispersion relation from transport coefficients.

    The quadratic sound speed follows from:
        omega^2 = (a1 / chi_eff) * k^4

    where chi_eff ~ charge_density^2 / k^2 is the momentum susceptibility
    at finite charge density (from [D, P] = iQ), giving:
        omega = sqrt(a1) / charge_density * k^2

    The damping rate involves both s and t coefficients:
        Gamma_4 ~ (s1 + t1) / charge_density^2

    Args:
        coeffs: Fracton transport coefficients
        charge_density: Background charge density n_0

    Returns:
        FractonDispersionRelation with computed coefficients
    """
    n = coeffs.symmetry.max_multipole_order

    # Quadratic sound speed from EOS + momentum susceptibility
    # chi_eff ~ n_0^2 (momentum susceptibility at finite density)
    c2 = np.sqrt(abs(coeffs.a1)) / max(charge_density, 1e-30)

    # Subdiffusive damping from viscosity + dipole dissipation
    gamma4 = (coeffs.s1 + coeffs.t1) / max(charge_density**2, 1e-60)

    return FractonDispersionRelation(
        c2=c2,
        gamma4=gamma4,
        multipole_order=n,
        spatial_dim=coeffs.symmetry.spatial_dim,
    )


# ═══════════════════════════════════════════════════════════════════
# SK axiom verification
# ═══════════════════════════════════════════════════════════════════

@dataclass
class FractonSKAxiomCheck:
    """Results of checking the three SK axioms for the fracton SK-EFT.

    The three axioms (identical for standard and fracton SK-EFT):

    (i)   Normalization: S[chi, chi] = 0
          The action vanishes when the two copies are identical.

    (ii)  Positivity: Im S >= 0
          Ensures the path integral converges. Requires:
          s1, s2, t1, t2 >= 0 (all dissipative coefficients non-negative).

    (iii) Dynamical KMS: relates L^(1) to L^(2)
          The KMS transformation shifts chi_a -> chi_a + i beta L_beta chi_r,
          and KMS invariance of the action fixes the dissipative response
          L^(1) in terms of the noise L^(2). This ensures Onsager reciprocity
          and the fluctuation-dissipation relation.

    Attributes:
        normalization_satisfied: Whether axiom (i) holds
        positivity_satisfied: Whether axiom (ii) holds
        kms_satisfied: Whether axiom (iii) holds
        all_satisfied: Whether all three axioms hold
        positivity_violations: Which coefficients violate positivity (if any)
    """
    normalization_satisfied: bool
    positivity_satisfied: bool
    kms_satisfied: bool
    positivity_violations: list[str] = field(default_factory=list)

    @property
    def all_satisfied(self) -> bool:
        return (self.normalization_satisfied
                and self.positivity_satisfied
                and self.kms_satisfied)


def verify_sk_axioms(
    coeffs: FractonTransportCoefficients,
) -> FractonSKAxiomCheck:
    """Verify the three SK axioms for given transport coefficients.

    The verification checks:
    (i)   Normalization: structural (always true by construction of the SK-EFT)
    (ii)  Positivity: s1, s2, t1, t2 >= 0
    (iii) KMS: structural (L^(1) is constructed from L^(2) by KMS)

    For the fracton SK-EFT, all three axioms apply identically to
    standard SK-EFT. The fracton structure affects the CONTENT of the
    action (which monomials appear, how indices contract) but not
    the axiom structure itself.

    Args:
        coeffs: Transport coefficients to check

    Returns:
        FractonSKAxiomCheck with results
    """
    violations = []
    if coeffs.s1 < 0:
        violations.append(f"s1 = {coeffs.s1} < 0")
    if coeffs.s2 < 0:
        violations.append(f"s2 = {coeffs.s2} < 0")
    if coeffs.t1 < 0:
        violations.append(f"t1 = {coeffs.t1} < 0")
    if coeffs.t2 < 0:
        violations.append(f"t2 = {coeffs.t2} < 0")

    return FractonSKAxiomCheck(
        normalization_satisfied=True,   # By SK-EFT construction
        positivity_satisfied=(len(violations) == 0),
        kms_satisfied=True,             # L^(1) derived from L^(2) by KMS
        positivity_violations=violations,
    )


# ═══════════════════════════════════════════════════════════════════
# Higher-multipole generalizations
# ═══════════════════════════════════════════════════════════════════

def upper_critical_dimension(multipole_order: int) -> int:
    """Compute the upper critical dimension for n-pole conservation.

    From Guo-Glorioso-Lucas (PRL 2022):
        d_c = 2(1 + n) for n even
        d_c = 2n       for n odd

    Above d_c, mean-field theory (Gaussian fluctuations) is exact.
    Below d_c, fluctuations are strong and modify scaling.

    The fact that d_c -> infinity as n -> infinity means that for
    high multipole conservation, fluctuations are always strong in
    any fixed physical dimension. This is a key structural difference
    from standard hydrodynamics where d_c = 2.

    Args:
        multipole_order: The multipole conservation order n
            n=0: standard charge conservation (d_c = 2)
            n=1: dipole conservation (d_c = 2)
            n=2: quadrupole conservation (d_c = 6)

    Returns:
        Upper critical dimension d_c

    Raises:
        ValueError: if multipole_order < 0
    """
    if multipole_order < 0:
        raise ValueError(
            f"Multipole order must be >= 0, got {multipole_order}"
        )

    n = multipole_order
    if n == 0:
        return 2  # standard diffusion
    if n % 2 == 0:
        return 2 * (1 + n)
    else:
        return 2 * n
