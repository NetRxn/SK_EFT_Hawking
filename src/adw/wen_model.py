"""Wen's Emergent QED from String-Net Condensation.

Implements the Levin-Wen rotor model on a 3D cubic lattice that produces
emergent QED_{3+1} in the deconfined (Coulomb) phase: N_f=4 Dirac fermions
coupled to an emergent U(1) gauge field.

The Herbut velocity equalization mechanism (Roy-Juricic-Herbut 2016) then
drives the bare lattice anisotropy toward emergent Lorentz invariance in
the deep IR.

Key physics:
    - Rotor model: H = U sum n^2 - t sum cos(Delta theta) + g sum (div n)^2
    - Coulomb phase: string-net condensation -> emergent QED
    - N_f = 4 four-component Dirac fermions (Nielsen-Ninomiya doubling)
    - Non-chiral: left and right chiralities couple identically
    - RG flow: v_F, v_B, c -> terminal velocity v_t

Lean: ADWMechanism.lean (wen_model_nf, nielsen_ninomiya_doubling)
"""

from dataclasses import dataclass
import numpy as np


@dataclass
class WenRotorModel:
    """Levin-Wen rotor model on a 3D cubic lattice.

    H = U sum_{links} n^2 - t sum_{plaquettes} cos(Delta theta)
        + g sum_{vertices} (div n)^2

    Attributes:
        U: Rotor kinetic energy (link) [dimensionless on lattice]
        t: Plaquette coupling (magnetic energy) [dimensionless]
        g: Gauss law enforcement (charge conservation) [dimensionless]
        lattice_dim: Spatial dimension (3 for physical case)
    """
    U: float
    t: float
    g: float
    lattice_dim: int = 3

    @property
    def is_coulomb_phase(self) -> bool:
        """Whether parameters are in the Coulomb (deconfined) phase.

        The Coulomb phase requires t >> U (strong plaquette coupling).
        In 3+1D, the transition is at (t/U)_c ~ O(1).
        """
        return self.t > self.U

    @property
    def spacetime_dim(self) -> int:
        return self.lattice_dim + 1


@dataclass
class VelocityStructure:
    """Velocity structure of the emergent QED theory.

    Bare lattice anisotropy generically produces different velocities
    for fermions (v_F), gauge bosons (v_B), and the lattice speed of
    light (c). RG flow drives them to a common terminal velocity.

    Attributes:
        v_F: Fermi velocity [lattice units]
        v_B: Gauge boson velocity [lattice units]
        c_lattice: Lattice speed of light [lattice units]
    """
    v_F: float
    v_B: float
    c_lattice: float

    @property
    def lorentz_violation(self) -> float:
        """Measure of Lorentz violation: max deviation from common velocity."""
        v_mean = (self.v_F + self.v_B + self.c_lattice) / 3
        deviations = [abs(v - v_mean) / v_mean
                      for v in [self.v_F, self.v_B, self.c_lattice]]
        return max(deviations)


@dataclass
class EmergentQED:
    """Low-energy effective theory emerging from the Coulomb phase.

    L = -(1/4) F_{mu nu} F^{mu nu} + sum_{alpha=1}^{N_f} psi_bar gamma^mu D_mu psi

    Attributes:
        N_f: Number of four-component Dirac fermions (4 from cubic lattice)
        N_weyl: Number of Weyl species (2 * N_f = 8)
        gauge_group: The emergent gauge group (U(1))
        is_chiral: Whether the theory is chiral (False for lattice models)
        velocities: Bare velocity structure
    """
    N_f: int
    N_weyl: int
    gauge_group: str
    is_chiral: bool
    velocities: VelocityStructure

    @property
    def has_lorentz_invariance(self) -> bool:
        """Whether Lorentz invariance has been restored by RG flow."""
        return self.velocities.lorentz_violation < 0.01


def wen_coulomb_phase(lattice_dim: int = 3,
                      v_F: float = 0.8,
                      v_B: float = 1.0,
                      c_lattice: float = 1.0) -> EmergentQED:
    """Construct the emergent QED theory from Wen's Coulomb phase.

    On a d-dimensional cubic lattice, the Nielsen-Ninomiya theorem
    mandates 2^d Weyl fermion species at Brillouin zone corners.
    For d=3: 2^3 = 8 Weyl species = 4 four-component Dirac fermions.

    Lean: wen_model_nf, nielsen_ninomiya_doubling

    Args:
        lattice_dim: Spatial dimension (3 for physical case)
        v_F: Bare Fermi velocity
        v_B: Bare gauge boson velocity
        c_lattice: Lattice speed of light

    Returns:
        EmergentQED with N_f = 2^(d-1) Dirac fermions.
    """
    N_weyl = 2 ** lattice_dim    # Nielsen-Ninomiya: 2^d Weyl species
    N_f = N_weyl // 2            # Pair into Dirac fermions

    velocities = VelocityStructure(
        v_F=v_F, v_B=v_B, c_lattice=c_lattice
    )

    return EmergentQED(
        N_f=N_f,
        N_weyl=N_weyl,
        gauge_group="U(1)",
        is_chiral=False,  # Lattice models are non-chiral
        velocities=velocities,
    )


def herbut_terminal_velocity(v_F: float, v_B: float, c: float,
                              alpha: float = 0.01,
                              rg_steps: int = 100) -> VelocityStructure:
    """Simulate Herbut velocity equalization RG flow.

    In 3+1D, one-loop RG drives v_F, v_B, c toward a common terminal
    velocity v_t. The flow is non-universal (v_t depends on bare
    couplings) but convergence is guaranteed.

    Schematic beta functions (Roy-Juricic-Herbut JHEP 04, 018 (2016)):
        dv_F/dl ~ alpha * v_F * f(v_F/c, v_F/v_B)
        dv_B/dl ~ alpha * v_B * g(v_F/c, v_B/c)

    The key physics: both terms drive velocities toward equality.

    Lean: velocity_equalization_convergence

    Args:
        v_F: Initial Fermi velocity
        v_B: Initial gauge boson velocity
        c: Initial lattice speed of light
        alpha: Fine structure constant (controls flow rate)
        rg_steps: Number of RG steps to simulate

    Returns:
        VelocityStructure after RG flow.
    """
    vf, vb, vc = v_F, v_B, c
    dl = 0.1

    for _ in range(rg_steps):
        # Simplified RG flow: velocities attracted to mean
        v_mean = (vf + vb + vc) / 3

        # Fermion velocity: driven by gauge interaction
        dvf = alpha * (v_mean - vf) * dl
        # Boson velocity: driven by fermion loop
        dvb = alpha * (v_mean - vb) * dl * 0.5
        # Lattice speed: driven by both
        dvc = alpha * (v_mean - vc) * dl * 0.3

        vf += dvf
        vb += dvb
        vc += dvc

    return VelocityStructure(v_F=vf, v_B=vb, c_lattice=vc)


def nielsen_ninomiya_weyl_count(lattice_dim: int) -> int:
    """Number of Weyl fermion species from Nielsen-Ninomiya theorem.

    On a d-dimensional cubic lattice, there are 2^d Brillouin zone
    corners, each hosting one Weyl fermion. These pair into 2^(d-1)
    four-component Dirac fermions.

    Lean: nielsen_ninomiya_doubling

    Args:
        lattice_dim: Spatial dimension

    Returns:
        Number of Weyl species (2^d)
    """
    return 2 ** lattice_dim


def nielsen_ninomiya_dirac_count(lattice_dim: int) -> int:
    """Number of Dirac fermion species from Nielsen-Ninomiya theorem.

    Lean: wen_model_nf

    Args:
        lattice_dim: Spatial dimension

    Returns:
        Number of Dirac fermions (2^(d-1))
    """
    return 2 ** (lattice_dim - 1)
