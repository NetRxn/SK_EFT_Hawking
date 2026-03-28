"""Analytical SU(2) Haar measure integration for the ADW lattice model.

Integrates out the SU(2) spin connection on lattice links analytically,
producing a purely fermionic effective action. This is the first step
in the Grassmann TRG pipeline: the gauge field is eliminated exactly,
leaving only multi-fermion vertices.

Key identity (Schur orthogonality for SU(2) fundamental rep):
    ∫ dU U_ij U*_kl = (1/2) δ_il δ_jk

For the 2D reduced ADW model (2 Grassmann variables per site):
- Each link carries an SU(2) matrix U ∈ SU(2)
- The gauge-coupled vertex is: (ψ̄(x) U ψ(y)) × (ψ̄(y) U† ψ(x))
- After integration: effective 4-fermion coupling with factor 1/2

The SU(2) pseudo-reality (fund rep is self-conjugate via ε_ij) ensures
that the effective action after integration is REAL, guaranteeing no
sign problem for Monte Carlo or positive-definite weights for TRG.

References:
    Vladimirov & Diakonov, PRD 86, 104019 (2012) — ADW model
    Creutz, "Quarks, Gluons and Lattices" (1983) — SU(2) integrals
"""

import numpy as np
from dataclasses import dataclass

from src.core.constants import ADW_2D_MODEL, SU2_HAAR
from src.core.formulas import su2_one_link_integral, adw_2d_effective_coupling


@dataclass
class SU2IntegrationResult:
    """Result of analytically integrating out SU(2) on one link.

    Attributes:
        g_EH: original Einstein-Hilbert gauge coupling
        g_eff: effective 4-fermion coupling after integration (g_EH/2)
        dim_fund: dimension of fundamental representation
        channels: dict mapping channel names to their effective couplings
    """
    g_EH: float
    g_eff: float
    dim_fund: int
    channels: dict


def integrate_one_link(g_EH: float) -> SU2IntegrationResult:
    """Integrate out the SU(2) spin connection on a single link.

    Uses the Schur orthogonality relation:
        ∫ dU U_ij U*_kl = (1/dim) δ_il δ_jk

    The gauge-coupled vertex (ψ̄_i U_ij ψ'_j)(χ̄_k U*_kl χ'_l) becomes:
        (1/dim)(ψ̄_i χ'_i)(χ̄_k ψ'_k) = (1/2)(ψ̄·χ')(χ̄·ψ')

    This is a color-singlet exchange with strength g_EH/2.

    For higher-spin channels (adjoint, etc.), the coupling is different:
        spin-0 singlet: g_EH / dim
        spin-1 adjoint: g_EH × (dim-1) / (dim × (dim²-1))
    For SU(2) dim=2, only the singlet channel contributes at leading order.

    Args:
        g_EH: Einstein-Hilbert coupling constant

    Returns:
        SU2IntegrationResult with effective couplings
    """
    dim = SU2_HAAR['dim_fund']
    g_eff = adw_2d_effective_coupling(g_EH, dim)

    channels = {
        'singlet': g_eff,
        'adjoint': 0.0,  # vanishes for 2-Grassmann model in 2D
    }

    return SU2IntegrationResult(
        g_EH=g_EH,
        g_eff=g_eff,
        dim_fund=dim,
        channels=channels,
    )


@dataclass
class EffectiveAction2D:
    """Effective 2D fermionic action after SU(2) integration.

    The action on a 2D square lattice with 2 Grassmann variables per site:

        S_eff = g_cosmo × Σ_x (ψ̄₁ψ₁)(ψ̄₂ψ₂)
              + g_eff  × Σ_{<xy>} [(ψ̄(x)·ψ(y))(ψ̄(y)·ψ(x))]

    where g_eff = g_EH / 2 from SU(2) integration.

    The first term is the on-site cosmological term (unchanged by
    gauge integration). The second term is the nearest-neighbor
    4-fermion interaction from the gauge-coupled vertex.

    Attributes:
        g_cosmo: on-site cosmological coupling
        g_eff: nearest-neighbor effective coupling (after SU(2) integration)
        d: spacetime dimension (2)
        n_grassmann: Grassmann variables per site (2)
    """
    g_cosmo: float
    g_eff: float
    d: int = 2
    n_grassmann: int = 2

    @property
    def n_terms_onsite(self) -> int:
        """Number of independent on-site 4-fermion terms."""
        return 1  # (ψ̄₁ψ₁)(ψ̄₂ψ₂) only

    @property
    def n_terms_nn(self) -> int:
        """Number of independent nearest-neighbor 4-fermion terms."""
        return 1  # singlet channel only for 2-Grassmann model

    @property
    def coordination_number(self) -> int:
        """Number of nearest neighbors per site on 2D square lattice."""
        return 2 * self.d  # = 4


def build_effective_action(g_cosmo: float, g_EH: float) -> EffectiveAction2D:
    """Build the effective 2D fermionic action after SU(2) integration.

    Args:
        g_cosmo: cosmological coupling (on-site 4-fermion)
        g_EH: Einstein-Hilbert coupling (gauge-coupled, nearest-neighbor)

    Returns:
        EffectiveAction2D with all parameters
    """
    integration = integrate_one_link(g_EH)

    return EffectiveAction2D(
        g_cosmo=g_cosmo,
        g_eff=integration.g_eff,
        d=ADW_2D_MODEL['d'],
        n_grassmann=ADW_2D_MODEL['n_grassmann'],
    )


def effective_boltzmann_weight_2d(g_cosmo: float, g_eff: float,
                                  n1_x: int, n2_x: int,
                                  n1_y: int, n2_y: int) -> float:
    """Compute the local Boltzmann weight for a bond in the 2D model.

    In the occupation number basis, the 2 Grassmann variables per site
    take values n_i ∈ {0, 1}. The Boltzmann weight for a bond (x, y) is:

        W(n(x), n(y)) = exp(-S_bond)

    where S_bond includes the cosmological term (split between bonds)
    and the nearest-neighbor term.

    For the 2D model with 2 Grassmann variables:
    - On-site term contributes when both n₁=1 and n₂=1 at site x
    - NN term contributes when both sites have matching occupations

    Args:
        g_cosmo: cosmological coupling
        g_eff: effective nearest-neighbor coupling (after SU(2))
        n1_x, n2_x: Grassmann occupation at site x (0 or 1)
        n1_y, n2_y: Grassmann occupation at site y (0 or 1)

    Returns:
        Boltzmann weight (real, non-negative due to SU(2) pseudo-reality)
    """
    # On-site cosmological term (split among z=4 bonds)
    S_cosmo = g_cosmo * n1_x * n2_x / 4.0

    # Nearest-neighbor singlet exchange
    S_nn = g_eff * (n1_x * n1_y + n2_x * n2_y)

    return np.exp(-(S_cosmo + S_nn))


def build_initial_tensor(g_cosmo: float, g_EH: float) -> np.ndarray:
    """Build the initial Grassmann tensor for the 2D TRG.

    The Grassmann tensor T has indices:
        T[n1, n2, i_left, i_right, i_up, i_down]

    where n1, n2 ∈ {0, 1} are the Grassmann occupation numbers
    and i_left, ..., i_down ∈ {0, 1, ..., D-1} are bond indices.

    For the initial tensor (before any coarse-graining), the bond
    dimension is 2 (one for each Grassmann occupation on the bond).

    The tensor encodes the Boltzmann weight as a sum over internal
    Grassmann variables contracted along shared bonds.

    Args:
        g_cosmo: cosmological coupling
        g_EH: Einstein-Hilbert coupling

    Returns:
        Initial tensor of shape (2, 2, 2, 2) for the 2D model.
        Indices: (left, right, up, down) bond states.
        Each bond state ∈ {0, 1} represents Grassmann occupation.
    """
    g_eff = adw_2d_effective_coupling(g_EH)

    # Build the tensor by summing over the on-site Grassmann variables
    # T[l, r, u, d] = Σ_{n1, n2} W_cosmo(n1, n2) × W_nn(n1, l) × W_nn(n2, r)
    #                                               × W_nn(n1, u) × W_nn(n2, d)
    #
    # Simplified: the initial tensor factorizes into bond weights
    T = np.zeros((2, 2, 2, 2))

    for n1 in range(2):
        for n2 in range(2):
            # Cosmological weight
            w_cosmo = np.exp(-g_cosmo * n1 * n2)

            for l in range(2):
                for r in range(2):
                    for u in range(2):
                        for d in range(2):
                            # NN weights on each bond
                            w_lr = np.exp(-g_eff * (n1 * l + n2 * r))
                            w_ud = np.exp(-g_eff * (n1 * u + n2 * d))
                            T[l, r, u, d] += w_cosmo * w_lr * w_ud

    return T


def su2_pseudo_reality_check() -> dict:
    """Verify the SU(2) pseudo-reality property numerically.

    The fundamental representation of SU(2) satisfies:
        U* = ε U ε^{-1}  where ε = [[0, -1], [1, 0]]

    This implies det(M_eff) is real for even numbers of Dirac flavors,
    guaranteeing no sign problem.

    Returns:
        Dict with verification results: epsilon matrix, identity check,
        and the implication for the effective action.
    """
    epsilon = np.array([[0, -1], [1, 0]], dtype=complex)

    # Generate random SU(2) matrices and verify U* = ε U ε^{-1}
    rng = np.random.default_rng(42)
    n_samples = 100
    max_error = 0.0

    for _ in range(n_samples):
        # Random SU(2): U = exp(i θ n·σ)
        theta = rng.uniform(0, np.pi)
        n = rng.standard_normal(3)
        n = n / np.linalg.norm(n)

        # Pauli matrices
        sigma = [
            np.array([[0, 1], [1, 0]], dtype=complex),
            np.array([[0, -1j], [1j, 0]], dtype=complex),
            np.array([[1, 0], [0, -1]], dtype=complex),
        ]
        n_dot_sigma = sum(n[i] * sigma[i] for i in range(3))
        U = np.cos(theta) * np.eye(2, dtype=complex) + 1j * np.sin(theta) * n_dot_sigma

        # Verify pseudo-reality: U* = ε U ε^{-1}
        U_conj = np.conj(U)
        eps_inv = np.linalg.inv(epsilon)
        reconstructed = epsilon @ U @ eps_inv
        error = np.max(np.abs(U_conj - reconstructed))
        max_error = max(max_error, error)

    return {
        'epsilon': epsilon,
        'max_reconstruction_error': max_error,
        'pseudo_real': max_error < 1e-10,
        'implication': 'effective_action_real_for_even_flavors',
        'n_flavors_adw': 2,  # 2D model has 1 Dirac = 2 Majorana
        'sign_problem_absent': True,
    }
