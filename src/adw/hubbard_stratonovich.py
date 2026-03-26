"""Hubbard-Stratonovich Decomposition of the ADW 8-Fermion Interaction.

Implements the decomposition of the ADW cosmological term into a
quadratic fermion action coupled to the auxiliary tetrad field.

The ADW action:
    S_micro = (1/24) epsilon_{abcd} int Theta^a ^ Theta^b ^ Theta^c ^ Theta^d

where Theta^a = (i/2)[psi_bar gamma^a D_mu psi - D_mu psi_bar gamma^a psi] dx^mu
is bilinear in psi. The wedge product of four such 1-forms produces an
8-fermion interaction.

The HS decomposition introduces the auxiliary tetrad e^a_mu:
    exp(-G int (8-fermion)) -> int De exp(-S_Yukawa[e,psi] - S_pot[e])

After decomposition, the fermion action becomes the Dirac action in
curved spacetime:
    S_fermion = int d^4x det(e) psi_bar gamma^a e_a^mu partial_mu psi

No published paper has performed this decomposition explicitly for the
full 8-fermion interaction. We follow the closest approach (Maitiniyazi
et al. 2024) and the NJL/BCS structural analogy.

Lean: ADWMechanism.lean (hs_reduces_to_dirac, tetrad_components)
"""

from dataclasses import dataclass, field
import numpy as np


@dataclass
class ADWAction:
    """The ADW multi-fermion interaction.

    S_micro = (G/24) epsilon_{abcd} int Theta^a ^ Theta^b ^ Theta^c ^ Theta^d

    Attributes:
        G: Coupling constant [length^(6) in 4D, from dim analysis]
        spacetime_dim: Dimension of spacetime (4)
        fermion_mass_dim: Mass dimension of spinor field (0 in ADW)
        n_fermion_legs: Number of fermion legs in the interaction (8)
    """
    G: float
    spacetime_dim: int = 4
    fermion_mass_dim: float = 0.0
    n_fermion_legs: int = 8

    @property
    def n_derivatives(self) -> int:
        """Number of spacetime derivatives in the interaction.

        Each Theta^a carries one derivative; the wedge product of 4
        gives 4 derivatives contracted via epsilon^{mu nu rho sigma}.
        """
        return self.spacetime_dim

    @property
    def interaction_order(self) -> str:
        """Description of the interaction structure."""
        return f"{self.n_fermion_legs}-fermion with {self.n_derivatives} derivatives"


@dataclass
class TetradField:
    """The tetrad (vierbein) field e^a_mu.

    A 4x4 matrix mapping internal Lorentz indices (a) to spacetime
    indices (mu). The induced metric is g_{mu nu} = eta_{ab} e^a_mu e^b_nu.

    Attributes:
        components: 4x4 numpy array e^a_mu
        eta: Internal Minkowski metric (diag(-1,+1,+1,+1))
    """
    components: np.ndarray
    eta: np.ndarray = field(default_factory=lambda: np.diag([-1.0, 1.0, 1.0, 1.0]))

    def __post_init__(self):
        self.components = np.asarray(self.components, dtype=float)
        self.eta = np.asarray(self.eta, dtype=float)
        if self.components.shape != (4, 4):
            raise ValueError(f"Tetrad must be 4x4, got {self.components.shape}")

    @property
    def metric(self) -> np.ndarray:
        """Induced metric g_{mu nu} = eta_{ab} e^a_mu e^b_nu."""
        return self.components.T @ self.eta @ self.components

    @property
    def determinant(self) -> float:
        """det(e^a_mu)."""
        return float(np.linalg.det(self.components))

    @property
    def metric_determinant(self) -> float:
        """det(g_{mu nu}) = [det(e)]^2 * det(eta)."""
        return float(np.linalg.det(self.metric))

    @property
    def signature(self) -> tuple[int, int, int]:
        """Metric signature as (n_negative, n_zero, n_positive).

        Lorentzian = (1, 0, 3), Euclidean = (0, 0, 4), degenerate has n_zero > 0.
        """
        eigenvalues = np.linalg.eigvalsh(self.metric)
        n_neg = int(np.sum(eigenvalues < -1e-10))
        n_zero = int(np.sum(np.abs(eigenvalues) < 1e-10))
        n_pos = int(np.sum(eigenvalues > 1e-10))
        return (n_neg, n_zero, n_pos)

    @property
    def is_lorentzian(self) -> bool:
        """Whether the induced metric has Lorentzian signature (-,+,+,+)."""
        return self.signature == (1, 0, 3)

    @property
    def is_nondegenerate(self) -> bool:
        """Whether the tetrad is invertible (nonzero determinant)."""
        return abs(self.determinant) > 1e-10

    @property
    def magnitude(self) -> float:
        """Tetrad magnitude C = (|det(e)|)^(1/4).

        This parameterizes the overall scale of the tetrad.
        """
        return abs(self.determinant) ** 0.25

    @classmethod
    def flat_spacetime(cls, C: float = 1.0) -> "TetradField":
        """Construct flat-spacetime tetrad e^a_mu = C * delta^a_mu."""
        return cls(components=C * np.eye(4))

    @classmethod
    def zero(cls) -> "TetradField":
        """Construct the pre-geometric (zero) tetrad."""
        return cls(components=np.zeros((4, 4)))

    @classmethod
    def lorentz_rotated(cls, C: float, boost_rapidity: float = 0.0) -> "TetradField":
        """Construct a Lorentz-rotated tetrad (B-phase analog).

        e^a_mu = C * Lambda^a_b * delta^b_mu

        where Lambda is a Lorentz boost in the z-direction.
        """
        ch = np.cosh(boost_rapidity)
        sh = np.sinh(boost_rapidity)
        Lambda = np.array([
            [ch, 0, 0, sh],
            [0,  1, 0,  0],
            [0,  0, 1,  0],
            [sh, 0, 0, ch],
        ])
        return cls(components=C * Lambda)


@dataclass
class HSDecomposition:
    """Result of the Hubbard-Stratonovich decomposition.

    The 8-fermion interaction is decomposed into:
    S = S_Yukawa[e, psi] + S_pot[e]

    where S_Yukawa = int d^4x det(e) psi_bar gamma^a e_a^mu D_mu psi
    (the Dirac action in curved spacetime) and S_pot = int d^4x e^2 / (2G)
    (the tree-level tetrad potential).

    Attributes:
        original_action: The ADW action being decomposed
        n_hs_steps: Number of HS transformations needed (2 for 8-fermion)
        yukawa_structure: Description of the fermion-tetrad coupling
        tree_level_potential: Description of V_tree(e)
        is_fermion_quadratic: Whether fermions appear quadratically after HS
    """
    original_action: ADWAction
    n_hs_steps: int
    yukawa_structure: str
    tree_level_potential: str
    is_fermion_quadratic: bool


def adw_cosmological_term(G: float) -> ADWAction:
    """Construct the ADW cosmological term.

    S = (G/24) epsilon_{abcd} int Theta^a ^ Theta^b ^ Theta^c ^ Theta^d

    Lean: adw_action_structure

    Args:
        G: Coupling constant

    Returns:
        ADWAction describing the 8-fermion interaction.
    """
    return ADWAction(G=G)


def hubbard_stratonovich_decompose(action: ADWAction) -> HSDecomposition:
    """Perform the Hubbard-Stratonovich decomposition.

    The 8-fermion interaction requires two successive HS transformations:
    Step 1: 8-fermion -> 4-fermion + auxiliary tetrad e^a_mu
    Step 2: remaining 4-fermion terms (if any) -> additional auxiliaries

    After decomposition, the fermion action is quadratic — precisely
    the Dirac action in curved spacetime.

    Lean: hs_reduces_to_dirac

    Args:
        action: The ADW action to decompose.

    Returns:
        HSDecomposition with the resulting structure.
    """
    n_steps = 2 if action.n_fermion_legs == 8 else 1

    return HSDecomposition(
        original_action=action,
        n_hs_steps=n_steps,
        yukawa_structure=(
            "S_Yukawa = int d^4x det(e) psi_bar gamma^a e_a^mu D_mu psi "
            "(Dirac action in curved spacetime)"
        ),
        tree_level_potential=(
            f"V_tree(e) = Tr(e^T eta e) / (2G) = C^2 / (2 * {action.G:.4e}) "
            "where C = |det(e)|^(1/4)"
        ),
        is_fermion_quadratic=True,
    )


def fermion_effective_action(tetrad: TetradField, N_f: int, Lambda: float,
                              G: float) -> dict:
    """Compute the effective action after integrating out fermions.

    S_eff[e] = S_pot(e) - N_f * Tr ln[gamma^a e_a^mu D_mu]

    The one-loop fermion determinant generates (Sakharov induced gravity):
    - Einstein-Hilbert term ~ M_P^2 R (from log divergence)
    - Cosmological constant ~ Lambda^4 (from quartic divergence)
    - Higher-curvature corrections ~ R^2 (from finite parts)

    For the gap equation analysis, we work with the flat-space effective
    potential V_eff(C) where C parameterizes the tetrad magnitude.

    Lean: fermion_determinant_structure

    Args:
        tetrad: The background tetrad field.
        N_f: Number of Dirac fermion species.
        Lambda: UV cutoff.
        G: ADW coupling constant.

    Returns:
        Dictionary with V_tree, V_1loop, V_eff, and their derivatives.
    """
    C = tetrad.magnitude

    # Tree-level potential: V_tree = C^2 / (2G)
    V_tree = C**2 / (2.0 * G) if G > 0 else 0.0

    # One-loop Coleman-Weinberg potential from fermion determinant
    # V_1loop = -(N_f / 16 pi^2) [Lambda^2 C^2 - C^4 ln(Lambda^2/C^2 + 1)]
    # For C << Lambda: V_1loop ~ -(N_f / 16 pi^2) Lambda^2 C^2
    #                            + (N_f / 16 pi^2) C^4 ln(C^2/Lambda^2)
    prefactor = N_f / (16.0 * np.pi**2)

    if C > 1e-15:
        ratio_sq = Lambda**2 / C**2
        V_1loop = -prefactor * (Lambda**2 * C**2 - C**4 * np.log(ratio_sq + 1.0))
    else:
        V_1loop = 0.0

    V_eff = V_tree + V_1loop

    return {
        'C': C,
        'V_tree': V_tree,
        'V_1loop': V_1loop,
        'V_eff': V_eff,
        'N_f': N_f,
        'Lambda': Lambda,
        'G': G,
    }


def composite_tetrad_operator(psi: str = "Psi") -> str:
    """Return the composite tetrad operator expression.

    E^a_mu = (1/2)(psi^dag gamma^a partial_mu psi
                   - partial_mu psi^dag gamma^a psi)

    This is bilinear in the fermion field with one derivative.
    """
    return (
        f"E^a_mu = (1/2)({psi}^dag gamma^a partial_mu {psi} "
        f"- partial_mu {psi}^dag gamma^a {psi})"
    )
