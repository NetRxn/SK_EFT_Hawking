"""ADW auxiliary-field descriptors and adopted scalar evaluation. The numerical split below is not a derivation of the full regulated8fermion HS action, channel normalization, matrix state or gravity. Those original objectives remain BUILD; no universal primary-literature absence is asserted. The retained Maitiniyazi et al.2024/NJL analogy is context, not a derived channel.

Existing attribution does not certify this evaluation or physical derivation:
Lean: ADWMechanism.lean (hs_reduces_to_dirac, tetrad_components)"""

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


def fermion_effective_action(tetrad: TetradField,N_f: int,Lambda: float,G: float,*,
                              rtol=2.0**-40,max_work=200000,max_bits=100000) -> dict:
    """Numerical split of the adopted scalar ansatz, not an HS derivation.

    Canonical total is evaluated directly; exact tree is subtracted from
    rational total bounds to enclose the loop column. Rounded columns need
    not reconstruct a tiny total accurately; their discrepancy is recorded.
    The matrix-to-scalar reduction/physical determinant remain BUILD.
    Existing fermion_determinant_structure proves neither this evaluation
    nor a microscopic action. No derivatives are returned by this API.

    Lean: fermion_determinant_structure
    """
    from itertools import permutations
    from fractions import Fraction
    from src.core.formulas import (_adw_exact,_ADWWork,_adw_pi_bounds,
        _adw_parameter_ratio,_adw_energy_bounds,_adw_binary_midpoint,ADWScalarUnresolved)
    inputs=tuple(_adw_exact(x,k,positive=True) for x,k in ((G,'G'),(Lambda,'Lambda'),(N_f,'N_f')))
    tolerance=_adw_exact(rtol,'rtol',positive=True)
    work=_ADWWork(max_work,max_bits)
    for x in inputs:work.take(x)
    components=np.asarray(tetrad.components)
    if components.shape!=(4,4):raise ValueError('actual4x4 tetrad required')
    matrix=tuple(tuple(_adw_exact(components[i,j],'tetrad component') for j in range(4)) for i in range(4))
    # Exact finite binary-rational determinant disambiguates genuine singular
    # matrices from a nonzero determinant lost by the legacy floating property.
    for row in matrix:
        for value in row:work.take(value)
    determinant=Fraction(0)
    for p in permutations(range(4)):
        term=Fraction(1)
        for i in range(4):term*=matrix[i][p[i]];work.take(term)
        inversions=sum(p[i]>p[j] for i in range(4) for j in range(i+1,4))
        determinant+=(-1 if inversions%2 else 1)*term;work.take(determinant)
    if determinant==0:
        c=Fraction(0)
    else:
        try:
            c=_adw_exact(tetrad.magnitude,'represented magnitude')
        except (ValueError,OverflowError,FloatingPointError) as exc:
            raise ADWScalarUnresolved('matrix scalar-coordinate representation unresolved') from exc
        if c<0:raise ValueError('nonnegative represented magnitude required')
    # A legacy nonzero determinant collapsing to0 is numerical refusal; an
    # exact singular nonzero matrix correctly has scalarcoordinate0.
    if determinant!=0 and c==0:
        raise ADWScalarUnresolved('nonzero exact determinant lost in represented magnitude')
    tree=c*c/(2*inputs[0]);work.take(tree)
    terms=4
    while True:
        pi=_adw_pi_bounds(terms,work)
        total=_adw_energy_bounds(c,inputs[1],inputs[2],_adw_parameter_ratio(inputs,pi),pi,terms,work)
        intervals={'V_tree':(tree,tree),'V_1loop':(total[0]-tree,total[1]-tree),'V_eff':total}
        represented={};errors={};ready=True
        for name,interval in intervals.items():
            if not(interval==(0,0) or interval[0]>0 or interval[1]<0):ready=False;break
            value,q,error=_adw_binary_midpoint(interval,name,nonzero=interval!=(0,0))
            if error>tolerance*abs(q):ready=False;break
            represented[name]=value;errors[name]=error
        if ready:
            discrepancy=abs(Fraction.from_float(represented['V_tree'])+Fraction.from_float(represented['V_1loop'])-Fraction.from_float(represented['V_eff']))
            return dict(C=float(c),N_f=N_f,Lambda=Lambda,G=G,**represented,
                scalar_model='supplied represented C; continuous adopted scalar ansatz',
                scalar_inputs=inputs,matrix_determinant_exact=determinant,scalar_coordinate_status='represented magnitude; general fourth-root error uncomputed',
                value_intervals=intervals,rounding_errors=errors,split_discrepancy=discrepancy,
                split_discrepancy_bound=sum(errors.values()),terms=terms,work_used=work.used)
        terms*=2;work.take(terms)


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
