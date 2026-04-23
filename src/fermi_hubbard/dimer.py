"""Phase 5t Wave 2 — Fermi-Hubbard dimer algebraic core (Python cross-check).

Python companion to ``lean/SKEFTHawking/FermiHubbardDimer.lean``. Every
function here has a Lean theorem; the tests verify numerical agreement
across a random parameter grid.

No experimental parameters, no provenance: the dimer is a purely
algebraic object. The module exists so that the Lean-verified structural
results (real-symmetry, chiral anticommutation, dark-state kernel,
triplet decoupling, det/trace identities) can be exercised by the same
Python pipeline that runs the rest of the project.

Lean refs
---------
- ``T1 H_singlet_isSymm``
- ``T2 dark_state_in_kernel``
- ``T3 darkVec_ne_zero``
- ``T4 chiralOp_sq``
- ``T5 chiral_anticommutes``
- ``T6 det_H_singlet``
- ``T7 trace_H_singlet``
- ``T10a triplet_plus_zero``
- ``T10b triplet_zero_zero``
- ``T10c triplet_minus_zero``

Aristotle: manual.
Source: Kiefer et al., arXiv:2507.22112 (Nature 2026). Deep research in
``Lit-Search/Phase-5t/Effective Fermi-Hubbard Dimer for the Doublon
Geometric Gate.md``.
"""

from __future__ import annotations

import numpy as np


# ---------------------------------------------------------------------------
# 1. 3×3 singlet-sector Hamiltonian in the {D+, D-, s} basis
# ---------------------------------------------------------------------------


def H_singlet(t: float, delta: float, U: float) -> np.ndarray:
    """Return the 3×3 singlet-sector Hamiltonian in the {|D+⟩, |D-⟩, |s⟩}
    symmetry-adapted basis.

    Matches ``SKEFTHawking.FermiHubbardDimer.H_singlet``. Real symmetric
    for all parameters.
    """
    return np.array(
        [
            [U, delta, -2.0 * t],
            [delta, U, 0.0],
            [-2.0 * t, 0.0, 0.0],
        ],
        dtype=float,
    )


def dark_vec(t: float, delta: float) -> np.ndarray:
    """Return the unnormalized dark-state vector ``(0, 2t, Δ)``.

    Matches ``SKEFTHawking.FermiHubbardDimer.darkVec``. Lies in
    ``ker(H_singlet t delta 0)`` by Lean theorem T2.
    """
    return np.array([0.0, 2.0 * t, delta], dtype=float)


def chiral_op() -> np.ndarray:
    """Return the chiral symmetry operator Γ = diag(+1, -1, -1).

    Matches ``SKEFTHawking.FermiHubbardDimer.chiralOp``. Involutory
    (Γ² = I) and anticommutes with H at U = 0.
    """
    return np.diag([1.0, -1.0, -1.0])


# ---------------------------------------------------------------------------
# 2. Full 6×6 Hamiltonian in the site basis
# ---------------------------------------------------------------------------


#: Basis indices for the 6×6 Hamiltonian, per Kiefer et al. convention.
BASIS_6 = (
    "|↑,↑⟩",
    "|↑↓,0⟩",
    "|↑,↓⟩",
    "|↓,↑⟩",
    "|0,↑↓⟩",
    "|↓,↓⟩",
)


def H_full(t: float, delta: float, U: float) -> np.ndarray:
    """Return the 6×6 site-basis Hamiltonian.

    Matches ``SKEFTHawking.FermiHubbardDimer.H_full``. The alternating
    (-t, +t) pattern on rows 2 and 3 encodes fermionic anticommutation.
    """
    return np.array(
        [
            [0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
            [0.0, U + delta, -t, t, 0.0, 0.0],
            [0.0, -t, 0.0, 0.0, -t, 0.0],
            [0.0, t, 0.0, 0.0, t, 0.0],
            [0.0, 0.0, -t, t, U - delta, 0.0],
            [0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
        ],
        dtype=float,
    )


#: The three triplet eigenvectors of H_full, each at exactly zero energy.
#: Match Lean theorems T10a (|t+⟩), T10b (|t0⟩ unnormalized), T10c (|t-⟩).
TRIPLET_PLUS = np.array([1, 0, 0, 0, 0, 0], dtype=float)
TRIPLET_ZERO_UNNORM = np.array([0, 0, 1, 1, 0, 0], dtype=float)
TRIPLET_MINUS = np.array([0, 0, 0, 0, 0, 1], dtype=float)


# ---------------------------------------------------------------------------
# 2b. Symmetry-adapted basis embeddings (Phase 5t W3)
# ---------------------------------------------------------------------------

#: Unnormalized symmetric doublon |D+⟩ ∝ |↑↓,0⟩ + |0,↑↓⟩.
#: Matches ``SKEFTHawking.FermiHubbardDimer.v_Dplus``.
V_DPLUS = np.array([0, 1, 0, 0, 1, 0], dtype=float)

#: Unnormalized antisymmetric doublon |D-⟩ ∝ |↑↓,0⟩ − |0,↑↓⟩.
#: Matches ``SKEFTHawking.FermiHubbardDimer.v_Dminus``.
V_DMINUS = np.array([0, 1, 0, 0, -1, 0], dtype=float)

#: Unnormalized spin singlet |s⟩ ∝ |↑,↓⟩ − |↓,↑⟩.
#: Matches ``SKEFTHawking.FermiHubbardDimer.v_s``.
V_S = np.array([0, 0, 1, -1, 0, 0], dtype=float)

#: Unnormalized S_z = 0 triplet |t0⟩ ∝ |↑,↓⟩ + |↓,↑⟩.
#: Matches ``SKEFTHawking.FermiHubbardDimer.v_t0``.
V_T0 = np.array([0, 0, 1, 1, 0, 0], dtype=float)

#: Computational basis |↑,↓⟩.
#: Matches ``SKEFTHawking.FermiHubbardDimer.up_down``.
UP_DOWN = np.array([0, 0, 1, 0, 0, 0], dtype=float)

#: Computational basis |↓,↑⟩.
#: Matches ``SKEFTHawking.FermiHubbardDimer.down_up``.
DOWN_UP = np.array([0, 0, 0, 1, 0, 0], dtype=float)


def block_match_Dplus(t: float, delta: float, U: float) -> np.ndarray:
    """Return the expected RHS of Lean W3a: ``U·v_Dplus + Δ·v_Dminus − 2t·v_s``.
    """
    return U * V_DPLUS + delta * V_DMINUS + (-2.0 * t) * V_S


def block_match_Dminus(t: float, delta: float, U: float) -> np.ndarray:
    """Return the expected RHS of Lean W3b: ``Δ·v_Dplus + U·v_Dminus``."""
    return delta * V_DPLUS + U * V_DMINUS


def block_match_s(t: float, delta: float, U: float) -> np.ndarray:
    """Return the expected RHS of Lean W3c: ``(−2t)·v_Dplus``."""
    return (-2.0 * t) * V_DPLUS


# ---------------------------------------------------------------------------
# 3. Derived quantities (bright-state energies, characteristic polynomial)
# ---------------------------------------------------------------------------


def bright_energies_U0(t: float, delta: float) -> tuple[float, float]:
    """Return the two nonzero eigenvalues of ``H_singlet t delta 0``.

    At U = 0 the characteristic polynomial is ``λ(λ² − Δ² − 4t²)``, so
    the nonzero eigenvalues are ``±√(Δ² + 4t²)``. Matches the informal
    statement of deep research T4; the formal characteristic-polynomial
    theorem T8 is deferred to Phase 5t Wave 3.
    """
    gap = np.sqrt(delta**2 + 4.0 * t**2)
    return (-gap, gap)


def singlet_determinant(t: float, delta: float, U: float) -> float:
    """Return ``det H_singlet(t, Δ, U) = -4 U t²`` (Lean T6).

    Note the result is independent of Δ. In particular, ``det H₃ = 0``
    whenever ``U = 0`` or ``t = 0`` — the former is the physically
    interesting dark-state case.
    """
    return -4.0 * U * t**2


def singlet_trace(t: float, delta: float, U: float) -> float:
    """Return ``tr H_singlet(t, Δ, U) = 2U`` (Lean T7).

    Independent of t and Δ. At U = 0 the trace vanishes, consistent
    with paired nonzero eigenvalues ±E plus the zero dark-state
    eigenvalue.
    """
    return 2.0 * U


def chiral_anticommutator_U0(t: float, delta: float) -> np.ndarray:
    """Return ``Γ · H₃(t, Δ, 0) + H₃(t, Δ, 0) · Γ``.

    Lean T5 asserts this is identically zero. The function is exposed
    so tests can verify by direct numerical evaluation on a random
    grid of (t, Δ) values.
    """
    H = H_singlet(t, delta, 0.0)
    G = chiral_op()
    return G @ H + H @ G


# ---------------------------------------------------------------------------
# 4. θ-parametrized dark state + bright eigenvectors + charpoly (Phase 5t W4)
# ---------------------------------------------------------------------------


def dark_state_theta(theta: float) -> np.ndarray:
    """Return the θ-parametrized dark-state vector ``(0, sin θ, cos θ)``
    in the {|D+⟩, |D-⟩, |s⟩} basis.

    Matches ``SKEFTHawking.FermiHubbardDimer.darkStateθ``. Lies in
    ``ker(H_singlet t Δ 0)`` when ``Δ · sin θ = 2t · cos θ``
    (Lean W4a ``dark_state_theta_in_kernel``).
    """
    return np.array([0.0, np.sin(theta), np.cos(theta)], dtype=float)


def bright_vec_plus(t: float, delta: float) -> np.ndarray:
    """Return the positive-energy bright-state eigenvector
    ``(√(Δ²+4t²), Δ, -2t)``.

    Matches ``SKEFTHawking.FermiHubbardDimer.brightVecPlus``.
    Eigenvector of ``H_singlet(t, Δ, 0)`` with eigenvalue
    ``+√(Δ²+4t²)`` (Lean W4b ``H_singlet_U0_brightVecPlus``).
    """
    g = np.sqrt(delta**2 + 4.0 * t**2)
    return np.array([g, delta, -2.0 * t], dtype=float)


def bright_vec_minus(t: float, delta: float) -> np.ndarray:
    """Return the negative-energy bright-state eigenvector
    ``(-√(Δ²+4t²), Δ, -2t)``.

    Matches ``SKEFTHawking.FermiHubbardDimer.brightVecMinus``.
    Eigenvector of ``H_singlet(t, Δ, 0)`` with eigenvalue
    ``-√(Δ²+4t²)`` (Lean W4c ``H_singlet_U0_brightVecMinus``).
    """
    g = np.sqrt(delta**2 + 4.0 * t**2)
    return np.array([-g, delta, -2.0 * t], dtype=float)


def gap_at_U0(t: float, delta: float) -> float:
    """Return the positive-energy bright-state eigenvalue
    ``√(Δ² + 4t²)`` — the gap between the dark state and the positive
    bright state at ``U = 0``.

    Matches ``SKEFTHawking.FermiHubbardDimer.gapAtU0``. Strictly
    positive when ``(t, Δ) ≠ (0, 0)`` (Lean W4d ``gapAtU0_pos``).
    """
    return float(np.sqrt(delta**2 + 4.0 * t**2))


def charpoly_coeffs(t: float, delta: float, U: float) -> tuple[float, float, float, float]:
    """Return the coefficients ``(c₃, c₂, c₁, c₀)`` of the monic
    characteristic polynomial of ``H_singlet(t, Δ, U)``:
        ``p(λ) = c₃·λ³ + c₂·λ² + c₁·λ + c₀``
    with ``c₃ = 1``, ``c₂ = -2U``, ``c₁ = U² - Δ² - 4t²``,
    ``c₀ = 4Ut²``.

    Matches Lean W4f ``charpoly_H_singlet``. At ``U = 0`` this
    reduces to ``λ(λ² − (Δ² + 4t²))`` with roots ``{0, ±√(Δ²+4t²)}``
    (Lean W4g ``charpoly_H_singlet_U0`` and W4h spectrum factored).
    """
    return (1.0, -2.0 * U, U**2 - delta**2 - 4.0 * t**2, 4.0 * U * t**2)


# --- Phase 5t W5: Chiral conjugation + BDI spectrum pairing ---


def chiral_conjugation_U0(t: float, delta: float) -> np.ndarray:
    """Return ``Γ · H_singlet(t, Δ, 0) · Γ``. By Lean W5a
    ``chiralOp_conjugation_neg``, this equals ``-H_singlet(t, Δ, 0)``
    exactly. Used to verify the BDI-class chiral conjugation rule
    numerically on a random (t, Δ) grid.
    """
    Gamma = chiral_op()
    H = H_singlet(t, delta, 0.0)
    return Gamma @ H @ Gamma


def chiral_image_plus(t: float, delta: float) -> np.ndarray:
    """Return ``Γ · brightVecPlus(t, Δ)``. By Lean W5g
    ``brightVecPlus_chiral_image``, this equals
    ``-brightVecMinus(t, Δ)``. Witnesses ± eigenvector pairing
    under chiral symmetry.
    """
    return chiral_op() @ bright_vec_plus(t, delta)


def chiral_image_minus(t: float, delta: float) -> np.ndarray:
    """Return ``Γ · brightVecMinus(t, Δ)``. By Lean W5g'
    ``brightVecMinus_chiral_image``, this equals
    ``-brightVecPlus(t, Δ)``. Mirror of ``chiral_image_plus``;
    together with it confirms ``Γ²·brightVecPlus = +brightVecPlus``
    (consistency with Γ² = I, Lean W2 T4).
    """
    return chiral_op() @ bright_vec_minus(t, delta)


def chiral_image_dark(t: float, delta: float) -> np.ndarray:
    """Return ``Γ · darkVec(t, Δ)``. By Lean W5e
    ``darkVec_in_chiral_minus_eigenspace``, this equals
    ``-darkVec(t, Δ)`` — pins the zero mode to the (-1)-eigenspace
    of Γ (the BDI sublattice structure, ``{|D₋⟩, |s⟩}``).
    """
    return chiral_op() @ dark_vec(t, delta)


def spectrum_U0(t: float, delta: float) -> np.ndarray:
    """Return the exact spectrum of ``H_singlet(t, Δ, 0)`` as a
    length-3 numpy array ``[0, +gap, -gap]``. Matches the Lean W4p
    ``H_singlet_U0_mem_spectrum_iff`` statement
    ``spectrum = {0, +√(Δ²+4t²), -√(Δ²+4t²)}``.
    """
    g = float(np.sqrt(delta**2 + 4.0 * t**2))
    return np.array([0.0, g, -g], dtype=float)


def spectrum_symmetric_under_neg(t: float, delta: float, tol: float = 1e-12) -> bool:
    """Return ``True`` iff the exact spectrum is symmetric under
    negation (the BDI ± pairing, Lean W5c ``spectrum_pairing_U0``).
    Since the spectrum is the finite set ``{0, ±gap}``, this is
    always true; the numeric check is a belt-and-suspenders witness
    for cross-checking against the Lean statement.
    """
    spec = spectrum_U0(t, delta)
    neg_spec = -spec
    return bool(np.allclose(np.sort(spec), np.sort(neg_spec), atol=tol))


# --- Phase 5t W5 round-2 strengthening: chiral sublattice projectors ---


def chiral_proj_plus() -> np.ndarray:
    """Return the ``(+1)``-eigenspace projector of the chiral operator:
    ``P_+ := (1 + Γ)/2``. For ``Γ = diag(+1, -1, -1)`` this is
    ``diag(1, 0, 0)``: projects onto span{|D₊⟩} (the 1-dim sublattice).

    Matches Lean W5l ``chiralProjPlus``.
    """
    return 0.5 * (np.eye(3) + chiral_op())


def chiral_proj_minus() -> np.ndarray:
    """Return the ``(-1)``-eigenspace projector of the chiral operator:
    ``P_- := (1 - Γ)/2``. For ``Γ = diag(+1, -1, -1)`` this is
    ``diag(0, 1, 1)``: projects onto span{|D₋⟩, |s⟩} (the 2-dim
    sublattice, where the zero mode lives by Lean W5e).

    Matches Lean W5m ``chiralProjMinus``.
    """
    return 0.5 * (np.eye(3) - chiral_op())


# --- Phase 5t W6A: Normalized eigenvectors (EuclideanSpace path) ---


def dark_vec_norm(t: float, delta: float) -> np.ndarray:
    """Return the L2-normalized dark-state eigenvector
    ``(0, 2t, Δ) / √(Δ²+4t²)``. Matches Lean W6A ``darkVecNorm``.
    Unit Euclidean norm when ``(t, Δ) ≠ (0, 0)``.
    """
    g = float(np.sqrt(delta**2 + 4.0 * t**2))
    return dark_vec(t, delta) / g


def bright_vec_plus_norm(t: float, delta: float) -> np.ndarray:
    """Return the L2-normalized positive-energy bright eigenvector
    ``(√g, Δ, -2t) / (√2 · √g)``. Matches Lean W6A
    ``brightVecPlusNorm``.
    """
    g = float(np.sqrt(delta**2 + 4.0 * t**2))
    return bright_vec_plus(t, delta) / (np.sqrt(2.0) * g)


def bright_vec_minus_norm(t: float, delta: float) -> np.ndarray:
    """Return the L2-normalized negative-energy bright eigenvector.
    Matches Lean W6A ``brightVecMinusNorm``.
    """
    g = float(np.sqrt(delta**2 + 4.0 * t**2))
    return bright_vec_minus(t, delta) / (np.sqrt(2.0) * g)


# --- Phase 5t W6C: Geometric SWAP operator on the singlet sector ---


def u_swap_singlet(t: float, delta: float) -> np.ndarray:
    """Return the geometric SWAP operator on the singlet subspace,
    expressed in the ``{|D₊⟩, |D₋⟩, |s⟩}`` basis. Householder-type
    reflection:
        ``U_SWAP(i, j) = δ_{ij} - (2 / (Δ²+4t²)) · darkVec(i) · darkVec(j)``
    This is the idealized geometric SWAP gate from the Kiefer et al.
    doublon protocol: dark state picks up `-1` on a 2π cycle (Berry
    phase), bright states are unchanged.

    Matches Lean W6C ``U_SWAP_singlet``. Properties (all Lean-verified):
    - ``U · darkVec = -darkVec`` (W6C-A1)
    - ``U · brightVec± = brightVec±`` (W6C-A2/A3)
    - ``Uᵀ = U`` (W6C-S1: symmetric)
    - ``U · U = I`` (W6C-S2: involution)
    - ``U · Uᵀ = I`` (W6C-S3: orthogonal/unitary)
    - ``det U = -1``, ``tr U = +1``
    """
    g_sq = delta**2 + 4.0 * t**2
    dv = dark_vec(t, delta)
    outer = np.outer(dv, dv)  # 3×3 matrix with entries dv[i] * dv[j]
    return np.eye(3) - (2.0 / g_sq) * outer


# --- Phase 5t W6 round-2 strengthening (W6C-A1s/A2s/A3s, W6C-U1, W6C-K1) ---


def u_swap_action_on_kernel(t: float, delta: float, v: np.ndarray) -> np.ndarray:
    """Return the SWAP operator's action on an arbitrary vector ``v`` in the
    kernel of ``H_singlet(t, delta, 0)``. By W5p zero-mode uniqueness + W6C-A1s
    scalar-multiple sign flip, every such ``v`` is mapped to ``-v``.

    This function exists as a cross-check for W6C-K1 (the Lean theorem):
        ``H · v = 0  ⟹  U_SWAP · v = -v``
    The return value should always equal ``-v`` (up to floating-point) for any
    ``v`` in the true kernel. Tests exercise this with random scalar multiples
    of ``dark_vec`` and random linear combinations that land in the kernel.

    Matches Lean W6C-K1 ``U_SWAP_singlet_on_kernel``.
    """
    return u_swap_singlet(t, delta) @ v


# --- Phase 5t W7: Direct Exchange vs Superexchange Scaling ---


def E_plus(t: float, U: float) -> float:
    """Return the upper eigenvalue of the 2×2 symmetric sector of the
    Hubbard dimer at zero detuning:
        ``E_plus(t, U) := (U + sqrt(U^2 + 16*t^2)) / 2``
    Root of the quadratic ``lambda^2 - U*lambda - 4*t^2 = 0``. Matches
    Lean W7 ``E_plus``.
    """
    return (U + float(np.sqrt(U**2 + 16.0 * t**2))) / 2.0


def E_minus(t: float, U: float) -> float:
    """Return the lower eigenvalue of the same 2×2 sector:
        ``E_minus(t, U) := (U - sqrt(U^2 + 16*t^2)) / 2``
    Matches Lean W7 ``E_minus``.
    """
    return (U - float(np.sqrt(U**2 + 16.0 * t**2))) / 2.0


def J_superexchange(t: float, U: float) -> float:
    """Return the superexchange gap:
        ``J(t, U) := E_plus(t, U) - U = (sqrt(U^2 + 16*t^2) - U) / 2``
    At large U this approaches ``4*t^2/U`` (textbook superexchange). At
    U = 0 it equals ``2|t|`` (direct-exchange value; regimes meet).
    Matches Lean W7 ``J_superexchange``.
    """
    return E_plus(t, U) - U


def J_leading_superexchange(t: float, U: float) -> float:
    """Return the textbook superexchange leading term ``4*t^2/U``.

    Used to cross-check the Lean W7i bound
    ``|J(t, U) - 4*t^2/U| <= 16*t^4/U^3`` for ``U >= 4*|t| > 0``.
    """
    return 4.0 * t**2 / U


# --- Phase 5t W7 round-2 strengthening (W7j-W7q) ---


def E_plus_eigenvector(t: float, U: float) -> np.ndarray:
    """Return the explicit eigenvector of ``H_singlet(t, 0, U)`` for the
    upper eigenvalue ``E_plus``. In the ``{|D+⟩, |D-⟩, |s⟩}`` basis this
    is the three-component vector ``[E_plus(t, U), 0, -2*t]``.

    Matches Lean W7m ``H_singlet_Δ0_E_plus_eigenvector``:
        ``H · [E_plus, 0, -2t] = E_plus • [E_plus, 0, -2t]``
    The D- component is zero because at ``Δ = 0`` the antisymmetric
    doublon decouples.
    """
    return np.array([E_plus(t, U), 0.0, -2.0 * t])


def E_minus_eigenvector(t: float, U: float) -> np.ndarray:
    """Return the explicit eigenvector of ``H_singlet(t, 0, U)`` for the
    lower eigenvalue ``E_minus``. Mirror of ``E_plus_eigenvector``."""
    return np.array([E_minus(t, U), 0.0, -2.0 * t])


def antisymmetric_doublon_vec() -> np.ndarray:
    """Return the antisymmetric-doublon eigenvector ``|D-⟩ = [0, 1, 0]``
    in the ``{|D+⟩, |D-⟩, |s⟩}`` basis. At ``Δ = 0`` this is an
    eigenvector of ``H_singlet(t, 0, U)`` with eigenvalue ``U`` (Lean W7o).
    """
    return np.array([0.0, 1.0, 0.0])


def E_plus_char_residual(t: float, U: float) -> float:
    """Return the characteristic-equation residual
    ``E_plus^2 - U * E_plus - 4*t^2``. Per Lean W7j this is exactly
    zero up to floating-point precision.
    """
    e = E_plus(t, U)
    return e * e - U * e - 4.0 * t**2


def E_minus_char_residual(t: float, U: float) -> float:
    """Return the characteristic-equation residual
    ``E_minus^2 - U * E_minus - 4*t^2``. Per Lean W7k this is exactly
    zero up to floating-point precision.
    """
    e = E_minus(t, U)
    return e * e - U * e - 4.0 * t**2


# --- Phase 5t W6-deferred: 6×6 SWAP lift in the symmetry-adapted basis ---


def u_swap_adapted(t: float, delta: float) -> np.ndarray:
    """Return the 6×6 block-diagonal lift of ``U_SWAP_singlet`` to the
    symmetry-adapted basis ``{|D+⟩, |D-⟩, |s⟩} ⊕ {|t+⟩, |t0⟩, |t-⟩}``
    (singlet ⊕ triplet). Top-left 3×3 block is ``U_SWAP_singlet``;
    bottom-right 3×3 block is the identity (triplet sector has no
    phase accumulation).

    Matches Lean W6D ``U_SWAP_adapted``. Properties (all Lean-verified):
    - ``U = Uᵀ`` (W6D-S1 symmetric)
    - ``U · U = I`` (W6D-S2 involution)
    - ``U · Uᵀ = I`` (W6D-S3 orthogonal/unitary)
    - Action agrees with ``U_SWAP_singlet`` on the top block; identity
      on the bottom block (W6D-A1/A2).

    NOT a claim about SWAP on ``{|↑,↓⟩, |↓,↑⟩}``: that requires
    Berry-phase holonomy (W8 / Phase 6).
    """
    block_top = u_swap_singlet(t, delta)
    result = np.zeros((6, 6))
    result[:3, :3] = block_top
    result[3:, 3:] = np.eye(3)
    return result


# --- Phase 5t W8 Target A: Minimal geometric phase theorem ---


def dark_state_theta_norm(theta: float) -> np.ndarray:
    """Return the θ-parameterized normalized dark state used in the
    Berry-phase formulation of the geometric gate:
        ``darkStateθ(θ) = [0, sin(θ), cos(θ)]``
    in the ``{|D+⟩, |D-⟩, |s⟩}`` basis.

    Matches Lean ``darkStateθ`` (Section 5). This is the **already
    L²-normalized** version of the dark state, parameterized by the
    mixing angle θ. The in-kernel condition is ``Δ·sin(θ) = 2t·cos(θ)``.
    """
    return np.array([0.0, np.sin(theta), np.cos(theta)])


def geometric_phase_loop_check(theta: float) -> dict[str, np.ndarray | float]:
    """Cross-check Lean W8 geometric-phase claims on a single θ-point:
    - W8a: ``darkStateθ(θ + π) = -darkStateθ(θ)`` (sign flip)
    - W8b: ``darkStateθ(θ + 2π) = darkStateθ(θ)`` (2π periodicity)
    - W8c: ``⟨darkStateθ(θ), darkStateθ(θ)⟩ = 1`` (L² unit norm)

    Returns a dict with the key vectors + a deviation-from-Lean-claim
    Frobenius-norm witness for each.
    """
    start = dark_state_theta_norm(theta)
    after_pi = dark_state_theta_norm(theta + np.pi)
    after_2pi = dark_state_theta_norm(theta + 2.0 * np.pi)
    return {
        "start": start,
        "after_pi": after_pi,
        "after_2pi": after_2pi,
        "sign_flip_err": float(np.linalg.norm(after_pi - (-start))),
        "periodicity_err": float(np.linalg.norm(after_2pi - start)),
        "unit_norm_err": float(abs(np.dot(start, start) - 1.0)),
    }
