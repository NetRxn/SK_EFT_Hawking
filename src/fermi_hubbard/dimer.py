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
