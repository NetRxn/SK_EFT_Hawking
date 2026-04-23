"""Phase 5t Wave 9 — Doublon geometric gate exact diagonalization
(Python cross-validation layer).

Thin experimental wrapper around ``src.fermi_hubbard.dimer`` that
exposes exact diagonalization of the 3×3 singlet-sector and 6×6
full-basis Fermi-Hubbard dimer Hamiltonians. Also packages the
direct-exchange vs superexchange scaling curves (from Lean W7) for
visualization.

Every function here is either:
- A direct call to ``numpy.linalg.eigh`` on the Lean-verified
  ``H_singlet`` / ``H_full`` matrices, OR
- A closed-form Lean-verified scalar (from ``E_plus``, ``J_superexchange``).

No new physics. No new constants. No new parameters. The module
exists so that the Stage-8 / Stage-9 pipeline (visualizations +
review) can consume the Phase 5t algebraic core without re-deriving
anything.

Lean refs
---------
- Section 6 ``charpoly_H_singlet`` (full cubic)
- Section 16 W7 ``E_plus``, ``E_minus``, ``J_superexchange``
- Section 17 W7 round-2 ``charpoly_H_singlet_Δ0_factored``

Aristotle: manual.
Source: Kiefer et al., arXiv:2507.22112 (Nature 2026). Deep research:
``Lit-Search/Phase-5t/``.
"""

from __future__ import annotations

from typing import NamedTuple

import numpy as np

from src.fermi_hubbard.dimer import (
    E_minus,
    E_plus,
    H_full,
    H_singlet,
    J_leading_superexchange,
    J_superexchange,
    u_swap_adapted,
    u_swap_singlet,
)


class DimerSpectrum(NamedTuple):
    """Full exact-diagonalization result for the Fermi-Hubbard dimer.

    Attributes
    ----------
    eigenvalues_3x3 :
        Sorted eigenvalues of the 3×3 singlet-sector block
        ``H_singlet(t, delta, U)`` — three values in ascending order.
    eigenvalues_6x6 :
        Sorted eigenvalues of the full 6×6 Hamiltonian
        ``H_full(t, delta, U)`` — six values in ascending order.
    eigenvectors_3x3 :
        Columns are the eigenvectors of ``H_singlet`` corresponding
        to ``eigenvalues_3x3``.
    eigenvectors_6x6 :
        Columns are the eigenvectors of ``H_full`` corresponding to
        ``eigenvalues_6x6``.
    """
    eigenvalues_3x3: np.ndarray
    eigenvalues_6x6: np.ndarray
    eigenvectors_3x3: np.ndarray
    eigenvectors_6x6: np.ndarray


def exact_diagonalize(t: float, delta: float, U: float) -> DimerSpectrum:
    """Return exact diagonalization of the 3×3 and 6×6 Fermi-Hubbard
    dimer Hamiltonians at parameters ``(t, delta, U)``.

    Uses numpy's Hermitian diagonalization. The 3×3 block is real
    symmetric (Lean T1); the 6×6 is also real symmetric (constructed
    that way in Lean Section 1). Eigenvalues returned in ascending
    order.
    """
    H3 = H_singlet(t, delta, U)
    H6 = H_full(t, delta, U)
    evals3, evecs3 = np.linalg.eigh(H3)
    evals6, evecs6 = np.linalg.eigh(H6)
    return DimerSpectrum(
        eigenvalues_3x3=evals3,
        eigenvalues_6x6=evals6,
        eigenvectors_3x3=evecs3,
        eigenvectors_6x6=evecs6,
    )


def scaling_comparison_curves(
    t: float,
    U_range: np.ndarray,
) -> dict[str, np.ndarray]:
    """Return the direct-exchange vs superexchange scaling curves for
    visualization.

    Returns a dict with:
    - ``U``:     the input U grid
    - ``E_plus``:  upper eigenvalue of the 2×2 symmetric block
    - ``E_minus``: lower eigenvalue of the 2×2 symmetric block
    - ``J``:     superexchange gap ``E_plus - U``
    - ``J_leading``: textbook leading superexchange ``4*t²/U`` (valid
      only for U > 0; returns nan at U=0 to avoid division by zero)
    - ``direct_linear``: direct-exchange linear approximation
      ``2|t| + U/2`` (valid for small U)

    All quantities are Lean-verified scalars (W7 Section 16). No new
    physics.
    """
    Us = np.asarray(U_range, dtype=float)
    E_plus_arr = np.array([E_plus(t, U) for U in Us])
    E_minus_arr = np.array([E_minus(t, U) for U in Us])
    J_arr = np.array([J_superexchange(t, U) for U in Us])
    J_lead = np.array([4.0 * t**2 / U if U > 0 else np.nan for U in Us])
    direct_linear = 2.0 * abs(t) + Us / 2.0
    return {
        "U": Us,
        "E_plus": E_plus_arr,
        "E_minus": E_minus_arr,
        "J": J_arr,
        "J_leading": J_lead,
        "direct_linear": direct_linear,
    }


def dimer_spectrum_at_U0(t: float, delta: float) -> np.ndarray:
    """Return the exact spectrum of ``H_singlet(t, delta, 0)`` — the
    Wave-4 U=0 result: three eigenvalues ``{0, +√(delta²+4t²), -√(...)}``.

    Lean reference: W4p ``H_singlet_U0_mem_spectrum_iff``.
    """
    return np.array(sorted(np.linalg.eigvalsh(H_singlet(t, delta, 0.0))))


def swap_action_on_singlet(t: float, delta: float) -> dict[str, np.ndarray]:
    """Verify the W6C Berry-phase-style gate action on the singlet
    sector. Returns a structured dict with the SWAP operator, the
    three eigenvectors (dark, bright+, bright-), and the
    corresponding SWAP-acted images (``-dark``, ``+bright+``, ``+bright-``).

    Lean refs: W6C-A1/A2/A3.
    """
    U = u_swap_singlet(t, delta)
    dark = np.array([0.0, 2.0 * t, delta])
    g = float(np.sqrt(delta**2 + 4.0 * t**2))
    bright_plus = np.array([g, delta, -2.0 * t])
    bright_minus = np.array([-g, delta, -2.0 * t])
    return {
        "U_SWAP": U,
        "dark": dark,
        "bright_plus": bright_plus,
        "bright_minus": bright_minus,
        "U_times_dark": U @ dark,
        "U_times_bright_plus": U @ bright_plus,
        "U_times_bright_minus": U @ bright_minus,
    }


def gate_6x6_unitarity_witness(t: float, delta: float) -> dict[str, float]:
    """Cross-check the 6×6 block-diagonal SWAP lift (W6D) is unitary.

    Returns a dict with the Frobenius norms of ``U·U - I``, ``U·Uᵀ - I``,
    and ``det(U) - (-1)``, all of which should be ≈ 0.
    """
    U6 = u_swap_adapted(t, delta)
    I6 = np.eye(6)
    return {
        "involution_err": float(np.linalg.norm(U6 @ U6 - I6)),
        "orthogonal_err": float(np.linalg.norm(U6 @ U6.T - I6)),
        "det_minus_one_err": float(abs(np.linalg.det(U6) - (-1.0))),
    }


def bench_superexchange_bound(
    t: float,
    U_factor_range: np.ndarray,
) -> dict[str, np.ndarray]:
    """Compute the superexchange approximation bound residuals across a
    range of ``U/(4|t|)`` factors. For each ``U = 4*|t| * factor``,
    returns:
    - ``U``:    the U values
    - ``residual``: ``|J(t, U) - 4*t²/U|`` (actual error)
    - ``bound``:    ``16 * t⁴ / U³`` (Lean W7i bound)

    Lean reference: W7i ``J_superexchange_bound``.
    """
    if t == 0:
        # Trivial case: all residuals zero, all bounds zero.
        Us = 4.0 * abs(t) * np.asarray(U_factor_range, dtype=float)
        return {
            "U": Us,
            "residual": np.zeros_like(Us),
            "bound": np.zeros_like(Us),
        }
    Us = 4.0 * abs(t) * np.asarray(U_factor_range, dtype=float)
    residuals = np.array([
        abs(J_superexchange(t, U) - J_leading_superexchange(t, U))
        if U > 0 else 0.0
        for U in Us
    ])
    bounds = np.where(
        Us > 0, 16.0 * t**4 / Us**3, np.zeros_like(Us)
    )
    return {
        "U": Us,
        "residual": residuals,
        "bound": bounds,
    }
