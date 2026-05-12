"""
Phase 6p Wave 3a.2.3c: Fibonacci 3-strand T-gate brute-force compiler.

Generates a braid word approximating the standard Clifford+T T-gate
T_NC = diag(1, e^(iπ/4)) on the Fibonacci 3-strand qubit-sector
representation over Q(ζ₄₀, √φ), to precision ε ≤ 10⁻³, via depth-bounded
brute-force search with beam-pruning.

Per Wave 3a.2.3c DR (`Lit-Search/Phase-6p/Phase 6p Wave 3a.2.3c — KBS T-gate
Algorithm- Fibonacci Substrate.md`, 2026-05-12):

  - PATH (a) [pre-computed primary-source braid]: NO-GO. Confirmed via 13-source
    audit including the KBS paper (arXiv:1310.4150), KBS PhD thesis, HZBS 2007
    (arXiv:quant-ph/0610111), TQSim (arXiv:2307.01892), Burrello-Trombettoni-
    Lepori 2010, Rouabah 2020, Long et al. 2025 GA-SK (arXiv:2501.01746),
    Carnahan-Zeuch-Bonesteel 2015, McDonald-Katzgraber 2013, MIP 2025
    (arXiv:2510.00649). **No primary-source publication ships a Fibonacci
    T-gate braid for any precision.**
  - PATH (b) Strategy P1 (this script): external generation + Lean literal
    embed. Recommended at ~30-60 LoC of Lean overhead (~150 LoC with
    framework) consuming the Python-generated braid.

Conventions (HZBS 2007, Eqs. 5-6):
  - R₁ = e^(-i4π/5) — R-matrix value for the τ⊗τ → 1 fusion channel.
  - Rτ = e^(i3π/5) — R-matrix value for the τ⊗τ → τ fusion channel.
  - F = [[φ⁻¹, φ⁻¹/²], [φ⁻¹/², -φ⁻¹]] — Bonesteel-Hormozi-Simon F-matrix.
  - σ₁ = diag(R₁, Rτ), σ₂ = F · σ₁ · F.
  - Distance: operator (spectral) norm after global-phase removal.

Output: braid word as list of (generator_label, signed_power) pairs +
Lean-formatted literal ready to copy-paste into
`lean/SKEFTHawking/TgateFibBraid.lean`.

Runtime budget: ~5-30 minutes for L_max = 20-22 with beam_width = 10000.

Usage:
    cd SK_EFT_Hawking
    uv run python scripts/phase6p_tgate_compiler.py [--Lmax 22] [--eps 1e-3] [--beam 10000]
"""
from __future__ import annotations

import argparse
import sys
import time

import numpy as np


# ---- Fibonacci 3-strand qubit-sector generators ----
phi = (1 + np.sqrt(5)) / 2
phi_inv = 1 / phi
sqrt_phi_inv = np.sqrt(phi_inv)

# HZBS 2007 R-matrix conventions
R1 = np.exp(-1j * 4 * np.pi / 5)
Rtau = np.exp(1j * 3 * np.pi / 5)

# Bonesteel-Hormozi-Simon F-matrix (= its own inverse: F² = I)
F = np.array(
    [[phi_inv, sqrt_phi_inv],
     [sqrt_phi_inv, -phi_inv]],
    dtype=complex,
)

sigma1 = np.diag([R1, Rtau]).astype(complex)
sigma2 = F @ sigma1 @ F

# Verify F is its own inverse (sanity)
assert np.allclose(F @ F, np.eye(2)), "F² ≠ I; convention mismatch"

# Target: standard Nielsen-Chuang T-gate
T_NC = np.diag([1.0 + 0j, np.exp(1j * np.pi / 4)])


# ---- Distance metric (spectral norm after global-phase removal) ----
def dist_spectral_modphase(U: np.ndarray, V: np.ndarray) -> float:
    """Spectral (operator) norm distance after removing global phase.

    Per HZBS 2007 Sec. V.B: ‖U − V‖_op where the global phase has been
    chosen to maximize the trace overlap.
    """
    tr = np.trace(U @ V.conj().T)
    if abs(tr) < 1e-12:
        return float(np.linalg.norm(U - V, ord=2))
    phase = tr / abs(tr)
    return float(np.linalg.norm(U - phase * V, ord=2))


# ---- Brute-force search with beam-pruning ----
# Generators: σ₁ (0), σ₂ (1), σ₁⁻¹ (2), σ₂⁻¹ (3)
GENS = [sigma1, sigma2, np.linalg.inv(sigma1), np.linalg.inv(sigma2)]
# Cancellation lookup: gens[g] · gens[inv_idx[g]] = I
INV_IDX = [2, 3, 0, 1]
# Generator labels for Lean literal output
LEAN_LABELS = ["σp 0", "σp 1", "σn 0", "σn 1"]


def search(L_max: int = 22, eps_target: float = 1e-3, beam_width: int = 10000):
    """Iterative-deepening BFS with beam-pruning.

    At each depth, expand all surviving states by 4 generators (skipping
    cancellation moves σᵢ · σᵢ⁻¹), keep the top `beam_width` by distance.
    """
    best_d = 2.0
    best_w: list[int] = []
    # State: (U, w) — current matrix product and the braid word that built it
    states: list[tuple[np.ndarray, list[int]]] = [(np.eye(2, dtype=complex), [])]
    t0 = time.time()
    for depth in range(1, L_max + 1):
        candidates: list[tuple[np.ndarray, list[int], float]] = []
        for U, w in states:
            for g_idx, G in enumerate(GENS):
                if w and INV_IDX[g_idx] == w[-1]:
                    continue  # skip σᵢ · σᵢ⁻¹ cancellation
                U_new = U @ G
                w_new = w + [g_idx]
                d = dist_spectral_modphase(U_new, T_NC)
                candidates.append((U_new, w_new, d))
                if d < best_d:
                    best_d = d
                    best_w = w_new
                    elapsed = time.time() - t0
                    print(
                        f"[L={len(w_new):2d}] dist={d:.6e}  "
                        f"(elapsed={elapsed:.1f}s, candidates={len(candidates)})"
                    )
                    sys.stdout.flush()
                    if d <= eps_target:
                        return best_w, best_d
        # Beam-prune
        candidates.sort(key=lambda x: x[2])
        states = [(U, w) for U, w, _ in candidates[:beam_width]]
        elapsed = time.time() - t0
        print(
            f"  [depth {depth} complete: {len(candidates)} candidates → "
            f"beam {len(states)}; elapsed={elapsed:.1f}s; best d={best_d:.6e}]"
        )
        sys.stdout.flush()
    return best_w, best_d


def format_lean_literal(w: list[int]) -> str:
    """Format the braid word as a Lean BraidWord 3 literal."""
    if not w:
        return "[]"  # empty braid = identity (BAD approximation, but valid)
    letters = ", ".join(LEAN_LABELS[g] for g in w)
    return f"[{letters}]"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--Lmax", type=int, default=22,
                        help="Maximum braid length to search (default: 22)")
    parser.add_argument("--eps", type=float, default=1e-3,
                        help="Target precision (default: 1e-3)")
    parser.add_argument("--beam", type=int, default=10000,
                        help="Beam-search width per depth (default: 10000)")
    args = parser.parse_args()

    print(f"Phase 6p Wave 3a.2.3c T-gate brute-force compiler")
    print(f"  Target: T_NC = diag(1, e^(iπ/4))")
    print(f"  Method: Fibonacci 3-strand qubit-sector + spectral-norm distance")
    print(f"  L_max={args.Lmax}, eps_target={args.eps:.1e}, beam_width={args.beam}")
    print()

    best_w, best_d = search(args.Lmax, args.eps, args.beam)

    print()
    print("=" * 60)
    print(f"FINAL: dist = {best_d:.6e}, length = {len(best_w)}")
    print(f"  Achieved target? {'YES' if best_d <= args.eps else 'NO (got %.3e, wanted %.3e)' % (best_d, args.eps)}")
    print()
    print("Lean literal (BraidWord 3 with TgateFibBraid helpers σp, σn):")
    print(f"  def tgateBraid : BraidWord 3 :=")
    print(f"    {format_lean_literal(best_w)}")
    print()
    print(f"Frobenius distance squared (rational target): {best_d**2:.6e}")
    print()
    return 0 if best_d <= args.eps else 1


if __name__ == "__main__":
    sys.exit(main())
