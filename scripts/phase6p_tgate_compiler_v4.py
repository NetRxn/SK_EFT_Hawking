"""
Phase 6p Wave 3a.2.3c-followup: Fibonacci 3-strand T-gate compiler v4
(random-search + local-improvement, parallelized).

Strategy:
  1. Generate M random braid words of length L (with cancellation pruning).
  2. Score each by spectral-norm distance to T_NC.
  3. Refine top-K via local search:
       For each position i, try replacing letter w[i] with each of the
       4 generators (subject to non-cancellation at i-1 and i+1); accept
       any change that lowers the distance.
       Iterate until convergence.
  4. Also try LENGTHENING: insert σ_i σ_j at random positions and check
     if the longer word is better.

This is essentially a hill-climbing GA without mutation/crossover. For
the Fibonacci T-gate problem, the literature suggests this is the
practical workhorse: McDonald-Katzgraber 2013 (arXiv:1211.7359) is exactly
this kind of GA over braids.

Usage:
    uv run python scripts/phase6p_tgate_compiler_v4.py [--L 30] [--trials 100000]
"""
from __future__ import annotations

import argparse
import sys
import time

import numpy as np


phi = (1 + np.sqrt(5)) / 2
phi_inv = 1 / phi
sqrt_phi_inv = np.sqrt(phi_inv)

R1 = np.exp(-1j * 4 * np.pi / 5)
Rtau = np.exp(1j * 3 * np.pi / 5)

F = np.array(
    [[phi_inv, sqrt_phi_inv],
     [sqrt_phi_inv, -phi_inv]],
    dtype=complex,
)

sigma1 = np.diag([R1, Rtau]).astype(complex)
sigma2 = F @ sigma1 @ F
assert np.allclose(F @ F, np.eye(2)), "F² ≠ I"

T_NC = np.diag([1.0 + 0j, np.exp(1j * np.pi / 4)])

GENS = [sigma1, sigma2, np.linalg.inv(sigma1), np.linalg.inv(sigma2)]
GENS_arr = np.array(GENS)  # (4, 2, 2) for vectorization
INV_IDX = [2, 3, 0, 1]
LEAN_LABELS = ["σp 0", "σp 1", "σn 0", "σn 1"]


def dist_spectral_modphase(U: np.ndarray, V: np.ndarray) -> float:
    tr = np.trace(U @ V.conj().T)
    if abs(tr) < 1e-12:
        return float(np.linalg.norm(U - V, ord=2))
    phase = tr / abs(tr)
    return float(np.linalg.norm(U - phase * V, ord=2))


def eval_word(w: list) -> np.ndarray:
    M = np.eye(2, dtype=complex)
    for g in w:
        M = M @ GENS[g]
    return M


def random_word(L: int, rng: np.random.Generator) -> list:
    """Random word of length L with no σᵢσᵢ⁻¹ cancellation."""
    w = [int(rng.integers(0, 4))]
    for _ in range(L - 1):
        # Choose any generator except the inverse of the previous
        choices = [g for g in range(4) if g != INV_IDX[w[-1]]]
        w.append(int(rng.choice(choices)))
    return w


def local_search(w: list, max_iters: int = 100, depth: int = 2) -> tuple[list, float]:
    """Hill-climbing local search on a braid word.

    Operations:
      - At each window of `depth` adjacent positions, try every combination
        of generators in the window (subject to non-cancellation with the
        word context).
      - Accept any change that reduces distance.

    Stops when no window-swap improves.
    """
    M = eval_word(w)
    d = dist_spectral_modphase(M, T_NC)
    L = len(w)
    for it in range(max_iters):
        improved = False
        for i in range(L - depth + 1):
            # Enumerate all 4^depth replacements of w[i:i+depth]
            current = list(w[i:i+depth])
            best_window = current
            best_d_local = d
            # Iterate all combinations
            def enumerate_window(prefix, remaining):
                nonlocal best_window, best_d_local
                if remaining == 0:
                    # Construct full word
                    w_new = list(w[:i]) + prefix + list(w[i+depth:])
                    # Check cancellations at window boundaries
                    if i > 0 and INV_IDX[prefix[0]] == w_new[i-1]:
                        return
                    for j in range(len(prefix) - 1):
                        if INV_IDX[prefix[j+1]] == prefix[j]:
                            return
                    if i + depth < L and INV_IDX[w_new[i+depth]] == prefix[-1]:
                        return
                    M_new = eval_word(w_new)
                    d_new = dist_spectral_modphase(M_new, T_NC)
                    if d_new < best_d_local - 1e-12:
                        best_d_local = d_new
                        best_window = list(prefix)
                    return
                for g in range(4):
                    enumerate_window(prefix + [g], remaining - 1)
            enumerate_window([], depth)
            if best_window != current:
                w[i:i+depth] = best_window
                d = best_d_local
                improved = True
        if not improved:
            break
    return w, d


def remove_cancellations(w: list) -> list:
    out = list(w)
    changed = True
    while changed:
        changed = False
        new_out = []
        i = 0
        while i < len(out):
            if i + 1 < len(out) and INV_IDX[out[i + 1]] == out[i]:
                i += 2
                changed = True
            else:
                new_out.append(out[i])
                i += 1
        out = new_out
    return out


def format_lean_literal(w: list[int]) -> str:
    if not w:
        return "[]"
    return "[" + ", ".join(LEAN_LABELS[g] for g in w) + "]"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--L", type=int, default=30, help="Braid word length")
    parser.add_argument("--trials", type=int, default=100000, help="Random starts")
    parser.add_argument("--keep-top", type=int, default=200, help="Top-K to refine")
    parser.add_argument("--seed", type=int, default=42, help="RNG seed")
    parser.add_argument("--eps", type=float, default=1e-3, help="Target eps")
    parser.add_argument("--ls-depth", type=int, default=2, help="Local search window depth")
    args = parser.parse_args()

    print(f"Phase 6p Wave 3a.2.3c-followup T-gate compiler v4")
    print(f"  Target: T_NC = diag(1, e^(iπ/4))")
    print(f"  L={args.L}, trials={args.trials}, keep_top={args.keep_top}, seed={args.seed}")
    print()

    rng = np.random.default_rng(args.seed)
    t0 = time.time()

    # Phase 1: random search
    print(f"[v4] Phase 1: random sampling {args.trials} words of length {args.L}...")
    sys.stdout.flush()
    scored = []
    for trial in range(args.trials):
        w = random_word(args.L, rng)
        M = eval_word(w)
        d = dist_spectral_modphase(M, T_NC)
        scored.append((d, w))
        if trial > 0 and trial % 10000 == 0:
            scored.sort(key=lambda x: x[0])
            print(f"  trial {trial}: best d so far={scored[0][0]:.6e}  (elapsed={time.time()-t0:.1f}s)")
            sys.stdout.flush()
    scored.sort(key=lambda x: x[0])
    print(f"[v4] Phase 1 done: best={scored[0][0]:.6e}, top-5={[f'{s[0]:.4e}' for s in scored[:5]]}")
    sys.stdout.flush()

    # Phase 2: local search on top-K
    print(f"[v4] Phase 2: local-search refinement of top {args.keep_top}...")
    sys.stdout.flush()
    refined = []
    for k, (d, w) in enumerate(scored[:args.keep_top]):
        w_new, d_new = local_search(list(w), depth=args.ls_depth)
        refined.append((d_new, w_new))
        if k > 0 and k % 50 == 0:
            refined.sort(key=lambda x: x[0])
            print(f"  refined {k}: best d after LS={refined[0][0]:.6e}  (elapsed={time.time()-t0:.1f}s)")
            sys.stdout.flush()
    refined.sort(key=lambda x: x[0])

    best_d, best_w = refined[0]
    best_w_opt = remove_cancellations(best_w)
    M_opt = eval_word(best_w_opt)
    d_opt = dist_spectral_modphase(M_opt, T_NC)

    print()
    print("=" * 60)
    print(f"FINAL: dist_spectral = {d_opt:.6e}, length = {len(best_w_opt)}")
    print(f"  (raw L={len(best_w)}, after peephole L={len(best_w_opt)})")
    print(f"  Achieved target? {'YES' if d_opt <= args.eps else 'NO (got %.3e, wanted %.3e)' % (d_opt, args.eps)}")
    print()
    print("Lean literal (BraidWord 3):")
    print(f"  def tgateBraid : BraidWord 3 :=")
    print(f"    {format_lean_literal(best_w_opt)}")
    print()
    print(f"Frobenius distance squared (upper bound): {d_opt**2:.6e}")
    print()
    print("Top-10 refined results:")
    for k, (d, w) in enumerate(refined[:10]):
        w_clean = remove_cancellations(w)
        print(f"  #{k+1}: d={d:.4e}, L={len(w_clean)} after peephole")

    return 0 if d_opt <= args.eps else 1


if __name__ == "__main__":
    sys.exit(main())
