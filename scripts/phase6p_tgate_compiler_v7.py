"""
Phase 6p Wave 3a.2.3c-substrate-upgrade: T-gate compiler v7 (QCyc80 phase grid).

Builds on v6 (Frobenius-direct over QCyc40 with 40-element phase grid). v6
identified a substrate-level parity obstruction in the 40-grid: det(ρ(braid))
takes values ζ_40^{-4n} (always even-power), while det(T_NC) = ζ_40^5
(odd-power). No `ζ_40^k` global phase can match parity, so QCyc40 had a
floor at ε ~ 1.27 × 10⁻² (Frobenius²) independent of compiler quality.

QCyc80 lifts the phase grid to 80 elements ζ_80^k, k ∈ {0,...,79}. Both odd
and even k are available. det(T_NC) = ζ_8 = ζ_80^10. det(ρ(w)) = ζ_10^{-n} =
ζ_80^{-8n} for net signed letter count n. Matching ζ_80^{-8n} against
ζ_80^{2k} · ζ_80^10 (i.e., k determines a global phase squared to det match)
gives -8n ≡ 2k + 10 (mod 80), i.e., k ≡ -4n - 5 (mod 40). The k value is
uniquely determined modulo 40 by n; both odd and even k exist as the parity
of -4n-5 toggles with n. SO PARITY IS UNBLOCKED.

Pragmatically: the v7 compiler scans all 80 phase shifts ζ_80^k (k=0..79),
and the discrete-grid Frobenius² floor is now bounded by random-search
fluctuation rather than the ζ_40 grid resolution.

Usage:
    uv run python scripts/phase6p_tgate_compiler_v7.py [--L 30] [--trials 1000000]
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
assert np.allclose(F @ F, np.eye(2)), "F^2 != I"

T_NC = np.diag([1.0 + 0j, np.exp(1j * np.pi / 4)])

# 80-element ζ_80 phase grid (the substrate-upgrade payoff)
ZETA80 = np.exp(2j * np.pi / 80)
TARGETS = [(ZETA80 ** k) * T_NC for k in range(80)]

GENS = [sigma1, sigma2, np.linalg.inv(sigma1), np.linalg.inv(sigma2)]
INV_IDX = [2, 3, 0, 1]
LEAN_LABELS = ["σp 0", "σp 1", "σn 0", "σn 1"]


def frob_dist_sq_to_target(M: np.ndarray, T: np.ndarray) -> float:
    """Squared Frobenius distance ||M - T||^2_F (no phase opt)."""
    D = M - T
    return float(np.sum(np.abs(D)**2))


def best_phase_frob_dist_sq(M: np.ndarray) -> tuple[float, int]:
    """Return (min squared Frobenius distance from M to any ζ_80^k · T_NC, k)."""
    best_d = float("inf")
    best_k = 0
    for k, T in enumerate(TARGETS):
        d = frob_dist_sq_to_target(M, T)
        if d < best_d:
            best_d = d
            best_k = k
    return best_d, best_k


def best_phase_continuous(M: np.ndarray) -> tuple[float, float]:
    """Find optimal continuous global phase α minimizing ||M - e^(iα) T_NC||^2_F."""
    tr = np.trace(T_NC @ M.conj().T)
    if abs(tr) < 1e-15:
        return float(np.sum(np.abs(M - T_NC)**2)), 0.0
    alpha = -np.angle(tr)
    T_opt = np.exp(1j * alpha) * T_NC
    return float(np.sum(np.abs(M - T_opt)**2)), float(alpha)


def eval_word(w: list) -> np.ndarray:
    M = np.eye(2, dtype=complex)
    for g in w:
        M = M @ GENS[g]
    return M


def random_word(L: int, rng: np.random.Generator) -> list:
    w = [int(rng.integers(0, 4))]
    for _ in range(L - 1):
        choices = [g for g in range(4) if g != INV_IDX[w[-1]]]
        w.append(int(rng.choice(choices)))
    return w


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


def local_search_frob(w: list, k_target: int, depth: int = 2, max_iters: int = 50) -> tuple[list, float]:
    """Hill-climbing local search optimizing Frobenius^2 to TARGETS[k_target]."""
    T = TARGETS[k_target]
    M = eval_word(w)
    d = frob_dist_sq_to_target(M, T)
    L = len(w)
    for _ in range(max_iters):
        improved = False
        for i in range(L - depth + 1):
            current = list(w[i:i+depth])
            best_window = current
            best_d_local = d
            stack = [[]]
            while stack:
                prefix = stack.pop()
                if len(prefix) == depth:
                    ok = True
                    for j in range(len(prefix) - 1):
                        if INV_IDX[prefix[j+1]] == prefix[j]:
                            ok = False; break
                    if not ok:
                        continue
                    if i > 0 and INV_IDX[prefix[0]] == w[i-1]:
                        continue
                    if i + depth < L and INV_IDX[w[i+depth]] == prefix[-1]:
                        continue
                    w_new = list(w[:i]) + prefix + list(w[i+depth:])
                    M_new = eval_word(w_new)
                    d_new = frob_dist_sq_to_target(M_new, T)
                    if d_new < best_d_local - 1e-15:
                        best_d_local = d_new
                        best_window = list(prefix)
                    continue
                for g in range(4):
                    stack.append(prefix + [g])
            if best_window != current:
                w[i:i+depth] = best_window
                d = best_d_local
                improved = True
        if not improved:
            break
    return w, d


def basin_hopping(w_start: list, k_target: int, n_basins: int = 20,
                  kick_size: int = 4, ls_depth: int = 2,
                  rng: np.random.Generator = None) -> tuple[list, float]:
    """Basin hopping: random perturbation + local search + accept-if-better.

    A simulated-annealing-style global-search wrapper on top of local search.
    Each basin: randomly mutate `kick_size` letters, run local_search_frob,
    accept the new optimum if better than current.
    """
    if rng is None:
        rng = np.random.default_rng(12345)
    L = len(w_start)
    w_best = list(w_start)
    M = eval_word(w_best)
    d_best = frob_dist_sq_to_target(M, TARGETS[k_target])
    for _ in range(n_basins):
        # Perturb: replace `kick_size` random positions with random letters
        w_pert = list(w_best)
        for _ in range(kick_size):
            pos = int(rng.integers(0, L))
            new_g = int(rng.integers(0, 4))
            # Maintain non-cancellation around pos
            if pos > 0 and INV_IDX[new_g] == w_pert[pos - 1]:
                continue
            if pos + 1 < L and INV_IDX[w_pert[pos + 1]] == new_g:
                continue
            w_pert[pos] = new_g
        w_pert = remove_cancellations(w_pert)
        # Pad back to length L if shortened (rare)
        while len(w_pert) < L:
            last = w_pert[-1] if w_pert else int(rng.integers(0, 4))
            choices = [g for g in range(4) if g != INV_IDX[last]]
            w_pert.append(int(rng.choice(choices)))
        w_pert = w_pert[:L]
        w_pert, d_pert = local_search_frob(w_pert, k_target, depth=ls_depth, max_iters=30)
        if d_pert < d_best - 1e-15:
            d_best = d_pert
            w_best = list(w_pert)
    return w_best, d_best


def format_lean_literal(w: list[int]) -> str:
    if not w:
        return "[]"
    return "[" + ", ".join(LEAN_LABELS[g] for g in w) + "]"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--L", type=int, default=30, help="Braid word length")
    parser.add_argument("--trials", type=int, default=1000000, help="Random seed words")
    parser.add_argument("--keep-top", type=int, default=100, help="Top-K to refine")
    parser.add_argument("--ls-depth", type=int, default=3, help="LS window depth")
    parser.add_argument("--basin-hops", type=int, default=30,
                        help="Basin-hopping perturbations per top-K word")
    parser.add_argument("--seed", type=int, default=42, help="RNG seed")
    parser.add_argument("--epsilon-target", type=float, default=1e-3,
                        help="Spectral norm target (default 1e-3)")
    args = parser.parse_args()

    print(f"Phase 6p Wave 3a.2.3c-substrate-upgrade T-gate compiler v7 (QCyc80 phase grid)")
    print(f"  Target: T_NC = diag(1, e^(iπ/4)) up to ζ_80^k global phase (80 classes)")
    print(f"  L={args.L}, trials={args.trials}, top={args.keep_top}, "
          f"ls-depth={args.ls_depth}, basin-hops={args.basin_hops}, seed={args.seed}")
    print()

    rng = np.random.default_rng(args.seed)
    t0 = time.time()

    # Phase 1: random sampling — score by min over 80 phase shifts
    print(f"[v7] Phase 1: random sampling {args.trials} words of length {args.L}...")
    sys.stdout.flush()
    scored = []
    for trial in range(args.trials):
        w = random_word(args.L, rng)
        M = eval_word(w)
        d_f, k = best_phase_frob_dist_sq(M)
        scored.append((d_f, k, w))
        if trial > 0 and trial % 100000 == 0:
            scored.sort(key=lambda x: x[0])
            print(f"  trial {trial}: best frob^2 (80-disc)={scored[0][0]:.6e}  "
                  f"(elapsed={time.time()-t0:.1f}s)")
            sys.stdout.flush()
    scored.sort(key=lambda x: x[0])
    print(f"[v7] Phase 1 done: best frob^2={scored[0][0]:.6e} (k={scored[0][1]})")
    sys.stdout.flush()

    # Phase 2: local search on top-K (with each top word's optimal k_target)
    print(f"[v7] Phase 2: local-search (depth {args.ls_depth}) refinement of top {args.keep_top}...")
    sys.stdout.flush()
    refined = []
    for k_idx, (d_f, k_phase, w) in enumerate(scored[:args.keep_top]):
        w_new, d_new = local_search_frob(list(w), k_phase, depth=args.ls_depth, max_iters=50)
        refined.append((d_new, k_phase, w_new))
        if k_idx > 0 and k_idx % 10 == 0:
            refined.sort(key=lambda x: x[0])
            print(f"  refined {k_idx}: best frob^2={refined[0][0]:.6e}  "
                  f"(elapsed={time.time()-t0:.1f}s)")
            sys.stdout.flush()
    refined.sort(key=lambda x: x[0])
    print(f"[v7] Phase 2 done: best frob^2={refined[0][0]:.6e}")
    sys.stdout.flush()

    # Phase 3: basin hopping on top-20
    print(f"[v7] Phase 3: basin hopping ({args.basin_hops} hops each) on top 20...")
    sys.stdout.flush()
    hopped = []
    bh_rng = np.random.default_rng(args.seed + 1)
    for k_idx, (d_f, k_phase, w) in enumerate(refined[:20]):
        w_h, d_h = basin_hopping(w, k_phase, n_basins=args.basin_hops,
                                 kick_size=3, ls_depth=args.ls_depth, rng=bh_rng)
        hopped.append((d_h, k_phase, w_h))
        if k_idx > 0 and k_idx % 5 == 0:
            hopped.sort(key=lambda x: x[0])
            print(f"  hopped {k_idx}: best frob^2={hopped[0][0]:.6e}  "
                  f"(elapsed={time.time()-t0:.1f}s)")
            sys.stdout.flush()
    hopped.sort(key=lambda x: x[0])

    # Combine all refinement results
    all_results = refined + hopped
    all_results.sort(key=lambda x: x[0])

    best_d_f, best_k, best_w = all_results[0]
    best_w_opt = remove_cancellations(best_w)
    M_opt = eval_word(best_w_opt)
    d_opt_f = frob_dist_sq_to_target(M_opt, TARGETS[best_k])
    d_opt_frob = np.sqrt(d_opt_f)
    D = M_opt - TARGETS[best_k]
    d_opt_spec = float(np.linalg.norm(D, ord=2))

    eps_target = args.epsilon_target

    print()
    print("=" * 70)
    print(f"FINAL: Frobenius dist = {d_opt_frob:.6e} (Frobenius^2 = {d_opt_f:.6e})")
    print(f"       spectral dist  = {d_opt_spec:.6e}")
    print(f"  target = ζ_80^{best_k} · T_NC,  phase angle = {2*np.pi*best_k/80:.4f} rad")
    print(f"  length L = {len(best_w_opt)}")
    print(f"  Achieved spectral ≤ {eps_target}? {'YES' if d_opt_spec <= eps_target else 'NO'}")
    print(f"  Achieved Frobenius^2 ≤ {eps_target**2:.1e}? "
          f"{'YES' if d_opt_f <= eps_target**2 else 'NO'}")
    print(f"  Achieved Frobenius^2 ≤ 1e-4 (ε^2 for ε=1e-2)? "
          f"{'YES' if d_opt_f <= 1e-4 else 'NO'}")
    print(f"  Achieved Frobenius^2 ≤ 1e-6 (ε^2 for ε=1e-3)? "
          f"{'YES' if d_opt_f <= 1e-6 else 'NO'}")
    print()
    print("Lean literal (BraidWord 3):")
    print(f"  def tgateBraid_v2 : BraidWord 3 :=")
    print(f"    {format_lean_literal(best_w_opt)}")
    print()
    print(f"Best phase shift index k = {best_k}  (so target = ζ_80^{best_k} · T_NC)")
    print(f"  ζ_80^{best_k} = e^(2πi·{best_k}/80)")
    print()
    print("Top-10 final results:")
    for k_idx, (d, k_p, w) in enumerate(all_results[:10]):
        w_clean = remove_cancellations(w)
        print(f"  #{k_idx+1}: frob^2={d:.6e}, frob={np.sqrt(d):.6e}, k_phase={k_p}, L={len(w_clean)}")

    # Compute integer-coefficient Lean basis for the chosen phase ζ_80^best_k
    # In QCyc80 basis (32 components), ζ_80^k mod Φ_80(x) = x^32 - x^24 + x^16 - x^8 + 1
    # For 0 ≤ k ≤ 31: it's just basis vector e_k (coefficient 1 at index k, 0 elsewhere).
    # For 32 ≤ k ≤ 39: reduce using x^32 = x^24 - x^16 + x^8 - 1.
    #   x^{32+r} = x^{r+24} - x^{r+16} + x^{r+8} - x^r  (for 0 ≤ r ≤ 7, so r+24 ≤ 31).
    # For 40 ≤ k ≤ 79: use x^40 = -1 (verified algebraically).
    #   x^{40+s} = -x^s (for 0 ≤ s ≤ 31, no further reduction needed)
    #   ... but s can be > 31; use the rules above iteratively.
    # For simplicity below we use the fact ζ_80^40 = -1.

    print()
    print("# Phase-shift basis coefficients for the Lean literal (32-tuple):")
    coeffs = np.zeros(32, dtype=int)
    k = best_k
    if k < 32:
        coeffs[k] = 1
    elif k < 40:
        # x^{32+r} = x^{r+24} - x^{r+16} + x^{r+8} - x^r,  0 ≤ r ≤ 7
        r = k - 32
        coeffs[r + 24] += 1
        coeffs[r + 16] -= 1
        coeffs[r + 8] += 1
        coeffs[r] -= 1
    else:
        # ζ_80^k = -ζ_80^{k-40} for k ≥ 40
        k2 = k - 40
        if k2 < 32:
            coeffs[k2] = -1
        else:
            r = k2 - 32
            coeffs[r + 24] -= 1
            coeffs[r + 16] += 1
            coeffs[r + 8] -= 1
            coeffs[r] += 1
    print(f"ζ_80^{best_k} = ⟨{', '.join(str(int(c)) for c in coeffs)}⟩")
    print()

    # Compute ζ_80^{best_k} * ζ_8 = ζ_80^{best_k + 10}
    k_22 = (best_k + 10) % 80
    coeffs22 = np.zeros(32, dtype=int)
    if k_22 < 32:
        coeffs22[k_22] = 1
    elif k_22 < 40:
        r = k_22 - 32
        coeffs22[r + 24] += 1
        coeffs22[r + 16] -= 1
        coeffs22[r + 8] += 1
        coeffs22[r] -= 1
    else:
        k2 = k_22 - 40
        if k2 < 32:
            coeffs22[k2] = -1
        else:
            r = k2 - 32
            coeffs22[r + 24] -= 1
            coeffs22[r + 16] += 1
            coeffs22[r + 8] -= 1
            coeffs22[r] += 1
    print(f"# Target [1,1] = ζ_80^{best_k} * ζ_80^10 = ζ_80^{k_22}")
    print(f"ζ_80^{k_22} = ⟨{', '.join(str(int(c)) for c in coeffs22)}⟩")

    return 0 if d_opt_spec <= eps_target else 1


if __name__ == "__main__":
    sys.exit(main())
