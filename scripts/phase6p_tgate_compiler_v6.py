"""
Phase 6p Wave 3a.2.3c-followup: T-gate compiler v6 (Frobenius-direct).

CRITICAL REVISION: v1-v5 optimized spectral norm with global phase opt-out,
but the Lean `IsBHSZApprox` predicate (and downstream `frobNormSq_ext`) does
NOT do global-phase modulo — it computes literal entry-wise distance.

For the Fibonacci 3-strand qubit-sector representation, det(σ₁) = e^(-iπ/5),
so net signed letter count `n` gives det(ρ(w)) = e^(-iπn/5). The target
T_NC has det = e^(iπ/4) = e^(iπ·1/4). No integer n satisfies
−n/5 ≡ 1/4 (mod 2). So ρ(w) cannot match T_NC literally even up to a
40th-root phase.

The fix: choose target `T_target = ζ_40^k · T_NC` for an optimal k that
minimizes Frobenius distance. Lean substrate (QCyc40Ext) natively supports
multiplication by ζ_40, so a shifted target is just as native.

Then the search is over braids AND phase shifts.

Actually even better: we want ρ(w) ≈ T_target, where T_target is any
"phase-equivalent" version of T_NC. The valid global phases in QCyc40 are
ζ_40^k for k ∈ {0,...,39}. We try each k and keep best.

Usage:
    uv run python scripts/phase6p_tgate_compiler_v6.py [--L 30]
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

# Precompute all 40 phase-shifted targets (ζ_40^k · T_NC)
ZETA40 = np.exp(2j * np.pi / 40)
TARGETS = [(ZETA40 ** k) * T_NC for k in range(40)]

GENS = [sigma1, sigma2, np.linalg.inv(sigma1), np.linalg.inv(sigma2)]
INV_IDX = [2, 3, 0, 1]
LEAN_LABELS = ["σp 0", "σp 1", "σn 0", "σn 1"]


def frob_dist_sq_to_target(M: np.ndarray, T: np.ndarray) -> float:
    """Squared Frobenius distance ‖M − T‖²_F (no phase opt)."""
    D = M - T
    return float(np.sum(np.abs(D)**2))


def best_phase_frob_dist_sq(M: np.ndarray) -> tuple[float, int]:
    """Return (min squared Frobenius distance from M to any ζ_40^k · T_NC, k)."""
    best_d = float("inf")
    best_k = 0
    for k, T in enumerate(TARGETS):
        d = frob_dist_sq_to_target(M, T)
        if d < best_d:
            best_d = d
            best_k = k
    return best_d, best_k


def best_phase_continuous(M: np.ndarray) -> tuple[float, float]:
    """Find optimal continuous global phase α minimizing ‖M − e^(iα) T_NC‖²_F.

    d²/dα = 2 Im[Tr(e^(iα) T_NC M†)] = 0  →  Tr(e^(iα) T_NC M†) is real.
    So α = -arg(Tr(T_NC M†)).
    """
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
    """Hill-climbing local search optimizing Frobenius² to TARGETS[k_target]."""
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


def format_lean_literal(w: list[int]) -> str:
    if not w:
        return "[]"
    return "[" + ", ".join(LEAN_LABELS[g] for g in w) + "]"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--L", type=int, default=30, help="Braid word length")
    parser.add_argument("--trials", type=int, default=500000, help="Random seed words")
    parser.add_argument("--keep-top", type=int, default=50, help="Top-K to refine")
    parser.add_argument("--ls-depth", type=int, default=2, help="LS window depth")
    parser.add_argument("--seed", type=int, default=42, help="RNG seed")
    args = parser.parse_args()

    print(f"Phase 6p Wave 3a.2.3c-followup T-gate compiler v6 (Frobenius-direct)")
    print(f"  Target: T_NC = diag(1, e^(iπ/4)) up to ζ_40^k global phase")
    print(f"  L={args.L}, trials={args.trials}, top={args.keep_top}, seed={args.seed}")
    print()

    rng = np.random.default_rng(args.seed)
    t0 = time.time()

    # Phase 1: random sampling — score by min over 40 phase shifts
    print(f"[v6] Phase 1: random sampling {args.trials} words of length {args.L}...")
    sys.stdout.flush()
    scored = []
    for trial in range(args.trials):
        w = random_word(args.L, rng)
        M = eval_word(w)
        # Score: min Frobenius² over 40 phase shifts (Lean-compatible)
        d_f, k = best_phase_frob_dist_sq(M)
        # Also compute optimal continuous phase for comparison
        d_cont, _ = best_phase_continuous(M)
        scored.append((d_f, k, w, d_cont))
        if trial > 0 and trial % 50000 == 0:
            scored.sort(key=lambda x: x[0])
            d_disc = scored[0][0]
            d_cont_best = scored[0][3]
            print(f"  trial {trial}: best frob² (40-disc)={d_disc:.6e} (cont={d_cont_best:.6e})  (elapsed={time.time()-t0:.1f}s)")
            sys.stdout.flush()
    scored.sort(key=lambda x: x[0])
    print(f"[v6] Phase 1 done: best frob²={scored[0][0]:.6e} (k={scored[0][1]})")
    sys.stdout.flush()

    # Phase 2: local search on top-K (with each top word's optimal k_target)
    print(f"[v6] Phase 2: local-search refinement of top {args.keep_top}...")
    sys.stdout.flush()
    refined = []
    for k_idx, (d_f, k_phase, w, d_cont) in enumerate(scored[:args.keep_top]):
        w_new, d_new = local_search_frob(list(w), k_phase, depth=args.ls_depth)
        refined.append((d_new, k_phase, w_new))
        if k_idx > 0 and k_idx % 10 == 0:
            refined.sort(key=lambda x: x[0])
            print(f"  refined {k_idx}: best frob²={refined[0][0]:.6e}  (elapsed={time.time()-t0:.1f}s)")
            sys.stdout.flush()
    refined.sort(key=lambda x: x[0])

    best_d_f, best_k, best_w = refined[0]
    best_w_opt = remove_cancellations(best_w)
    M_opt = eval_word(best_w_opt)
    # Verify against the phase-shifted target
    d_opt_f = frob_dist_sq_to_target(M_opt, TARGETS[best_k])
    d_opt_frob = np.sqrt(d_opt_f)
    # Spectral norm
    D = M_opt - TARGETS[best_k]
    d_opt_spec = float(np.linalg.norm(D, ord=2))

    print()
    print("=" * 60)
    print(f"FINAL: Frobenius dist = {d_opt_frob:.6e} (Frobenius² = {d_opt_f:.6e})")
    print(f"       spectral dist  = {d_opt_spec:.6e}")
    print(f"  target = ζ_40^{best_k} · T_NC,  phase angle = {2*np.pi*best_k/40:.4f} rad")
    print(f"  length L = {len(best_w_opt)}")
    print(f"  Achieved Frobenius² ≤ (1e-3)² = 1e-6? {'YES' if d_opt_f <= 1e-6 else 'NO'}")
    print(f"  Achieved Frobenius² ≤ (1e-2)² = 1e-4? {'YES' if d_opt_f <= 1e-4 else 'NO'}")
    print()
    print("Lean literal (BraidWord 3):")
    print(f"  def tgateBraid : BraidWord 3 :=")
    print(f"    {format_lean_literal(best_w_opt)}")
    print()
    print(f"Best phase shift index k = {best_k}  (so target = ζ_40^{best_k} · T_NC)")
    print(f"  ζ_40^{best_k} = e^(2πi·{best_k}/40)")
    print()
    print("Top-10 refined results:")
    for k_idx, (d, k_p, w) in enumerate(refined[:10]):
        w_clean = remove_cancellations(w)
        print(f"  #{k_idx+1}: frob²={d:.6e}, frob={np.sqrt(d):.6e}, k_phase={k_p}, L={len(w_clean)}")

    return 0 if d_opt_f <= 1e-6 else 1


if __name__ == "__main__":
    sys.exit(main())
