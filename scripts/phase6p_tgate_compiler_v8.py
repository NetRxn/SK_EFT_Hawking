"""
Phase 6p Wave 3a.2.3c-substrate-upgrade-followup: T-gate compiler v8 (Solovay-Kitaev iteration).

Builds on v7 (random search + local search + basin hopping over QCyc80 phase grid;
saturates at ε_spec ≈ 1.38 × 10⁻² regardless of L). v7 identified an algorithmic
quality gap: random search at any L cannot exceed the spectral floor set by the
ε of the base library.

v8 implements **Solovay-Kitaev level-1 iteration** on top of v7's base library:
  - Use v7 to find U_0 ≈ T_target (ε_0 ≈ 1.4e-2)
  - Compute residual error E = T_target · U_0⁻¹  (so E ≈ I, with ‖E - I‖ ≈ ε_0)
  - Decompose E = V · W · V⁻¹ · W⁻¹  (balanced group commutator)
    For SU(2) rotations: explicit Dawson-Nielsen 2005 §A formula
  - Use v7 (with shorter L since V, W are small perturbations) to approximate V, W as Fibonacci
    braids V_braid, W_braid
  - Output: T_v8 = W_braid · V_braid · W_braid⁻¹ · V_braid⁻¹ · v7_braid

Solovay-Kitaev scaling: ε_v8 ≈ c · ε_0^(3/2) where c depends on the SK constants
(typically c ≤ 5). For ε_0 = 1.4e-2, ε_v8 ≈ 1.65e-3·c — close to but not below 1e-3
target with single SK level.

Multiple SK levels would require recursive approximation of V, W via SK at next-lower level.
Implementation here ships single-level SK as the substrate; level-2 is a parameter
hook for future iteration.

References:
  - Dawson-Nielsen 2005, *QIC* 6:81–95, arXiv:quant-ph/0505030 (SK algorithm + balanced
    commutator decomposition §A, §B.1).
  - Kliuchnikov-Bocharov-Svore 2013, *PRL* 112:140504 (KBS, alternative O(log(1/ε)) approach).
  - Long et al. 2025, *Phys. Scr.*, arXiv:2501.01746 (GA-Solovay-Kitaev on Fibonacci).

Usage:
    uv run python scripts/phase6p_tgate_compiler_v8.py [--L-base 46] [--L-VW 30] [--trials 200000]

Reads v7's best L=46 braid hardcoded below (from Phase 6p Wave 3a.2.3c-followup ship).
For a freshly-discovered v7 seed, replace `V7_BEST_BRAID` literal.
"""
from __future__ import annotations

import argparse
import sys
import time

import numpy as np


# ---------------------------------------------------------------------------
# Fibonacci 3-strand generators (same as v7) + targets
# ---------------------------------------------------------------------------

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

T_NC = np.diag([1.0 + 0j, np.exp(1j * np.pi / 4)])

ZETA80 = np.exp(2j * np.pi / 80)
TARGETS = [(ZETA80 ** k) * T_NC for k in range(80)]

GENS = [sigma1, sigma2, np.linalg.inv(sigma1), np.linalg.inv(sigma2)]
INV_IDX = [2, 3, 0, 1]
LEAN_LABELS = ["σp 0", "σp 1", "σn 0", "σn 1"]


# Phase 6p Wave 3a.2.3c-followup v7-discovered best L=46 T-gate-approximation braid.
# Indices into GENS: 0=σ₁, 1=σ₂, 2=σ₁⁻¹, 3=σ₂⁻¹.
V7_BEST_BRAID = [
    3, 0, 3, 0, 1, 0, 1, 2, 3, 0,
    1, 1, 0, 3, 3, 2, 1, 1, 1, 1,
    0, 1, 0, 3, 0, 0, 0, 3, 2, 2,
    2, 2, 1, 2, 2, 2, 2, 2, 1, 2,
    3, 0, 3, 0, 3, 3,
]


# ---------------------------------------------------------------------------
# Braid + target evaluation utilities
# ---------------------------------------------------------------------------

def eval_word(w: list[int]) -> np.ndarray:
    M = np.eye(2, dtype=complex)
    for g in w:
        M = M @ GENS[g]
    return M


def invert_word(w: list[int]) -> list[int]:
    """Reverse word + invert each letter."""
    return [INV_IDX[g] for g in reversed(w)]


def remove_cancellations(w: list[int]) -> list[int]:
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


def random_word(L: int, rng: np.random.Generator) -> list[int]:
    w = [int(rng.integers(0, 4))]
    for _ in range(L - 1):
        choices = [g for g in range(4) if g != INV_IDX[w[-1]]]
        w.append(int(rng.choice(choices)))
    return w


def frob_dist_sq(M: np.ndarray, T: np.ndarray) -> float:
    D = M - T
    return float(np.sum(np.abs(D)**2))


def best_phase_frob_dist_sq(M: np.ndarray) -> tuple[float, int]:
    """Min Frobenius² over 80 ζ_80^k · T_NC phase shifts."""
    best_d = float("inf")
    best_k = 0
    for k, T in enumerate(TARGETS):
        d = frob_dist_sq(M, T)
        if d < best_d:
            best_d = d
            best_k = k
    return best_d, best_k


def best_phase_continuous(M: np.ndarray) -> tuple[float, float]:
    """Continuous-phase optimal global phase α (any real)."""
    tr = np.trace(T_NC @ M.conj().T)
    if abs(tr) < 1e-15:
        return float(np.sum(np.abs(M - T_NC)**2)), 0.0
    alpha = -np.angle(tr)
    T_opt = np.exp(1j * alpha) * T_NC
    return float(np.sum(np.abs(M - T_opt)**2)), float(alpha)


def spectral_dist(M: np.ndarray, T: np.ndarray) -> float:
    return float(np.linalg.norm(M - T, ord=2))


# ---------------------------------------------------------------------------
# SU(2) balanced commutator decomposition (Dawson-Nielsen 2005 §A)
# ---------------------------------------------------------------------------

PAULI_X = np.array([[0, 1], [1, 0]], dtype=complex)
PAULI_Y = np.array([[0, -1j], [1j, 0]], dtype=complex)
PAULI_Z = np.array([[1, 0], [0, -1]], dtype=complex)


def su2_axis_angle(U: np.ndarray) -> tuple[float, np.ndarray]:
    """Decompose U ∈ SU(2) as exp(-i α/2 σ·n̂). Return (α, n̂).

    For U = a*I + i*(b σ_x + c σ_y + d σ_z) with a²+b²+c²+d² = 1:
      α = 2*arccos(a)
      n̂ = (b, c, d) / sqrt(b²+c²+d²)
    """
    # Normalize to SU(2) (det = 1)
    det = np.linalg.det(U)
    U_sd = U / np.sqrt(det)
    a = float(np.real(np.trace(U_sd)) / 2)
    a = np.clip(a, -1.0, 1.0)
    alpha = 2 * np.arccos(a)
    if abs(np.sin(alpha / 2)) < 1e-15:
        # U ≈ ±I, axis is undefined; return ẑ as default
        return float(alpha), np.array([0.0, 0.0, 1.0])
    sin_half = np.sin(alpha / 2)
    # The anti-Hermitian part: i * (b σ_x + c σ_y + d σ_z)
    AH = (U_sd - U_sd.conj().T) / 2
    # AH = i * (b σ_x + c σ_y + d σ_z), so b σ_x + c σ_y + d σ_z = -i * AH
    H = -1j * AH
    b = float(np.real(np.trace(H @ PAULI_X)) / 2)
    c = float(np.real(np.trace(H @ PAULI_Y)) / 2)
    d = float(np.real(np.trace(H @ PAULI_Z)) / 2)
    norm = np.sqrt(b*b + c*c + d*d)
    if norm < 1e-15:
        return float(alpha), np.array([0.0, 0.0, 1.0])
    n_hat = np.array([b, c, d]) / norm
    # The convention: U = a*I - i*sin(α/2) σ·n̂
    # Verify sign: -i*sin(α/2)*n̂ should match H/sin(α/2) up to sign
    # H is real-coeff combination of paulis; we extracted b, c, d such that
    # H = -i*sin(α/2)*(real coefficients). So divide:
    n_hat_signed = -np.array([b, c, d]) / sin_half
    n_hat_signed_norm = np.linalg.norm(n_hat_signed)
    if n_hat_signed_norm > 1e-12:
        n_hat = n_hat_signed / n_hat_signed_norm
    return float(alpha), n_hat


def rotation_matrix(angle: float, axis: np.ndarray) -> np.ndarray:
    """Return U = exp(-i angle/2 σ·n̂) ∈ SU(2)."""
    axis_norm = axis / np.linalg.norm(axis)
    sigma_n = (axis_norm[0] * PAULI_X +
               axis_norm[1] * PAULI_Y +
               axis_norm[2] * PAULI_Z)
    return np.cos(angle / 2) * np.eye(2) - 1j * np.sin(angle / 2) * sigma_n


def find_orthonormal_pair(n: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    """Find two orthonormal vectors perpendicular to n in ℝ³."""
    n = n / np.linalg.norm(n)
    # Pick a non-parallel vector
    if abs(n[2]) < 0.9:
        v = np.array([0.0, 0.0, 1.0])
    else:
        v = np.array([1.0, 0.0, 0.0])
    a = v - np.dot(v, n) * n
    a = a / np.linalg.norm(a)
    b = np.cross(n, a)
    return a, b


def balanced_commutator(E: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    """Dawson-Nielsen 2005 §A.1: given E ∈ SU(2), find V, W with V·W·V⁻¹·W⁻¹ = E.

    For E = R_n̂(α), choose V = R_â(φ), W = R_b̂(φ) where â, b̂ ⊥ n̂ and φ
    satisfies sin²(φ/2) = sqrt(sin(α/4)).

    The standard formula: cos(α) = 1 - 8·sin⁴(φ/2)
                     ⟹ sin⁴(φ/2) = (1 - cos α)/8 = sin²(α/2)/4
                     ⟹ sin²(φ/2) = sin(α/2)/2
                     ⟹ φ = 2·arcsin(sqrt(sin(α/2)/2))
    """
    alpha, n_hat = su2_axis_angle(E)
    # Wrap α to (-π, π]
    while alpha > np.pi:
        alpha -= 2 * np.pi
    while alpha <= -np.pi:
        alpha += 2 * np.pi
    if alpha < 0:
        alpha = -alpha
        n_hat = -n_hat
    sin_half_phi_sq = np.sin(alpha / 2) / 2.0
    sin_half_phi_sq = np.clip(sin_half_phi_sq, 0.0, 1.0)
    phi_val = 2 * np.arcsin(np.sqrt(sin_half_phi_sq))
    a_hat, b_hat = find_orthonormal_pair(n_hat)
    V = rotation_matrix(phi_val, a_hat)
    W = rotation_matrix(phi_val, b_hat)
    return V, W


# ---------------------------------------------------------------------------
# Fibonacci-3-strand approximation of a target U (used by SK recursion)
# ---------------------------------------------------------------------------

def approximate_unitary(target: np.ndarray, L: int, trials: int,
                        ls_depth: int, basin_hops: int,
                        rng: np.random.Generator) -> tuple[list[int], float]:
    """Random search + local search + basin hopping to approximate `target` ∈ SU(2)
    as a Fibonacci-3-strand braid of length ≤ L. Returns (word, frob² distance).

    NOTE: no phase quotient — we want EXACT approximation of `target`, not target
    up to global phase. For SK iteration, V, W are absolute unitaries, not
    target-up-to-phase.
    """
    # Phase 1: random sampling
    scored: list[tuple[float, list[int]]] = []
    for _ in range(trials):
        w = random_word(L, rng)
        M = eval_word(w)
        d = frob_dist_sq(M, target)
        scored.append((d, w))
    scored.sort(key=lambda x: x[0])

    # Phase 2: local search on top 100
    refined: list[tuple[float, list[int]]] = []
    for d_init, w in scored[:100]:
        w_new, d_new = local_search_frob(w, target, depth=ls_depth, max_iters=30)
        refined.append((d_new, w_new))
    refined.sort(key=lambda x: x[0])

    # Phase 3: basin hopping on top 10
    bh_rng = np.random.default_rng(rng.integers(0, 2**32))
    hopped: list[tuple[float, list[int]]] = []
    for d_init, w in refined[:10]:
        w_h, d_h = basin_hopping(w, target, n_basins=basin_hops, kick_size=3,
                                  ls_depth=ls_depth, rng=bh_rng)
        hopped.append((d_h, w_h))
    hopped.sort(key=lambda x: x[0])

    all_results = refined + hopped
    all_results.sort(key=lambda x: x[0])
    return remove_cancellations(all_results[0][1]), all_results[0][0]


def local_search_frob(w: list[int], target: np.ndarray, depth: int = 2,
                       max_iters: int = 50) -> tuple[list[int], float]:
    """Hill-climbing local search optimizing Frobenius² to `target`."""
    M = eval_word(w)
    d = frob_dist_sq(M, target)
    L = len(w)
    for _ in range(max_iters):
        improved = False
        for i in range(L - depth + 1):
            current = list(w[i:i+depth])
            best_window = current
            best_d_local = d
            stack: list[list[int]] = [[]]
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
                    d_new = frob_dist_sq(M_new, target)
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


def basin_hopping(w_start: list[int], target: np.ndarray, n_basins: int = 20,
                  kick_size: int = 4, ls_depth: int = 2,
                  rng: np.random.Generator = None) -> tuple[list[int], float]:
    if rng is None:
        rng = np.random.default_rng(12345)
    L = len(w_start)
    w_best = list(w_start)
    M = eval_word(w_best)
    d_best = frob_dist_sq(M, target)
    for _ in range(n_basins):
        w_pert = list(w_best)
        for _ in range(kick_size):
            pos = int(rng.integers(0, L))
            new_g = int(rng.integers(0, 4))
            if pos > 0 and INV_IDX[new_g] == w_pert[pos - 1]:
                continue
            if pos + 1 < L and INV_IDX[w_pert[pos + 1]] == new_g:
                continue
            w_pert[pos] = new_g
        w_pert = remove_cancellations(w_pert)
        while len(w_pert) < L:
            last = w_pert[-1] if w_pert else int(rng.integers(0, 4))
            choices = [g for g in range(4) if g != INV_IDX[last]]
            w_pert.append(int(rng.choice(choices)))
        w_pert = w_pert[:L]
        w_pert, d_pert = local_search_frob(w_pert, target, depth=ls_depth, max_iters=30)
        if d_pert < d_best - 1e-15:
            d_best = d_pert
            w_best = list(w_pert)
    return w_best, d_best


# ---------------------------------------------------------------------------
# Solovay-Kitaev level-1 iteration
# ---------------------------------------------------------------------------

def sk_level_1(base_braid: list[int], L_VW: int, trials_VW: int,
                ls_depth: int, basin_hops: int,
                k_target: int, rng: np.random.Generator) -> tuple[list[int], float, dict]:
    """One SK level on top of `base_braid` approximation of TARGETS[k_target].

    Returns (combined_braid, frob²_dist_to_TARGETS[k_target], diagnostics).
    """
    U_0 = eval_word(base_braid)
    target = TARGETS[k_target]
    # E = target · U_0⁻¹  (E ≈ I when U_0 ≈ target)
    U_0_inv = np.linalg.inv(U_0)
    E = target @ U_0_inv

    alpha_E, n_E = su2_axis_angle(E)
    # SU(2) balanced commutator decomposition
    V, W = balanced_commutator(E)

    # Sanity-check: V W V^-1 W^-1 == E?
    V_inv = np.linalg.inv(V)
    W_inv = np.linalg.inv(W)
    E_reconstructed = V @ W @ V_inv @ W_inv
    sk_decomp_error = float(np.linalg.norm(E - E_reconstructed, ord=2))

    # Find Fibonacci braids approximating V and W
    print(f"  Finding Fibonacci approximation of V (α_V ≈ {2*np.arcsin(np.sqrt(np.sin(alpha_E/2)/2)):.4f} rad)...")
    sys.stdout.flush()
    v_braid, v_d = approximate_unitary(V, L=L_VW, trials=trials_VW,
                                        ls_depth=ls_depth, basin_hops=basin_hops, rng=rng)
    print(f"  V_braid: L={len(v_braid)}, frob²={v_d:.6e} (target ‖V - V_braid‖_F²)")
    sys.stdout.flush()
    print(f"  Finding Fibonacci approximation of W...")
    sys.stdout.flush()
    w_braid, w_d = approximate_unitary(W, L=L_VW, trials=trials_VW,
                                        ls_depth=ls_depth, basin_hops=basin_hops, rng=rng)
    print(f"  W_braid: L={len(w_braid)}, frob²={w_d:.6e}")
    sys.stdout.flush()

    # Build combined braid: W · V · W⁻¹ · V⁻¹ · base_braid
    v_braid_inv = invert_word(v_braid)
    w_braid_inv = invert_word(w_braid)
    combined = w_braid + v_braid + w_braid_inv + v_braid_inv + base_braid
    combined = remove_cancellations(combined)

    M_combined = eval_word(combined)
    d_combined = frob_dist_sq(M_combined, target)
    diag = {
        "alpha_E": alpha_E,
        "sk_decomp_error": sk_decomp_error,
        "V_braid_frob_sq": v_d,
        "W_braid_frob_sq": w_d,
        "combined_braid_length": len(combined),
        "combined_frob_sq": d_combined,
    }
    return combined, d_combined, diag


def format_lean_literal(w: list[int]) -> str:
    if not w:
        return "[]"
    return "[" + ", ".join(LEAN_LABELS[g] for g in w) + "]"


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--L-base", type=int, default=46,
                        help="(Documentation) v7's base braid length (read from V7_BEST_BRAID).")
    parser.add_argument("--L-VW", type=int, default=46,
                        help="Length budget for approximating V, W in Fibonacci braids.")
    parser.add_argument("--trials", type=int, default=200000,
                        help="Random-search trials per V/W approximation.")
    parser.add_argument("--ls-depth", type=int, default=2,
                        help="Local-search window depth.")
    parser.add_argument("--basin-hops", type=int, default=30,
                        help="Basin-hopping perturbations per top word.")
    parser.add_argument("--seed", type=int, default=42, help="RNG seed.")
    parser.add_argument("--epsilon-target", type=float, default=1e-3,
                        help="Spectral target (default 1e-3).")
    args = parser.parse_args()

    print("Phase 6p Wave 3a.2.3c-substrate-upgrade-followup T-gate compiler v8")
    print("(Solovay-Kitaev level-1 iteration on v7 base)")
    print()
    print(f"  v7 base braid:     L = {len(V7_BEST_BRAID)}")
    print(f"  V/W L budget:      L_VW = {args.L_VW}")
    print(f"  V/W random trials: {args.trials}")
    print()

    rng = np.random.default_rng(args.seed)
    t0 = time.time()

    # Diagnose v7 base
    U_0 = eval_word(V7_BEST_BRAID)
    base_d_f, k_best = best_phase_frob_dist_sq(U_0)
    base_target = TARGETS[k_best]
    print(f"v7 base diagnostics:")
    print(f"  Target (best k):  ζ_80^{k_best} · T_NC")
    print(f"  Frobenius² to target: {base_d_f:.6e}  (sqrt = {np.sqrt(base_d_f):.6e})")
    base_d_spec = spectral_dist(U_0, base_target)
    print(f"  Spectral dist:    {base_d_spec:.6e}")
    print()

    # SK level-1 iteration
    print("Running Solovay-Kitaev level-1 iteration...")
    sys.stdout.flush()
    combined, d_combined, diag = sk_level_1(
        V7_BEST_BRAID,
        L_VW=args.L_VW,
        trials_VW=args.trials,
        ls_depth=args.ls_depth,
        basin_hops=args.basin_hops,
        k_target=k_best,
        rng=rng,
    )
    elapsed = time.time() - t0

    sk_target = TARGETS[k_best]
    M_combined = eval_word(combined)
    d_combined_spec = spectral_dist(M_combined, sk_target)
    d_combined_frob = np.sqrt(d_combined)

    print()
    print("=" * 70)
    print(f"v8 SK-level-1 result:")
    print(f"  Target: ζ_80^{k_best} · T_NC")
    print(f"  Frobenius dist = {d_combined_frob:.6e} (Frobenius² = {d_combined:.6e})")
    print(f"  Spectral dist  = {d_combined_spec:.6e}")
    print(f"  Length L       = {len(combined)}")
    print(f"  Achieved spectral ≤ {args.epsilon_target}? "
          f"{'YES' if d_combined_spec <= args.epsilon_target else 'NO'}")
    print(f"  Achieved Frobenius² ≤ {args.epsilon_target**2:.1e}? "
          f"{'YES' if d_combined <= args.epsilon_target**2 else 'NO'}")
    print()
    print(f"Diagnostics:")
    print(f"  E = target·U_0⁻¹ rotation angle: {diag['alpha_E']:.6e} rad")
    print(f"  SK decomp ‖E − V·W·V⁻¹·W⁻¹‖_op: {diag['sk_decomp_error']:.6e} (should be ~0)")
    print(f"  ‖V_braid - V‖_F² = {diag['V_braid_frob_sq']:.6e}")
    print(f"  ‖W_braid - W‖_F² = {diag['W_braid_frob_sq']:.6e}")
    print(f"  Wall time: {elapsed:.1f}s")
    print()
    print(f"Improvement vs v7 base:")
    print(f"  base spectral = {base_d_spec:.6e}, v8 spectral = {d_combined_spec:.6e}")
    print(f"  speedup factor = {base_d_spec / d_combined_spec if d_combined_spec > 0 else float('inf'):.2f}×")
    print()
    print(f"  Lean literal (BraidWord 3) [v8 SK-level-1 braid]:")
    print(f"    def tgateBraid_v8 : BraidWord 3 :=")
    print(f"      {format_lean_literal(combined)}")
    print()
    return 0 if d_combined_spec <= args.epsilon_target else 1


if __name__ == "__main__":
    sys.exit(main())
