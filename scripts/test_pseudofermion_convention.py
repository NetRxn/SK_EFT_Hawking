#!/usr/bin/env python3
"""Empirical test: Pfaffian RHMC pseudofermion convention.

Compares three approaches at L=2 (dim=128, exact computation feasible):
  1. Exact MC: Metropolis with explicit log det(A†A) — gold standard
  2. RHMC x^{-1/4}: Current code (gives det^{1/8} if real convention is wrong)
  3. RHMC x^{-1/2}: Proposed fix (gives det^{1/4} for real pseudofermion)

The observable ⟨h²⟩ should match between the correct RHMC and the exact MC.
Whichever RHMC matches the exact MC has the right pseudofermion convention.

Usage:
  .venv/bin/python scripts/test_pseudofermion_convention.py
"""

import numpy as np
import time
from src.core.constants import MAJORANA_GAMMA_8x8, MAJORANA_J1
from src.vestigial.hs_rhmc import compute_zolotarev_coefficients

# ═══════════════════════════════════════════════════════════════
# Build full antisymmetric matrix A[h] at L=2
# ═══════════════════════════════════════════════════════════════

L = 2
V = L**4  # 16 sites
DIM = 8 * V  # 128
g = 2.0

# CG matrices: CG[a] = J1 @ Gamma[a]
CG = np.array([MAJORANA_J1 @ MAJORANA_GAMMA_8x8[a] for a in range(4)])

# Build neighbor table (periodic L^4 lattice)
def build_neighbors(l):
    v = l**4
    fwd = np.zeros((v, 4), dtype=int)
    for site in range(v):
        x = np.array([
            site // (l**3),
            (site // (l**2)) % l,
            (site // l) % l,
            site % l
        ])
        for mu in range(4):
            xp = x.copy()
            xp[mu] = (xp[mu] + 1) % l
            fwd[site, mu] = xp[0]*l**3 + xp[1]*l**2 + xp[2]*l + xp[3]
    return fwd

FWD = build_neighbors(L)

def build_A_matrix(h):
    """Build full 8V×8V antisymmetric matrix A[h]."""
    A = np.zeros((DIM, DIM))
    for site in range(V):
        for mu in range(4):
            nb = FWD[site, mu]
            for a in range(4):
                h_val = h[site, mu, a]
                if abs(h_val) < 1e-15:
                    continue
                # A_{(site,I),(nb,J)} = h * CG[a]_{I,J}
                for I in range(8):
                    for J in range(8):
                        c = CG[a, I, J]
                        if abs(c) < 1e-15:
                            continue
                        A[8*site + I, 8*nb + J] += c * h_val
                        # Antisymmetric: A_{(nb,J),(site,I)} = -c * h_val
                        A[8*nb + J, 8*site + I] -= c * h_val
    return A


def log_det_AtA(h):
    """Compute log det(A†A) for configuration h."""
    A = build_A_matrix(h)
    AtA = A.T @ A  # = -A² for antisymmetric A
    # Use eigenvalues for numerical stability
    eigs = np.linalg.eigvalsh(AtA)
    eigs = np.maximum(eigs, 1e-30)  # clamp for log
    return np.sum(np.log(eigs))


# ═══════════════════════════════════════════════════════════════
# Exact MC: Metropolis with explicit det(A†A)^{1/4}
# ═══════════════════════════════════════════════════════════════

def exact_mc(g, alpha, n_traj, n_therm, seed=42):
    """Run Metropolis MC with weight exp(-h²/4g) × det(A†A)^alpha.

    alpha=1/4 gives the correct Pf(A) weight.
    alpha=1/8 gives what single-real-pseudofermion x^{-1/4} would give.
    """
    rng = np.random.default_rng(seed)
    h = rng.normal(0, np.sqrt(2*g), (V, 4, 4))

    s_aux = np.sum(h**2) / (4*g)
    ld = log_det_AtA(h)

    h_sq_list = []
    n_accept = 0
    eps = 0.3  # proposal width (tuned for ~50% acceptance at L=2)

    for t in range(n_traj):
        # Propose
        h_new = h + rng.normal(0, eps, h.shape)
        s_aux_new = np.sum(h_new**2) / (4*g)
        ld_new = log_det_AtA(h_new)

        # log acceptance ratio: -dS_aux + alpha * d(log det)
        log_ratio = -(s_aux_new - s_aux) + alpha * (ld_new - ld)

        if np.log(rng.random()) < log_ratio:
            h = h_new
            s_aux = s_aux_new
            ld = ld_new
            n_accept += 1

        if t >= n_therm:
            h_sq_list.append(np.mean(h**2))

    return {
        'h_sq': np.mean(h_sq_list),
        'h_sq_err': np.std(h_sq_list) / np.sqrt(len(h_sq_list)),
        'accept': n_accept / n_traj,
    }


# ═══════════════════════════════════════════════════════════════
# RHMC tests via Rust backend
# ═══════════════════════════════════════════════════════════════

def run_rhmc(power_action, power_hb, n_traj=200, n_therm=50, seed=42):
    """Run RHMC with given Zolotarev powers."""
    import sk_eft_rhmc

    # CG stencil entries
    cg_a, cg_i, cg_j, cg_val = [], [], [], []
    for a in range(4):
        for I in range(8):
            for J in range(8):
                v = CG[a, I, J]
                if abs(v) > 1e-15:
                    cg_a.append(a); cg_i.append(I); cg_j.append(J); cg_val.append(v)
    cg_a = np.array(cg_a, dtype=np.int64)
    cg_i = np.array(cg_i, dtype=np.int64)
    cg_j = np.array(cg_j, dtype=np.int64)
    cg_val = np.array(cg_val, dtype=np.float64)

    # Spectral range for L=2 (from Lanczos)
    lmin, lmax = sk_eft_rhmc.estimate_spectral_range_py(L, g, seed, 30,
                                                         cg_a, cg_i, cg_j, cg_val)
    eps = max(lmin * 0.5, 1e-4)
    lmax_padded = lmax * 1.5

    n_poles = 16 if abs(power_action) <= 0.25 else 24
    a0, alphas, betas = compute_zolotarev_coefficients(
        n_poles, eps, lmax_padded, power=power_action)
    a0_hb, alphas_hb, betas_hb = compute_zolotarev_coefficients(
        n_poles, eps, lmax_padded, power=power_hb)

    r = sk_eft_rhmc.run_rhmc_rust(
        L, g, n_traj, n_therm, 1, 10, 1.0,
        float(a0), alphas, betas,
        float(a0_hb), alphas_hb, betas_hb,
        seed, cg_a, cg_i, cg_j, cg_val)

    h_sq = np.array(r['h_sq_history'])
    return {
        'h_sq': np.mean(h_sq),
        'h_sq_err': np.std(h_sq) / np.sqrt(len(h_sq)),
        'accept': r['acceptance_rate'],
    }


# ═══════════════════════════════════════════════════════════════
# Run all tests
# ═══════════════════════════════════════════════════════════════

if __name__ == '__main__':
    print("=" * 70)
    print("Pfaffian RHMC Pseudofermion Convention Test (L=2, g=2.0)")
    print("=" * 70)
    print()

    N_EXACT = 5000
    N_THERM = 1000
    N_RHMC = 200
    N_RHMC_THERM = 50

    # 1. Exact MC with det^{1/4} (the correct Pfaffian weight)
    print("1. Exact MC: det(A†A)^{1/4} weight (gold standard)...")
    t0 = time.time()
    exact_quarter = exact_mc(g, alpha=0.25, n_traj=N_EXACT, n_therm=N_THERM, seed=42)
    print(f"   ⟨h²⟩ = {exact_quarter['h_sq']:.4f} ± {exact_quarter['h_sq_err']:.4f}, "
          f"accept = {exact_quarter['accept']:.2f}, time = {time.time()-t0:.1f}s")

    # 2. Exact MC with det^{1/8} (what single-real x^{-1/4} gives)
    print("2. Exact MC: det(A†A)^{1/8} weight (wrong power)...")
    t0 = time.time()
    exact_eighth = exact_mc(g, alpha=0.125, n_traj=N_EXACT, n_therm=N_THERM, seed=42)
    print(f"   ⟨h²⟩ = {exact_eighth['h_sq']:.4f} ± {exact_eighth['h_sq_err']:.4f}, "
          f"accept = {exact_eighth['accept']:.2f}, time = {time.time()-t0:.1f}s")

    # 3. Exact MC with det^0 (pure Gaussian, no fermion)
    print("3. Exact MC: no fermion determinant (pure Gaussian)...")
    t0 = time.time()
    exact_gauss = exact_mc(g, alpha=0.0, n_traj=N_EXACT, n_therm=N_THERM, seed=42)
    print(f"   ⟨h²⟩ = {exact_gauss['h_sq']:.4f} ± {exact_gauss['h_sq_err']:.4f}, "
          f"accept = {exact_gauss['accept']:.2f}, time = {time.time()-t0:.1f}s")
    print(f"   (Expected: 2g = {2*g:.1f})")

    # 4. RHMC with current x^{-1/4} action
    print("\n4. RHMC: action=x^{-1/4}, HB=x^{-1/8} (CURRENT CODE)...")
    t0 = time.time()
    rhmc_quarter = run_rhmc(power_action=-0.25, power_hb=-0.125,
                            n_traj=N_RHMC, n_therm=N_RHMC_THERM, seed=42)
    print(f"   ⟨h²⟩ = {rhmc_quarter['h_sq']:.4f} ± {rhmc_quarter['h_sq_err']:.4f}, "
          f"accept = {rhmc_quarter['accept']:.2f}, time = {time.time()-t0:.1f}s")

    # 5. RHMC with x^{-1/2} action (proposed fix)
    print("5. RHMC: action=x^{-1/2}, HB=x^{-1/4} (PROPOSED FIX)...")
    t0 = time.time()
    rhmc_half = run_rhmc(power_action=-0.50, power_hb=-0.25,
                         n_traj=N_RHMC, n_therm=N_RHMC_THERM, seed=42)
    print(f"   ⟨h²⟩ = {rhmc_half['h_sq']:.4f} ± {rhmc_half['h_sq_err']:.4f}, "
          f"accept = {rhmc_half['accept']:.2f}, time = {time.time()-t0:.1f}s")

    # Summary
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"  Exact det^{{1/4}} (Pf):  ⟨h²⟩ = {exact_quarter['h_sq']:.4f} ± {exact_quarter['h_sq_err']:.4f}")
    print(f"  Exact det^{{1/8}}:       ⟨h²⟩ = {exact_eighth['h_sq']:.4f} ± {exact_eighth['h_sq_err']:.4f}")
    print(f"  Exact Gaussian:        ⟨h²⟩ = {exact_gauss['h_sq']:.4f} ± {exact_gauss['h_sq_err']:.4f}")
    print(f"  RHMC x^{{-1/4}} (curr):  ⟨h²⟩ = {rhmc_quarter['h_sq']:.4f} ± {rhmc_quarter['h_sq_err']:.4f}")
    print(f"  RHMC x^{{-1/2}} (fix):   ⟨h²⟩ = {rhmc_half['h_sq']:.4f} ± {rhmc_half['h_sq_err']:.4f}")
    print()

    # Determine which matches
    d_quarter = abs(rhmc_quarter['h_sq'] - exact_quarter['h_sq'])
    d_eighth = abs(rhmc_quarter['h_sq'] - exact_eighth['h_sq'])
    d_fix_quarter = abs(rhmc_half['h_sq'] - exact_quarter['h_sq'])

    print(f"  |RHMC_curr - Exact_1/4| = {d_quarter:.4f}")
    print(f"  |RHMC_curr - Exact_1/8| = {d_eighth:.4f}")
    print(f"  |RHMC_fix  - Exact_1/4| = {d_fix_quarter:.4f}")
    print()

    if d_eighth < d_quarter:
        print("  CONCLUSION: Current RHMC matches det^{1/8}, NOT det^{1/4}.")
        print("  → BUG CONFIRMED: simulating Pf^{1/2} instead of Pf.")
    elif d_quarter < d_eighth:
        print("  CONCLUSION: Current RHMC matches det^{1/4}.")
        print("  → No bug: x^{-1/4} is correct for this pseudofermion setup.")
    else:
        print("  INCONCLUSIVE: need more statistics or different observable.")

    if d_fix_quarter < d_quarter:
        print(f"  → x^{{-1/2}} fix is CLOSER to correct Pf weight.")
    elif d_fix_quarter > d_quarter:
        print(f"  → x^{{-1/2}} fix is WORSE. Current x^{{-1/4}} may be correct.")
