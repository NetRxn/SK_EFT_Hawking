"""PyTorch MPS-accelerated HS+RHMC computational backend.

Replaces JAX inner loops with PyTorch operations on Apple Silicon GPU (MPS).
Key performance design:
  - Dense matrix ops on MPS (float32) for MD force computation
  - Mixed precision: float32 MPS for MD, float64 CPU for Metropolis accept/reject
  - Batch CG over shifts via sequential solve (MPS parallel within each solve)
  - Vectorized force computation via einsum on MPS

MPS does NOT support float64 (as of PyTorch 2.11). The mixed-precision strategy
is standard in lattice QCD: single-precision MD + double-precision accept/reject.
The MD trajectory is an approximate proposal regardless of precision (ε > 0 gives
ΔH ≠ 0), and detailed balance is maintained by the Metropolis test in float64.

The physics layer (formulas.py, constants.py, Lean proofs) is unchanged.
This module provides drop-in replacements for the hot paths in hs_rhmc.py.

Requires: torch >= 2.11 with MPS support (Apple Silicon)
  uv sync --extra gpu

Lean: HubbardStratonovichRHMC.lean (13 theorems, zero sorry)
Source: "HS+RHMC for ADW tetrad condensation..." (deep research)
"""

import torch
import numpy as np
from dataclasses import dataclass, field
from typing import Optional

from src.core.constants import RHMC_PARAMS, MAJORANA_GAMMA_8x8, MAJORANA_J1
from src.core.formulas import binder_cumulant_tetrad, binder_cumulant_metric


# ════════════════════════════════════════════════════════════════════
# Device setup — auto-detect MPS, fall back to CPU
# ════════════════════════════════════════════════════════════════════

def _get_device():
    """Return MPS device if available, else CPU.

    MPS is Apple Silicon GPU backend. Falls back gracefully to CPU
    if unavailable (e.g., on Linux or older macOS).
    """
    if torch.backends.mps.is_available():
        return torch.device('mps')
    return torch.device('cpu')

DEVICE = _get_device()
# float64 operations always on CPU (MPS doesn't support float64)
CPU = torch.device('cpu')


# ════════════════════════════════════════════════════════════════════
# Precomputed constants (torch tensors, computed once at import time)
# ════════════════════════════════════════════════════════════════════

# CG[a] = J₁ @ Γ^a — the charge conjugation bilinear matrices (4 × 8 × 8)
# These are the building blocks of A[h,U].
# Lean: kramers_holds_hs_matrix (HubbardStratonovichRHMC.lean)
# Source: Wei et al., PRL 116, 250601 (2016) — Kramers structure
_CG_np = np.array([MAJORANA_J1 @ MAJORANA_GAMMA_8x8[a] for a in range(4)])
_CG_TORCH = torch.tensor(_CG_np, dtype=torch.float32, device=DEVICE)  # (4, 8, 8)
_CG_CPU64 = torch.tensor(_CG_np, dtype=torch.float64, device=CPU)  # for Metropolis


# ════════════════════════════════════════════════════════════════════
# Neighbor table — precomputed for each L (cached)
#
# For a 4D periodic lattice of size L, neighbor[site, mu] = flat index
# of site + e_mu (with periodic boundary conditions).
# ════════════════════════════════════════════════════════════════════

_neighbor_cache = {}

def _get_neighbors(L):
    """Get neighbor table for lattice size L. Cached.

    Returns:
        neighbors: np.ndarray shape (V, 4), dtype int64
    """
    if L in _neighbor_cache:
        return _neighbor_cache[L]
    V = L ** 4
    coords = np.array(np.unravel_index(np.arange(V), (L, L, L, L))).T  # (V, 4)
    neighbors = np.zeros((V, 4), dtype=np.int64)
    for mu in range(4):
        nb_coords = coords.copy()
        nb_coords[:, mu] = (nb_coords[:, mu] + 1) % L
        neighbors[:, mu] = np.ravel_multi_index(nb_coords.T, (L, L, L, L))
    _neighbor_cache[L] = neighbors
    return neighbors


# ════════════════════════════════════════════════════════════════════
# Fermion matrix A[h,U] — dense, on MPS
#
# At β=0 with gauge-fixed identity links (S = I₈):
#   A_{(x,I),(y,J)} = Σ_a h^a_{x,μ} · CG[a]_{IJ} · δ_{y,x+μ} − (transpose)
#
# Lean: hs_fermion_matrix_antisymmetric (HubbardStratonovichRHMC.lean)
# Source: "HS+RHMC for ADW tetrad condensation..." Section 1
# ════════════════════════════════════════════════════════════════════


def build_fermion_matrix_torch(h_flat, L, device=None, dtype=None):
    """Build 8V×8V antisymmetric fermion matrix A[h] on specified device.

    At β=0 the gauge links are gauge-fixed to identity (S = I₈).
    A_{(x,I),(y,J)} = Σ_{μ,a} h^a_{x,μ} CG[a]_{IJ} δ_{y,x+μ̂} − (transpose)

    Vectorized: one einsum + one scatter per direction (4 total), no inner
    loops over spinor indices I,J. This is critical for MPS performance —
    each scatter is a single GPU kernel instead of 64 tiny ones per (mu, a).

    Lean: hs_fermion_matrix_antisymmetric (HubbardStratonovichRHMC.lean)
    Source: "HS+RHMC for ADW tetrad condensation..." Section 1

    Args:
        h_flat: shape (V, 4, 4) — h[site, mu, a]
        L: lattice size
        device: torch device (default: module DEVICE)
        dtype: torch dtype (default: float32)

    Returns:
        A: dense antisymmetric matrix, shape (8V, 8V)
    """
    if device is None:
        device = DEVICE
    if dtype is None:
        dtype = torch.float32
    V = L ** 4
    dim = 8 * V
    neighbors = _get_neighbors(L)

    CG = _CG_TORCH if dtype == torch.float32 else _CG_CPU64
    CG_dev = CG.to(device)

    if isinstance(h_flat, np.ndarray):
        h = torch.tensor(h_flat, dtype=dtype, device=device)
    elif h_flat.device.type == 'mps' and dtype == torch.float64:
        h = h_flat.cpu().to(dtype=dtype).to(device=device)
    else:
        h = h_flat.to(dtype=dtype, device=device)

    A = torch.zeros((dim, dim), dtype=dtype, device=device)

    # Precompute index grid (site × I, site × J) for scatter
    sites = torch.arange(V, dtype=torch.long, device=device)
    idx8 = torch.arange(8, dtype=torch.long, device=device)

    for mu in range(4):
        nbs_t = torch.tensor(neighbors[:, mu], dtype=torch.long, device=device)

        # block[site, I, J] = Σ_a h[site, mu, a] * CG[a, I, J]
        # einsum: (V, 4) × (4, 8, 8) → (V, 8, 8)
        block = torch.einsum('va,aij->vij', h[:, mu, :], CG_dev)

        # Build flat index arrays: row[v,I,J] = 8*v + I, col[v,I,J] = 8*nbs[v] + J
        row_idx = (sites[:, None, None] * 8 + idx8[None, :, None]).expand(V, 8, 8).reshape(-1)
        col_idx = (nbs_t[:, None, None] * 8 + idx8[None, None, :]).expand(V, 8, 8).reshape(-1)
        vals = block.reshape(-1)

        # Forward + antisymmetric (no collision: each site has unique neighbor per mu)
        A[row_idx, col_idx] += vals
        A[col_idx, row_idx] -= vals

    return A


# ════════════════════════════════════════════════════════════════════
# CG solver — iterative on MPS/CPU
#
# Solves (A†A + σ)x = b where A†A = -A² for real antisymmetric A.
#
# Lean: multishift_cg_shared_krylov (HubbardStratonovichRHMC.lean)
# Source: Jegerlehner, hep-lat/9612014 (1996)
# ════════════════════════════════════════════════════════════════════


# ── Solver strategy ──
# Batched LU: O(K·n³) direct, no iteration, used for float64 Metropolis
# Shared-Krylov CG: O(n²·√κ) with ONE matmul per iteration for ALL K shifts
#   → K× fewer matmuls than per-shift CG (16× for our 16-pole Zolotarev)
#   → Faster than batched LU for dim ≤ ~8192 where LU dominates
# Measured (2026-04-02): batched LU 119ms, shared-Krylov target ~10-30ms at dim=2048
BATCHED_LU_DIM_CUTOFF = 65536  # only use LU as fallback for huge matrices


def batched_cg(AtA, b, shifts, tol=1e-6, max_iter=500):
    """Solve (A†A + σ_k)x_k = b for all shifts with batched matmul.

    All K shifts run as independent CG solvers, but share ONE batched
    matrix-vector product per iteration: M @ P where P is (dim, K).
    This amortizes the dominant matmul cost across all shifts.

    AtA can be either a dense matrix (dim, dim) or a callable that applies
    A†A to a vector. When callable, each column of P is processed separately
    (matrix-free mode, Phase 5g).

    At dim=2048 with K=16 shifts:
    - Per-shift CG (sequential): 16 × ~250 iter × 1 matmul = 4000 matmuls
    - Batched CG: ~250 iter × 1 batched matmul = 250 matmuls (16× amortized)

    Unlike shared-Krylov CG, this avoids the numerically unstable ζ recurrence
    while achieving similar matmul savings via batched BLAS.

    Lean: multishift_cg_shared_krylov (HubbardStratonovichRHMC.lean)
    Source: Standard CG (Hestenes & Stiefel, 1952) with batched matvec

    Args:
        AtA: SPD matrix (dim, dim) OR callable (v -> AtA @ v)
        b: RHS vector (dim,)
        shifts: list of σ_k values (all ≥ 0)
        tol: relative residual tolerance
        max_iter: iteration cap

    Returns:
        (solutions, max_iter): list of solution tensors, max iterations used
    """
    K = len(shifts)
    dim = b.shape[0]
    is_callable = callable(AtA)
    device = b.device if is_callable else AtA.device
    dtype = b.dtype if is_callable else AtA.dtype

    sigma_t = torch.tensor(shifts, dtype=dtype, device=device)  # (K,)

    # Initialize all K systems: x=0, r=b, p=b
    X = torch.zeros(dim, K, dtype=dtype, device=device)     # (dim, K)
    R = b.unsqueeze(1).expand(dim, K).clone()                # (dim, K)
    P = R.clone()                                             # (dim, K)

    # Per-shift residual norms
    rr = torch.sum(R * R, dim=0)  # (K,)
    b_norm_sq = rr.clone()
    tol_sq = tol ** 2 * b_norm_sq

    converged = torch.zeros(K, dtype=torch.bool, device=device)

    n_iter = 0
    while not converged.all() and n_iter < max_iter:
        # ══ ONE (batched) matmul for ALL shifts ══
        if is_callable:
            # Matrix-free: apply operator to each shift's search direction
            MP = torch.stack([AtA(P[:, k]) for k in range(K)], dim=1)
        else:
            # Dense: AtA @ P: (dim, dim) @ (dim, K) → (dim, K)
            MP = AtA @ P

        # Add shift: (AtA + σ_k I) p_k = MP_k + σ_k * P_k
        AP = MP + sigma_t.unsqueeze(0) * P  # (dim, K)

        # Per-shift CG scalars
        pAp = torch.sum(P * AP, dim=0)  # (K,)
        alpha = rr / torch.clamp(pAp, min=1e-30)  # (K,)

        # Update solutions and residuals (vectorized over all shifts)
        X = X + alpha.unsqueeze(0) * P
        R = R - alpha.unsqueeze(0) * AP

        rr_new = torch.sum(R * R, dim=0)  # (K,)
        beta = rr_new / torch.clamp(rr, min=1e-30)  # (K,)

        P = R + beta.unsqueeze(0) * P

        # Check per-shift convergence
        converged = rr_new < tol_sq
        rr = rr_new
        n_iter += 1

    return [X[:, k] for k in range(K)], n_iter


def solve_batched_lu(AtA, b, shifts):
    """Fallback: batched LU solve for float64 Metropolis Hamiltonian.

    Direct solve — no iteration tolerance, exact to machine precision.
    Used for the Metropolis accept/reject step where detailed balance
    requires precise Hamiltonian evaluation.

    Args:
        AtA: SPD matrix (dim, dim)
        b: RHS vector (dim,)
        shifts: list of σ_k values

    Returns:
        list of solution tensors
    """
    dtype = AtA.dtype
    dim = AtA.shape[0]
    n_shifts = len(shifts)

    AtA_cpu = AtA.cpu().to(dtype=dtype)
    b_cpu = b.cpu().to(dtype=dtype)
    eye = torch.eye(dim, dtype=dtype)

    shifts_t = torch.tensor(shifts, dtype=dtype).reshape(-1, 1, 1)
    batch_M = AtA_cpu.unsqueeze(0).expand(n_shifts, -1, -1) + shifts_t * eye.unsqueeze(0)
    batch_b = b_cpu.unsqueeze(0).expand(n_shifts, -1)

    batch_x = torch.linalg.solve(batch_M, batch_b)

    orig_device = AtA.device
    return [batch_x[k].to(orig_device) for k in range(n_shifts)]


def _solve_asymptotic_shifts(AtA, b, shifts, device, dtype):
    """Direct solve for shifts σ >> spectral range where κ ≈ 1.

    For σ >> λ_max, (M + σI)^{-1} ≈ b/σ with condition number < 2.
    One CG refinement step gives machine-precision accuracy.

    Args:
        AtA: matrix (dim, dim) OR callable (v -> AtA @ v)
        b: RHS vector
        shifts: list of large σ values
        device, dtype: tensor parameters

    Returns:
        list of solution tensors
    """
    is_callable = callable(AtA)
    _apply = AtA if is_callable else lambda v: AtA @ v

    solutions = []
    for sigma in shifts:
        # Initial guess: x₀ = b / σ (exact in limit σ → ∞)
        x = b / sigma
        # One CG refinement step: residual then correction
        r = b - (_apply(x) + sigma * x)
        Ar = _apply(r) + sigma * r
        rAr = torch.dot(r, Ar)
        if rAr > 1e-30:
            alpha = torch.dot(r, r) / rAr
            x = x + alpha * r
        solutions.append(x)
    return solutions


def multi_shift_solve_torch(AtA, phi, shifts, tol=1e-6, max_iter=500,
                            lam_max=None, method='auto'):
    """Solve (A†A + σ_k)ψ_k = φ for all shifts.

    Hybrid strategy:
    - Shifts within spectral range: shared-Krylov CG (1 matmul/iter for all)
    - Shifts far beyond spectral range: direct solve (κ ≈ 1, 2 matmuls each)
    - float64 Metropolis: batched LU (exact, no iteration tolerance)
    - Matrix-free: AtA can be a callable (Phase 5g, L=12+ support)

    The Zolotarev poles span many orders of magnitude (e.g., [0, 10⁹] for
    spectral range [0.5, 130]). Only ~10 of 16 poles are "spectral" —
    the rest are asymptotic where (M + σI) has condition number < 2.

    Lean: multishift_cg_shared_krylov (HubbardStratonovichRHMC.lean)
    Source: Jegerlehner, hep-lat/9612014 (1996) — shared Krylov space

    Args:
        AtA: matrix A†A (dim, dim) on device, OR callable (v -> AtA @ v)
        phi: source vector (dim,) on device
        shifts: list/array of σ_k values
        tol: CG tolerance (shared_krylov only)
        max_iter: iteration cap
        lam_max: upper spectral bound of AtA (for shift classification)
        method: 'auto', 'shared_krylov', or 'batched_lu'

    Returns:
        list of solution tensors
    """
    n_shifts = len(shifts)
    float_shifts = [float(s) if not isinstance(s, float) else s for s in shifts]
    is_callable = callable(AtA)

    if is_callable:
        device = phi.device
        dtype = phi.dtype
    else:
        device = AtA.device
        dtype = AtA.dtype

    if method == 'auto':
        if is_callable:
            method = 'shared_krylov'  # matrix-free always uses CG
        else:
            method = 'batched_lu' if dtype == torch.float64 else 'shared_krylov'

    if method == 'batched_lu':
        if is_callable:
            raise ValueError("batched_lu requires a dense matrix, not a callable")
        return solve_batched_lu(AtA, phi, float_shifts)

    # Strategy by dimension:
    # - dim ≤ 4096 (L≤4): batched LU wins (one LAPACK call, excellent cache locality)
    #   Measured: 120ms vs 250-iteration CG at 8.4s (memory-bound: 250 × 32MB reads)
    # - dim > 4096 (L≥6): batched CG wins (O(n²√κ) < O(n³), fits in memory)
    #   Batched LU at dim=10368 needs 16 × 10368² × 4 = 6.9GB — tight on 16GB machines
    # - Matrix-free (callable AtA): always CG (no matrix to factor)
    dim = phi.shape[0]
    if not is_callable and dim <= 4096:
        return solve_batched_lu(AtA, phi, float_shifts)
    else:
        solutions, _ = batched_cg(AtA, phi, float_shifts, tol, max_iter)
        return solutions


# ════════════════════════════════════════════════════════════════════
# Zolotarev coefficients (reuse from hs_rhmc.py — numpy, no numba)
# ════════════════════════════════════════════════════════════════════

from src.vestigial.hs_rhmc import compute_zolotarev_coefficients  # noqa: E402


# ════════════════════════════════════════════════════════════════════
# Force computation — vectorized on MPS
#
# F_h = -h/(2g) + Σ_k α_k ψ_k^T (∂M/∂h) ψ_k
# where M = A†A = -A² and ∂M/∂h is sparse (only connects neighbors).
#
# Lean: rhmc_hamiltonian_conserved (HubbardStratonovichRHMC.lean)
# Source: "HS+RHMC for ADW tetrad condensation..." Section 3
# ════════════════════════════════════════════════════════════════════


def compute_forces_torch(h_flat, g, A, phi, alphas, betas, L, lam_max=None,
                         stencil_ops=None):
    """Compute h-field forces on MPS device.

    At β=0 with identity gauge links, only F_h is needed.
    Force = -∂H/∂h = -h/(2g) + pseudofermion contribution.

    The pseudofermion contribution involves CG solves and local
    contractions, all running on MPS for the mat-vec operations.

    Lean: rhmc_hamiltonian_conserved (HubbardStratonovichRHMC.lean)
    Source: "HS+RHMC for ADW tetrad condensation..." Section 3

    Args:
        h_flat: shape (V, 4, 4) on device
        g: coupling (float)
        A: fermion matrix (dim, dim) on device, or None if stencil_ops provided
        phi: pseudofermion (dim,) on device
        alphas: Zolotarev coefficients, 1D tensor on device
        betas: Zolotarev shifts, 1D tensor on device
        L: lattice size
        stencil_ops: optional dict with 'apply_A' and 'apply_AtA' callables
                     for matrix-free mode (Phase 5g). If provided, A is ignored.

    Returns:
        F_h: shape (V, 4, 4) on device — force on h-fields
    """
    V = L ** 4
    device = h_flat.device
    dtype = h_flat.dtype

    if stencil_ops is not None:
        apply_A = stencil_ops['apply_A']
        apply_AtA = stencil_ops['apply_AtA']
    else:
        AtA = -A @ A  # A†A = -A² for real antisymmetric
        apply_A = lambda v: A @ v  # noqa: E731
        apply_AtA = AtA

    # Solve all shifted systems (shared-Krylov for spectral, direct for asymptotic)
    shifts = [float(b) for b in betas]
    psi_list = multi_shift_solve_torch(apply_AtA, phi, shifts, tol=1e-6,
                                        max_iter=500, lam_max=lam_max)

    # Stack solutions and compute A @ ψ_k for each
    psi_all = torch.stack(psi_list)  # (n_poles, dim)
    Apsi_all = torch.stack([apply_A(psi) for psi in psi_list])  # (n_poles, dim)

    neighbors = _get_neighbors(L)
    CG = _CG_TORCH.to(device)  # (4, 8, 8)

    # Gaussian prior force: F = -h / (2g)
    F_h = -h_flat / (2.0 * g)

    n_poles = len(alphas)
    alphas_t = alphas if isinstance(alphas, torch.Tensor) else torch.tensor(
        alphas, dtype=dtype, device=device)

    # Reshape solutions to (n_poles, V, 8)
    psi_reshaped = psi_all.reshape(n_poles, V, 8)    # (K, V, 8)
    Apsi_reshaped = Apsi_all.reshape(n_poles, V, 8)  # (K, V, 8)

    # Vectorized force: batch over poles (k) and channels (a) simultaneously.
    # The bilinear form ψ_k · CG[a] · Aψ_k is per-pole (cannot pre-weight)
    # but we vectorize the contraction across all (a, k) pairs.
    for mu in range(4):
        nbs_t = torch.tensor(neighbors[:, mu], dtype=torch.long, device=device)

        psi_j = psi_reshaped[:, nbs_t, :]    # (K, V, 8) neighbor values
        Apsi_j = Apsi_reshaped[:, nbs_t, :]  # (K, V, 8)

        # CG[a] @ Aψ_k[neighbor]: (a,I,J) × (K,V,J) → (a,K,V,I)
        CG_Apsi_j = torch.einsum('aij,kvj->akvi', CG, Apsi_j)
        # ψ_k[site] · (CG[a] @ Aψ_k[neighbor]): (K,V,I) × (a,K,V,I) → (a,K,V)
        term1 = torch.einsum('kvi,akvi->akv', psi_reshaped, CG_Apsi_j)

        CG_psi_j = torch.einsum('aij,kvj->akvi', CG, psi_j)
        # Aψ_k[site] · (CG[a] @ ψ_k[neighbor])
        term2 = torch.einsum('kvi,akvi->akv', Apsi_reshaped, CG_psi_j)

        # Weight by α_k and sum over poles: (a, K, V) → (a, V)
        force_mu = torch.einsum('k,akv->av', alphas_t, -2.0 * (term1 - term2))
        F_h[:, mu, :] += force_mu.T  # (V, 4)

    return F_h


# ════════════════════════════════════════════════════════════════════
# Hamiltonian evaluation — float64 on CPU for Metropolis
#
# H = K + S_aux + S_PF
# where S_PF = φ · r(A†A)⁻¹ φ via rational approximation.
#
# Lean: rhmc_hamiltonian_nonneg (HubbardStratonovichRHMC.lean)
# Source: Duane, Kennedy, Pendleton & Roweth, PLB 195, 216 (1987)
# ════════════════════════════════════════════════════════════════════


def compute_hamiltonian_torch(h_flat, pi_h, g, phi, alpha_0, alphas, betas,
                              L, precision='float64'):
    """Compute H = K + S_aux + S_PF.

    For Metropolis accept/reject: uses float64 on CPU for exact detailed balance.
    For MD diagnostic: can use float32 on MPS.

    Lean: rhmc_hamiltonian_nonneg (HubbardStratonovichRHMC.lean)
    Source: Duane et al., PLB 195, 216 (1987), Eq. (2.5)

    Args:
        h_flat: shape (V, 4, 4) — h-field configuration
        pi_h: shape (V, 4, 4) — conjugate momenta
        g: coupling
        phi: pseudofermion vector
        alpha_0: Zolotarev constant term
        alphas: Zolotarev residues (numpy array)
        betas: Zolotarev shifts (numpy array)
        L: lattice size
        precision: 'float64' (CPU, Metropolis) or 'float32' (MPS, diagnostic)

    Returns:
        H: total Hamiltonian (float)
    """
    if precision == 'float64':
        dev = CPU
        dt = torch.float64
    else:
        dev = DEVICE
        dt = torch.float32

    def _to_dev(t, dt, dev):
        """Move tensor to device+dtype, handling MPS→float64 path."""
        if isinstance(t, np.ndarray):
            return torch.tensor(t, dtype=dt, device=dev)
        if t.device.type == 'mps' and dt == torch.float64:
            return t.cpu().to(dtype=dt).to(device=dev)
        return t.to(dtype=dt, device=dev)

    h = _to_dev(h_flat, dt, dev)
    pi = _to_dev(pi_h, dt, dev)
    p = _to_dev(phi, dt, dev)

    K = 0.5 * torch.sum(pi ** 2)
    S_aux = torch.sum(h ** 2) / (4.0 * g)

    # Build A in the target precision
    A = build_fermion_matrix_torch(h, L, device=dev, dtype=dt)
    AtA = -A @ A

    # CG tolerance: tight for float64 Metropolis, relaxed for float32
    cg_tol = 1e-12 if precision == 'float64' else 1e-6
    shifts = [float(b) for b in betas]
    psi_list = multi_shift_solve_torch(AtA, p, shifts, tol=cg_tol, max_iter=5000)

    S_PF = alpha_0 * torch.dot(p, p)
    for k in range(len(betas)):
        S_PF = S_PF + float(alphas[k]) * torch.dot(p, psi_list[k])

    return float(K + S_aux + S_PF)


# ════════════════════════════════════════════════════════════════════
# Pseudofermion heat bath
#
# φ = r_HB(A†A) · ξ where r_HB ≈ x^{-1/8}
# (NOT x^{-1} — that gives wrong distribution and h-field blowup)
#
# Lean: hs_gaussian_identity_zero (HubbardStratonovichRHMC.lean)
# Source: Clark & Kennedy, NPB PS 129, 850 (2004), Section 2.2
# ════════════════════════════════════════════════════════════════════


def pseudofermion_heatbath_torch(A, dim, rng, alpha_0_hb, alphas_hb, betas_hb,
                                lam_max=None):
    """Generate pseudofermion from correct distribution using x^{-1/8}.

    φ = r_HB(A†A) · ξ where r_HB ≈ x^{-1/8} and ξ ~ N(0,1).

    Lean: hs_gaussian_identity_zero (HubbardStratonovichRHMC.lean)
    Source: Clark & Kennedy, NPB PS 129, 850 (2004), Section 2.2

    Args:
        A: fermion matrix on device
        dim: matrix dimension
        rng: torch.Generator
        alpha_0_hb: constant term for x^{-1/8} approximation
        alphas_hb: residues (numpy array)
        betas_hb: shifts (numpy array)

    Returns:
        phi: pseudofermion vector on device
    """
    device = A.device
    dtype = A.dtype
    xi = torch.randn(dim, dtype=dtype, device=device, generator=rng)
    AtA = -A @ A

    shifts = [float(b) for b in betas_hb]
    psi_list = multi_shift_solve_torch(AtA, xi, shifts, tol=1e-6, max_iter=500,
                                        lam_max=lam_max)

    phi = alpha_0_hb * xi
    for k in range(len(betas_hb)):
        phi = phi + float(alphas_hb[k]) * psi_list[k]
    return phi


# ════════════════════════════════════════════════════════════════════
# Measurements — O(V), no CG needed
#
# Lean: binder_tetrad_prefactor, binder_metric_prefactor (MajoranaKramers.lean)
# ════════════════════════════════════════════════════════════════════


def measure_h_observables_torch(h_flat, L):
    """h-field order parameters. O(V), no CG.

    Tetrad proxy: m_h^a_μ = (1/V) Σ_x h^a_{x,μ}; |m_h|² (d=16 Binder: 8/9)
    Metric proxy: M_μν = (1/V) Σ_{x,a} h^a_{x,μ} h^a_{x,ν}; trQ² (d=9 Binder: 9/11)

    Lean: binder_tetrad_prefactor, binder_metric_prefactor (MajoranaKramers.lean)
    Source: Project-original (h ∝ E at mean-field saddle point)

    Returns:
        (h_sq, tet_m2, trQ2) as Python floats
    """
    V = L ** 4
    if isinstance(h_flat, torch.Tensor):
        h = h_flat
    else:
        h = torch.tensor(h_flat, dtype=torch.float32, device=DEVICE)

    h_sq = float(torch.mean(h ** 2))

    # Tetrad proxy: volume average then norm squared
    m_h = torch.mean(h, dim=0)  # (4, 4)
    tet_m2 = float(torch.sum(m_h ** 2))

    # Metric proxy: Q_μν = M_μν - (Tr M / 4) I₄
    M = torch.einsum('vma,vna->mn', h, h) / V
    tr = torch.trace(M)
    Q = M - (tr / 4.0) * torch.eye(4, dtype=h.dtype, device=h.device)
    trQ2 = float(torch.sum(Q * Q))

    return h_sq, tet_m2, trQ2


# ════════════════════════════════════════════════════════════════════
# Full RHMC trajectory + production runner
#
# Algorithm: Omelyan 2MN integrator with 3 force evaluations per step.
# Mixed precision: float32 MPS for MD hot path, float64 CPU for Metropolis.
#
# Lean: omelyan_second_order_symplectic, omelyan_time_reversible,
#       rhmc_detailed_balance (HubbardStratonovichRHMC.lean)
# Source: Omelyan et al., CPC 146, 188 (2002); Duane et al., PLB 195, 216 (1987)
# ════════════════════════════════════════════════════════════════════


@dataclass
class RHMCResultTorch:
    """Results from PyTorch MPS-accelerated RHMC.

    Same fields as RHMCResultJax for compatibility with production runner.
    """
    h_tetrad_m2: float = 0.0
    h_tetrad_m4: float = 0.0
    binder_tetrad: float = 0.0
    h_metric_m2: float = 0.0
    h_metric_m4: float = 0.0
    binder_metric: float = 0.0
    avg_plaquette: list = field(default_factory=list)
    h_sq_history: list = field(default_factory=list)
    delta_H_history: list = field(default_factory=list)
    acceptance_history: list = field(default_factory=list)
    acceptance_rate: float = 0.0
    tetrad_m2_history: list = field(default_factory=list)
    metric_trQ2_history: list = field(default_factory=list)
    n_measurements: int = 0
    g: float = 0.0
    beta: float = 0.0
    L: int = 0
    sign_free: bool = True


def run_rhmc_torch(L, g, beta=0.0, n_traj=200, n_therm=50, n_meas_skip=5,
                   n_md_steps=10, tau=1.0, n_poles=16, seed=42):
    """Run HS+RHMC with PyTorch MPS-accelerated backend.

    At β=0: gauge links fixed to identity, only h-fields evolve.
    Mixed precision: float32 on MPS for MD, float64 on CPU for Metropolis.

    Performance design:
      - Matrix building: float32 on MPS
      - CG for MD forces: float32 on MPS (tol=1e-6)
      - CG for Metropolis H: float64 on CPU (tol=1e-12)
      - 3 force evals per Omelyan step × n_md_steps = bottleneck is CG on MPS

    Lean: adw_sign_problem_free (MajoranaKramers.lean)
    Lean: omelyan_second_order_symplectic, rhmc_detailed_balance
          (HubbardStratonovichRHMC.lean)
    Source: "HS+RHMC for ADW tetrad condensation..." (deep research)

    Args:
        L: lattice size
        g: four-fermion coupling
        beta: Wilson coupling (0.0 for gauge-fixed — correct at β=0)
        n_traj: total trajectories
        n_therm: thermalization trajectories
        n_meas_skip: trajectories between measurements
        n_md_steps: Omelyan steps per trajectory
        tau: MD trajectory length
        n_poles: Zolotarev poles (same for MD+MC — avoids S_PF mismatch)
        seed: random seed

    Returns:
        RHMCResultTorch with observables, histories, and diagnostics
    """
    V = L ** 4
    dim = 8 * V
    eps = tau / n_md_steps
    lam = 0.1932  # Omelyan 2MN parameter
    # Measured (2026-04-02): λ=0.1932 gives O(ε⁴) leading error,
    # 3 force evals per step. C≈44 at L=2 (documented in RHMC_PARAMS).

    # Device selection: CPU for small matrices (dim ≤ cutoff),
    # MPS for large matrices where GPU matmul dominates kernel launch overhead.
    # Measured (2026-04-02): CPU batched solve 119ms vs MPS 1947ms at dim=2048.
    # MPS wins only when dim >> 8192 (CG matmul dominates launch overhead).
    if dim <= BATCHED_LU_DIM_CUTOFF:
        device = CPU    # avoid MPS↔CPU transfer overhead
        dtype = torch.float32
    else:
        device = DEVICE  # MPS for large matrices
        dtype = torch.float32

    result = RHMCResultTorch(g=g, beta=beta, L=L)
    rng = torch.Generator(device=device)
    rng.manual_seed(seed)
    rng_cpu = torch.Generator(device=CPU)
    rng_cpu.manual_seed(seed + 7919)

    # Initialize h-field: h ~ N(0, √(2g))
    sigma_h = np.sqrt(2.0 * g) if g > 0 else 1.0
    h = torch.randn(V, 4, 4, dtype=dtype, device=device, generator=rng) * sigma_h

    # Estimate spectral range from initial config (CPU float64 for eigenvalues)
    A_init = build_fermion_matrix_torch(h, L, device=CPU, dtype=torch.float64)
    AtA_init = -A_init @ A_init
    eigvals = torch.linalg.eigvalsh(AtA_init)
    eigvals_pos = eigvals[eigvals > 1e-10]
    lam_min = float(torch.min(eigvals_pos)) * 0.8
    lam_max = float(torch.max(eigvals_pos)) * 1.2

    # Zolotarev coefficients (same for MD, HB, MC — avoids S_PF mismatch)
    # Measured (2026-04-02): same-precision eliminates S_PF bias artifacts.
    a0, alphas, betas_z = compute_zolotarev_coefficients(n_poles, lam_min, lam_max, -0.25)
    a0_hb, alphas_hb, betas_hb = compute_zolotarev_coefficients(
        n_poles, lam_min, lam_max, -0.125)

    # Convert to torch tensors on MPS for force computation
    alphas_t = torch.tensor(alphas, dtype=dtype, device=device)
    betas_t = torch.tensor(betas_z, dtype=dtype, device=device)

    n_accepted = 0

    for traj in range(n_traj):
        # Build A from current h (float32, MPS)
        A = build_fermion_matrix_torch(h, L, device=device, dtype=dtype)

        # Pseudofermion heat bath: φ = r_HB(A†A) ξ
        phi = pseudofermion_heatbath_torch(A, dim, rng,
                                           float(a0_hb), alphas_hb, betas_hb,
                                           lam_max=lam_max)

        # Refresh momenta
        pi_h = torch.randn_like(h, generator=rng)

        # Store old state for reject
        h_old = h.clone()

        # Compute H_old (float64, CPU — exact for Metropolis)
        H_old = compute_hamiltonian_torch(h, pi_h, g, phi, float(a0),
                                           alphas, betas_z, L, precision='float64')

        # ── Omelyan MD trajectory with FSAL ──
        # FSAL (First Same As Last): last force of step k = first force of step k+1.
        # Saves 1 force eval per step (except first): 3N → 2N+1 force evals.
        # Source: Omelyan et al., CPC 146, 188 (2002), Section 4
        A_cur = build_fermion_matrix_torch(h, L, device=device, dtype=dtype)
        F_h = compute_forces_torch(h, g, A_cur, phi, alphas_t, betas_t, L,
                                    lam_max=lam_max)

        for step in range(n_md_steps):
            # λε kick (uses F_h from end of previous step, or initial)
            pi_h = pi_h + lam * eps * F_h

            # ε/2 drift
            h = h + (eps / 2) * pi_h

            A_cur = build_fermion_matrix_torch(h, L, device=device, dtype=dtype)
            F_h = compute_forces_torch(h, g, A_cur, phi, alphas_t, betas_t, L,
                                        lam_max=lam_max)

            # (1-2λ)ε kick
            pi_h = pi_h + (1 - 2 * lam) * eps * F_h

            # ε/2 drift
            h = h + (eps / 2) * pi_h

            A_cur = build_fermion_matrix_torch(h, L, device=device, dtype=dtype)
            F_h = compute_forces_torch(h, g, A_cur, phi, alphas_t, betas_t, L,
                                        lam_max=lam_max)

            # λε kick
            pi_h = pi_h + lam * eps * F_h

        # Compute H_new (float64, CPU — exact for Metropolis)
        H_new = compute_hamiltonian_torch(h, pi_h, g, phi, float(a0),
                                           alphas, betas_z, L, precision='float64')

        delta_H = H_new - H_old
        result.delta_H_history.append(delta_H)

        # Metropolis accept/reject
        accept = (delta_H <= 0) or (
            float(torch.rand(1, generator=rng_cpu)) < np.exp(min(-delta_H, 0)))
        if accept:
            n_accepted += 1
            result.acceptance_history.append(1.0)
        else:
            h = h_old
            result.acceptance_history.append(0.0)

        # Measure (after thermalization, every n_meas_skip trajectories)
        if traj >= n_therm and (traj - n_therm) % n_meas_skip == 0:
            h_sq, tet_m2, trQ2 = measure_h_observables_torch(h, L)
            result.h_sq_history.append(h_sq)
            result.tetrad_m2_history.append(tet_m2)
            result.metric_trQ2_history.append(trQ2)
            result.n_measurements += 1

    # Summary statistics
    if result.n_measurements > 0:
        tet = np.array(result.tetrad_m2_history)
        met = np.array(result.metric_trQ2_history)
        result.h_tetrad_m2 = float(np.mean(tet))
        result.h_tetrad_m4 = float(np.mean(tet ** 2))
        if result.h_tetrad_m2 > 0:
            result.binder_tetrad = binder_cumulant_tetrad(
                result.h_tetrad_m2, result.h_tetrad_m4)
        result.h_metric_m2 = float(np.mean(met))
        result.h_metric_m4 = float(np.mean(met ** 2))
        if result.h_metric_m2 > 0:
            result.binder_metric = binder_cumulant_metric(
                result.h_metric_m2, result.h_metric_m4)

    result.acceptance_rate = n_accepted / max(n_traj, 1)
    return result
