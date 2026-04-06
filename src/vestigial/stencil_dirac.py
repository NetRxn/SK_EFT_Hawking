"""Matrix-free staggered Dirac operator via torch.roll() stencil.

Replaces the dense 8V x 8V matrix construction in hs_rhmc_torch.py with a
matrix-free operator that applies A @ v via nearest-neighbor stencil operations.
This reduces memory from O(V^2) to O(V), enabling L=12+ RHMC on workstations.

Memory comparison at L=12 (V=20736, dim=165888):
  Dense:       220 GB (8V x 8V float64)
  Matrix-free: ~130 MB (gauge field + CG workspace)

The operator is:
  (Av)[x] = sum_mu [ block_mu[x] @ v[x+mu] - block_mu[x-mu]^T @ v[x-mu] ]

where block_mu[x] = sum_a h[x,mu,a] * CG[a] is the site-dependent 8x8 hopping
matrix and CG[a] = J1 @ Gamma^a are the charge conjugation bilinear matrices.

For CG solves, A^dagger A = -A^2 (real antisymmetric A), so:
  apply_AtA(v) = -apply_A(apply_A(v))

Multi-shift CG works identically: shifts are diagonal (sigma * v), added after
the matrix-free A^dagger A application.

Lean: hs_fermion_matrix_antisymmetric (HubbardStratonovichRHMC.lean)
Source: Every production lattice QCD code (MILC, Grid, QUDA, openQCD)
"""

import torch
import numpy as np

# Reuse the CG bilinear matrices from hs_rhmc_torch (same source: constants.py)
from src.vestigial.hs_rhmc_torch import _CG_np


def precompute_blocks(h, CG, L):
    """Precompute site-dependent hopping matrices for all directions.

    block_mu[x] = sum_a h[x, mu, a] * CG[a]  is the 8x8 matrix coupling
    site x to its neighbor x+mu_hat.

    Args:
        h: h-field, shape (V, 4, 4) where h[site, mu, a]
        CG: charge conjugation bilinears, shape (4, 8, 8)
        L: lattice size

    Returns:
        blocks: shape (4, L, L, L, L, 8, 8) — hopping matrices per direction
    """
    V = L ** 4
    device = h.device
    dtype = h.dtype

    # Reshape h from flat (V, 4, 4) to spatial (L, L, L, L, 4, 4)
    h_spatial = h.reshape(L, L, L, L, 4, 4)

    # Contract over channel a for each direction mu:
    # h_spatial: (L, L, L, L, mu=4, a=4), CG: (a=4, I=8, J=8)
    # result[mu, x0, x1, x2, x3, I, J] = sum_a h[x0,x1,x2,x3, mu, a] * CG[a, I, J]
    blocks = torch.einsum('pqrsma,aij->mpqrsij', h_spatial, CG)

    return blocks


def apply_fermion_matrix(v_flat, blocks, L):
    """Apply the antisymmetric fermion matrix A to a vector, matrix-free.

    (Av)[x] = sum_mu [ block_mu[x] @ v[x+mu] - block_mu[x-mu]^T @ v[x-mu] ]

    The backward hop uses the TRANSPOSE of the block because the dense
    construction's antisymmetric scatter transposes the spinor indices:
    A[col, row] -= vals maps A[x, x-mu]_{J,I} -= block[x-mu]_{I,J}.

    Uses torch.roll() for periodic boundary shifts — no explicit neighbor
    tables, no dense matrix storage.

    Args:
        v_flat: input vector, shape (8V,) or (V, 8)
        blocks: precomputed hopping matrices from precompute_blocks,
                shape (4, L, L, L, L, 8, 8)
        L: lattice size

    Returns:
        result: (Av), same shape as v_flat
    """
    V = L ** 4
    was_flat = (v_flat.ndim == 1)

    # Reshape to spatial: (L, L, L, L, 8)
    v = v_flat.reshape(L, L, L, L, 8)
    result = torch.zeros_like(v)

    for mu in range(4):
        block_mu = blocks[mu]  # (L, L, L, L, 8, 8)

        # Forward hop: block_mu[x] @ v[x + mu_hat]
        v_fwd = torch.roll(v, shifts=-1, dims=mu)
        fwd = torch.einsum('...ij,...j->...i', block_mu, v_fwd)

        # Backward hop: block_mu[x-mu]^T @ v[x-mu]
        # Transpose is needed because the antisymmetric scatter in the dense
        # code maps A[nb*8+J, site*8+I] -= block[site, I, J], effectively
        # transposing the block for the backward direction.
        block_bwd = torch.roll(block_mu, shifts=+1, dims=mu)
        v_bwd = torch.roll(v, shifts=+1, dims=mu)
        bwd = torch.einsum('...ji,...j->...i', block_bwd, v_bwd)

        result = result + fwd - bwd

    if was_flat:
        return result.reshape(-1)
    return result


def apply_AtA(v_flat, blocks, L):
    """Apply A^dagger A = -A^2 to a vector, matrix-free.

    For real antisymmetric A: A^T = -A, so A^dagger A = A^T A = -A^2.
    This is positive semidefinite (eigenvalues of A are +/- i*lambda,
    eigenvalues of -A^2 are lambda^2 >= 0).

    Args:
        v_flat: input vector, shape (8V,)
        blocks: precomputed hopping matrices
        L: lattice size

    Returns:
        result: (A^dagger A v), shape (8V,)
    """
    Av = apply_fermion_matrix(v_flat, blocks, L)
    return -apply_fermion_matrix(Av, blocks, L)


def verify_against_dense(h_flat, L, n_vectors=10, device=None, dtype=None):
    """Verify matrix-free operator matches dense construction.

    Builds the dense matrix via build_fermion_matrix_torch, then compares
    A @ v (dense) vs apply_fermion_matrix(v) (matrix-free) for random vectors.

    Args:
        h_flat: h-field, shape (V, 4, 4)
        L: lattice size
        n_vectors: number of random vectors to test
        device: torch device
        dtype: torch dtype

    Returns:
        max_rel_error: maximum relative error across all test vectors
        max_abs_error: maximum absolute error across all test vectors
    """
    from src.vestigial.hs_rhmc_torch import build_fermion_matrix_torch

    if device is None:
        device = torch.device('cpu')
    if dtype is None:
        dtype = torch.float64

    h_t = torch.tensor(h_flat, dtype=dtype, device=device) if isinstance(
        h_flat, np.ndarray) else h_flat.to(dtype=dtype, device=device)

    # Dense matrix
    A_dense = build_fermion_matrix_torch(h_t, L, device=device, dtype=dtype)

    # Matrix-free blocks
    CG = torch.tensor(_CG_np, dtype=dtype, device=device)
    blocks = precompute_blocks(h_t, CG, L)

    V = L ** 4
    dim = 8 * V
    max_rel = 0.0
    max_abs = 0.0

    for _ in range(n_vectors):
        v = torch.randn(dim, dtype=dtype, device=device)

        # Dense
        Av_dense = A_dense @ v

        # Matrix-free
        Av_mf = apply_fermion_matrix(v, blocks, L)

        diff = torch.abs(Av_dense - Av_mf)
        abs_err = diff.max().item()
        norm = torch.norm(Av_dense).item()
        rel_err = abs_err / norm if norm > 1e-15 else abs_err

        max_rel = max(max_rel, rel_err)
        max_abs = max(max_abs, abs_err)

    return max_rel, max_abs


def make_cg_operator(blocks, L):
    """Create a callable operator for use in CG solvers.

    Returns a function that applies A^dagger A to a vector, compatible
    with the batched_cg interface (operates on flat vectors).

    Args:
        blocks: precomputed hopping matrices
        L: lattice size

    Returns:
        apply_fn: callable (v_flat) -> AtA @ v_flat
    """
    def apply_fn(v):
        return apply_AtA(v, blocks, L)
    return apply_fn
