"""Batched matrix-free stencil for the HS+RHMC fermion operator (GPU port).

The dense scaffold (`hs_rhmc_torch.build_fermion_matrix_torch`) materializes the
8V×8V matrix A — O(dim²) memory (110 GB at L=12) and O(dim³) solves. This module
applies A matrix-free as an 8-neighbor stencil, with arbitrary LEADING BATCH
dimensions so couplings × replicas × Zolotarev poles fuse into one wide kernel
that saturates the GPU (a single coupling's matvec is too small to do so).

Operator (β=0, identity links), matching the dense oracle exactly:
    A_{(x,I),(y,J)} = Σ_{μ,a} h^a_{x,μ} CG[a]_{IJ} δ_{y,x+μ̂} − (transpose)
⟹   (Aψ)_{x,I} = Σ_μ  Σ_J block^μ_{x,I,J} ψ_{x+μ̂,J}          (forward hop)
               − Σ_μ ( Σ_J block^μ_{·,J,I} ψ_{·,J} )|_{x−μ̂}  (backward hop)
with block^μ_{x,I,J} = Σ_a h^a_{x,μ} CG[a]_{IJ}.

CG operator for the multishift solver: A†A = −A² (A real antisymmetric ⟹ PSD).
"""
import numpy as np
import torch

from src.vestigial.hs_rhmc_torch import _CG_np   # (4, 8, 8) — same convention as the dense oracle

_nbr_cache = {}


def neighbor_tables(L, device):
    """Forward/backward neighbor index tables, each (V, 4) long.
    fwd[x, μ] = flat(x + ê_μ),  back[x, μ] = flat(x − ê_μ)  (periodic)."""
    key = (L, str(device))
    if key in _nbr_cache:
        return _nbr_cache[key]
    V = L ** 4
    coords = np.array(np.unravel_index(np.arange(V), (L, L, L, L))).T  # (V, 4)
    fwd = np.zeros((V, 4), np.int64)
    back = np.zeros((V, 4), np.int64)
    for mu in range(4):
        f = coords.copy(); f[:, mu] = (f[:, mu] + 1) % L
        b = coords.copy(); b[:, mu] = (b[:, mu] - 1) % L
        fwd[:, mu] = np.ravel_multi_index(f.T, (L, L, L, L))
        back[:, mu] = np.ravel_multi_index(b.T, (L, L, L, L))
    out = (torch.tensor(fwd, dtype=torch.long, device=device),
           torch.tensor(back, dtype=torch.long, device=device))
    _nbr_cache[key] = out
    return out


def hopping_blocks(h, L, device=None, dtype=None):
    """block[..., x, μ, I, J] = Σ_a h[..., x, μ, a] · CG[a, I, J].

    h: (*batch, V, 4, 4) [site, μ, a].  Returns (*batch, V, 4, 8, 8)
    (μ at axis −3, so block^μ = blocks[..., μ, :, :])."""
    if device is None:
        device = h.device if torch.is_tensor(h) else torch.device("cpu")
    if dtype is None:
        dtype = h.dtype if torch.is_tensor(h) else torch.float32
    if not torch.is_tensor(h):
        h = torch.tensor(h, dtype=dtype, device=device)
    else:
        h = h.to(device=device, dtype=dtype)
    CG = torch.tensor(_CG_np, dtype=dtype, device=device)        # (4, 8, 8)
    # (*batch, V, μ, a) × (a, I, J) → (*batch, V, μ, I, J)
    return torch.einsum('...vma,aij->...vmij', h, CG)


def apply_A(psi, blocks, fwd, back):
    """Apply the antisymmetric fermion matrix A to ψ, matrix-free.

    psi:    (*batch, V, 8)
    blocks: (*batch, V, 4, 8, 8) from `hopping_blocks` (μ axis = -3)
    Returns (*batch, V, 8) = A ψ.
    """
    out = torch.zeros_like(psi)
    for mu in range(4):
        bmu = blocks[..., mu, :, :]                    # (*batch, V, 8, 8) = block^μ_{x,I,J}
        psi_fwd = psi.index_select(-2, fwd[:, mu])     # ψ_{x+μ̂, J}
        out = out + torch.einsum('...vij,...vj->...vi', bmu, psi_fwd)   # forward hop
        t = torch.einsum('...vji,...vj->...vi', bmu, psi)              # tᵀ at each site
        out = out - t.index_select(-2, back[:, mu])    # backward hop: − t_{x−μ̂}
    return out


def apply_AtA(psi, blocks, fwd, back, shift=0.0):
    """Apply (A†A + shift·I) ψ = −A(Aψ) + shift·ψ  (A†A = −A², PSD)."""
    a_psi = apply_A(psi, blocks, fwd, back)
    out = -apply_A(a_psi, blocks, fwd, back)
    if shift:
        out = out + shift * psi
    return out
