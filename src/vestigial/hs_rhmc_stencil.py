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


def multishift_cg(b, blocks, fwd, back, shifts, tol=1e-8, max_iter=2000):
    """Solve (A†A + σ_k) x_k = b for all shifts σ_k, batched over configs.

    K-parallel conjugate gradient: each (config, shift) system is a standard CG,
    all sharing ONE wide batched stencil matvec per iteration; converged systems
    are masked out of further updates. (True multishift ζ-recurrence would do
    fewer matvecs but on a narrower batch — a profiling-driven optimization; the
    solutions are identical to CG tolerance.)

    b:      (*batch, V, 8) source (shared across shifts within a config)
    blocks: (*batch, V, 4, 8, 8) from `hopping_blocks`
    shifts: (K,) or (*batch, K)  — σ_k ≥ 0
    Returns x: (*batch, K, V, 8).
    """
    nb = b.dim() - 2                                  # number of leading batch dims
    Bshape = b.shape[:nb]
    V, S = b.shape[-2], b.shape[-1]
    shifts = torch.as_tensor(shifts, dtype=b.dtype, device=b.device)
    K = shifts.shape[-1]
    if shifts.dim() == 1:
        shifts = shifts.reshape((1,) * nb + (K,))
    sigma = shifts.expand(*Bshape, K).reshape(*Bshape, K, 1, 1)   # (*B, K, 1, 1)

    blocks_k = blocks.unsqueeze(nb)                   # (*B, 1, V, 4, 8, 8) — broadcast over K
    bk = b.unsqueeze(nb).expand(*Bshape, K, V, S)     # (*B, K, V, 8)

    x = torch.zeros_like(bk)
    r = bk.clone()
    p = bk.clone()
    rs = (r * r).sum(dim=(-2, -1))                    # (*B, K)
    tol_sq = tol * tol * rs.clamp_min(1e-300)
    converged = rs <= tol_sq

    for _ in range(max_iter):
        if bool(converged.all()):
            break
        Ap = apply_AtA(p, blocks_k, fwd, back) + sigma * p          # (*B, K, V, 8)
        pAp = (p * Ap).sum(dim=(-2, -1))                            # (*B, K)
        alpha = torch.where(converged, torch.zeros_like(rs), rs / pAp)
        x = x + alpha[..., None, None] * p
        r = r - alpha[..., None, None] * Ap
        rs_new = (r * r).sum(dim=(-2, -1))
        beta = torch.where(converged, torch.zeros_like(rs), rs_new / rs)
        p = r + beta[..., None, None] * p
        rs = rs_new
        converged = converged | (rs <= tol_sq)

    return x


def action(h, phi, g, alpha_0, alphas, betas, fwd, back, L, tol=1e-10, max_iter=5000):
    """RHMC h-action S = Σh²/(4g) + α₀ φ†φ + Σ_k α_k φ†ψ_k,  ψ_k=(A†A+β_k)⁻¹φ.

    (Excludes the momentum kinetic term — added at the Hamiltonian level.)
    h: (*batch, V, 4, 4),  phi: (*batch, V, 8).  Returns (*batch,) action."""
    blocks = hopping_blocks(h, L, device=h.device, dtype=h.dtype)
    alphas = torch.as_tensor(alphas, dtype=h.dtype, device=h.device)
    betas = torch.as_tensor(betas, dtype=h.dtype, device=h.device)
    psi = multishift_cg(phi, blocks, fwd, back, betas, tol=tol, max_iter=max_iter)  # (*B,K,V,8)

    s_aux = (h * h).sum(dim=(-3, -2, -1)) / (4.0 * g)              # (*B,)
    phi_phi = (phi * phi).sum(dim=(-2, -1))                        # (*B,)
    phi_psi = (phi.unsqueeze(-3) * psi).sum(dim=(-2, -1))          # (*B, K)
    s_pf = float(alpha_0) * phi_phi + (alphas * phi_psi).sum(dim=-1)
    return s_aux + s_pf


def compute_force(h, phi, g, alphas, betas, fwd, back, L, tol=1e-10, max_iter=5000):
    """MD force F = −∂S/∂h = −h/(2g) + pseudofermion term, batched over configs.

    Per μ: F^a_{x,μ} += Σ_k α_k (−2)[ψ_k(x)·CG[a]·Aψ_k(x+μ̂) − Aψ_k(x)·CG[a]·ψ_k(x+μ̂)].
    h: (*batch, V, 4, 4),  phi: (*batch, V, 8).  Returns (*batch, V, 4, 4)."""
    nb = h.dim() - 3
    alphas = torch.as_tensor(alphas, dtype=h.dtype, device=h.device)
    betas = torch.as_tensor(betas, dtype=h.dtype, device=h.device)
    blocks = hopping_blocks(h, L, device=h.device, dtype=h.dtype)          # (*B,V,4,8,8)
    psi = multishift_cg(phi, blocks, fwd, back, betas, tol=tol, max_iter=max_iter)  # (*B,K,V,8)
    a_psi = apply_A(psi, blocks.unsqueeze(nb), fwd, back)                   # (*B,K,V,8)

    CG = torch.tensor(_CG_np, dtype=h.dtype, device=h.device)              # (4,8,8)
    F = -h / (2.0 * g)                                                     # (*B,V,4,4)
    for mu in range(4):
        psi_fwd = psi.index_select(-2, fwd[:, mu])                         # ψ_k(x+μ̂)
        a_psi_fwd = a_psi.index_select(-2, fwd[:, mu])
        cg_apsi = torch.einsum('aij,...kvj->...akvi', CG, a_psi_fwd)       # CG[a]·Aψ_k(x+μ̂)
        term1 = torch.einsum('...kvi,...akvi->...akv', psi, cg_apsi)
        cg_psi = torch.einsum('aij,...kvj->...akvi', CG, psi_fwd)          # CG[a]·ψ_k(x+μ̂)
        term2 = torch.einsum('...kvi,...akvi->...akv', a_psi, cg_psi)
        weighted = torch.einsum('k,...akv->...av', alphas, -2.0 * (term1 - term2))  # (*B,a,V)
        F[..., :, mu, :] = F[..., :, mu, :] + weighted.transpose(-1, -2)   # (*B,V,a)
    return F


OMELYAN_LAMBDA = 0.1931833275037836   # 2MN minimal-norm coefficient


def integrate(h, pi, phi, g, alphas, betas, fwd, back, L, eps, n_steps,
              lam=OMELYAN_LAMBDA, tol=1e-10, max_iter=5000):
    """Omelyan 2MN (2nd-order minimal-norm) molecular-dynamics evolution.

    One step: π+=λεF; h+=ε/2·π; π+=(1−2λ)εF; h+=ε/2·π; π+=λεF.
    Reversible + symplectic ⟹ the Metropolis accept/reject on ΔH is exact.
    Returns (h, π) after n_steps."""
    def force(hh):
        return compute_force(hh, phi, g, alphas, betas, fwd, back, L, tol=tol, max_iter=max_iter)

    half = 0.5 * eps
    for _ in range(n_steps):
        pi = pi + (lam * eps) * force(h)
        h = h + half * pi
        pi = pi + ((1.0 - 2.0 * lam) * eps) * force(h)
        h = h + half * pi
        pi = pi + (lam * eps) * force(h)
    return h, pi
