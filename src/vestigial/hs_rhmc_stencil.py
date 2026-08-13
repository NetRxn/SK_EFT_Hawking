"""Batched matrix-free stencil for the HS+RHMC fermion operator (GPU port).
Even-odd reduction gives a single-pole exact action and force; the solve is
FP32-inner / FP64-residual refined and warm-started by chronological
inversion. Certified against the dense oracle and Creutz, it also serves as
the cross-engine oracle for the MLX port.

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

# Real-pseudofermion Gaussian normalization. The intended weight is
# |Pf(A)| = det(A†A+m²)^{1/4}  (ONE Majorana; Lit-Search/Phase-5/HS+RHMC...Spin(4).md §60,64).
# The heatbath draws φ = B^{1/2}ξ with ξ~N(0,1) (B the relevant operator power), giving
# ⟨φφᵀ⟩ = B; but the action S = φᵀB⁻¹φ needs its conditional e^{−S} ⟹ ⟨φφᵀ⟩ = B/2.
# For a REAL field the missing factor is 1/√2 (the "complex Gaussian convention" the Rust
# engine applies at rust/src/lib.rs `pseudofermion_heatbath`, inv_sqrt2, Lean-backed by
# `hs_gaussian_identity_zero`). Omitting it samples det^{1/2} (two Majorana / Dirac) — a
# factor-2 flavor error. Every heatbath here scales its output by INV_SQRT2 to fix this.
INV_SQRT2 = 2.0 ** -0.5

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


_eo_cache = {}


def eo_tables(L, device):
    """Even-odd (parity) partition + half-size hop tables for the bipartite lattice.

    The 4D hypercubic lattice with even L is bipartite: A hops ONLY between parities,
    so A†A = diag(M_e, M_o) is block-diagonal (M_e on the even sublattice). This returns
    the index maps for the half-size even-block matvec `apply_Me`. EVEN L ONLY — odd L
    with periodic BC is not bipartite (a torus loop has odd length) and the reduction is
    invalid.

    Returns dict: even_idx, odd_idx (V/2,) flat indices; o2e_fwd/o2e_back (V/2,4) map an
    odd-half site's ±μ neighbor to its even-half index; e2o_fwd/e2o_back (V/2,4) the dual.
    """
    if L % 2 != 0:
        raise ValueError(f"even-odd reduction requires even L (bipartite); got L={L}")
    key = (L, str(device))
    if key in _eo_cache:
        return _eo_cache[key]
    V = L ** 4
    coords = np.array(np.unravel_index(np.arange(V), (L, L, L, L))).T   # (V, 4)
    parity = coords.sum(axis=1) % 2
    even_flat = np.where(parity == 0)[0]
    odd_flat = np.where(parity == 1)[0]
    pos = np.empty(V, np.int64)                       # flat → index within its parity group
    pos[even_flat] = np.arange(even_flat.size)
    pos[odd_flat] = np.arange(odd_flat.size)

    fwd_np = np.zeros((V, 4), np.int64)
    back_np = np.zeros((V, 4), np.int64)
    for mu in range(4):
        f = coords.copy(); f[:, mu] = (f[:, mu] + 1) % L
        b = coords.copy(); b[:, mu] = (b[:, mu] - 1) % L
        fwd_np[:, mu] = np.ravel_multi_index(f.T, (L, L, L, L))
        back_np[:, mu] = np.ravel_multi_index(b.T, (L, L, L, L))

    def half(src_flat):                               # ±μ neighbor → opposite-parity half-index
        return (torch.tensor(pos[fwd_np[src_flat]], dtype=torch.long, device=device),
                torch.tensor(pos[back_np[src_flat]], dtype=torch.long, device=device))
    o2e_fwd, o2e_back = half(odd_flat)
    e2o_fwd, e2o_back = half(even_flat)
    out = dict(even_idx=torch.tensor(even_flat, dtype=torch.long, device=device),
               odd_idx=torch.tensor(odd_flat, dtype=torch.long, device=device),
               o2e_fwd=o2e_fwd, o2e_back=o2e_back, e2o_fwd=e2o_fwd, e2o_back=e2o_back)
    _eo_cache[key] = out
    return out


def _hop(psi_in, blocks_out, blocks_in, fwd_h, back_h):
    """One bipartite hop D: (in-parity) → (out-parity), mirroring `apply_A` split by parity.

    out_y = Σ_μ [ blocks_out[y,μ]·ψ_{y+μ} − blocks_in[y−μ,μ]ᵀ·ψ_{y−μ} ], with y±μ on the
    in-parity sublattice. blocks_out: (*B, Vout, 4, 8, 8); blocks_in: (*B, Vin, 4, 8, 8);
    fwd_h/back_h: (Vout, 4) out-half → in-half index of y±μ. Returns (*B, Vout, 8)."""
    out = None
    for mu in range(4):
        bo = blocks_out[..., mu, :, :]                                  # (*B, Vout, 8, 8)
        bi = blocks_in[..., mu, :, :]                                   # (*B, Vin, 8, 8)
        fwd_term = torch.einsum('...vij,...vj->...vi', bo, psi_in.index_select(-2, fwd_h[:, mu]))
        t_in = torch.einsum('...vji,...vj->...vi', bi, psi_in)          # bᵀψ at each in-site
        back_term = t_in.index_select(-2, back_h[:, mu])
        out = (fwd_term - back_term) if out is None else out + (fwd_term - back_term)
    return out


def apply_Me(psi_e, blocks, eo, shift=0.0):
    """Apply the even-block operator (M_e + shift) ψ_e on the half-size even sublattice.

    M_e = −D_eo D_oe (= the even block of A†A = −A²). Half the degrees of freedom of the
    full `apply_AtA` for the same spectrum ⟹ the even-odd-reduced RHMC matvec. blocks is
    the FULL (*B, V, 4, 8, 8) hopping table; `eo` from `eo_tables`. Returns (*B, V/2, 8).
    """
    blocks_e = blocks.index_select(-4, eo['even_idx'])                  # (*B, V/2, 4, 8, 8)
    blocks_o = blocks.index_select(-4, eo['odd_idx'])
    w_o = _hop(psi_e, blocks_o, blocks_e, eo['o2e_fwd'], eo['o2e_back'])   # D_oe ψ_e  (odd)
    v_e = _hop(w_o, blocks_e, blocks_o, eo['e2o_fwd'], eo['e2o_back'])     # D_eo w_o  (even)
    out = -v_e                                                          # M_e = −D_eo D_oe
    if shift:
        out = out + shift * psi_e
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


def eo_multishift_cg(b, blocks, eo, shifts, tol=1e-8, max_iter=4000, x0=None):
    """Multishift CG on the even-block operator M_e (half size). Mirrors `multishift_cg`
    but with `apply_Me` — ~2× cheaper for the same spectrum. b: (*B, V/2, 8).

    `x0` (optional, shape (*B, V/2, 8)) is a warm-start initial guess broadcast across shifts
    — chronological inversion: during MD the source φ is fixed and h changes slowly, so the
    previous step's solution seeds the CG and cuts iterations ~3–5×. Convergence is relative
    to ‖b‖ (not ‖r0‖), so the result is identical to a cold start to the same tol."""
    nb = b.dim() - 2
    Bshape = b.shape[:nb]
    Ve, S = b.shape[-2], b.shape[-1]
    shifts = torch.as_tensor(shifts, dtype=b.dtype, device=b.device)
    K = shifts.shape[-1]
    if shifts.dim() == 1:
        shifts = shifts.reshape((1,) * nb + (K,))
    sigma = shifts.expand(*Bshape, K).reshape(*Bshape, K, 1, 1)
    blocks_k = blocks.unsqueeze(nb)                   # (*B, 1, V, 4, 8, 8) — broadcast over K
    bk = b.unsqueeze(nb).expand(*Bshape, K, Ve, S)

    if x0 is None:
        x = torch.zeros_like(bk)
        r = bk.clone()
    else:
        x = x0.unsqueeze(nb).expand(*Bshape, K, Ve, S).clone()
        r = bk - (apply_Me(x, blocks_k, eo) + sigma * x)
    p = r.clone()
    rs = (r * r).sum(dim=(-2, -1))
    tol_sq = tol * tol * (bk * bk).sum(dim=(-2, -1)).clamp_min(1e-300)   # relative to ‖b‖
    converged = rs <= tol_sq
    for _ in range(max_iter):
        if bool(converged.all()):
            break
        Ap = apply_Me(p, blocks_k, eo) + sigma * p
        pAp = (p * Ap).sum(dim=(-2, -1))
        alpha = torch.where(converged, torch.zeros_like(rs), rs / pAp)
        x = x + alpha[..., None, None] * p
        r = r - alpha[..., None, None] * Ap
        rs_new = (r * r).sum(dim=(-2, -1))
        beta = torch.where(converged, torch.zeros_like(rs), rs_new / rs)
        p = r + beta[..., None, None] * p
        rs = rs_new
        converged = converged | (rs <= tol_sq)
    return x


def eo_action(h, phi_e, g, msq, eo, fwd, back, L, tol=1e-10, max_iter=5000):
    """Even-odd reduced action S = Σh²/(4g) + φ_e†(M_e+m²)⁻¹φ_e.

    The determinant factorizes (det(A†A+m²)=det(M_e+m²)²) ⟹ the SAME fermion weight
    det(A†A+m²)^{1/4}=det(M_e+m²)^{1/2} is represented by ONE even pseudofermion with
    action power −1 — a single exact solve, no rational sum. φ_e: (*B, V/2, 8)."""
    blocks = hopping_blocks(h, L, device=h.device, dtype=h.dtype)
    psi = eo_multishift_cg(phi_e, blocks, eo, [msq], tol=tol, max_iter=max_iter)[..., 0, :, :]
    s_aux = (h * h).sum(dim=(-3, -2, -1)) / (4.0 * g)
    s_pf = (phi_e * psi).sum(dim=(-2, -1))
    return s_aux + s_pf


def _scatter_even(psi_e, eo, V):
    """Embed a half-size even vector into a full-lattice vector (zero on odd)."""
    Bshape = psi_e.shape[:-2]
    full = psi_e.new_zeros(*Bshape, V, psi_e.shape[-1])
    full.index_copy_(-2, eo['even_idx'], psi_e)
    return full


def eo_fermion_force(h, phi_e, msq, eo, fwd, back, L, tol=1e-10, max_iter=5000,
                     x0=None, return_psi=False):
    """Fermion part ONLY of the eo MD force: −∂/∂h[φ_e†(M_e+m²)⁻¹φ_e] (NO aux −h/2g term).
    ψ_e=(M_e+m²)⁻¹φ_e (ONE solve); contraction with the single vector ψ=scatter(ψ_e).
    Factored out of `eo_compute_force` so Hasenbusch's ratio force can reuse it (scaled).

    `x0` warm-starts the solve (chronological inversion); `return_psi=True` also returns ψ_e
    so the integrator can feed it as the next step's x0."""
    V = L ** 4
    blocks = hopping_blocks(h, L, device=h.device, dtype=h.dtype)
    psi_e = eo_multishift_cg(phi_e, blocks, eo, [msq], tol=tol, max_iter=max_iter, x0=x0)[..., 0, :, :]
    psi = _scatter_even(psi_e, eo, V)                                  # (*B, V, 8) on even
    a_psi = apply_A(psi, blocks, fwd, back)                            # (*B, V, 8) on odd

    CG = torch.tensor(_CG_np, dtype=h.dtype, device=h.device)         # (4, 8, 8)
    F = torch.zeros_like(h)
    for mu in range(4):
        psi_fwd = psi.index_select(-2, fwd[:, mu])
        a_psi_fwd = a_psi.index_select(-2, fwd[:, mu])
        cg_apsi = torch.einsum('aij,...vj->...avi', CG, a_psi_fwd)
        term1 = torch.einsum('...vi,...avi->...av', psi, cg_apsi)
        cg_psi = torch.einsum('aij,...vj->...avi', CG, psi_fwd)
        term2 = torch.einsum('...vi,...avi->...av', a_psi, cg_psi)
        weighted = -2.0 * (term1 - term2)                             # (*B, a, V), single pole α=1
        F[..., :, mu, :] = F[..., :, mu, :] + weighted.transpose(-1, -2)
    return (F, psi_e) if return_psi else F


def eo_compute_force(h, phi_e, g, msq, eo, fwd, back, L, tol=1e-10, max_iter=5000,
                     x0=None, return_psi=False):
    """MD force for the even-odd action = −h/(2g) (aux) + eo_fermion_force. h: (*B, V, 4, 4).
    `x0`/`return_psi` thread chronological-inversion warm-start through the fermion solve."""
    if return_psi:
        Ff, psi_e = eo_fermion_force(h, phi_e, msq, eo, fwd, back, L, tol=tol, max_iter=max_iter,
                                     x0=x0, return_psi=True)
        return -h / (2.0 * g) + Ff, psi_e
    return -h / (2.0 * g) + eo_fermion_force(h, phi_e, msq, eo, fwd, back, L, tol=tol,
                                             max_iter=max_iter, x0=x0)


def eo_ratio_action(h, phi_R, msq, mu2, eo, fwd, back, L, tol=1e-10, max_iter=5000):
    """Hasenbusch RATIO pseudofermion action (μ²>m²), representing det[(M_e+m²)/(M_e+μ²)]^{1/2}:
        S_R = ‖φ_R‖² + (μ²−m²)·φ_R†(M_e+m²)⁻¹φ_R
    (from W=(M_e+μ²)(M_e+m²)⁻¹ = I + (μ²−m²)(M_e+m²)⁻¹, real-PF weight det(W)^{−1/2}).
    NO aux term. Pairs with the heavy PF S_H = φ_H†(M_e+μ²)⁻¹φ_H (= eo_action at μ²)."""
    blocks = hopping_blocks(h, L, device=h.device, dtype=h.dtype)
    psi = eo_multishift_cg(phi_R, blocks, eo, [msq], tol=tol, max_iter=max_iter)[..., 0, :, :]
    return (phi_R * phi_R).sum(dim=(-2, -1)) + (mu2 - msq) * (phi_R * psi).sum(dim=(-2, -1))


def eo_ratio_force(h, phi_R, msq, mu2, eo, fwd, back, L, tol=1e-10, max_iter=5000):
    """MD force of `eo_ratio_action` = (μ²−m²)·eo_fermion_force(φ_R, m²) — the stiff light
    force scaled DOWN by (μ²−m²) ⟹ smaller fluctuations ⟹ larger stable eps (the Hasenbusch win)."""
    return (mu2 - msq) * eo_fermion_force(h, phi_R, msq, eo, fwd, back, L, tol=tol, max_iter=max_iter)


def _eo_rsqrt_inv(x, blocks, eo, coeffs, shift, tol, max_iter):
    """(M_e+shift)^{−1/2} x via the r_{−1/2} rational (coeffs = make_rhmc_coeffs at this range)."""
    betas = torch.as_tensor(coeffs['betas'], dtype=x.dtype, device=x.device) + shift
    alphas = torch.as_tensor(coeffs['alphas'], dtype=x.dtype, device=x.device)
    psi = eo_multishift_cg(x, blocks, eo, betas, tol=tol, max_iter=max_iter)
    return float(coeffs['a0']) * x + (alphas[..., None, None] * psi).sum(dim=-3)


def eo_ratio_heatbath(xi, h, coeffs_m, coeffs_mu, msq, mu2, eo, fwd, back, L, tol=1e-10, max_iter=8000):
    """φ_R = (M_e+m²)^{1/2}(M_e+μ²)^{−1/2} ξ  ⟹  S_R(φ_R)=‖ξ‖² (ratio-PF heatbath).
    coeffs_mu = make_rhmc_coeffs at μ² range (its r_{−1/2} a0/alphas/betas); coeffs_m at m² range.
    (M_e+m²)^{1/2} v = (M_e+m²)·[r_{−1/2}(m²) v]."""
    blocks = hopping_blocks(h, L, device=h.device, dtype=h.dtype)
    v = _eo_rsqrt_inv(xi, blocks, eo, coeffs_mu, mu2, tol, max_iter)          # (M_e+μ²)^{−1/2} ξ
    w = _eo_rsqrt_inv(v, blocks, eo, coeffs_m, msq, tol, max_iter)            # (M_e+m²)^{−1/2} v
    return INV_SQRT2 * apply_Me(w, blocks, eo, shift=msq)                     # (M_e+m²)^{1/2}·ξ/√2


def eo_heatbath(xi_e, h, coeffs, msq, eo, fwd, back, L, tol=1e-10, max_iter=8000):
    """φ_e = (M_e+m²)^{1/2} ξ_e / √2 = (M_e+m²)·r_{-1/2}(M_e+m²)·ξ_e / √2, so S_PF(φ_e)=½‖ξ_e‖².

    The 1/√2 (INV_SQRT2) is the real-Gaussian normalization: it makes the heatbath sample the
    action's conditional e^{−φ†(M_e+m²)⁻¹φ}, so the h-marginal is det(M_e+m²)^{1/2}=det(A†A+m²)^{1/4}
    (ONE Majorana). Without it the engine sampled det^1 (Dirac) — see the INV_SQRT2 note above.
    Reuses make_rhmc_coeffs' power −1/2 set (coeffs a0/alphas/betas) as r_{-1/2}. xi_e: (*B, V/2, 8)."""
    blocks = hopping_blocks(h, L, device=h.device, dtype=h.dtype)
    betas = torch.as_tensor(coeffs['betas'], dtype=xi_e.dtype, device=xi_e.device) + msq
    alphas = torch.as_tensor(coeffs['alphas'], dtype=xi_e.dtype, device=xi_e.device)
    psi = eo_multishift_cg(xi_e, blocks, eo, betas, tol=tol, max_iter=max_iter)
    v = float(coeffs['a0']) * xi_e + (alphas[..., None, None] * psi).sum(dim=-3)   # r_{-1/2} ξ
    return INV_SQRT2 * apply_Me(v, blocks, eo, shift=msq)              # (M_e+m²)^{1/2}·ξ/√2


def _cg_shifted(rhs, blocks_k, fwd, back, sigma, tol=1e-8, max_iter=4000):
    """Batched CG for (A†A + σ) x = rhs with a PER-SHIFT right-hand side.

    Generalizes `multishift_cg`: there the K systems share one source b (broadcast);
    here each system k carries its own `rhs[..., k, :, :]` (the iterative-refinement
    correction step). Same per-iteration cost — one wide batched matvec over the
    K axis — with per-(config,shift) convergence masking.

    rhs:      (*batch, K, V, 8)   — distinct source per shift
    blocks_k: (*batch, 1, V, 4, 8, 8)  from `blocks.unsqueeze(nb)` (broadcast over K)
    sigma:    (*batch, K, 1, 1)   — shift σ_k ≥ 0
    Returns x: (*batch, K, V, 8).
    """
    x = torch.zeros_like(rhs)
    r = rhs.clone()
    p = rhs.clone()
    rs = (r * r).sum(dim=(-2, -1))                                  # (*B, K)
    tol_sq = tol * tol * rs.clamp_min(1e-300)
    converged = rs <= tol_sq

    for _ in range(max_iter):
        if bool(converged.all()):
            break
        Ap = apply_AtA(p, blocks_k, fwd, back) + sigma * p
        pAp = (p * Ap).sum(dim=(-2, -1))
        alpha = torch.where(converged, torch.zeros_like(rs), rs / pAp)
        x = x + alpha[..., None, None] * p
        r = r - alpha[..., None, None] * Ap
        rs_new = (r * r).sum(dim=(-2, -1))
        beta = torch.where(converged, torch.zeros_like(rs), rs_new / rs)
        p = r + beta[..., None, None] * p
        rs = rs_new
        converged = converged | (rs <= tol_sq)

    return x


def multishift_cg_refined(b64, h64, shifts, fwd64, back64, fwd_dev, back_dev, L, device,
                          tol=1e-10, inner_tol=3e-4, max_outer=12, max_inner=4000):
    """FP64-accurate multishift solve via FP32-inner / FP64-residual ITERATIVE REFINEMENT.

    Solves (A†A + σ_k) x_k = b64 for all k to FP64 relative residual `tol`, doing the
    heavy CG work in FP32 on `device` (GPU) and the residual + accumulation in FP64 on
    b64.device (CPU). This is the standard mixed-precision lattice solver: each outer
    pass shrinks the TRUE (FP64) residual by ~`inner_tol`, so ~3–4 passes reach FP64
    accuracy while every CG iteration runs at FP32 speed.

    The exact FP64 Metropolis test is preserved (x_k are FP64-accurate) at a fraction
    of the cost of a pure-FP64 CG — the fix for the accept/reject bottleneck that the
    Mac cannot accelerate (MPS is FP32-only).

    b64: (*batch, V, 8) FP64 source;  h64: (*batch, V, 4, 4) FP64 config.
    Returns x: FP64 (*batch, K, V, 8) on b64.device.
    """
    res_dev = b64.device
    nb = b64.dim() - 2
    Bshape = b64.shape[:nb]
    V, S = b64.shape[-2], b64.shape[-1]

    shifts64 = torch.as_tensor(shifts, dtype=torch.float64, device=res_dev)
    K = shifts64.shape[-1]
    if shifts64.dim() == 1:
        shifts64 = shifts64.reshape((1,) * nb + (K,))
    sigma64 = shifts64.expand(*Bshape, K).reshape(*Bshape, K, 1, 1)
    sigma32 = sigma64.to(dtype=torch.float32, device=device)

    blocks64 = hopping_blocks(h64, L, device=res_dev, dtype=torch.float64).unsqueeze(nb)
    blocks32 = hopping_blocks(h64, L, device=device, dtype=torch.float32).unsqueeze(nb)

    x = b64.new_zeros(*Bshape, K, V, S)                            # FP64 accumulator
    bk64 = b64.unsqueeze(nb).expand(*Bshape, K, V, S)              # FP64 source per shift
    bnorm = bk64.norm(dim=(-2, -1)).clamp_min(1e-300)             # (*B, K)

    for _ in range(max_outer):
        Ax = apply_AtA(x, blocks64, fwd64, back64) + sigma64 * x   # FP64 residual on CPU
        r64 = bk64 - Ax
        if bool((r64.norm(dim=(-2, -1)) <= tol * bnorm).all()):
            break
        r32 = r64.to(dtype=torch.float32).to(device=device)       # FP32 inner solve on device
        d32 = _cg_shifted(r32, blocks32, fwd_dev, back_dev, sigma32, tol=inner_tol, max_iter=max_inner)
        x = x + d32.to(device=res_dev).to(dtype=torch.float64)     # move off device BEFORE f64 cast (MPS)

    return x


def action_refined(h, phi, g, alpha_0, alphas, betas, fwd64, back64, fwd_dev, back_dev, L, device,
                   tol=1e-10, inner_tol=3e-4, max_outer=12, max_inner=4000):
    """`action` with the multishift solve done by the mixed-precision refined solver.

    Identical value to `action` (to FP64 `tol`); the FP64 reductions are unchanged, only
    ψ_k = (A†A+β_k)⁻¹φ is computed via FP32-inner/FP64-residual refinement on `device`."""
    alphas = torch.as_tensor(alphas, dtype=h.dtype, device=h.device)
    betas = torch.as_tensor(betas, dtype=h.dtype, device=h.device)
    psi = multishift_cg_refined(phi, h, betas, fwd64, back64, fwd_dev, back_dev, L, device,
                                tol=tol, inner_tol=inner_tol, max_outer=max_outer, max_inner=max_inner)
    s_aux = (h * h).sum(dim=(-3, -2, -1)) / (4.0 * g)
    phi_phi = (phi * phi).sum(dim=(-2, -1))
    phi_psi = (phi.unsqueeze(-3) * psi).sum(dim=(-2, -1))
    s_pf = float(alpha_0) * phi_phi + (alphas * phi_psi).sum(dim=-1)
    return s_aux + s_pf


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


def estimate_lambda_max(blocks, fwd, back, V, n_iter=200, seed=0, v0=None):
    """Largest eigenvalue of A†A per config, via power iteration. Returns (*batch,)."""
    Bshape = blocks.shape[:-4]
    dtype, device = blocks.dtype, blocks.device
    if v0 is None:
        gen = torch.Generator(device=device).manual_seed(seed)
        v = torch.randn(*Bshape, V, 8, dtype=dtype, device=device, generator=gen)
    else:
        v = v0.clone()
    for _ in range(n_iter):
        w = apply_AtA(v, blocks, fwd, back)
        v = w / (w * w).sum(dim=(-2, -1), keepdim=True).sqrt().clamp_min(1e-300)
    w = apply_AtA(v, blocks, fwd, back)
    return (v * w).sum(dim=(-2, -1)) / (v * v).sum(dim=(-2, -1))


def make_rhmc_coeffs(lam_max, msq, n_poles, action_power=-0.5, hb_power=-0.75):
    """Zolotarev partial-fraction coeffs for the FULL real operator A†A+m².

    Action ≈ (A†A+m²)^{-1/2} (real φ ⟹ weight det(A†A)^{1/4}); heatbath builds
    (A†A+m²)^{+1/4} = (A†A+m²)·(A†A+m²)^{-3/4}. Spectral range [m², λmax+m²];
    raw `betas` are added to m² at CG-call sites (mirrors production make_coeffs)."""
    from src.vestigial.hs_rhmc import compute_zolotarev_coefficients
    lo = msq if msq > 0 else max(float(lam_max) * 1e-7, 1e-12)
    hi = float(lam_max) + msq
    a0, alphas, betas = compute_zolotarev_coefficients(n_poles, lo, hi, action_power)
    a0_hb, alphas_hb, betas_hb = compute_zolotarev_coefficients(n_poles, lo, hi, hb_power)
    return dict(a0=float(a0), alphas=np.asarray(alphas), betas=np.asarray(betas),
                a0_hb=float(a0_hb), alphas_hb=np.asarray(alphas_hb), betas_hb=np.asarray(betas_hb))


def heatbath(xi, blocks, fwd, back, coeffs, msq, tol=1e-10, max_iter=8000):
    """φ = (A†A+m²)^{1/4} ξ / √2 = (A†A+m²)·r_{-3/4}(A†A+m²)·ξ / √2, so S_PF(φ)=½‖ξ‖².

    The 1/√2 (INV_SQRT2) is the real-Gaussian normalization (see the INV_SQRT2 note): it makes
    the heatbath sample the action's conditional e^{−φ†(A†A+m²)^{-1/2}φ}, so the h-marginal is
    det(A†A+m²)^{1/4} (ONE Majorana). Without it the engine sampled det^{1/2} (Dirac). ξ: (*batch, V, 8)."""
    betas_hb = torch.as_tensor(coeffs['betas_hb'], dtype=xi.dtype, device=xi.device) + msq
    alphas_hb = torch.as_tensor(coeffs['alphas_hb'], dtype=xi.dtype, device=xi.device)
    psi = multishift_cg(xi, blocks, fwd, back, betas_hb, tol=tol, max_iter=max_iter)  # (*B,K,V,8)
    v = float(coeffs['a0_hb']) * xi + (alphas_hb[..., None, None] * psi).sum(dim=-3)   # r_{-3/4}ξ
    return INV_SQRT2 * (apply_AtA(v, blocks, fwd, back) + msq * v)                      # (A†A+m²)^{1/4}·ξ/√2


def heatbath_refined(xi, h64, coeffs, msq, fwd64, back64, fwd_dev, back_dev, L, device,
                     tol=1e-10, inner_tol=3e-4, max_outer=12, max_inner=4000):
    """`heatbath` with the (A†A+m²)^{-3/4} multishift solve done by the refined solver.

    Same φ (to FP64 `tol`) as `heatbath`; the heavy CG runs FP32 on `device`. The final
    (A†A+m²)·v matvec stays FP64 on xi.device — it is one matvec, not a solve."""
    betas_hb = torch.as_tensor(coeffs['betas_hb'], dtype=torch.float64, device=xi.device) + msq
    alphas_hb = torch.as_tensor(coeffs['alphas_hb'], dtype=torch.float64, device=xi.device)
    psi = multishift_cg_refined(xi, h64, betas_hb, fwd64, back64, fwd_dev, back_dev, L, device,
                                tol=tol, inner_tol=inner_tol, max_outer=max_outer, max_inner=max_inner)
    v = float(coeffs['a0_hb']) * xi + (alphas_hb[..., None, None] * psi).sum(dim=-3)   # r_{-3/4}ξ
    blocks64 = hopping_blocks(h64, L, device=xi.device, dtype=torch.float64)
    return INV_SQRT2 * (apply_AtA(v, blocks64, fwd64, back64) + msq * v)                # (A†A+m²)^{1/4}·ξ/√2


def rhmc_trajectory_refined(h64, g, msq, coeffs, fwd64, back64, fwd_dev, back_dev, L,
                            eps, n_md, device, gen_dev, gen_cpu,
                            tol_md=1e-5, tol_acc=1e-10, inner_tol=3e-4,
                            max_outer=12, max_inner=4000):
    """Mixed-precision trajectory with the accept/reject solves ALSO offloaded to
    `device` (FP32 inner + FP64 residual refinement) — FP64-EXACT Metropolis at GPU
    speed. This removes the pure-FP64 CPU heatbath + Hamiltonians that dominate the
    `rhmc_trajectory_mixed` cost on a device (MPS) that cannot run FP64.

    RNG draw order (xi, pi, u) matches `rhmc_trajectory_mixed` exactly, so the two are
    interchangeable. h64: FP64 (*batch, V, 4, 4) on CPU."""
    Bshape = h64.shape[:-3]
    V = L ** 4

    xi = torch.randn(*Bshape, V, 8, dtype=torch.float64, generator=gen_cpu)
    phi64 = heatbath_refined(xi, h64, coeffs, msq, fwd64, back64, fwd_dev, back_dev, L, device,
                             tol=tol_acc, inner_tol=inner_tol, max_outer=max_outer, max_inner=max_inner)
    pi64 = torch.randn(*Bshape, V, 4, 4, dtype=torch.float64, generator=gen_cpu)

    a0 = float(coeffs['a0'])
    al64 = torch.as_tensor(coeffs['alphas'], dtype=torch.float64)
    be64 = torch.as_tensor(coeffs['betas'], dtype=torch.float64) + msq

    def H(hh, pp):
        kin = 0.5 * (pp * pp).sum(dim=(-3, -2, -1))
        return kin + action_refined(hh, phi64, g, a0, al64, be64, fwd64, back64, fwd_dev, back_dev,
                                     L, device, tol=tol_acc, inner_tol=inner_tol,
                                     max_outer=max_outer, max_inner=max_inner)

    H_old = H(h64, pi64)

    # --- FP32 (device): MD proposal (unchanged) ---
    h32 = h64.to(dtype=torch.float32, device=device)
    pi32 = pi64.to(dtype=torch.float32, device=device)
    phi32 = phi64.to(dtype=torch.float32, device=device)
    al32 = al64.to(dtype=torch.float32, device=device)
    be32 = be64.to(dtype=torch.float32, device=device)
    h_new32, pi_new32 = integrate(h32, pi32, phi32, g, al32, be32, fwd_dev, back_dev, L,
                                  eps, n_md, tol=tol_md, max_iter=max_inner)

    h_new64 = h_new32.cpu().to(dtype=torch.float64)
    pi_new64 = pi_new32.cpu().to(dtype=torch.float64)
    dH = H(h_new64, pi_new64) - H_old

    u = torch.rand(Bshape, dtype=torch.float64, generator=gen_cpu)
    accept = u < torch.exp(torch.clamp(-dH, max=0.0))
    h_out = torch.where(accept[..., None, None, None], h_new64, h64)
    return h_out, dH, accept


def eo_integrate(h, pi, phi_e, g, msq, eo, fwd, back, L, eps, n_steps,
                 lam=OMELYAN_LAMBDA, tol=1e-10, max_iter=5000, chrono=False):
    """Omelyan 2MN MD for the even-odd action (force via `eo_compute_force`).

    chrono=False (default): cold-start every solve ⟹ deterministic in (h,π) ⟹ EXACTLY
    reversible (unit-tested). chrono=True: chronological inversion — each fermion solve
    warm-starts from the previous eval's ψ_e (h changes slowly ⟹ few CG iters, ~3-5× faster).
    Warm-start softens reversibility to O(tol) (history-dependent), so it is a controlled
    approximation whose lack of bias is certified by the Creutz identity on the chain; use it
    only through the trajectory drivers (which pass chrono=True) where accept/reject is exact."""
    psi_cache = None

    def force(hh):
        nonlocal psi_cache
        if not chrono:
            return eo_compute_force(hh, phi_e, g, msq, eo, fwd, back, L, tol=tol, max_iter=max_iter)
        F, psi_cache = eo_compute_force(hh, phi_e, g, msq, eo, fwd, back, L, tol=tol,
                                        max_iter=max_iter, x0=psi_cache, return_psi=True)
        return F

    half = 0.5 * eps
    for _ in range(n_steps):
        pi = pi + (lam * eps) * force(h)
        h = h + half * pi
        pi = pi + ((1.0 - 2.0 * lam) * eps) * force(h)
        h = h + half * pi
        pi = pi + (lam * eps) * force(h)
    return h, pi


def eo_rhmc_trajectory(h, g, msq, coeffs, eo, fwd, back, L, eps, n_md, rng_gen,
                       tol=1e-10, max_iter=8000, tol_md=None, chrono=False):
    """One even-odd RHMC trajectory (single dtype): heatbath → Omelyan → Metropolis.

    ~2× cheaper than `rhmc_trajectory` (half-size solves) for identical physics — the
    even pseudofermion samples the SAME fermion weight det(A†A+m²)^{1/4}. Returns
    (h_out, ΔH, accept), per-config.

    `tol` is the accept/reject (heatbath + Hamiltonian) tolerance — must be tight for an
    EXACT Metropolis test. `tol_md` (default = `tol`) is the MD-force tolerance; set it
    loose (e.g. 1e-4) since integration error is corrected exactly by accept/reject — this
    is the pure-FP64-CPU analogue of the mixed scheme's loose MD / tight accept split and
    is the fast CPU production setting (CPU FP32 gives no speedup; GPU is launch-bound)."""
    V = L ** 4
    Bshape = h.shape[:-3]
    dtype, device = h.dtype, h.device
    Ve = V // 2
    tol_md = tol if tol_md is None else tol_md

    xi = torch.randn(*Bshape, Ve, 8, dtype=dtype, device=device, generator=rng_gen)
    phi_e = eo_heatbath(xi, h, coeffs, msq, eo, fwd, back, L, tol=tol, max_iter=max_iter)
    pi = torch.randn(*Bshape, V, 4, 4, dtype=dtype, device=device, generator=rng_gen)

    def hamiltonian(hh, pp):
        kin = 0.5 * (pp * pp).sum(dim=(-3, -2, -1))
        return kin + eo_action(hh, phi_e, g, msq, eo, fwd, back, L, tol=tol, max_iter=max_iter)

    h_old_H = hamiltonian(h, pi)
    h_new, pi_new = eo_integrate(h, pi, phi_e, g, msq, eo, fwd, back, L,
                                 eps, n_md, tol=tol_md, max_iter=max_iter, chrono=chrono)
    dH = hamiltonian(h_new, pi_new) - h_old_H

    u = torch.rand(Bshape, dtype=dtype, device=device, generator=rng_gen)
    accept = u < torch.exp(torch.clamp(-dH, max=0.0))
    h_out = torch.where(accept[..., None, None, None], h_new, h)
    return h_out, dH, accept


def eo_rhmc_trajectory_mixed(h64, g, msq, coeffs, eo64, fwd64, back64,
                             eo_dev, fwd_dev, back_dev, L, eps, n_md,
                             device, gen_dev, gen_cpu, tol_md=1e-4, tol_acc=1e-10,
                             max_iter=8000, chrono=False):
    """Mixed-precision EVEN-ODD trajectory: FP32 MD proposal on `device` (GPU) + FP64
    accept/reject on CPU. The production-deployable eo path.

    Mirrors `rhmc_trajectory_mixed` but on the even-odd action: the MD force and the
    accept/reject are each a SINGLE (M_e+m²)⁻¹ solve (no 12-pole multishift), so — unlike
    the full engine — the FP64 accept/reject is already cheap and needs no iterative-
    refinement solver. The FP32 MD only affects acceptance efficiency; the FP64 Metropolis
    test is EXACT (same fermion weight det(A†A+m²)^{1/4}=det(M_e+m²)^{1/2} as the full
    engine — proven identical target density). h64: FP64 (*batch, V, 4, 4) on CPU."""
    Bshape = h64.shape[:-3]
    V = L ** 4
    Ve = V // 2

    # --- FP64 (CPU): heatbath (one multishift for r_{-1/2}) + momenta + H_old (exact) ---
    xi = torch.randn(*Bshape, Ve, 8, dtype=torch.float64, generator=gen_cpu)
    phi_e64 = eo_heatbath(xi, h64, coeffs, msq, eo64, fwd64, back64, L, tol=tol_acc, max_iter=max_iter)
    pi64 = torch.randn(*Bshape, V, 4, 4, dtype=torch.float64, generator=gen_cpu)

    def H(hh, pp, phi_e):
        kin = 0.5 * (pp * pp).sum(dim=(-3, -2, -1))
        return kin + eo_action(hh, phi_e, g, msq, eo64, fwd64, back64, L, tol=tol_acc, max_iter=max_iter)

    H_old = H(h64, pi64, phi_e64)

    # --- FP32 (device): MD proposal (single-pole eo force) ---
    h32 = h64.to(dtype=torch.float32, device=device)
    pi32 = pi64.to(dtype=torch.float32, device=device)
    phi_e32 = phi_e64.to(dtype=torch.float32, device=device)
    h_new32, pi_new32 = eo_integrate(h32, pi32, phi_e32, g, msq, eo_dev, fwd_dev, back_dev, L,
                                     eps, n_md, tol=tol_md, max_iter=max_iter, chrono=chrono)

    # --- FP64 (CPU): H_new + exact Metropolis (move off device BEFORE f64 cast; MPS quirk) ---
    h_new64 = h_new32.to(device=h64.device).to(dtype=torch.float64)
    pi_new64 = pi_new32.to(device=h64.device).to(dtype=torch.float64)
    dH = H(h_new64, pi_new64, phi_e64) - H_old

    u = torch.rand(Bshape, dtype=torch.float64, generator=gen_cpu)
    accept = u < torch.exp(torch.clamp(-dH, max=0.0))
    h_out = torch.where(accept[..., None, None, None], h_new64, h64)
    return h_out, dH, accept


def _omelyan_inner(h, pi, force_fast, T, n_inner, lam):
    """n_inner Omelyan 2MN steps of the FAST force over total MD time T (drift-kick-...)."""
    eps = T / n_inner
    half = 0.5 * eps
    for _ in range(n_inner):
        pi = pi + (lam * eps) * force_fast(h)
        h = h + half * pi
        pi = pi + ((1.0 - 2.0 * lam) * eps) * force_fast(h)
        h = h + half * pi
        pi = pi + (lam * eps) * force_fast(h)
    return h, pi


def eo_hb_integrate(h, pi, force_slow, force_fast, eps_o, n_outer, n_inner, lam=OMELYAN_LAMBDA):
    """Nested 2-timescale Omelyan (Sexton–Weingarten): the SLOW (ratio) force on the coarse
    outer step, a full inner Omelyan evolution of the FAST (heavy+aux) force between slow kicks.
    Reversible + area-preserving. Total slow-force evals = 3·n_outer (few); fast = 3·n_outer·n_inner."""
    half_o = 0.5 * eps_o
    for _ in range(n_outer):
        pi = pi + (lam * eps_o) * force_slow(h)
        h, pi = _omelyan_inner(h, pi, force_fast, half_o, n_inner, lam)
        pi = pi + ((1.0 - 2.0 * lam) * eps_o) * force_slow(h)
        h, pi = _omelyan_inner(h, pi, force_fast, half_o, n_inner, lam)
        pi = pi + (lam * eps_o) * force_slow(h)
    return h, pi


def eo_hb_trajectory(h, g, msq, mu2, coeffs_m, coeffs_mu, eo, fwd, back, L,
                     eps_o, n_outer, n_inner, rng_gen, tol_md=1e-4, tol_acc=1e-10, max_iter=8000):
    """One Hasenbusch even-odd RHMC trajectory (single dtype), 2-timescale.

    Splits det(M_e+m²)^{1/2} = det(M_e+μ²)^{1/2}·det[(M_e+m²)/(M_e+μ²)]^{1/2}:
      • heavy PF φ_H (mass μ², well-conditioned) — S_H = eo_action(μ²); fast force (+aux).
      • ratio PF φ_R — S_R = eo_ratio_action; slow force = (μ²−m²)·fermion_force, SMALL.
    Same target density as plain eo (det(M_e+m²)^{1/2}); the split just tames the stiff light
    force so a much larger effective step works. Returns (h_out, ΔH, accept)."""
    V = L ** 4
    Bshape = h.shape[:-3]
    dtype, device = h.dtype, h.device
    Ve = V // 2

    xi_H = torch.randn(*Bshape, Ve, 8, dtype=dtype, device=device, generator=rng_gen)
    phi_H = eo_heatbath(xi_H, h, coeffs_mu, mu2, eo, fwd, back, L, tol=tol_acc, max_iter=max_iter)
    xi_R = torch.randn(*Bshape, Ve, 8, dtype=dtype, device=device, generator=rng_gen)
    phi_R = eo_ratio_heatbath(xi_R, h, coeffs_m, coeffs_mu, msq, mu2, eo, fwd, back, L,
                              tol=tol_acc, max_iter=max_iter)
    pi = torch.randn(*Bshape, V, 4, 4, dtype=dtype, device=device, generator=rng_gen)

    def force_fast(hh):
        return eo_compute_force(hh, phi_H, g, mu2, eo, fwd, back, L, tol=tol_md, max_iter=max_iter)

    def force_slow(hh):
        return eo_ratio_force(hh, phi_R, msq, mu2, eo, fwd, back, L, tol=tol_md, max_iter=max_iter)

    def H(hh, pp):
        kin = 0.5 * (pp * pp).sum(dim=(-3, -2, -1))
        s_H = eo_action(hh, phi_H, g, mu2, eo, fwd, back, L, tol=tol_acc, max_iter=max_iter)   # incl aux
        s_R = eo_ratio_action(hh, phi_R, msq, mu2, eo, fwd, back, L, tol=tol_acc, max_iter=max_iter)
        return kin + s_H + s_R

    H_old = H(h, pi)
    h_new, pi_new = eo_hb_integrate(h, pi, force_slow, force_fast, eps_o, n_outer, n_inner)
    dH = H(h_new, pi_new) - H_old

    u = torch.rand(Bshape, dtype=dtype, device=device, generator=rng_gen)
    accept = u < torch.exp(torch.clamp(-dH, max=0.0))
    h_out = torch.where(accept[..., None, None, None], h_new, h)
    return h_out, dH, accept


def rhmc_trajectory(h, g, msq, coeffs, fwd, back, L, eps, n_md, rng_gen,
                    tol=1e-10, max_iter=8000):
    """One full RHMC trajectory: heatbath → Omelyan MD → Metropolis accept/reject.

    Returns (h_out, ΔH, accept) — ΔH and accept are per-config (*batch,).
    Run the integrator and ΔH in the working dtype; for the GPU path use FP32 MD
    and an FP64 accept/reject (here single-dtype for the FP64 validation chain)."""
    V = L ** 4
    Bshape = h.shape[:-3]
    dtype, device = h.dtype, h.device
    blocks = hopping_blocks(h, L, device=device, dtype=dtype)

    xi = torch.randn(*Bshape, V, 8, dtype=dtype, device=device, generator=rng_gen)
    phi = heatbath(xi, blocks, fwd, back, coeffs, msq, tol=tol, max_iter=max_iter)
    pi = torch.randn(*Bshape, V, 4, 4, dtype=dtype, device=device, generator=rng_gen)

    a0 = float(coeffs['a0'])
    alphas = torch.as_tensor(coeffs['alphas'], dtype=dtype, device=device)
    betas = torch.as_tensor(coeffs['betas'], dtype=dtype, device=device) + msq

    def hamiltonian(hh, pp):
        kin = 0.5 * (pp * pp).sum(dim=(-3, -2, -1))
        return kin + action(hh, phi, g, a0, alphas, betas, fwd, back, L, tol=tol, max_iter=max_iter)

    h_old_H = hamiltonian(h, pi)
    h_new, pi_new = integrate(h, pi, phi, g, alphas, betas, fwd, back, L,
                              eps, n_md, tol=tol, max_iter=max_iter)
    dH = hamiltonian(h_new, pi_new) - h_old_H                       # (*B,)

    u = torch.rand(Bshape, dtype=dtype, device=device, generator=rng_gen)
    accept = u < torch.exp(torch.clamp(-dH, max=0.0))              # Metropolis (*B,)
    h_out = torch.where(accept[..., None, None, None], h_new, h)
    return h_out, dH, accept


def rhmc_trajectory_mixed(h64, g, msq, coeffs, fwd64, back64, fwd_dev, back_dev, L,
                          eps, n_md, device, gen_dev, gen_cpu,
                          tol_md=1e-5, tol_acc=1e-10, max_iter=4000):
    """Mixed-precision trajectory: FP32 MD proposal on `device` (GPU) + FP64
    accept/reject on CPU. Heatbath and both Hamiltonians are FP64-tight, so the
    Metropolis test is EXACT — the FP32 MD only affects acceptance, never the
    sampled distribution. h64: FP64 (*batch, V, 4, 4) on CPU."""
    Bshape = h64.shape[:-3]
    V = L ** 4

    # --- FP64 (CPU): heatbath + momenta + H_old (exact) ---
    blocks64 = hopping_blocks(h64, L, device=h64.device, dtype=torch.float64)
    xi = torch.randn(*Bshape, V, 8, dtype=torch.float64, generator=gen_cpu)
    phi64 = heatbath(xi, blocks64, fwd64, back64, coeffs, msq, tol=tol_acc, max_iter=max_iter)
    pi64 = torch.randn(*Bshape, V, 4, 4, dtype=torch.float64, generator=gen_cpu)

    a0 = float(coeffs['a0'])
    al64 = torch.as_tensor(coeffs['alphas'], dtype=torch.float64)
    be64 = torch.as_tensor(coeffs['betas'], dtype=torch.float64) + msq

    def H(hh, pp, phi):
        kin = 0.5 * (pp * pp).sum(dim=(-3, -2, -1))
        return kin + action(hh, phi, g, a0, al64, be64, fwd64, back64, L, tol=tol_acc, max_iter=max_iter)

    H_old = H(h64, pi64, phi64)

    # --- FP32 (device): MD proposal ---
    h32 = h64.to(dtype=torch.float32, device=device)
    pi32 = pi64.to(dtype=torch.float32, device=device)
    phi32 = phi64.to(dtype=torch.float32, device=device)
    al32 = al64.to(dtype=torch.float32, device=device)
    be32 = be64.to(dtype=torch.float32, device=device)
    h_new32, pi_new32 = integrate(h32, pi32, phi32, g, al32, be32, fwd_dev, back_dev, L,
                                  eps, n_md, tol=tol_md, max_iter=max_iter)

    # --- FP64 (CPU): H_new + exact Metropolis (move off MPS BEFORE casting to f64) ---
    h_new64 = h_new32.cpu().to(dtype=torch.float64)
    pi_new64 = pi_new32.cpu().to(dtype=torch.float64)
    dH = H(h_new64, pi_new64, phi64) - H_old

    u = torch.rand(Bshape, dtype=torch.float64, generator=gen_cpu)
    accept = u < torch.exp(torch.clamp(-dH, max=0.0))
    h_out = torch.where(accept[..., None, None, None], h_new64, h64)
    return h_out, dH, accept


def measure_observables(h, L):
    """h-field order parameters, batched. h: (*batch, V, 4, 4) [site, μ, a].

    Returns (tet_m2, trQ2, m_h, Q):
      m_h   = (1/V) Σ_x h            (*batch, 4, 4)   — tetrad proxy ⟨h⟩_vol
      tet_m2 = |m_h|²                (*batch,)
      M_μν  = (1/V) Σ_{x,a} h_μ h_ν;  Q = M − (TrM/4)I  (*batch, 4, 4) — traceless metric
      trQ2  = Tr Q²                  (*batch,)
    m_h and Q are the per-trajectory instrumentation that lets the noise-immune
    detectors (Binder cumulant, ensemble shuffle floor) be formed post-hoc."""
    V = L ** 4
    m_h = h.mean(dim=-3)                                            # (*B, 4, 4)
    tet_m2 = (m_h * m_h).sum(dim=(-2, -1))
    M = torch.einsum('...vma,...vna->...mn', h, h) / V             # (*B, 4, 4)
    tr = M.diagonal(dim1=-2, dim2=-1).sum(dim=-1)                  # (*B,)
    eye = torch.eye(4, dtype=h.dtype, device=h.device)
    Q = M - (tr / 4.0)[..., None, None] * eye
    trQ2 = (Q * Q).sum(dim=(-2, -1))
    return tet_m2, trQ2, m_h, Q


# --- optional torch.compile of the hot stencil matvecs -------------------------------------
# EXACT op-fusion (no numerics change beyond fp reassociation ~machine-eps): ~2.6× on CPU at
# L=8; on CUDA `mode='reduce-overhead'` captures CUDA graphs to amortize the launch overhead
# that makes the eager CG launch-bound (the L=10/12 lever, needs the 3090). MPS gains little
# (~1.14×) — its inductor backend is weak. Rebinds the module-global matvecs so every caller
# (CG loops, force, heatbath) picks up the compiled version with no other code change.
# Opt-in: production drivers call enable_matvec_compile(); tests use eager (compile warmup cost).
_MATVEC_EAGER = {}


def enable_matvec_compile(mode="default"):
    """Compile apply_A / apply_AtA / apply_Me with torch.compile (idempotent). Call once before
    a production run. mode='reduce-overhead' on CUDA uses CUDA graphs; 'default' elsewhere."""
    global apply_A, apply_AtA, apply_Me
    if not _MATVEC_EAGER:
        _MATVEC_EAGER.update(A=apply_A, AtA=apply_AtA, Me=apply_Me)
    apply_A = torch.compile(_MATVEC_EAGER['A'], mode=mode)
    apply_AtA = torch.compile(_MATVEC_EAGER['AtA'], mode=mode)
    apply_Me = torch.compile(_MATVEC_EAGER['Me'], mode=mode)


def disable_matvec_compile():
    """Restore the eager matvecs (undo enable_matvec_compile)."""
    global apply_A, apply_AtA, apply_Me
    if _MATVEC_EAGER:
        apply_A, apply_AtA, apply_Me = _MATVEC_EAGER['A'], _MATVEC_EAGER['AtA'], _MATVEC_EAGER['Me']
