"""MLX port of the batched matrix-free stencil RHMC engine (`hs_rhmc_stencil`).

Same operator, same algorithms, same conventions as the certified torch engine —
one codebase for Apple-Silicon Metal (macOS) AND CUDA (Linux, via mlx[cuda]),
replacing the torch-MPS path whose per-op dispatch overhead dominates the MD
force cost. Function names/signatures mirror `hs_rhmc_stencil` (minus torch's
device/generator plumbing: MLX arrays live in unified memory; the compute
device is the stream, chosen here by dtype — float64 runs on the CPU stream
since Metal is FP32-only, everything else on the default (GPU) stream).

Operator (β=0, identity links), matching the dense oracle exactly:
    A_{(x,I),(y,J)} = Σ_{μ,a} h^a_{x,μ} CG[a]_{IJ} δ_{y,x+μ̂} − (transpose)
CG operator for the multishift solver: A†A = −A² (A real antisymmetric ⟹ PSD).

torch-free by design: Clifford constants come from src.core.constants; Zolotarev
coefficients from src.vestigial.hs_rhmc (numpy). The torch engine appears only
in the test suite, as the cross-engine oracle.
"""
import numpy as np
import mlx.core as mx

from src.core.constants import MAJORANA_GAMMA_8x8, MAJORANA_J1

# CG[a] = J₁Γ^a — same convention as hs_rhmc_torch._CG_np / the dense oracle.
_CG_NP = np.array([MAJORANA_J1 @ MAJORANA_GAMMA_8x8[a] for a in range(4)])

# Real-pseudofermion Gaussian normalization — see hs_rhmc_stencil.INV_SQRT2 for the
# full derivation. The intended weight is det(A†A+m²)^{1/4} (ONE Majorana;
# Lit-Search/Phase-5/HS+RHMC...Spin(4).md §60,64); omitting the 1/√2 samples
# det^{1/2} (Dirac) — the 2026-07-01 factor-2 flavor bug. Every heatbath here
# scales its output by INV_SQRT2.
INV_SQRT2 = 2.0 ** -0.5

_cg_cache = {}
_nbr_cache = {}
_eo_cache = {}


def _stream(dtype):
    """Compute stream by dtype: float64 must run on CPU (Metal is FP32-only)."""
    return mx.cpu if dtype == mx.float64 else mx.default_device()


def _cg_const(dtype):
    if dtype not in _cg_cache:
        _cg_cache[dtype] = mx.array(_CG_NP, dtype=dtype)
    return _cg_cache[dtype]


def neighbor_tables(L):
    """Forward/backward neighbor index tables, each (V, 4) int32.
    fwd[x, μ] = flat(x + ê_μ),  back[x, μ] = flat(x − ê_μ)  (periodic)."""
    if L in _nbr_cache:
        return _nbr_cache[L]
    V = L ** 4
    coords = np.array(np.unravel_index(np.arange(V), (L, L, L, L))).T  # (V, 4)
    fwd = np.zeros((V, 4), np.int32)
    back = np.zeros((V, 4), np.int32)
    for mu in range(4):
        f = coords.copy(); f[:, mu] = (f[:, mu] + 1) % L
        b = coords.copy(); b[:, mu] = (b[:, mu] - 1) % L
        fwd[:, mu] = np.ravel_multi_index(f.T, (L, L, L, L))
        back[:, mu] = np.ravel_multi_index(b.T, (L, L, L, L))
    out = (mx.array(fwd), mx.array(back))
    _nbr_cache[L] = out
    return out


def hopping_blocks(h, L, dtype=None):
    """block[..., x, μ, I, J] = Σ_a h[..., x, μ, a] · CG[a, I, J].

    h: (*batch, V, 4, 4) [site, μ, a].  Returns (*batch, V, 4, 8, 8)
    (μ at axis −3, so block^μ = blocks[..., μ, :, :])."""
    if not isinstance(h, mx.array):
        h = mx.array(np.asarray(h), dtype=dtype or mx.float32)
    elif dtype is not None and h.dtype != dtype:
        h = h.astype(dtype)
    with mx.stream(_stream(h.dtype)):
        return mx.einsum('...vma,aij->...vmij', h, _cg_const(h.dtype))


def apply_A(psi, blocks, fwd, back):
    """Apply the antisymmetric fermion matrix A to ψ, matrix-free.

    psi:    (*batch, V, 8)
    blocks: (*batch, V, 4, 8, 8) from `hopping_blocks` (μ axis = -3)
    Returns (*batch, V, 8) = A ψ.
    """
    with mx.stream(_stream(psi.dtype)):
        out = mx.zeros(psi.shape, dtype=psi.dtype)
        for mu in range(4):
            bmu = blocks[..., mu, :, :]                       # (*batch, V, 8, 8)
            psi_fwd = mx.take(psi, fwd[:, mu], axis=-2)       # ψ_{x+μ̂, J}
            # matmul (not einsum): mx.einsum does not broadcast mismatched ellipsis
            # batch dims (blocks (B,1,...) vs psi (B,K,...)); matmul does, numpy-style.
            out = out + mx.squeeze(bmu @ psi_fwd[..., None], -1)          # forward hop
            t = mx.squeeze(psi[..., None, :] @ bmu, -2)       # (ψᵀB)_i = Σ_j ψ_j b_{ji}
            out = out - mx.take(t, back[:, mu], axis=-2)      # backward hop: − t_{x−μ̂}
        return out


def apply_AtA(psi, blocks, fwd, back, shift=0.0):
    """Apply (A†A + shift·I) ψ = −A(Aψ) + shift·ψ  (A†A = −A², PSD)."""
    a_psi = apply_A(psi, blocks, fwd, back)
    with mx.stream(_stream(psi.dtype)):
        out = -apply_A(a_psi, blocks, fwd, back)
        if shift:
            out = out + shift * psi
        return out


def eo_tables(L):
    """Even-odd (parity) partition + half-size hop tables for the bipartite lattice.

    Mirrors `hs_rhmc_stencil.eo_tables` (see its docstring for the M_e = −D_eo D_oe
    reduction). EVEN L ONLY — odd L with periodic BC is not bipartite.

    Returns dict: even_idx, odd_idx (V/2,) int32; o2e_fwd/o2e_back (V/2,4) map an
    odd-half site's ±μ neighbor to its even-half index; e2o_fwd/e2o_back the dual.
    """
    if L % 2 != 0:
        raise ValueError(f"even-odd reduction requires even L (bipartite); got L={L}")
    if L in _eo_cache:
        return _eo_cache[L]
    V = L ** 4
    coords = np.array(np.unravel_index(np.arange(V), (L, L, L, L))).T   # (V, 4)
    parity = coords.sum(axis=1) % 2
    even_flat = np.where(parity == 0)[0]
    odd_flat = np.where(parity == 1)[0]
    pos = np.empty(V, np.int32)                       # flat → index within its parity group
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
        return (mx.array(pos[fwd_np[src_flat]]), mx.array(pos[back_np[src_flat]]))
    o2e_fwd, o2e_back = half(odd_flat)
    e2o_fwd, e2o_back = half(even_flat)
    out = dict(even_idx=mx.array(even_flat.astype(np.int32)),
               odd_idx=mx.array(odd_flat.astype(np.int32)),
               o2e_fwd=o2e_fwd, o2e_back=o2e_back, e2o_fwd=e2o_fwd, e2o_back=e2o_back)
    _eo_cache[L] = out
    return out


def _hop(psi_in, blocks_out, blocks_in, fwd_h, back_h):
    """One bipartite hop D: (in-parity) → (out-parity), mirroring `apply_A` split by parity.

    out_y = Σ_μ [ blocks_out[y,μ]·ψ_{y+μ} − blocks_in[y−μ,μ]ᵀ·ψ_{y−μ} ], with y±μ on the
    in-parity sublattice. Returns (*B, Vout, 8)."""
    out = None
    for mu in range(4):
        bo = blocks_out[..., mu, :, :]                                  # (*B, Vout, 8, 8)
        bi = blocks_in[..., mu, :, :]                                   # (*B, Vin, 8, 8)
        psi_fwd = mx.take(psi_in, fwd_h[:, mu], axis=-2)
        fwd_term = mx.squeeze(bo @ psi_fwd[..., None], -1)              # broadcast-safe matmul
        t_in = mx.squeeze(psi_in[..., None, :] @ bi, -2)                # bᵀψ at each in-site
        back_term = mx.take(t_in, back_h[:, mu], axis=-2)
        out = (fwd_term - back_term) if out is None else out + (fwd_term - back_term)
    return out


def apply_Me(psi_e, blocks, eo, shift=0.0):
    """Apply the even-block operator (M_e + shift) ψ_e on the half-size even sublattice.

    M_e = −D_eo D_oe (= the even block of A†A = −A²). blocks is the FULL
    (*B, V, 4, 8, 8) hopping table; `eo` from `eo_tables`. Returns (*B, V/2, 8).
    """
    with mx.stream(_stream(psi_e.dtype)):
        blocks_e = mx.take(blocks, eo['even_idx'], axis=-4)             # (*B, V/2, 4, 8, 8)
        blocks_o = mx.take(blocks, eo['odd_idx'], axis=-4)
        w_o = _hop(psi_e, blocks_o, blocks_e, eo['o2e_fwd'], eo['o2e_back'])   # D_oe ψ_e  (odd)
        v_e = _hop(w_o, blocks_e, blocks_o, eo['e2o_fwd'], eo['e2o_back'])     # D_eo w_o  (even)
        out = -v_e                                                      # M_e = −D_eo D_oe
        if shift:
            out = out + shift * psi_e
        return out


def _to_mx(a, dtype):
    if not isinstance(a, mx.array):
        return mx.array(np.asarray(a), dtype=dtype)
    return a.astype(dtype) if a.dtype != dtype else a


def _as_shift_tensor(shifts, nb, Bshape, dtype):
    """shifts (K,) or (*B, K) → σ broadcast tensor (*B, K, 1, 1) + K."""
    if not isinstance(shifts, mx.array):
        shifts = mx.array(np.asarray(shifts), dtype=dtype)
    elif shifts.dtype != dtype:
        shifts = shifts.astype(dtype)
    K = shifts.shape[-1]
    if shifts.ndim == 1:
        shifts = shifts.reshape((1,) * nb + (K,))
    sigma = mx.broadcast_to(shifts, Bshape + (K,)).reshape(Bshape + (K, 1, 1))
    return sigma, K


def _cg_loop(bk, matvec, sigma, tol, max_iter, x0=None, rel_to_b=False, check_every=8):
    """Shared K-parallel CG core: solve (Op + σ_k) x_k = bk[..., k, :, :] per (config, shift).

    bk: (*B, K, V', 8); matvec(p) applies the shift-free operator batched over K.
    Converged systems are masked out of further updates each iteration (in-graph,
    same semantics as the torch engine) — so the host break-check only needs to
    run every `check_every` iterations: converged systems just coast through ≤7
    masked no-op updates, mathematically identical. Between checks, async_eval
    keeps the GPU pipeline fed without a host sync — the per-iteration
    `bool(converged.all())` sync is what throttles a lazy-graph CG."""
    if x0 is None:
        x = mx.zeros(bk.shape, dtype=bk.dtype)
        r = bk
    else:
        x = x0
        r = bk - (matvec(x0) + sigma * x0)
    p = r
    rs = mx.sum(r * r, axis=(-2, -1))                     # (*B, K)
    ref = mx.sum(bk * bk, axis=(-2, -1)) if rel_to_b else rs
    tol_sq = tol * tol * mx.maximum(ref, 1e-300)
    converged = rs <= tol_sq
    zeros = mx.zeros(rs.shape, dtype=bk.dtype)

    for i in range(max_iter):
        if i % check_every == 0 and bool(mx.all(converged)):
            break
        Ap = matvec(p) + sigma * p
        pAp = mx.sum(p * Ap, axis=(-2, -1))
        alpha = mx.where(converged, zeros, rs / pAp)
        x = x + alpha[..., None, None] * p
        r = r - alpha[..., None, None] * Ap
        rs_new = mx.sum(r * r, axis=(-2, -1))
        beta = mx.where(converged, zeros, rs_new / rs)
        p = r + beta[..., None, None] * p
        rs = rs_new
        converged = mx.logical_or(converged, rs <= tol_sq)
        mx.async_eval(x, r, p, rs, converged)
    return x


def multishift_cg(b, blocks, fwd, back, shifts, tol=1e-8, max_iter=2000):
    """Solve (A†A + σ_k) x_k = b for all shifts σ_k, batched over configs.

    K-parallel conjugate gradient (identical algorithm to the torch engine):
    each (config, shift) system is a standard CG, all sharing ONE wide batched
    stencil matvec per iteration.

    b:      (*batch, V, 8) source (shared across shifts within a config)
    shifts: (K,) or (*batch, K)  — σ_k ≥ 0
    Returns x: (*batch, K, V, 8).
    """
    nb = b.ndim - 2
    Bshape = b.shape[:nb]
    V, S = b.shape[-2], b.shape[-1]
    with mx.stream(_stream(b.dtype)):
        sigma, K = _as_shift_tensor(shifts, nb, Bshape, b.dtype)
        blocks_k = mx.expand_dims(blocks, nb)             # (*B, 1, V, 4, 8, 8)
        bk = mx.broadcast_to(mx.expand_dims(b, nb), Bshape + (K, V, S))

        def matvec(p):
            return apply_AtA(p, blocks_k, fwd, back)

        return _cg_loop(bk, matvec, sigma, tol, max_iter)


def eo_multishift_cg(b, blocks, eo, shifts, tol=1e-8, max_iter=4000, x0=None):
    """Multishift CG on the even-block operator M_e (half size). Mirrors `multishift_cg`
    but with `apply_Me` — ~2× cheaper for the same spectrum. b: (*B, V/2, 8).

    `x0` (optional, (*B, V/2, 8)) warm-starts the solve (chronological inversion);
    convergence is relative to ‖b‖ so the result matches a cold start to the same tol."""
    nb = b.ndim - 2
    Bshape = b.shape[:nb]
    Ve, S = b.shape[-2], b.shape[-1]
    with mx.stream(_stream(b.dtype)):
        sigma, K = _as_shift_tensor(shifts, nb, Bshape, b.dtype)
        blocks_k = mx.expand_dims(blocks, nb)
        bk = mx.broadcast_to(mx.expand_dims(b, nb), Bshape + (K, Ve, S))
        x0k = None
        if x0 is not None:
            x0k = mx.broadcast_to(mx.expand_dims(x0, nb), Bshape + (K, Ve, S))

        def matvec(p):
            return apply_Me(p, blocks_k, eo)

        return _cg_loop(bk, matvec, sigma, tol, max_iter, x0=x0k, rel_to_b=True)


# --- dynamics: action, force, integrator ----------------------------------------------------

def estimate_lambda_max(blocks, fwd, back, V, n_iter=200, seed=0, v0=None):
    """Largest eigenvalue of A†A per config, via power iteration. Returns (*batch,)."""
    Bshape = blocks.shape[:-4]
    dtype = blocks.dtype
    with mx.stream(_stream(dtype)):
        if v0 is None:
            rng = np.random.default_rng(seed)
            v = mx.array(rng.standard_normal(tuple(Bshape) + (V, 8)), dtype=dtype)
        else:
            v = v0
        for _ in range(n_iter):
            w = apply_AtA(v, blocks, fwd, back)
            v = w / mx.sqrt(mx.maximum(mx.sum(w * w, axis=(-2, -1), keepdims=True), 1e-300))
            mx.eval(v)
        w = apply_AtA(v, blocks, fwd, back)
        return mx.sum(v * w, axis=(-2, -1)) / mx.sum(v * v, axis=(-2, -1))


def action(h, phi, g, alpha_0, alphas, betas, fwd, back, L, tol=1e-10, max_iter=5000):
    """RHMC h-action S = Σh²/(4g) + α₀ φ†φ + Σ_k α_k φ†ψ_k,  ψ_k=(A†A+β_k)⁻¹φ.

    (Excludes the momentum kinetic term — added at the Hamiltonian level.)
    h: (*batch, V, 4, 4),  phi: (*batch, V, 8).  Returns (*batch,) action."""
    blocks = hopping_blocks(h, L, dtype=h.dtype)
    with mx.stream(_stream(h.dtype)):
        alphas = _to_mx(alphas, h.dtype)
        betas = _to_mx(betas, h.dtype)
        psi = multishift_cg(phi, blocks, fwd, back, betas, tol=tol, max_iter=max_iter)  # (*B,K,V,8)

        s_aux = mx.sum(h * h, axis=(-3, -2, -1)) / (4.0 * g)           # (*B,)
        phi_phi = mx.sum(phi * phi, axis=(-2, -1))                     # (*B,)
        phi_psi = mx.sum(mx.expand_dims(phi, -3) * psi, axis=(-2, -1))  # (*B, K)
        return s_aux + float(alpha_0) * phi_phi + mx.sum(alphas * phi_psi, axis=-1)


def _pf_force_contraction(psi, a_psi, fwd, CG, nb):
    """Per-μ pseudofermion force pieces: term1/term2 of
    F^a_{x,μ} ∝ ψ(x)·CG[a]·Aψ(x+μ̂) − Aψ(x)·CG[a]·ψ(x+μ̂), batched over any leading
    dims of psi/a_psi. Yields (mu, -2·(term1−term2)) with shape (*lead, 4, V)."""
    for mu in range(4):
        psi_fwd = mx.take(psi, fwd[:, mu], axis=-2)
        a_psi_fwd = mx.take(a_psi, fwd[:, mu], axis=-2)
        cg_apsi = mx.einsum('aij,...vj->...avi', CG, a_psi_fwd)         # (*lead, 4, V, 8)
        term1 = mx.sum(mx.expand_dims(psi, -3) * cg_apsi, axis=-1)      # (*lead, 4, V)
        cg_psi = mx.einsum('aij,...vj->...avi', CG, psi_fwd)
        term2 = mx.sum(mx.expand_dims(a_psi, -3) * cg_psi, axis=-1)
        yield mu, -2.0 * (term1 - term2)


def compute_force(h, phi, g, alphas, betas, fwd, back, L, tol=1e-10, max_iter=5000):
    """MD force F = −∂S/∂h = −h/(2g) + pseudofermion term, batched over configs.

    Per μ: F^a_{x,μ} += Σ_k α_k (−2)[ψ_k(x)·CG[a]·Aψ_k(x+μ̂) − Aψ_k(x)·CG[a]·ψ_k(x+μ̂)].
    h: (*batch, V, 4, 4),  phi: (*batch, V, 8).  Returns (*batch, V, 4, 4)."""
    nb = h.ndim - 3
    blocks = hopping_blocks(h, L, dtype=h.dtype)
    with mx.stream(_stream(h.dtype)):
        alphas = _to_mx(alphas, h.dtype)
        betas = _to_mx(betas, h.dtype)
        psi = multishift_cg(phi, blocks, fwd, back, betas, tol=tol, max_iter=max_iter)  # (*B,K,V,8)
        a_psi = apply_A(psi, mx.expand_dims(blocks, nb), fwd, back)                     # (*B,K,V,8)

        CG = _cg_const(h.dtype)
        F = -h / (2.0 * g)                                              # (*B,V,4,4)
        K = alphas.shape[-1]
        al = alphas.reshape((K, 1, 1))                                  # align K with axis −3
        for mu, weighted_k in _pf_force_contraction(psi, a_psi, fwd, CG, nb):
            # psi carries lead dims (*B, K) ⟹ weighted_k: (*B, K, 4, V);
            # weight by α_k along the K axis (−3) and sum it out.
            wk = mx.sum(al * weighted_k, axis=-3)                       # (*B, 4, V)
            F[..., :, mu, :] = F[..., :, mu, :] + mx.swapaxes(wk, -1, -2)
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
    with mx.stream(_stream(h.dtype)):
        for _ in range(n_steps):
            pi = pi + (lam * eps) * force(h)
            h = h + half * pi
            pi = pi + ((1.0 - 2.0 * lam) * eps) * force(h)
            h = h + half * pi
            pi = pi + (lam * eps) * force(h)
            mx.eval(h, pi)
    return h, pi


# --- sampling: coefficients + heatbath ------------------------------------------------------

def make_rhmc_coeffs(lam_max, msq, n_poles, action_power=-0.5, hb_power=-0.75):
    """Zolotarev partial-fraction coeffs for the FULL real operator A†A+m².

    Identical to hs_rhmc_stencil.make_rhmc_coeffs (numpy-only): action ≈
    (A†A+m²)^{-1/2} (real φ ⟹ weight det(A†A)^{1/4}); heatbath builds
    (A†A+m²)^{+1/4} = (A†A+m²)·(A†A+m²)^{-3/4}. Spectral range [m², λmax+m²];
    raw `betas` are added to m² at CG-call sites."""
    from src.vestigial.hs_rhmc import compute_zolotarev_coefficients
    lo = msq if msq > 0 else max(float(lam_max) * 1e-7, 1e-12)
    hi = float(lam_max) + msq
    a0, alphas, betas = compute_zolotarev_coefficients(n_poles, lo, hi, action_power)
    a0_hb, alphas_hb, betas_hb = compute_zolotarev_coefficients(n_poles, lo, hi, hb_power)
    return dict(a0=float(a0), alphas=np.asarray(alphas), betas=np.asarray(betas),
                a0_hb=float(a0_hb), alphas_hb=np.asarray(alphas_hb), betas_hb=np.asarray(betas_hb))


def heatbath(xi, blocks, fwd, back, coeffs, msq, tol=1e-10, max_iter=8000):
    """φ = (A†A+m²)^{1/4} ξ / √2 = (A†A+m²)·r_{-3/4}(A†A+m²)·ξ / √2, so S_PF(φ)=½‖ξ‖².

    The 1/√2 (INV_SQRT2) makes the heatbath sample the action's conditional
    e^{−φ†(A†A+m²)^{-1/2}φ} ⟹ h-marginal det(A†A+m²)^{1/4} (ONE Majorana).
    ξ: (*batch, V, 8)."""
    with mx.stream(_stream(xi.dtype)):
        betas_hb = _to_mx(coeffs['betas_hb'], xi.dtype) + msq
        alphas_hb = _to_mx(coeffs['alphas_hb'], xi.dtype)
        psi = multishift_cg(xi, blocks, fwd, back, betas_hb, tol=tol, max_iter=max_iter)
        v = float(coeffs['a0_hb']) * xi + mx.sum(alphas_hb[..., None, None] * psi, axis=-3)
        return INV_SQRT2 * (apply_AtA(v, blocks, fwd, back) + msq * v)


def eo_heatbath(xi_e, h, coeffs, msq, eo, fwd, back, L, tol=1e-10, max_iter=8000):
    """φ_e = (M_e+m²)^{1/2} ξ_e / √2 = (M_e+m²)·r_{-1/2}(M_e+m²)·ξ_e / √2, so
    S_PF(φ_e)=½‖ξ_e‖² ⟹ h-marginal det(M_e+m²)^{1/2}=det(A†A+m²)^{1/4} (ONE Majorana).
    Reuses the coeffs' power −1/2 set (a0/alphas/betas) as r_{-1/2}. xi_e: (*B, V/2, 8)."""
    blocks = hopping_blocks(h, L, dtype=h.dtype)
    with mx.stream(_stream(xi_e.dtype)):
        betas = _to_mx(coeffs['betas'], xi_e.dtype) + msq
        alphas = _to_mx(coeffs['alphas'], xi_e.dtype)
        psi = eo_multishift_cg(xi_e, blocks, eo, betas, tol=tol, max_iter=max_iter)
        v = float(coeffs['a0']) * xi_e + mx.sum(alphas[..., None, None] * psi, axis=-3)
        return INV_SQRT2 * apply_Me(v, blocks, eo, shift=msq)


# --- even-odd dynamics ----------------------------------------------------------------------

def eo_action(h, phi_e, g, msq, eo, fwd, back, L, tol=1e-10, max_iter=5000):
    """Even-odd reduced action S = Σh²/(4g) + φ_e†(M_e+m²)⁻¹φ_e.

    Same fermion weight det(A†A+m²)^{1/4}=det(M_e+m²)^{1/2} as the full engine,
    represented by ONE even pseudofermion with action power −1 (single exact
    solve, no rational sum). φ_e: (*B, V/2, 8)."""
    blocks = hopping_blocks(h, L, dtype=h.dtype)
    with mx.stream(_stream(h.dtype)):
        psi = eo_multishift_cg(phi_e, blocks, eo, [msq], tol=tol, max_iter=max_iter)[..., 0, :, :]
        s_aux = mx.sum(h * h, axis=(-3, -2, -1)) / (4.0 * g)
        s_pf = mx.sum(phi_e * psi, axis=(-2, -1))
        return s_aux + s_pf


def _scatter_even(psi_e, eo, V):
    """Embed a half-size even vector into a full-lattice vector (zero on odd)."""
    Bshape = psi_e.shape[:-2]
    full = mx.zeros(tuple(Bshape) + (V, psi_e.shape[-1]), dtype=psi_e.dtype)
    full[..., eo['even_idx'], :] = psi_e
    return full


def eo_fermion_force(h, phi_e, msq, eo, fwd, back, L, tol=1e-10, max_iter=5000,
                     x0=None, return_psi=False):
    """Fermion part ONLY of the eo MD force: −∂/∂h[φ_e†(M_e+m²)⁻¹φ_e] (NO aux −h/2g term).
    ψ_e=(M_e+m²)⁻¹φ_e (ONE solve); contraction with the single vector ψ=scatter(ψ_e).

    `x0` warm-starts the solve (chronological inversion); `return_psi=True` also returns
    ψ_e so the integrator can feed it as the next step's x0."""
    V = L ** 4
    blocks = hopping_blocks(h, L, dtype=h.dtype)
    with mx.stream(_stream(h.dtype)):
        psi_e = eo_multishift_cg(phi_e, blocks, eo, [msq], tol=tol, max_iter=max_iter,
                                 x0=x0)[..., 0, :, :]
        psi = _scatter_even(psi_e, eo, V)                               # (*B, V, 8) on even
        a_psi = apply_A(psi, blocks, fwd, back)                         # (*B, V, 8) on odd

        CG = _cg_const(h.dtype)
        F = mx.zeros(h.shape, dtype=h.dtype)
        for mu, weighted in _pf_force_contraction(psi, a_psi, fwd, CG, h.ndim - 3):
            F[..., :, mu, :] = F[..., :, mu, :] + mx.swapaxes(weighted, -1, -2)
        return (F, psi_e) if return_psi else F


def eo_compute_force(h, phi_e, g, msq, eo, fwd, back, L, tol=1e-10, max_iter=5000,
                     x0=None, return_psi=False):
    """MD force for the even-odd action = −h/(2g) (aux) + eo_fermion_force. h: (*B, V, 4, 4).
    `x0`/`return_psi` thread chronological-inversion warm-start through the fermion solve."""
    if return_psi:
        Ff, psi_e = eo_fermion_force(h, phi_e, msq, eo, fwd, back, L, tol=tol, max_iter=max_iter,
                                     x0=x0, return_psi=True)
        with mx.stream(_stream(h.dtype)):
            return -h / (2.0 * g) + Ff, psi_e
    Ff = eo_fermion_force(h, phi_e, msq, eo, fwd, back, L, tol=tol, max_iter=max_iter, x0=x0)
    with mx.stream(_stream(h.dtype)):
        return -h / (2.0 * g) + Ff


def eo_integrate(h, pi, phi_e, g, msq, eo, fwd, back, L, eps, n_steps,
                 lam=OMELYAN_LAMBDA, tol=1e-10, max_iter=5000, chrono=False):
    """Omelyan 2MN MD for the even-odd action (force via `eo_compute_force`).

    chrono=False (default): cold-start every solve ⟹ deterministic in (h,π) ⟹ EXACTLY
    reversible. chrono=True: chronological inversion — each fermion solve warm-starts
    from the previous eval's ψ_e (~3-5× fewer CG iters); softens reversibility to O(tol),
    certified unbiased at chain level via Creutz — use only through trajectory drivers."""
    psi_cache = None

    def force(hh):
        nonlocal psi_cache
        if not chrono:
            return eo_compute_force(hh, phi_e, g, msq, eo, fwd, back, L, tol=tol, max_iter=max_iter)
        F, psi_cache = eo_compute_force(hh, phi_e, g, msq, eo, fwd, back, L, tol=tol,
                                        max_iter=max_iter, x0=psi_cache, return_psi=True)
        return F

    half = 0.5 * eps
    with mx.stream(_stream(h.dtype)):
        for _ in range(n_steps):
            pi = pi + (lam * eps) * force(h)
            h = h + half * pi
            pi = pi + ((1.0 - 2.0 * lam) * eps) * force(h)
            h = h + half * pi
            pi = pi + (lam * eps) * force(h)
            mx.eval(h, pi)
    return h, pi


# --- trajectories + measurement -------------------------------------------------------------

def _cast(x, dtype):
    """dtype cast that never touches the GPU stream — MLX rejects any op with a
    float64 operand on Metal, INCLUDING the cast itself (the analogue of torch-MPS's
    'move off device before the f64 cast' quirk)."""
    with mx.stream(mx.cpu):
        return x.astype(dtype)


def eo_rhmc_trajectory_mixed(h64, g, msq, coeffs, eo, fwd, back, L, eps, n_md, rng,
                             tol_md=1e-4, tol_acc=1e-10, max_iter=8000, chrono=False):
    """Mixed-precision EVEN-ODD trajectory: FP32 MD proposal on the default device
    (Metal / CUDA) + FP64 accept/reject on the CPU stream. The production path.

    Unlike the torch engine, ONE set of tables serves both stages (MLX unified
    memory — no device-resident copies), and the compute device is picked per-op
    by dtype. The MD force and accept/reject are each a SINGLE (M_e+m²)⁻¹ solve;
    FP32 MD only affects acceptance efficiency — the FP64 Metropolis test is
    EXACT (same fermion weight det(M_e+m²)^{1/2}=det(A†A+m²)^{1/4} as the full
    engine). Noise from a numpy Generator `rng` (framework-independent), draw
    order (ξ, π, u) as in the torch engine. h64: FP64 (*batch, V, 4, 4).
    Returns (h_out, ΔH, accept), per-config."""
    Bshape = tuple(h64.shape[:-3])
    V = L ** 4
    Ve = V // 2
    F64 = mx.float64

    # --- FP64 (CPU stream): heatbath + momenta + H_old (exact) ---
    xi = mx.array(rng.standard_normal(Bshape + (Ve, 8)), dtype=F64)
    phi_e64 = eo_heatbath(xi, h64, coeffs, msq, eo, fwd, back, L, tol=tol_acc, max_iter=max_iter)
    pi64 = mx.array(rng.standard_normal(Bshape + (V, 4, 4)), dtype=F64)

    def H(hh, pp, phi_e):
        S = eo_action(hh, phi_e, g, msq, eo, fwd, back, L, tol=tol_acc, max_iter=max_iter)
        with mx.stream(mx.cpu):        # seam arithmetic on f64 must stay off the GPU stream
            return 0.5 * mx.sum(pp * pp, axis=(-3, -2, -1)) + S

    H_old = H(h64, pi64, phi_e64)

    # --- FP32 (default device): MD proposal (single-pole eo force) ---
    h32 = _cast(h64, mx.float32)
    pi32 = _cast(pi64, mx.float32)
    phi_e32 = _cast(phi_e64, mx.float32)
    h_new32, pi_new32 = eo_integrate(h32, pi32, phi_e32, g, msq, eo, fwd, back, L,
                                     eps, n_md, tol=tol_md, max_iter=max_iter, chrono=chrono)

    # --- FP64 (CPU stream): H_new + exact Metropolis ---
    h_new64 = _cast(h_new32, F64)
    pi_new64 = _cast(pi_new32, F64)
    H_new = H(h_new64, pi_new64, phi_e64)

    u = mx.array(rng.random(Bshape), dtype=F64)
    with mx.stream(mx.cpu):
        dH = H_new - H_old
        accept = u < mx.exp(mx.minimum(-dH, 0.0))
        h_out = mx.where(accept[..., None, None, None], h_new64, h64)
        mx.eval(h_out, dH, accept)
    return h_out, dH, accept


def measure_observables(h, L):
    """h-field order parameters, batched. h: (*batch, V, 4, 4) [site, μ, a].

    Returns (tet_m2, trQ2, m_h, Q):
      m_h   = (1/V) Σ_x h            (*batch, 4, 4)   — tetrad proxy ⟨h⟩_vol
      tet_m2 = |m_h|²                (*batch,)
      M_μν  = (1/V) Σ_{x,a} h_μ h_ν;  Q = M − (TrM/4)I  (*batch, 4, 4) — traceless metric
      trQ2  = Tr Q²                  (*batch,)
    m_h and Q are the per-trajectory instrumentation for the noise-immune
    detectors (Binder cumulant, ensemble shuffle floor)."""
    V = L ** 4
    with mx.stream(_stream(h.dtype)):
        m_h = mx.mean(h, axis=-3)                                       # (*B, 4, 4)
        tet_m2 = mx.sum(m_h * m_h, axis=(-2, -1))
        M = mx.sum(h @ mx.swapaxes(h, -1, -2), axis=-3) / V             # Σ_v h_v h_vᵀ / V
        tr = mx.sum(mx.diagonal(M, axis1=-2, axis2=-1), axis=-1)        # (*B,)
        eye = mx.eye(4, dtype=h.dtype)
        Q = M - (tr / 4.0)[..., None, None] * eye
        trQ2 = mx.sum(Q * Q, axis=(-2, -1))
        return tet_m2, trQ2, m_h, Q
