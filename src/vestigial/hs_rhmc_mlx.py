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


def _cg_loop(bk, matvec, sigma, tol, max_iter, x0=None, rel_to_b=False):
    """Shared K-parallel CG core: solve (Op + σ_k) x_k = bk[..., k, :, :] per (config, shift).

    bk: (*B, K, V', 8); matvec(p) applies the shift-free operator batched over K.
    Converged systems are masked out of further updates (same semantics as the
    torch engine). One mx.eval per iteration syncs the carries — the lazy-graph
    analogue of torch's per-iteration `bool(converged.all())`."""
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

    for _ in range(max_iter):
        if bool(mx.all(converged)):
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
        mx.eval(x, r, p, rs, converged)
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
