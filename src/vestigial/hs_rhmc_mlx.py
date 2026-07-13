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

Production driver + operator guide (resource profile, m→0 targeting, recipes):
`scripts/run_rhmc_gpu_production.py --backend mlx` and `docs/RHMC_MLX_RUNBOOK.md`.
The `refined` trajectory (FP32 GPU inner + FP64 CPU residual → FP64-exact
Metropolis) is the production path; `mixed` (FP64 accept/reject on the CPU
stream) is a portable fallback only.

⚠️ Metal is FP32-only: every op with a float64 operand — including casts and
array slices `x[0]` — must run on the CPU stream (`with mx.stream(mx.cpu)`),
else MLX raises "float64 is not supported on the GPU". The test suite pins the
default device to CPU (autouse fixture), which masks such seams; verify any new
FP64 path under the GPU default device separately.
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
        # default the dtype from the input array (float64 numpy → float64), not to
        # float32 — `dtype or mx.float32` would silently downcast an f64 numpy config.
        if dtype is None:
            arr = np.asarray(h)
            dtype = mx.float64 if arr.dtype == np.float64 else mx.float32
        h = mx.array(np.asarray(h), dtype=dtype)
    target = dtype if dtype is not None else h.dtype
    with mx.stream(_stream(target)):              # open the (dtype-correct) stream FIRST,
        if h.dtype != target:                     # then cast inside it — an f64 cast must
            h = h.astype(target)                  # not run on the GPU default stream
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
    in-parity sublattice. psi_in (*B, K, Vin, 8); blocks_* (*B, 1, V*, 4, 8, 8) (the K
    axis broadcast). Returns (*B, K, Vout, 8).

    K-batched contraction via EXPLICIT-INDEX einsum, not broadcast matmul: the matmul
    form `bo(B,1,V,8,8) @ psi(B,K,V,8,1)` re-materializes the blocks per shift — the
    measured per-iteration cost scaled ~linearly in K (3.11 ms at K=44 vs 0.52 ms for
    einsum, 6×; 2.5× even at K=1; perf audit 2026-07-13). Also accepts the plain
    (no-K) contract psi (*B, Vin, 8) with blocks (*B, V*, 4, 8, 8) — used by the
    full-wrapper `apply_Me` (e.g. the heatbath's final FP64 matvec); both ranks are
    normalized to a flat batch + K so one subscript string serves every caller."""
    S = psi_in.shape[-1]
    kbatched = (blocks_out.ndim == psi_in.ndim + 2 and blocks_out.ndim >= 5
                and blocks_out.shape[-5] == 1)              # blocks carry a K-broadcast axis
    if kbatched:
        K, Vin = psi_in.shape[-3], psi_in.shape[-2]
        Bshape = psi_in.shape[:-3]
    else:
        K, Vin = 1, psi_in.shape[-2]
        Bshape = psi_in.shape[:-2]
    Vout = blocks_out.shape[-4]
    p = psi_in.reshape((-1, K, Vin, S))
    bo = blocks_out.reshape((-1,) + tuple(blocks_out.shape[-4:]))       # (Bf, Vout, 4, 8, 8)
    bi = blocks_in.reshape((-1,) + tuple(blocks_in.shape[-4:]))         # (Bf, Vin, 4, 8, 8)
    out = None
    for mu in range(4):
        psi_fwd = mx.take(p, fwd_h[:, mu], axis=-2)                     # (Bf, K, Vout, 8)
        fwd_term = mx.einsum('bvij,bkvj->bkvi', bo[..., mu, :, :], psi_fwd)
        t_in = mx.einsum('bvji,bkvj->bkvi', bi[..., mu, :, :], p)       # (bᵀψ)_i at in-sites
        back_term = mx.take(t_in, back_h[:, mu], axis=-2)
        out = (fwd_term - back_term) if out is None else out + (fwd_term - back_term)
    return out.reshape(Bshape + ((K, Vout, S) if kbatched else (Vout, S)))


def _split_eo(blocks, eo):
    """Gather the even/odd parity partitions of the hopping table ONCE.

    blocks: (*B, V, 4, 8, 8) → (blocks_e, blocks_o), each (*B, V/2, 4, 8, 8). Hoist this
    out of a CG loop (blocks are constant for a whole solve) and feed the result to
    apply_Me_split, so the full-table index-select is not redone every matvec."""
    with mx.stream(_stream(blocks.dtype)):
        return (mx.take(blocks, eo['even_idx'], axis=-4),
                mx.take(blocks, eo['odd_idx'], axis=-4))


def apply_Me_split(psi_e, blocks_eo, eo, shift=0.0):
    """(M_e + shift) ψ_e from PRE-GATHERED even/odd blocks `blocks_eo = (blocks_e, blocks_o)`.

    M_e = −D_eo D_oe (the even block of A†A = −A²). This is the per-iteration matvec of the
    even-odd CG; the gather is done once by `_split_eo` and reused across all iterations."""
    blocks_e, blocks_o = blocks_eo
    with mx.stream(_stream(psi_e.dtype)):
        w_o = _hop(psi_e, blocks_o, blocks_e, eo['o2e_fwd'], eo['o2e_back'])   # D_oe ψ_e  (odd)
        v_e = _hop(w_o, blocks_e, blocks_o, eo['e2o_fwd'], eo['e2o_back'])     # D_eo w_o  (even)
        out = -v_e                                                      # M_e = −D_eo D_oe
        if shift:
            out = out + shift * psi_e
        return out


def apply_Me(psi_e, blocks, eo, shift=0.0):
    """Apply the even-block operator (M_e + shift) ψ_e on the half-size even sublattice.

    blocks is the FULL (*B, V, 4, 8, 8) hopping table; `eo` from `eo_tables`. Returns
    (*B, V/2, 8). Thin wrapper that gathers the parity partitions then calls
    `apply_Me_split`; inside a CG loop gather once via `_split_eo` and call
    `apply_Me_split` directly to avoid re-gathering the full table every iteration."""
    return apply_Me_split(psi_e, _split_eo(blocks, eo), eo, shift=shift)


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

    Handles both a source broadcast across shifts (multishift solve) and a distinct
    per-shift source (the iterative-refinement correction step) — it only reads
    bk[..., k, :, :] per system either way.

    bk: (*B, K, V', 8); matvec(p) applies the shift-free operator batched over K.
    Converged systems are masked out of further updates each iteration (in-graph,
    same semantics as the torch engine); between checks, async_eval keeps the GPU
    pipeline fed without a host sync — the per-iteration `bool(converged.all())`
    sync is what throttles a lazy-graph CG.

    ACTIVE-SHIFT NARROWING (perf audit 2026-07-13): the per-iteration cost scales
    ~linearly with the working K (measured 1.6 ms K=1 → 81 ms K=44 at L=8 R=16),
    so masked coasting made the 44-pole heatbath pay full width for thousands of
    iterations after the large, log-spaced shifts converged. At each host
    checkpoint, shifts converged across ALL batch configs are sliced OUT of the
    working set (their frozen solutions parked and re-assembled at exit). This is
    value-preserving: each (config, shift) system's CG arithmetic is elementwise
    independent, and the in-graph mask already froze the parked solution at its
    convergence iteration."""
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

    K = bk.shape[-3]
    active = np.arange(K)          # original-K indices of the current working set
    parked = {}                    # original k → frozen solution slice (*B, V', 8)

    for i in range(max_iter):
        if i % check_every == 0:
            conv_np = np.array(converged)                 # host sync (was bool(mx.all(...)))
            if conv_np.all():
                break
            if active.size > 1:
                conv_k = conv_np.reshape(-1, active.size).all(axis=0)   # per-shift, all configs
                if conv_k.any():
                    done, keep = np.nonzero(conv_k)[0], np.nonzero(~conv_k)[0]
                    for j in done:
                        parked[int(active[j])] = x[..., j, :, :]
                    keep_idx = mx.array(keep)
                    x = mx.take(x, keep_idx, axis=-3)
                    r = mx.take(r, keep_idx, axis=-3)
                    p = mx.take(p, keep_idx, axis=-3)
                    sigma = mx.take(sigma, keep_idx, axis=-3)
                    rs = mx.take(rs, keep_idx, axis=-1)
                    tol_sq = mx.take(tol_sq, keep_idx, axis=-1)
                    converged = mx.take(converged, keep_idx, axis=-1)
                    zeros = mx.zeros(rs.shape, dtype=bk.dtype)
                    active = active[keep]
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

    if parked:                     # re-assemble full-K output in original shift order
        slices = {int(k): x[..., j, :, :] for j, k in enumerate(active)}
        slices.update(parked)
        x = mx.stack([slices[k] for k in range(K)], axis=-3)
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
        blocks_k_eo = _split_eo(blocks_k, eo)     # gather even/odd ONCE, reuse every iteration
        bk = mx.broadcast_to(mx.expand_dims(b, nb), Bshape + (K, Ve, S))
        x0k = None
        if x0 is not None:
            x0k = mx.broadcast_to(mx.expand_dims(x0, nb), Bshape + (K, Ve, S))

        def matvec(p):
            return apply_Me_split(p, blocks_k_eo, eo)

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
        for i in range(n_iter):
            w = apply_AtA(v, blocks, fwd, back)
            v = w / mx.sqrt(mx.maximum(mx.sum(w * w, axis=(-2, -1), keepdims=True), 1e-300))
            mx.async_eval(v)                    # keep the pipeline fed without a host barrier
            if i % 16 == 15:
                mx.eval(v)                      # bound graph depth periodically
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


def make_eo_ratio_sqrt_coeffs(a, b, lam_max, n_poles):
    """Partial fractions for the Hasenbusch RATIO heatbath g(x) = ((x+a)/(x+b))^{1/2},
    a = m² < b = μ² (the split mass). Used to draw φ = INV_SQRT2·g(M_e)ξ for the ratio
    pseudofermion whose action S = φ†(M_e+b)(M_e+a)⁻¹φ contributes the exact factor
    det[(M_e+a)/(M_e+b)]^{1/2} (power-1 action ⟹ single exact solve, no rational).

    Construction (Phase-5s DR §4-5 variable transform): with t = (x+a)/(x+b) the target
    is t^{1/2} = t·r_{-1/2}(t) (the A-trick), where r_{-1/2} is standard Zolotarev over
    t ∈ [a/b, (λmax+a)/(λmax+b)] — conditioning κ_t = b/a, NOT λmax/a, so ~12 poles
    suffice where the direct heatbath needs 44 at m=0.05. Möbius back-substitution
    yields the standard form

        g(x) ≈ A + B/(x+b) + Σ_k w_k/(x+e_k),   e_k = (a + d_k b)/(1+d_k) ∈ (a, b),

    applied with ONE multishift solve over shifts {b} ∪ {e_k}. Pass `lam_max` already
    safety-margined (callers use 1.25×the power-iteration estimate, as make_rhmc_coeffs).
    """
    from src.vestigial.hs_rhmc import compute_zolotarev_coefficients
    t_lo = a / b
    t_hi = (lam_max + a) / (lam_max + b)
    c0, cks, dks = compute_zolotarev_coefficients(n_poles, t_lo, t_hi, -0.5)
    cks, dks = np.asarray(cks), np.asarray(dks)
    ek = (a + dks * b) / (1.0 + dks)
    wk = cks * (a - ek) / (1.0 + dks)
    A = float(c0 + np.sum(cks / (1.0 + dks)))
    B = float(c0 * (a - b))
    return dict(A=A, B=B, w=wk, e=ek, a=float(a), b=float(b))


def eo_ratio_sqrt_max_relerr(ratio_coeffs, lam_max, n_grid=4000):
    """Unsigned max relative error of `make_eo_ratio_sqrt_coeffs` partial fractions vs
    the exact g(x) = ((x+a)/(x+b))^{1/2} over x ∈ [0, lam_max] (dense log grid + the
    x=0 endpoint). The ratio-heatbath analogue of `zolotarev_max_relerr` — gate on
    THIS, not on a consistency ratio (signed averages equioscillation-cancel)."""
    rc = ratio_coeffs
    a, b = rc['a'], rc['b']
    x = np.concatenate([[0.0], np.exp(np.linspace(np.log(max(a * 1e-3, 1e-12)),
                                                  np.log(lam_max), n_grid))])
    g = np.sqrt((x + a) / (x + b))
    r = (rc['A'] + rc['B'] / (x + b)
         + np.sum(np.asarray(rc['w'])[:, None] / (x[None, :] + np.asarray(rc['e'])[:, None]),
                  axis=0))
    return float(np.max(np.abs(r / g - 1.0)))


def zolotarev_max_relerr(a0, alphas, betas, lo, hi, power=-0.5, n_grid=4000):
    """Max relative error of the partial-fraction rational r(x)=a0+Σ_k alphas_k/(x+betas_k)
    vs the target x^power, over [lo, hi] on a dense log grid.

    The UNSIGNED quality gate for a Zolotarev fractional-power approximation. The
    heatbath-consistency ratio S_PF/(½‖ξ‖²) is a SIGNED spectral average of this same error,
    so equioscillation cancellation can drive it near 1 even when the true (max) error is
    large — size n_poles against THIS, not the ratio. The eo heatbath's only rational-approx
    locus is the power −1/2 set (a0/alphas/betas); the action + MD force are single-pole
    exact. Pure numpy (no MLX/Metal)."""
    a0 = float(a0)
    alphas = np.asarray(alphas, dtype=float)
    betas = np.asarray(betas, dtype=float)
    x = np.exp(np.linspace(np.log(lo), np.log(hi), n_grid))
    r = a0 + np.sum(alphas[:, None] / (x[None, :] + betas[:, None]), axis=0)
    return float(np.max(np.abs(r * x ** (-power) - 1.0)))


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


def _cast_to(x, dtype, device):
    """Cast `x` to `dtype`, doing any float64-involving cast on the CPU stream (Metal is
    FP32-only), and materialize the result on `device`'s stream.

    A float64 target is CPU-only regardless of `device` (Metal rejects f64) — the guard
    below prevents an f64-on-GPU crash for a float64 target reached with a GPU `device`.
    NOTE: this only pins the dtype and pre-materializes; where the RESULT's downstream ops
    actually run is governed by `_stream(dtype)` at their call sites (f64→CPU,
    f32→default device), so the FP32 inner CG lands on the GPU when it is the default
    device — `device` here does not by itself pin subsequent placement."""
    if dtype == mx.float64 or x.dtype == mx.float64:
        with mx.stream(mx.cpu):                    # any f64 operand → CPU stream
            out = x.astype(dtype)
            mx.eval(out)
            return out
    with mx.stream(device):                        # GPU-legal target, GPU-legal source
        out = x.astype(dtype)
        mx.eval(out)
        return out


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


class RefinementNotConverged(RuntimeError):
    """The refined solve exhausted max_outer without reaching the FP64 tolerance.

    Silent under-convergence would bias the exact-Metropolis test (and, for the
    heatbath, the sampled ensemble — which Metropolis cannot correct). Carries the
    worst relative residual so the caller can raise max_outer / inner_tol or the mass."""

    def __init__(self, worst_rel_resid, tol, max_outer):
        self.worst_rel_resid = worst_rel_resid
        super().__init__(
            f"eo_multishift_cg_refined did not reach tol={tol:.1e} in max_outer={max_outer} "
            f"(worst relative residual {worst_rel_resid:.2e}). A non-converged solve biases "
            f"the FP64-exact Metropolis test / heatbath. Increase max_outer or inner_tol, or "
            f"raise the mass; pass strict=False to accept the best-effort result.")


def eo_multishift_cg_refined(b64, h64, eo, shifts, L, device, tol=1e-10, inner_tol=3e-4,
                             max_outer=12, max_inner=4000, strict=True):
    """FP64-accurate even-odd multishift solve via FP32-inner / FP64-residual ITERATIVE
    REFINEMENT — the trajectory-level speed brick.

    Solves (M_e + σ_k) x_k = b64 for all k to FP64 relative residual `tol`, doing the
    heavy CG in FP32 on `device` (Metal / CUDA) and the residual + accumulation in FP64
    on the CPU stream. Each outer pass shrinks the TRUE (FP64) residual by ~`inner_tol`,
    so ~3–4 passes reach FP64 accuracy while every CG iteration runs at FP32 speed. This
    moves the eo heatbath + accept/reject solves off the (slow) MLX CPU backend onto the
    GPU — the fix for the FP64-CPU trajectory bottleneck (Metal is FP32-only).

    `strict=True` (default) raises `RefinementNotConverged` if `max_outer` passes do not
    reach `tol` — a non-converged solve silently biases the exact-Metropolis test, so it
    must be loud (matters as m→0, where M_e+σ conditioning worsens). `strict=False`
    returns the best-effort result.

    b64: (*batch, V/2, 8) FP64;  h64: (*batch, V, 4, 4) FP64.
    Returns x: FP64 (*batch, K, V/2, 8)."""
    nb = b64.ndim - 2
    Bshape = tuple(b64.shape[:nb])
    Ve, S = b64.shape[-2], b64.shape[-1]

    with mx.stream(mx.cpu):
        sigma64, K = _as_shift_tensor(shifts, nb, Bshape, mx.float64)
        blocks64 = mx.expand_dims(hopping_blocks(h64, L, dtype=mx.float64), nb)   # (*B,1,V,...)
        x = mx.zeros(Bshape + (K, Ve, S), dtype=mx.float64)
        bk64 = mx.broadcast_to(mx.expand_dims(b64, nb), Bshape + (K, Ve, S))
        bnorm = mx.maximum(mx.sqrt(mx.sum(bk64 * bk64, axis=(-2, -1))), 1e-300)

    blocks64_eo = _split_eo(blocks64, eo)         # gather even/odd ONCE (hoisted out of the loop)

    # FP32 operator on `device`
    sigma32 = _cast_to(sigma64, mx.float32, device)
    blocks32 = mx.expand_dims(hopping_blocks(_cast_to(h64, mx.float32, device), L,
                                             dtype=mx.float32), nb)
    blocks32_eo = _split_eo(blocks32, eo)

    def matvec32(p):
        return apply_Me_split(p, blocks32_eo, eo)

    def fp64_residual(xx):                         # r = b − (M_e+σ)x, ‖r‖ per (config,shift)
        r = bk64 - (apply_Me_split(xx, blocks64_eo, eo) + sigma64 * xx)
        return r, mx.sqrt(mx.sum(r * r, axis=(-2, -1)))

    converged = False
    for _ in range(max_outer):
        with mx.stream(mx.cpu):
            r64, rnorm = fp64_residual(x)          # FULL residual — re-verifies parked shifts
            done_np = np.array(rnorm <= tol * bnorm)                       # (*B, K) host-side
            if done_np.all():
                converged = True
                break
            # OUTER NARROWING (perf audit 2026-07-13): shifts already at the FP64 tol for
            # every config skip the correction solve — each skipped solve saves a full
            # inner CG run to inner_tol-relative on a negligible source (the large
            # Zolotarev shifts retire after 1-2 passes; only the ~m² tail keeps refining).
            act = np.nonzero(~done_np.reshape(-1, K).all(axis=0))[0]
            r64a = mx.take(r64, mx.array(act), axis=-3) if act.size < K else r64
        r32 = _cast_to(r64a, mx.float32, device)
        sigma32a = mx.take(sigma32, mx.array(act), axis=-3) if act.size < K else sigma32
        # the refinement correction is a plain CG with a per-shift source r32 — the
        # x0=None / rel_to_b=False case of _cg_loop (residual relative to r32 itself).
        d32 = _cg_loop(r32, matvec32, sigma32a, inner_tol, max_inner)
        with mx.stream(mx.cpu):
            d64 = _cast_to(d32, mx.float64, mx.cpu)
            if act.size < K:       # scatter-add corrections into the active slots only
                slices = [x[..., k, :, :] for k in range(K)]
                for j, k in enumerate(act):
                    slices[k] = slices[k] + d64[..., j, :, :]
                x = mx.stack(slices, axis=-3)
            else:
                x = x + d64
            mx.eval(x)

    if not converged:                             # verify the FINAL x (post last correction)
        with mx.stream(mx.cpu):
            _, rnorm = fp64_residual(x)
            converged = bool(mx.all(rnorm <= tol * bnorm))
            worst = float(mx.max(rnorm / bnorm))
        if not converged and strict:
            raise RefinementNotConverged(worst, tol, max_outer)
    return x


def eo_action_refined(h, phi_e, g, msq, eo, L, device, tol=1e-10, inner_tol=3e-4,
                      max_outer=12, max_inner=4000):
    """`eo_action` with the (M_e+m²)⁻¹ solve done by the mixed-precision refined solver.
    Identical value to `eo_action` (to FP64 `tol`); the heavy CG runs FP32 on `device`."""
    psi_k = eo_multishift_cg_refined(phi_e, h, eo, [msq], L, device, tol=tol, inner_tol=inner_tol,
                                     max_outer=max_outer, max_inner=max_inner)
    with mx.stream(mx.cpu):
        psi = psi_k[..., 0, :, :]              # f64 slice must stay on the CPU stream
        s_aux = mx.sum(h * h, axis=(-3, -2, -1)) / (4.0 * g)
        s_pf = mx.sum(phi_e * psi, axis=(-2, -1))
        return s_aux + s_pf


def eo_heatbath_refined(xi_e, h, coeffs, msq, eo, L, device, tol=1e-10, inner_tol=3e-4,
                        max_outer=12, max_inner=4000):
    """`eo_heatbath` with the r_{-1/2} K-pole multishift done by the refined solver.
    Same φ_e (to FP64 `tol`) as `eo_heatbath`; the heavy CG runs FP32 on `device`. The
    final (M_e+m²)·v matvec stays FP64 on the CPU stream (one matvec, not a solve)."""
    with mx.stream(mx.cpu):
        betas = _to_mx(coeffs['betas'], mx.float64) + msq
        alphas = _to_mx(coeffs['alphas'], mx.float64)
    psi = eo_multishift_cg_refined(xi_e, h, eo, betas, L, device, tol=tol, inner_tol=inner_tol,
                                   max_outer=max_outer, max_inner=max_inner)
    with mx.stream(mx.cpu):
        blocks64 = hopping_blocks(h, L, dtype=mx.float64)
        v = float(coeffs['a0']) * xi_e + mx.sum(alphas[..., None, None] * psi, axis=-3)
        return INV_SQRT2 * apply_Me(v, blocks64, eo, shift=msq)


# --- Hasenbusch (K=1) mass-preconditioned trajectory (Phase-5s DR) -------------------------
#
# det(M_e+m²)^{1/2} = det(M_e+μ²)^{1/2} · det[(M_e+m²)/(M_e+μ²)]^{1/2}, exact for any μ².
# Two REAL pseudofermions, both with power-1 (single-exact-solve) actions:
#   HEAVY:  S_H = φ_H†(M_e+μ²)⁻¹φ_H            (existing machinery, m²→μ²; κ=λmax/μ² small)
#   RATIO:  S_R = φ_R†(M_e+μ²)(M_e+m²)⁻¹φ_R = φ_R†φ_R + (μ²−m²)·φ_R†(M_e+m²)⁻¹φ_R
# The hard (M_e+m²)⁻¹ solve survives only in the RATIO force/action, whose force is small
# (∝ μ²−m²-suppressed spectrum) — so it sits on the COARSE timescale of a 2-level nested
# Omelyan and is evaluated ~n_outer times per trajectory instead of ~3·n_md. Rationals
# survive only in the heatbaths (as in the single-PF scheme).
#
# NOTE: this deliberately DIFFERS from the Rust engine's Hasenbusch structure
# (rhmc_trajectory_eo_2pf_hasenbusch: Clark-Kennedy 2 complex PFs per factor, α=1/4
# rational actions). The single-REAL-PF power-1 form is the Phase-5s DR's "no-CK α=1/2"
# variant — it keeps this engine's action/force = single-exact-solve property at every
# factor and reuses eo_fermion_force/eo_compute_force/eo_heatbath unchanged. Both sample
# the identical target density (the det split is exact); certification is dense-oracle
# (weight identities, FD forces) + Creutz, not cross-engine trajectory matching.


def eo_heatbath_ratio(xi_e, h, ratio_coeffs, eo, fwd, back, L, tol=1e-10, max_iter=8000):
    """Draw the RATIO pseudofermion φ_R = INV_SQRT2·g(M_e)ξ with g = ((x+a)/(x+b))^{1/2}
    applied via `make_eo_ratio_sqrt_coeffs` partial fractions — ONE multishift solve over
    shifts {b} ∪ {e_k} ⊂ (a, b]. Gives S_R = ½‖ξ‖² exactly (to the rational's relerr)."""
    rc = ratio_coeffs
    blocks = hopping_blocks(h, L, dtype=h.dtype)
    with mx.stream(_stream(h.dtype)):
        shifts = np.concatenate([[rc['b']], np.asarray(rc['e'])])
        w = _to_mx(np.concatenate([[rc['B']], np.asarray(rc['w'])]), h.dtype)
        psi = eo_multishift_cg(xi_e, blocks, eo, shifts, tol=tol, max_iter=max_iter)
        return INV_SQRT2 * (rc['A'] * xi_e + mx.sum(w[..., None, None] * psi, axis=-3))


def eo_heatbath_ratio_refined(xi_e, h, ratio_coeffs, eo, L, device, tol=1e-10,
                              inner_tol=3e-4, max_outer=12, max_inner=4000):
    """`eo_heatbath_ratio` with the multishift done by the FP32-inner/FP64-residual
    refined solver (heavy CG on `device`, combination on the CPU stream)."""
    rc = ratio_coeffs
    shifts = np.concatenate([[rc['b']], np.asarray(rc['e'])])
    psi = eo_multishift_cg_refined(xi_e, h, eo, shifts, L, device, tol=tol,
                                   inner_tol=inner_tol, max_outer=max_outer,
                                   max_inner=max_inner)
    with mx.stream(mx.cpu):
        w = _to_mx(np.concatenate([[rc['B']], np.asarray(rc['w'])]), mx.float64)
        return INV_SQRT2 * (rc['A'] * xi_e + mx.sum(w[..., None, None] * psi, axis=-3))


def eo_action_hasenbusch(h, phi_h, phi_r, g, msq, musq, eo, fwd, back, L,
                         tol=1e-10, max_iter=5000):
    """Hasenbusch(K=1) action — every solve exact (power-1), no rational:
    S = Σh²/4g + φ_H†(M_e+μ²)⁻¹φ_H + φ_R†φ_R + (μ²−m²)·φ_R†(M_e+m²)⁻¹φ_R."""
    blocks = hopping_blocks(h, L, dtype=h.dtype)
    with mx.stream(_stream(h.dtype)):
        psi_h = eo_multishift_cg(phi_h, blocks, eo, [musq], tol=tol,
                                 max_iter=max_iter)[..., 0, :, :]
        psi_r = eo_multishift_cg(phi_r, blocks, eo, [msq], tol=tol,
                                 max_iter=max_iter)[..., 0, :, :]
        s_aux = mx.sum(h * h, axis=(-3, -2, -1)) / (4.0 * g)
        s_h = mx.sum(phi_h * psi_h, axis=(-2, -1))
        s_r = mx.sum(phi_r * phi_r, axis=(-2, -1)) + (musq - msq) * mx.sum(
            phi_r * psi_r, axis=(-2, -1))
        return s_aux + s_h + s_r


def eo_action_hasenbusch_refined(h, phi_h, phi_r, g, msq, musq, eo, L, device,
                                 tol=1e-10, inner_tol=3e-4, max_outer=12, max_inner=4000):
    """`eo_action_hasenbusch` with both exact solves routed through the refined solver."""
    kw = dict(tol=tol, inner_tol=inner_tol, max_outer=max_outer, max_inner=max_inner)
    psi_h = eo_multishift_cg_refined(phi_h, h, eo, [musq], L, device, **kw)
    psi_r = eo_multishift_cg_refined(phi_r, h, eo, [msq], L, device, **kw)
    with mx.stream(mx.cpu):
        s_aux = mx.sum(h * h, axis=(-3, -2, -1)) / (4.0 * g)
        s_h = mx.sum(phi_h * psi_h[..., 0, :, :], axis=(-2, -1))
        s_r = mx.sum(phi_r * phi_r, axis=(-2, -1)) + (musq - msq) * mx.sum(
            phi_r * psi_r[..., 0, :, :], axis=(-2, -1))
        return s_aux + s_h + s_r


def eo_integrate_hasenbusch(h, pi, phi_h, phi_r, g, msq, musq, eo, fwd, back, L,
                            eps, n_outer, n_inner, lam=OMELYAN_LAMBDA, tol=1e-10,
                            max_iter=5000, chrono=False):
    """Two-level nested Omelyan 2MN (Phase-5s DR §3): COARSE kicks from the ratio force
    F_R = (μ²−m²)·eo_fermion_force(φ_R at m²) — the hard solve, small magnitude — and
    FINE position-blocks integrating F_fine = −h/2g + eo_fermion_force(φ_H at μ²) —
    cheap solves. `eps` is the coarse step (τ = eps·n_outer); each coarse position
    block runs `n_inner` fine 2MN steps. chrono warm-starts each force's solve from
    its own previous ψ (per-trajectory caches, same softening contract as
    `eo_integrate`)."""
    psi_r_cache = psi_h_cache = None

    def f_coarse(hh):
        nonlocal psi_r_cache
        F, psi_r_cache = eo_fermion_force(hh, phi_r, msq, eo, fwd, back, L, tol=tol,
                                          max_iter=max_iter,
                                          x0=psi_r_cache if chrono else None,
                                          return_psi=True)
        return (musq - msq) * F

    def f_fine(hh):
        nonlocal psi_h_cache
        F, psi_h_cache = eo_compute_force(hh, phi_h, g, musq, eo, fwd, back, L, tol=tol,
                                          max_iter=max_iter,
                                          x0=psi_h_cache if chrono else None,
                                          return_psi=True)
        return F

    def inner(hh, pp, T):
        dt = T / n_inner
        half = 0.5 * dt
        for _ in range(n_inner):
            pp = pp + (lam * dt) * f_fine(hh)
            hh = hh + half * pp
            pp = pp + ((1.0 - 2.0 * lam) * dt) * f_fine(hh)
            hh = hh + half * pp
            pp = pp + (lam * dt) * f_fine(hh)
        return hh, pp

    with mx.stream(_stream(h.dtype)):
        half_eps = 0.5 * eps
        for _ in range(n_outer):
            h, pi = inner(h, pi, lam * eps)
            pi = pi + half_eps * f_coarse(h)
            h, pi = inner(h, pi, (1.0 - 2.0 * lam) * eps)
            pi = pi + half_eps * f_coarse(h)
            h, pi = inner(h, pi, lam * eps)
            mx.eval(h, pi)
    return h, pi


def eo_rhmc_trajectory_hasenbusch_refined(h64, g, msq, musq, hb_coeffs, ratio_coeffs,
                                          eo, fwd, back, L, eps, n_outer, n_inner, rng,
                                          device, tol_md=1e-4, tol_acc=1e-10,
                                          inner_tol=3e-4, max_outer=12, max_inner=4000,
                                          chrono=False):
    """Hasenbusch(K=1) refined trajectory: heavy PF at μ² via the EXISTING heatbath
    machinery (`hb_coeffs` = make_rhmc_coeffs(λ, μ², ·)), ratio PF via the Möbius
    partial fractions (`ratio_coeffs` = make_eo_ratio_sqrt_coeffs(m², μ², λ, ·)),
    2-level nested MD, FP64-exact Metropolis. RNG draw order: ξ_H, ξ_R, π, u.
    Samples the IDENTICAL target density as `eo_rhmc_trajectory_refined` (exact
    determinant split). h64: FP64 (*batch, V, 4, 4). Returns (h_out, ΔH, accept)."""
    Bshape = tuple(h64.shape[:-3])
    V = L ** 4
    Ve = V // 2
    F64 = mx.float64

    xi_h = mx.array(rng.standard_normal(Bshape + (Ve, 8)), dtype=F64)
    phi_h64 = eo_heatbath_refined(xi_h, h64, hb_coeffs, musq, eo, L, device, tol=tol_acc,
                                  inner_tol=inner_tol, max_outer=max_outer,
                                  max_inner=max_inner)
    xi_r = mx.array(rng.standard_normal(Bshape + (Ve, 8)), dtype=F64)
    phi_r64 = eo_heatbath_ratio_refined(xi_r, h64, ratio_coeffs, eo, L, device,
                                        tol=tol_acc, inner_tol=inner_tol,
                                        max_outer=max_outer, max_inner=max_inner)
    pi64 = mx.array(rng.standard_normal(Bshape + (V, 4, 4)), dtype=F64)

    def H(hh, pp, ph, pr):
        S = eo_action_hasenbusch_refined(hh, ph, pr, g, msq, musq, eo, L, device,
                                         tol=tol_acc, inner_tol=inner_tol,
                                         max_outer=max_outer, max_inner=max_inner)
        with mx.stream(mx.cpu):
            return 0.5 * mx.sum(pp * pp, axis=(-3, -2, -1)) + S

    H_old = H(h64, pi64, phi_h64, phi_r64)

    h32 = _cast(h64, mx.float32)
    pi32 = _cast(pi64, mx.float32)
    phi_h32 = _cast(phi_h64, mx.float32)
    phi_r32 = _cast(phi_r64, mx.float32)
    h_new32, pi_new32 = eo_integrate_hasenbusch(h32, pi32, phi_h32, phi_r32, g, msq,
                                                musq, eo, fwd, back, L, eps, n_outer,
                                                n_inner, tol=tol_md, max_iter=max_inner,
                                                chrono=chrono)

    H_new = H(_cast(h_new32, F64), _cast(pi_new32, F64), phi_h64, phi_r64)
    h_new64 = _cast(h_new32, F64)

    u = mx.array(rng.random(Bshape), dtype=F64)
    with mx.stream(mx.cpu):
        dH = H_new - H_old
        accept = u < mx.exp(mx.minimum(-dH, 0.0))
        h_out = mx.where(accept[..., None, None, None], h_new64, h64)
        mx.eval(h_out, dH, accept)
    return h_out, dH, accept


def eo_rhmc_trajectory_refined(h64, g, msq, coeffs, eo, fwd, back, L, eps, n_md, rng, device,
                               tol_md=1e-4, tol_acc=1e-10, inner_tol=3e-4, max_outer=12,
                               max_inner=4000, chrono=False):
    """Mixed-precision eo trajectory with the accept/reject solves ALSO offloaded to
    `device` (FP32 inner + FP64 residual refinement) — FP64-EXACT Metropolis at GPU speed.

    Unlike `eo_rhmc_trajectory_mixed` (which runs the FP64 heatbath + Hamiltonians on the
    CPU stream — fine for torch-CPU but slow on the MLX CPU backend), this routes those
    FP64 solves through the refined solver so the heavy CG lands on Metal/CUDA. RNG draw
    order (ξ, π, u) matches the mixed trajectory exactly, so the two are interchangeable.
    h64: FP64 (*batch, V, 4, 4). Returns (h_out, ΔH, accept)."""
    Bshape = tuple(h64.shape[:-3])
    V = L ** 4
    Ve = V // 2
    F64 = mx.float64

    xi = mx.array(rng.standard_normal(Bshape + (Ve, 8)), dtype=F64)
    phi_e64 = eo_heatbath_refined(xi, h64, coeffs, msq, eo, L, device, tol=tol_acc,
                                  inner_tol=inner_tol, max_outer=max_outer, max_inner=max_inner)
    pi64 = mx.array(rng.standard_normal(Bshape + (V, 4, 4)), dtype=F64)

    def H(hh, pp):
        S = eo_action_refined(hh, phi_e64, g, msq, eo, L, device, tol=tol_acc,
                              inner_tol=inner_tol, max_outer=max_outer, max_inner=max_inner)
        with mx.stream(mx.cpu):
            return 0.5 * mx.sum(pp * pp, axis=(-3, -2, -1)) + S

    H_old = H(h64, pi64)

    # FP32 MD proposal on device (single-pole eo force)
    h32 = _cast(h64, mx.float32)
    pi32 = _cast(pi64, mx.float32)
    phi_e32 = _cast(phi_e64, mx.float32)
    h_new32, pi_new32 = eo_integrate(h32, pi32, phi_e32, g, msq, eo, fwd, back, L,
                                     eps, n_md, tol=tol_md, max_iter=max_inner, chrono=chrono)

    H_new = H(_cast(h_new32, F64), _cast(pi_new32, F64))
    h_new64 = _cast(h_new32, F64)

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
