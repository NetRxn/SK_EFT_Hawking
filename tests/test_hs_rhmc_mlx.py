"""TDD for the MLX port of the batched stencil RHMC engine (hs_rhmc_mlx).

Oracles (same certification pattern that gated the torch engine):
  1. the dense fermion matrix `build_fermion_matrix_torch` (exact, FP64), and
  2. cross-engine agreement with the certified `hs_rhmc_stencil` torch engine.

The MLX engine itself is torch-free (Clifford constants come from
src.core.constants); torch appears here ONLY as the test oracle. All FP64
oracle tests run on MLX's CPU stream (Metal has no float64); the FP32/Metal
path is certified separately (mixed-precision trajectory + Creutz).
"""
import numpy as np
import pytest

torch = pytest.importorskip("torch")
pytest.importorskip("mlx.core")
import mlx.core as mx

from src.vestigial.hs_rhmc_torch import build_fermion_matrix_torch
import src.vestigial.hs_rhmc_stencil as st
import src.vestigial.hs_rhmc_mlx as me

CPU = torch.device("cpu")
F64 = torch.float64


def _accelerator_available():
    """True if a non-CPU MLX accelerator is present — Metal (macOS) OR CUDA (Linux/3090).
    GPU-path tests must gate on this, not on `mx.metal.is_available()` alone, or the CUDA
    production target (mlx[cuda]) gets zero GPU coverage (review finding 3)."""
    if mx.metal.is_available():
        return True
    cuda = getattr(mx, "cuda", None)
    return bool(cuda and cuda.is_available())


@pytest.fixture(autouse=True)
def _cpu_default_device():
    # All oracle tests here are FP64, which Metal cannot run. The engine's own
    # functions pick the CPU stream for f64 internally, but the tests' raw mx
    # slicing/conversion of results would land on the GPU default stream — pin
    # the default device to CPU for this module. The FP32/Metal path is
    # exercised by the mixed-precision trajectory tests + the benchmark script.
    prev = mx.default_device()
    mx.set_default_device(mx.cpu)
    yield
    mx.set_default_device(prev)


def _dense(h, L):
    A = build_fermion_matrix_torch(h, L, device=CPU, dtype=F64)
    return A.cpu().numpy()


def _mx64(a):
    return mx.array(np.asarray(a), dtype=mx.float64)


def _np(a):
    return np.array(a)


# --- core stencil matvecs -------------------------------------------------------------------

def test_hopping_blocks_preserves_numpy_float64_dtype():
    # Review A-cluster: hopping_blocks(numpy_f64, L) with dtype=None must produce FP64
    # blocks, not silently downcast to FP32 (the old `dtype or mx.float32` precision
    # footgun that would break the exact-FP64 contract for numpy-fed configs).
    L, V = 2, 2 ** 4
    h = np.random.default_rng(0).standard_normal((V, 4, 4))    # numpy float64, no dtype arg
    blk = me.hopping_blocks(h, L)
    assert blk.dtype == mx.float64
    # and an explicit f32 request still downcasts
    assert me.hopping_blocks(h, L, dtype=mx.float32).dtype == mx.float32


def test_apply_A_matches_dense_single_config():
    L, V = 2, 2 ** 4
    rng = np.random.default_rng(0)
    h = rng.standard_normal((V, 4, 4))
    psi = rng.standard_normal((V, 8))

    expected = _dense(h, L) @ psi.reshape(-1)          # (8V,)

    fwd, back = me.neighbor_tables(L)
    blocks = me.hopping_blocks(_mx64(h), L)
    got = me.apply_A(_mx64(psi), blocks, fwd, back)    # (V, 8)

    assert np.allclose(_np(got).reshape(-1), expected, atol=1e-10)


def test_apply_A_batched_over_distinct_configs():
    L, V, B = 2, 2 ** 4, 3
    rng = np.random.default_rng(1)
    h = rng.standard_normal((B, V, 4, 4))
    psi = rng.standard_normal((B, V, 8))

    fwd, back = me.neighbor_tables(L)
    blocks = me.hopping_blocks(_mx64(h), L)
    got = _np(me.apply_A(_mx64(psi), blocks, fwd, back))   # (B, V, 8)

    for b in range(B):
        expected = (_dense(h[b], L) @ psi[b].reshape(-1)).reshape(V, 8)
        assert np.allclose(got[b], expected, atol=1e-10)
    assert not np.allclose(got[0], got[1])


def test_apply_AtA_matches_minus_A_squared_with_shift():
    L, V = 2, 2 ** 4
    rng = np.random.default_rng(2)
    h = rng.standard_normal((V, 4, 4))
    psi = rng.standard_normal((V, 8))
    shift = 0.37

    A = _dense(h, L)
    expected = (-A @ A @ psi.reshape(-1)) + shift * psi.reshape(-1)

    fwd, back = me.neighbor_tables(L)
    blocks = me.hopping_blocks(_mx64(h), L)
    got = me.apply_AtA(_mx64(psi), blocks, fwd, back, shift=shift)

    assert np.allclose(_np(got).reshape(-1), expected, atol=1e-10)
    ata = _np(me.apply_AtA(_mx64(psi), blocks, fwd, back)).reshape(-1)
    assert float(psi.reshape(-1) @ ata) >= -1e-10


def test_apply_A_broadcasts_config_over_poles():
    # CG usage: ONE config, K shift-vectors. blocks (B,1,...) broadcast over psi (B,K,...).
    L, V, B, K = 2, 2 ** 4, 2, 5
    rng = np.random.default_rng(3)
    h = rng.standard_normal((B, V, 4, 4))
    psi = rng.standard_normal((B, K, V, 8))

    fwd, back = me.neighbor_tables(L)
    blocks = me.hopping_blocks(_mx64(h), L)
    blocks_k = mx.expand_dims(blocks, 1, stream=mx.cpu)  # (B, 1, V, 4, 8, 8); f64 → CPU stream
    got = _np(me.apply_A(_mx64(psi), blocks_k, fwd, back))   # (B, K, V, 8)

    for b in range(B):
        A = _dense(h[b], L)
        for k in range(K):
            expected = (A @ psi[b, k].reshape(-1)).reshape(V, 8)
            assert np.allclose(got[b, k], expected, atol=1e-10)


def test_cross_engine_apply_A_matches_torch_stencil():
    # Cross-engine oracle: MLX matvec ≡ certified torch stencil matvec, batched.
    L, V, B = 3, 3 ** 4, 2
    rng = np.random.default_rng(6)
    h = rng.standard_normal((B, V, 4, 4))
    psi = rng.standard_normal((B, V, 8))

    fwd_t, back_t = st.neighbor_tables(L, CPU)
    blocks_t = st.hopping_blocks(torch.tensor(h), L, device=CPU, dtype=F64)
    ref = st.apply_A(torch.tensor(psi), blocks_t, fwd_t, back_t).numpy()

    fwd, back = me.neighbor_tables(L)
    blocks = me.hopping_blocks(_mx64(h), L)
    got = _np(me.apply_A(_mx64(psi), blocks, fwd, back))

    assert np.allclose(got, ref, atol=1e-12)


# --- multishift CG --------------------------------------------------------------------------

def test_multishift_cg_matches_dense_solve_single_config():
    L, V = 2, 2 ** 4
    rng = np.random.default_rng(4)
    h = rng.standard_normal((V, 4, 4))
    b = rng.standard_normal((V, 8))
    shifts = np.array([0.5, 1.0, 2.0, 5.0])

    A = _dense(h, L)
    AtA = -A @ A
    eye = np.eye(8 * V)
    expected = np.stack([np.linalg.solve(AtA + s * eye, b.reshape(-1)) for s in shifts])

    fwd, back = me.neighbor_tables(L)
    blocks = me.hopping_blocks(_mx64(h), L)
    x = me.multishift_cg(_mx64(b), blocks, fwd, back, _mx64(shifts), tol=1e-10, max_iter=4000)

    for k in range(len(shifts)):
        assert np.allclose(_np(x[k]).reshape(-1), expected[k], atol=1e-6)


def test_multishift_cg_batched_over_configs():
    L, V, B = 2, 2 ** 4, 3
    rng = np.random.default_rng(5)
    h = rng.standard_normal((B, V, 4, 4))
    b = rng.standard_normal((B, V, 8))
    shifts = np.array([0.5, 2.0])

    fwd, back = me.neighbor_tables(L)
    blocks = me.hopping_blocks(_mx64(h), L)
    x = me.multishift_cg(_mx64(b), blocks, fwd, back, _mx64(shifts), tol=1e-10, max_iter=4000)

    for bi in range(B):
        A = _dense(h[bi], L)
        AtA = -A @ A
        eye = np.eye(8 * V)
        for k, s in enumerate(shifts):
            expected = np.linalg.solve(AtA + s * eye, b[bi].reshape(-1))
            assert np.allclose(_np(x[bi, k]).reshape(-1), expected, atol=1e-6)


# --- even-odd reduction ---------------------------------------------------------------------

def test_eo_tables_parity_partition():
    L, V = 4, 4 ** 4
    eo = me.eo_tables(L)
    assert eo['even_idx'].shape == (V // 2,) and eo['odd_idx'].shape == (V // 2,)
    allidx = np.sort(np.concatenate([_np(eo['even_idx']), _np(eo['odd_idx'])]))
    assert np.array_equal(allidx, np.arange(V))
    fwd, back = me.neighbor_tables(L)
    parity = np.zeros(V, dtype=np.int64)
    parity[_np(eo['odd_idx'])] = 1
    fwd_np, back_np = _np(fwd), _np(back)
    even_np = _np(eo['even_idx'])
    for mu in range(4):
        assert (parity[fwd_np[even_np, mu]] == 1).all()
        assert (parity[back_np[even_np, mu]] == 1).all()


def test_eo_tables_odd_L_rejected():
    with pytest.raises(ValueError):
        me.eo_tables(3)


def test_apply_Me_halfsize_matches_full_AtA_on_even():
    L, V = 4, 4 ** 4
    rng = np.random.default_rng(30)
    h = rng.standard_normal((V, 4, 4))
    fwd, back = me.neighbor_tables(L)
    blocks = me.hopping_blocks(_mx64(h), L)
    eo = me.eo_tables(L)
    Ve = V // 2
    psi_e = rng.standard_normal((Ve, 8))

    # oracle: scatter even → full, apply_AtA, gather even
    psi_full = np.zeros((V, 8))
    psi_full[_np(eo['even_idx'])] = psi_e
    ref = _np(me.apply_AtA(_mx64(psi_full), blocks, fwd, back))[_np(eo['even_idx'])]

    got = me.apply_Me(_mx64(psi_e), blocks, eo)
    assert got.shape == (Ve, 8)
    assert np.allclose(_np(got), ref, atol=1e-10)

    got_s = _np(me.apply_Me(_mx64(psi_e), blocks, eo, shift=0.37))
    assert np.allclose(got_s, ref + 0.37 * psi_e, atol=1e-10)


def test_apply_Me_batched_over_configs():
    L, V, B = 4, 4 ** 4, 3
    rng = np.random.default_rng(31)
    h = rng.standard_normal((B, V, 4, 4))
    fwd, back = me.neighbor_tables(L)
    blocks = me.hopping_blocks(_mx64(h), L)
    eo = me.eo_tables(L)
    Ve = V // 2
    psi_e = rng.standard_normal((B, Ve, 8))

    got = _np(me.apply_Me(_mx64(psi_e), blocks, eo))
    even_np = _np(eo['even_idx'])
    for b in range(B):
        psi_full = np.zeros((V, 8))
        psi_full[even_np] = psi_e[b]
        blocks_b = me.hopping_blocks(_mx64(h[b]), L)
        ref = _np(me.apply_AtA(_mx64(psi_full), blocks_b, fwd, back))[even_np]
        assert np.allclose(got[b], ref, atol=1e-10)


def test_lambda_max_matches_dense():
    L, V = 2, 2 ** 4
    rng = np.random.default_rng(9)
    h = rng.standard_normal((V, 4, 4))
    A = _dense(h, L)
    lam_true = np.linalg.eigvalsh(-A @ A).max()

    fwd, back = me.neighbor_tables(L)
    blocks = me.hopping_blocks(_mx64(h), L)
    lam = float(me.estimate_lambda_max(blocks, fwd, back, V, n_iter=400, seed=0))

    assert abs(lam - lam_true) / lam_true < 1e-2


# --- dynamics: action, force, integrator ----------------------------------------------------

def test_action_matches_torch_stencil():
    # Cross-engine value agreement on identical inputs (deterministic oracle).
    L, V, g = 2, 2 ** 4, 1.5
    rng = np.random.default_rng(40)
    h = rng.standard_normal((V, 4, 4))
    phi = rng.standard_normal((V, 8))
    alphas = np.array([0.5, 0.3, 0.2])
    betas = np.array([0.3, 1.0, 3.0])
    a0 = 0.4

    fwd_t, back_t = st.neighbor_tables(L, CPU)
    ref = float(st.action(torch.tensor(h), torch.tensor(phi), g, a0,
                          torch.tensor(alphas), torch.tensor(betas),
                          fwd_t, back_t, L, tol=1e-12, max_iter=5000))

    fwd, back = me.neighbor_tables(L)
    got = float(me.action(_mx64(h), _mx64(phi), g, a0, _mx64(alphas), _mx64(betas),
                          fwd, back, L, tol=1e-12, max_iter=5000))
    assert abs(got - ref) < 1e-8 * max(1.0, abs(ref))


def test_force_equals_negative_action_gradient():
    # The property that makes HMC conserve H: F = −∂S/∂h (reference-independent FD).
    L, V, g = 2, 2 ** 4, 1.5
    rng = np.random.default_rng(7)
    h = rng.standard_normal((V, 4, 4))
    phi = rng.standard_normal((V, 8))
    alphas = np.array([0.5, 0.3, 0.2])
    betas = np.array([0.3, 1.0, 3.0])
    a0 = 0.4
    fwd, back = me.neighbor_tables(L)
    phim = _mx64(phi)
    al, be = _mx64(alphas), _mx64(betas)

    F = _np(me.compute_force(_mx64(h), phim, g, al, be, fwd, back, L,
                             tol=1e-12, max_iter=5000))

    def action(hh):
        return float(me.action(_mx64(hh), phim, g, a0, al, be, fwd, back, L,
                               tol=1e-12, max_iter=5000))

    eps = 1e-5
    for (x, mu, a) in [(0, 0, 0), (3, 2, 1), (7, 1, 3), (12, 3, 2)]:
        hp = h.copy(); hp[x, mu, a] += eps
        hm = h.copy(); hm[x, mu, a] -= eps
        fd = -(action(hp) - action(hm)) / (2 * eps)
        assert abs(F[x, mu, a] - fd) <= 1e-4 * max(1.0, abs(fd)), (x, mu, a, F[x, mu, a], fd)


def test_omelyan_integrator_is_reversible():
    # Reversibility (⟹ detailed balance): forward, flip momenta, forward → start.
    L, V, g = 2, 2 ** 4, 1.5
    rng = np.random.default_rng(8)
    h0 = rng.standard_normal((V, 4, 4))
    pi0 = rng.standard_normal((V, 4, 4))
    phi = _mx64(rng.standard_normal((V, 8)))
    al = _mx64([0.5, 0.3, 0.2])
    be = _mx64([0.3, 1.0, 3.0])
    fwd, back = me.neighbor_tables(L)
    kw = dict(fwd=fwd, back=back, L=L, eps=0.1, n_steps=5, tol=1e-12, max_iter=5000)

    h1, pi1 = me.integrate(_mx64(h0), _mx64(pi0), phi, g, al, be, **kw)
    assert not np.allclose(_np(h1), h0)                     # it actually moved
    h2, pi2 = me.integrate(h1, -pi1, phi, g, al, be, **kw)

    assert np.allclose(_np(h2), h0, atol=1e-9)
    assert np.allclose(_np(pi2), -pi0, atol=1e-9)


def test_eo_force_equals_negative_action_gradient():
    # F = −∂S_eo/∂h, finite-differenced against the reference-independent eo_action.
    L, V, g = 4, 4 ** 4, 1.5
    msq = 0.04
    rng = np.random.default_rng(34)
    h = rng.standard_normal((V, 4, 4))
    eo = me.eo_tables(L)
    Ve = V // 2
    phi_e = _mx64(rng.standard_normal((Ve, 8)))
    fwd, back = me.neighbor_tables(L)

    F = _np(me.eo_compute_force(_mx64(h), phi_e, g, msq, eo, fwd, back, L,
                                tol=1e-12, max_iter=8000))

    def action(hh):
        return float(me.eo_action(_mx64(hh), phi_e, g, msq, eo, fwd, back, L,
                                  tol=1e-12, max_iter=8000))

    eps = 1e-5
    for (x, mu, a) in [(0, 0, 0), (5, 2, 1), (17, 1, 3), (40, 3, 2)]:
        hp = h.copy(); hp[x, mu, a] += eps
        hm = h.copy(); hm[x, mu, a] -= eps
        fd = -(action(hp) - action(hm)) / (2 * eps)
        assert abs(F[x, mu, a] - fd) <= 1e-4 * max(1.0, abs(fd)), (x, mu, a, F[x, mu, a], fd)


def test_eo_integrator_is_reversible():
    L, V, g = 4, 4 ** 4, 1.5
    msq = 0.04
    rng = np.random.default_rng(35)
    eo = me.eo_tables(L)
    Ve = V // 2
    h0 = rng.standard_normal((V, 4, 4))
    pi0 = rng.standard_normal((V, 4, 4))
    phi_e = _mx64(rng.standard_normal((Ve, 8)))
    fwd, back = me.neighbor_tables(L)
    kw = dict(phi_e=phi_e, g=g, msq=msq, eo=eo, fwd=fwd, back=back, L=L,
              eps=0.08, n_steps=5, tol=1e-12, max_iter=8000)

    h1, pi1 = me.eo_integrate(_mx64(h0), _mx64(pi0), **kw)
    assert not np.allclose(_np(h1), h0)
    h2, pi2 = me.eo_integrate(h1, -pi1, **kw)
    assert np.allclose(_np(h2), h0, atol=1e-9)
    assert np.allclose(_np(pi2), -pi0, atol=1e-9)


# --- refined (FP32-inner / FP64-residual) solver — the trajectory-level speed brick ---------

def test_eo_multishift_cg_refined_matches_fp64_with_fp32_inner():
    # Core certification: FP32 inner solves + FP64 residual refinement reproduce the
    # pure-FP64 eo multishift solution to ~1e-8, including the ill-conditioned small
    # shift (the one that drives the cost). device='cpu' exercises the precision mix
    # without needing Metal; the Metal path is the same code on the gpu default device.
    L, V = 4, 4 ** 4
    rng = np.random.default_rng(21)
    h = rng.standard_normal((V, 4, 4))
    b_e = rng.standard_normal((V // 2, 8))
    shifts = np.array([0.01, 0.05, 0.3, 1.0, 4.0, 20.0])     # small shift = ill-conditioned
    eo = me.eo_tables(L)
    fwd, back = me.neighbor_tables(L)
    blocks = me.hopping_blocks(_mx64(h), L)

    x_fp64 = me.eo_multishift_cg(_mx64(b_e), blocks, eo, _mx64(shifts), tol=1e-12, max_iter=8000)
    x_ref = me.eo_multishift_cg_refined(_mx64(b_e), _mx64(h), eo, _mx64(shifts), L, mx.cpu,
                                        tol=1e-10, inner_tol=3e-4, max_outer=20, max_inner=8000)
    assert x_ref.dtype == mx.float64 and x_ref.shape == x_fp64.shape
    assert np.allclose(_np(x_ref), _np(x_fp64), atol=1e-8, rtol=1e-6), \
        float(np.abs(_np(x_ref) - _np(x_fp64)).max())


def test_eo_multishift_cg_refined_raises_on_nonconvergence():
    # Robustness (review finding 1): an exhausted max_outer must NOT silently return an
    # under-converged x that then feeds the FP64-exact Metropolis / heatbath. With too few
    # outer passes to reach a tight tol, the refined solve must raise (strict=True default).
    L, V = 4, 4 ** 4
    rng = np.random.default_rng(21)
    h = rng.standard_normal((V, 4, 4))
    b_e = rng.standard_normal((V // 2, 8))
    shifts = np.array([0.001])                    # small shift = ill-conditioned
    eo = me.eo_tables(L)

    with pytest.raises(RuntimeError, match="did not reach tol"):
        me.eo_multishift_cg_refined(_mx64(b_e), _mx64(h), eo, _mx64(shifts), L, mx.cpu,
                                    tol=1e-12, inner_tol=3e-4, max_outer=1, max_inner=4000)

    # strict=False returns best-effort without raising (documented escape hatch)
    x = me.eo_multishift_cg_refined(_mx64(b_e), _mx64(h), eo, _mx64(shifts), L, mx.cpu,
                                    tol=1e-12, inner_tol=3e-4, max_outer=1, max_inner=4000,
                                    strict=False)
    assert x.dtype == mx.float64 and x.shape == (1, V // 2, 8)


def test_cg_loop_narrows_active_shift_set_as_shifts_converge():
    # Perf-audit 2026-07-13: the K=44 heatbath iteration cost 44x the K=1 iteration —
    # converged (large, log-spaced) shifts kept full-bandwidth masked no-op updates until
    # the m² shift finished thousands of iterations later. _cg_loop must NARROW: drop
    # converged shifts from the working set at host checkpoints, so the matvec batch
    # width shrinks toward the slowest shift. Narrowing is value-preserving (each
    # (config, shift) system's arithmetic is independent; the in-graph mask already
    # freezes converged systems), so per-shift solutions must still meet tol exactly.
    L, V = 2, 2 ** 4
    rng = np.random.default_rng(31)
    h = rng.standard_normal((V, 4, 4)) * 4.0
    b_e = _mx64(rng.standard_normal((V // 2, 8)))
    shifts = np.array([1e-3, 1e-1, 10.0, 1e3])    # spread: big shifts converge 100x sooner
    eo = me.eo_tables(L)
    blocks_k = mx.expand_dims(me.hopping_blocks(_mx64(h), L), 0)
    blocks_eo = me._split_eo(blocks_k, eo)

    widths = []
    def recording_matvec(p):
        widths.append(p.shape[-3])
        return me.apply_Me_split(p, blocks_eo, eo)

    K = len(shifts)
    sigma, _ = me._as_shift_tensor(_mx64(shifts), 0, (), mx.float64)
    bk = mx.broadcast_to(mx.expand_dims(b_e, 0), (K, V // 2, 8))
    x = me._cg_loop(bk, recording_matvec, sigma, 1e-8, 20000)
    mx.eval(x)

    # behavior: the working set actually narrowed, monotonically, down to the slow tail
    assert widths[0] == K
    assert widths[-1] < K, "converged shifts were never dropped from the working set"
    assert all(a >= b for a, b in zip(widths, widths[1:])), "active set must only shrink"
    assert min(widths) <= 2, f"tail should run with the slowest shift(s) only, saw {min(widths)}"

    # correctness: full-size output, every shift solved to tol (relative to ||b||)
    assert x.shape == (K, V // 2, 8)
    bnorm = float(mx.sqrt(mx.sum(b_e * b_e)))
    for k in range(K):
        xk = x[k]
        r = b_e - (me.apply_Me_split(mx.expand_dims(xk, 0), blocks_eo, eo)[0]
                   + shifts[k] * xk)
        assert float(mx.sqrt(mx.sum(r * r))) <= 1e-7 * bnorm


def test_eo_multishift_cg_refined_narrows_outer_passes():
    # Outer-level narrowing: once a shift's FP64 residual is ≤ tol, later refinement
    # passes must NOT re-solve its correction (each such solve costs O(inner-CG) on a
    # negligible source — measured as part of the 74%-of-trajectory heatbath). The
    # production mechanism: the ~m² shift's inner solve is max_inner-capped, so its
    # per-pass reduction is worse than the easy shifts' (which achieve the full
    # inner_tol every pass and retire early) — later passes must carry ONLY the hard
    # shift, and the final result must still satisfy the FP64 tol for EVERY shift.
    L, V = 4, 4 ** 4
    rng = np.random.default_rng(33)
    h = rng.standard_normal((V, 4, 4))
    b_e = _mx64(rng.standard_normal((V // 2, 8)))
    shifts = np.array([3e-4, 50.0])       # κ contrast ~2e5 : 1; 50.0 retires passes early
    eo = me.eo_tables(L)

    inner_widths = []
    orig_cg_loop = me._cg_loop
    def recording_cg_loop(bk, matvec, sigma, tol, max_iter, **kw):
        inner_widths.append(bk.shape[-3])
        return orig_cg_loop(bk, matvec, sigma, tol, max_iter, **kw)

    me._cg_loop = recording_cg_loop
    try:
        # max_inner=150 caps the hard shift far below its ~2000-iteration need, forcing
        # multiple partial-reduction passes for it — exactly the production asymmetry.
        x = me.eo_multishift_cg_refined(b_e, _mx64(h), eo, _mx64(shifts), L, mx.cpu,
                                        tol=1e-6, inner_tol=3e-4, max_outer=60,
                                        max_inner=150)
    finally:
        me._cg_loop = orig_cg_loop
    mx.eval(x)

    assert inner_widths[0] == 2
    assert inner_widths[-1] == 1, f"retired shift still in late passes: {inner_widths}"

    # every shift meets the FP64 tol (the easy one must not have been corrupted)
    blocks_eo = me._split_eo(mx.expand_dims(me.hopping_blocks(_mx64(h), L), 0), eo)
    bnorm = float(mx.sqrt(mx.sum(b_e * b_e)))
    for k, s in enumerate(shifts):
        xk = x[k]
        r = b_e - (me.apply_Me_split(mx.expand_dims(xk, 0), blocks_eo, eo)[0] + s * xk)
        assert float(mx.sqrt(mx.sum(r * r))) <= 1e-6 * bnorm


def test_refined_path_gpu_default_seam_and_gross_bias():
    # Two review gaps in one FAST (non-slow) test:
    #  (1) structural — the autouse fixture pins the default device to CPU, masking any
    #      f64-on-GPU-stream seam in the refined path; here we run the refined heatbath /
    #      action / trajectory under the GPU (Metal/CUDA) DEFAULT device, so a missed
    #      `with mx.stream(mx.cpu)` guard crashes IN CI, not only in production.
    #  (2) finding 4 — the fast mechanics tests pass even with a biased ΔH; a short Creutz
    #      chain here catches a gross ΔH / normalization regression (e.g. a factor-2 bug)
    #      without the cost of the full @slow gate.
    if not _accelerator_available():
        pytest.skip("no GPU accelerator")
    mx.set_default_device(mx.gpu)                 # fixture restores afterward
    L, V = 2, 2 ** 4
    g, msq = 1.5, 0.04
    fwd, back = me.neighbor_tables(L)
    eo = me.eo_tables(L)
    rng0 = np.random.default_rng(0)
    h = _mx64(1.3 * rng0.standard_normal((V, 4, 4)))
    lam = float(me.estimate_lambda_max(me.hopping_blocks(h, L), fwd, back, V))
    coeffs = me.make_rhmc_coeffs(1.3 * lam, msq, n_poles=12)

    # exercise each refined-path f64 seam once under the GPU default device
    xi = _mx64(rng0.standard_normal((V // 2, 8)))
    phi = me.eo_heatbath_refined(xi, h, coeffs, msq, eo, L, mx.gpu)
    S = me.eo_action_refined(h, phi, g, msq, eo, L, mx.gpu)
    mx.eval(phi, S)
    assert np.isfinite(float(S))                  # read the eval'd f64 scalar (no new GPU op)

    # short Creutz chain (gross-bias catcher; loose tol, few trajectories). The rigorous
    # unbiasedness gate is the @slow test_creutz_identity_eo_refined_chain_unbiased.
    rng = np.random.default_rng(5)
    dHs, nacc, n = [], 0, 30
    for t in range(n):
        h, dH, acc = me.eo_rhmc_trajectory_refined(h, g, msq, coeffs, eo, fwd, back, L,
                                                   0.05, 6, rng, mx.gpu, tol_md=1e-4,
                                                   inner_tol=3e-4, max_outer=20)
        mx.eval(h, dH, acc)
        assert h.dtype == mx.float64 and np.isfinite(float(dH))
        if t >= n // 4:
            dHs.append(float(dH)); nacc += int(bool(acc))
    creutz = float(np.mean(np.exp(-np.array(dHs))))
    assert nacc / (n - n // 4) > 0.4 and abs(creutz - 1.0) < 0.2, (creutz, nacc / (n - n // 4))


def test_all_public_entry_points_no_f64_seam_under_gpu_default():
    """Every public f64 entry point runs under the GPU DEFAULT device without raising
    'float64 is not supported on the GPU'. The autouse fixture pins CPU (masking f64 seams);
    this flips the default to the accelerator — the real production placement — so an
    unguarded f64 op (function body OR result read) is caught in CI, not only in a multi-day
    run. Generalizes test_refined_path_gpu_default_seam_and_gross_bias (refined path only) to
    the full pure-f64 surface: matvecs, CG, action/force/integrator, heatbath, the mixed
    trajectory, and measurement."""
    if not _accelerator_available():
        pytest.skip("no GPU accelerator")
    mx.set_default_device(mx.gpu)                     # fixture restores afterward
    L, V, Ve = 2, 2 ** 4, (2 ** 4) // 2
    g, msq = 1.5, 0.04
    rng = np.random.default_rng(0)
    fwd, back = me.neighbor_tables(L)
    eo = me.eo_tables(L)
    h = _mx64(1.3 * rng.standard_normal((V, 4, 4)))
    blocks = me.hopping_blocks(h, L)
    phi, xi = _mx64(rng.standard_normal((V, 8))), _mx64(rng.standard_normal((V, 8)))
    phi_e, xi_e = _mx64(rng.standard_normal((Ve, 8))), _mx64(rng.standard_normal((Ve, 8)))
    pi = _mx64(rng.standard_normal((V, 4, 4)))
    lam = float(me.estimate_lambda_max(blocks, fwd, back, V))
    coeffs = me.make_rhmc_coeffs(1.3 * lam, msq, 12)
    a0, alphas, betas = coeffs['a0'], coeffs['alphas'], coeffs['betas'] + msq

    entry_points = {
        'hopping_blocks': lambda: me.hopping_blocks(h, L),
        'apply_A': lambda: me.apply_A(phi, blocks, fwd, back),
        'apply_AtA': lambda: me.apply_AtA(phi, blocks, fwd, back),
        'apply_Me': lambda: me.apply_Me(phi_e, blocks, eo),
        'estimate_lambda_max': lambda: me.estimate_lambda_max(blocks, fwd, back, V),
        'multishift_cg': lambda: me.multishift_cg(phi, blocks, fwd, back, betas),
        'eo_multishift_cg': lambda: me.eo_multishift_cg(phi_e, blocks, eo, betas),
        'action': lambda: me.action(h, phi, g, a0, alphas, betas, fwd, back, L),
        'compute_force': lambda: me.compute_force(h, phi, g, alphas, betas, fwd, back, L),
        'integrate': lambda: me.integrate(h, pi, phi, g, alphas, betas, fwd, back, L, 0.02, 2),
        'heatbath': lambda: me.heatbath(xi, blocks, fwd, back, coeffs, msq),
        'eo_action': lambda: me.eo_action(h, phi_e, g, msq, eo, fwd, back, L),
        'eo_compute_force': lambda: me.eo_compute_force(h, phi_e, g, msq, eo, fwd, back, L),
        'eo_integrate': lambda: me.eo_integrate(h, pi, phi_e, g, msq, eo, fwd, back, L, 0.02, 2),
        'eo_heatbath': lambda: me.eo_heatbath(xi_e, h, coeffs, msq, eo, fwd, back, L),
        'eo_rhmc_trajectory_mixed': lambda: me.eo_rhmc_trajectory_mixed(
            h, g, msq, coeffs, eo, fwd, back, L, 0.03, 2, np.random.default_rng(1)),
        'measure_observables': lambda: me.measure_observables(h, L),
    }
    for name, fn in entry_points.items():
        try:
            out = fn()
            mx.eval(*out) if isinstance(out, tuple) else mx.eval(out)
        except ValueError as e:                       # the f64-on-GPU seam signature
            if "float64" in str(e):
                pytest.fail(f"f64-on-GPU seam in {name}(): {e}")
            raise
        arr = out[0] if isinstance(out, tuple) else out
        assert np.all(np.isfinite(_np(arr))), name    # result read under GPU default too


def test_eo_action_refined_matches_fp64_action():
    # Integration: eo action via the refined solver matches pure-FP64 to ~1e-7 ⟹ the
    # accept/reject ΔH is FP64-exact ⟹ no bias.
    L, V, g = 4, 4 ** 4, 1.5
    msq = 0.01
    rng = np.random.default_rng(22)
    h = _mx64(rng.standard_normal((V, 4, 4)))
    phi_e = _mx64(rng.standard_normal((V // 2, 8)))
    eo = me.eo_tables(L)
    fwd, back = me.neighbor_tables(L)

    S_fp64 = float(me.eo_action(h, phi_e, g, msq, eo, fwd, back, L, tol=1e-12, max_iter=8000))
    S_ref = float(me.eo_action_refined(h, phi_e, g, msq, eo, L, mx.cpu,
                                       tol=1e-10, inner_tol=3e-4, max_outer=20, max_inner=8000))
    assert abs(S_ref - S_fp64) < 1e-6 * max(1.0, abs(S_fp64)), (S_ref, S_fp64)


def test_eo_heatbath_refined_consistency():
    # The refined heatbath must still sample S_PF(heatbath(ξ)) = ½‖ξ‖² (one-Majorana),
    # with the heavy r_{-1/2} multishift done FP32-inner on device.
    L, V = 4, 4 ** 4
    msq = 0.04
    rng = np.random.default_rng(33)
    h = _mx64(rng.standard_normal((V, 4, 4)))
    eo = me.eo_tables(L)
    fwd, back = me.neighbor_tables(L)
    blocks = me.hopping_blocks(h, L)
    lam = float(me.estimate_lambda_max(blocks, fwd, back, V, n_iter=300, seed=0))
    coeffs = me.make_rhmc_coeffs(1.3 * lam, msq, n_poles=18)

    xi = _mx64(rng.standard_normal((V // 2, 8)))
    phi = me.eo_heatbath_refined(xi, h, coeffs, msq, eo, L, mx.cpu, inner_tol=3e-4, max_outer=20)
    psi = me.eo_multishift_cg(phi, blocks, eo, [msq], tol=1e-12, max_iter=8000)[..., 0, :, :]
    s_pf = float(mx.sum(phi * psi))
    half_xi_norm = 0.5 * float(mx.sum(xi * xi))
    assert abs(s_pf - half_xi_norm) / half_xi_norm < 0.03


def test_eo_refined_trajectory_mechanics():
    # Mechanics of the refined trajectory (FP32-inner accept/reject on device + FP32 MD):
    # runs, returns FP64 configs, finite ΔH, boolean accept, exact Metropolis (rejected
    # replicas retain the previous config bit-for-bit). Unbiasedness = the slow Creutz test.
    L, V, B = 4, 4 ** 4, 2
    g, msq = 1.5, 0.04
    rng0 = np.random.default_rng(23)
    h = _mx64(rng0.standard_normal((B, V, 4, 4)))
    fwd, back = me.neighbor_tables(L)
    eo = me.eo_tables(L)
    with mx.stream(mx.cpu):
        h00 = h[0]
    lam = float(me.estimate_lambda_max(me.hopping_blocks(h00, L), fwd, back, V, n_iter=150, seed=0))
    coeffs = me.make_rhmc_coeffs(1.3 * lam, msq, n_poles=12)
    rng = np.random.default_rng(7)

    for _ in range(3):
        h_prev = _np(h)
        h, dH, acc = me.eo_rhmc_trajectory_refined(h, g, msq, coeffs, eo, fwd, back, L,
                                                   0.03, 4, rng, mx.cpu, inner_tol=3e-4, max_outer=20)
        assert h.dtype == mx.float64 and h.shape == (B, V, 4, 4)
        assert dH.shape == (B,) and bool(mx.all(mx.isfinite(dH)))
        assert acc.dtype == mx.bool_ and acc.shape == (B,)
        h_np = _np(h)
        for b in range(B):
            if not bool(acc[b]):
                assert np.array_equal(h_np[b], h_prev[b])


@pytest.mark.skipif(not pytest.importorskip("mlx.core").metal.is_available(),
                    reason="fused hop kernel is Metal-only (CUDA uses the einsum path)")
def test_metal_hop_matches_einsum_hop():
    # Wave B: the fused mx.fast.metal_kernel eo-hop must reproduce the einsum _hop
    # bit-for-bit-ish (fp32 reassociation tolerance). The K=1 CG iteration is ~90%
    # kernel-dispatch overhead (~35 launches; mx.compile measured a 4% no-op), so the
    # hop's ~16 launches collapse to 1. Exploits CG[a] = J₁Γᵃ being SIGNED
    # PERMUTATIONS: per site the block action is 4 shuffle-and-FMA terms, no matmul.
    L = 4
    V, Ve = L ** 4, L ** 4 // 2
    rng = np.random.default_rng(63)
    eo = me.eo_tables(L)
    prev = mx.default_device()
    mx.set_default_device(mx.gpu)
    try:
        for (B, K) in ((2, 3), (1, 1), (4, 1)):
            h32 = mx.array(rng.standard_normal((B, V, 4, 4)), dtype=mx.float32)
            psi = mx.array(rng.standard_normal((B, K, Ve, 8)), dtype=mx.float32)
            blocks_k = mx.expand_dims(me.hopping_blocks(h32, L), 1)
            be, bo = me._split_eo(blocks_k, eo)
            h_e = mx.take(h32, eo['even_idx'], axis=-3)
            h_o = mx.take(h32, eo['odd_idx'], axis=-3)

            # even→odd hop (D_oe ψ_e): out-parity = odd, in-parity = even
            ref = me._hop(psi, bo, be, eo['o2e_fwd'], eo['o2e_back'])
            got = me._hop_metal(psi, h_o, h_e, eo['o2e_fwd'], eo['o2e_back'])
            mx.eval(ref, got)
            scale = float(mx.max(mx.abs(ref))) or 1.0
            assert got.shape == ref.shape
            assert float(mx.max(mx.abs(got - ref))) < 1e-4 * scale, (B, K)

            # odd→even hop as well (the second half of M_e)
            ref2 = me._hop(psi, be, bo, eo['e2o_fwd'], eo['e2o_back'])
            got2 = me._hop_metal(psi, h_e, h_o, eo['e2o_fwd'], eo['e2o_back'])
            mx.eval(ref2, got2)
            assert float(mx.max(mx.abs(got2 - ref2))) < 1e-4 * scale, (B, K)
    finally:
        mx.set_default_device(prev)


def test_eo_ratio_sqrt_coeffs_approximate_ratio_sqrt():
    # Hasenbusch (Wave C) brick 1: partial fractions for the RATIO heatbath function
    # g(x) = ((x+a)/(x+b))^{1/2} (a=m², b=μ²), via t·r_{-1/2}(t) with t=(x+a)/(x+b)
    # Möbius-substituted back to x — the Phase-5s DR §4-5 variable transform. The
    # conditioning is κ_t = b/a (NOT λmax/m²), so 24 poles reach the production
    # 1e-3 gate where the direct r_{-1/2} needs 44 at a 1300× worse κ. (The
    # in-house Zolotarev generator converges ~3× slower than optimal-Zolotarev
    # theory — measured 12→3.4e-2, 24→3.3e-4, monotone ×0.22/4-poles — which the
    # auto-bump gate absorbs, as it does for the direct heatbath.) Shifts must
    # land in (a, b) (positive, CG-safe).
    a, b, lam = 0.05 ** 2, 3.3, 1.25 * 4300.0          # the m=0.05 production corner
    C = me.make_eo_ratio_sqrt_coeffs(a, b, lam, n_poles=24)
    assert np.all((C['e'] > a) & (C['e'] < b))
    x = np.concatenate([[0.0], np.exp(np.linspace(np.log(1e-6), np.log(lam), 4000))])
    g = np.sqrt((x + a) / (x + b))
    r = (C['A'] + C['B'] / (x + b)
         + np.sum(C['w'][:, None] / (x[None, :] + C['e'][:, None]), axis=0))
    relerr = np.max(np.abs(r / g - 1.0))
    assert relerr < 1e-3, relerr
    # and the quality improves with poles (monotone convergence, same gate logic as
    # the direct heatbath's zolotarev_max_relerr)
    C12 = me.make_eo_ratio_sqrt_coeffs(a, b, lam, n_poles=12)
    r12 = (C12['A'] + C12['B'] / (x + b)
           + np.sum(C12['w'][:, None] / (x[None, :] + C12['e'][:, None]), axis=0))
    assert np.max(np.abs(r12 / g - 1.0)) > relerr


def test_eo_ratio_sqrt_max_relerr_gate_util():
    # The unsigned max-relerr gate for the RATIO heatbath rational — same role as
    # zolotarev_max_relerr for the direct heatbath (the S_PF consistency ratio is a
    # signed average and under-reports; the gate must use the unsigned max).
    a, b, lam = 0.05 ** 2, 3.3, 1.25 * 4300.0
    e24 = me.eo_ratio_sqrt_max_relerr(me.make_eo_ratio_sqrt_coeffs(a, b, lam, 24), lam)
    e12 = me.eo_ratio_sqrt_max_relerr(me.make_eo_ratio_sqrt_coeffs(a, b, lam, 12), lam)
    assert e24 < 1e-3 < e12                      # monotone, and 24 poles meet the gate


def test_eo_hasenbusch_ratio_heatbath_weight_dense_oracle():
    # Operator-level certification at L=2 against the dense eo operator: with
    # φ = INV_SQRT2·g(M_e)ξ applied via the partial fractions (dense solves), the
    # ratio action S₂ = φ†(M_e+b)(M_e+a)⁻¹φ must equal ½‖ξ‖² — the exact-weight
    # sampling identity (the analogue of the S_PF=½‖ξ‖² heatbath consistency gate).
    L, V = 2, 2 ** 4
    rng = np.random.default_rng(51)
    h = rng.standard_normal((V, 4, 4))
    eo = me.eo_tables(L)
    A = _dense(h, L)
    AtA = -A @ A
    ev = _np(eo['even_idx'])
    idx = (8 * ev[:, None] + np.arange(8)[None, :]).reshape(-1)
    Me = AtA[np.ix_(idx, idx)]                       # dense even-block operator
    lam = float(np.linalg.eigvalsh(Me).max())
    a, b = 0.0025, 1.0
    C = me.make_eo_ratio_sqrt_coeffs(a, b, 1.25 * lam, n_poles=24)

    xi = rng.standard_normal(8 * (V // 2))
    eye = np.eye(Me.shape[0])
    phi = C['A'] * xi + C['B'] * np.linalg.solve(Me + b * eye, xi)
    for wk, ek in zip(C['w'], C['e']):
        phi = phi + wk * np.linalg.solve(Me + ek * eye, xi)
    phi *= me.INV_SQRT2

    S2 = phi @ (Me + b * eye) @ np.linalg.solve(Me + a * eye, phi)
    assert abs(S2 / (0.5 * xi @ xi) - 1.0) < 1e-4, S2 / (0.5 * xi @ xi)


def test_eo_heatbath_ratio_dense_parity_and_weight():
    # Engine-path certification of the ratio heatbath: eo_heatbath_ratio must equal the
    # dense partial-fraction application of the same coefficients, and its action
    # S_R = φ†φ + (b−a)·φ†(M_e+a)⁻¹φ must equal ½‖ξ‖² (exact-weight sampling).
    L, V = 2, 2 ** 4
    rng = np.random.default_rng(53)
    h = rng.standard_normal((V, 4, 4))
    eo = me.eo_tables(L)
    fwd, back = me.neighbor_tables(L)
    A = _dense(h, L)
    ev = _np(eo['even_idx'])
    idx = (8 * ev[:, None] + np.arange(8)[None, :]).reshape(-1)
    Me = (-A @ A)[np.ix_(idx, idx)]
    lam = float(np.linalg.eigvalsh(Me).max())
    a, b = 0.0025, 1.0
    C = me.make_eo_ratio_sqrt_coeffs(a, b, 1.25 * lam, n_poles=24)

    xi_np = rng.standard_normal((V // 2, 8))
    phi = me.eo_heatbath_ratio(_mx64(xi_np), _mx64(h), C, eo, fwd, back, L,
                               tol=1e-12, max_iter=8000)

    xi_fl = xi_np.reshape(-1)
    eye = np.eye(Me.shape[0])
    phi_dense = C['A'] * xi_fl + C['B'] * np.linalg.solve(Me + b * eye, xi_fl)
    for wk, ek in zip(C['w'], C['e']):
        phi_dense = phi_dense + wk * np.linalg.solve(Me + ek * eye, xi_fl)
    phi_dense *= me.INV_SQRT2
    assert np.allclose(_np(phi).reshape(-1), phi_dense, atol=1e-8)

    S_r = (phi_dense @ phi_dense
           + (b - a) * phi_dense @ np.linalg.solve(Me + a * eye, phi_dense))
    assert abs(S_r / (0.5 * xi_fl @ xi_fl) - 1.0) < 1e-4


def test_eo_action_hasenbusch_matches_dense():
    # S = Σh²/4g + φ_H†(M+μ²)⁻¹φ_H + φ_R†φ_R + (μ²−m²)·φ_R†(M+m²)⁻¹φ_R — every solve
    # exact (power-1 actions, no rational), checked against dense linear algebra.
    L, V = 2, 2 ** 4
    g, msq, musq = 1.5, 0.0025, 1.0
    rng = np.random.default_rng(55)
    h = rng.standard_normal((V, 4, 4))
    eo = me.eo_tables(L)
    fwd, back = me.neighbor_tables(L)
    phi_h = rng.standard_normal((V // 2, 8))
    phi_r = rng.standard_normal((V // 2, 8))

    S = float(me.eo_action_hasenbusch(_mx64(h), _mx64(phi_h), _mx64(phi_r), g, msq, musq,
                                      eo, fwd, back, L, tol=1e-12, max_iter=8000))

    A = _dense(h, L)
    ev = _np(eo['even_idx'])
    idx = (8 * ev[:, None] + np.arange(8)[None, :]).reshape(-1)
    Me = (-A @ A)[np.ix_(idx, idx)]
    eye = np.eye(Me.shape[0])
    ph, pr = phi_h.reshape(-1), phi_r.reshape(-1)
    S_dense = (np.sum(h * h) / (4 * g)
               + ph @ np.linalg.solve(Me + musq * eye, ph)
               + pr @ pr + (musq - msq) * pr @ np.linalg.solve(Me + msq * eye, pr))
    assert abs(S - S_dense) < 1e-7 * max(1.0, abs(S_dense)), (S, S_dense)


def test_hasenbusch_forces_equal_negative_total_action_gradient():
    # The two-level forces from EXISTING primitives — coarse = (μ²−m²)·eo_fermion_force
    # (φ_R at m²), fine = eo_compute_force(φ_H at μ²) — must sum to −∂S_hasenbusch/∂h.
    L, V, g = 4, 4 ** 4, 1.5
    msq, musq = 0.04, 2.0
    rng = np.random.default_rng(57)
    h = rng.standard_normal((V, 4, 4))
    eo = me.eo_tables(L)
    fwd, back = me.neighbor_tables(L)
    phi_h = _mx64(rng.standard_normal((V // 2, 8)))
    phi_r = _mx64(rng.standard_normal((V // 2, 8)))

    F = _np((musq - msq) * me.eo_fermion_force(_mx64(h), phi_r, msq, eo, fwd, back, L,
                                               tol=1e-12, max_iter=8000)
            + me.eo_compute_force(_mx64(h), phi_h, g, musq, eo, fwd, back, L,
                                  tol=1e-12, max_iter=8000))

    def action(hh):
        return float(me.eo_action_hasenbusch(_mx64(hh), phi_h, phi_r, g, msq, musq,
                                             eo, fwd, back, L, tol=1e-12, max_iter=8000))

    eps = 1e-5
    for (x, mu, a) in [(0, 0, 0), (5, 2, 1), (17, 1, 3), (40, 3, 2)]:
        hp = h.copy(); hp[x, mu, a] += eps
        hm = h.copy(); hm[x, mu, a] -= eps
        fd = -(action(hp) - action(hm)) / (2 * eps)
        assert abs(F[x, mu, a] - fd) <= 1e-4 * max(1.0, abs(fd)), (x, mu, a, F[x, mu, a], fd)


def test_eo_integrate_hasenbusch_is_reversible():
    # The 2-level nested Omelyan must retrace under momentum flip (cold starts, tight
    # tol) — same gate as the single-level integrator.
    L, V, g = 4, 4 ** 4, 1.5
    msq, musq = 0.04, 2.0
    rng = np.random.default_rng(59)
    eo = me.eo_tables(L)
    h0 = rng.standard_normal((V, 4, 4))
    pi0 = rng.standard_normal((V, 4, 4))
    phi_h = _mx64(rng.standard_normal((V // 2, 8)))
    phi_r = _mx64(rng.standard_normal((V // 2, 8)))
    fwd, back = me.neighbor_tables(L)
    kw = dict(g=g, msq=msq, musq=musq, eo=eo, fwd=fwd, back=back, L=L,
              eps=0.1, n_outer=3, n_inner=3, tol=1e-12, max_iter=8000)

    h1, pi1 = me.eo_integrate_hasenbusch(_mx64(h0), _mx64(pi0), phi_h, phi_r, **kw)
    assert not np.allclose(_np(h1), h0)
    h2, pi2 = me.eo_integrate_hasenbusch(h1, -pi1, phi_h, phi_r, **kw)
    assert np.allclose(_np(h2), h0, atol=1e-9)
    assert np.allclose(_np(pi2), -pi0, atol=1e-9)


def test_hasenbusch_trajectory_mechanics():
    # Mechanics of the Hasenbusch refined trajectory: runs, FP64 configs out, finite ΔH,
    # boolean accept, exact Metropolis (rejected replicas keep the previous config
    # bit-for-bit). Chain-level unbiasedness = the slow Creutz gate.
    L, V, B = 4, 4 ** 4, 2
    g, msq, musq = 1.5, 0.04, 2.0
    rng0 = np.random.default_rng(61)
    h = _mx64(rng0.standard_normal((B, V, 4, 4)))
    fwd, back = me.neighbor_tables(L)
    eo = me.eo_tables(L)
    with mx.stream(mx.cpu):
        h00 = h[0]
    lam = 1.3 * float(me.estimate_lambda_max(me.hopping_blocks(h00, L), fwd, back, V,
                                             n_iter=150, seed=0))
    hb = me.make_rhmc_coeffs(lam, musq, n_poles=10)          # heavy PF at μ² (existing)
    rc = me.make_eo_ratio_sqrt_coeffs(msq, musq, lam, n_poles=20)
    rng = np.random.default_rng(9)

    for _ in range(3):
        h_prev = _np(h)
        h, dH, acc = me.eo_rhmc_trajectory_hasenbusch_refined(
            h, g, msq, musq, hb, rc, eo, fwd, back, L, 0.1, 3, 3, rng, mx.cpu,
            inner_tol=3e-4, max_outer=20)
        assert h.dtype == mx.float64 and h.shape == (B, V, 4, 4)
        assert dH.shape == (B,) and bool(mx.all(mx.isfinite(dH)))
        assert acc.dtype == mx.bool_ and acc.shape == (B,)
        h_np = _np(h)
        for b in range(B):
            if not bool(acc[b]):
                assert np.array_equal(h_np[b], h_prev[b])


@pytest.mark.slow
def test_creutz_identity_hasenbusch_chain_unbiased():
    # Chain-level correctness gate for the Hasenbusch split: the 2-PF sampled ensemble
    # must satisfy ⟨e^-ΔH⟩ = 1 — certifying the det-split + both heatbaths + the nested
    # integrator end to end (runs the FP32 inner solves on Metal when available).
    if _accelerator_available():
        mx.set_default_device(mx.gpu)
        device = mx.gpu
    else:
        device = mx.cpu
    L, V = 2, 2 ** 4
    g, msq, musq = 1.5, 0.01, 1.0
    fwd, back = me.neighbor_tables(L)
    eo = me.eo_tables(L)
    rng0 = np.random.default_rng(3)
    h0 = _mx64(1.7 * rng0.standard_normal((V, 4, 4)))
    lam = 1.3 * float(me.estimate_lambda_max(me.hopping_blocks(h0, L), fwd, back, V))
    hb = me.make_rhmc_coeffs(lam, musq, n_poles=10)
    rc = me.make_eo_ratio_sqrt_coeffs(msq, musq, lam, n_poles=20)
    rng = np.random.default_rng(5)
    h = _mx64(1.7 * rng.standard_normal((V, 4, 4)))
    dHs, nacc, n = [], 0, 240
    for t in range(n):
        h, dH, acc = me.eo_rhmc_trajectory_hasenbusch_refined(
            h, g, msq, musq, hb, rc, eo, fwd, back, L, 0.1, 4, 4, rng, device,
            tol_md=1e-4, inner_tol=3e-4, max_outer=20)
        mx.eval(h, dH, acc)
        if t >= n // 4:
            dHs.append(float(dH)); nacc += int(bool(acc))
    creutz = float(np.mean(np.exp(-np.array(dHs))))
    assert nacc / (n - n // 4) > 0.5 and abs(creutz - 1.0) < 0.08, (creutz, nacc / (n - n // 4))


def test_chrono_integrate_reaches_same_solution_at_tight_tol():
    # Chrono warm-starting changes only the CG starting guess; at tight tol the solve
    # converges to the SAME ψ_e, so the MD trajectory must match the cold-start one.
    # This is the fast correctness gate for defaulting chrono on in the driver.
    L, V = 4, 4 ** 4
    g, msq = 1.5, 0.04
    rng = np.random.default_rng(41)
    h0 = _mx64(rng.standard_normal((V, 4, 4)))
    pi0 = _mx64(rng.standard_normal((V, 4, 4)))
    phi_e = _mx64(rng.standard_normal((V // 2, 8)))
    fwd, back = me.neighbor_tables(L)
    eo = me.eo_tables(L)

    h_c, pi_c = me.eo_integrate(h0, pi0, phi_e, g, msq, eo, fwd, back, L, 0.03, 3,
                                tol=1e-10, chrono=False)
    h_w, pi_w = me.eo_integrate(h0, pi0, phi_e, g, msq, eo, fwd, back, L, 0.03, 3,
                                tol=1e-10, chrono=True)
    assert np.allclose(_np(h_w), _np(h_c), atol=1e-6), \
        float(np.abs(_np(h_w) - _np(h_c)).max())
    assert np.allclose(_np(pi_w), _np(pi_c), atol=1e-6)


def test_chrono_reversibility_softening_is_bounded():
    # Cold starts make the force a pure function of h, so the only reversibility
    # violation is the CG stopping rule crossing an iteration-count boundary between
    # legs — O(tol), measured ~2e-7 here. Chrono adds solver-history dependence on top
    # (a larger O(tol) softening). Both must stay far below field scale at production
    # tol (else Metropolis exactness is compromised); Creutz (slow) is the chain gate.
    L, V = 4, 4 ** 4
    g, msq = 1.5, 0.04
    rng = np.random.default_rng(43)
    h0 = _mx64(rng.standard_normal((V, 4, 4)))
    pi0 = _mx64(rng.standard_normal((V, 4, 4)))
    phi_e = _mx64(rng.standard_normal((V // 2, 8)))
    fwd, back = me.neighbor_tables(L)
    eo = me.eo_tables(L)
    href = float(mx.sqrt(mx.mean(h0 * h0)))

    def roundtrip(chrono):
        h1, pi1 = me.eo_integrate(h0, pi0, phi_e, g, msq, eo, fwd, back, L, 0.03, 4,
                                  tol=1e-4, chrono=chrono)
        h2, pi2 = me.eo_integrate(h1, -pi1, phi_e, g, msq, eo, fwd, back, L, 0.03, 4,
                                  tol=1e-4, chrono=chrono)
        return float(mx.sqrt(mx.mean((h2 - h0) ** 2))) / href

    assert roundtrip(False) < 1e-5      # cold: stopping-boundary crossings only, O(tol)
    assert roundtrip(True) < 5e-3       # chrono: controlled O(tol) history softening


@pytest.mark.slow
def test_creutz_identity_eo_refined_chain_unbiased_chrono():
    # Chain-level unbiasedness gate for chrono=True (the driver default): the O(tol_md)
    # reversibility softening must leave ⟨e^-ΔH⟩ = 1 intact. Mirrors the cold-start
    # Creutz test below with warm-started MD solves.
    if _accelerator_available():
        mx.set_default_device(mx.gpu)   # fixture restores after the test
        device = mx.gpu
    else:
        device = mx.cpu
    L, V = 2, 2 ** 4
    g, msq = 1.5, 0.01
    fwd, back = me.neighbor_tables(L)
    eo = me.eo_tables(L)
    rng0 = np.random.default_rng(3)
    h0 = _mx64(1.7 * rng0.standard_normal((V, 4, 4)))
    lam = float(me.estimate_lambda_max(me.hopping_blocks(h0, L), fwd, back, V))
    coeffs = me.make_rhmc_coeffs(1.3 * lam, msq, n_poles=12)
    rng = np.random.default_rng(5)
    h = _mx64(1.7 * rng.standard_normal((V, 4, 4)))
    dHs, nacc, n = [], 0, 240
    for t in range(n):
        h, dH, acc = me.eo_rhmc_trajectory_refined(h, g, msq, coeffs, eo, fwd, back, L,
                                                   0.05, 8, rng, device, tol_md=1e-4,
                                                   inner_tol=3e-4, max_outer=20,
                                                   chrono=True)
        mx.eval(h, dH, acc)
        if t >= n // 4:
            dHs.append(float(dH)); nacc += int(bool(acc))
    creutz = float(np.mean(np.exp(-np.array(dHs))))
    assert nacc / (n - n // 4) > 0.5 and abs(creutz - 1.0) < 0.08, (creutz, nacc / (n - n // 4))


@pytest.mark.slow
def test_creutz_identity_eo_refined_chain_unbiased():
    # The trajectory-level correctness gate for the refined (GPU-offloaded FP64) path:
    # FP32-inner accept/reject must leave the chain UNBIASED ⟹ Creutz ⟨e^-ΔH⟩ = 1.
    # Runs the FP32 inner solves on Metal when available (the production config).
    if _accelerator_available():
        mx.set_default_device(mx.gpu)   # fixture restores after the test
        device = mx.gpu
    else:
        device = mx.cpu
    L, V = 2, 2 ** 4
    g, msq = 1.5, 0.01
    fwd, back = me.neighbor_tables(L)
    eo = me.eo_tables(L)
    rng0 = np.random.default_rng(3)
    h0 = _mx64(1.7 * rng0.standard_normal((V, 4, 4)))
    lam = float(me.estimate_lambda_max(me.hopping_blocks(h0, L), fwd, back, V))
    coeffs = me.make_rhmc_coeffs(1.3 * lam, msq, n_poles=12)
    rng = np.random.default_rng(5)
    h = _mx64(1.7 * rng.standard_normal((V, 4, 4)))
    dHs, nacc, n = [], 0, 240
    for t in range(n):
        h, dH, acc = me.eo_rhmc_trajectory_refined(h, g, msq, coeffs, eo, fwd, back, L,
                                                   0.05, 8, rng, device, tol_md=1e-4,
                                                   inner_tol=3e-4, max_outer=20)
        mx.eval(h, dH, acc)
        if t >= n // 4:
            dHs.append(float(dH)); nacc += int(bool(acc))
    creutz = float(np.mean(np.exp(-np.array(dHs))))
    assert nacc / (n - n // 4) > 0.5 and abs(creutz - 1.0) < 0.08, (creutz, nacc / (n - n // 4))


# --- sampling: heatbath, trajectories, measurement ------------------------------------------

def test_heatbath_consistency_S_PF_equals_half_xi_norm():
    # Convention gate (real-PF): heatbath includes the 1/√2 real-Gaussian normalization
    # (INV_SQRT2) so S_PF(heatbath(ξ)) = ½‖ξ‖² — the ONE-Majorana weight det(A†A+m²)^{1/4}.
    # ‖ξ‖² (no ½) was the factor-2 Dirac bug. To Zolotarev accuracy.
    L, V = 2, 2 ** 4
    msq = 0.04
    rng = np.random.default_rng(10)
    h = _mx64(rng.standard_normal((V, 4, 4)))
    fwd, back = me.neighbor_tables(L)
    blocks = me.hopping_blocks(h, L)
    lam_max = float(me.estimate_lambda_max(blocks, fwd, back, V, n_iter=400, seed=0))
    coeffs = me.make_rhmc_coeffs(lam_max, msq, n_poles=18)

    xi = _mx64(rng.standard_normal((V, 8)))
    phi = me.heatbath(xi, blocks, fwd, back, coeffs, msq)

    # S_PF = a0 φ·φ + Σ_k α_k φ·(A†A+m²+β_k)⁻¹φ  (action operator r_{-1/2})
    betas = _mx64(coeffs['betas'] + msq)
    psi = me.multishift_cg(phi, blocks, fwd, back, betas, tol=1e-12, max_iter=8000)
    alphas = _mx64(coeffs['alphas'])
    phi_psi = mx.sum(mx.expand_dims(phi, -3) * psi, axis=(-2, -1))
    s_pf = float(coeffs['a0'] * mx.sum(phi * phi) + mx.sum(alphas * phi_psi))
    half_xi_norm = 0.5 * float(mx.sum(xi * xi))

    assert abs(s_pf - half_xi_norm) / half_xi_norm < 0.03


def test_eo_heatbath_consistency_S_PF_equals_half_xi_norm():
    # Power-pairing certification: eo heatbath (+1/2, /√2) ↔ eo action (−1) ⟹
    # S_PF(heatbath(ξ)) = ½‖ξ‖² ⟹ weight det(M_e+m²)^{1/2} (ONE Majorana).
    L, V = 4, 4 ** 4
    msq = 0.04
    rng = np.random.default_rng(33)
    h = _mx64(rng.standard_normal((V, 4, 4)))
    eo = me.eo_tables(L)
    Ve = V // 2
    fwd, back = me.neighbor_tables(L)
    blocks = me.hopping_blocks(h, L)
    lam = float(me.estimate_lambda_max(blocks, fwd, back, V, n_iter=300, seed=0))
    coeffs = me.make_rhmc_coeffs(1.3 * lam, msq, n_poles=18)

    xi = _mx64(rng.standard_normal((Ve, 8)))
    phi = me.eo_heatbath(xi, h, coeffs, msq, eo, fwd, back, L)
    psi = me.eo_multishift_cg(phi, blocks, eo, [msq], tol=1e-12, max_iter=8000)[..., 0, :, :]
    s_pf = float(mx.sum(phi * psi))
    half_xi_norm = 0.5 * float(mx.sum(xi * xi))
    assert abs(s_pf - half_xi_norm) / half_xi_norm < 0.03


def test_measure_observables_matches_numpy():
    from src.vestigial.hs_rhmc import hs_auxiliary_field_metric
    L, V, B = 2, 2 ** 4, 3
    rng = np.random.default_rng(11)
    h = rng.standard_normal((B, V, 4, 4))

    tet, trq, m_h, Q = me.measure_observables(_mx64(h), L)

    for b in range(B):
        Qn, trq2n = hs_auxiliary_field_metric(h[b].reshape(L, L, L, L, 4, 4), L)
        mhn = h[b].reshape(V, 4, 4).mean(0)
        tetn = float((mhn ** 2).sum())
        assert np.isclose(float(tet[b]), tetn, atol=1e-10)
        assert np.isclose(float(trq[b]), trq2n, atol=1e-10)
        assert np.allclose(_np(m_h[b]), mhn, atol=1e-10)
        assert np.allclose(_np(Q[b]), Qn, atol=1e-10)


def test_eo_mixed_trajectory_mechanics():
    # Mechanics of the eo mixed scheme (FP32 MD + FP64 accept/reject): runs, returns
    # FP64 configs, finite ΔH, boolean accept, exact Metropolis (rejected replicas
    # retain the previous config bit-for-bit). Noise from a numpy Generator —
    # framework-independent and deterministic.
    L, V, B = 2, 2 ** 4, 4
    rng_np = np.random.default_rng(21)
    h = _mx64(rng_np.standard_normal((B, V, 4, 4)))
    fwd, back = me.neighbor_tables(L)
    eo = me.eo_tables(L)
    blocks0 = me.hopping_blocks(h[0], L)
    lam_max = float(me.estimate_lambda_max(blocks0, fwd, back, V, n_iter=200, seed=0))
    coeffs = me.make_rhmc_coeffs(1.3 * lam_max, 0.04, n_poles=12)
    rng = np.random.default_rng(0)

    for _ in range(3):
        h_prev = _np(h)
        h, dH, acc = me.eo_rhmc_trajectory_mixed(h, 1.5, 0.04, coeffs, eo, fwd, back,
                                                 L, 0.05, 8, rng)
        assert h.dtype == mx.float64 and h.shape == (B, V, 4, 4)
        assert dH.shape == (B,) and bool(mx.all(mx.isfinite(dH)))
        assert acc.dtype == mx.bool_ and acc.shape == (B,)
        h_np = _np(h)
        for b in range(B):
            if not bool(acc[b]):
                assert np.array_equal(h_np[b], h_prev[b])


def test_fp32_metal_matvec_and_cg_match_fp64_cpu():
    # The Metal-path numerical gate: FP32 stencil matvec + CG on the GPU agree with
    # the FP64 CPU reference to FP32 accuracy. (Chain-level Metal certification =
    # the slow Creutz test + benchmark script.)
    if not _accelerator_available():
        pytest.skip("no GPU accelerator")
    prev = mx.default_device()
    mx.set_default_device(mx.gpu)
    try:
        L, V, B = 4, 4 ** 4, 3
        rng = np.random.default_rng(50)
        h = rng.standard_normal((B, V, 4, 4))
        psi = rng.standard_normal((B, V, 8))
        fwd, back = me.neighbor_tables(L)

        ref = _np(me.apply_AtA(_mx64(psi), me.hopping_blocks(_mx64(h), L), fwd, back))

        h32 = mx.array(h, dtype=mx.float32)
        psi32 = mx.array(psi, dtype=mx.float32)
        got = _np(me.apply_AtA(psi32, me.hopping_blocks(h32, L), fwd, back))
        scale = np.abs(ref).max()
        assert np.allclose(got, ref, atol=5e-5 * scale)

        # FP32 CG on Metal: solve then verify the FP64 residual is at FP32 level
        shifts = np.array([0.5, 2.0], dtype=np.float32)
        b32 = mx.array(rng.standard_normal((B, V, 8)), dtype=mx.float32)
        x32 = me.multishift_cg(b32, me.hopping_blocks(h32, L), fwd, back,
                               mx.array(shifts), tol=1e-5, max_iter=4000)
        x64 = _mx64(_np(x32))
        blocks64 = me.hopping_blocks(_mx64(h), L)
        b64 = _mx64(_np(b32))
        for k, s in enumerate(shifts):
            with mx.stream(mx.cpu):                # raw f64 slicing must stay off the GPU
                xk = x64[:, k]
            r = _np(me.apply_AtA(xk, blocks64, fwd, back, shift=float(s))) - _np(b64)
            rel = np.linalg.norm(r) / np.linalg.norm(_np(b64))
            assert rel < 5e-4, (k, rel)
    finally:
        mx.set_default_device(prev)


@pytest.mark.slow
def test_creutz_identity_eo_mixed_chain_unbiased():
    # Chain-level certification: FP32 MD + FP64 accept/reject leaves the chain
    # UNBIASED ⟹ Creutz ⟨e^-ΔH⟩ = 1 within error. Runs the FP32 stage on Metal
    # when available (the production configuration), else FP32-CPU.
    if _accelerator_available():
        mx.set_default_device(mx.gpu)   # fixture restores after the test
    L, V = 2, 2 ** 4
    g, msq = 1.5, 0.01
    fwd, back = me.neighbor_tables(L)
    eo = me.eo_tables(L)
    rng0 = np.random.default_rng(3)
    h0 = _mx64(1.7 * rng0.standard_normal((V, 4, 4)))
    lam = float(me.estimate_lambda_max(me.hopping_blocks(h0, L), fwd, back, V))
    coeffs = me.make_rhmc_coeffs(1.3 * lam, msq, n_poles=12)
    rng = np.random.default_rng(5)
    h = _mx64(1.7 * rng.standard_normal((V, 4, 4)))
    dHs, nacc, n = [], 0, 240
    for t in range(n):
        h, dH, acc = me.eo_rhmc_trajectory_mixed(h, g, msq, coeffs, eo, fwd, back,
                                                 L, 0.05, 8, rng, tol_md=1e-4, tol_acc=1e-10)
        if t >= n // 4:
            dHs.append(float(dH)); nacc += int(bool(acc))
    creutz = float(np.mean(np.exp(-np.array(dHs))))
    assert nacc / (n - n // 4) > 0.5 and abs(creutz - 1.0) < 0.08, (creutz, nacc / (n - n // 4))


def test_eo_multishift_cg_matches_full_on_even():
    L, V = 4, 4 ** 4
    rng = np.random.default_rng(32)
    h = rng.standard_normal((V, 4, 4))
    shifts = np.array([0.05, 0.5, 3.0])
    eo = me.eo_tables(L)
    Ve = V // 2
    b_e = rng.standard_normal((Ve, 8))
    fwd, back = me.neighbor_tables(L)
    blocks = me.hopping_blocks(_mx64(h), L)

    b_full = np.zeros((V, 8))
    b_full[_np(eo['even_idx'])] = b_e
    x_full = me.multishift_cg(_mx64(b_full), blocks, fwd, back, _mx64(shifts),
                              tol=1e-10, max_iter=8000)
    x_eo = me.eo_multishift_cg(_mx64(b_e), blocks, eo, _mx64(shifts), tol=1e-10, max_iter=8000)

    even_np = _np(eo['even_idx'])
    for k in range(len(shifts)):
        assert np.allclose(_np(x_eo[k]), _np(x_full[k])[even_np], atol=1e-7)


# --- Zolotarev heatbath-coefficient quality: the m->0 rational-approx gate -----------------

def test_zolotarev_max_relerr_exact_single_pole_is_zero():
    # r(x) = 1/x is EXACTLY x^{-1}; the unsigned max relerr must be ~0 (eval sanity).
    err = me.zolotarev_max_relerr(0.0, [1.0], [0.0], 0.1, 100.0, power=-1.0)
    assert err < 1e-12


def test_zolotarev_max_relerr_exposes_undersized_poles_at_stiff_mass():
    # Ground-truth quality of the heatbath r_{-1/2} set: unsigned max relerr over the
    # spectral range. Must (a) fall sharply with pole count and (b) show n_poles=14 is
    # inadequate at the stiff m=0.05 range where the heatbath-CONSISTENCY ratio (a signed
    # spectral average) hides the true error via equioscillation cancellation.
    from src.vestigial.hs_rhmc import compute_zolotarev_coefficients
    lo, hi = 0.05 ** 2, 4220.0                       # m=0.05, g=8 padded spectral range

    def relerr(n):
        a0, al, be = compute_zolotarev_coefficients(n, lo, hi, -0.5)
        return me.zolotarev_max_relerr(a0, al, be, lo, hi, power=-0.5)

    e14, e50 = relerr(14), relerr(50)
    assert e14 > 0.05          # default 14 poles: >5% max error at m=0.05 (measured ~15%)
    assert e50 < 5e-3          # 50 poles: sub-0.5% (measured ~2e-4)
    assert e50 < e14


def test_gate_selected_heatbath_samples_correct_weight_at_m005():
    """End-to-end m→0 regression: build_coeffs_mlx's GATE-selected n_poles must make the
    heatbath sample the correct one-Majorana weight at the stiffest campaign mass — i.e.
    S_PF(φ(ξ)) = ½‖ξ‖² to ~1%. Ties the numerical max-error gate to correct PHYSICS
    sampling (which the S_PF ratio measures). κ is volume-flat so L=2 reproduces the m=0.05
    stiffness cheaply. Guards against a future coeff/default change silently regressing the
    heatbath weight — the uncorrectable-bias case that motivated the gate."""
    import scripts.run_rhmc_gpu_production as drv
    L, V, Ve = 2, 2 ** 4, (2 ** 4) // 2
    g, m = 8.0, 0.05
    msq = m * m
    coeffs, lam = drv.build_coeffs_mlx(L, g, msq, n_poles=14, seed=5, hb_relerr_tol=1e-3)
    fwd, back = me.neighbor_tables(L)
    eo = me.eo_tables(L)
    h = _mx64(np.sqrt(2 * g) * np.random.default_rng(7).standard_normal((V, 4, 4)))
    blocks = me.hopping_blocks(h, L)
    ratios = []
    for s in range(4):
        xi = _mx64(np.random.default_rng(100 + s).standard_normal((Ve, 8)))
        phi_e = me.eo_heatbath(xi, h, coeffs, msq, eo, fwd, back, L, tol=1e-10)
        psi = me.eo_multishift_cg(phi_e, blocks, eo, _mx64([msq]), tol=1e-10)[0]
        ratios.append(float(mx.sum(phi_e * psi)) / (0.5 * float(mx.sum(xi * xi))))
    assert abs(float(np.mean(ratios)) - 1.0) < 0.02, float(np.mean(ratios))   # gate → correct sampling
