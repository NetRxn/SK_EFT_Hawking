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
