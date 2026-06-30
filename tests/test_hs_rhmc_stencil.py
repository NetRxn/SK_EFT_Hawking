"""TDD for the batched stencil matvec (the GPU-port perf kernel).

Oracle: the scaffold's dense `build_fermion_matrix_torch`. The matrix-free
stencil A·ψ must equal A_dense @ ψ exactly (to float64 round-off), including
across batch dimensions (couplings × replicas × poles fused into leading axes).
"""
import numpy as np
import pytest

torch = pytest.importorskip("torch")

from src.vestigial.hs_rhmc_torch import build_fermion_matrix_torch
import src.vestigial.hs_rhmc_stencil as st

CPU = torch.device("cpu")
F64 = torch.float64


def _dense(h, L):
    A = build_fermion_matrix_torch(h, L, device=CPU, dtype=F64)
    return A.cpu().numpy()


def test_apply_A_matches_dense_single_config():
    L, V = 2, 2 ** 4
    rng = np.random.default_rng(0)
    h = rng.standard_normal((V, 4, 4))
    psi = rng.standard_normal((V, 8))

    expected = _dense(h, L) @ psi.reshape(-1)          # (8V,)

    fwd, back = st.neighbor_tables(L, CPU)
    blocks = st.hopping_blocks(torch.tensor(h), L, device=CPU, dtype=F64)
    got = st.apply_A(torch.tensor(psi), blocks, fwd, back)   # (V, 8)

    assert np.allclose(got.reshape(-1).numpy(), expected, atol=1e-10)


def test_apply_A_batched_over_distinct_configs():
    # The whole point: couplings × replicas as leading batch dims, each config
    # solved against its OWN matrix (not a broadcast of one).
    L, V, B = 2, 2 ** 4, 3
    rng = np.random.default_rng(1)
    h = rng.standard_normal((B, V, 4, 4))
    psi = rng.standard_normal((B, V, 8))

    fwd, back = st.neighbor_tables(L, CPU)
    blocks = st.hopping_blocks(torch.tensor(h), L, device=CPU, dtype=F64)
    got = st.apply_A(torch.tensor(psi), blocks, fwd, back).numpy()   # (B, V, 8)

    for b in range(B):
        expected = (_dense(h[b], L) @ psi[b].reshape(-1)).reshape(V, 8)
        assert np.allclose(got[b], expected, atol=1e-10)
    # configs are genuinely distinct (not a broadcast)
    assert not np.allclose(got[0], got[1])


def test_apply_AtA_matches_minus_A_squared_with_shift():
    L, V = 2, 2 ** 4
    rng = np.random.default_rng(2)
    h = rng.standard_normal((V, 4, 4))
    psi = rng.standard_normal((V, 8))
    shift = 0.37

    A = _dense(h, L)
    expected = (-A @ A @ psi.reshape(-1)) + shift * psi.reshape(-1)   # (A†A + σ)ψ

    fwd, back = st.neighbor_tables(L, CPU)
    blocks = st.hopping_blocks(torch.tensor(h), L, device=CPU, dtype=F64)
    got = st.apply_AtA(torch.tensor(psi), blocks, fwd, back, shift=shift)

    assert np.allclose(got.reshape(-1).numpy(), expected, atol=1e-10)
    # A†A is symmetric PSD ⟹ ψ·(A†Aψ) ≥ 0
    ata = st.apply_AtA(torch.tensor(psi), blocks, fwd, back).reshape(-1).numpy()
    assert float(psi.reshape(-1) @ ata) >= -1e-10


def test_apply_A_broadcasts_config_over_poles():
    # CG usage: ONE config, K shift-vectors. blocks (B,1,...) broadcast over psi (B,K,...).
    L, V, B, K = 2, 2 ** 4, 2, 5
    rng = np.random.default_rng(3)
    h = rng.standard_normal((B, V, 4, 4))
    psi = rng.standard_normal((B, K, V, 8))

    fwd, back = st.neighbor_tables(L, CPU)
    blocks = st.hopping_blocks(torch.tensor(h), L, device=CPU, dtype=F64)
    blocks_k = blocks.unsqueeze(1)                       # (B, 1, V, 4, 8, 8)
    got = st.apply_A(torch.tensor(psi), blocks_k, fwd, back).numpy()   # (B, K, V, 8)

    for b in range(B):
        A = _dense(h[b], L)
        for k in range(K):
            expected = (A @ psi[b, k].reshape(-1)).reshape(V, 8)
            assert np.allclose(got[b, k], expected, atol=1e-10)


def test_multishift_cg_matches_dense_solve_single_config():
    # Solve (A†A + σ_k) x_k = b for all shifts; match a dense linear solve.
    L, V = 2, 2 ** 4
    rng = np.random.default_rng(4)
    h = rng.standard_normal((V, 4, 4))
    b = rng.standard_normal((V, 8))
    shifts = np.array([0.5, 1.0, 2.0, 5.0])

    A = _dense(h, L)
    AtA = -A @ A
    eye = np.eye(8 * V)
    expected = np.stack([np.linalg.solve(AtA + s * eye, b.reshape(-1)) for s in shifts])  # (K, 8V)

    fwd, back = st.neighbor_tables(L, CPU)
    blocks = st.hopping_blocks(torch.tensor(h), L, device=CPU, dtype=F64)
    x = st.multishift_cg(torch.tensor(b), blocks, fwd, back,
                         torch.tensor(shifts), tol=1e-10, max_iter=4000)  # (K, V, 8)

    for k in range(len(shifts)):
        assert np.allclose(x[k].reshape(-1).numpy(), expected[k], atol=1e-6)


def test_multishift_cg_batched_over_configs():
    L, V, B = 2, 2 ** 4, 3
    rng = np.random.default_rng(5)
    h = rng.standard_normal((B, V, 4, 4))
    b = rng.standard_normal((B, V, 8))
    shifts = np.array([0.5, 2.0])

    fwd, back = st.neighbor_tables(L, CPU)
    blocks = st.hopping_blocks(torch.tensor(h), L, device=CPU, dtype=F64)
    x = st.multishift_cg(torch.tensor(b), blocks, fwd, back,
                         torch.tensor(shifts), tol=1e-10, max_iter=4000)  # (B, K, V, 8)

    for bi in range(B):
        A = _dense(h[bi], L)
        AtA = -A @ A
        eye = np.eye(8 * V)
        for k, s in enumerate(shifts):
            expected = np.linalg.solve(AtA + s * eye, b[bi].reshape(-1))
            assert np.allclose(x[bi, k].reshape(-1).numpy(), expected, atol=1e-6)
