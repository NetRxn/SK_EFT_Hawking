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


def test_force_equals_negative_action_gradient():
    # The property that makes HMC conserve H: F = −∂S/∂h. Finite-difference the
    # action (reference-independent ground truth) and match the analytic force.
    L, V, g = 2, 2 ** 4, 1.5
    rng = np.random.default_rng(7)
    h = rng.standard_normal((V, 4, 4))
    phi = rng.standard_normal((V, 8))
    alphas = np.array([0.5, 0.3, 0.2])
    betas = np.array([0.3, 1.0, 3.0])
    a0 = 0.4
    fwd, back = st.neighbor_tables(L, CPU)
    phit = torch.tensor(phi)
    al, be = torch.tensor(alphas), torch.tensor(betas)

    F = st.compute_force(torch.tensor(h), phit, g, al, be, fwd, back, L,
                         tol=1e-12, max_iter=5000).numpy()

    def action(hh):
        return float(st.action(torch.tensor(hh), phit, g, a0, al, be, fwd, back, L,
                               tol=1e-12, max_iter=5000))

    eps = 1e-5
    for (x, mu, a) in [(0, 0, 0), (3, 2, 1), (7, 1, 3), (12, 3, 2)]:
        hp = h.copy(); hp[x, mu, a] += eps
        hm = h.copy(); hm[x, mu, a] -= eps
        fd = -(action(hp) - action(hm)) / (2 * eps)
        assert abs(F[x, mu, a] - fd) <= 1e-4 * max(1.0, abs(fd)), (x, mu, a, F[x, mu, a], fd)


def test_omelyan_integrator_is_reversible():
    # Reversibility (⟹ detailed balance): integrate forward, flip momenta,
    # integrate forward again → return to the start (FP64 round-off).
    L, V, g = 2, 2 ** 4, 1.5
    rng = np.random.default_rng(8)
    h0 = torch.tensor(rng.standard_normal((V, 4, 4)))
    pi0 = torch.tensor(rng.standard_normal((V, 4, 4)))
    phi = torch.tensor(rng.standard_normal((V, 8)))
    al = torch.tensor([0.5, 0.3, 0.2])
    be = torch.tensor([0.3, 1.0, 3.0])
    fwd, back = st.neighbor_tables(L, CPU)
    kw = dict(fwd=fwd, back=back, L=L, eps=0.1, n_steps=5, tol=1e-12, max_iter=5000)

    h1, pi1 = st.integrate(h0, pi0, phi, g, al, be, **kw)
    assert not torch.allclose(h1, h0)                       # it actually moved
    h2, pi2 = st.integrate(h1, -pi1, phi, g, al, be, **kw)

    assert torch.allclose(h2, h0, atol=1e-9)
    assert torch.allclose(pi2, -pi0, atol=1e-9)


def test_lambda_max_matches_dense():
    L, V = 2, 2 ** 4
    rng = np.random.default_rng(9)
    h = rng.standard_normal((V, 4, 4))
    A = _dense(h, L)
    lam_true = np.linalg.eigvalsh(-A @ A).max()

    fwd, back = st.neighbor_tables(L, CPU)
    blocks = st.hopping_blocks(torch.tensor(h), L, device=CPU, dtype=F64)
    lam = float(st.estimate_lambda_max(blocks, fwd, back, V, n_iter=400, seed=0))

    assert abs(lam - lam_true) / lam_true < 1e-2


def test_heatbath_consistency_S_PF_equals_xi_norm():
    # Convention-independent gate: heatbath = (action operator)^{-1/2} ⟹
    # S_PF(heatbath(ξ)) = ‖ξ‖² (to Zolotarev accuracy).
    L, V, g = 2, 2 ** 4, 1.5
    msq = 0.04                                              # m = 0.2 regulator
    rng = np.random.default_rng(10)
    h = torch.tensor(rng.standard_normal((V, 4, 4)))
    fwd, back = st.neighbor_tables(L, CPU)
    blocks = st.hopping_blocks(h, L, device=CPU, dtype=F64)
    lam_max = float(st.estimate_lambda_max(blocks, fwd, back, V, n_iter=400, seed=0))
    coeffs = st.make_rhmc_coeffs(lam_max, msq, n_poles=18)

    gen = torch.Generator().manual_seed(0)
    xi = torch.randn(V, 8, dtype=F64, generator=gen)
    phi = st.heatbath(xi, blocks, fwd, back, coeffs, msq)

    # S_PF = φ · r_{-1/2}(A†A+m²) · φ  (action operator)
    betas = torch.as_tensor(coeffs['betas'], dtype=F64) + msq
    psi = st.multishift_cg(phi, blocks, fwd, back, betas, tol=1e-12, max_iter=8000)  # (K,V,8)
    alphas = torch.as_tensor(coeffs['alphas'], dtype=F64)
    s_pf = float(coeffs['a0']) * (phi * phi).sum() + (alphas * (phi.unsqueeze(-3) * psi).sum((-2, -1))).sum()
    xi_norm = (xi * xi).sum()

    assert abs(float(s_pf) - float(xi_norm)) / float(xi_norm) < 0.03


@pytest.mark.slow
def test_creutz_identity_unbiased_chain():
    # The integrated correctness gate: a correct heatbath + force + reversible
    # integrator + Metropolis ⟹ ⟨exp(−ΔH)⟩ = 1 in equilibrium.
    L, V, g = 2, 2 ** 4, 2.0
    msq = 0.04
    fwd, back = st.neighbor_tables(L, CPU)
    gen = torch.Generator().manual_seed(0)
    h = 0.1 * torch.randn(V, 4, 4, dtype=F64, generator=gen)

    # fix coeffs from a generous spectral range (bounds the chain's λmax)
    blk0 = st.hopping_blocks(2.0 * torch.randn(V, 4, 4, dtype=F64, generator=gen), L, device=CPU, dtype=F64)
    lam_max = 1.5 * float(st.estimate_lambda_max(blk0, fwd, back, V, n_iter=300, seed=1))
    coeffs = st.make_rhmc_coeffs(lam_max, msq, n_poles=16)

    kw = dict(g=g, msq=msq, coeffs=coeffs, fwd=fwd, back=back, L=L, eps=0.1, n_md=10,
              rng_gen=gen, tol=1e-11, max_iter=8000)
    dHs, naccept = [], 0
    n_therm, n_meas = 25, 120
    for t in range(n_therm + n_meas):
        h, dH, acc = st.rhmc_trajectory(h, **kw)
        if t >= n_therm:
            dHs.append(float(dH))
            naccept += int(bool(acc))
    creutz = float(np.mean(np.exp(-np.array(dHs))))
    acc_rate = naccept / n_meas
    assert acc_rate > 0.7, acc_rate
    assert abs(creutz - 1.0) < 0.05, (creutz, acc_rate)


def test_measure_observables_matches_numpy():
    # Batched measurement (tet_m2, trQ2 + m_h, Q instrumentation) vs the existing
    # numpy reference; per config.
    from src.vestigial.hs_rhmc import hs_auxiliary_field_metric
    L, V, B = 2, 2 ** 4, 3
    rng = np.random.default_rng(11)
    h = rng.standard_normal((B, V, 4, 4))

    tet, trq, m_h, Q = st.measure_observables(torch.tensor(h), L)

    for b in range(B):
        Qn, trq2n = hs_auxiliary_field_metric(h[b].reshape(L, L, L, L, 4, 4), L)
        mhn = h[b].reshape(V, 4, 4).mean(0)
        tetn = float((mhn ** 2).sum())
        assert np.isclose(float(tet[b]), tetn, atol=1e-10)
        assert np.isclose(float(trq[b]), trq2n, atol=1e-10)
        assert np.allclose(m_h[b].numpy(), mhn, atol=1e-10)
        assert np.allclose(Q[b].numpy(), Qn, atol=1e-10)


def test_mixed_trajectory_mechanics():
    # Mechanics of the mixed scheme (FP32 MD + FP64 accept/reject): runs, returns
    # FP64 configs, finite ΔH, boolean accept. (Device='cpu' exercises the precision
    # mixing without needing MPS; full unbiasedness is in validate_rhmc_gpu.py.)
    L, V, B = 2, 2 ** 4, 4
    rng = np.random.default_rng(13)
    h = torch.tensor(rng.standard_normal((B, V, 4, 4)))            # FP64
    fwd, back = st.neighbor_tables(L, CPU)
    lam_max = float(st.estimate_lambda_max(st.hopping_blocks(h[0], L, device=CPU, dtype=F64),
                                           fwd, back, V, n_iter=200, seed=0))
    coeffs = st.make_rhmc_coeffs(1.3 * lam_max, 0.04, n_poles=12)
    gen = torch.Generator().manual_seed(0)

    for _ in range(3):
        h, dH, acc = st.rhmc_trajectory_mixed(h, 1.5, 0.04, coeffs, fwd, back, fwd, back,
                                              L, 0.05, 8, CPU, gen, gen)
        assert h.dtype == torch.float64 and h.shape == (B, V, 4, 4)
        assert dH.shape == (B,) and torch.isfinite(dH).all()
        assert acc.dtype == torch.bool and acc.shape == (B,)
