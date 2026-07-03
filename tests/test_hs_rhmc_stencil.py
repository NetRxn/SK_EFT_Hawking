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


def test_heatbath_consistency_S_PF_equals_half_xi_norm():
    # Convention gate (real-PF): heatbath includes the 1/√2 real-Gaussian normalization
    # (INV_SQRT2) so it samples e^{−S_PF} for S_PF=φ·(A†A+m²)^{-1/2}·φ, giving the correct
    # ONE-Majorana weight det(A†A+m²)^{1/4}. Consequently S_PF(heatbath(ξ)) = ½‖ξ‖²
    # (NOT ‖ξ‖² — that was the factor-2 Dirac bug). To Zolotarev accuracy.
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
    half_xi_norm = 0.5 * (xi * xi).sum()

    assert abs(float(s_pf) - float(half_xi_norm)) / float(half_xi_norm) < 0.03


def test_eo_integrator_is_reversible():
    # Reversibility of the even-odd MD (⟹ detailed balance): fwd → flip π → fwd returns.
    L, V, g = 4, 4 ** 4, 1.5
    msq = 0.04
    rng = np.random.default_rng(35)
    eo = st.eo_tables(L, CPU)
    Ve = V // 2
    h0 = torch.tensor(rng.standard_normal((V, 4, 4)))
    pi0 = torch.tensor(rng.standard_normal((V, 4, 4)))
    phi_e = torch.tensor(rng.standard_normal((Ve, 8)))
    fwd, back = st.neighbor_tables(L, CPU)
    kw = dict(phi_e=phi_e, g=g, msq=msq, eo=eo, fwd=fwd, back=back, L=L,
              eps=0.08, n_steps=5, tol=1e-12, max_iter=8000)

    h1, pi1 = st.eo_integrate(h0, pi0, **kw)
    assert not torch.allclose(h1, h0)
    h2, pi2 = st.eo_integrate(h1, -pi1, **kw)
    assert torch.allclose(h2, h0, atol=1e-9)
    assert torch.allclose(pi2, -pi0, atol=1e-9)


@pytest.mark.slow
def test_eo_creutz_and_matches_full_observables():
    # The decisive even-odd gate: (a) the eo chain is unbiased (⟨e^−ΔH⟩=1), AND (b) its
    # ⟨tet_m2⟩ matches the FULL-engine chain at the same (g,m,L) ⟹ even-odd samples the
    # identical fermion weight det(A†A+m²)^{1/4}, at ~2× lower cost.
    L, V, g = 2, 2 ** 4, 2.0
    msq = 0.04
    fwd, back = st.neighbor_tables(L, CPU)
    eo = st.eo_tables(L, CPU)
    Ve = V // 2
    gen = torch.Generator().manual_seed(0)
    blk0 = st.hopping_blocks(2.0 * torch.randn(V, 4, 4, dtype=F64, generator=gen), L, device=CPU, dtype=F64)
    lam = 1.5 * float(st.estimate_lambda_max(blk0, fwd, back, V, n_iter=300, seed=1))
    coeffs = st.make_rhmc_coeffs(lam, msq, n_poles=16)
    n_therm, n_meas = 20, 150
    # L=2, eps=0.05 (τ=0.5): stable step (both engines accept well). Loose MD tol (tol_md=1e-4)
    # + tight accept tol (1e-8) keeps it fast — the accept/reject stays FP64-exact. (This is a
    # cheap gross-mismatch check; the rigorous eo≡full proof is the deterministic logdet identity.)
    EPS, NMD = 0.05, 10

    gen_eo = torch.Generator().manual_seed(7)
    h = 0.1 * torch.randn(V, 4, 4, dtype=F64, generator=gen_eo)
    dHs, nacc = [], 0
    for t in range(n_therm + n_meas):
        h, dH, acc = st.eo_rhmc_trajectory(h, g, msq, coeffs, eo, fwd, back, L,
                                           eps=EPS, n_md=NMD, rng_gen=gen_eo, tol=1e-8, tol_md=1e-4, max_iter=8000)
        if t >= n_therm:
            dHs.append(float(dH)); nacc += int(bool(acc))
    creutz = float(np.mean(np.exp(-np.array(dHs))))
    assert nacc / n_meas > 0.7 and abs(creutz - 1.0) < 0.05, (creutz, nacc / n_meas)

    # (b) eo and full sample the IDENTICAL fermion weight — proven DETERMINISTICALLY per-config,
    # NOT via a stochastic ⟨tet_m2⟩ chain race. (At small V that race has huge autocorrelation-
    # inflated error — naive var/N badly underestimates it, manufacturing false "many-σ" gaps;
    # that fragile comparison is exactly what sent a prior session down a 10h dead end.)
    # ¼logdet(A†A+m²) == ½logdet(M_e+m²) ⟺ det(A†A+m²)^{1/4}=det(M_e+m²)^{1/2} (same target).
    nF = V * 8
    gen_c = torch.Generator().manual_seed(3)
    for _ in range(5):
        hc = (2.0 * g) ** 0.5 * torch.randn(V, 4, 4, dtype=F64, generator=gen_c)
        blk = st.hopping_blocks(hc, L, device=CPU, dtype=F64)
        AtA = torch.stack([st.apply_AtA(torch.eye(nF, dtype=F64)[i].reshape(V, 8), blk, fwd, back, shift=msq).reshape(nF)
                           for i in range(nF)], 1)
        Me = torch.stack([st.apply_Me(torch.eye(Ve * 8, dtype=F64)[i].reshape(Ve, 8), blk, eo, shift=msq).reshape(Ve * 8)
                          for i in range(Ve * 8)], 1)
        _, ldA = torch.linalg.slogdet(AtA)
        _, ldM = torch.linalg.slogdet(Me)
        assert abs(0.25 * float(ldA) - 0.5 * float(ldM)) < 1e-8, (float(ldA), float(ldM))


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


@pytest.mark.slow
def test_creutz_identity_refined_chain_unbiased():
    # Chain-level certification of the mixed-precision refined trajectory: the FP32-inner
    # accept/reject must keep the FULL chain unbiased ⟹ ⟨exp(−ΔH)⟩ = 1 in equilibrium.
    # (device=CPU runs the inner solve in FP32 on CPU — exercises the precision mix.)
    L, V, g = 2, 2 ** 4, 2.0
    msq = 0.04
    fwd, back = st.neighbor_tables(L, CPU)
    gen = torch.Generator().manual_seed(0)
    h = 0.1 * torch.randn(V, 4, 4, dtype=F64, generator=gen)

    blk0 = st.hopping_blocks(2.0 * torch.randn(V, 4, 4, dtype=F64, generator=gen), L, device=CPU, dtype=F64)
    lam_max = 1.5 * float(st.estimate_lambda_max(blk0, fwd, back, V, n_iter=300, seed=1))
    coeffs = st.make_rhmc_coeffs(lam_max, msq, n_poles=16)

    dHs, naccept = [], 0
    n_therm, n_meas = 25, 120
    for t in range(n_therm + n_meas):
        h, dH, acc = st.rhmc_trajectory_refined(h, g, msq, coeffs, fwd, back, fwd, back,
                                                L, eps=0.1, n_md=10, device=CPU,
                                                gen_dev=gen, gen_cpu=gen,
                                                inner_tol=3e-4, max_outer=20)
        if t >= n_therm:
            dHs.append(float(dH))
            naccept += int(bool(acc))
    creutz = float(np.mean(np.exp(-np.array(dHs))))
    acc_rate = naccept / n_meas
    assert acc_rate > 0.7, acc_rate
    assert abs(creutz - 1.0) < 0.05, (creutz, acc_rate)


def test_eo_tables_parity_partition():
    # Even/odd partition is exact for even L and every hop flips parity (bipartite).
    L, V = 4, 4 ** 4
    eo = st.eo_tables(L, CPU)
    assert eo['even_idx'].shape == (V // 2,) and eo['odd_idx'].shape == (V // 2,)
    # disjoint cover
    allidx = torch.cat([eo['even_idx'], eo['odd_idx']]).sort().values
    assert torch.equal(allidx, torch.arange(V))
    # every forward/back neighbor of an even site is odd (parity flips)
    fwd, back = st.neighbor_tables(L, CPU)
    parity = torch.zeros(V, dtype=torch.long)
    parity[eo['odd_idx']] = 1
    for mu in range(4):
        assert (parity[fwd[eo['even_idx'], mu]] == 1).all()
        assert (parity[back[eo['even_idx'], mu]] == 1).all()


def test_apply_Me_halfsize_matches_full_AtA_on_even():
    # Even-odd reduction: A†A is block-diagonal in parity, so the half-size even-block
    # operator M_e must equal the full A†A restricted to even-supported vectors.
    L, V = 4, 4 ** 4
    rng = np.random.default_rng(30)
    h = rng.standard_normal((V, 4, 4))
    fwd, back = st.neighbor_tables(L, CPU)
    blocks = st.hopping_blocks(torch.tensor(h), L, device=CPU, dtype=F64)
    eo = st.eo_tables(L, CPU)
    Ve = V // 2
    psi_e = torch.tensor(rng.standard_normal((Ve, 8)))

    # oracle: scatter even → full, apply_AtA (certified), gather even
    psi_full = torch.zeros(V, 8, dtype=F64)
    psi_full[eo['even_idx']] = psi_e
    ref = st.apply_AtA(psi_full, blocks, fwd, back)[eo['even_idx']]

    got = st.apply_Me(psi_e, blocks, eo)
    assert got.shape == (Ve, 8)
    assert torch.allclose(got, ref, atol=1e-10), float((got - ref).abs().max())

    # with shift
    got_s = st.apply_Me(psi_e, blocks, eo, shift=0.37)
    assert torch.allclose(got_s, ref + 0.37 * psi_e, atol=1e-10)


def test_apply_Me_batched_over_configs():
    # Half-size matvec carries leading batch dims (couplings × replicas), each its own M_e.
    L, V, B = 4, 4 ** 4, 3
    rng = np.random.default_rng(31)
    h = rng.standard_normal((B, V, 4, 4))
    fwd, back = st.neighbor_tables(L, CPU)
    blocks = st.hopping_blocks(torch.tensor(h), L, device=CPU, dtype=F64)
    eo = st.eo_tables(L, CPU)
    Ve = V // 2
    psi_e = torch.tensor(rng.standard_normal((B, Ve, 8)))

    got = st.apply_Me(psi_e, blocks, eo)
    for b in range(B):
        psi_full = torch.zeros(V, 8, dtype=F64)
        psi_full[eo['even_idx']] = psi_e[b]
        ref = st.apply_AtA(psi_full, blocks[b], fwd, back)[eo['even_idx']]
        assert torch.allclose(got[b], ref, atol=1e-10)


def test_eo_multishift_cg_matches_full_on_even():
    # The even-odd solve (M_e+σ)⁻¹b_e equals the full (A†A+σ)⁻¹ solve restricted to even
    # (A†A block-diagonal ⟹ odd block stays zero for an even source).
    L, V = 4, 4 ** 4
    rng = np.random.default_rng(32)
    h = rng.standard_normal((V, 4, 4))
    shifts = np.array([0.05, 0.5, 3.0])
    eo = st.eo_tables(L, CPU)
    Ve = V // 2
    b_e = torch.tensor(rng.standard_normal((Ve, 8)))
    fwd, back = st.neighbor_tables(L, CPU)
    blocks = st.hopping_blocks(torch.tensor(h), L, device=CPU, dtype=F64)

    b_full = torch.zeros(V, 8, dtype=F64)
    b_full[eo['even_idx']] = b_e
    x_full = st.multishift_cg(b_full, blocks, fwd, back, torch.tensor(shifts), tol=1e-10, max_iter=8000)
    x_eo = st.eo_multishift_cg(b_e, blocks, eo, torch.tensor(shifts), tol=1e-10, max_iter=8000)

    for k in range(len(shifts)):
        assert torch.allclose(x_eo[k], x_full[k][eo['even_idx']], atol=1e-7), \
            float((x_eo[k] - x_full[k][eo['even_idx']]).abs().max())


def test_eo_heatbath_consistency_S_PF_equals_half_xi_norm():
    # Power-pairing certification with the real-PF 1/√2 normalization (INV_SQRT2): heatbath
    # (+1/2, /√2) ↔ action (−1) ⟹ S_PF(heatbath(ξ)) = ½‖ξ‖² ⟹ weight det(M_e+m²)^{1/2}
    # = det(A†A+m²)^{1/4} (ONE Majorana). ‖ξ‖² (no ½) was the factor-2 Dirac bug.
    L, V = 4, 4 ** 4
    msq = 0.04
    rng = np.random.default_rng(33)
    h = torch.tensor(rng.standard_normal((V, 4, 4)))
    eo = st.eo_tables(L, CPU)
    Ve = V // 2
    fwd, back = st.neighbor_tables(L, CPU)
    blocks = st.hopping_blocks(h, L, device=CPU, dtype=F64)
    lam = float(st.estimate_lambda_max(blocks, fwd, back, V, n_iter=300, seed=0))
    coeffs = st.make_rhmc_coeffs(1.3 * lam, msq, n_poles=18)

    gen = torch.Generator().manual_seed(0)
    xi = torch.randn(Ve, 8, dtype=F64, generator=gen)
    phi = st.eo_heatbath(xi, h, coeffs, msq, eo, fwd, back, L)
    psi = st.eo_multishift_cg(phi, blocks, eo, [msq], tol=1e-12, max_iter=8000)[..., 0, :, :]
    s_pf = float((phi * psi).sum())
    half_xi_norm = 0.5 * float((xi * xi).sum())
    assert abs(s_pf - half_xi_norm) / half_xi_norm < 0.03


@pytest.mark.slow
def test_eo_samples_one_majorana_flavor_power():
    # FLAVOR-COUNT REGRESSION GUARD (would have caught the 2026-07-01 factor-2 bug):
    # the heatbath-averaged MD fermion force ⟨F_eo_ferm⟩ = p·∂logdet(M_e+m²) with p = the
    # sampled determinant power. Intended weight det(M_e+m²)^{1/2}=det(A†A+m²)^{1/4} ⟹ p=1/2
    # (ONE Majorana). The pre-fix engine (heatbath missing 1/√2) gave p≈1 (Dirac). Exact
    # reference: dense-logdet finite-diff at L=2.
    L, V = 2, 2 ** 4; Ve = V // 2
    msq = 0.04
    fwd, back = st.neighbor_tables(L, CPU); eo = st.eo_tables(L, CPU)
    gen = torch.Generator().manual_seed(4)
    h = 0.6 * torch.randn(V, 4, 4, dtype=F64, generator=gen)
    lam = float(st.estimate_lambda_max(st.hopping_blocks(h, L, device=CPU, dtype=F64), fwd, back, V))
    cm = st.make_rhmc_coeffs(lam, msq, n_poles=16)

    def logdet(hh):
        n = Ve * 8
        blk = st.hopping_blocks(hh, L, device=CPU, dtype=F64)
        cols = [st.apply_Me(torch.eye(n, dtype=F64)[i].reshape(Ve, 8), blk, eo, shift=msq).reshape(n) for i in range(n)]
        _, ld = torch.linalg.slogdet(torch.stack(cols, 1)); return float(ld)

    dirs = [torch.randn(V, 4, 4, dtype=F64, generator=gen) for _ in range(4)]
    dirs = [n / n.norm() for n in dirs]
    dd = 1e-5
    gld = [(logdet(h + dd * n) - logdet(h - dd * n)) / (2 * dd) for n in dirs]

    N = 400
    Ff = torch.zeros_like(h)
    for _ in range(N):
        phi = st.eo_heatbath(torch.randn(Ve, 8, dtype=F64, generator=gen), h, cm, msq, eo, fwd, back, L, tol=1e-10)
        Ff += st.eo_fermion_force(h, phi, msq, eo, fwd, back, L, tol=1e-10)
    Ff /= N
    ratios = [float((Ff * n).sum()) / gld[i] for i, n in enumerate(dirs) if abs(gld[i]) > 1e-6]
    p = float(np.mean(ratios))
    assert 0.35 < p < 0.65, f"sampled flavor power p={p:.3f}; expected ~0.5 (Majorana). p~1 = factor-2 Dirac bug."


def test_eo_force_equals_negative_action_gradient():
    # F = −∂S_eo/∂h, finite-differenced against the reference-independent eo_action.
    L, V, g = 4, 4 ** 4, 1.5
    msq = 0.04
    rng = np.random.default_rng(34)
    h = rng.standard_normal((V, 4, 4))
    eo = st.eo_tables(L, CPU)
    Ve = V // 2
    phi_e = torch.tensor(rng.standard_normal((Ve, 8)))
    fwd, back = st.neighbor_tables(L, CPU)

    F = st.eo_compute_force(torch.tensor(h), phi_e, g, msq, eo, fwd, back, L,
                            tol=1e-12, max_iter=8000).numpy()

    def action(hh):
        return float(st.eo_action(torch.tensor(hh), phi_e, g, msq, eo, fwd, back, L,
                                  tol=1e-12, max_iter=8000))

    eps = 1e-5
    for (x, mu, a) in [(0, 0, 0), (5, 2, 1), (17, 1, 3), (40, 3, 2)]:
        hp = h.copy(); hp[x, mu, a] += eps
        hm = h.copy(); hm[x, mu, a] -= eps
        fd = -(action(hp) - action(hm)) / (2 * eps)
        assert abs(F[x, mu, a] - fd) <= 1e-4 * max(1.0, abs(fd)), (x, mu, a, F[x, mu, a], fd)


def test_cg_shifted_per_shift_distinct_rhs():
    # The refinement primitive: each shift carries its OWN rhs (unlike multishift's
    # shared b). Batched-shifted CG must solve (A†A+σ_k) x_k = rhs_k per k.
    L, V = 2, 2 ** 4
    rng = np.random.default_rng(20)
    h = rng.standard_normal((V, 4, 4))
    shifts = np.array([0.5, 1.0, 3.0])
    rhs = rng.standard_normal((len(shifts), V, 8))            # DISTINCT per shift

    A = _dense(h, L)
    AtA = -A @ A
    eye = np.eye(8 * V)
    expected = np.stack([np.linalg.solve(AtA + s * eye, rhs[k].reshape(-1))
                         for k, s in enumerate(shifts)])       # (K, 8V)

    fwd, back = st.neighbor_tables(L, CPU)
    blocks = st.hopping_blocks(torch.tensor(h), L, device=CPU, dtype=F64)
    blocks_k = blocks.unsqueeze(0)                            # (1, V, 4, 8, 8) broadcast over K
    sigma = torch.tensor(shifts).reshape(-1, 1, 1)            # (K, 1, 1)
    x = st._cg_shifted(torch.tensor(rhs), blocks_k, fwd, back, sigma, tol=1e-10, max_iter=4000)

    assert x.shape == (len(shifts), V, 8)
    for k in range(len(shifts)):
        assert np.allclose(x[k].reshape(-1).numpy(), expected[k], atol=1e-6)


def test_multishift_cg_refined_matches_fp64_with_fp32_inner():
    # Core certification: FP32 inner solves + FP64 residual refinement reproduce the
    # pure-FP64 multishift solution to ~1e-8, including the ill-conditioned small shift
    # (the one that drives the cost). device=CPU runs the inner solve in FP32 on CPU,
    # exercising the precision mix without needing MPS.
    L, V = 3, 3 ** 4
    rng = np.random.default_rng(21)
    h = rng.standard_normal((V, 4, 4))
    b = rng.standard_normal((V, 8))
    shifts = np.array([0.01, 0.05, 0.3, 1.0, 4.0, 20.0])      # small shift = ill-conditioned

    h64 = torch.tensor(h)
    b64 = torch.tensor(b)
    fwd, back = st.neighbor_tables(L, CPU)
    blocks = st.hopping_blocks(h64, L, device=CPU, dtype=F64)
    x_fp64 = st.multishift_cg(b64, blocks, fwd, back, torch.tensor(shifts), tol=1e-12, max_iter=8000)

    x_ref = st.multishift_cg_refined(b64, h64, torch.tensor(shifts), fwd, back, fwd, back, L, CPU,
                                     tol=1e-10, inner_tol=3e-4, max_outer=20, max_inner=8000)

    assert x_ref.dtype == torch.float64 and x_ref.shape == x_fp64.shape
    assert torch.allclose(x_ref, x_fp64, atol=1e-8, rtol=1e-6), \
        float((x_ref - x_fp64).abs().max())


def test_refined_action_matches_fp64_action():
    # Integration: action via the refined solver matches the pure-FP64 action to ~1e-7
    # ⟹ the accept/reject ΔH is FP64-exact ⟹ no bias (the property the chain needs).
    L, V, g = 3, 3 ** 4, 1.5
    rng = np.random.default_rng(22)
    h = torch.tensor(rng.standard_normal((V, 4, 4)))
    phi = torch.tensor(rng.standard_normal((V, 8)))
    msq = 0.01
    fwd, back = st.neighbor_tables(L, CPU)
    blocks = st.hopping_blocks(h, L, device=CPU, dtype=F64)
    lam = float(st.estimate_lambda_max(blocks, fwd, back, V, n_iter=300, seed=0))
    coeffs = st.make_rhmc_coeffs(1.3 * lam, msq, n_poles=14)
    al = torch.as_tensor(coeffs['alphas'], dtype=F64)
    be = torch.as_tensor(coeffs['betas'], dtype=F64) + msq
    a0 = float(coeffs['a0'])

    S_fp64 = float(st.action(h, phi, g, a0, al, be, fwd, back, L, tol=1e-12, max_iter=8000))
    S_ref = float(st.action_refined(h, phi, g, a0, al, be, fwd, back, fwd, back, L, CPU,
                                    tol=1e-10, inner_tol=3e-4, max_outer=20, max_inner=8000))

    assert abs(S_ref - S_fp64) < 1e-6 * max(1.0, abs(S_fp64)), (S_ref, S_fp64)


def test_refined_trajectory_matches_mixed_dH():
    # Certification (unit-scale): offloading the accept/reject solves to FP32-inner
    # refinement reproduces the pure-FP64 mixed trajectory's ΔH for identical RNG ⟹
    # identical Metropolis decisions ⟹ no bias. Same draw order (xi, pi, u) in both.
    L, V, B = 2, 2 ** 4, 3
    rng = np.random.default_rng(23)
    h0 = torch.tensor(rng.standard_normal((B, V, 4, 4)))
    fwd, back = st.neighbor_tables(L, CPU)
    lam = float(st.estimate_lambda_max(st.hopping_blocks(h0[0], L, device=CPU, dtype=F64),
                                       fwd, back, V, n_iter=200, seed=0))
    coeffs = st.make_rhmc_coeffs(1.3 * lam, 0.04, n_poles=12)
    kw = dict(coeffs=coeffs, fwd64=fwd, back64=back, fwd_dev=fwd, back_dev=back, L=L,
              eps=0.05, n_md=8, device=CPU)

    g1 = torch.Generator().manual_seed(7)
    _, dH_m, acc_m = st.rhmc_trajectory_mixed(h0.clone(), 1.5, 0.04, coeffs, fwd, back, fwd, back,
                                              L, 0.05, 8, CPU, g1, g1)
    g2 = torch.Generator().manual_seed(7)
    h_r, dH_r, acc_r = st.rhmc_trajectory_refined(h0.clone(), 1.5, 0.04, gen_dev=g2, gen_cpu=g2,
                                                  inner_tol=3e-4, max_outer=20, **kw)

    assert h_r.dtype == torch.float64 and h_r.shape == (B, V, 4, 4)
    assert torch.allclose(dH_m, dH_r, atol=1e-5, rtol=1e-4), (dH_m, dH_r)
    assert torch.equal(acc_m, acc_r)


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


def test_eo_mixed_trajectory_mechanics():
    # Mechanics of the even-odd mixed scheme (FP32 MD + FP64 accept/reject) — the
    # production-deployable eo path. Runs, returns FP64 configs, finite ΔH, boolean
    # accept, exact Metropolis (h_out is either the proposal or the old config).
    # (Device='cpu' exercises the precision mix; chain-level unbiasedness / Creutz=1
    # is the slow test test_creutz_identity_eo_mixed_chain_unbiased.)
    L, V, B = 2, 2 ** 4, 4
    Ve = V // 2
    rng = np.random.default_rng(21)
    h = torch.tensor(rng.standard_normal((B, V, 4, 4)))                # FP64
    fwd, back = st.neighbor_tables(L, CPU)
    eo = st.eo_tables(L, CPU)
    lam_max = float(st.estimate_lambda_max(st.hopping_blocks(h[0], L, device=CPU, dtype=F64),
                                           fwd, back, V, n_iter=200, seed=0))
    coeffs = st.make_rhmc_coeffs(1.3 * lam_max, 0.04, n_poles=12)
    gen = torch.Generator().manual_seed(0)

    for _ in range(3):
        h_prev = h.clone()
        h, dH, acc = st.eo_rhmc_trajectory_mixed(h, 1.5, 0.04, coeffs, eo, fwd, back, eo, fwd, back,
                                                 L, 0.05, 8, CPU, gen, gen)
        assert h.dtype == torch.float64 and h.shape == (B, V, 4, 4)
        assert dH.shape == (B,) and torch.isfinite(dH).all()
        assert acc.dtype == torch.bool and acc.shape == (B,)
        # exact Metropolis: rejected replicas retain the previous config bit-for-bit
        for b in range(B):
            if not bool(acc[b]):
                assert torch.equal(h[b], h_prev[b])


@pytest.mark.slow
def test_creutz_identity_eo_mixed_chain_unbiased():
    # Chain-level certification of the eo mixed-precision trajectory: FP32 MD + FP64
    # accept/reject must leave the chain UNBIASED ⟹ Creutz ⟨e^-ΔH⟩ = 1 within error.
    # Pairs with the L2/L4 identity proof (eo and full target det(M_e+m²)^{1/2}).
    L, V = 2, 2 ** 4
    Ve = V // 2
    g, msq = 1.5, 0.01
    fwd, back = st.neighbor_tables(L, CPU)
    eo = st.eo_tables(L, CPU)
    gen0 = torch.Generator().manual_seed(3)
    lam = float(st.estimate_lambda_max(st.hopping_blocks(1.7 * torch.randn(V, 4, 4, dtype=F64, generator=gen0), L,
                                                         device=CPU, dtype=F64), fwd, back, V))
    coeffs = st.make_rhmc_coeffs(1.3 * lam, msq, n_poles=12)
    gen = torch.Generator().manual_seed(5)
    h = 1.7 * torch.randn(V, 4, 4, dtype=F64, generator=gen)
    dHs, nacc, n = [], 0, 240
    for t in range(n):
        h, dH, acc = st.eo_rhmc_trajectory_mixed(h, g, msq, coeffs, eo, fwd, back, eo, fwd, back,
                                                 L, 0.05, 8, CPU, gen, gen, tol_md=1e-4, tol_acc=1e-10)
        if t >= n // 4:
            dHs.append(float(dH)); nacc += int(bool(acc))
    creutz = float(np.mean(np.exp(-np.array(dHs))))
    assert nacc / (n - n // 4) > 0.5 and abs(creutz - 1.0) < 0.08, (creutz, nacc / (n - n // 4))


# --- Hasenbusch mass-preconditioning (eo) --------------------------------------------------

def test_eo_ratio_force_equals_negative_action_gradient():
    # F_ratio = -dS_R/dh, central finite-difference vs the reference-independent eo_ratio_action.
    L, V = 2, 2 ** 4; Ve = V // 2
    msq, mu2 = 0.04, 0.15
    fwd, back = st.neighbor_tables(L, CPU); eo = st.eo_tables(L, CPU)
    gen = torch.Generator().manual_seed(1)
    h = 0.6 * torch.randn(V, 4, 4, dtype=F64, generator=gen)
    phi_R = torch.randn(Ve, 8, dtype=F64, generator=gen)
    F = st.eo_ratio_force(h, phi_R, msq, mu2, eo, fwd, back, L, tol=1e-12)
    d = 1e-5
    for _ in range(5):
        n = torch.randn(V, 4, 4, dtype=F64, generator=gen); n /= n.norm()
        Sp = float(st.eo_ratio_action(h + d * n, phi_R, msq, mu2, eo, fwd, back, L, tol=1e-12))
        Sm = float(st.eo_ratio_action(h - d * n, phi_R, msq, mu2, eo, fwd, back, L, tol=1e-12))
        fd = -(Sp - Sm) / (2 * d)
        assert abs(fd - float((F * n).sum())) < 1e-4 * (abs(fd) + 1e-9)


def test_eo_ratio_heatbath_consistency():
    # Ratio-PF heatbath convention with the real-PF 1/√2 (INV_SQRT2): S_R(phi_R) == ½||xi||^2
    # (the historically bug-prone step; the ½ is the one-Majorana normalization).
    L, V = 2, 2 ** 4; Ve = V // 2
    msq, mu2 = 0.04, 0.15
    fwd, back = st.neighbor_tables(L, CPU); eo = st.eo_tables(L, CPU)
    gen = torch.Generator().manual_seed(2)
    h = 0.6 * torch.randn(V, 4, 4, dtype=F64, generator=gen)
    lam = float(st.estimate_lambda_max(st.hopping_blocks(h, L, device=CPU, dtype=F64), fwd, back, V))
    cm = st.make_rhmc_coeffs(lam, msq, n_poles=16)
    cmu = st.make_rhmc_coeffs(lam, mu2, n_poles=16)
    for _ in range(5):
        xi = torch.randn(Ve, 8, dtype=F64, generator=gen)
        phi_R = st.eo_ratio_heatbath(xi, h, cm, cmu, msq, mu2, eo, fwd, back, L, tol=1e-12)
        S = float(st.eo_ratio_action(h, phi_R, msq, mu2, eo, fwd, back, L, tol=1e-12))
        half_xi_norm = 0.5 * float((xi * xi).sum())
        assert abs(S - half_xi_norm) < 3e-2 * half_xi_norm


def test_eo_hb_integrate_reversible():
    # Nested 2-timescale Omelyan must be exactly reversible: fwd -> flip pi -> fwd == start.
    L, V = 2, 2 ** 4; Ve = V // 2
    g, msq, mu2 = 1.5, 0.04, 0.20
    fwd, back = st.neighbor_tables(L, CPU); eo = st.eo_tables(L, CPU)
    gen = torch.Generator().manual_seed(4)
    h0 = 0.6 * torch.randn(V, 4, 4, dtype=F64, generator=gen)
    lam = float(st.estimate_lambda_max(st.hopping_blocks(h0, L, device=CPU, dtype=F64), fwd, back, V))
    cm = st.make_rhmc_coeffs(lam, msq, n_poles=16); cmu = st.make_rhmc_coeffs(lam, mu2, n_poles=16)
    phi_H = st.eo_heatbath(torch.randn(Ve, 8, dtype=F64, generator=gen), h0, cmu, mu2, eo, fwd, back, L, tol=1e-12)
    phi_R = st.eo_ratio_heatbath(torch.randn(Ve, 8, dtype=F64, generator=gen), h0, cm, cmu, msq, mu2, eo, fwd, back, L, tol=1e-12)
    pi0 = torch.randn(V, 4, 4, dtype=F64, generator=gen)
    ff = lambda hh: st.eo_compute_force(hh, phi_H, g, mu2, eo, fwd, back, L, tol=1e-12)
    fs = lambda hh: st.eo_ratio_force(hh, phi_R, msq, mu2, eo, fwd, back, L, tol=1e-12)
    h1, p1 = st.eo_hb_integrate(h0, pi0, fs, ff, 0.1, 5, 4)
    h2, _ = st.eo_hb_integrate(h1, -p1, fs, ff, 0.1, 5, 4)
    assert float((h2 - h0).abs().max()) < 1e-9


@pytest.mark.slow
def test_creutz_identity_eo_hb_chain_unbiased():
    # The Hasenbusch 2-timescale trajectory must be an UNBIASED HMC on its (proven-identical)
    # target: Creutz <e^-dH> = 1 within error over a chain.
    L, V = 2, 2 ** 4; Ve = V // 2
    g, msq, mu2 = 1.5, 0.04, 0.20
    fwd, back = st.neighbor_tables(L, CPU); eo = st.eo_tables(L, CPU)
    gen = torch.Generator().manual_seed(4)
    h0 = 0.6 * torch.randn(V, 4, 4, dtype=F64, generator=gen)
    lam = float(st.estimate_lambda_max(st.hopping_blocks(h0, L, device=CPU, dtype=F64), fwd, back, V))
    cm = st.make_rhmc_coeffs(lam, msq, n_poles=16); cmu = st.make_rhmc_coeffs(lam, mu2, n_poles=16)
    gc = torch.Generator().manual_seed(7)
    h = 0.3 * torch.randn(V, 4, 4, dtype=F64, generator=gc)
    dHs, nacc, n = [], 0, 200
    for t in range(n):
        h, dH, a = st.eo_hb_trajectory(h, g, msq, mu2, cm, cmu, eo, fwd, back, L, 0.1, 5, 4, gc,
                                       tol_md=1e-4, tol_acc=1e-10)
        if t >= n // 4:
            dHs.append(float(dH)); nacc += int(bool(a))
    creutz = float(np.mean(np.exp(-np.array(dHs))))
    assert nacc / (n - n // 4) > 0.5 and abs(creutz - 1.0) < 0.08, (creutz, nacc / (n - n // 4))
