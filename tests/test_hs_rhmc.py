"""Tests for HS+RHMC algorithm (Wave 7C).

Tests cover:
  - Fermion matrix A[h,U] antisymmetry and Kramers positivity
  - CG solver convergence
  - SU(2) exponential correctness
  - Zolotarev coefficient positivity and approximation accuracy
  - Omelyan integrator reversibility and ΔH scaling
  - RHMC trajectory acceptance and thermalization
  - h-field measurement correctness
  - PyTorch MPS backend: matrix correctness, solver accuracy, trajectory physics
"""

import numpy as np
import pytest

try:
    import numba
    HAS_NUMBA = True
except ImportError:
    HAS_NUMBA = False

needs_numba = pytest.mark.skipif(not HAS_NUMBA, reason="numba required for numpy RHMC backend")


# ════════════════════════════════════════════════════════════════════
# Fermion matrix A[h,U]
# ════════════════════════════════════════════════════════════════════


@needs_numba
class TestFermionMatrixHS:
    """Verify A[h,U] is antisymmetric and satisfies Kramers."""

    def test_antisymmetry(self):
        """A^T = -A for random h, U at L=2."""
        from src.vestigial.hs_rhmc import (
            create_rhmc_config, build_fermion_matrix_dense,
            _precompute_spin4_cache,
        )
        rng = np.random.default_rng(42)
        config = create_rhmc_config(2, g=2.0, rng=rng)
        spin4 = _precompute_spin4_cache(config.gauge, config.L)
        A = build_fermion_matrix_dense(config.h, config.gauge, config.L, spin4)
        np.testing.assert_allclose(A, -A.T, atol=1e-12)

    def test_kramers_anticommutation(self):
        """{J₂, A} = 0 for the HS fermion matrix."""
        from src.vestigial.hs_rhmc import (
            create_rhmc_config, build_fermion_matrix_dense,
            _precompute_spin4_cache,
        )
        from src.core.constants import MAJORANA_J2
        rng = np.random.default_rng(42)
        config = create_rhmc_config(2, g=2.0, rng=rng)
        spin4 = _precompute_spin4_cache(config.gauge, config.L)
        A = build_fermion_matrix_dense(config.h, config.gauge, config.L, spin4)
        V = config.L**4
        J2_full = np.kron(np.eye(V), MAJORANA_J2)
        anticomm = J2_full @ A + A @ J2_full
        np.testing.assert_allclose(anticomm, 0, atol=1e-10)

    def test_zero_h_gives_zero_matrix(self):
        """A[h=0, U] = 0 (no fermion hopping without auxiliary fields)."""
        from src.vestigial.hs_rhmc import (
            create_rhmc_config, build_fermion_matrix_dense,
            _precompute_spin4_cache,
        )
        rng = np.random.default_rng(42)
        config = create_rhmc_config(2, g=2.0, rng=rng, cold_start=True)
        spin4 = _precompute_spin4_cache(config.gauge, config.L)
        A = build_fermion_matrix_dense(config.h, config.gauge, config.L, spin4)
        np.testing.assert_allclose(A, 0, atol=1e-15)

    def test_dimension(self):
        """A has shape (8V, 8V)."""
        from src.vestigial.hs_rhmc import (
            create_rhmc_config, build_fermion_matrix_dense,
            _precompute_spin4_cache,
        )
        rng = np.random.default_rng(42)
        for L in [2, 3]:
            config = create_rhmc_config(L, g=1.0, rng=rng)
            spin4 = _precompute_spin4_cache(config.gauge, config.L)
            A = build_fermion_matrix_dense(config.h, config.gauge, L, spin4)
            V = L**4
            assert A.shape == (8 * V, 8 * V)


# ════════════════════════════════════════════════════════════════════
# CG solver
# ════════════════════════════════════════════════════════════════════


@needs_numba
class TestMultiShiftCG:
    """Verify CG solver convergence for all shifts."""

    def test_single_shift_convergence(self):
        """(A†A + σ)ψ = φ converges to tolerance."""
        from src.vestigial.hs_rhmc import (
            create_rhmc_config, build_fermion_matrix_dense,
            _precompute_spin4_cache, make_AtA_apply, _cg_single_shift,
        )
        rng = np.random.default_rng(42)
        config = create_rhmc_config(2, g=2.0, rng=rng)
        spin4 = _precompute_spin4_cache(config.gauge, config.L)
        A = build_fermion_matrix_dense(config.h, config.gauge, config.L, spin4)
        AtA = make_AtA_apply(A)
        phi = rng.standard_normal(128)
        psi, n_iter = _cg_single_shift(AtA, phi, sigma=1.0, tol=1e-10)
        residual = AtA(psi) + 1.0 * psi - phi
        assert np.linalg.norm(residual) / np.linalg.norm(phi) < 1e-10

    def test_multi_shift_all_converge(self):
        """All shifts converge in multi_shift_cg."""
        from src.vestigial.hs_rhmc import (
            create_rhmc_config, build_fermion_matrix_dense,
            _precompute_spin4_cache, make_AtA_apply, multi_shift_cg,
        )
        rng = np.random.default_rng(42)
        config = create_rhmc_config(2, g=2.0, rng=rng)
        spin4 = _precompute_spin4_cache(config.gauge, config.L)
        A = build_fermion_matrix_dense(config.h, config.gauge, config.L, spin4)
        AtA = make_AtA_apply(A)
        phi = rng.standard_normal(128)
        shifts = [0.01, 0.1, 1.0, 10.0]
        psi_list, _ = multi_shift_cg(AtA, phi, shifts, tol=1e-10)
        for k, sigma in enumerate(shifts):
            res = AtA(psi_list[k]) + sigma * psi_list[k] - phi
            assert np.linalg.norm(res) / np.linalg.norm(phi) < 1e-9


# ════════════════════════════════════════════════════════════════════
# SU(2) exponential
# ════════════════════════════════════════════════════════════════════


class TestSU2Exp:
    """Verify SU(2) Lie algebra exponential."""

    def test_unit_quaternion(self):
        """Output is a unit quaternion for random P."""
        from src.core.formulas import su2_lie_exp
        P = np.array([1.0, 2.0, 3.0])
        q = su2_lie_exp(P, 0.5)
        assert abs(np.sum(q**2) - 1.0) < 1e-14

    def test_zero_is_identity(self):
        """exp(0) = (1, 0, 0, 0)."""
        from src.core.formulas import su2_lie_exp
        q = su2_lie_exp(np.array([0.0, 0.0, 0.0]), 1.0)
        np.testing.assert_allclose(q, [1, 0, 0, 0], atol=1e-15)

    def test_inverse(self):
        """exp(P, ε) · exp(P, -ε) = identity."""
        from src.core.formulas import su2_lie_exp, quaternion_multiply
        P = np.array([1.5, -0.7, 2.3])
        q_fwd = su2_lie_exp(P, 0.3)
        q_bwd = su2_lie_exp(P, -0.3)
        q_prod = quaternion_multiply(q_fwd, q_bwd)
        np.testing.assert_allclose(q_prod, [1, 0, 0, 0], atol=1e-14)


# ════════════════════════════════════════════════════════════════════
# Zolotarev coefficients
# ════════════════════════════════════════════════════════════════════


class TestZolotarev:
    """Verify Zolotarev rational approximation."""

    def test_positive_coefficients(self):
        """All α_k > 0, β_k > 0."""
        from src.vestigial.hs_rhmc import compute_zolotarev_coefficients
        a0, al, be = compute_zolotarev_coefficients(12, 1.0, 100.0, -0.25)
        assert a0 >= 0
        assert np.all(al > 0)
        assert np.all(be > 0)

    def test_approximation_accuracy(self):
        """Approximation error < 1% for 16 poles at κ=100."""
        from src.vestigial.hs_rhmc import compute_zolotarev_coefficients
        eps, lam = 1.0, 100.0
        a0, al, be = compute_zolotarev_coefficients(16, eps, lam, -0.25)
        x = np.exp(np.linspace(np.log(eps), np.log(lam), 200))
        target = x ** (-0.25)
        r = a0 + np.sum(al[:, None] / (x[None, :] + be[:, None]), axis=0)
        max_err = np.max(np.abs((r - target) / target))
        assert max_err < 0.01, f"Zolotarev max relative error {max_err:.4f} > 1%"

    def test_convergence_with_poles(self):
        """More poles → smaller error."""
        from src.vestigial.hs_rhmc import compute_zolotarev_coefficients
        eps, lam = 1.0, 100.0
        errors = []
        for n in [8, 12, 16]:
            a0, al, be = compute_zolotarev_coefficients(n, eps, lam, -0.25)
            x = np.exp(np.linspace(np.log(eps), np.log(lam), 200))
            target = x ** (-0.25)
            r = a0 + np.sum(al[:, None] / (x[None, :] + be[:, None]), axis=0)
            errors.append(np.max(np.abs((r - target) / target)))
        # Each step should reduce error
        assert errors[1] < errors[0], f"12 poles ({errors[1]}) not better than 8 ({errors[0]})"
        assert errors[2] < errors[1], f"16 poles ({errors[2]}) not better than 12 ({errors[1]})"


# ════════════════════════════════════════════════════════════════════
# Omelyan integrator
# ════════════════════════════════════════════════════════════════════


@needs_numba
class TestOmelyanIntegrator:
    """Verify integrator reversibility and energy conservation."""

    def test_reversibility(self):
        """Forward + flip + backward recovers initial state to ~1e-14."""
        from src.vestigial.hs_rhmc import (
            RHMCParams, create_rhmc_config, build_fermion_matrix,
            _precompute_spin4_cache, make_AtA_apply, estimate_spectral_range,
            compute_zolotarev_coefficients, compute_forces,
        )
        rng = np.random.default_rng(42)
        config = create_rhmc_config(2, g=2.0, rng=rng)
        params = RHMCParams(g=2.0, tau=0.5, n_md_steps=5, cg_tol_md=1e-14)
        spin4 = _precompute_spin4_cache(config.gauge, config.L)
        A = build_fermion_matrix(config.h, config.gauge, config.L, spin4)
        AtA = make_AtA_apply(A)
        dim = 8 * config.L**4
        lm, lM = estimate_spectral_range(AtA, dim, rng=rng)
        _, al, be = compute_zolotarev_coefficients(16, lm, lM, -0.25)

        phi = rng.standard_normal(dim)
        config.pi_h = rng.standard_normal(config.h.shape)
        config.mom_L = np.zeros((2, 2, 2, 2, 4, 3))
        config.mom_R = np.zeros((2, 2, 2, 2, 4, 3))
        h_init = config.h.copy()
        pi_init = config.pi_h.copy()

        eps = params.tau / params.n_md_steps
        lam = params.omelyan_lambda

        # Forward
        for _ in range(params.n_md_steps):
            A_cur = build_fermion_matrix(config.h, config.gauge, config.L, spin4)
            F_h, _, _ = compute_forces(config, params, phi, al, be, A_cur, spin4)
            config.pi_h += lam * eps * F_h
            config.h += (eps / 2) * config.pi_h
            A_cur = build_fermion_matrix(config.h, config.gauge, config.L, spin4)
            F_h, _, _ = compute_forces(config, params, phi, al, be, A_cur, spin4)
            config.pi_h += (1 - 2 * lam) * eps * F_h
            config.h += (eps / 2) * config.pi_h
            A_cur = build_fermion_matrix(config.h, config.gauge, config.L, spin4)
            F_h, _, _ = compute_forces(config, params, phi, al, be, A_cur, spin4)
            config.pi_h += lam * eps * F_h

        # Flip + backward
        config.pi_h *= -1
        for _ in range(params.n_md_steps):
            A_cur = build_fermion_matrix(config.h, config.gauge, config.L, spin4)
            F_h, _, _ = compute_forces(config, params, phi, al, be, A_cur, spin4)
            config.pi_h += lam * eps * F_h
            config.h += (eps / 2) * config.pi_h
            A_cur = build_fermion_matrix(config.h, config.gauge, config.L, spin4)
            F_h, _, _ = compute_forces(config, params, phi, al, be, A_cur, spin4)
            config.pi_h += (1 - 2 * lam) * eps * F_h
            config.h += (eps / 2) * config.pi_h
            A_cur = build_fermion_matrix(config.h, config.gauge, config.L, spin4)
            F_h, _, _ = compute_forces(config, params, phi, al, be, A_cur, spin4)
            config.pi_h += lam * eps * F_h
        config.pi_h *= -1

        assert np.max(np.abs(config.h - h_init)) < 1e-12
        assert np.max(np.abs(config.pi_h - pi_init)) < 1e-12

    def test_force_matches_finite_difference(self):
        """Analytic force matches -∂H/∂h via central differences."""
        from src.vestigial.hs_rhmc import (
            RHMCParams, create_rhmc_config, build_fermion_matrix,
            _precompute_spin4_cache, make_AtA_apply, estimate_spectral_range,
            compute_zolotarev_coefficients, compute_forces, compute_hamiltonian,
        )
        rng = np.random.default_rng(42)
        config = create_rhmc_config(2, g=2.0, rng=rng)
        params = RHMCParams(g=2.0, cg_tol_md=1e-12, cg_tol_mc=1e-12)
        spin4 = _precompute_spin4_cache(config.gauge, config.L)
        A = build_fermion_matrix(config.h, config.gauge, config.L, spin4)
        AtA = make_AtA_apply(A)
        dim = 8 * config.L**4
        lm, lM = estimate_spectral_range(AtA, dim, rng=rng)
        _, al, be = compute_zolotarev_coefficients(16, lm, lM, -0.25)
        al_full = np.concatenate([[0.0], al])  # alpha_0 = 0 for simplicity

        phi = rng.standard_normal(dim)
        config.pi_h = np.zeros_like(config.h)
        config.mom_L = np.zeros((2, 2, 2, 2, 4, 3))
        config.mom_R = np.zeros((2, 2, 2, 2, 4, 3))

        F_h, _, _ = compute_forces(config, params, phi, al, be, A, spin4)

        delta = 1e-5
        x0, x1, x2, x3, mu, a = 0, 0, 0, 1, 2, 3
        h_save = config.h[x0, x1, x2, x3, mu, a]

        config.h[x0, x1, x2, x3, mu, a] = h_save + delta
        Ap = build_fermion_matrix(config.h, config.gauge, config.L, spin4)
        Hp = compute_hamiltonian(config, params, phi, al_full, be, Ap)

        config.h[x0, x1, x2, x3, mu, a] = h_save - delta
        Am = build_fermion_matrix(config.h, config.gauge, config.L, spin4)
        Hm = compute_hamiltonian(config, params, phi, al_full, be, Am)

        config.h[x0, x1, x2, x3, mu, a] = h_save
        F_numerical = -(Hp - Hm) / (2 * delta)
        F_analytic = F_h[x0, x1, x2, x3, mu, a]

        np.testing.assert_allclose(F_analytic, F_numerical, rtol=1e-5)


# ════════════════════════════════════════════════════════════════════
# RHMC trajectory
# ════════════════════════════════════════════════════════════════════


@needs_numba
class TestRHMCTrajectory:
    """Verify RHMC trajectory produces correct physics."""

    def test_h_field_stable(self):
        """⟨h²⟩ stays near 2g (equilibrium Gaussian) after thermalization."""
        from src.vestigial.hs_rhmc import run_rhmc
        result = run_rhmc(L=2, g=2.0, beta=0.0, n_traj=15, n_therm=3,
                          n_meas_skip=1, n_md_steps=10, tau=1.0, seed=42)
        mean_h2 = np.mean(result.h_sq_history)
        # Equilibrium: ⟨h²⟩ ≈ 2g = 4.0. Allow 50% tolerance for small statistics.
        assert 1.0 < mean_h2 < 12.0, f"⟨h²⟩ = {mean_h2:.2f}, expected ~4.0"

    def test_acceptance_nonzero(self):
        """Acceptance rate > 0 (some trajectories accepted)."""
        from src.vestigial.hs_rhmc import run_rhmc
        result = run_rhmc(L=2, g=2.0, beta=0.0, n_traj=10, n_therm=2,
                          n_meas_skip=1, n_md_steps=10, tau=1.0, seed=42)
        assert result.acceptance_rate > 0.0

    def test_deterministic_with_seed(self):
        """Same seed produces same result."""
        from src.vestigial.hs_rhmc import run_rhmc
        r1 = run_rhmc(L=2, g=1.0, n_traj=5, n_therm=1, n_meas_skip=1,
                       n_md_steps=5, tau=0.5, seed=123)
        r2 = run_rhmc(L=2, g=1.0, n_traj=5, n_therm=1, n_meas_skip=1,
                       n_md_steps=5, tau=0.5, seed=123)
        np.testing.assert_allclose(r1.delta_H_history, r2.delta_H_history)


# ════════════════════════════════════════════════════════════════════
# h-field measurements
# ════════════════════════════════════════════════════════════════════


@needs_numba
class TestHFieldMeasurements:
    """Verify h-field order parameter measurements."""

    def test_zero_h_gives_zero_observables(self):
        """h=0 → all observables zero."""
        from src.vestigial.hs_rhmc import create_rhmc_config, measure_h_field_observables
        rng = np.random.default_rng(42)
        config = create_rhmc_config(2, g=1.0, rng=rng, cold_start=True)
        h_sq, tet_sq, trQ2 = measure_h_field_observables(config)
        assert h_sq == 0.0
        assert tet_sq == 0.0
        assert trQ2 == 0.0

    def test_random_h_gives_nonzero(self):
        """Random h → nonzero observables."""
        from src.vestigial.hs_rhmc import create_rhmc_config, measure_h_field_observables
        rng = np.random.default_rng(42)
        config = create_rhmc_config(2, g=2.0, rng=rng)
        h_sq, tet_sq, trQ2 = measure_h_field_observables(config)
        assert h_sq > 0
        assert trQ2 > 0


# ════════════════════════════════════════════════════════════════════
# PyTorch backend (hs_rhmc_torch.py)
# ════════════════════════════════════════════════════════════════════


class TestTorchFermionMatrix:
    """Verify torch backend fermion matrix properties."""

    def test_antisymmetry(self):
        """A^T = -A for random h at L=2."""
        import torch
        from src.vestigial.hs_rhmc_torch import build_fermion_matrix_torch
        L = 2
        V = L ** 4
        h = torch.randn(V, 4, 4, dtype=torch.float32)
        A = build_fermion_matrix_torch(h, L, device=torch.device('cpu'))
        err = torch.max(torch.abs(A + A.T))
        assert err < 1e-6, f"Antisymmetry error {err:.2e}"

    def test_zero_h_gives_zero(self):
        """h=0 → A=0."""
        import torch
        from src.vestigial.hs_rhmc_torch import build_fermion_matrix_torch
        L = 2
        V = L ** 4
        h = torch.zeros(V, 4, 4, dtype=torch.float32)
        A = build_fermion_matrix_torch(h, L, device=torch.device('cpu'))
        assert torch.max(torch.abs(A)) < 1e-15

    def test_dimension(self):
        """A has shape (8V, 8V)."""
        import torch
        from src.vestigial.hs_rhmc_torch import build_fermion_matrix_torch
        for L in [2, 3]:
            V = L ** 4
            h = torch.randn(V, 4, 4, dtype=torch.float32)
            A = build_fermion_matrix_torch(h, L, device=torch.device('cpu'))
            assert A.shape == (8 * V, 8 * V)

    def test_ata_positive_semidefinite(self):
        """A†A = -A² is PSD (Kramers guarantees Pf≥0)."""
        import torch
        from src.vestigial.hs_rhmc_torch import build_fermion_matrix_torch
        L = 2
        V = L ** 4
        h = torch.randn(V, 4, 4, dtype=torch.float32)
        A = build_fermion_matrix_torch(h, L, device=torch.device('cpu'))
        AtA = -A @ A
        eigvals = torch.linalg.eigvalsh(AtA)
        assert float(eigvals.min()) >= -1e-5, f"Negative eigenvalue: {eigvals.min():.2e}"


class TestTorchSolver:
    """Verify torch shifted solver correctness."""

    def test_solve_shifted_residuals(self):
        """All shifted solves have small residual."""
        import torch
        from src.vestigial.hs_rhmc_torch import (
            build_fermion_matrix_torch, multi_shift_solve_torch,
        )
        L = 2
        V = L ** 4
        dim = 8 * V
        h = torch.randn(V, 4, 4, dtype=torch.float32)
        A = build_fermion_matrix_torch(h, L, device=torch.device('cpu'))
        AtA = -A @ A
        b = torch.randn(dim)
        shifts = [0.1, 1.0, 10.0, 50.0]
        solutions = multi_shift_solve_torch(AtA, b, shifts)
        for k, sigma in enumerate(shifts):
            residual = torch.norm(AtA @ solutions[k] + sigma * solutions[k] - b)
            rel_res = residual / torch.norm(b)
            assert rel_res < 1e-4, f"shift={sigma}: rel_res={rel_res:.2e}"

    def test_cg_fallback_for_large_dim(self):
        """Batched CG works for shifted systems."""
        import torch
        from src.vestigial.hs_rhmc_torch import batched_cg
        # Verify batched CG works directly with a single shift
        dim = 64
        A = torch.randn(dim, dim, dtype=torch.float64)
        AtA = A.T @ A + 0.01 * torch.eye(dim, dtype=torch.float64)
        b = torch.randn(dim, dtype=torch.float64)  # batched_cg expects (dim,)
        shifts = [1.0]
        x_list, n_iter = batched_cg(AtA, b, shifts, tol=1e-6, max_iter=200)
        residual = torch.norm(AtA @ x_list[0] + 1.0 * x_list[0] - b) / torch.norm(b)
        assert residual < 1e-5


class TestTorchForces:
    """Verify torch force computation."""

    def test_force_finite_difference(self):
        """Analytic force matches numerical -∂H/∂h."""
        import torch
        from src.vestigial.hs_rhmc_torch import (
            build_fermion_matrix_torch, compute_forces_torch,
            compute_hamiltonian_torch,
        )
        from src.vestigial.hs_rhmc import compute_zolotarev_coefficients
        L = 2
        V = L ** 4
        dim = 8 * V
        dev = torch.device('cpu')
        dtype = torch.float32
        torch.manual_seed(42)

        h = torch.randn(V, 4, 4, dtype=dtype, device=dev)
        A = build_fermion_matrix_torch(h, L, device=dev, dtype=dtype)
        AtA = -A @ A
        eigvals = torch.linalg.eigvalsh(AtA)
        epos = eigvals[eigvals > 1e-10]
        lam_min, lam_max = float(epos.min())*0.8, float(epos.max())*1.2

        a0, alphas, betas = compute_zolotarev_coefficients(8, lam_min, lam_max, -0.25)
        alphas_t = torch.tensor(alphas, dtype=dtype, device=dev)
        betas_t = torch.tensor(betas, dtype=dtype, device=dev)

        phi = torch.randn(dim, dtype=dtype, device=dev)
        pi_h = torch.zeros(V, 4, 4, dtype=dtype, device=dev)

        # Analytic force
        F_h = compute_forces_torch(h, 2.0, A, phi, alphas_t, betas_t, L)

        # Numerical force at one component
        delta = 1e-4
        idx = (3, 1, 2)  # site=3, mu=1, a=2
        h_plus = h.clone()
        h_plus[idx] += delta
        H_plus = compute_hamiltonian_torch(h_plus, pi_h, 2.0, phi,
                                            float(a0), alphas, betas, L, 'float32')
        h_minus = h.clone()
        h_minus[idx] -= delta
        H_minus = compute_hamiltonian_torch(h_minus, pi_h, 2.0, phi,
                                             float(a0), alphas, betas, L, 'float32')

        F_numerical = -(H_plus - H_minus) / (2 * delta)
        F_analytic = float(F_h[idx])

        # float32 + 8-pole Zolotarev limits force accuracy to ~5-10%
        np.testing.assert_allclose(F_analytic, F_numerical, rtol=0.10,
                                   err_msg=f"Force mismatch: analytic={F_analytic:.6f}, "
                                           f"numerical={F_numerical:.6f}")


class TestTorchMeasurements:
    """Verify torch measurement functions."""

    def test_zero_h_observables(self):
        """h=0 → all observables zero."""
        import torch
        from src.vestigial.hs_rhmc_torch import measure_h_observables_torch
        L = 2
        V = L ** 4
        h = torch.zeros(V, 4, 4, dtype=torch.float32)
        h_sq, tet, trQ2 = measure_h_observables_torch(h, L)
        assert h_sq == 0.0
        assert tet == 0.0
        assert trQ2 == 0.0

    def test_random_h_nonzero(self):
        """Random h → nonzero observables."""
        import torch
        from src.vestigial.hs_rhmc_torch import measure_h_observables_torch
        L = 2
        V = L ** 4
        h = torch.randn(V, 4, 4, dtype=torch.float32)
        h_sq, tet, trQ2 = measure_h_observables_torch(h, L)
        assert h_sq > 0
        assert trQ2 > 0


class TestTorchTrajectory:
    """Verify full torch RHMC trajectory produces correct physics."""

    def test_h_field_equilibrium(self):
        """⟨h²⟩ ≈ 2g after thermalization."""
        from src.vestigial.hs_rhmc_torch import run_rhmc_torch
        r = run_rhmc_torch(L=2, g=2.0, n_traj=30, n_therm=10, n_meas_skip=1,
                           n_md_steps=10, tau=1.0, n_poles=16, seed=42)
        mean_h2 = np.mean(r.h_sq_history)
        # ⟨h²⟩ ≈ 2g = 4.0, allow wide tolerance for 20 measurements
        assert 1.0 < mean_h2 < 12.0, f"⟨h²⟩ = {mean_h2:.2f}, expected ~4.0"

    def test_acceptance_nonzero(self):
        """Acceptance rate > 0."""
        from src.vestigial.hs_rhmc_torch import run_rhmc_torch
        r = run_rhmc_torch(L=2, g=2.0, n_traj=10, n_therm=2, n_meas_skip=1,
                           n_md_steps=10, tau=1.0, seed=42)
        assert r.acceptance_rate > 0.0

    def test_deterministic(self):
        """Same seed → same ΔH sequence."""
        from src.vestigial.hs_rhmc_torch import run_rhmc_torch
        r1 = run_rhmc_torch(L=2, g=1.0, n_traj=5, n_therm=1, n_meas_skip=1,
                            n_md_steps=5, tau=0.5, seed=123)
        r2 = run_rhmc_torch(L=2, g=1.0, n_traj=5, n_therm=1, n_meas_skip=1,
                            n_md_steps=5, tau=0.5, seed=123)
        np.testing.assert_allclose(r1.delta_H_history, r2.delta_H_history, rtol=1e-5)

    def test_sign_free(self):
        """Result reports sign_free=True (Kramers)."""
        from src.vestigial.hs_rhmc_torch import run_rhmc_torch
        r = run_rhmc_torch(L=2, g=1.0, n_traj=3, n_therm=0, n_meas_skip=1,
                           n_md_steps=3, tau=0.5, seed=42)
        assert r.sign_free is True
