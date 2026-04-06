"""Tests for matrix-free staggered Dirac operator (stencil_dirac.py).

Verifies that the torch.roll()-based matrix-free operator produces identical
results to the dense matrix construction in hs_rhmc_torch.py. This is the
critical validation for Phase 5g Wave 1: matrix-free CG enabling L=12+ RHMC.

Key invariants tested:
- Matrix-free A@v matches dense A@v to machine precision (< 1e-13)
- Matrix-free AtA@v matches dense AtA@v to machine precision
- AtA is positive semidefinite (all eigenvalues >= 0)
- Antisymmetry: A^T = -A (verified via inner product identity)
- CG convergence is identical with matrix-free operator
"""

import pytest
import torch
import numpy as np

from src.vestigial.stencil_dirac import (
    precompute_blocks,
    apply_fermion_matrix,
    apply_AtA,
    verify_against_dense,
    make_cg_operator,
    _CG_np,
)
from src.vestigial.hs_rhmc_torch import build_fermion_matrix_torch


# Use CPU float64 for all verification (maximum precision)
DEVICE = torch.device('cpu')
DTYPE = torch.float64
CG = torch.tensor(_CG_np, dtype=DTYPE, device=DEVICE)


def _random_h_field(L, seed=42):
    """Generate random h-field for testing."""
    rng = np.random.default_rng(seed)
    V = L ** 4
    return rng.standard_normal((V, 4, 4))


class TestPrecomputeBlocks:
    """Test block precomputation."""

    def test_shape_L4(self):
        h = torch.tensor(_random_h_field(4), dtype=DTYPE, device=DEVICE)
        blocks = precompute_blocks(h, CG, 4)
        assert blocks.shape == (4, 4, 4, 4, 4, 8, 8)

    def test_shape_L2(self):
        h = torch.tensor(_random_h_field(2), dtype=DTYPE, device=DEVICE)
        blocks = precompute_blocks(h, CG, 2)
        assert blocks.shape == (4, 2, 2, 2, 2, 8, 8)

    def test_blocks_match_einsum(self):
        """Verify block computation matches manual einsum at a single site."""
        L = 2
        h_np = _random_h_field(L, seed=99)
        h = torch.tensor(h_np, dtype=DTYPE, device=DEVICE)
        blocks = precompute_blocks(h, CG, L)

        # Check site (0,0,0,0) = flat index 0, direction mu=1
        mu = 1
        h_site_mu = h[0, mu, :]  # (4,) — h[site=0, mu=1, a=0..3]
        expected = torch.einsum('a,aij->ij', h_site_mu, CG)
        actual = blocks[mu, 0, 0, 0, 0]  # [mu=1, x0=0, x1=0, x2=0, x3=0]
        torch.testing.assert_close(actual, expected, atol=1e-14, rtol=1e-14)


class TestApplyFermionMatrix:
    """Test matrix-free operator against dense construction."""

    @pytest.fixture
    def setup_L4(self):
        """Set up L=4 test case."""
        L = 4
        h_np = _random_h_field(L, seed=42)
        h = torch.tensor(h_np, dtype=DTYPE, device=DEVICE)
        V = L ** 4
        dim = 8 * V

        A_dense = build_fermion_matrix_torch(h, L, device=DEVICE, dtype=DTYPE)
        blocks = precompute_blocks(h, CG, L)

        return {'L': L, 'A_dense': A_dense, 'blocks': blocks, 'dim': dim, 'h': h}

    def test_matches_dense_single_vector(self, setup_L4):
        """Matrix-free matches dense for a single random vector."""
        s = setup_L4
        v = torch.randn(s['dim'], dtype=DTYPE, device=DEVICE)

        Av_dense = s['A_dense'] @ v
        Av_mf = apply_fermion_matrix(v, s['blocks'], s['L'])

        torch.testing.assert_close(Av_mf, Av_dense, atol=1e-12, rtol=1e-12)

    def test_matches_dense_multiple_vectors(self, setup_L4):
        """Matrix-free matches dense for 10 random vectors."""
        s = setup_L4
        rng = torch.Generator(device=DEVICE).manual_seed(123)

        for _ in range(10):
            v = torch.randn(s['dim'], dtype=DTYPE, device=DEVICE, generator=rng)
            Av_dense = s['A_dense'] @ v
            Av_mf = apply_fermion_matrix(v, s['blocks'], s['L'])
            torch.testing.assert_close(Av_mf, Av_dense, atol=1e-12, rtol=1e-12)

    def test_zero_vector(self, setup_L4):
        """A @ 0 = 0."""
        s = setup_L4
        v = torch.zeros(s['dim'], dtype=DTYPE, device=DEVICE)
        Av = apply_fermion_matrix(v, s['blocks'], s['L'])
        assert torch.allclose(Av, torch.zeros_like(Av))

    def test_antisymmetry(self, setup_L4):
        """<u, Av> = -<Au, v> for antisymmetric A."""
        s = setup_L4
        rng = torch.Generator(device=DEVICE).manual_seed(456)
        u = torch.randn(s['dim'], dtype=DTYPE, device=DEVICE, generator=rng)
        v = torch.randn(s['dim'], dtype=DTYPE, device=DEVICE, generator=rng)

        Au = apply_fermion_matrix(u, s['blocks'], s['L'])
        Av = apply_fermion_matrix(v, s['blocks'], s['L'])

        lhs = torch.dot(u, Av)
        rhs = -torch.dot(Au, v)
        torch.testing.assert_close(lhs, rhs, atol=1e-10, rtol=1e-10)

    def test_flat_vs_reshaped_input(self, setup_L4):
        """Flat (dim,) and reshaped (V,8) inputs give same result."""
        s = setup_L4
        v_flat = torch.randn(s['dim'], dtype=DTYPE, device=DEVICE)
        V = s['L'] ** 4
        v_shaped = v_flat.reshape(V, 8)

        result_flat = apply_fermion_matrix(v_flat, s['blocks'], s['L'])
        result_shaped = apply_fermion_matrix(v_shaped, s['blocks'], s['L'])

        torch.testing.assert_close(result_flat, result_shaped.reshape(-1),
                                    atol=1e-14, rtol=1e-14)


class TestApplyAtA:
    """Test A^dagger A = -A^2 operator."""

    @pytest.fixture
    def setup_L4(self):
        L = 4
        h_np = _random_h_field(L, seed=42)
        h = torch.tensor(h_np, dtype=DTYPE, device=DEVICE)
        V = L ** 4
        dim = 8 * V

        A_dense = build_fermion_matrix_torch(h, L, device=DEVICE, dtype=DTYPE)
        AtA_dense = -A_dense @ A_dense
        blocks = precompute_blocks(h, CG, L)

        return {'L': L, 'AtA_dense': AtA_dense, 'blocks': blocks, 'dim': dim}

    def test_matches_dense_AtA(self, setup_L4):
        """Matrix-free AtA matches dense -A@A."""
        s = setup_L4
        rng = torch.Generator(device=DEVICE).manual_seed(789)

        for _ in range(5):
            v = torch.randn(s['dim'], dtype=DTYPE, device=DEVICE, generator=rng)
            AtAv_dense = s['AtA_dense'] @ v
            AtAv_mf = apply_AtA(v, s['blocks'], s['L'])
            torch.testing.assert_close(AtAv_mf, AtAv_dense, atol=1e-10, rtol=1e-10)

    def test_positive_semidefinite(self, setup_L4):
        """AtA is PSD: v^T (AtA) v >= 0 for all v."""
        s = setup_L4
        rng = torch.Generator(device=DEVICE).manual_seed(101)

        for _ in range(20):
            v = torch.randn(s['dim'], dtype=DTYPE, device=DEVICE, generator=rng)
            AtAv = apply_AtA(v, s['blocks'], s['L'])
            inner = torch.dot(v, AtAv)
            assert inner.item() >= -1e-10, f"AtA not PSD: v^T AtA v = {inner.item()}"

    def test_symmetric(self, setup_L4):
        """AtA is symmetric: <u, AtA v> = <AtA u, v>."""
        s = setup_L4
        rng = torch.Generator(device=DEVICE).manual_seed(202)
        u = torch.randn(s['dim'], dtype=DTYPE, device=DEVICE, generator=rng)
        v = torch.randn(s['dim'], dtype=DTYPE, device=DEVICE, generator=rng)

        AtAu = apply_AtA(u, s['blocks'], s['L'])
        AtAv = apply_AtA(v, s['blocks'], s['L'])

        lhs = torch.dot(u, AtAv)
        rhs = torch.dot(AtAu, v)
        torch.testing.assert_close(lhs, rhs, atol=1e-9, rtol=1e-9)


class TestVerifyAgainstDense:
    """Test the built-in verification function."""

    def test_L4_verification(self):
        h_np = _random_h_field(4, seed=42)
        max_rel, max_abs = verify_against_dense(
            h_np, L=4, n_vectors=5, device=DEVICE, dtype=DTYPE)
        assert max_rel < 1e-13, f"Relative error too large: {max_rel}"
        assert max_abs < 1e-10, f"Absolute error too large: {max_abs}"

    def test_L2_verification(self):
        h_np = _random_h_field(2, seed=99)
        max_rel, max_abs = verify_against_dense(
            h_np, L=2, n_vectors=10, device=DEVICE, dtype=DTYPE)
        assert max_rel < 1e-13, f"Relative error too large: {max_rel}"


class TestMakeCGOperator:
    """Test the CG-compatible operator wrapper."""

    def test_callable_returns_correct_shape(self):
        L = 2
        h = torch.tensor(_random_h_field(L), dtype=DTYPE, device=DEVICE)
        blocks = precompute_blocks(h, CG, L)
        apply_fn = make_cg_operator(blocks, L)

        dim = 8 * L ** 4
        v = torch.randn(dim, dtype=DTYPE, device=DEVICE)
        result = apply_fn(v)
        assert result.shape == (dim,)

    def test_cg_convergence(self):
        """CG with matrix-free operator converges to same solution as dense."""
        L = 4
        h_np = _random_h_field(L, seed=42)
        h = torch.tensor(h_np, dtype=DTYPE, device=DEVICE)
        dim = 8 * L ** 4

        # Dense reference
        A_dense = build_fermion_matrix_torch(h, L, device=DEVICE, dtype=DTYPE)
        AtA_dense = -A_dense @ A_dense

        # Matrix-free
        blocks = precompute_blocks(h, CG, L)
        apply_fn = make_cg_operator(blocks, L)

        # RHS
        rng = torch.Generator(device=DEVICE).manual_seed(42)
        b = torch.randn(dim, dtype=DTYPE, device=DEVICE, generator=rng)

        # Solve with dense: (AtA + sigma) x = b
        sigma = 1.0
        M_dense = AtA_dense + sigma * torch.eye(dim, dtype=DTYPE, device=DEVICE)
        x_dense = torch.linalg.solve(M_dense, b)

        # Solve with matrix-free CG
        x_mf = torch.zeros(dim, dtype=DTYPE, device=DEVICE)
        r = b.clone()
        p = r.clone()
        rr = torch.dot(r, r)

        for _ in range(1000):
            Ap = apply_fn(p) + sigma * p
            pAp = torch.dot(p, Ap)
            alpha = rr / pAp
            x_mf = x_mf + alpha * p
            r = r - alpha * Ap
            rr_new = torch.dot(r, r)
            if rr_new < 1e-20:
                break
            beta = rr_new / rr
            p = r + beta * p
            rr = rr_new

        # Solutions should match
        rel_err = torch.norm(x_mf - x_dense) / torch.norm(x_dense)
        assert rel_err < 1e-8, f"CG solution error: {rel_err}"


class TestMultiShiftIntegration:
    """Test matrix-free operator with the RHMC multi-shift solver."""

    def test_multi_shift_solve_matches_dense(self):
        """Matrix-free multi_shift_solve gives same solutions as dense."""
        from src.vestigial.hs_rhmc_torch import multi_shift_solve_torch

        L = 4
        h_np = _random_h_field(L, seed=42)
        h = torch.tensor(h_np, dtype=DTYPE, device=DEVICE)
        dim = 8 * L ** 4

        # Dense
        A_dense = build_fermion_matrix_torch(h, L, device=DEVICE, dtype=DTYPE)
        AtA_dense = -A_dense @ A_dense

        # Matrix-free
        blocks = precompute_blocks(h, CG, L)
        apply_fn = make_cg_operator(blocks, L)

        # RHS and shifts
        rng = torch.Generator(device=DEVICE).manual_seed(42)
        b = torch.randn(dim, dtype=DTYPE, device=DEVICE, generator=rng)
        shifts = [0.1, 1.0, 10.0]

        # Dense solve (LU)
        sols_dense = multi_shift_solve_torch(
            AtA_dense, b, shifts, method='batched_lu')

        # Matrix-free solve (CG)
        sols_mf = multi_shift_solve_torch(
            apply_fn, b, shifts, tol=1e-10, max_iter=2000, method='shared_krylov')

        for k, (sd, sm) in enumerate(zip(sols_dense, sols_mf)):
            rel_err = torch.norm(sd - sm) / torch.norm(sd)
            assert rel_err < 1e-6, (
                f"Shift {shifts[k]}: rel error {rel_err:.2e}")

    def test_force_computation_matches_dense(self):
        """Matrix-free force computation matches dense."""
        from src.vestigial.hs_rhmc_torch import (
            compute_forces_torch, build_fermion_matrix_torch
        )
        from src.vestigial.stencil_dirac import (
            apply_fermion_matrix as apply_A_stencil,
            apply_AtA as apply_AtA_stencil,
        )

        L = 4
        h_np = _random_h_field(L, seed=42)
        h = torch.tensor(h_np, dtype=torch.float32, device=DEVICE)
        V = L ** 4
        dim = 8 * V
        g = 2.0

        # Build dense matrix
        A_dense = build_fermion_matrix_torch(h, L, device=DEVICE, dtype=torch.float32)

        # Build matrix-free operators
        CG32 = torch.tensor(_CG_np, dtype=torch.float32, device=DEVICE)
        blocks = precompute_blocks(h, CG32, L)
        stencil_ops = {
            'apply_A': lambda v: apply_A_stencil(v, blocks, L),
            'apply_AtA': lambda v: apply_AtA_stencil(v, blocks, L),
        }

        # Pseudofermion
        rng = torch.Generator(device=DEVICE).manual_seed(42)
        phi = torch.randn(dim, dtype=torch.float32, device=DEVICE, generator=rng)

        # Zolotarev coefficients (small set for testing)
        alphas = torch.tensor([0.5, 0.3, 0.2], dtype=torch.float32, device=DEVICE)
        betas = torch.tensor([0.1, 1.0, 10.0], dtype=torch.float32, device=DEVICE)

        # Dense forces
        F_dense = compute_forces_torch(h, g, A_dense, phi, alphas, betas, L)

        # Matrix-free forces
        F_mf = compute_forces_torch(h, g, None, phi, alphas, betas, L,
                                     stencil_ops=stencil_ops)

        # Should match (float32 tolerance)
        rel_err = torch.norm(F_dense - F_mf) / torch.norm(F_dense)
        assert rel_err < 1e-3, f"Force rel error: {rel_err:.2e}"


class TestMemoryScaling:
    """Verify memory characteristics of matrix-free approach."""

    def test_no_dense_matrix_allocated(self):
        """Matrix-free path doesn't allocate V^2 storage."""
        L = 4
        V = L ** 4
        h = torch.tensor(_random_h_field(L), dtype=DTYPE, device=DEVICE)
        blocks = precompute_blocks(h, CG, L)

        # blocks shape: (4, L, L, L, L, 8, 8) = 4 * V * 64 elements
        blocks_elements = blocks.numel()
        dense_elements = (8 * V) ** 2

        # Matrix-free should use << dense storage
        assert blocks_elements < dense_elements / 10, (
            f"Blocks ({blocks_elements}) should be much smaller than "
            f"dense ({dense_elements})")

    def test_blocks_memory_L12_estimate(self):
        """Estimate memory for L=12 blocks (don't actually allocate)."""
        L = 12
        V = L ** 4  # 20736
        # blocks: 4 * V * 8 * 8 = 4 * 20736 * 64 = 5,308,416 float64 elements
        # = 5,308,416 * 8 bytes = ~42 MB
        blocks_bytes = 4 * V * 64 * 8
        assert blocks_bytes < 50_000_000, f"Blocks for L=12 should be < 50 MB, got {blocks_bytes}"

        # Dense would be: (8*V)^2 * 8 = 165888^2 * 8 = ~220 GB
        dense_bytes = (8 * V) ** 2 * 8
        ratio = dense_bytes / blocks_bytes
        assert ratio > 4000, f"Memory savings ratio should be > 4000x, got {ratio}"
