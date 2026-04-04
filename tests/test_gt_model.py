"""
Tests for Gioia-Thorngren lattice chiral fermion model (Phase 5a Wave 2).

Covers: Wilson mass function, chiral charge, commutator identity,
BdG structure, and connections to existing GS/TPF formalization.
"""

import numpy as np
import pytest

from src.core.constants import GT_MODEL, ONSAGER_ALGEBRA
from src.core.formulas import (
    gt_chiral_charge,
    gt_commutator_identity,
    gt_wilson_mass,
)


class TestWilsonMass:
    """Wilson mass M(k) = 3 - cos(kx) - cos(ky) - cos(kz)."""

    def test_zero_at_origin(self):
        result = gt_wilson_mass(0, 0, 0)
        assert result['is_zero'] is True
        assert result['mass'] == pytest.approx(0.0)

    def test_positive_at_pi_zero_zero(self):
        result = gt_wilson_mass(np.pi, 0, 0)
        assert result['is_positive'] is True
        assert result['mass'] == pytest.approx(2.0)

    def test_positive_at_pi_pi_zero(self):
        result = gt_wilson_mass(np.pi, np.pi, 0)
        assert result['is_positive'] is True
        assert result['mass'] == pytest.approx(4.0)

    def test_max_at_pi_pi_pi(self):
        result = gt_wilson_mass(np.pi, np.pi, np.pi)
        assert result['mass'] == pytest.approx(6.0)

    def test_nonneg_random(self):
        """Wilson mass is non-negative for random momenta."""
        rng = np.random.default_rng(42)
        for _ in range(100):
            k = rng.uniform(-np.pi, np.pi, size=3)
            result = gt_wilson_mass(*k)
            assert result['mass'] >= -1e-14

    def test_only_zero_at_origin_on_lattice(self):
        """On discrete BZ with L=4, M(k)=0 only at k=(0,0,0)."""
        L = 4
        zero_count = 0
        for n1 in range(L):
            for n2 in range(L):
                for n3 in range(L):
                    k = (2 * np.pi * n1 / L, 2 * np.pi * n2 / L, 2 * np.pi * n3 / L)
                    result = gt_wilson_mass(*k)
                    if result['is_zero']:
                        zero_count += 1
        assert zero_count == GT_MODEL['WEYL_NODE_COUNT']

    def test_symmetry(self):
        """Wilson mass is symmetric under k -> -k."""
        k = (0.5, 1.2, 2.3)
        mk = (-0.5, -1.2, -2.3)
        assert gt_wilson_mass(*k)['mass'] == pytest.approx(gt_wilson_mass(*mk)['mass'])

    def test_max_value_constant(self):
        result = gt_wilson_mass(0, 0, 0)
        assert result['max_value'] == GT_MODEL['WILSON_MAX']


class TestChiralCharge:
    """Chiral charge q_A(p) in 2x2 Nambu space."""

    def test_hermitian(self):
        result = gt_chiral_charge(1.5)
        assert result['is_hermitian'] is True
        m = result['matrix_2x2']
        assert np.allclose(m, m.conj().T)

    def test_eigenvalues_at_zero(self):
        """At p3=0: eigenvalues ±1 (full chirality)."""
        result = gt_chiral_charge(0)
        assert result['eigenvalues'][0] == pytest.approx(1.0)
        assert result['eigenvalues'][1] == pytest.approx(-1.0)

    def test_eigenvalues_at_pi(self):
        """At p3=π: eigenvalues ±0 (chirality fades at doubler)."""
        result = gt_chiral_charge(np.pi)
        assert abs(result['eigenvalues'][0]) < 1e-10

    def test_gw_relation(self):
        """Ginsparg-Wilson: q_A^2 = cos^2(p3/2) * I."""
        for p3 in [0, 0.5, 1.0, np.pi / 2, np.pi]:
            result = gt_chiral_charge(p3)
            m = result['matrix_2x2']
            m_sq = m @ m
            expected = np.cos(p3 / 2) ** 2 * np.eye(2)
            assert np.allclose(m_sq, expected, atol=1e-12)

    def test_non_on_site_range(self):
        """Chiral charge has range R=1 (nearest-neighbor)."""
        result = gt_chiral_charge(1.0)
        assert result['range_R'] == GT_MODEL['Q_A_RANGE']

    def test_noncompact_spectrum(self):
        """Eigenvalues are continuous (non-quantized) across the BZ."""
        eigenvals = [gt_chiral_charge(p3)['eigenvalues'][0] for p3 in np.linspace(0, 2 * np.pi, 50)]
        # Not all the same — non-compact
        assert max(eigenvals) - min(eigenvals) > 0.5


class TestCommutatorIdentity:
    """The 2x2 Nambu-space commutator [h_tau, q_tau] = 0."""

    def test_vanishes_at_zero(self):
        result = gt_commutator_identity(0)
        assert result['vanishes'] is True

    def test_vanishes_at_pi(self):
        result = gt_commutator_identity(np.pi)
        assert result['vanishes'] is True

    def test_vanishes_at_random(self):
        """Commutator vanishes for all p3 — this is sin^2 + cos^2 = 1."""
        rng = np.random.default_rng(123)
        for _ in range(200):
            p3 = rng.uniform(-np.pi, np.pi)
            result = gt_commutator_identity(p3)
            assert result['vanishes'] is True

    def test_pythagorean_identity(self):
        """The two terms are equal (both sin^2(p3)/2)."""
        for p3 in np.linspace(0.1, 3.0, 20):
            result = gt_commutator_identity(p3)
            assert result['term1_sin_sq'] == pytest.approx(result['term2_product'], abs=1e-12)

    def test_identity_label(self):
        result = gt_commutator_identity(1.0)
        assert 'Pythagorean' in result['identity_used']


class TestGTModelConstants:
    """GT model constants consistency."""

    def test_lattice_dim(self):
        assert GT_MODEL['LATTICE_DIM'] == 3

    def test_bdg_block_dim(self):
        assert GT_MODEL['BDG_BLOCK_DIM'] == GT_MODEL['NAMBU_FACTOR'] * GT_MODEL['N_BANDS']

    def test_weyl_node_count(self):
        assert GT_MODEL['WEYL_NODE_COUNT'] == 1

    def test_gs_violations(self):
        """GT violates at least 2 GS conditions."""
        assert len(GT_MODEL['GS_VIOLATIONS']) >= 2
        assert 'I2_on_site' in GT_MODEL['GS_VIOLATIONS']
        assert 'I3_compact_spectrum' in GT_MODEL['GS_VIOLATIONS']

    def test_dg_coeff_matches_onsager(self):
        """DG coefficient 16 connects GT to Onsager algebra."""
        assert ONSAGER_ALGEBRA['DG_COEFF'] == 16


class TestBdGStructure:
    """BdG Hamiltonian structural tests."""

    def test_full_commutator_4x4(self):
        """Verify [H_BdG(k), q_A(k)] = 0 as explicit 4x4 matrix multiplication."""
        sigma_x = np.array([[0, 1], [1, 0]], dtype=complex)
        sigma_y = np.array([[0, -1j], [1j, 0]], dtype=complex)
        sigma_z = np.array([[1, 0], [0, -1]], dtype=complex)
        I2 = np.eye(2, dtype=complex)

        for p1, p2, p3 in [(0, 0, 0), (1.0, 0.5, 0.7), (np.pi, np.pi / 2, 1.5)]:
            r = 1.0
            W = 2 - np.cos(p1) - np.cos(p2)
            h_eff = (r * W * np.eye(2)
                     + np.sin(p3) * sigma_z
                     + (1 - np.cos(p3)) * sigma_x)
            H_bdg = (np.sin(p1) * np.kron(sigma_x, I2)
                     + np.sin(p2) * np.kron(sigma_z, I2)
                     + np.kron(sigma_y, h_eff))

            q_tau = ((1 + np.cos(p3)) / 2 * sigma_z
                     + np.sin(p3) / 2 * sigma_x)
            Q_A = np.kron(I2, q_tau)

            commutator = H_bdg @ Q_A - Q_A @ H_bdg
            assert np.allclose(commutator, 0, atol=1e-12), (
                f"[H, Q_A] ≠ 0 at p=({p1},{p2},{p3}), max |entry| = {np.max(np.abs(commutator))}"
            )

    def test_particle_hole_symmetry(self):
        """BdG particle-hole symmetry: tau_x H*(k) tau_x = -H(-k)."""
        sigma_x = np.array([[0, 1], [1, 0]], dtype=complex)
        sigma_y = np.array([[0, -1j], [1j, 0]], dtype=complex)
        sigma_z = np.array([[1, 0], [0, -1]], dtype=complex)
        tau_x = np.array([[0, 1], [1, 0]], dtype=complex)
        I2 = np.eye(2, dtype=complex)

        p1, p2, p3, r = 0.7, 1.2, 0.5, 1.0
        W = 2 - np.cos(p1) - np.cos(p2)
        h_eff = r * W * I2 + np.sin(p3) * sigma_z + (1 - np.cos(p3)) * sigma_x
        H_k = (np.sin(p1) * np.kron(sigma_x, I2)
               + np.sin(p2) * np.kron(sigma_z, I2)
               + np.kron(sigma_y, h_eff))

        # P = 1_sigma ⊗ tau_x (particle-hole)
        P = np.kron(I2, tau_x)
        lhs = P @ H_k.conj() @ P

        # H(-k)
        Wn = 2 - np.cos(-p1) - np.cos(-p2)
        h_eff_neg = r * Wn * I2 + np.sin(-p3) * sigma_z + (1 - np.cos(-p3)) * sigma_x
        H_neg = (np.sin(-p1) * np.kron(sigma_x, I2)
                 + np.sin(-p2) * np.kron(sigma_z, I2)
                 + np.kron(sigma_y, h_eff_neg))

        assert np.allclose(lhs, -H_neg, atol=1e-12)
