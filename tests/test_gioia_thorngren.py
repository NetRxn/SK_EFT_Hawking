"""
Tests for Gioia-Thorngren domain module (src/chirality/gioia_thorngren.py).

Covers: BZ construction, vectorized BdG, commutator verification,
band structure, GW relation, and full evasion analysis.
"""

import numpy as np
import pytest

from src.chirality.gioia_thorngren import (
    analyze_gt_evasion,
    band_structure,
    bdg_hamiltonian,
    bdg_hamiltonian_fast,
    brillouin_zone,
    chiral_charge_4x4,
    chiral_charge_eigenvalues,
    chiral_charge_tau,
    find_weyl_nodes,
    ginsparg_wilson_check,
    h_eff,
    h_tau,
    verify_commutator,
    verify_commutator_tau,
    wilson_mass,
)


class TestBrillouinZone:
    """Discrete BZ construction."""

    def test_shape(self):
        k = brillouin_zone(4)
        assert k.shape == (64, 3)

    def test_includes_origin(self):
        k = brillouin_zone(4)
        assert np.any(np.all(np.abs(k) < 1e-10, axis=1))

    def test_periodicity(self):
        """All momenta in [0, 2π)."""
        k = brillouin_zone(8)
        assert np.all(k >= 0)
        assert np.all(k < 2 * np.pi + 1e-10)

    def test_count(self):
        for L in [2, 4, 6, 8]:
            k = brillouin_zone(L)
            assert len(k) == L ** 3


class TestWilsonMass:
    """Vectorized Wilson mass."""

    def test_zero_at_origin(self):
        k = np.array([[0.0, 0.0, 0.0]])
        M = wilson_mass(k)
        assert np.isclose(M[0], 0.0)

    def test_positive_away_from_origin(self):
        k = brillouin_zone(4)
        M = wilson_mass(k)
        origin_mask = np.all(np.abs(k) < 1e-10, axis=1)
        assert np.all(M[~origin_mask] > 0)

    def test_single_weyl_node(self):
        for L in [4, 8, 12]:
            k = brillouin_zone(L)
            nodes = find_weyl_nodes(k)
            assert len(nodes) == 1


class TestBdGHamiltonian:
    """BdG Hamiltonian construction."""

    def test_hermitian(self):
        k = brillouin_zone(4)
        H = bdg_hamiltonian_fast(k)
        assert np.allclose(H, np.conj(np.transpose(H, (0, 2, 1))), atol=1e-12)

    def test_fast_matches_loop(self):
        """Fast vectorized version matches explicit loop version."""
        k = brillouin_zone(4)
        H_fast = bdg_hamiltonian_fast(k, r=1.0)
        H_loop = bdg_hamiltonian(k, r=1.0)
        assert np.allclose(H_fast, H_loop, atol=1e-12)

    def test_shape(self):
        k = brillouin_zone(4)
        H = bdg_hamiltonian_fast(k)
        assert H.shape == (64, 4, 4)

    def test_gapless_at_weyl_node(self):
        """Energy gap vanishes at k=0 (Weyl node)."""
        k = np.array([[0.0, 0.0, 0.0]])
        bands = band_structure(k, r=1.0)
        # At k=0 with r=1: H = σ₂⊗(r·0·𝟙) = 0, so all bands = 0
        assert np.allclose(bands, 0, atol=1e-12)

    def test_gapped_at_doubler(self):
        """Energy gap is nonzero at doubler momenta."""
        k = np.array([[np.pi, 0.0, 0.0]])
        bands = band_structure(k, r=1.0)
        assert np.any(np.abs(bands) > 0.1)


class TestChiralCharge:
    """Chiral charge properties."""

    def test_hermitian(self):
        k = brillouin_zone(4)
        Q = chiral_charge_4x4(k)
        assert np.allclose(Q, np.conj(np.transpose(Q, (0, 2, 1))), atol=1e-12)

    def test_eigenvalues(self):
        k = brillouin_zone(4)
        ev = chiral_charge_eigenvalues(k)
        assert ev.shape == (64, 2)
        # Eigenvalues are ±cos(p3/2)
        p3 = k[:, 2]
        expected = np.cos(p3 / 2.0)
        assert np.allclose(ev[:, 0], expected, atol=1e-12)
        assert np.allclose(ev[:, 1], -expected, atol=1e-12)

    def test_ginsparg_wilson(self):
        """GW relation: q_A² = cos²(p3/2) · 𝟙₄."""
        for L in [4, 8]:
            k = brillouin_zone(L)
            result = ginsparg_wilson_check(k)
            assert result['passes']

    def test_noncompact_spectrum(self):
        """Eigenvalues take non-integer values."""
        k = brillouin_zone(8)
        ev = chiral_charge_eigenvalues(k)
        # Should have values strictly between 0 and 1
        assert np.any((np.abs(ev) > 0.01) & (np.abs(ev) < 0.99))


class TestCommutator:
    """[H, Q_A] = 0 verification."""

    def test_4x4_commutator(self):
        for L in [4, 8]:
            k = brillouin_zone(L)
            result = verify_commutator(k, r=1.0)
            assert result['all_zero']
            assert result['max_norm'] < 1e-12

    def test_2x2_tau_commutator(self):
        k = brillouin_zone(8)
        result = verify_commutator_tau(k)
        assert result['all_zero']
        assert result['max_norm'] < 1e-12

    def test_parameter_independent(self):
        """Commutator vanishes for all Wilson parameter values."""
        k = brillouin_zone(4)
        for r in [0.1, 0.5, 1.0, 2.0, 10.0]:
            result = verify_commutator(k, r=r)
            assert result['all_zero'], f"Failed for r={r}"


class TestEvasionAnalysis:
    """Full GT evasion report."""

    def test_single_weyl_node(self):
        report = analyze_gt_evasion(L=4)
        assert report.weyl_node_count == 1

    def test_chiral(self):
        report = analyze_gt_evasion(L=4)
        assert report.is_chiral

    def test_non_on_site(self):
        report = analyze_gt_evasion(L=4)
        assert not report.is_on_site
        assert report.q_a_range == 1

    def test_non_compact(self):
        report = analyze_gt_evasion(L=4)
        assert not report.is_compact

    def test_commutator_verified(self):
        report = analyze_gt_evasion(L=8)
        assert report.commutator_verified

    def test_gs_violations(self):
        report = analyze_gt_evasion(L=4)
        assert len(report.gs_violations) >= 2
        assert 'I2_on_site' in report.gs_violations
        assert 'I3_compact_spectrum' in report.gs_violations
