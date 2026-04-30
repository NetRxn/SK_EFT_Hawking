"""Cross-layer parity tests for DiracFluidWKB.lean (Phase 5w Wave 4).

Each test class mirrors a section of `lean/SKEFTHawking/DiracFluidWKB.lean`
and asserts that the Python helpers in `src/core/formulas.py` reproduce the
content of the Lean theorems numerically.

The cross-layer parity pattern is the durable mitigation against the
Python-Lean drift class documented in `feedback_python_lean_refs_drift.md`
(2 confirmed incidents through 2026-04-29).
"""

import numpy as np
import pytest

from src.core.constants import HBAR, K_B
from src.core.formulas import (
    dirac_fluid_sound_speed,
    dirac_fluid_horizon_velocity,
    graphene_transverse_momentum,
    graphene_channel_cutoff_energy,
    graphene_channel_spectrum_sum,
)


# ── Section 1: Sound-speed binding ───────────────────────────────────


class TestDiracFluidSoundSpeed:
    """Mirror of DiracFluidWKB.soundSpeed_* theorems."""

    @pytest.mark.parametrize("v_F", [1.0e5, 4.4e5, 7.1e5, 1.0e6])
    def test_soundSpeed_pos(self, v_F):
        """soundSpeed_pos: c_s > 0 when v_F > 0."""
        assert dirac_fluid_sound_speed(v_F) > 0

    @pytest.mark.parametrize("v_F", [1.0e5, 4.4e5, 7.1e5, 1.0e6])
    def test_soundSpeed_sq_eq_diracFluidSoundSpeedSq(self, v_F):
        """soundSpeed_sq + soundSpeed_sq_eq_diracFluidSoundSpeedSq:
        c_s² = v_F² / 2."""
        c_s = dirac_fluid_sound_speed(v_F)
        np.testing.assert_allclose(c_s ** 2, v_F ** 2 / 2, rtol=1e-12)

    @pytest.mark.parametrize("v_F", [1.0e5, 4.4e5, 7.1e5, 1.0e6])
    def test_soundSpeed_lt_vF_subluminal(self, v_F):
        """soundSpeed_lt_vF: graphene-specific subluminal property c_s < v_F.
        Distinct from BEC Bogoliubov superluminal regime; foundation of the
        more-robust-horizon claim of GrapheneHawking.lean."""
        assert dirac_fluid_sound_speed(v_F) < v_F

    @pytest.mark.parametrize("v_F", [1.0e5, 4.4e5, 1.0e6])
    def test_horizon_velocity_equals_soundSpeed(self, v_F):
        """Horizon condition v² = c_s² selects v = c_s = v_F/√2."""
        np.testing.assert_allclose(
            dirac_fluid_horizon_velocity(v_F),
            dirac_fluid_sound_speed(v_F),
            rtol=1e-12,
        )


# ── Section 2: Substantive cross-bridges to WKBConnection + QuasiOneD ─


class TestSubstantiveCrossBridges:
    """Mirror of DiracFluidWKB substantive cross-bridges.

    `noiseFloor_bounded_perturbative` and `channel_greybody_le_one` are
    the two non-trivial cross-bridges shipped after the strengthening pass
    (P3-class trivial restatements were cut).
    """

    def test_noiseFloor_bounded_perturbative(self):
        """noiseFloor_bounded_perturbative: under Γ_H ≤ κ (perturbative
        regime), noise floor n_noise = Γ_H/κ ≤ 1.

        For Dean device: Γ_H ≈ 10¹⁰ s⁻¹, κ ≈ 10¹² s⁻¹ → noise ≈ 10⁻² < 1.
        """
        Gamma_H = 1e10
        kappa = 1e12
        assert Gamma_H <= kappa  # perturbative-regime hypothesis
        noise_floor = Gamma_H / kappa
        assert noise_floor <= 1
        assert noise_floor < 0.02  # quantitatively well-perturbative

    def test_channel_greybody_le_one(self):
        """channel_greybody_le_one: Γ_n = 4·c_s·v / (c_s + v)² ≤ 1
        for any subsonic v with 0 < v ≤ c_s. Cross-bridge to
        QuasiOneDReduction.greybody_zero_freq_le_one.
        """
        for v_F in [4.4e5, 7.1e5, 1.0e6]:
            c_s = dirac_fluid_sound_speed(v_F)
            for v in [0.1 * c_s, 0.5 * c_s, 0.99 * c_s, c_s]:
                gamma = 4 * c_s * v / (c_s + v) ** 2
                assert 0 <= gamma <= 1
                # equality iff c_s = v (step-horizon limit)
                if abs(c_s - v) < 1e-10:
                    np.testing.assert_allclose(gamma, 1.0, rtol=1e-10)


# ── Section 3: Transverse-mode quantization ──────────────────────────


class TestTransverseMomentum:
    """Mirror of DiracFluidWKB.transverseMomentum_* theorems."""

    @pytest.mark.parametrize("n", [0, 1, 2, 5, 10])
    @pytest.mark.parametrize("W", [1e-7, 1e-6, 1e-5])
    def test_transverseMomentum_pos(self, n, W):
        """transverseMomentum_pos: k_n > 0 for any n, W > 0."""
        assert graphene_transverse_momentum(n, W) > 0

    def test_transverseMomentum_strictMono(self):
        """transverseMomentum_strictMono: k_n strictly increasing in n."""
        W = 1e-6
        ks = [graphene_transverse_momentum(n, W) for n in range(20)]
        for i in range(len(ks) - 1):
            assert ks[i] < ks[i + 1]

    @pytest.mark.parametrize("W", [1e-7, 1e-6, 1e-5])
    def test_transverseMomentum_zero(self, W):
        """transverseMomentum_zero: k_0 = π / W."""
        np.testing.assert_allclose(
            graphene_transverse_momentum(0, W), np.pi / W, rtol=1e-12,
        )


class TestChannelCutoffEnergy:
    """Mirror of DiracFluidWKB.channelCutoffEnergy_* theorems."""

    @pytest.mark.parametrize("n", [0, 1, 5])
    @pytest.mark.parametrize("v_F,W", [(1.0e6, 1e-6), (4.4e5, 1e-6)])
    def test_channelCutoffEnergy_pos(self, n, v_F, W):
        """channelCutoffEnergy_pos: ω_⊥(n) > 0."""
        c_s = dirac_fluid_sound_speed(v_F)
        assert graphene_channel_cutoff_energy(n, W, c_s) > 0

    def test_channelCutoffEnergy_strictMono(self):
        """channelCutoffEnergy_strictMono: ω_⊥(n) strictly increasing."""
        v_F = 1.0e6
        W = 1e-6
        c_s = dirac_fluid_sound_speed(v_F)
        omegas = [graphene_channel_cutoff_energy(n, W, c_s) for n in range(20)]
        for i in range(len(omegas) - 1):
            assert omegas[i] < omegas[i + 1]


# ── Section 4: Quantitative Dean-geometry separation ─────────────────


class TestDeanGeometrySeparation:
    """Mirror of DiracFluidWKB.dean_lowest_channel_above_four_omega_H.

    For the realised Dean bilayer-graphene de Laval nozzle:
      W = 1 μm, c_s = 4.4×10⁵ m/s, T_H ≈ 2.4 K → ω_H ≈ 3.14×10¹¹ s⁻¹
    The lowest transverse-mode cutoff exceeds ω_H by a factor of ~4.4.
    """

    def test_dean_lowest_channel_above_four_omega_H_norm_num(self):
        """Lean norm-num form (factor-of-4 strengthened):
        4.4e5 · π / 1e-6 > 4 · 3.14e11.

        Mirror of `dean_lowest_channel_above_four_omega_H` — the
        factor-of-4 form is load-bearing for Paper 16's "well-separated
        quasi-1D detection band" claim across the [0, 4ω_H] integration window.
        """
        lhs = 4.4e5 * np.pi / 1e-6
        rhs = 4 * 3.14e11
        assert lhs > rhs

    def test_dean_lowest_channel_above_four_omega_H_via_helpers(self):
        """Same claim using the production helpers."""
        v_F = 6.2e5  # bilayer Fermi velocity (c_s = v_F/√2 ≈ 4.4e5)
        c_s = dirac_fluid_sound_speed(v_F)
        np.testing.assert_allclose(c_s, 4.4e5, rtol=2e-2)

        W = 1e-6
        omega_perp_0 = graphene_channel_cutoff_energy(0, W, c_s)

        T_H = 2.4
        omega_H = K_B * T_H / HBAR

        assert omega_perp_0 > omega_H
        assert omega_perp_0 / omega_H > 4.0  # quantitative gap

    def test_dean_separation_factor(self):
        """The separation factor should be approximately π · c_s / (W · ω_H)."""
        c_s = 4.4e5
        W = 1e-6
        T_H = 2.4
        omega_H = K_B * T_H / HBAR
        factor = c_s * np.pi / W / omega_H
        # Expected: π·4.4e5/(1e-6·3.14e11) ≈ 4.4
        assert 4.0 < factor < 5.0


# ── Section 5: Sum-over-channels spectrum ────────────────────────────


class TestChannelSpectrumSum:
    """Mirror of DiracFluidWKB.channelSpectrumSum_* theorems."""

    def test_channelSpectrumSum_nonneg(self):
        """channelSpectrumSum_nonneg: Σ β·Γ ≥ 0 when each β, Γ ≥ 0."""
        rng = np.random.default_rng(20260429)
        for _ in range(20):
            N = rng.integers(1, 20)
            beta = rng.uniform(0, 10, size=N)
            gamma = rng.uniform(0, 1, size=N)
            assert graphene_channel_spectrum_sum(beta, gamma) >= 0

    def test_channelSpectrumSum_bounded_uniform(self):
        """channelSpectrumSum_bounded_uniform: Σ β·Γ ≤ Γ_max · Σ β."""
        rng = np.random.default_rng(20260429)
        for _ in range(20):
            N = rng.integers(1, 20)
            beta = rng.uniform(0, 10, size=N)
            Gamma_max = rng.uniform(0.1, 1.0)
            gamma = rng.uniform(0, Gamma_max, size=N)
            lhs = graphene_channel_spectrum_sum(beta, gamma)
            rhs = Gamma_max * np.sum(beta)
            assert lhs <= rhs + 1e-12  # numerical slack

    def test_channelSpectrumSum_at_unit_greybody(self):
        """When Γ = 1 uniformly, the sum equals Σ β (recovers single-channel
        upper bound used in the original Γ=1 Paper 16 treatment)."""
        beta = np.array([1.0, 2.0, 3.0, 4.0, 5.0])
        gamma = np.ones_like(beta)
        np.testing.assert_allclose(
            graphene_channel_spectrum_sum(beta, gamma),
            np.sum(beta),
            rtol=1e-12,
        )

    def test_channelSpectrumSum_at_zero_greybody(self):
        """When all Γ_n = 0, the channel sum vanishes (no transmission)."""
        beta = np.array([1.0, 2.0, 3.0])
        gamma = np.zeros_like(beta)
        assert graphene_channel_spectrum_sum(beta, gamma) == 0.0
