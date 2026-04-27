"""Tests for `src/qec_holography/` — Phase 6c Wave 4 mirrors.

Covers `code_distance.py` and `scrambling_time.py`. Numerical anchors
verify the Lean theorems on three concrete MTC substrates: Fibonacci,
Ising, and trivial-abelian.
"""

from __future__ import annotations

import math

import pytest

from src.qec_holography import (
    FIBONACCI_SPECTRUM,
    ISING_SPECTRUM,
    SU3K2_SPECTRUM,
    TRIVIAL_ABELIAN_SPECTRUM,
    MTCSpectrum,
    code_distance,
    code_distance_admissible,
    global_dim_sq,
    recovery_possible_at_scrambling_bound,
    recovery_threshold,
    scrambling_time_bound,
)


# ---------------------------------------------------------------------------
# §1 — MTCSpectrum invariants
# ---------------------------------------------------------------------------


class TestMTCSpectrumInvariants:
    """Validates the spectrum dataclass enforces unit + positivity."""

    def test_fibonacci_unit_first(self) -> None:
        assert FIBONACCI_SPECTRUM.quantum_dims[0] == 1.0

    def test_ising_unit_first(self) -> None:
        assert ISING_SPECTRUM.quantum_dims[0] == 1.0

    def test_empty_spectrum_rejected(self) -> None:
        with pytest.raises(ValueError, match="empty"):
            MTCSpectrum(name="empty", quantum_dims=())

    def test_non_unit_first_rejected(self) -> None:
        with pytest.raises(ValueError, match="unit"):
            MTCSpectrum(name="bad", quantum_dims=(2.0, 1.0))

    def test_negative_dim_rejected(self) -> None:
        with pytest.raises(ValueError, match="positive"):
            MTCSpectrum(name="bad", quantum_dims=(1.0, -1.0))

    def test_d_max_fibonacci(self) -> None:
        assert FIBONACCI_SPECTRUM.d_max == pytest.approx(
            (1.0 + math.sqrt(5.0)) / 2.0
        )

    def test_d_max_trivial_abelian(self) -> None:
        assert TRIVIAL_ABELIAN_SPECTRUM.d_max == 1.0


# ---------------------------------------------------------------------------
# §2 — Code distance (mirror of Lean codeDistance + biconditional)
# ---------------------------------------------------------------------------


class TestCodeDistance:
    """Mirrors `HPCode.codeDistance_pos_iff_non_abelian`."""

    def test_fibonacci_positive(self) -> None:
        # log(φ) ≈ 0.481 > 0
        assert code_distance(FIBONACCI_SPECTRUM) > 0.0

    def test_fibonacci_concrete_value(self) -> None:
        phi = (1.0 + math.sqrt(5.0)) / 2.0
        assert code_distance(FIBONACCI_SPECTRUM) == pytest.approx(math.log(phi))

    def test_fibonacci_lt_log_two(self) -> None:
        """Mirrors `fibonacci_HPCode_codeDistance_lt_log_two`."""
        assert code_distance(FIBONACCI_SPECTRUM) < math.log(2.0)

    def test_ising_positive(self) -> None:
        # σ has d = √2 > 1 ⇒ log(√2) > 0
        assert code_distance(ISING_SPECTRUM) > 0.0

    def test_ising_concrete_value(self) -> None:
        # log(√2) = (log 2)/2
        assert code_distance(ISING_SPECTRUM) == pytest.approx(0.5 * math.log(2.0))

    def test_trivial_abelian_zero(self) -> None:
        assert code_distance(TRIVIAL_ABELIAN_SPECTRUM) == 0.0

    def test_admissibility_fibonacci(self) -> None:
        assert code_distance_admissible(FIBONACCI_SPECTRUM)

    def test_admissibility_ising(self) -> None:
        assert code_distance_admissible(ISING_SPECTRUM)

    def test_admissibility_su3_k2_subsector(self) -> None:
        assert code_distance_admissible(SU3K2_SPECTRUM)

    def test_admissibility_trivial_abelian_fails(self) -> None:
        """Mirrors `trivialAbelian_violates_admissibility`."""
        assert not code_distance_admissible(TRIVIAL_ABELIAN_SPECTRUM)


# ---------------------------------------------------------------------------
# §3 — Global dim and scrambling time
# ---------------------------------------------------------------------------


class TestScramblingTime:
    """Mirrors `HPCode.scramblingTimeBound` + `*_pos_iff_nontrivial`."""

    def test_global_dim_sq_fibonacci(self) -> None:
        # D² = 1 + φ² = 1 + (1+φ) = 2 + φ (since φ² = φ + 1)
        phi = (1.0 + math.sqrt(5.0)) / 2.0
        assert global_dim_sq(FIBONACCI_SPECTRUM) == pytest.approx(1.0 + phi * phi)

    def test_global_dim_sq_ising(self) -> None:
        # D² = 1 + 2 + 1 = 4
        assert global_dim_sq(ISING_SPECTRUM) == pytest.approx(4.0)

    def test_global_dim_sq_trivial_abelian(self) -> None:
        assert global_dim_sq(TRIVIAL_ABELIAN_SPECTRUM) == 1.0

    def test_global_dim_sq_unit_lower_bound(self) -> None:
        """Mirrors `one_le_globalDimSq` from the Lean module."""
        for spec in (
            FIBONACCI_SPECTRUM,
            ISING_SPECTRUM,
            SU3K2_SPECTRUM,
            TRIVIAL_ABELIAN_SPECTRUM,
        ):
            assert global_dim_sq(spec) >= 1.0

    def test_scrambling_time_fibonacci_positive(self) -> None:
        """Mirrors `fibonacci_HPCode_scramblingTimeBound_pos`."""
        assert scrambling_time_bound(FIBONACCI_SPECTRUM) > 0.0

    def test_scrambling_time_ising_log_four(self) -> None:
        assert scrambling_time_bound(ISING_SPECTRUM) == pytest.approx(math.log(4.0))

    def test_scrambling_time_trivial_abelian_zero(self) -> None:
        assert scrambling_time_bound(TRIVIAL_ABELIAN_SPECTRUM) == 0.0

    def test_scrambling_time_pos_iff_nontrivial(self) -> None:
        """Mirrors `scramblingTimeBound_pos_iff_nontrivial`."""
        for spec in (FIBONACCI_SPECTRUM, ISING_SPECTRUM, SU3K2_SPECTRUM):
            assert scrambling_time_bound(spec) > 0.0
        assert scrambling_time_bound(TRIVIAL_ABELIAN_SPECTRUM) == 0.0


# ---------------------------------------------------------------------------
# §4 — Recovery threshold + recovery at scrambling bound
# ---------------------------------------------------------------------------


class TestRecoveryThreshold:
    """Mirrors `HPCode.recovery_at_scrambling_bound`."""

    def test_threshold_unit_zero(self) -> None:
        assert recovery_threshold(FIBONACCI_SPECTRUM, 0) == 0.0

    def test_threshold_fibonacci_tau(self) -> None:
        phi = (1.0 + math.sqrt(5.0)) / 2.0
        assert recovery_threshold(FIBONACCI_SPECTRUM, 1) == pytest.approx(math.log(phi))

    def test_threshold_out_of_range(self) -> None:
        with pytest.raises(IndexError):
            recovery_threshold(FIBONACCI_SPECTRUM, 5)

    def test_recovery_at_bound_all_spectra(self) -> None:
        """Universal claim from the Lean theorem."""
        for spec in (
            FIBONACCI_SPECTRUM,
            ISING_SPECTRUM,
            SU3K2_SPECTRUM,
            TRIVIAL_ABELIAN_SPECTRUM,
        ):
            for idx in range(len(spec.quantum_dims)):
                assert recovery_possible_at_scrambling_bound(spec, idx)

    def test_recovery_fibonacci_tau(self) -> None:
        # log(φ) < log(D²_Fibonacci) ≈ log(3.618) ≈ 1.286
        assert recovery_possible_at_scrambling_bound(FIBONACCI_SPECTRUM, 1)
