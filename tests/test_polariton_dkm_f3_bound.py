"""Regression source for photon-equivalent arithmetic and scalar comparisons.

Legacy F3/occupation/uniqueness names and diagnostics are retained for
compatibility. Assertions verify unchanged arithmetic and refusal behavior;
they are not physical F3, mode-support or platform-branch certificates.
"""

import math
import pytest

from src.core.formulas import polariton_mode_occupation_per_pulse
from src.dkm_polariton import (
    mode_occupation_per_pulse,
    is_below_dkm_f3_threshold,
    DKM_F3_THRESHOLD_OCCUPATION,
    penn_tmd_occupation_at_switching_threshold,
    paris_lkb_occupation_at_typical_pump,
)


# ─── Canonical formula identity ────────────────────────────────────────


def test_module_wraps_canonical_formula():
    """`dkm_polariton.mode_occupation_per_pulse` is a thin wrapper around
    the canonical `src.core.formulas` formula."""
    for pulse_J, ph_eV in [(4e-15, 1.736), (1e-12, 1.485), (3.2e-19, 1.0)]:
        assert mode_occupation_per_pulse(pulse_J, ph_eV) == (
            polariton_mode_occupation_per_pulse(pulse_J, ph_eV)
        )


def test_canonical_formula_matches_planck_constant_identity():
    """`n = E / (ℏω)` evaluated against exact SI 2019 constants."""
    # E = 4 fJ, ℏω = 1.736 eV → n = 4e-15 / (1.736 × 1.602176634e-19)
    expected = 4e-15 / (1.736 * 1.602176634e-19)
    assert polariton_mode_occupation_per_pulse(4e-15, 1.736) == pytest.approx(
        expected, rel=1e-12
    )


def test_canonical_formula_rejects_negative_pulse_energy():
    with pytest.raises(ValueError):
        polariton_mode_occupation_per_pulse(-1.0, 1.0)


def test_canonical_formula_rejects_nonpositive_photon_energy():
    with pytest.raises(ValueError):
        polariton_mode_occupation_per_pulse(1e-15, 0.0)
    with pytest.raises(ValueError):
        polariton_mode_occupation_per_pulse(1e-15, -0.5)


# ─── Penn TMD witness ──────────────────────────────────────────────────


def test_penn_tmd_per_pulse_occupation_in_expected_range():
    """Adopted4fJ/1.736eV conversion gives about1.44e4 incident photon equivalents."""
    n_penn = penn_tmd_occupation_at_switching_threshold()
    assert 1.40e4 < n_penn < 1.50e4, f"n_penn = {n_penn}"
    # Sanity: matches the strategy-synthesis "≈ 1.5 × 10⁴" headline.
    assert math.isclose(n_penn, 1.438e4, rel_tol=2e-2)


def test_penn_tmd_below_f3_threshold():
    """The stored conversion is below the adopted legacy scalar proxy."""
    n_penn = penn_tmd_occupation_at_switching_threshold()
    assert is_below_dkm_f3_threshold(n_penn)
    # About70-fold scalar headroom; no two-orders or physical-F3 inference.
    headroom = DKM_F3_THRESHOLD_OCCUPATION / n_penn
    assert headroom > 50.0, f"Penn TMD margin only {headroom:.1f}x"


# ─── Paris-LKB witness ─────────────────────────────────────────────────


def test_paris_lkb_per_coherence_occupation_negligible():
    """Illustrative1nW*8ps conversion gives about0.0336 photon equivalents."""
    n_paris = paris_lkb_occupation_at_typical_pump()
    assert 0.01 < n_paris < 0.10, f"n_paris = {n_paris}"


def test_paris_lkb_below_f3_threshold():
    """Compare illustrative photon equivalents with the adopted scalar proxy."""
    n_paris = paris_lkb_occupation_at_typical_pump()
    assert is_below_dkm_f3_threshold(n_paris)
    headroom = DKM_F3_THRESHOLD_OCCUPATION / n_paris
    assert headroom > 1e7  # ≳ 10⁷× margin


def test_paris_lkb_scales_linearly_with_pump_power():
    """`mode_occupation_per_pulse` is linear in pulse_energy_J."""
    n1 = paris_lkb_occupation_at_typical_pump(pump_power_W=1e-9)
    n2 = paris_lkb_occupation_at_typical_pump(pump_power_W=2e-9)
    assert n2 == pytest.approx(2.0 * n1)


# ─── Threshold predicate sanity ────────────────────────────────────────


def test_is_below_dkm_f3_threshold_at_default():
    assert is_below_dkm_f3_threshold(0.0)
    assert is_below_dkm_f3_threshold(1e5)
    assert not is_below_dkm_f3_threshold(1e7)
    assert not is_below_dkm_f3_threshold(DKM_F3_THRESHOLD_OCCUPATION)


def test_is_below_dkm_f3_threshold_with_custom_threshold():
    assert is_below_dkm_f3_threshold(5.0, threshold=10.0)
    assert not is_below_dkm_f3_threshold(15.0, threshold=10.0)


# Legacy branch-test label; only scalar comparisons occur below.


def test_both_polariton_platforms_take_positive_uniqueness_branch():
    """Legacy test name retained: the body compares two counts with a scalar proxy.

    The unchanged failure text uses the legacy F3 threshold label only;
    it is no physical certificate. Neither actual platform classification
    nor exclusive graphene/BEC/polariton partition is proved by this test.
    """
    for name, n in [
        ("Penn TMD",   penn_tmd_occupation_at_switching_threshold()),
        ("Paris-LKB", paris_lkb_occupation_at_typical_pump()),
    ]:
        assert is_below_dkm_f3_threshold(n), (
            f"{name}: occupation {n:.2e} exceeds F3 threshold "
            f"{DKM_F3_THRESHOLD_OCCUPATION:.0e}"
        )
