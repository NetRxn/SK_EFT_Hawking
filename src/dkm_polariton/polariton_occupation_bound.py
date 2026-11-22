"""Incident photon-equivalent counts and a legacy scalar threshold comparison.

E/(hbar omega) converts supplied energy; no mode projection, occupation
tail, hard support cutoff or Hamiltonian/open-generator growth bound is
derived here. The 1e6 constant is an adopted comparison proxy, not an
established physical F3 onset. A true comparison gives no transport or
uniqueness branch. Existing names and numerical behavior are preserved.
The conditional Lean growth theorem assumes its growth bound; its MIR
inheritance proof uses a normalized witness independently of pump data.
"""

from __future__ import annotations

from typing import Final

from src.core.constants import POLARITON_PLATFORMS
from src.core.formulas import polariton_mode_occupation_per_pulse


# ──────────────────────────────────────────────────────────────────────
# Substrate constants
# ──────────────────────────────────────────────────────────────────────


# Legacy adopted scalar proxy. Its name does not establish a physical
# F3 onset, operator-norm growth law or platform classification.
DKM_F3_THRESHOLD_OCCUPATION: Final[float] = 1.0e6


# Adopted bare-cavity reference energy from Wang arXiv:2411.16635v1.
# Retained for conversion; it is not the coupled-device/pump photon energy.
PENN_CAVITY_RESONANCE_eV: Final[float] = 1.736


# Adopted illustrative Paris reference energy. Supplied power*time
# gives a pulse-equivalent energy, not a calibrated modal occupation.
PARIS_LKB_POLARITON_eV: Final[float] = 1.485


# ──────────────────────────────────────────────────────────────────────
# Canonical formulas
# ──────────────────────────────────────────────────────────────────────


def mode_occupation_per_pulse(
    pulse_energy_J: float,
    photon_energy_eV: float,
) -> float:
    """Return incident photon equivalents from the canonical energy conversion.

    Legacy public wrapper name retained; neither per-cavity-mode population
    nor quantum occupation support is determined by these two inputs.
    """
    return polariton_mode_occupation_per_pulse(pulse_energy_J, photon_energy_eV)


def is_below_dkm_f3_threshold(
    n_per_mode: float,
    threshold: float = DKM_F3_THRESHOLD_OCCUPATION,
) -> bool:
    """Return exactly n_per_mode < threshold, with legacy parameter names.

    The default 1e6 is an adopted scalar proxy. True is no certificate of
    physical F3, bounded commutators, a hard occupation cutoff or uniqueness.
    No domain validation or alternative physical criterion is added.
    """
    return n_per_mode < threshold


# ──────────────────────────────────────────────────────────────────────
# Per-platform witnesses
# ──────────────────────────────────────────────────────────────────────


def penn_tmd_occupation_at_switching_threshold() -> float:
    """Return photon equivalents for the stored 4 fJ and bare-cavity1.736 eV.

    The unchanged arithmetic is about 1.44e4. In Wang arXiv:2411.16635v1,
    the 4 fJ input is a bandwidth-matched estimate, not a measured
    intracavity per-mode occupation or a hard cutoff. The coupled device
    has different resonances. Pump/source/modal/reservoir calibration
    and actual physical growth/transport remain required.
    """
    e_pulse_J = POLARITON_PLATFORMS["Penn_TMD_MoSe2"]["switching_energy_fJ"] * 1e-15
    return mode_occupation_per_pulse(e_pulse_J, PENN_CAVITY_RESONANCE_eV)


def paris_lkb_occupation_at_typical_pump(pump_power_W: float = 1e-9,
                                         coherence_time_s: float = 8e-12) -> float:
    """Return photon equivalents for supplied power times supplied time.

    The legacy defaults 1 nW, 8 ps and adopted1.485 eV give about0.0336.
    These are illustrative conversion inputs, not a measured Falque pump,
    coherence time, per-mode population or stationary state calibration.
    No physical F3 branch or occupation-support conclusion follows.
    """
    pulse_equivalent_J = pump_power_W * coherence_time_s
    return mode_occupation_per_pulse(pulse_equivalent_J, PARIS_LKB_POLARITON_eV)
