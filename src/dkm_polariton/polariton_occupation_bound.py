"""
Polariton per-mode occupation bound for the DKM F3 axiom check.

Background (Phase 6q context). The Chowdhury-Hartnoll-Hebbar-Khondaker
(2509.18255) DKM transport bootstrap requires the F3 operator-growth
axiom: ``‖[H, …, n₀]_κ‖ ≤ κ! · ε^κ · ‖n₀‖``. For continuum-bosonic
substrates (BEC Bogoliubov), the κ-fold commutator grows
super-factorially when the per-mode occupation is unbounded
(Yin-Lucas arXiv:2106.09726; Kuwahara-Saito arXiv:2103.11592
Lieb-Robinson-for-bosons), violating F3 for any choice of (ε, ‖n₀‖).
Phase 6q's `sharpened_no_go_super_factorial` formalizes this.

For driven-dissipative polaritons the per-mode occupation is *finitely
bounded* under any device-operating pump constraint. The number of
photons (and hence polaritons) per cavity mode per switching pulse is

.. math::

    n_{\\rm per\\ pulse} = \\frac{E_{\\rm pulse}}{\\hbar \\omega_{\\rm cav}}

For the UPenn nanocavity-polariton platform (Wang et al. PRL 136,
146901, 2026), the all-optical switching threshold is
``E_pulse = 4 fJ`` at cavity resonance ``ℏω_cav = 1.736 eV``, giving

.. math::

    n_{\\rm per\\ pulse} \\approx 4 \\times 10^{-15} / (1.736 \\times 1.602 \\times 10^{-19})
                       \\approx 1.44 \\times 10^4

which is FOUR orders of magnitude below the F3-breaking regime
threshold ``n_threshold ≈ 10⁶``. Polariton therefore takes the
POSITIVE-uniqueness branch of the Phase 6q `PlatformBimodalOutcome`
under any device-operating pump constraint.

Lean cross-bridge: ``polariton_dkm_f3_holds_at_pump_below_threshold``
and ``polariton_inherits_graphene_uniqueness_result`` in
``lean/SKEFTHawking/DKMBootstrap/PolaritonF3Bound.lean`` encode the
substrate-level form of the bound.
"""

from __future__ import annotations

from typing import Final

from src.core.constants import POLARITON_PLATFORMS
from src.core.formulas import polariton_mode_occupation_per_pulse


# ──────────────────────────────────────────────────────────────────────
# Substrate constants
# ──────────────────────────────────────────────────────────────────────


# The F3-breaking onset for continuum-bosonic substrates per Yin-Lucas /
# Kuwahara-Saito Lieb-Robinson-for-bosons (Phase 6q Wave 2a.1 DR §1 BEC
# row): commutator norms become super-factorial unbounded when the
# effective per-mode bosonic occupation exceeds ~10⁶. Below this value
# the operator growth is bounded by κ! · ε^κ · ‖n₀‖ with ε proportional
# to √n_max, and F3 holds.
DKM_F3_THRESHOLD_OCCUPATION: Final[float] = 1.0e6


# Penn TMD cavity resonance energy — Wang et al. 2026 §"Cavity-polariton
# spectroscopy". Used to convert the 4 fJ switching pulse energy to a
# per-pulse photon count.
PENN_CAVITY_RESONANCE_eV: Final[float] = 1.736


# Paris-LKB polariton effective photon energy — the polariton dispersion
# in the working configuration sits in the ≈ 1.4 – 1.5 eV range; we use
# 1.485 eV as a representative working-point value. This anchors the
# per-pulse occupation cross-check; the substantive Paris-LKB Hawking
# experiment is CW, so per-pulse-equivalent here is the "per coherence
# time" occupation under a typical sub-nW pump.
PARIS_LKB_POLARITON_eV: Final[float] = 1.485


# ──────────────────────────────────────────────────────────────────────
# Canonical formulas
# ──────────────────────────────────────────────────────────────────────


def mode_occupation_per_pulse(
    pulse_energy_J: float,
    photon_energy_eV: float,
) -> float:
    """Per-cavity-mode photon count for a pulse of energy ``pulse_energy_J``
    at photon energy ``photon_energy_eV``.

    Thin wrapper around the canonical formula
    ``src.core.formulas.polariton_mode_occupation_per_pulse``; preserved
    here under the module-public name expected by external callers and
    by ``polariton_dkm_f3_holds_at_pump_below_threshold``'s Python-side
    cross-check.
    """
    return polariton_mode_occupation_per_pulse(pulse_energy_J, photon_energy_eV)


def is_below_dkm_f3_threshold(
    n_per_mode: float,
    threshold: float = DKM_F3_THRESHOLD_OCCUPATION,
) -> bool:
    """Return ``True`` iff the per-mode occupation is below the DKM-F3
    breaking threshold (default ``10⁶``).

    A ``True`` return means the polariton commutator-norm sequence is
    bounded by a factorial-power product (i.e. F3 holds), placing the
    platform on the POSITIVE-uniqueness branch of the Phase 6q
    `PlatformBimodalOutcome`.
    """
    return n_per_mode < threshold


# ──────────────────────────────────────────────────────────────────────
# Per-platform witnesses
# ──────────────────────────────────────────────────────────────────────


def penn_tmd_occupation_at_switching_threshold() -> float:
    """Per-pulse mode occupation at the Penn TMD device's 4 fJ switching
    threshold. Returns ≈ 1.44 × 10⁴.

    Sources for the input numbers
    -----------------------------
    - Penn switching pulse energy ``E_pulse = 4 fJ``: Wang et al. PRL 136,
      146901 (2026), arXiv:2411.16635 (registered as
      ``POLARITON_PLATFORMS['Penn_TMD_MoSe2']['switching_energy_fJ']``).
    - Penn cavity resonance ``ℏω_cav = 1.736 eV``: same paper (used to
      compute the Q-factor ``Q = E/γ_cav ≈ 914`` registered as
      ``POLARITON_PLATFORMS['Penn_TMD_MoSe2']['Q_factor']``).
    """
    e_pulse_J = POLARITON_PLATFORMS["Penn_TMD_MoSe2"]["switching_energy_fJ"] * 1e-15
    return mode_occupation_per_pulse(e_pulse_J, PENN_CAVITY_RESONANCE_eV)


def paris_lkb_occupation_at_typical_pump(pump_power_W: float = 1e-9,
                                         coherence_time_s: float = 8e-12) -> float:
    """Per-coherence-time mode occupation for the Paris-LKB polariton
    platform under a sub-nW pump (CW) over the standard 8 ps cavity
    coherence time.

    Default pump ``1 nW`` over coherence time ``8 ps`` corresponds to a
    pulse-equivalent energy of ``8 × 10⁻²¹ J``, yielding per-mode
    occupation ≈ ``8e-21 / (1.485 × 1.602e-19) ≈ 3.4 × 10⁻²`` — utterly
    negligible, far below the DKM-F3 threshold.

    Parameters
    ----------
    pump_power_W : float, optional
        Average CW pump power in watts (default 1 nW; the Falque 2025
        platform operates in this regime).
    coherence_time_s : float, optional
        Cavity coherence time in seconds (default 8 ps, the Falque 2025
        ``Paris_standard`` cavity lifetime).
    """
    pulse_equivalent_J = pump_power_W * coherence_time_s
    return mode_occupation_per_pulse(pulse_equivalent_J, PARIS_LKB_POLARITON_eV)
