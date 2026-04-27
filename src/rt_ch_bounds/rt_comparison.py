"""Classical RT vs W3 Kaul-Majumdar microscopic entropy.

Mirrors `RTCasiniHuertaBounds` Lean theorems
`rt_kaulMajumdar_gap_at_reduced_area_two`,
`rt_eq_kaulMajumdar_iff_trivial_reduced_area` (correctness-push;
its contrapositive supersedes the prior
`rt_classical_inconsistent_with_kaul_majumdar`, removed in the
2026-04-28 cross-wave strengthening pass),
`kaulMajumdar_not_H_RT`, and the W3 cross-bridge
`sen_4d_disagrees_with_kaul_majumdar`.
"""

from __future__ import annotations

import math


def classical_rt_entropy(area: float, G_N: float) -> float:
    """Classical Ryu-Takayanagi entropy `S = A/(4 G_N)`.

    Mirrors the H_RT_Formula_Valid tracked Prop's content.
    """
    if area <= 0 or G_N <= 0:
        raise ValueError(
            f"Classical RT requires positive area and G_N, "
            f"got A = {area}, G_N = {G_N}"
        )
    return area / (4.0 * G_N)


def kaul_majumdar_entropy(area: float, G_N: float, c0: float = 0.0) -> float:
    """Phase 6a Wave 3 Kaul-Majumdar microscopic entropy.

    `S = A/(4 G_N) - (3/2) log(A/(4 G_N)) + c0`.

    Mirrors `BHEntropyMicroscopic.kaulMajumdarS`.
    """
    if area <= 0 or G_N <= 0:
        raise ValueError(
            f"Kaul-Majumdar entropy requires positive area and G_N, "
            f"got A = {area}, G_N = {G_N}"
        )
    reduced = area / (4.0 * G_N)
    return reduced - 1.5 * math.log(reduced) + c0


def rt_kaul_majumdar_gap(area: float, G_N: float) -> float:
    """Universality-failure gap: classical-RT minus W3 Kaul-Majumdar.

    Equals `(3/2) log(A/(4 G_N))`.  Vanishes only at the knife-edge case
    `A = 4 G_N` (reduced area = 1).

    Mirrors the universality-gap formula derived in
    `rt_kaulMajumdar_gap_at_reduced_area_two`: at reduced area = 2 (i.e.
    `A = 8 G_N`), the gap equals `(3/2) log 2 ≈ 1.040`.
    """
    return classical_rt_entropy(area, G_N) - kaul_majumdar_entropy(area, G_N, c0=0.0)


# Phase 6a Wave 3 Sen 4D non-universality witness.
# Sen 4D Schwarzschild log coefficient: 212/45 - 3 = 77/45 ≈ 1.711.
def sen_4d_log_coeff() -> float:
    """Sen 4D Schwarzschild log coefficient `212/45 - 3`.

    Mirrors `BHEntropyMicroscopic.senFourDimSchwarzschildLogCoeff`.
    """
    return 212.0 / 45.0 - 3.0


# Quantitative gap between Sen 4D and Kaul-Majumdar log coefficients.
# Sen 4D = 212/45 - 3 = 77/45; Kaul-Majumdar = -3/2.
# Gap = 77/45 - (-3/2) = (77*2 + 3*45)/90 = (154 + 135)/90 = 289/90 ≈ 3.211.
SEN_KAUL_MAJUMDAR_COEFF_GAP = 289.0 / 90.0  # ≈ 3.211
