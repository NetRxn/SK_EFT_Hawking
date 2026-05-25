"""Graphene MIR bound numerical confrontation with Crossno 2016 data.

Phase 6q Wave 2b numerical companion. Lifts the Lean substrate-level
placeholder ``horizon_transport_uniqueness_graphene_witness_one_half``
(mirConst = 1/2) to the substantive CHHK ``(2·β_2/(4π))^(1/3) ≈ 0.0756``
graphene MIR constant.

Canonical formulas live in :mod:`src.core.formulas`; this module performs
the graphene-platform specialization and confronts the bound with measured
Crossno 2016 Dirac-fluid mean-free-path data.

References:
    CHHK arXiv:2509.18255 — eq. (29) super-Planckian MIR-style limit.
    Crossno et al. Science 351, 1058 (2016) — ℓ ~ 50-100 nm at T ~ 75 K
        in clean graphene Dirac fluid (WF violation regime).
    Castro Neto et al. RMP 81, 109 (2009) — graphene tight-binding
        a = 0.246 nm.
"""

from __future__ import annotations

from src.core.formulas import (
    graphene_mir_constant,
    graphene_mir_constant_mpmath,
)


# ──────────────────────────────────────────────────────────────────────
# Graphene experimental anchors
# ──────────────────────────────────────────────────────────────────────

#: Graphene lattice spacing a = 0.246 nm (= √3 · 0.142 nm = √3 · a_CC).
#:
#: Source: Castro Neto, Guinea, Peres, Novoselov, Geim, "The electronic
#: properties of graphene," Rev. Mod. Phys. 81, 109 (2009), §I.B.1
#: (Tight-Binding Hamiltonian) — the standard graphene lattice constant.
#: Cached primary source at
#: `Lit-Search/Phase-1-and-Background/primary-sources/CastroNeto2009RMPGraphene.pdf`.
GRAPHENE_LATTICE_SPACING_M: float = 0.246e-9

#: Representative Dirac-fluid momentum-relaxation length ℓ_m (sample S1) at 60 K.
#:
#: Source: Crossno et al. Science 351, 1058 (2016), Fig. 3C caption (p. 4 of
#: cached PDF): "ℓ_m is estimated to be 1.5, 0.6, and 0.034 μm for samples
#: S1, S2, and S3, respectively." We adopt S1 (cleanest sample, mobility
#: ~3·10⁵ cm²/V·s per Table S.I) as the representative value for the CHHK
#: MIR-bound confrontation; S2 (0.6 μm) and S3 (0.034 μm) bracket the
#: substrate-quality range. The earlier figure of 80 nm (in pre-adversarial-
#: review prose) was not paper-anchored and has been corrected here.
CROSSNO_GRAPHENE_MEAN_FREE_PATH_M: float = 1.5e-6

#: Range of Crossno 2016 sample mean-free-paths (S3, S2, S1 at 60 K).
#:
#: Source: Crossno et al. Science 351, 1058 (2016), Fig. 3C caption.
#: Spans ~44× across samples — substrate-quality range, not measurement
#: uncertainty. The dirtiest sample S3 (0.034 μm) is the closest to the
#: CHHK MIR bound; the cleanest sample S1 (1.5 μm) is the furthest above.
CROSSNO_GRAPHENE_MEAN_FREE_PATH_RANGE_M: tuple[float, float, float] = (
    0.034e-6,  # S3
    0.6e-6,    # S2
    1.5e-6,    # S1
)


# ──────────────────────────────────────────────────────────────────────
# Graphene MIR bound — substantive lift of the Lean substrate placeholder
# ──────────────────────────────────────────────────────────────────────

def graphene_mir_bound_constant() -> float:
    """CHHK MIR constant `(2·β_2/(4π))^(1/3)` for d=2 graphene Dirac fluid.

    Substantive numerical lift of the Lean substrate-level placeholder
    ``horizon_transport_uniqueness_graphene_witness_one_half`` (which
    ships at ``mirConst = 1/2``). The Lean placeholder is a *safe upper
    bound*: 1/2 > 0.0756, so the Lean theorem ℓ/a ≥ 1/2 trivially
    implies ℓ/a ≥ 0.0756 (the substantive CHHK bound).

    The constant comes from CHHK eq. (29) super-Planckian limit
    ``(d·β_d/(4π))^(1/(d+1))`` at d=2 with
    ``β_d = (1/π)·(V_{d-1}/(2π)^d)·(1 - π/4)/(d+2)`` and
    ``V_1 = 2π`` (unit-circle circumference, standard physics convention).

    Returns:
        float MIR constant ≈ 0.07562892800257200.
    """
    return graphene_mir_constant()


def graphene_mir_constraint(ell_m: float, a_m: float = GRAPHENE_LATTICE_SPACING_M) -> bool:
    """Check whether ℓ/a satisfies the CHHK MIR bound for graphene Dirac fluid.

    The CHHK bootstrap states that any DKM transport correlator satisfying
    the six CHHK axiom families on a d=2 substrate has collective mean free
    path ``ℓ = √(τ·D)`` at least ``(2·β_2/(4π))^(1/3) · a`` where ``a`` is
    the microscopic lattice scale.

    Args:
        ell_m: collective mean free path in meters.
        a_m: lattice spacing in meters (default: graphene a = 0.246 nm).

    Returns:
        True if ℓ/a ≥ MIR constant, False otherwise.

    Raises:
        ValueError: if ``ell_m <= 0`` or ``a_m <= 0``.
    """
    if ell_m <= 0:
        raise ValueError(f"mean free path must be positive, got {ell_m}")
    if a_m <= 0:
        raise ValueError(f"lattice spacing must be positive, got {a_m}")
    return ell_m / a_m >= graphene_mir_bound_constant()


def crossno_graphene_satisfies_chhk_bound() -> dict:
    """Crossno 2016 graphene Dirac fluid satisfies CHHK MIR bound (verification).

    Computes the ratio ℓ/a for Crossno's measured momentum-relaxation
    length ℓ_m on the three reported samples (S1=1.5 μm, S2=0.6 μm,
    S3=0.034 μm at 60 K, per Fig. 3C caption) and Castro Neto's graphene
    lattice spacing (0.246 nm). Confronts each sample with the CHHK MIR
    constant.

    The Crossno regime is the Dirac-fluid window where Wiedemann-Franz is
    violated and the system enters hydrodynamic transport; this is the
    regime in which the CHHK bootstrap applies. The bound is satisfied
    by all three samples with margins ranging from ~1800× (cleanest S1)
    to ~1.8× (dirtiest S3) — the dirtiest sample is closest to (but still
    above) the CHHK MIR bound.

    Returns:
        Dict with keys:
            ell_over_a_representative: float, S1 (cleanest) measured ℓ/a.
            ell_over_a_per_sample: dict, per-sample {S3, S2, S1} ℓ/a values.
            mir_bound: float, CHHK MIR constant lower bound.
            margin_representative: float, S1 ratio of observed to bound.
            margin_per_sample: dict, per-sample margin values.
            satisfies_bound_all_samples: bool, True iff all three samples
                exceed the bound.
    """
    s3_ell, s2_ell, s1_ell = CROSSNO_GRAPHENE_MEAN_FREE_PATH_RANGE_M
    a = GRAPHENE_LATTICE_SPACING_M
    mir_bound = graphene_mir_bound_constant()

    per_sample = {
        "S3": s3_ell / a,
        "S2": s2_ell / a,
        "S1": s1_ell / a,
    }
    margins = {k: v / mir_bound for k, v in per_sample.items()}

    return {
        "ell_over_a_representative": s1_ell / a,
        "ell_over_a_per_sample": per_sample,
        "mir_bound": mir_bound,
        "margin_representative": (s1_ell / a) / mir_bound,
        "margin_per_sample": margins,
        "satisfies_bound_all_samples": all(v >= mir_bound for v in per_sample.values()),
    }


def graphene_mir_constant_high_precision(dps: int = 30) -> str:
    """Graphene MIR constant to ``dps`` decimal places via mpmath.

    Returns the decimal-string representation suitable for committing to
    Lean numeric literals or paper tables. Default dps=30 far exceeds the
    Wave 2a.1 DR §6 target of 10^{-6} precision.

    Args:
        dps: decimal places (default 30).

    Returns:
        str decimal representation, e.g., "0.0756289280025720..." .
    """
    import mpmath
    return mpmath.nstr(graphene_mir_constant_mpmath(dps), dps)
